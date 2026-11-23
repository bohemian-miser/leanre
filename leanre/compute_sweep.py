#!/usr/bin/env python3
"""Phase 4 Computation & Dead-Code Archaeology sweep for leanre (gate D4).

Produces `outputs/decomp/compute_atlas.json` via two corpus-wide parallel sweeps
across all 175,187 `.lean` files in `data/rh_mirror/src`, cross-referenced
read-only (`mode=ro`) against `outputs/kernel/kernel.db`, `outputs/leanre.db`,
and `outputs/flirt/tier1.db`:

  1. Exact, disjoint 6-bucket classification of all 28,904 zero-kernel-decl
     modules (reachable via Main vs unreachable, alignment gaps in sighash /
     anonymous instances / duplicate decl names, pure import shims, erased
     macro/tactic/elab/syntax-only files, private/inline/instance/abbrev/struct-
     only files, and imported-but-unused theorems/defs) plus >=30 spot checks
     per non-empty bucket and full importer-chain proof for `DyadicPrimeIntervals`.
  2. Complete kernel-time computation & metaprogramming atlas (`decide +kernel`,
     plain `decide`, `native_decide`, giant `norm_num` blocks, `rfl`/numeric
     tables, `elab`/`run_tac`/`run_cmd`/`macro`/`kexactB`/`kcopy`/`CutCptCopy`/
     `SideCopy.LamCopy`/`sigSpan_copy`), distinguishing LIVE vs ABSENT/DEAD
     across `solution.ndjson.zst` / `kernel.db`.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import sqlite3
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from leanre import sighash  # noqa: E402

DEFAULT_MIRROR = ROOT / "data" / "rh_mirror"
DEFAULT_SRC = DEFAULT_MIRROR / "src"
DEFAULT_KERNEL_DB = ROOT / "outputs" / "kernel" / "kernel.db"
DEFAULT_LEANRE_DB = ROOT / "outputs" / "leanre.db"
DEFAULT_TIER1_DB = ROOT / "outputs" / "flirt" / "tier1.db"
DEFAULT_OUT_JSON = ROOT / "outputs" / "decomp" / "compute_atlas.json"

MAX_WORKERS = 16
BUCKET_ORDER = (
    "module_import_unreachable",
    "alignment_gap",
    "import_shim_reexport",
    "macro_tactic_elab_syntax_only",
    "unexported_private_or_inline",
    "imported_but_unused_by_kernel",
)

DECL_MODIFIERS = frozenset({
    "private", "protected", "noncomputable", "nonrec", "unsafe", "partial", "scoped", "local",
})
DECL_KINDS = frozenset({
    "theorem", "lemma", "def", "abbrev", "instance",
    "structure", "class", "inductive", "axiom", "opaque", "example",
})
NON_PRIVATE_CORE_KINDS = frozenset({
    "theorem", "lemma", "def", "inductive", "axiom", "opaque", "example",
})
META_ONLY_KEYWORDS = frozenset({
    "macro", "macro_rules", "syntax", "declare_syntax_cat",
    "elab", "elab_rules", "notation", "prefix", "infix", "infixl", "infixr", "postfix",
    "run_cmd", "run_tac", "initialize", "register_simp_attr", "attribute",
    "declare_aesop_rule_sets", "declare_command_tag",
})
SHIM_SKIP_KEYWORDS = frozenset({
    "import", "export", "open", "namespace", "section", "end",
    "variable", "variables", "universe", "universes", "set_option", "mutual",
})

# Regexes for comment-stripped source scanning
_DECIDE_KERNEL_RE = re.compile(r"\bdecide\b[^\n,;)]*?\+kernel\b")
_DECIDE_PLAIN_RE = re.compile(r"\bdecide\b")
_DECIDE_CBV_RE = re.compile(r"\bdecide_cbv\b")
_NATIVE_DECIDE_RE = re.compile(r"\bnative_decide\b")
_NORM_NUM_RE = re.compile(r"\bnorm_num\b")
_RFL_TOKEN_RE = re.compile(r"(?:\bby\s+rfl\b|:=\s*rfl\b|\brfl\s*$)")
_ELAB_CMD_RE = re.compile(r"^\s*(?:(?:local|scoped|private)\s+)*elab(?:_rules)?\b")
_MACRO_CMD_RE = re.compile(r"^\s*(?:(?:local|scoped|private)\s+)*macro(?:_rules)?\b")
_SYNTAX_CMD_RE = re.compile(r"^\s*(?:(?:local|scoped|private)\s+)*(?:syntax|declare_syntax_cat|notation|prefix|infix[lr]?|postfix)\b")
_ATTR_CMD_RE = re.compile(r"^\s*(?:local\s+)?attribute\b")
_RUN_CMD_RE = re.compile(r"^\s*run_cmd\b")
_RUN_TAC_RE = re.compile(r"\brun_tac\b")
_KEXACTB_RE = re.compile(r"\bkexactB\b")
_KCOPY_RE = re.compile(r"\bkcopy\b")
_CPT_COPY_RE = re.compile(r"\bcpt_copy_thms\b")
_COPY_CASES_RE = re.compile(r"\bcopy_cases\b")
_LAM_COPY_RE = re.compile(r"\b(?:lam_copy|sigSpan_copy)\b")
_BIG_INT_RE = re.compile(r"\b\d{18,}\b")
_RANGE_COMPUTE_RE = re.compile(r"\b(?:List\.range|Finset\.range|Finset\.Icc|Finset\.Ico|lcmUpto|Nat\.Prime|factorial_ladder|table_ok|loop_run|bernoulli)\b")

_NS_RE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.'₀-₉ₐ-ₜ]*)")
_SEC_RE = re.compile(r"^section(?:\s+([A-Za-z_][A-Za-z0-9_.'₀-₉ₐ-ₜ]*))?\b")
_END_RE = re.compile(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_.'₀-₉ₐ-ₜ]*))?\b")
_LEAN_META_MOD_RE = re.compile(
    r"\b(?:Lean\.(?:Elab|Meta|Parser|Syntax)|CoreM|MetaM|TacticM|CommandElab|TermElab|MacroM|Environment|Expr|NameSet|NameMap|Name)\b"
)


def connect_ro(path: Path) -> sqlite3.Connection:
    """Open an existing SQLite database strictly read-only."""
    if not path.is_file():
        raise FileNotFoundError(f"Missing SQLite database: {path}")
    return sqlite3.connect(f"file:{path}?mode=ro", uri=True)


def _strip_leading_attrs_and_mods(stmt: str) -> Tuple[str, List[str], List[str]]:
    """Peel leading `@[...]` attribute blocks and declaration modifiers."""
    attrs: List[str] = []
    mods: List[str] = []
    pos = 0
    n = len(stmt)
    while pos < n:
        while pos < n and stmt[pos].isspace():
            pos += 1
        if stmt.startswith("@[", pos):
            depth = 1
            j = pos + 2
            while j < n and depth > 0:
                if stmt[j] == "[":
                    depth += 1
                elif stmt[j] == "]":
                    depth -= 1
                j += 1
            attrs.append(stmt[pos + 2 : max(pos + 2, j - 1)].strip())
            pos = j
            continue
        m = re.match(r"([A-Za-z_][A-Za-z0-9_]*)\b", stmt[pos:])
        if m and m.group(1) in DECL_MODIFIERS:
            mods.append(m.group(1))
            pos += m.end()
            continue
        break
    return stmt[pos:], attrs, mods


def _pop_end_stack(ns_stack: List[Tuple[str, List[str]]], end_arg: Optional[str]) -> None:
    """Pop Lean 4 `namespace` / `section` / `mutual` frames cleanly on `end`."""
    if not ns_stack:
        return
    if not end_arg:
        ns_stack.pop()
        return
    rem = end_arg.split(".")
    while rem and ns_stack:
        kind, parts = ns_stack[-1]
        if kind == "mutual":
            ns_stack.pop()
            continue
        if not parts:
            ns_stack.pop()
            continue
        if len(parts) >= len(rem) and parts[-len(rem) :] == rem:
            if len(parts) == len(rem):
                ns_stack.pop()
            else:
                ns_stack[-1] = (kind, parts[: -len(rem)])
            return
        if len(rem) > len(parts) and rem[-len(parts) :] == parts:
            rem = rem[: -len(parts)]
            ns_stack.pop()
            continue
        ns_stack.pop()
        return


def _current_ns(ns_stack: Sequence[Tuple[str, List[str]]]) -> str:
    """Join active namespace components into a dot-separated prefix."""
    comps: List[str] = []
    for kind, parts in ns_stack:
        if kind == "ns":
            comps.extend(parts)
    return ".".join(comps)


def _extract_instance_target_class(sig_tail: str) -> str:
    """Extract the head type/class identifier after `:` in an instance header."""
    # Strip trailing `:= ...` or `where ...` first
    head = re.split(r"(?:\s:=\s|\bwhere\b)", sig_tail, maxsplit=1)[0]
    # Walk top-level brackets to locate top-level `:` separating binders from target
    depth = 0
    in_str = False
    colon_idx = -1
    i = 0
    while i < len(head):
        ch = head[i]
        if ch == '"' and (i == 0 or head[i - 1] != "\\"):
            in_str = not in_str
        elif not in_str:
            if ch in "([{⟨⦃":
                depth += 1
            elif ch in ")]}⟩⦄":
                depth = max(0, depth - 1)
            elif ch == ":" and depth == 0 and (i + 1 >= len(head) or head[i + 1] != "="):
                colon_idx = i
                break
        i += 1
    if colon_idx < 0:
        return ""
    rhs = head[colon_idx + 1 :].strip()
    # Skip leading universally quantified binders `{...}`, `[...]`, `(...)`, `∀ ... ,`
    rhs = re.sub(r"^(?:∀\s+[^,]+,\s*)+", "", rhs).strip()
    m = re.match(r"([A-Za-z_][A-Za-z0-9_.']*)", rhs)
    if not m:
        return ""
    tok = m.group(1)
    return tok.rsplit(".", 1)[-1]


def parse_module_decls_and_meta(
    text: str, module_name: str
) -> Dict[str, Any]:
    """Parse declarations, namespace scopes, and meta/shim flags from a `.lean` file."""
    stripped = sighash.strip_comments(text)
    lines = stripped.splitlines()
    n = len(lines)
    ns_stack: List[Tuple[str, List[str]]] = []

    imports: List[str] = []
    imports_lean_meta = False
    shim_cmds = 0
    meta_cmds: List[Tuple[str, int, str]] = []
    decls: List[Dict[str, Any]] = []

    i = 0
    while i < n:
        raw_line = lines[i]
        s = raw_line.strip()
        if not s:
            i += 1
            continue

        # Check namespace / section / end / mutual (at any shallow scope)
        m_ns = _NS_RE.match(s)
        if m_ns and not s.startswith("namespace "):
            pass
        if m_ns:
            ns_stack.append(("ns", m_ns.group(1).split(".")))
            shim_cmds += 1
            i += 1
            continue
        m_sec = _SEC_RE.match(s)
        if m_sec:
            sec_name = [m_sec.group(1)] if m_sec.group(1) else []
            ns_stack.append(("sec", sec_name))
            shim_cmds += 1
            i += 1
            continue
        if s == "mutual":
            ns_stack.append(("mutual", []))
            shim_cmds += 1
            i += 1
            continue
        m_end = _END_RE.match(s)
        if m_end and (s == "end" or re.match(r"^end\s+[A-Za-z_]", s)):
            _pop_end_stack(ns_stack, m_end.group(1))
            shim_cmds += 1
            i += 1
            continue

        if s.startswith("import "):
            imp = s[7:].strip().split()[0] if len(s) > 7 else ""
            imports.append(imp)
            if imp == "Lean" or imp.startswith("Lean."):
                imports_lean_meta = True
            shim_cmds += 1
            i += 1
            continue

        if re.match(r"^open\b", s) and (
            "Lean" in s.split() or "Lean.Elab" in s or "Lean.Meta" in s or "Lean.Parser" in s
        ):
            imports_lean_meta = True

        # Only look at declaration / command starts at shallow indentation or top-level
        indent = len(raw_line) - len(raw_line.lstrip(" "))
        # Allow nested namespace/section indentation (normally 0, sometimes 2 in this repo)
        rest, attrs, mods = _strip_leading_attrs_and_mods(s)
        if not rest and s.startswith("@["):
            # Multiline attribute header before decl — merge until closing `]` + next line
            hdr, next_i = sighash._header_extent(lines, i, max_lines=80)
            rest, attrs, mods = _strip_leading_attrs_and_mods(hdr)
            cand_end = next_i
        else:
            hdr = s
            cand_end = i + 1

        first_tok_m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\b", rest)
        first_tok = first_tok_m.group(1) if first_tok_m else ""

        if first_tok in META_ONLY_KEYWORDS:
            meta_cmds.append((first_tok, i + 1, rest[:48]))
            i = cand_end
            continue

        if first_tok in SHIM_SKIP_KEYWORDS:
            shim_cmds += 1
            i = cand_end
            continue

        # Check declaration keyword
        if first_tok in DECL_KINDS and (indent == 0 or ns_stack):
            # Re-read full multi-line header if single line didn't capture it
            if cand_end == i + 1:
                hdr, next_i = sighash._header_extent(lines, i, max_lines=400)
            else:
                next_i = cand_end
            parsed = sighash.split_header(hdr)
            if parsed is not None:
                kind = parsed["kind"]
                raw_name = parsed["name"] or ""
                is_private = "private" in mods
                attr_text = " ".join(attrs)
                is_inline = bool(re.search(r"\binline\b", attr_text))
                is_anon = kind == "instance" and (not raw_name or raw_name == "_")
                cur_ns = _current_ns(ns_stack)
                if raw_name and raw_name != "_":
                    fqn = f"{cur_ns}.{raw_name}" if cur_ns else raw_name
                else:
                    fqn = ""
                is_meta_def = bool(
                    imports_lean_meta
                    and kind in {"def", "abbrev"}
                    and bool(_LEAN_META_MOD_RE.search(hdr))
                )
                target_cls = _extract_instance_target_class(hdr) if is_anon else ""
                decls.append({
                    "kind": kind,
                    "raw_name": raw_name,
                    "fqn": fqn,
                    "ns": cur_ns,
                    "line_no": i + 1,
                    "is_private": is_private,
                    "is_inline": is_inline,
                    "is_anon_instance": is_anon,
                    "is_meta_def": is_meta_def,
                    "target_class": target_cls,
                })
                i = max(i + 1, next_i)
                continue

        # Fallback: standalone `_` or `run_tac` inside blocks is NOT a top-level meta cmd unless matched above
        i += 1

    return {
        "module": module_name,
        "imports": imports,
        "imports_lean_meta": imports_lean_meta,
        "shim_cmds": shim_cmds,
        "meta_cmds": meta_cmds,
        "decls": decls,
    }


def _worker_scan_batch(args: Tuple[List[Tuple[str, str]], Path]) -> List[Dict[str, Any]]:
    """Worker process scanning a batch of `(module_name, rel_file_path)` pairs."""
    batch, mirror_dir = args
    out: List[Dict[str, Any]] = []
    for mod, rel_path in batch:
        fpath = mirror_dir / rel_path
        raw = fpath.read_text(encoding="utf-8", errors="replace")

        lines_wc = raw.count("\n")
        bytes_len = len(raw.encode("utf-8", errors="replace"))
        stripped = sighash.strip_comments(raw)
        slines = stripped.splitlines()

        dk_hits: List[int] = []
        dk_occ = 0
        dp_hits: List[int] = []
        d_cbv_hits: List[int] = []
        native_hits: List[int] = []
        norm_hits: List[int] = []
        rfl_hits: List[int] = []
        elab_hits: List[int] = []
        macro_hits: List[int] = []
        syntax_hits: List[int] = []
        attr_hits: List[int] = []
        run_cmd_hits: List[int] = []
        run_tac_hits: List[int] = []
        kexactb_hits: List[int] = []
        kcopy_hits: List[int] = []
        cpt_copy_hits: List[int] = []
        copy_cases_hits: List[int] = []
        lam_copy_hits: List[int] = []
        big_int_hits: List[int] = []
        range_compute_hits: List[int] = []

        for ln, line in enumerate(slines, 1):
            dk_m = _DECIDE_KERNEL_RE.findall(line)
            if dk_m:
                dk_hits.append(ln)
                dk_occ += len(dk_m)
            elif _DECIDE_PLAIN_RE.search(line):
                # Check again excluding `decide_cbv` false positive
                cleaned = _DECIDE_CBV_RE.sub("", line)
                if _DECIDE_PLAIN_RE.search(cleaned):
                    dp_hits.append(ln)
            if _DECIDE_CBV_RE.search(line):
                d_cbv_hits.append(ln)
            if _NATIVE_DECIDE_RE.search(line):
                native_hits.append(ln)
            if _NORM_NUM_RE.search(line):
                norm_hits.append(ln)
            if _RFL_TOKEN_RE.search(line):
                rfl_hits.append(ln)
            if _ELAB_CMD_RE.match(line):
                elab_hits.append(ln)
            if _MACRO_CMD_RE.match(line):
                macro_hits.append(ln)
            if _SYNTAX_CMD_RE.match(line):
                syntax_hits.append(ln)
            if _ATTR_CMD_RE.match(line):
                attr_hits.append(ln)
            if _RUN_CMD_RE.match(line):
                run_cmd_hits.append(ln)
            if _RUN_TAC_RE.search(line):
                run_tac_hits.append(ln)
            if _KEXACTB_RE.search(line):
                kexactb_hits.append(ln)
            if _KCOPY_RE.search(line):
                kcopy_hits.append(ln)
            if _CPT_COPY_RE.search(line):
                cpt_copy_hits.append(ln)
            if _COPY_CASES_RE.search(line):
                copy_cases_hits.append(ln)
            if _LAM_COPY_RE.search(line):
                lam_copy_hits.append(ln)
            if _BIG_INT_RE.search(line):
                big_int_hits.append(ln)
            if _RANGE_COMPUTE_RE.search(line):
                range_compute_hits.append(ln)

        # Keep concise hits; cap per-file line arrays for huge files
        rec: Dict[str, Any] = {
            "module": mod,
            "file_path": rel_path,
            "lines_wc": lines_wc,
            "bytes": bytes_len,
            "dk": dk_hits,
            "dk_occ": dk_occ,
            "dp_count": len(dp_hits),
            "dp_sample": dp_hits[:5],
            "d_cbv_count": len(d_cbv_hits),
            "native": native_hits,
            "norm_count": len(norm_hits),
            "rfl_count": len(rfl_hits),
            "elab": elab_hits,
            "macro": macro_hits,
            "syntax": syntax_hits,
            "attr_count": len(attr_hits),
            "run_cmd": run_cmd_hits,
            "run_tac": run_tac_hits,
            "kexactb_count": len(kexactb_hits),
            "kexactb_sample": kexactb_hits[:5],
            "kcopy": kcopy_hits,
            "cpt_copy": cpt_copy_hits,
            "copy_cases": copy_cases_hits,
            "lam_copy": lam_copy_hits,
            "big_int_count": len(big_int_hits),
            "range_compute_count": len(range_compute_hits),
        }
        out.append(rec)
    return out


def _worker_parse_zero_batch(args: Tuple[List[Tuple[str, str]], Path]) -> List[Dict[str, Any]]:
    """Worker process performing full declaration & scope extraction for zero-kernel modules."""
    batch, mirror_dir = args
    out: List[Dict[str, Any]] = []
    for mod, rel_path in batch:
        fpath = mirror_dir / rel_path
        raw = fpath.read_text(encoding="utf-8", errors="replace")
        parsed = parse_module_decls_and_meta(raw, mod)
        parsed["lines_wc"] = raw.count("\n")
        parsed["bytes"] = len(raw.encode("utf-8", errors="replace"))
        parsed["file_path"] = rel_path
        out.append(parsed)
    return out


def compute_main_bfs(leanre_conn: sqlite3.Connection) -> Set[str]:
    """Compute transitive module import reachability from `Main` over `module_edges`."""
    adj: Dict[str, List[str]] = defaultdict(list)
    for src, dst in leanre_conn.execute("SELECT src, dst FROM module_edges"):
        adj[src].append(dst)
    seen: Set[str] = {"Main"}
    q = ["Main"]
    qi = 0
    while qi < len(q):
        cur = q[qi]
        qi += 1
        for nxt in adj.get(cur, ()):
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
    return seen


def _build_kernel_lookups(kconn: sqlite3.Connection) -> Dict[str, Any]:
    """Build compact read-only lookups over `kernel.db`."""
    name_to_ids: Dict[str, List[int]] = defaultdict(list)
    id_to_row: Dict[int, Tuple[str, str, int, int, int, int]] = {}
    for did, name, kind, flags, live_mask, value_nodes, type_nodes in kconn.execute(
        "SELECT id, name, kind, flags, live_mask, value_nodes, type_nodes FROM decls"
    ):
        name_to_ids[name].append(did)
        id_to_row[did] = (name, kind, flags, live_mask, value_nodes, type_nodes)

    const_to_decl_ids: Dict[str, List[int]] = defaultdict(list)
    for cname, did in kconn.execute("SELECT name, decl_id FROM consts"):
        const_to_decl_ids[cname].append(did)

    decl_to_mod: Dict[int, str] = {}
    decl_to_method: Dict[int, str] = {}
    mod_decl_counts: Counter[str] = Counter()
    unmatched_anon_ids: List[int] = []
    unmatched_named_ids: List[int] = []
    for did, mod, method in kconn.execute("SELECT decl_id, module, method FROM decl_module"):
        decl_to_method[did] = method
        if mod:
            decl_to_mod[did] = mod
            mod_decl_counts[mod] += 1
        elif method == "unmatched:project_auto_instance":
            unmatched_anon_ids.append(did)
        else:
            unmatched_named_ids.append(did)

    # Shortest root reach depth per decl_id
    min_depth: Dict[int, Tuple[int, int]] = {}
    for rid, did, depth in kconn.execute("SELECT root_id, decl_id, depth FROM reach"):
        prev = min_depth.get(did)
        if prev is None or depth < prev[0]:
            min_depth[did] = (depth, rid)

    return {
        "name_to_ids": name_to_ids,
        "id_to_row": id_to_row,
        "const_to_decl_ids": const_to_decl_ids,
        "decl_to_mod": decl_to_mod,
        "decl_to_method": decl_to_method,
        "mod_decl_counts": mod_decl_counts,
        "unmatched_anon_ids": unmatched_anon_ids,
        "unmatched_named_ids": unmatched_named_ids,
        "min_depth": min_depth,
    }


def _build_reverse_import_map(leanre_conn: sqlite3.Connection) -> Dict[str, Set[str]]:
    """Return `mod -> set of all modules that transitively import mod` plus `{mod}`."""
    importers: Dict[str, List[str]] = defaultdict(list)
    all_mods: List[str] = []
    for (m,) in leanre_conn.execute("SELECT name FROM modules"):
        all_mods.append(m)
    for src, dst in leanre_conn.execute("SELECT src, dst FROM module_edges"):
        importers[dst].append(src)
    # Build transitive importers lazily on demand via memoized DFS/BFS
    memo: Dict[str, Set[str]] = {}

    def get_trans_importers(target: str) -> Set[str]:
        if target in memo:
            return memo[target]
        seen = {target}
        stack = [target]
        while stack:
            cur = stack.pop()
            for par in importers.get(cur, ()):
                if par not in seen:
                    seen.add(par)
                    stack.append(par)
        memo[target] = seen
        return seen

    return importers, get_trans_importers  # type: ignore[return-value]


def _verify_anon_instance_matches(
    zero_parsed: Dict[str, Dict[str, Any]],
    kconn: sqlite3.Connection,
    klookups: Dict[str, Any],
    leanre_conn: sqlite3.Connection,
) -> Dict[str, List[Dict[str, Any]]]:
    """Strictly match `unmatched:project_auto_instance` kernel decls to zero-kernel modules."""
    importers: Dict[str, List[str]] = defaultdict(list)
    deps_fwd: Dict[str, List[str]] = defaultdict(list)
    for src, dst in leanre_conn.execute("SELECT src, dst FROM module_edges"):
        importers[dst].append(src)
        deps_fwd[src].append(dst)

    imp_cache: Dict[str, Set[str]] = {}
    dep_cache: Dict[str, Set[str]] = {}

    def trans_importers(m: str) -> Set[str]:
        if m not in imp_cache:
            s = {m}
            q = [m]
            while q:
                cur = q.pop()
                for p in importers.get(cur, ()):
                    if p not in s:
                        s.add(p)
                        q.append(p)
            imp_cache[m] = s
        return imp_cache[m]

    def trans_deps(m: str) -> Set[str]:
        if m not in dep_cache:
            s = {m}
            q = [m]
            while q:
                cur = q.pop()
                for d in deps_fwd.get(cur, ()):
                    if d not in s:
                        s.add(d)
                        q.append(d)
            dep_cache[m] = s
        return dep_cache[m]

    decl_to_mod = klookups["decl_to_mod"]
    id_to_row = klookups["id_to_row"]

    # Index candidate zero-kernel modules by `(target_class, anon_decl_record)`
    by_class: Dict[str, List[Tuple[str, Dict[str, Any]]]] = defaultdict(list)
    for mod, info in zero_parsed.items():
        for d in info["decls"]:
            if d["is_anon_instance"] and d["target_class"]:
                by_class[d["target_class"]].append((mod, d))

    matched_by_mod: Dict[str, List[Dict[str, Any]]] = defaultdict(list)

    # Examine only unmatched auto instances whose suffix/prefix matches a zero-kernel class
    for kid in klookups["unmatched_anon_ids"]:
        kname = id_to_row[kid][0]
        short = kname.rsplit(".", 1)[-1]
        if not short.startswith("inst"):
            continue
        # Extract candidate class prefix after `inst`
        matched_cands: List[Tuple[str, Dict[str, Any]]] = []
        for cls_name, entries in by_class.items():
            if short.startswith("inst" + cls_name):
                matched_cands.extend(entries)
        if not matched_cands:
            continue

        # Fetch kernel reverse users (src modules) and forward project dependencies (dst modules)
        user_mods = {
            decl_to_mod[src_id]
            for (src_id,) in kconn.execute("SELECT src FROM edges WHERE dst=?", (kid,))
            if src_id in decl_to_mod
        }
        if not user_mods:
            continue
        dep_mods = {
            decl_to_mod[dst_id]
            for (dst_id,) in kconn.execute("SELECT dst FROM edges WHERE src=?", (kid,))
            if dst_id in decl_to_mod
        }

        passing: List[Tuple[str, Dict[str, Any]]] = []
        for mod, d in matched_cands:
            ti = trans_importers(mod)
            if not user_mods.issubset(ti):
                continue
            td = trans_deps(mod)
            if not dep_mods.issubset(td):
                continue
            passing.append((mod, d))

        if len(passing) == 1:
            mod, d = passing[0]
            matched_by_mod[mod].append({
                "reason": "anon_instance_unmatched",
                "kernel_decl_id": kid,
                "kernel_name": kname,
                "kernel_live_mask": id_to_row[kid][3],
                "line_no": d["line_no"],
                "target_class": d["target_class"],
                "user_mod_count": len(user_mods),
                "dep_mod_count": len(dep_mods),
            })

    return matched_by_mod


def _top_folders(modules_rows: Sequence[Dict[str, Any]], depth: int = 2, limit: int = 12) -> List[Dict[str, Any]]:
    """Aggregate module counts and `lines_wc` by module prefix at depth 1 or 2."""
    counts: Counter[str] = Counter()
    lines_sum: Counter[str] = Counter()
    for r in modules_rows:
        parts = r["module"].split(".")
        key = ".".join(parts[:depth]) if len(parts) >= depth else r["module"]
        counts[key] += 1
        lines_sum[key] += r["lines_wc"]
    out = []
    for key, n_mods in counts.most_common(limit):
        out.append({"folder": key, "modules": n_mods, "lines_wc": lines_sum[key]})
    return out


def _build_spot_checks(
    bucket_rows: Dict[str, List[Dict[str, Any]]],
    parsed_zero: Dict[str, Dict[str, Any]],
    gap_details: Dict[str, List[Dict[str, Any]]],
    target_n: int = 32,
) -> Dict[str, List[Dict[str, Any]]]:
    """Select deterministic stratified >=30 spot-check receipts per non-empty bucket."""
    out: Dict[str, List[Dict[str, Any]]] = {}
    for bkt in BUCKET_ORDER:
        rows = sorted(bucket_rows[bkt], key=lambda x: x["module"])
        if not rows:
            out[bkt] = []
            continue
        if len(rows) <= target_n:
            chosen = rows
        else:
            # Uniform deterministic stride across lexicographically sorted modules
            step = len(rows) / target_n
            chosen = [rows[int(k * step)] for k in range(target_n)]
        samples: List[Dict[str, Any]] = []
        for r in chosen:
            mod = r["module"]
            p = parsed_zero[mod]
            decls = p.get("decls", [])
            metas = p.get("meta_cmds", [])
            entry: Dict[str, Any] = {
                "module": mod,
                "file_path": r["file_path"],
                "lines_wc": r["lines_wc"],
                "decl_count": len(decls),
                "meta_cmd_count": len(metas),
                "reason": r["reason"],
            }
            if decls:
                d0 = decls[0]
                entry["first_decl"] = f"{d0['kind']}:{d0['fqn'] or d0['raw_name'] or '_'}@{d0['line_no']}"
            elif metas:
                m0 = metas[0]
                entry["first_meta"] = f"{m0[0]}@{m0[1]}"
            if mod in gap_details:
                gd0 = gap_details[mod][0]
                entry["kernel_decl_id"] = gd0["kernel_decl_id"]
                entry["kernel_name"] = gd0["kernel_name"]
                entry["kernel_live_mask"] = gd0["kernel_live_mask"]
            samples.append(entry)
        out[bkt] = samples
    return out


def _trace_dyadic_chain(
    leanre_conn: sqlite3.Connection,
    klookups: Dict[str, Any],
    zero_mod_to_bucket: Dict[str, str],
) -> Dict[str, Any]:
    """Verify exact module & theorem reachability chain for `DyadicPrimeIntervals.Run1..4`."""
    importers: Dict[str, List[str]] = defaultdict(list)
    for src, dst in leanre_conn.execute("SELECT src, dst FROM module_edges"):
        importers[dst].append(src)

    focus_mods = [
        "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.SmallLoop",
        "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run1",
        "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run2",
        "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run3",
        "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run4",
        "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.SmallNaturalNumbersBound",
        "Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimesDyadicRS",
        "Formalism.PeriodIntegrals.ExplicitFormulaCounts.SqfCounts",
        "Formalism.SharpRestriction.LevelLetterCocycles.CylinderCountFamily",
        "Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JCount",
        "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop",
        "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.CountSuccLe",
    ]
    mod_stats = {}
    mod_lines = dict(leanre_conn.execute("SELECT name, lines_wc FROM modules").fetchall())
    for mod in focus_mods:
        kcnt = klookups["mod_decl_counts"].get(mod, 0)
        mod_stats[mod] = {
            "lines_wc": mod_lines.get(mod, 0),
            "kernel_decl_count": kcnt,
            "zero_bucket": zero_mod_to_bucket.get(mod),
            "direct_importers": sorted(importers.get(mod, [])),
        }

    # Check target names in kernel.db decls AND consts directly
    checked_symbols = [
        "PI.PrimesDyadicRS.K.run1",
        "PI.PrimesDyadicRS.K.run2",
        "PI.PrimesDyadicRS.K.run3",
        "PI.PrimesDyadicRS.K.run4",
        "PI.PrimesDyadicRS.primes_dyadic_range",
        "PI.EF.counts_closed",
        "Formalism.RS.family_bound_all",
        "Formalism.RS.family_count_all",
        "PI.PC.loop_run",
        "PI.PC.loop_run._proof_1_1",
        "PI.PC.count_succ_le",
    ]
    sym_status = {}
    for sym in checked_symbols:
        ids = klookups["name_to_ids"].get(sym, [])
        cids = klookups["const_to_decl_ids"].get(sym, [])
        row_info = []
        for did in ids:
            nm, kind, flags, lmask, vnodes, tnodes = klookups["id_to_row"][did]
            row_info.append({
                "decl_id": did,
                "kind": kind,
                "flags": flags,
                "live_mask": lmask,
                "value_nodes": vnodes,
                "module": klookups["decl_to_mod"].get(did),
            })
        sym_status[sym] = {
            "in_decls": len(ids) > 0,
            "in_consts": len(cids) > 0,
            "entries": row_info,
        }

    return {
        "modules": mod_stats,
        "symbols": sym_status,
        "dyadic_all_6_files_zero_kernel": all(
            mod_stats[m]["kernel_decl_count"] == 0 for m in focus_mods[:6]
        ),
        "chebyshev_smallloop_live_count": mod_stats[
            "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop"
        ]["kernel_decl_count"],
    }


def _collect_export_semantics(
    kconn: sqlite3.Connection, leanre_conn: sqlite3.Connection
) -> Dict[str, Any]:
    """Empirically verify which Lean 4 declaration kinds export to kernel.db."""
    # Sample kernel decls matching `private` (`_private.%`), `@[inline]`/`abbrev`/`structure`/`class`/`instance` in source
    priv_kernel_count = kconn.execute(
        "SELECT COUNT(*) FROM decls WHERE name LIKE '_private.%'"
    ).fetchone()[0]
    kind_counts = dict(kconn.execute("SELECT kind, COUNT(*) FROM decls GROUP BY kind").fetchall())
    method_counts = dict(
        kconn.execute("SELECT method, COUNT(*) FROM decl_module GROUP BY method").fetchall()
    )
    inst_method_matched = kconn.execute(
        "SELECT COUNT(*) FROM decls d JOIN decl_module dm ON dm.decl_id=d.id "
        "WHERE d.name LIKE '%.inst%' OR d.name LIKE 'inst%'"
    ).fetchone()[0]
    src_kind_counts = dict(
        leanre_conn.execute("SELECT kind, COUNT(*) FROM declarations GROUP BY kind").fetchall()
    )
    return {
        "kernel_decl_kind_counts": kind_counts,
        "kernel_private_prefixed_decls": priv_kernel_count,
        "kernel_inst_named_decls": inst_method_matched,
        "decl_module_methods": method_counts,
        "source_decl_kind_counts_leanre_db": src_kind_counts,
    }


def _enrich_decide_kernel_records(
    scan_rows: List[Dict[str, Any]],
    mirror_dir: Path,
    klookups: Dict[str, Any],
    zero_mod_to_bucket: Dict[str, str],
) -> List[Dict[str, Any]]:
    """Produce enriched entries for every `decide +kernel` `.lean` file (LIVE vs DEAD)."""
    dk_rows = [r for r in scan_rows if r["dk"]]
    out: List[Dict[str, Any]] = []
    for r in sorted(dk_rows, key=lambda x: x["module"]):
        mod = r["module"]
        fpath = mirror_dir / r["file_path"]
        raw = fpath.read_text(encoding="utf-8", errors="replace")
        parsed = parse_module_decls_and_meta(raw, mod)
        decls = parsed["decls"]

        hit_details: List[Dict[str, Any]] = []
        for ln in r["dk"]:
            # Find closest declaration with line_no <= ln
            enc: Optional[Dict[str, Any]] = None
            for d in decls:
                if d["line_no"] <= ln:
                    enc = d
                else:
                    break
            fqn = enc["fqn"] if enc else ""
            did = None
            k_info = None
            if fqn:
                if enc and enc["is_private"]:
                    cands = klookups["name_to_ids"].get(f"_private.{mod}.0.{fqn}", [])
                else:
                    cands = klookups["name_to_ids"].get(fqn, [])
                if cands:
                    did = cands[0]
                    nm, kind, flags, lmask, vnodes, tnodes = klookups["id_to_row"][did]
                    d_depth = klookups["min_depth"].get(did)
                    aux_cands = (
                        klookups["name_to_ids"].get(f"{nm}._proof_1_1")
                        or klookups["name_to_ids"].get(f"{nm}._proof_1")
                        or []
                    )
                    aux_info = None
                    if aux_cands:
                        adid = aux_cands[0]
                        anm, _, aflags, almask, avnodes, _ = klookups["id_to_row"][adid]
                        adepth = klookups["min_depth"].get(adid)
                        aux_info = {
                            "decl_id": adid,
                            "name": anm,
                            "flags": aflags,
                            "live_mask": almask,
                            "value_nodes": avnodes,
                            "min_root_depth": adepth[0] if adepth else None,
                        }
                    k_info = {
                        "decl_id": did,
                        "flags": flags,
                        "live_mask": lmask,
                        "value_nodes": vnodes,
                        "type_nodes": tnodes,
                        "min_root_depth": d_depth[0] if d_depth else None,
                        "aux_proof": aux_info,
                    }
            hit_details.append({
                "line_no": ln,
                "enclosing_kind": enc["kind"] if enc else None,
                "enclosing_fqn": fqn or None,
                "enclosing_line": enc["line_no"] if enc else None,
                "kernel": k_info,
            })

        k_mod_count = klookups["mod_decl_counts"].get(mod, 0)
        decl_live_hits = sum(1 for h in hit_details if h["kernel"] is not None)
        is_live = k_mod_count > 0 or decl_live_hits > 0
        decl_status = (
            "LIVE_IN_KERNEL"
            if decl_live_hits > 0
            else ("DEAD_IN_LIVE_MODULE" if is_live else "ABSENT_DEAD")
        )
        out.append({
            "module": mod,
            "file_path": r["file_path"],
            "lines_wc": r["lines_wc"],
            "hit_count": len(r["dk"]),
            "occurrence_count": r["dk_occ"],
            "decl_in_kernel_hits": decl_live_hits,
            "decide_kernel_in_kernel": decl_live_hits > 0,
            "status": "LIVE" if is_live else "ABSENT_DEAD",
            "decl_status": decl_status,
            "kernel_module_decls": k_mod_count,
            "zero_bucket": zero_mod_to_bucket.get(mod),
            "hits": hit_details,
        })
    return out


def _enrich_meta_inventory(
    scan_rows: List[Dict[str, Any]],
    klookups: Dict[str, Any],
    kconn: sqlite3.Connection,
) -> Dict[str, Any]:
    """Summarize all metaprogramming & code-copy constructs across 175k modules + kernel.db."""
    cats = {}
    for key in ("elab", "macro", "syntax", "run_cmd", "run_tac", "kcopy", "cpt_copy", "copy_cases", "lam_copy"):
        hits = []
        for r in scan_rows:
            lns = r[key]
            if lns:
                kcnt = klookups["mod_decl_counts"].get(r["module"], 0)
                hits.append({
                    "module": r["module"],
                    "file_path": r["file_path"],
                    "lines": lns[:20],
                    "hit_count": len(lns),
                    "kernel_module_decls": kcnt,
                })
        hits.sort(key=lambda x: (-x["hit_count"], x["module"]))
        cats[key] = {
            "file_count": len(hits),
            "total_hits": sum(h["hit_count"] for h in hits),
            "live_module_count": sum(1 for h in hits if h["kernel_module_decls"] > 0),
            "zero_kernel_module_count": sum(1 for h in hits if h["kernel_module_decls"] == 0),
            "files": hits[:65] if len(hits) <= 80 else hits[:40],
        }

    # kexactB summary (call sites vs definition)
    kex_files = [
        {
            "module": r["module"],
            "file_path": r["file_path"],
            "hit_count": r["kexactb_count"],
            "sample_lines": r["kexactb_sample"],
            "kernel_module_decls": klookups["mod_decl_counts"].get(r["module"], 0),
        }
        for r in scan_rows
        if r["kexactb_count"] > 0
    ]
    kex_files.sort(key=lambda x: (-x["hit_count"], x["module"]))
    cats["kexactB"] = {
        "file_count": len(kex_files),
        "total_hits": sum(x["hit_count"] for x in kex_files),
        "live_module_count": sum(1 for x in kex_files if x["kernel_module_decls"] > 0),
        "zero_kernel_module_count": sum(1 for x in kex_files if x["kernel_module_decls"] == 0),
        "top_files": kex_files[:25],
    }

    # Kernel-side generated targets (`CutMainCpt` *Cpt + `SideCopy` massive proof-term decls)
    cut_cpt_kernel = [
        {"id": did, "name": nm, "kind": k, "value_nodes": vn, "live_mask": lm}
        for did, nm, k, vn, lm in kconn.execute(
            "SELECT d.id, d.name, d.kind, d.value_nodes, d.live_mask "
            "FROM decl_module dm JOIN decls d ON d.id=dm.decl_id "
            "WHERE dm.method='generated:CutCptCopy' ORDER BY d.value_nodes DESC"
        ).fetchall()
    ]
    top_value_decls = [
        {
            "id": did,
            "name": nm,
            "kind": k,
            "value_nodes": vn,
            "type_nodes": tn,
            "flags": fl,
            "live_mask": lm,
            "module": klookups["decl_to_mod"].get(did),
        }
        for did, nm, k, vn, tn, fl, lm in kconn.execute(
            "SELECT id, name, kind, value_nodes, type_nodes, flags, live_mask "
            "FROM decls ORDER BY value_nodes DESC LIMIT 20"
        ).fetchall()
    ]
    return {
        "categories": cats,
        "cut_main_cpt_generated_decls": cut_cpt_kernel,
        "top_kernel_value_nodes_20": top_value_decls,
    }


def _build_certified_math_table(
    dk_entries: List[Dict[str, Any]],
    klookups: Dict[str, Any],
) -> List[Dict[str, Any]]:
    """Compile structured inventory of concrete mathematical computations checked by kernel/tactics."""
    by_mod = {e["module"]: e for e in dk_entries}

    def mod_live(mod: str) -> Tuple[str, int]:
        cnt = klookups["mod_decl_counts"].get(mod, 0)
        return ("LIVE" if cnt > 0 else "ABSENT_DEAD"), cnt

    specs = [
        (
            "Prime reciprocal table (`InvFiveLogLeSumInvPrimes`)",
            "Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes",
            301,
            "GlobalTheory.PrimeRecip.table_ok",
            "Explicit rational sum of 1/p over 12 intervals from 100 to 16900 compared against 1/(5*log p) thresholds",
            "decide +kernel",
        ),
        (
            "Chebyshev `SmallLoop` primorial/prime-count loop (`362`, `131070`)",
            "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop",
            24,
            "PI.PC.loop_run",
            "Finite 131070-step loop bound verification feeding `count_succ_le` (Chebyshev upper bound recursion)",
            "decide +kernel",
        ),
        (
            "Dyadic prime intervals `Run1..4` (`32768..131072`)",
            "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run1",
            6,
            "PI.PrimesDyadicRS.K.run1",
            "Dyadic interval prime checks imported only by unused `primes_dyadic_range` -> `counts_closed` -> `family_bound_all`",
            "decide +kernel (UNUSED in solution)",
        ),
        (
            "Padic factorial valuation ladders (`13`, `31`, `141`)",
            "Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeRecipSum",
            120,
            "Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.factorial_ladder_one_forty_one",
            "Discrete threshold inequalities across range `100..20000` (stages 13, 31, 141)",
            "decide +kernel",
        ),
        (
            "Chebyshev `lcm(1..n) <= 4^n` base cases (`n <= 100`)",
            "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumVonMangoldtLeTwoMul",
            12,
            "GlobalTheory.Mem.An.lcmUpto_le_four_pow_small",
            "Brute-force check of `lcmUpto n <= 4^n` for `0 <= n <= 100`",
            "decide +kernel",
        ),
        (
            "Chebyshev `lcm(1..n) <= 3^n` base cases (`n < 30`)",
            "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiUpperBoundOfLtThirtyMulSixPow",
            28,
            "PI.PC.lcmUpto_le_three_pow",
            "Brute-force check of `lcmUpto n <= 3^n` for `n < 30`",
            "decide +kernel",
        ),
        (
            "Cuspidal GL separation inequality primeFactors (`1..10`)",
            "Development.AbelianVarietyTheory.Proofs.CharacterTheory.SeparationNumericalIneqCuspidalGL",
            74,
            "GlobalTheory.CuspGL.sep_numerical_ineq",
            "Explicit `Nat.primeFactors` tables for `n = 2..10` inside `sep_numerical_ineq`",
            "decide +kernel",
        ),
        (
            "Bernoulli `B_4 = -1/30`, `B_6 = 1/42` (`E_4`, `E_6`, `ζ(6)`)",
            "Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsPolynomialModularJOfHasQExpansion",
            65,
            "GlobalTheory.qExpansion_E₄",
            "Explicit rational Bernoulli checks yielding `ζ(6)=π^6/945` and modular `E_4`/`E_6` q-expansions",
            "decide +kernel",
        ),
        (
            "Weak Shimura 4x4 Boolean relation SAT (`redM_key`, `redT_ex`)",
            "Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RedList",
            13,
            "_private.Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RedList.0.UpperTheory.V.Ws.redM_key",
            "Exhaustive 8-Boolean `4x4` transitive relation check feeding `red_rel`",
            "decide +kernel",
        ),
        (
            "Frobenius smooth-vector `Fin 3 -> ZMod 2` counts (`db_counts`)",
            "Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpDimb",
            77,
            "_private.Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpDimb.0.db_counts",
            "Finite cardinality lower bounds (>=4, >=2) over surjective `Fin 3 -> ZMod 2` maps",
            "decide +kernel",
        ),
        (
            "Cyclotomic `D7` concrete prime witnesses (`413718278401`, `603339156001`)",
            "Formalism.LocalRingCardinality.SpanPowerMembership.Primes",
            558,
            "Formalism.BasicNotions.Examples₂.BB_disj0",
            "Lucas primality certificates (`411` `decide` + `norm_num`) plus 5 `decide +kernel` disjointness checks feeding `SpanPowerMembership`",
            "decide +kernel + Lucas decide",
        ),
        (
            "Gaussian primes `xi` unit arithmetic (`toyPrimes`, unit check)",
            "Formalism.LocalToGlobal.Columns.ChainInst",
            1780,
            "Formalism.L2.Col.primes_over_one_mod_four",
            "Small Gaussian prime norm `mod 4 = 1` check on `toyPrimes` (unused in live proofs despite module live)",
            "decide +kernel (UNUSED decl)",
        ),
        (
            "`SL2` binomial lattice witness (`n = 13`, `24` posPairs)",
            "Formalism.PieriBlockIdeals.PieriColumnMinors.SL2BinomialLattices",
            303,
            "Formalism.CohomologicalDescent.SL2BinomialLattices.witness_thirteen",
            "Explicit positive-pair determinant witness at `k = 13`, bound `24` (unused in live proofs despite module live)",
            "decide +kernel (UNUSED decl)",
        ),
        (
            "`U(6,2)` Harish-Chandra grid sanity checks (`grid4`, `exGrid`)",
            "Development.AbelianVarietyTheory.Definitions.Foundations.UnitarySixTwoHarishChandraParameter",
            27,
            "GlobalTheory.SignedHC.Model.unitary_six_two_grid_counts",
            "Concrete interlacing and `Icc (-6:ℤ) 6` checks (unused in kernel; only `nMinus_parD` exports)",
            "decide +kernel (UNUSED decl)",
        ),
        (
            "Abelian variety `FoundationsPrimeFact` Lucas primes (`10944929`, `128860109809`, `328347841`, `1395478321`)",
            "Development.AbelianVarietyTheory.Definitions.Foundations.FoundationsPrimeFact",
            44,
            "GlobalTheory.Mem.Cert.foundations_prime_fact_ter",
            "Four concrete good/bad prime witnesses and `siteGood_prime_torsion`",
            "decide +kernel + Lucas primality",
        ),
        (
            "Cyclotomic extension explicit `438`-digit `nd2N` checks (27 checks)",
            "Formalism.LocalToGlobal.Columns.CyclotomicIsCyclotomicExtension",
            404,
            "Formalism.L2.Col.example_first_prime",
            "27 modular/divisor checks on 438-digit constant `nd2N` and prime witnesses",
            "decide +kernel",
        ),
        (
            "Chowla-Selberg Bernoulli values `B_4`, `B_6` (`12 | ...`)",
            "GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.DeltaQExpansionIntegral",
            23,
            "GroundTheory.Heights₂.Heights.ChowlaSelberg.DeltaQExpansionIntegral.qExpansion_E₄",
            "Explicit checks on `bernoulli 4`, `bernoulli 6`, and `12` divisibility",
            "decide +kernel / decide",
        ),
    ]

    table: List[Dict[str, Any]] = []
    for label, mod, line_no, sym, desc, mech in specs:
        status, kcnt = mod_live(mod)
        sym_ids = klookups["name_to_ids"].get(sym, [])
        dk_entry = by_mod.get(mod)
        decl_status = (
            "LIVE_IN_KERNEL"
            if sym_ids
            else ("DEAD_IN_LIVE_MODULE" if kcnt > 0 else "ABSENT_DEAD")
        )
        table.append({
            "label": label,
            "module": mod,
            "file_path": f"src/{mod.replace('.', '/')}.lean",
            "anchor_line": line_no,
            "symbol": sym,
            "status": status,
            "kernel_status": status,
            "decl_status": decl_status,
            "kernel_module_decls": kcnt,
            "symbol_in_kernel_decls": len(sym_ids) > 0,
            "decide_kernel_hits": dk_entry["hit_count"] if dk_entry else 0,
            "mechanism": mech,
            "mathematical_scope": desc,
        })
    return table


def run_sweep(args: argparse.Namespace) -> Dict[str, Any]:
    """Execute both corpus-wide sweeps and return the structured compute atlas."""
    t0 = time.monotonic()
    mirror_dir = Path(args.mirror)
    src_dir = mirror_dir / "src"
    kconn = connect_ro(Path(args.kernel_db))
    lconn = connect_ro(Path(args.leanre_db))
    t1conn = connect_ro(Path(args.tier1_db))

    # Load repo metadata and commit provenance
    klookups = _build_kernel_lookups(kconn)
    all_mods_rows = lconn.execute(
        "SELECT name, file_path, lines_wc, bytes, is_shim, decl_count FROM modules ORDER BY name"
    ).fetchall()
    all_mods: Dict[str, Tuple[str, int, int, int, int]] = {
        r[0]: (f"src/{r[1]}" if not r[1].startswith("src/") else r[1], r[2], r[3], r[4], r[5])
        for r in all_mods_rows
    }
    verify_rh = bool(getattr(args, "verify_rh", False))
    if verify_rh:
        assert len(all_mods) == 175187, f"Expected 175,187 modules, got {len(all_mods)}"

    main_reachable = compute_main_bfs(lconn)
    covered_mods = set(klookups["mod_decl_counts"].keys())
    zero_mods = sorted(m for m in all_mods if m not in covered_mods)
    if verify_rh:
        assert len(covered_mods) == 146283 and len(zero_mods) == 28904, (
            len(covered_mods),
            len(zero_mods),
        )

    # Parallel Sweep A: Parse all 28,904 zero-kernel modules with fixed stack parser
    zero_pairs = [(m, all_mods[m][0]) for m in zero_mods]
    chunk_z = max(1, (len(zero_pairs) + MAX_WORKERS - 1) // MAX_WORKERS)
    z_batches = [(zero_pairs[k : k + chunk_z], mirror_dir) for k in range(0, len(zero_pairs), chunk_z)]
    parsed_zero: Dict[str, Dict[str, Any]] = {}
    with concurrent.futures.ProcessPoolExecutor(max_workers=MAX_WORKERS) as pool:
        for res_batch in pool.map(_worker_parse_zero_batch, z_batches):
            for rec in res_batch:
                parsed_zero[rec["module"]] = rec

    # Anonymous-instance strict reachability + dep verification across unmatched auto-instances
    anon_matches = _verify_anon_instance_matches(parsed_zero, kconn, klookups, lconn)

    # Classify all 28,904 modules into the 6 strict, disjoint buckets
    bucket_rows: Dict[str, List[Dict[str, Any]]] = {b: [] for b in BUCKET_ORDER}
    zero_mod_to_bucket: Dict[str, str] = {}
    gap_details: Dict[str, List[Dict[str, Any]]] = {}
    gap_subcounts: Counter[str] = Counter()
    meta_subcounts: Counter[str] = Counter()
    unexp_kind_counts: Counter[str] = Counter()
    unused_tag_counts: Counter[str] = Counter()

    # Load tier1 statement_wrapper & boilerplate clone memberships for sub-breakdown
    tier1_wrapper_mods = {
        m for (m,) in t1conn.execute("SELECT module FROM module_fingerprints WHERE is_statement_wrapper=1")
    }
    clone_kind_by_mod: Dict[str, Set[str]] = defaultdict(set)
    for m, kind in t1conn.execute(
        "SELECT bm.module, bc.kind FROM boilerplate_members bm "
        "JOIN boilerplate_clusters bc ON bc.cluster_id = bm.cluster_id"
    ):
        clone_kind_by_mod[m].add(kind)

    name_to_ids = klookups["name_to_ids"]
    const_to_ids = klookups["const_to_decl_ids"]
    decl_to_mod = klookups["decl_to_mod"]
    id_to_row = klookups["id_to_row"]

    importers_adj: Dict[str, List[str]] = defaultdict(list)
    for src_m, dst_m in lconn.execute("SELECT src, dst FROM module_edges"):
        importers_adj[dst_m].append(src_m)
    trans_imp_cache: Dict[str, Set[str]] = {}

    def get_trans_imp(mod_name: str) -> Set[str]:
        if mod_name not in trans_imp_cache:
            seen_m = {mod_name}
            q_m = [mod_name]
            while q_m:
                cur_m = q_m.pop()
                for par_m in importers_adj.get(cur_m, ()):
                    if par_m not in seen_m:
                        seen_m.add(par_m)
                        q_m.append(par_m)
            trans_imp_cache[mod_name] = seen_m
        return trans_imp_cache[mod_name]

    stale_duplicate_mods: Set[str] = set()

    for m in zero_mods:
        rel_path, lines_wc, bytes_len, _is_shim, _dc = all_mods[m]
        p = parsed_zero[m]
        decls = p["decls"]
        metas = p["meta_cmds"]

        # 1. Reachability check from Main
        if m not in main_reachable:
            bkt = "module_import_unreachable"
            reason = "unreachable_from_main"
        else:
            # 2. Alignment gap check against kernel.db (`decls` / `consts` / `_private.` / anon inst)
            gaps: List[Dict[str, Any]] = []
            for d in decls:
                fqn = d["fqn"]
                if not fqn:
                    continue
                if d["is_private"]:
                    cand_names = [f"_private.{m}.0.{fqn}"]
                else:
                    cand_names = [fqn]
                    if d["kind"] in {"structure", "inductive", "class"}:
                        cand_names.extend([f"{fqn}.mk", f"{fqn}.rec"])
                found_did = None
                match_sub = ""
                for cname in cand_names:
                    ids = name_to_ids.get(cname) or const_to_ids.get(cname)
                    if ids:
                        cand_did = ids[0]
                        if cand_did not in decl_to_mod:
                            found_did = cand_did
                            match_sub = "unmatched_named_decl"
                            break
                        # For duplicate names assigned elsewhere, require a kernel dependent to import `m`
                        user_mods = {
                            decl_to_mod[src_id]
                            for (src_id,) in kconn.execute("SELECT src FROM edges WHERE dst=?", (cand_did,))
                            if src_id in decl_to_mod
                        }
                        if user_mods and (user_mods & get_trans_imp(m)):
                            found_did = cand_did
                            match_sub = "duplicate_decl_name_shadowed"
                            break
                        stale_duplicate_mods.add(m)
                if found_did is not None:
                    row = id_to_row[found_did]
                    gaps.append({
                        "reason": match_sub,
                        "kernel_decl_id": found_did,
                        "kernel_name": row[0],
                        "kernel_live_mask": row[3],
                        "assigned_module": decl_to_mod.get(found_did),
                        "line_no": d["line_no"],
                    })
            if not gaps and m in anon_matches:
                gaps.extend(anon_matches[m])

            if gaps:
                bkt = "alignment_gap"
                reason = gaps[0]["reason"]
                gap_details[m] = gaps
                gap_subcounts[reason] += 1
            elif not decls and not metas:
                # 3. Import shim / re-export only
                bkt = "import_shim_reexport"
                reason = "leanre_is_shim" if _is_shim else "import_open_export_ns_only"
            else:
                non_meta_decls = [d for d in decls if not d["is_meta_def"]]
                if metas and not non_meta_decls:
                    # 4. Macro / tactic / elab / syntax / attribute only
                    bkt = "macro_tactic_elab_syntax_only"
                    top_meta = metas[0][0]
                    reason = f"meta_only_{top_meta}"
                    meta_subcounts[top_meta] += 1
                elif non_meta_decls and all(
                    d["is_private"]
                    or d["is_inline"]
                    or d["kind"] in {"instance", "abbrev", "structure", "class"}
                    for d in non_meta_decls
                ):
                    # 5. Only private / @[inline] / instance / abbrev / structure / class
                    bkt = "unexported_private_or_inline"
                    kinds = sorted({
                        ("private" if d["is_private"] else ("inline" if d["is_inline"] else d["kind"]))
                        for d in non_meta_decls
                    })
                    reason = "+".join(kinds[:3])
                    for k in kinds:
                        unexp_kind_counts[k] += 1
                else:
                    # 6. Imported by Main, declares theorems/defs/inductives, yet 0 in kernel
                    bkt = "imported_but_unused_by_kernel"
                    if m in tier1_wrapper_mods:
                        reason = "statement_wrapper_unused"
                    elif clone_kind_by_mod.get(m):
                        reason = "clone_" + sorted(clone_kind_by_mod[m])[0]
                    elif not non_meta_decls and not metas:
                        reason = "empty_parse"
                    else:
                        reason = "unused_theorem_or_def"
                    if m in stale_duplicate_mods:
                        unused_tag_counts["stale_duplicate_decl_unused"] += 1
                    if m in tier1_wrapper_mods:
                        unused_tag_counts["statement_wrapper"] += 1
                    for ck in clone_kind_by_mod.get(m, ()):
                        unused_tag_counts[f"boilerplate_{ck}"] += 1
                    if m not in tier1_wrapper_mods and not clone_kind_by_mod.get(m):
                        unused_tag_counts["unique_non_wrapper_theorems_or_defs"] += 1

        row_rec = {
            "module": m,
            "file_path": rel_path,
            "lines_wc": lines_wc,
            "bytes": bytes_len,
            "reason": reason,
        }
        bucket_rows[bkt].append(row_rec)
        zero_mod_to_bucket[m] = bkt

    # Verify strict completeness and disjointness invariants
    total_bkt_mods = sum(len(v) for v in bucket_rows.values())
    total_bkt_lines = sum(r["lines_wc"] for v in bucket_rows.values() for r in v)
    expected_zero_lines = sum(all_mods[m][1] for m in zero_mods)
    assert total_bkt_mods == len(zero_mods), f"Bucket sum {total_bkt_mods} != {len(zero_mods)}"
    assert total_bkt_lines == expected_zero_lines, f"Line sum {total_bkt_lines} != {expected_zero_lines}"
    assert len(zero_mod_to_bucket) == len(zero_mods)
    if verify_rh:
        assert total_bkt_mods == 28904, f"RH bucket sum {total_bkt_mods} != 28904"

    # Parallel Sweep B: Computation & Meta sweep across ALL modules
    all_pairs = [(m, all_mods[m][0]) for m in sorted(all_mods)]
    chunk_a = max(1, (len(all_pairs) + MAX_WORKERS - 1) // MAX_WORKERS)
    a_batches = [(all_pairs[k : k + chunk_a], mirror_dir) for k in range(0, len(all_pairs), chunk_a)]
    scan_rows: List[Dict[str, Any]] = []
    with concurrent.futures.ProcessPoolExecutor(max_workers=MAX_WORKERS) as pool:
        for res_batch in pool.map(_worker_scan_batch, a_batches):
            scan_rows.extend(res_batch)

    assert len(scan_rows) == len(all_mods)

    # Aggregate computation summaries (LIVE vs ABSENT_DEAD)
    def summarize_metric(pred, count_fn) -> Dict[str, Any]:
        files = [r for r in scan_rows if pred(r)]
        live = [r for r in files if r["module"] in covered_mods]
        dead = [r for r in files if r["module"] not in covered_mods]
        return {
            "files": len(files),
            "total_hits": sum(count_fn(r) for r in files),
            "live_files": len(live),
            "live_hits": sum(count_fn(r) for r in live),
            "dead_files": len(dead),
            "dead_hits": sum(count_fn(r) for r in dead),
            "total_lines_wc": sum(r["lines_wc"] for r in files),
        }

    dk_entries = _enrich_decide_kernel_records(scan_rows, mirror_dir, klookups, zero_mod_to_bucket)
    meta_inventory = _enrich_meta_inventory(scan_rows, klookups, kconn)
    dyadic_chain = _trace_dyadic_chain(lconn, klookups, zero_mod_to_bucket)
    export_sem = _collect_export_semantics(kconn, lconn)
    spot_checks = _build_spot_checks(bucket_rows, parsed_zero, gap_details, target_n=32)
    cert_table = _build_certified_math_table(dk_entries, klookups)

    # Top giant norm_num files and rfl/numeric table files
    norm_files = [r for r in scan_rows if r["norm_count"] > 0]
    giant_norm = sorted(
        [r for r in norm_files if r["norm_count"] >= 40],
        key=lambda x: (-x["norm_count"], -x["lines_wc"]),
    )
    giant_norm_list = [
        {
            "module": r["module"],
            "file_path": r["file_path"],
            "lines_wc": r["lines_wc"],
            "norm_num_hits": r["norm_count"],
            "status": "LIVE" if r["module"] in covered_mods else "ABSENT_DEAD",
            "kernel_module_decls": klookups["mod_decl_counts"].get(r["module"], 0),
        }
        for r in giant_norm[:40]
    ]

    numeric_table_files = sorted(
        [
            r
            for r in scan_rows
            if (r["big_int_count"] >= 2 or r["range_compute_count"] >= 2 or (r["dk"] and r["lines_wc"] >= 40))
            and (r["rfl_count"] > 0 or r["dk"] or r["dp_count"] > 0 or r["big_int_count"] >= 2)
        ],
        key=lambda x: (-(x["big_int_count"] + x["range_compute_count"] * 2 + len(x["dk"]) * 5), x["module"]),
    )
    numeric_table_list = [
        {
            "module": r["module"],
            "file_path": r["file_path"],
            "lines_wc": r["lines_wc"],
            "status": "LIVE" if r["module"] in covered_mods else "ABSENT_DEAD",
            "decide_kernel_hits": len(r["dk"]),
            "decide_plain_hits": r["dp_count"],
            "rfl_hits": r["rfl_count"],
            "big_int_literals_ge18d": r["big_int_count"],
            "range_compute_hits": r["range_compute_count"],
            "kernel_module_decls": klookups["mod_decl_counts"].get(r["module"], 0),
        }
        for r in numeric_table_files[:45]
    ]

    decide_plain_top = [
        {
            "module": r["module"],
            "file_path": r["file_path"],
            "lines_wc": r["lines_wc"],
            "decide_plain_hits": r["dp_count"],
            "status": "LIVE" if r["module"] in covered_mods else "ABSENT_DEAD",
            "kernel_module_decls": klookups["mod_decl_counts"].get(r["module"], 0),
        }
        for r in sorted([r for r in scan_rows if r["dp_count"] > 0], key=lambda x: (-x["dp_count"], x["module"]))[:35]
    ]

    # Kernel flags distribution across live/all kernel.db decls
    flag_stats = {}
    for bit, name in [
        (1, "F_REFL_TRUE"),
        (2, "F_OF_DECIDE"),
        (4, "F_REDUCE_BOOL"),
        (8, "F_REDUCE_NAT"),
        (16, "F_SORRY"),
        (32, "F_TRUST_COMPILER"),
    ]:
        cnt_all = kconn.execute(f"SELECT COUNT(*) FROM decls WHERE (flags & {bit}) != 0").fetchone()[0]
        cnt_live = kconn.execute(
            f"SELECT COUNT(*) FROM decls WHERE live_mask != 0 AND (flags & {bit}) != 0"
        ).fetchone()[0]
        flag_stats[name] = {"bit": bit, "all_decls": cnt_all, "live_decls": cnt_live}

    top_of_decide = [
        {
            "id": did,
            "name": nm,
            "kind": k,
            "value_nodes": vn,
            "flags": fl,
            "live_mask": lm,
            "module": klookups["decl_to_mod"].get(did),
        }
        for did, nm, k, vn, fl, lm in kconn.execute(
            "SELECT id, name, kind, value_nodes, flags, live_mask FROM decls "
            "WHERE (flags & 2) != 0 ORDER BY value_nodes DESC LIMIT 30"
        ).fetchall()
    ]

    # Build bucket summaries for JSON
    bucket_summaries = {}
    for bkt in BUCKET_ORDER:
        rows = bucket_rows[bkt]
        binfo: Dict[str, Any] = {
            "modules": len(rows),
            "pct_of_zero": round(100.0 * len(rows) / max(1, len(zero_mods)), 4),
            "pct_of_corpus": round(100.0 * len(rows) / max(1, len(all_mods)), 4),
            "lines_wc": sum(r["lines_wc"] for r in rows),
            "bytes": sum(r["bytes"] for r in rows),
            "top_folders_l1": _top_folders(rows, depth=1, limit=10),
            "top_folders_l2": _top_folders(rows, depth=2, limit=12),
        }
        if bkt == "alignment_gap":
            binfo["subreasons"] = dict(gap_subcounts)
            binfo["all_modules"] = [
                {
                    "module": r["module"],
                    "file_path": r["file_path"],
                    "lines_wc": r["lines_wc"],
                    "reason": r["reason"],
                    "matches": gap_details[r["module"]][:5],
                }
                for r in sorted(rows, key=lambda x: x["module"])
            ]
        elif bkt == "macro_tactic_elab_syntax_only":
            binfo["subreasons"] = dict(meta_subcounts)
            binfo["all_modules"] = [
                {"module": r["module"], "file_path": r["file_path"], "lines_wc": r["lines_wc"], "reason": r["reason"]}
                for r in sorted(rows, key=lambda x: x["module"])
            ]
        elif bkt == "unexported_private_or_inline":
            binfo["kind_breakdown"] = dict(unexp_kind_counts)
            binfo["sample_modules"] = [
                {"module": r["module"], "file_path": r["file_path"], "lines_wc": r["lines_wc"], "reason": r["reason"]}
                for r in sorted(rows, key=lambda x: -x["lines_wc"])[:40]
            ]
        elif bkt == "import_shim_reexport":
            binfo["reason_breakdown"] = dict(Counter(r["reason"] for r in rows))
        elif bkt == "imported_but_unused_by_kernel":
            binfo["sub_classification"] = dict(unused_tag_counts)
            binfo["largest_modules_top30"] = [
                {"module": r["module"], "file_path": r["file_path"], "lines_wc": r["lines_wc"], "reason": r["reason"]}
                for r in sorted(rows, key=lambda x: -x["lines_wc"])[:30]
            ]
        bucket_summaries[bkt] = binfo

    total_corpus_lines_wc = sum(v[1] for v in all_mods.values())
    total_live_lines_wc = sum(all_mods[m][1] for m in covered_mods)

    kmeta_input = json.loads(
        kconn.execute("SELECT value_json FROM meta WHERE key='input'").fetchone()[0]
    )
    kmeta_sha = kmeta_input.get("uncompressed_sha256", "")
    elapsed = round(time.monotonic() - t0, 2)

    atlas = {
        "schema": "leanre.compute_atlas/1",
        "epistemic_layers": {
            "Layer 1": "Lean 4 kernel validity (verified locally against solution.ndjson.zst / outputs/kernel/kernel.db)",
            "Layer 2": "Spec, TCB & definition fidelity (audited in Gate D3; kernel presence does not certify informal meaning)",
            "Layer 3": "Human comprehension & proof architecture (module graph, zero-kernel taxonomy, computation inventory)",
            "Layer 4": "Mathematical peer consensus (outside this repository's scope)",
        },
        "provenance_legend": {
            "L": "Extracted or verified locally from pinned inputs (solution.ndjson.zst / kernel.db, leanre.db, tier1.db, data/rh_mirror/src)",
            "A": "Author prose (remark.pdf)",
            "C": "Third-party claim (e.g., Sutherland / lean4lean reports)",
            "S": "Standard published mathematics",
            "M": "CS/RE analogy (with where it breaks) or AI-draft heuristic",
        },
        "target": {
            "repo_mirror": "Deicyde/riemann-hypothesis@40e56bab",
            "ndjson_uncompressed_sha256": kmeta_sha,
            "generated_elapsed_s": elapsed,
            "workers": MAX_WORKERS,
        },
        "corpus_totals": {
            "total_modules": len(all_mods),
            "total_lines_wc": total_corpus_lines_wc,
            "main_reachable_modules": len(main_reachable),
            "main_unreachable_modules": len(all_mods) - len(main_reachable),
            "kernel_covered_modules": len(covered_mods),
            "kernel_covered_lines_wc": total_live_lines_wc,
            "zero_kernel_modules": len(zero_mods),
            "zero_kernel_lines_wc": expected_zero_lines,
        },
        "zero_kernel_classification": {
            "bucket_sum_modules": total_bkt_mods,
            "bucket_sum_lines_wc": total_bkt_lines,
            "strictly_disjoint": True,
            "buckets": bucket_summaries,
            "lean4_export_semantics_proof": export_sem,
            "dyadic_prime_intervals_chain": dyadic_chain,
            "spot_checks_per_bucket": spot_checks,
        },
        "computation_atlas": {
            "kernel_flag_counts": flag_stats,
            "source_tactic_summaries": {
                "decide_kernel": {
                    **summarize_metric(lambda r: bool(r["dk"]), lambda r: len(r["dk"])),
                    "total_occurrences": sum(r["dk_occ"] for r in scan_rows),
                    "live_occurrences": sum(r["dk_occ"] for r in scan_rows if r["module"] in covered_mods),
                    "dead_occurrences": sum(r["dk_occ"] for r in scan_rows if r["module"] not in covered_mods),
                },
                "decide_plain": summarize_metric(lambda r: r["dp_count"] > 0, lambda r: r["dp_count"]),
                "decide_cbv": summarize_metric(lambda r: r["d_cbv_count"] > 0, lambda r: r["d_cbv_count"]),
                "native_decide": summarize_metric(lambda r: bool(r["native"]), lambda r: len(r["native"])),
                "norm_num": summarize_metric(lambda r: r["norm_count"] > 0, lambda r: r["norm_count"]),
                "norm_num_giant_ge40": summarize_metric(lambda r: r["norm_count"] >= 40, lambda r: r["norm_count"]),
                "rfl": summarize_metric(lambda r: r["rfl_count"] > 0, lambda r: r["rfl_count"]),
            },
            "decide_kernel_decl_breakdown": {
                "live_in_kernel_files": sum(1 for e in dk_entries if e["decl_status"] == "LIVE_IN_KERNEL"),
                "live_in_kernel_hits": sum(e["decl_in_kernel_hits"] for e in dk_entries),
                "dead_in_live_module_files": sum(1 for e in dk_entries if e["decl_status"] == "DEAD_IN_LIVE_MODULE"),
                "dead_in_live_module_hits": sum(
                    e["hit_count"] for e in dk_entries if e["decl_status"] == "DEAD_IN_LIVE_MODULE"
                ),
                "absent_dead_files": sum(1 for e in dk_entries if e["decl_status"] == "ABSENT_DEAD"),
                "absent_dead_hits": sum(
                    e["hit_count"] for e in dk_entries if e["decl_status"] == "ABSENT_DEAD"
                ),
            },
            "decide_kernel_all_files": dk_entries,
            "decide_plain_top_files": decide_plain_top,
            "norm_num_giant_top_files": giant_norm_list,
            "numeric_table_and_rfl_top_files": numeric_table_list,
            "top_kernel_f_of_decide_decls": top_of_decide,
            "metaprogramming_and_copy_macros": meta_inventory,
            "certified_math_table": cert_table,
        },
    }

    kconn.close()
    lconn.close()
    t1conn.close()
    return atlas


def run_selftest() -> None:
    """Self-test fixed parser, stack scoping, instance priority parsing, and invariants."""
    # 1. Multi-component namespace `end C` bug fix (KillPoly.lean pattern)
    src_ns = """
namespace PositivityTheory.Rg.Rs
theorem inside_rs : True := trivial
end Rs
theorem inside_rg : True := trivial
end PositivityTheory.Rg
theorem at_root : True := trivial
"""
    p_ns = parse_module_decls_and_meta(src_ns, "Test.KillPoly")
    fqns = [d["fqn"] for d in p_ns["decls"]]
    assert fqns == [
        "PositivityTheory.Rg.Rs.inside_rs",
        "PositivityTheory.Rg.inside_rg",
        "at_root",
    ], f"Namespace end-pop failed: {fqns}"

    # 2. `instance (priority := 200) name` and anonymous instance target extraction
    src_inst = """
namespace Foo.Bar
instance (priority := 200) rules0 : Prop := True
instance : Infinite Nat := inferInstance
private def helper : Nat := 1
@[inline] def fast_id (x : Nat) := x
end Foo.Bar
"""
    p_inst = parse_module_decls_and_meta(src_inst, "Test.RulInst")
    decls = p_inst["decls"]
    assert len(decls) == 4, decls
    assert decls[0]["fqn"] == "Foo.Bar.rules0" and decls[0]["kind"] == "instance"
    assert decls[1]["is_anon_instance"] and decls[1]["target_class"] == "Infinite", decls[1]
    assert decls[2]["is_private"] and decls[2]["fqn"] == "Foo.Bar.helper"
    assert decls[3]["is_inline"] and decls[3]["fqn"] == "Foo.Bar.fast_id"

    # 3. Meta-only vs shim vs private classification logic
    src_meta = """
import Lean
open Lean Elab Command
elab "my_elab" : command => pure ()
private def helperCore (x : Lean.Syntax) : Lean.Elab.Command.CommandElabM Unit := pure ()
"""
    p_meta = parse_module_decls_and_meta(src_meta, "Test.MetaOnly")
    assert len(p_meta["meta_cmds"]) == 1 and p_meta["meta_cmds"][0][0] == "elab"
    assert p_meta["decls"][0]["is_meta_def"], p_meta["decls"]

    src_shim = """
import Mathlib
import Foo.Bar
export Foo (baz)
"""
    p_shim = parse_module_decls_and_meta(src_shim, "Test.Shim")
    assert not p_shim["decls"] and not p_shim["meta_cmds"]

    print("SELFTEST PASS (namespace-end stack, instance-priority, anon-class, meta-vs-shim)")


def verify_atlas(atlas_path: Path, *, verify_rh: bool = False) -> None:
    """Verify invariants and size/leak constraints on `compute_atlas.json`.

    RH-specific corpus counts (`175,187`, `28,904`, Dyadic/Chebyshev checks) are
    enforced only when ``verify_rh=True`` (``--verify-rh``).
    """
    raw = atlas_path.read_text(encoding="utf-8")
    sz = len(raw.encode("utf-8"))
    assert sz < 2 * 1024 * 1024, f"compute_atlas.json too large: {sz} B"
    data = json.loads(raw)
    assert data["schema"] == "leanre.compute_atlas/1"
    tot = data["corpus_totals"]
    zk = data["zero_kernel_classification"]
    total_mods = tot["total_modules"]
    zero_mods_n = tot["zero_kernel_modules"]
    assert tot["kernel_covered_modules"] + zero_mods_n == total_mods
    assert zk["bucket_sum_modules"] == zero_mods_n
    assert sum(zk["buckets"][b]["modules"] for b in BUCKET_ORDER) == zero_mods_n
    assert sum(zk["buckets"][b]["lines_wc"] for b in BUCKET_ORDER) == zk["bucket_sum_lines_wc"]
    for b in BUCKET_ORDER:
        cnt = zk["buckets"][b]["modules"]
        sc = len(zk["spot_checks_per_bucket"][b])
        if cnt >= 30:
            assert sc >= 30, f"Bucket {b} has {sc} spot checks (<30)"
        else:
            assert sc == cnt, f"Bucket {b} has {sc} spot checks != {cnt}"
    if verify_rh:
        assert total_mods == 175187, f"Expected 175,187 RH modules, got {total_mods}"
        assert zero_mods_n == 28904, f"Expected 28,904 RH zero-kernel modules, got {zero_mods_n}"
        ca = data["computation_atlas"]
        assert ca["source_tactic_summaries"]["native_decide"]["total_hits"] == 0
        assert zk["dyadic_prime_intervals_chain"]["dyadic_all_6_files_zero_kernel"] is True
        assert zk["dyadic_prime_intervals_chain"]["chebyshev_smallloop_live_count"] == 9
        print(f"VERIFY-RH PASS ({sz:,} B < 2 MB, 6 buckets sum=28,904, all spot-checks & RH invariants OK)")
    else:
        print(f"VERIFY PASS ({sz:,} B < 2 MB, modules={total_mods:,}, zero_kernel={zero_mods_n:,}, invariants OK)")


def main() -> None:
    ap = argparse.ArgumentParser(description="Phase 4 Computation & Dead-Code Archaeology sweep.")
    ap.add_argument("--mirror", default=str(DEFAULT_MIRROR))
    ap.add_argument("--kernel-db", default=str(DEFAULT_KERNEL_DB))
    ap.add_argument("--leanre-db", default=str(DEFAULT_LEANRE_DB))
    ap.add_argument("--tier1-db", default=str(DEFAULT_TIER1_DB))
    ap.add_argument("--json-out", default=str(DEFAULT_OUT_JSON))
    ap.add_argument("--selftest", action="store_true", help="Run fast parser/logic unit checks and exit.")
    ap.add_argument("--verify", action="store_true", help="Verify generic compute_atlas.json invariants.")
    ap.add_argument(
        "--verify-rh",
        action="store_true",
        help="Verify RH-specific 175,187 / 28,904 corpus invariants on compute_atlas.json.",
    )
    args = ap.parse_args()

    if args.selftest:
        run_selftest()
        return

    out_path = Path(args.json_out)
    verify_only = (args.verify or args.verify_rh) and out_path.exists()
    if not verify_only:
        atlas = run_sweep(args)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(atlas, indent=2) + "\n", encoding="utf-8")
        print(
            f"Wrote {out_path} ({out_path.stat().st_size:,} B) in {atlas['target']['generated_elapsed_s']}s"
        )
    if args.verify or args.verify_rh:
        verify_atlas(out_path, verify_rh=args.verify_rh)


if __name__ == "__main__":
    main()
