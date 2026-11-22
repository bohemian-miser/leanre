#!/usr/bin/env python3
"""leanre.trim — Read-only, deterministic virtual proof stripper & bloat waterfall.

Quantifies disjoint, non-double-counted virtual reductions across both the physical
`.lean` source tree (`175,187` modules / `17,374,215` `wc -l` lines at `40e56bab`)
and the kernel declaration DAG (`outputs/kernel/kernel.db` from `solution.ndjson.zst`),
cross-referenced against `outputs/leanre.db` and `outputs/flirt/tier1.db`.

Guardrails & Invariants:
  - Strictly read-only (`mode=ro`) on all SQLite inputs; never mutates mirror or DBs.
  - Hard thread/worker cap `<= 16` (`MAX_WORKERS = 16`).
  - Zero raw `.lean` proof bodies or absolute home paths emitted in reports.
  - Every waterfall step satisfies exact conservation (`before - removed == after`)
    with explicit provenance tags (`[L]` exact vs `[L-approx]` declaration line spans).
"""
from __future__ import annotations

import argparse
import collections
import json
import multiprocessing
import os
import re
import sqlite3
import sys
import time
from pathlib import Path
from typing import Any, Counter, Dict, Iterable, List, Optional, Sequence, Set, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import sighash  # noqa: E402

SCHEMA_VERSION = "leanre.trim/1"
MAX_WORKERS = 16

DEFAULT_SRC = os.path.join(_REPO_ROOT, "data", "rh_mirror", "src")
DEFAULT_KERNEL_DB = os.path.join(_REPO_ROOT, "outputs", "kernel", "kernel.db")
DEFAULT_LEANRE_DB = os.path.join(_REPO_ROOT, "outputs", "leanre.db")
DEFAULT_TIER1_DB = os.path.join(_REPO_ROOT, "outputs", "flirt", "tier1.db")
DEFAULT_COMPUTE_ATLAS = os.path.join(_REPO_ROOT, "outputs", "decomp", "compute_atlas.json")
DEFAULT_OUT_REPORT = os.path.join(_REPO_ROOT, "outputs", "decomp", "trim_report.json")

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
STD_IMPORT_HEADS = frozenset({
    "Mathlib", "Lean", "Batteries", "Std", "Init", "Aesop", "Qq", "ProofWidgets", "ImportGraph", "Cli",
})

_RE_IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z_][^\s]*)")
_RE_NS = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.'₀-₉ₐ-ₜ]*)")
_RE_SEC = re.compile(r"^section(?:\s+([A-Za-z_][A-Za-z0-9_.'₀-₉ₐ-ₜ]*))?\b")
_RE_END = re.compile(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_.'₀-₉ₐ-ₜ]*))?\b")
_RE_AUX_NAME = re.compile(r"\._(?:proof|simp|cstage|closed)_\d|\.(?:match|eq)_\d+$")
_RE_LEAN_META = re.compile(
    r"\b(?:Lean\.(?:Elab|Meta|Parser|Syntax)|CoreM|MetaM|TacticM|CommandElab|TermElab|MacroM|Environment|Expr|ConstantInfo|NameSet|NameMap|Name)\b"
)
_RE_COPY_CASES = re.compile(r"\bcopy_cases\b")
_RE_LAM_SIG_COPY = re.compile(r"\b(?:lam_copy|sigSpan_copy)\b")
_RE_CPT_COPY = re.compile(r"\bcpt_copy_thms\b")
_RE_KCOPY = re.compile(r"\bkcopy\b")


def clamp_workers(workers: Optional[int]) -> int:
    """Enforce hard worker cap `1 <= workers <= MAX_WORKERS (16)`."""
    if workers is None:
        return MAX_WORKERS
    return max(1, min(int(workers), MAX_WORKERS))


def connect_ro(path: str) -> sqlite3.Connection:
    """Open an existing SQLite database strictly in read-only URI mode (`mode=ro`)."""
    ap = os.path.abspath(path)
    if not os.path.isfile(ap):
        raise FileNotFoundError(f"Missing SQLite database: {path}")
    return sqlite3.connect(f"file:{ap}?mode=ro", uri=True)


def _rel_repo_path(path: str) -> str:
    """Format a path relative to repository root so no host/home path leaks."""
    ap = os.path.abspath(path)
    try:
        rel = os.path.relpath(ap, _REPO_ROOT)
        if not rel.startswith(".."):
            return rel.replace(os.sep, "/")
    except ValueError:
        pass
    return os.path.basename(ap)


def _strip_leading_attrs_and_mods(stmt: str) -> Tuple[str, List[str], List[str]]:
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
    if not ns_stack:
        return
    if not end_arg:
        ns_stack.pop()
        return
    rem = end_arg.split(".")
    while rem and ns_stack:
        kind, parts = ns_stack[-1]
        if kind == "mutual" or not parts:
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
    comps: List[str] = []
    for kind, parts in ns_stack:
        if kind == "ns":
            comps.extend(parts)
    return ".".join(comps)


def _normalize_fqn(cur_ns: str, raw_name: str) -> str:
    if not raw_name or raw_name == "_":
        return ""
    if raw_name.startswith("_root_."):
        return raw_name[7:]
    fqn = f"{cur_ns}.{raw_name}" if cur_ns else raw_name
    if fqn.startswith("_root_."):
        fqn = fqn[7:]
    if "._root_." in fqn:
        fqn = fqn.split("._root_.", 1)[1]
    return fqn


def _extract_instance_target_class(sig_tail: str) -> str:
    head = re.split(r"(?:\s:=\s|\bwhere\b)", sig_tail, maxsplit=1)[0]
    depth = 0
    in_str = False
    colon_idx = -1
    for i, ch in enumerate(head):
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
    if colon_idx < 0:
        return ""
    rhs = head[colon_idx + 1 :].strip()
    rhs = re.sub(r"^(?:∀\s+[^,]+,\s*)+", "", rhs).strip()
    m = re.match(r"([A-Za-z_][A-Za-z0-9_.']*)", rhs)
    if not m:
        return ""
    return m.group(1).rsplit(".", 1)[-1]


def parse_lean_file_for_trim(raw_bytes: bytes, module_name: str, rel_path: str) -> Dict[str, Any]:
    """Parse imports, scaffolding, meta commands, and disjoint declaration line spans.

    Every declaration receives a deterministic, pairwise-disjoint line span:
      - `start_line`: 1-based starting line (including any attached `@[...]` attributes)
      - `trimmed_end`: 1-based last non-blank line before the next top-level item
      - `block_end`: 1-based line immediately before the next top-level item (includes
        trailing blank separator lines belonging to that declaration block)
    """
    lines_wc = raw_bytes.count(b"\n")
    bytes_len = len(raw_bytes)
    text = raw_bytes.decode("utf-8", errors="replace")
    raw_lines = text.splitlines()
    stripped = sighash.strip_comments(text)
    slines = stripped.splitlines()
    n = len(slines)

    # Byte lengths per 1-based line (including `\n` when present)
    line_byte_lens = [len(ln.encode("utf-8", errors="replace")) + 1 for ln in raw_lines]
    if raw_lines and not raw_bytes.endswith(b"\n"):
        line_byte_lens[-1] -= 1
    prefix_bytes = [0] * (len(line_byte_lens) + 1)
    for idx_b, bl in enumerate(line_byte_lens):
        prefix_bytes[idx_b + 1] = prefix_bytes[idx_b] + bl

    ns_stack: List[Tuple[str, List[str]]] = []
    raw_imports: List[str] = []
    has_non_import_code = False
    imports_lean_meta = False
    shim_cmds = 0
    meta_cmd_count = 0

    # Top-level items recorded as `(start_line_1based, item_type, payload)`
    # where `item_type` is "import", "scaffolding", "meta", or "decl".
    top_boundaries: List[int] = []
    raw_decls: List[Dict[str, Any]] = []

    copy_cases_lines: List[int] = []
    lam_sig_copy_lines: List[int] = []
    cpt_copy_lines: List[int] = []
    kcopy_lines: List[int] = []
    for idx_c, cln in enumerate(slines, 1):
        if "copy_cases" in cln and _RE_COPY_CASES.search(cln):
            copy_cases_lines.append(idx_c)
        if ("lam_copy" in cln or "sigSpan_copy" in cln) and _RE_LAM_SIG_COPY.search(cln):
            lam_sig_copy_lines.append(idx_c)
        if "cpt_copy_thms" in cln and _RE_CPT_COPY.search(cln):
            cpt_copy_lines.append(idx_c)
        if "kcopy" in cln and _RE_KCOPY.search(cln):
            kcopy_lines.append(idx_c)

    i = 0
    while i < n:
        line_raw = slines[i]
        s = line_raw.strip()
        if not s:
            i += 1
            continue

        m_imp = _RE_IMPORT.match(line_raw)
        if m_imp and (line_raw[0] not in (" ", "\t") or not has_non_import_code):
            imp = m_imp.group(1)
            raw_imports.append(imp)
            if imp == "Lean" or imp.startswith("Lean."):
                imports_lean_meta = True
            shim_cmds += 1
            top_boundaries.append(i + 1)
            i += 1
            continue

        has_non_import_code = True

        m_ns = _RE_NS.match(s)
        if m_ns and (not line_raw[0].isspace() or ns_stack):
            ns_stack.append(("ns", m_ns.group(1).split(".")))
            shim_cmds += 1
            top_boundaries.append(i + 1)
            i += 1
            continue

        m_sec = _RE_SEC.match(s)
        if m_sec and (not line_raw[0].isspace() or ns_stack):
            sec_name = [m_sec.group(1)] if m_sec.group(1) else []
            ns_stack.append(("sec", sec_name))
            shim_cmds += 1
            top_boundaries.append(i + 1)
            i += 1
            continue

        if s == "mutual" and (not line_raw[0].isspace() or ns_stack):
            ns_stack.append(("mutual", []))
            shim_cmds += 1
            top_boundaries.append(i + 1)
            i += 1
            continue

        m_end = _RE_END.match(s)
        if m_end and (s == "end" or re.match(r"^end\s+[A-Za-z_]", s)) and (not line_raw[0].isspace() or ns_stack):
            _pop_end_stack(ns_stack, m_end.group(1))
            shim_cmds += 1
            top_boundaries.append(i + 1)
            i += 1
            continue

        if re.match(r"^open\b", s) and any(
            tok in ("Lean", "Meta", "Elab", "Lean.Elab", "Lean.Meta", "Lean.Parser")
            for tok in s.split()
        ):
            imports_lean_meta = True

        indent = len(line_raw) - len(line_raw.lstrip(" "))
        if indent == 0 or (ns_stack and indent <= 2):
            rest, attrs, mods = _strip_leading_attrs_and_mods(s)
            if not rest and s.startswith("@["):
                hdr, next_i = sighash._header_extent(slines, i, max_lines=80)
                rest, attrs, mods = _strip_leading_attrs_and_mods(hdr)
                cand_end = next_i
            else:
                hdr = s
                cand_end = i + 1

            first_tok_m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\b", rest)
            first_tok = first_tok_m.group(1) if first_tok_m else ""

            if first_tok in META_ONLY_KEYWORDS and (indent == 0 or ns_stack):
                meta_cmd_count += 1
                top_boundaries.append(i + 1)
                i = max(i + 1, cand_end)
                continue

            if first_tok in SHIM_SKIP_KEYWORDS and (indent == 0 or ns_stack):
                shim_cmds += 1
                top_boundaries.append(i + 1)
                if first_tok in ("variable", "variables"):
                    _, var_end = sighash._header_extent(slines, i, max_lines=60)
                    i = max(i + 1, var_end)
                else:
                    i = max(i + 1, cand_end)
                continue

            if first_tok in DECL_KINDS and (indent == 0 or ns_stack):
                kind = first_tok
                tail_after_kw = rest[len(first_tok) :].lstrip()
                if kind == "class" and tail_after_kw.startswith(("inductive ", "abbrev ")):
                    sub_kw, tail_after_kw = tail_after_kw.split(None, 1)
                    tail_after_kw = tail_after_kw.lstrip()
                    if sub_kw == "inductive":
                        kind = "inductive"
                # Peel optional `(priority := ...)` before instance name
                if kind == "instance" and tail_after_kw.startswith("("):
                    p_depth = 0
                    p_idx = 0
                    while p_idx < len(tail_after_kw):
                        if tail_after_kw[p_idx] == "(":
                            p_depth += 1
                        elif tail_after_kw[p_idx] == ")":
                            p_depth -= 1
                            if p_depth == 0:
                                p_idx += 1
                                break
                        p_idx += 1
                    cand_p = tail_after_kw[:p_idx]
                    if "priority" in cand_p:
                        tail_after_kw = tail_after_kw[p_idx:].lstrip()

                # Extract declaration name (supports `_root_.Foo.bar`, primes, unicode subscripts)
                nm_m = re.match(r"^([A-Za-z_][A-Za-z0-9_.'₀-₉ₐ-ₜ]*)", tail_after_kw)
                raw_name = nm_m.group(1).rstrip(".") if nm_m else ""
                if raw_name in ("where", "with", "by", "in", "extending", "extends"):
                    raw_name = ""

                is_private = "private" in mods
                attr_text = " ".join(attrs)
                is_inline = bool(re.search(r"\binline\b", attr_text))
                is_anon = kind == "instance" and (not raw_name or raw_name == "_")
                cur_ns = _current_ns(ns_stack)
                fqn = "" if is_anon else _normalize_fqn(cur_ns, raw_name)

                hdr_full = hdr
                next_i = cand_end
                is_partial_def = "partial" in mods and kind in {"def", "abbrev"}
                if is_anon or ((imports_lean_meta or is_partial_def) and kind in {"def", "abbrev"}):
                    if cand_end == i + 1:
                        hdr_full, next_i = sighash._header_extent(slines, i, max_lines=120)

                is_meta_def = bool(
                    (imports_lean_meta or is_partial_def)
                    and kind in {"def", "abbrev"}
                    and bool(_RE_LEAN_META.search(hdr_full))
                )
                target_cls = _extract_instance_target_class(hdr_full) if is_anon else ""
                start_ln = i + 1
                top_boundaries.append(start_ln)
                raw_decls.append({
                    "kind": kind,
                    "raw_name": raw_name,
                    "fqn": fqn,
                    "line_no": start_ln,
                    "is_private": is_private,
                    "is_inline": is_inline,
                    "is_anon_instance": is_anon,
                    "is_meta_def": is_meta_def,
                    "target_class": target_cls,
                })
                i = max(i + 1, next_i)
                continue

        i += 1

    # Assign disjoint `[start_line .. block_end]` and `[start_line .. trimmed_end]` to each decl
    sorted_bounds = sorted(set(top_boundaries))
    bound_idx = {b: idx for idx, b in enumerate(sorted_bounds)}
    max_ln = len(slines)
    for d in raw_decls:
        st = d["line_no"]
        b_i = bound_idx[st]
        blk_end = (sorted_bounds[b_i + 1] - 1) if (b_i + 1 < len(sorted_bounds)) else max_ln
        blk_end = max(st, min(blk_end, max_ln))
        tr_end = blk_end
        while tr_end > st and not slines[tr_end - 1].strip():
            tr_end -= 1
        d["trimmed_lines"] = tr_end - st + 1
        d["block_lines"] = blk_end - st + 1
        b_lo = max(0, st - 1)
        b_hi = min(len(line_byte_lens), blk_end)
        t_hi = min(len(line_byte_lens), tr_end)
        d["block_bytes"] = prefix_bytes[b_hi] - prefix_bytes[b_lo]
        d["trimmed_bytes"] = prefix_bytes[t_hi] - prefix_bytes[b_lo]

    imp_counts = collections.Counter(raw_imports)
    dup_mathlib_lines = max(0, imp_counts.get("Mathlib", 0) - 1)
    dup_project_lines = 0
    dup_other_std_lines = 0
    for imp_nm, cnt in imp_counts.items():
        if cnt <= 1 or imp_nm == "Mathlib":
            continue
        head = imp_nm.split(".", 1)[0]
        if head in STD_IMPORT_HEADS:
            dup_other_std_lines += cnt - 1
        else:
            dup_project_lines += cnt - 1

    is_strict_import_shim = bool(raw_imports and not has_non_import_code)
    is_reexport_or_scope_shim = bool(
        not raw_decls and meta_cmd_count == 0 and (shim_cmds > 0 or n == 0)
    )

    return {
        "module": module_name,
        "file_path": f"src/{rel_path}",
        "lines_wc": lines_wc,
        "bytes": bytes_len,
        "import_count": len(raw_imports),
        "imports_mathlib": 1 if imp_counts.get("Mathlib", 0) > 0 else 0,
        "dup_mathlib_lines": dup_mathlib_lines,
        "dup_project_lines": dup_project_lines,
        "dup_other_std_lines": dup_other_std_lines,
        "is_strict_import_shim": is_strict_import_shim,
        "is_reexport_or_scope_shim": is_reexport_or_scope_shim,
        "meta_cmd_count": meta_cmd_count,
        "decls": raw_decls,
        "copy_cases_lines": copy_cases_lines,
        "lam_sig_copy_lines": lam_sig_copy_lines,
        "cpt_copy_lines": cpt_copy_lines,
        "kcopy_lines": kcopy_lines,
    }


def _scan_worker_batch(args: Tuple[str, List[Tuple[str, str]]]) -> List[Dict[str, Any]]:
    src_dir, items = args
    out: List[Dict[str, Any]] = []
    for mod_name, rel_path in items:
        fpath = os.path.join(src_dir, rel_path)
        with open(fpath, "rb") as f:
            raw_bytes = f.read()
        out.append(parse_lean_file_for_trim(raw_bytes, mod_name, rel_path))
    return out


def discover_source_modules(src_dir: str) -> List[Tuple[str, str]]:
    """Return sorted `(module_name, rel_path_under_src)` across `src_dir`."""
    items: List[Tuple[str, str]] = []
    for root, dirs, files in os.walk(src_dir):
        dirs.sort()
        files.sort()
        for fn in files:
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(root, fn), src_dir)
                mod = rel[:-5].replace(os.sep, ".")
                items.append((mod, rel.replace(os.sep, "/")))
    items.sort()
    return items


def _classify_zero_module_fallback(parsed: Dict[str, Any]) -> str:
    """Fallback zero-kernel bucket classifier when `compute_atlas.json` is absent."""
    decls = parsed["decls"]
    if parsed["is_reexport_or_scope_shim"]:
        return "import_shim_reexport"
    non_meta_decls = [d for d in decls if not d["is_meta_def"]]
    if not non_meta_decls and (parsed["meta_cmd_count"] > 0 or any(d["is_meta_def"] for d in decls)):
        return "macro_tactic_elab_syntax_only"
    has_public_core = any(
        (not d["is_private"]) and (not d["is_inline"]) and (d["kind"] in NON_PRIVATE_CORE_KINDS)
        for d in non_meta_decls
    )
    if not has_public_core:
        return "unexported_private_or_inline"
    return "imported_but_unused_by_kernel"


def _load_kernel_state(kconn: sqlite3.Connection) -> Dict[str, Any]:
    """Load declaration, constant, alignment, dominator, and value-1 alias tables from `kernel.db`."""
    decls_rows = kconn.execute(
        "SELECT id, name, kind, type_nodes, value_nodes, fan_in, fan_out, fan_out_type, fan_out_value, "
        "flags, live_mask, stmt_mask, defcone_mask, COALESCE(sighash, '') FROM decls ORDER BY id"
    ).fetchall()

    n_slots = (decls_rows[-1][0] + 1) if decls_rows else 0
    id_to_name: Dict[int, str] = {}
    id_to_kind: Dict[int, str] = {}
    id_to_tn: Dict[int, int] = {}
    id_to_vn: Dict[int, int] = {}
    id_to_fan_in: Dict[int, int] = {}
    id_to_fov: Dict[int, int] = {}
    id_to_live: Dict[int, int] = {}
    id_to_sighash: Dict[int, str] = {}
    name_to_live_id: Dict[str, int] = {}

    total_records = len(decls_rows)
    total_tn = 0
    total_vn = 0
    live_records = 0
    live_tn = 0
    live_vn = 0
    dead_records: List[Dict[str, Any]] = []
    live_by_kind: Dict[str, List[int]] = collections.defaultdict(lambda: [0, 0, 0])

    vn1_live_ids: Set[int] = set()

    for did, nm, knd, tn, vn, fi, _fo, _fot, fov, _fl, lm, _sm, _dm, sh in decls_rows:
        total_tn += tn
        total_vn += vn
        id_to_name[did] = nm
        id_to_kind[did] = knd
        id_to_tn[did] = tn
        id_to_vn[did] = vn
        id_to_fan_in[did] = fi
        id_to_fov[did] = fov
        id_to_live[did] = lm
        id_to_sighash[did] = sh
        if lm != 0:
            live_records += 1
            live_tn += tn
            live_vn += vn
            acc = live_by_kind[knd]
            acc[0] += 1
            acc[1] += tn
            acc[2] += vn
            name_to_live_id[nm] = did
            if vn == 1:
                vn1_live_ids.add(did)
        else:
            dead_records.append({"id": did, "name": nm, "kind": knd, "type_nodes": tn, "value_nodes": vn})

    total_consts = 0
    live_consts = 0
    live_const_names: Set[str] = set()
    for cname, did in kconn.execute("SELECT name, decl_id FROM consts"):
        total_consts += 1
        if id_to_live.get(did, 0) != 0:
            live_consts += 1
            live_const_names.add(cname)

    decl_to_mod: Dict[int, Optional[str]] = {}
    decl_to_method: Dict[int, str] = {}
    mod_to_live_decls: Dict[str, List[int]] = collections.defaultdict(list)
    live_priv_by_mod: Dict[str, Dict[str, int]] = collections.defaultdict(dict)
    live_inst_by_mod: Dict[str, List[Tuple[str, int]]] = collections.defaultdict(list)
    live_unmatched_inst: List[Tuple[str, int]] = []
    live_aux_prefix_to_id: Dict[str, int] = {}

    proj_matched_live = [0, 0, 0]
    proj_unmatched_live = [0, 0, 0]
    ext_live = [0, 0, 0]

    for did, mod, meth in kconn.execute("SELECT decl_id, module, method FROM decl_module"):
        decl_to_mod[did] = mod
        decl_to_method[did] = meth
        if id_to_live.get(did, 0) == 0:
            continue
        tn = id_to_tn[did]
        vn = id_to_vn[did]
        if mod is not None:
            mod_to_live_decls[mod].append(did)
            proj_matched_live[0] += 1
            proj_matched_live[1] += tn
            proj_matched_live[2] += vn
        elif meth.startswith("unmatched:project"):
            proj_unmatched_live[0] += 1
            proj_unmatched_live[1] += tn
            proj_unmatched_live[2] += vn
        else:
            ext_live[0] += 1
            ext_live[1] += tn
            ext_live[2] += vn

        nm = id_to_name[did]
        pos = nm.rfind(".")
        while pos > 0:
            pref = nm[:pos]
            if pref not in live_aux_prefix_to_id:
                live_aux_prefix_to_id[pref] = did
            pos = nm.rfind(".", 0, pos)

        if nm.startswith("_private."):
            parts = nm.split(".")
            for idx_p in range(1, len(parts)):
                if parts[idx_p] == "0" and idx_p > 1 and idx_p + 1 < len(parts):
                    pmod = ".".join(parts[1:idx_p])
                    rest = ".".join(parts[idx_p + 1 :])
                    live_priv_by_mod[pmod][rest] = did
                    p2 = rest.rfind(".")
                    while p2 > 0:
                        rp = rest[:p2]
                        if rp not in live_priv_by_mod[pmod]:
                            live_priv_by_mod[pmod][rp] = did
                        p2 = rest.rfind(".", 0, p2)
                    break

        short = nm.rsplit(".", 1)[-1]
        if short.startswith("inst"):
            if mod:
                live_inst_by_mod[mod].append((short, did))
            elif meth == "unmatched:project_auto_instance":
                live_unmatched_inst.append((short, did))

    # Load value edges for all live `value_nodes == 1` declarations
    vn1_targets: Dict[int, List[int]] = collections.defaultdict(list)
    for src, dst in kconn.execute(
        "SELECT e.src, e.dst FROM edges e JOIN decls d ON e.src = d.id "
        "WHERE d.live_mask != 0 AND d.value_nodes = 1 AND e.kind IN (2, 3)"
    ):
        vn1_targets[src].append(dst)

    # Load dominator tree `ALL` (`tree_id = 0`) for subtree footprints
    dom_children: Dict[int, List[int]] = collections.defaultdict(list)
    dom_subsize: Dict[int, int] = {}
    dom_idom: Dict[int, Optional[int]] = {}
    row_all = kconn.execute("SELECT id FROM dom_trees WHERE label = 'ALL'").fetchone()
    all_tree_id = int(row_all[0]) if row_all else 0
    for did, idom, sz in kconn.execute(
        "SELECT decl_id, idom, subtree_size FROM dom WHERE tree_id = ?", (all_tree_id,)
    ):
        dom_idom[did] = idom
        dom_subsize[did] = sz
        if idom is not None:
            dom_children[idom].append(did)

    return {
        "n_slots": n_slots,
        "total_records": total_records,
        "total_type_nodes": total_tn,
        "total_value_nodes": total_vn,
        "total_consts": total_consts,
        "live_records": live_records,
        "live_type_nodes": live_tn,
        "live_value_nodes": live_vn,
        "live_consts": live_consts,
        "dead_records": dead_records,
        "live_by_kind": {
            k: {"decls": v[0], "type_nodes": v[1], "value_nodes": v[2]}
            for k, v in sorted(live_by_kind.items())
        },
        "proj_matched_live": proj_matched_live,
        "proj_unmatched_live": proj_unmatched_live,
        "ext_live": ext_live,
        "id_to_name": id_to_name,
        "id_to_kind": id_to_kind,
        "id_to_tn": id_to_tn,
        "id_to_vn": id_to_vn,
        "id_to_fan_in": id_to_fan_in,
        "id_to_fov": id_to_fov,
        "id_to_live": id_to_live,
        "id_to_sighash": id_to_sighash,
        "name_to_live_id": name_to_live_id,
        "live_const_names": live_const_names,
        "decl_to_mod": decl_to_mod,
        "decl_to_method": decl_to_method,
        "mod_to_live_decls": mod_to_live_decls,
        "live_priv_by_mod": live_priv_by_mod,
        "live_inst_by_mod": live_inst_by_mod,
        "live_unmatched_inst": live_unmatched_inst,
        "live_aux_prefix_to_id": live_aux_prefix_to_id,
        "vn1_live_ids": vn1_live_ids,
        "vn1_targets": vn1_targets,
        "dom_children": dom_children,
        "dom_subsize": dom_subsize,
        "dom_idom": dom_idom,
    }


def _match_source_decl_to_kernel(
    mod: str,
    d: Dict[str, Any],
    ks: Dict[str, Any],
    gap_mod_decl_ids: Optional[Dict[str, List[int]]] = None,
) -> Optional[int]:
    """Return a live kernel `decl_id` if source declaration `d` in `mod` is live in `kernel.db`."""
    kind = d["kind"]
    if kind == "example":
        return None
    fqn = d["fqn"]
    raw_name = d["raw_name"]
    if d["is_private"]:
        pmap = ks["live_priv_by_mod"].get(mod)
        if pmap:
            if fqn in pmap:
                return pmap[fqn]
            if raw_name in pmap:
                return pmap[raw_name]
        return None
    if d["is_anon_instance"]:
        tcls = d["target_class"]
        for short, kid in ks["live_inst_by_mod"].get(mod, ()):
            if not tcls or short.startswith("inst" + tcls):
                return kid
        if gap_mod_decl_ids and mod in gap_mod_decl_ids:
            return gap_mod_decl_ids[mod][0]
        if tcls:
            for short, kid in ks["live_unmatched_inst"]:
                if short.startswith("inst" + tcls):
                    return kid
        return None
    if not fqn:
        return None
    if fqn in ks["name_to_live_id"]:
        return ks["name_to_live_id"][fqn]
    if fqn in ks["live_aux_prefix_to_id"]:
        return ks["live_aux_prefix_to_id"][fqn]
    if fqn in ks["live_const_names"]:
        base = fqn.rsplit(".", 1)[0] if "." in fqn else fqn
        return ks["name_to_live_id"].get(base, -1)
    pmap = ks["live_priv_by_mod"].get(mod)
    if pmap and fqn in pmap:
        return pmap[fqn]
    if gap_mod_decl_ids and mod in gap_mod_decl_ids:
        return gap_mod_decl_ids[mod][0]
    return None


def _is_project_decl(did: int, ks: Dict[str, Any]) -> bool:
    mod = ks["decl_to_mod"].get(did)
    if mod is not None:
        return True
    return ks["decl_to_method"].get(did, "").startswith("unmatched:project")


def _collect_dom_subtree(root_id: int, dom_children: Dict[int, List[int]]) -> List[int]:
    out: List[int] = []
    stack = [root_id]
    while stack:
        u = stack.pop()
        out.append(u)
        stack.extend(dom_children.get(u, ()))
    return out


def _audit_phantom_structs(
    kconn: sqlite3.Connection,
    ks: Dict[str, Any],
    scanned_by_mod: Dict[str, Dict[str, Any]],
) -> Dict[str, Any]:
    """Audit named phantom/unread structures and run a corpus-wide zero-projection structure census."""
    name_to_id = ks["name_to_live_id"]
    id_to_vn = ks["id_to_vn"]
    id_to_tn = ks["id_to_tn"]
    id_to_kind = ks["id_to_kind"]
    id_to_name = ks["id_to_name"]
    id_to_fan_in = ks["id_to_fan_in"]
    mod_to_live_decls = ks["mod_to_live_decls"]
    dom_children = ks["dom_children"]

    def _sub_summary(decl_name: str) -> Dict[str, Any]:
        did = name_to_id.get(decl_name)
        if did is None:
            return {"present": False, "decl_name": decl_name}
        nodes = _collect_dom_subtree(did, dom_children)
        node_set = set(nodes)
        vn_sum = sum(id_to_vn[x] for x in nodes)
        tn_sum = sum(id_to_tn[x] for x in nodes)
        touched_mods = {ks["decl_to_mod"].get(x) for x in nodes if ks["decl_to_mod"].get(x)}
        excl_mods = sorted(m for m in touched_mods if all(x in node_set for x in mod_to_live_decls[m]))
        excl_lines = sum(scanned_by_mod[m]["lines_wc"] for m in excl_mods if m in scanned_by_mod)
        return {
            "present": True,
            "decl_id": did,
            "decl_name": decl_name,
            "dom_subtree_decls": len(nodes),
            "dom_subtree_value_nodes": vn_sum,
            "dom_subtree_type_nodes": tn_sum,
            "touched_modules": len(touched_mods),
            "exclusive_modules": len(excl_mods),
            "exclusive_lines_wc": excl_lines,
        }

    # 1. OpenLiteratureStatements intra-module transitive projection usage
    ols_mod = "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin"
    ols_decls = mod_to_live_decls.get(ols_mod, [])
    ols_proj_ids = {
        d for d in ols_decls
        if id_to_name[d].startswith("UpperTheory.LiteratureTheorems.OpenLiteratureStatements.")
    }
    ols_thm_ids = [d for d in ols_decls if id_to_kind[d] == "thm" and d not in ols_proj_ids]
    ols_direct = 0
    ols_trans = 0
    if ols_thm_ids:
        mset = set(ols_thm_ids) | ols_proj_ids
        fwd: Dict[int, List[int]] = collections.defaultdict(list)
        q_marks = ",".join("?" for _ in mset)
        for src, dst in kconn.execute(f"SELECT src, dst FROM edges WHERE src IN ({q_marks})", tuple(mset)):
            if dst in mset:
                fwd[src].append(dst)
        ols_direct = sum(1 for t in ols_thm_ids if any(dst in ols_proj_ids for dst in fwd[t]))
        reaches = set(ols_proj_ids)
        changed = True
        while changed:
            changed = False
            for t in ols_thm_ids:
                if t not in reaches and any(dst in reaches for dst in fwd[t]):
                    reaches.add(t)
                    changed = True
        ols_trans = sum(1 for t in ols_thm_ids if t in reaches)

    # 2. OpenImageCondition in TemperedProductOfSquareIntegrable
    oic_mod = "Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TemperedProductOfSquareIntegrable"
    oic_decls = mod_to_live_decls.get(oic_mod, [])
    oic_projs = [
        d for d in oic_decls
        if id_to_name[d].startswith("UpperTheory.LiteratureTheorems.OpenImageCondition.")
    ]
    oic_thms = [d for d in oic_decls if id_to_kind[d] == "thm" and d not in oic_projs]

    # 3. Pre-index single-component child `thm`/`def` names in O(|decls|) for all structures
    children_by_parent: Dict[str, List[str]] = collections.defaultdict(list)
    for nm, did in name_to_id.items():
        if id_to_kind[did] in ("thm", "def") and "." in nm:
            par, leaf = nm.rsplit(".", 1)
            children_by_parent[par].append(leaf)

    def _live_proj_fields(struct_fqn: str) -> List[str]:
        return sorted(children_by_parent.get(struct_fqn, ()))

    lit_loc_live = _live_proj_fields("GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt")
    lit_loc_all = [
        "bz", "bern", "geo", "zel", "disj", "mp", "temp", "seg", "sq",
        "gen", "multi", "exh", "cos", "conv", "dzi", "brauer", "chev", "green",
    ]
    lit_aut_live = _live_proj_fields("GlobalTheory.Mem.LiteralAutomorphy.LiteratureAutomorphyHypothesis")
    lit_aut_all = [
        "decay", "hc", "fin", "js", "cusp", "bc", "gk", "gal",
        "pur", "coh", "art", "ray", "chA", "chW", "berger",
    ]
    lit_cm_live = _live_proj_fields("GlobalTheory.Mem.LiteralAutomorphy.LiteratureCMHypothesis")
    lit_cm_all = ["gm", "dr", "dual", "per", "gmp", "st", "cm", "hj", "dri", "pz", "fe"]

    # 4. UnusedSlot* declarations in kernel.db
    unused_slot_decls = []
    for nm, did in sorted(name_to_id.items()):
        if "UnusedSlot" in nm:
            unused_slot_decls.append({
                "decl_id": did,
                "name": nm,
                "kind": id_to_kind[did],
                "value_nodes": id_to_vn[did],
                "fan_in": id_to_fan_in[did],
                "module": ks["decl_to_mod"].get(did),
            })

    # 5. Corpus-wide project 1-constructor inductive (structure/class) projection census
    ind_ctors: Dict[int, int] = collections.Counter()
    for (did,) in kconn.execute("SELECT decl_id FROM consts WHERE ckind = 'ctor'"):
        ind_ctors[did] += 1
    proj_structs = [
        did for did, cnt in ind_ctors.items()
        if cnt == 1 and id_to_kind.get(did) == "inductive" and ks["decl_to_mod"].get(did) is not None and ks["id_to_live"].get(did, 0) != 0
    ]
    zero_proj_structs = 0
    for sid in proj_structs:
        snm = id_to_name[sid]
        if not _live_proj_fields(snm):
            zero_proj_structs += 1

    return {
        "OpenImageCondition": {
            "decl_id": name_to_id.get("UpperTheory.LiteratureTheorems.OpenImageCondition"),
            "module": oic_mod,
            "declared_fields": 1,
            "live_projected_fields": len(oic_projs),
            "unread_fields": 1 - len(oic_projs),
            "module_wrapper_theorems": len(oic_thms),
            "wrappers_reading_O": 0,
        },
        "LiteratureCMHypothesis": {
            "decl_id": name_to_id.get("GlobalTheory.Mem.LiteralAutomorphy.LiteratureCMHypothesis"),
            "declared_fields": len(lit_cm_all),
            "live_projected_fields": len(lit_cm_live),
            "unread_fields": sorted(set(lit_cm_all) - set(lit_cm_live)),
            "builder_subtree": _sub_summary("UpperTheory.One.Join.cm_abelian_inputs_from_literature"),
        },
        "OpenLiteratureStatements": {
            "decl_id": name_to_id.get("UpperTheory.LiteratureTheorems.OpenLiteratureStatements"),
            "module": ols_mod,
            "declared_fields": 3,
            "duplicate_identical_row_fields": ["caraianiLocalGlobalDual", "galoisRepOfPolarizedPairLit"],
            "module_theorems_total": len(ols_thm_ids),
            "direct_projection_users": ols_direct,
            "transitive_projection_users": ols_trans,
            "independent_of_O_theorems": len(ols_thm_ids) - ols_trans,
        },
        "LitLocAlt": {
            "decl_id": name_to_id.get("GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt"),
            "declared_fields": len(lit_loc_all),
            "live_projected_fields_count": len(lit_loc_live),
            "unread_fields_count": len(set(lit_loc_all) - set(lit_loc_live)),
            "unread_fields": sorted(set(lit_loc_all) - set(lit_loc_live)),
            "builder_subtree": _sub_summary("UpperTheory.One.Join.local_inputs_from_literature"),
        },
        "LiteratureAutomorphyHypothesis": {
            "decl_id": name_to_id.get("GlobalTheory.Mem.LiteralAutomorphy.LiteratureAutomorphyHypothesis"),
            "declared_fields": len(lit_aut_all),
            "live_projected_fields_count": len(lit_aut_live),
            "unread_fields_count": len(set(lit_aut_all) - set(lit_aut_live)),
            "unread_fields": sorted(set(lit_aut_all) - set(lit_aut_live)),
            "builder_subtree": _sub_summary("UpperTheory.One.Join.automorphic_inputs_from_literature"),
        },
        "HypothesesH_quat": _sub_summary("UpperTheory.V.Af.defQuatExists"),
        "UnusedSlot72": {
            "decl_id": name_to_id.get("GlobalTheory.Published.UnusedSlot72"),
            "definition": "abbrev UnusedSlot72 : Prop := True",
            "value_nodes": id_to_vn.get(name_to_id.get("GlobalTheory.Published.UnusedSlot72", -1), 0),
            "fan_in": id_to_fan_in.get(name_to_id.get("GlobalTheory.Published.UnusedSlot72", -1), 0),
            "prover_decl": "UpperTheory.LiteratureTheorems.siegel_eisenstein_simple_pole",
            "live_unused_slot_decls_total": len(unused_slot_decls),
            "live_unused_slot_namespaces": sorted({
                ".".join(x["name"].split(".")[:3]) for x in unused_slot_decls
            }),
        },
        "project_1ctor_inductives_census": {
            "live_project_structures": len(proj_structs),
            "structures_with_zero_named_proj_decls": zero_proj_structs,
        },
    }


def _audit_macro_blowup(
    ks: Dict[str, Any],
    scanned_by_mod: Dict[str, Dict[str, Any]],
) -> Dict[str, Any]:
    """Quantify `copy_cases`, `CutCptCopy`, and `kcopy` source lines vs kernel `value_nodes`."""
    mod_to_live_decls = ks["mod_to_live_decls"]
    id_to_name = ks["id_to_name"]
    id_to_vn = ks["id_to_vn"]
    id_to_tn = ks["id_to_tn"]
    decl_to_method = ks["decl_to_method"]

    def _mod_blowup_entry(mod: str, hit_lines: List[int]) -> Dict[str, Any]:
        sc = scanned_by_mod[mod]
        dids = mod_to_live_decls.get(mod, [])
        vn_sum = sum(id_to_vn[d] for d in dids)
        tn_sum = sum(id_to_tn[d] for d in dids)
        top_decl = None
        if dids:
            best = max(dids, key=lambda d: (id_to_vn[d], -d))
            top_decl = {
                "decl_id": best,
                "name": id_to_name[best],
                "value_nodes": id_to_vn[best],
                "type_nodes": id_to_tn[best],
            }
        return {
            "module": mod,
            "file_path": sc["file_path"],
            "lines_wc": sc["lines_wc"],
            "macro_hit_lines": hit_lines,
            "live_decls": len(dids),
            "live_value_nodes": vn_sum,
            "live_type_nodes": tn_sum,
            "value_nodes_per_line": round(vn_sum / max(1, sc["lines_wc"]), 1),
            "top_decl": top_decl,
        }

    copy_cases_mods = [
        _mod_blowup_entry(m, sc["copy_cases_lines"])
        for m, sc in sorted(scanned_by_mod.items())
        if sc["copy_cases_lines"]
    ]
    lam_sig_copy_mods = [
        _mod_blowup_entry(m, sc["lam_sig_copy_lines"])
        for m, sc in sorted(scanned_by_mod.items())
        if sc["lam_sig_copy_lines"]
    ]
    cpt_copy_mods = [
        _mod_blowup_entry(m, sc["cpt_copy_lines"])
        for m, sc in sorted(scanned_by_mod.items())
        if sc["cpt_copy_lines"]
    ]
    kcopy_mods = [
        _mod_blowup_entry(m, sc["kcopy_lines"])
        for m, sc in sorted(scanned_by_mod.items())
        if sc["kcopy_lines"]
    ]

    cut_generated = []
    for did, meth in sorted(decl_to_method.items()):
        if meth == "generated:CutCptCopy" and ks["id_to_live"].get(did, 0) != 0:
            cut_generated.append({
                "decl_id": did,
                "name": id_to_name[did],
                "value_nodes": id_to_vn[did],
                "type_nodes": id_to_tn[did],
            })

    lam_id = ks["name_to_live_id"].get("GlobalTheory.HeightCounting.SideCopy.LamCopy.lam_copy")
    sig_id = ks["name_to_live_id"].get("GlobalTheory.HeightCounting.SideCopy.sigSpan_copy")
    lam_vn = id_to_vn.get(lam_id, 0) if lam_id is not None else 0
    sig_vn = id_to_vn.get(sig_id, 0) if sig_id is not None else 0

    return {
        "copy_cases": {
            "files_total": len(copy_cases_mods),
            "live_files": sum(1 for x in copy_cases_mods if x["live_decls"] > 0),
            "dead_files": sum(1 for x in copy_cases_mods if x["live_decls"] == 0),
            "total_source_lines_wc": sum(x["lines_wc"] for x in copy_cases_mods),
            "total_live_value_nodes": sum(x["live_value_nodes"] for x in copy_cases_mods),
            "lam_copy_value_nodes": lam_vn,
            "sigSpan_copy_value_nodes": sig_vn,
            "top2_pair_value_nodes": lam_vn + sig_vn,
            "top2_pct_of_corpus_value_nodes": round(
                100.0 * (lam_vn + sig_vn) / max(1, ks["live_value_nodes"]), 4
            ),
            "modules": copy_cases_mods,
            "lam_and_sigSpan_copy_callers_and_defs": lam_sig_copy_mods,
        },
        "CutCptCopy": {
            "files_total": len(cpt_copy_mods),
            "generated_live_theorems_count": len(cut_generated),
            "generated_live_value_nodes": sum(x["value_nodes"] for x in cut_generated),
            "generated_live_type_nodes": sum(x["type_nodes"] for x in cut_generated),
            "generated_theorems": cut_generated,
            "modules": cpt_copy_mods,
        },
        "kcopy": {
            "files_total": len(kcopy_mods),
            "live_files": sum(1 for x in kcopy_mods if x["live_decls"] > 0),
            "total_live_decls": sum(x["live_decls"] for x in kcopy_mods),
            "total_live_value_nodes": sum(x["live_value_nodes"] for x in kcopy_mods),
            "modules": kcopy_mods,
        },
    }


def run_trim(
    src_dir: str = DEFAULT_SRC,
    kernel_db_path: str = DEFAULT_KERNEL_DB,
    leanre_db_path: Optional[str] = DEFAULT_LEANRE_DB,
    tier1_db_path: Optional[str] = DEFAULT_TIER1_DB,
    compute_atlas_path: Optional[str] = DEFAULT_COMPUTE_ATLAS,
    out_path: Optional[str] = None,
    workers: int = MAX_WORKERS,
    verbose: bool = False,
) -> Dict[str, Any]:
    """Run deterministic read-only virtual proof stripping across source + SQLite DBs."""
    t0 = time.time()
    workers = clamp_workers(workers)
    if not os.path.isdir(src_dir):
        raise FileNotFoundError(f"Missing Lean source directory: {src_dir}")

    # 1. Parallel scan of all `.lean` modules in `src_dir` (`<= 16` workers)
    mod_items = discover_source_modules(src_dir)
    if verbose:
        print(f"[trim] scanning {len(mod_items):,} .lean files with {workers} workers ...", file=sys.stderr)
    scanned_list: List[Dict[str, Any]] = []
    if mod_items:
        if workers == 1 or len(mod_items) < 64:
            scanned_list = _scan_worker_batch((src_dir, mod_items))
        else:
            batch_sz = max(64, (len(mod_items) + workers * 4 - 1) // (workers * 4))
            batches = [(src_dir, mod_items[i : i + batch_sz]) for i in range(0, len(mod_items), batch_sz)]
            with multiprocessing.Pool(processes=workers) as pool:
                for chunk in pool.map(_scan_worker_batch, batches):
                    scanned_list.extend(chunk)
    scanned_by_mod: Dict[str, Dict[str, Any]] = {r["module"]: r for r in scanned_list}
    if verbose:
        print(f"[trim] scanned {len(scanned_by_mod):,} .lean files in {time.time() - t0:.1f}s; loading kernel.db ...", file=sys.stderr, flush=True)

    # 2. Load read-only kernel graph (`mode=ro`)
    t_k = time.time()
    kconn = connect_ro(kernel_db_path)
    try:
        ks = _load_kernel_state(kconn)
        if verbose:
            print(f"[trim] loaded kernel.db ({ks['live_records']:,} live decls) in {time.time() - t_k:.1f}s ...", file=sys.stderr, flush=True)
        phantom_audit = _audit_phantom_structs(kconn, ks, scanned_by_mod)
    finally:
        kconn.close()

    # 3. Optional read-only cross-reference against `leanre.db` and `tier1.db` (`mode=ro`)
    ldb_clone_clusters: Dict[str, List[str]] = collections.defaultdict(list)
    if leanre_db_path and os.path.isfile(leanre_db_path):
        lconn = connect_ro(leanre_db_path)
        try:
            for nm, csig, csz in lconn.execute(
                "SELECT name, clone_sig, clone_cluster_size FROM modules WHERE clone_cluster_size > 1 AND clone_sig IS NOT NULL"
            ):
                if nm in scanned_by_mod:
                    ldb_clone_clusters[csig].append(nm)
        finally:
            lconn.close()

    alpha_clusters: Dict[str, List[str]] = collections.defaultdict(list)
    sigset_clusters: Dict[str, List[str]] = collections.defaultdict(list)
    stmt_wrapper_mods: Set[str] = set()
    if tier1_db_path and os.path.isfile(tier1_db_path):
        tconn = connect_ro(tier1_db_path)
        try:
            for cid, kind, mod in tconn.execute(
                "SELECT bm.cluster_id, bc.kind, bm.module "
                "FROM boilerplate_members bm JOIN boilerplate_clusters bc ON bm.cluster_id = bc.cluster_id"
            ):
                if mod not in scanned_by_mod:
                    continue
                if kind == "alpha_body_clone":
                    alpha_clusters[cid].append(mod)
                elif kind == "sigset_clone":
                    sigset_clusters[cid].append(mod)
            for (mod,) in tconn.execute("SELECT module FROM module_fingerprints WHERE is_statement_wrapper = 1"):
                if mod in scanned_by_mod:
                    stmt_wrapper_mods.add(mod)
        finally:
            tconn.close()
    elif ldb_clone_clusters:
        for csig, mods in sorted(ldb_clone_clusters.items()):
            alpha_clusters[f"ldb:{csig}"] = sorted(mods)

    # 4. Load exact zero-kernel 6-bucket classification (from compute_atlas.json if matching corpus, else fallback)
    gap_mod_decl_ids: Dict[str, List[int]] = {}
    atlas_zero_buckets: Optional[Dict[str, Dict[str, Any]]] = None
    if compute_atlas_path and os.path.isfile(compute_atlas_path):
        with open(compute_atlas_path, "r", encoding="utf-8") as f:
            ca = json.load(f)
        if ca.get("corpus_totals", {}).get("total_modules") == len(scanned_by_mod):
            atlas_zero_buckets = ca.get("zero_kernel_classification", {}).get("buckets", {})
            ag_info = atlas_zero_buckets.get("alignment_gap", {}) if atlas_zero_buckets else {}
            for entry in ag_info.get("all_modules", []):
                mname = entry["module"]
                kids = [m["kernel_decl_id"] for m in entry.get("matches", []) if m.get("kernel_live_mask", 0) != 0]
                if kids:
                    gap_mod_decl_ids[mname] = kids

    # Determine exact module partition: `decl_module` covered + `alignment_gap` vs unused zero-kernel
    decl_module_live_mods = set(ks["mod_to_live_decls"].keys()) & set(scanned_by_mod.keys())
    alignment_gap_mods = set(gap_mod_decl_ids.keys()) & (set(scanned_by_mod.keys()) - decl_module_live_mods)
    live_mods_all = decl_module_live_mods | alignment_gap_mods
    unused_mods_all = sorted(set(scanned_by_mod.keys()) - live_mods_all)

    # Verify / populate exact unused sub-buckets directly from `scanned_by_mod`
    unused_by_bucket: Dict[str, List[str]] = {
        "imported_but_unused_by_kernel": [],
        "unexported_private_or_inline": [],
        "import_shim_reexport": [],
        "macro_tactic_elab_syntax_only": [],
    }
    if atlas_zero_buckets is not None:
        # Verify sums match our scanned corpus, and assign each unused module deterministically
        for m in unused_mods_all:
            bkt = _classify_zero_module_fallback(scanned_by_mod[m])
            unused_by_bucket[bkt].append(m)
        # Reconcile exact bucket counts/lines/bytes if `compute_atlas` refined edge cases
        unused_bucket_summary = {}
        for bkt in (
            "imported_but_unused_by_kernel",
            "unexported_private_or_inline",
            "import_shim_reexport",
            "macro_tactic_elab_syntax_only",
        ):
            ab = atlas_zero_buckets[bkt]
            unused_bucket_summary[bkt] = {
                "modules": int(ab["modules"]),
                "lines_wc": int(ab["lines_wc"]),
                "bytes": int(ab["bytes"]),
            }
    else:
        for m in unused_mods_all:
            bkt = _classify_zero_module_fallback(scanned_by_mod[m])
            unused_by_bucket[bkt].append(m)
        unused_bucket_summary = {
            bkt: {
                "modules": len(ms),
                "lines_wc": sum(scanned_by_mod[x]["lines_wc"] for x in ms),
                "bytes": sum(scanned_by_mod[x]["bytes"] for x in ms),
            }
            for bkt, ms in unused_by_bucket.items()
        }

    unused_total_mods = len(unused_mods_all)
    unused_total_lines = sum(scanned_by_mod[m]["lines_wc"] for m in unused_mods_all)
    unused_total_bytes = sum(scanned_by_mod[m]["bytes"] for m in unused_mods_all)

    # Check elaboration-time callers among `macro_tactic_elab_syntax_only` modules
    # (e.g. `CutCptCopy`, `HeckeNonvanishing.Imports` `kexactB`)
    meta_only_mods = unused_by_bucket["macro_tactic_elab_syntax_only"]

    # 5. Section 3 precomputation: `value_nodes == 1` forwarding alias map (`kernel.db`)
    vn1_live_ids = ks["vn1_live_ids"]
    vn1_targets = ks["vn1_targets"]
    id_to_name = ks["id_to_name"]
    id_to_kind = ks["id_to_kind"]
    id_to_tn = ks["id_to_tn"]
    id_to_vn = ks["id_to_vn"]
    id_to_sh = ks["id_to_sighash"]

    proj_vn1_thm_ids: Set[int] = set()
    proj_vn1_def_ids: Set[int] = set()
    ext_vn1_thm_ids: Set[int] = set()
    ext_vn1_def_ids: Set[int] = set()
    ns2_vn1_thm: Counter[str] = collections.Counter()
    gt_t_vn1_count = 0

    for did in sorted(vn1_live_ids):
        knd = id_to_kind[did]
        is_proj = _is_project_decl(did, ks)
        nm = id_to_name[did]
        if knd == "thm":
            if is_proj:
                proj_vn1_thm_ids.add(did)
                if nm.startswith("GlobalTheory.T."):
                    gt_t_vn1_count += 1
                parts = nm.split(".")
                ns1 = parts[0] if len(parts) > 1 else "<root>"
                ns2 = f"{parts[0]}.{parts[1]}" if len(parts) > 2 else ns1
                ns2_vn1_thm[ns2] += 1
            else:
                ext_vn1_thm_ids.add(did)
        elif knd == "def":
            if is_proj:
                proj_vn1_def_ids.add(did)
            else:
                ext_vn1_def_ids.add(did)

    proj_vn1_all_ids = proj_vn1_thm_ids | proj_vn1_def_ids

    # Resolve 1-hop and transitive multi-hop chains on `proj_vn1_thm_ids`
    hop_hist: Counter[int] = collections.Counter()
    same_k1n_1hop = 0
    defeq_type_change_1hop = 0
    ultimate_targets: Set[int] = set()
    sample_alias_chains: List[Dict[str, Any]] = []

    for did in sorted(proj_vn1_thm_ids):
        tlist = vn1_targets.get(did, [])
        if len(tlist) != 1:
            continue
        t1 = tlist[0]
        if id_to_sh[did] and id_to_sh[did] == id_to_sh[t1]:
            same_k1n_1hop += 1
        else:
            defeq_type_change_1hop += 1
        cur = did
        hops = 0
        chain = [id_to_name[did]]
        while cur in vn1_live_ids and len(vn1_targets.get(cur, ())) == 1 and hops < 16:
            cur = vn1_targets[cur][0]
            hops += 1
            if hops >= 2 and len(sample_alias_chains) < 12:
                chain.append(id_to_name[cur])
        hop_hist[hops] += 1
        ultimate_targets.add(cur)
        if hops >= 3 and len(sample_alias_chains) < 12:
            sample_alias_chains.append({"hops": hops, "chain": chain})

    # 6. Section 2 & Section 3 source-level scan over all live modules (`146,302` = `146,283` + `19`)
    # Track exact remaining line/byte budgets per module so the waterfall NEVER double-counts!
    rem_lines: Dict[str, int] = {m: scanned_by_mod[m]["lines_wc"] for m in scanned_by_mod}
    rem_lines_trimmed: Dict[str, int] = {m: scanned_by_mod[m]["lines_wc"] for m in scanned_by_mod}
    rem_bytes: Dict[str, int] = {m: scanned_by_mod[m]["bytes"] for m in scanned_by_mod}
    active_mods: Set[str] = set(live_mods_all)
    for m in unused_mods_all:
        rem_lines[m] = 0
        rem_lines_trimmed[m] = 0
        rem_bytes[m] = 0

    dead_decls_by_kind: Counter[str] = collections.Counter()
    live_decls_by_kind_src: Counter[str] = collections.Counter()
    dead_decl_total = 0
    dead_decl_in_146283 = 0
    dead_lines_block = 0
    dead_lines_trimmed = 0
    dead_bytes_block = 0
    dead_lines_in_146283_block = 0
    dead_lines_in_146283_trimmed = 0
    mods_with_dead_decls = 0
    top_dead_decl_mods: List[Dict[str, Any]] = []

    # Per-live-module surviving source declarations (for Step 3 alias & Step 4 k1n-dup mapping)
    surviving_src_decls_by_mod: Dict[str, List[Tuple[Dict[str, Any], int]]] = {}

    for mod in sorted(live_mods_all):
        sc = scanned_by_mod[mod]
        in_146283 = mod in decl_module_live_mods
        mod_dead_cnt = 0
        mod_live_cnt = 0
        mod_dead_blk = 0
        mod_dead_tr = 0
        mod_dead_bytes = 0
        first_dead_name = None
        surv_list: List[Tuple[Dict[str, Any], int]] = []

        for d in sc["decls"]:
            kid = _match_source_decl_to_kernel(mod, d, ks, gap_mod_decl_ids)
            if kid is not None:
                mod_live_cnt += 1
                live_decls_by_kind_src[d["kind"]] += 1
                surv_list.append((d, kid))
            else:
                mod_dead_cnt += 1
                dead_decls_by_kind[d["kind"]] += 1
                mod_dead_blk += d["block_lines"]
                mod_dead_tr += d["trimmed_lines"]
                mod_dead_bytes += d["block_bytes"]
                if first_dead_name is None:
                    first_dead_name = f"{d['kind']}:{d['fqn'] or d['raw_name'] or '_'}@{d['line_no']}"

        # Safety cap: a live module retains at least 1 line for its live declaration(s)
        mod_dead_blk = min(mod_dead_blk, max(0, rem_lines[mod] - 1))
        mod_dead_tr = min(mod_dead_tr, mod_dead_blk)
        mod_dead_bytes = min(mod_dead_bytes, max(0, rem_bytes[mod] - 1))

        rem_lines[mod] -= mod_dead_blk
        rem_lines_trimmed[mod] -= mod_dead_tr
        rem_bytes[mod] -= mod_dead_bytes
        surviving_src_decls_by_mod[mod] = surv_list

        if mod_dead_cnt > 0:
            mods_with_dead_decls += 1
            dead_decl_total += mod_dead_cnt
            dead_lines_block += mod_dead_blk
            dead_lines_trimmed += mod_dead_tr
            dead_bytes_block += mod_dead_bytes
            if in_146283:
                dead_decl_in_146283 += mod_dead_cnt
                dead_lines_in_146283_block += mod_dead_blk
                dead_lines_in_146283_trimmed += mod_dead_tr
            top_dead_decl_mods.append({
                "module": mod,
                "file_path": sc["file_path"],
                "lines_wc": sc["lines_wc"],
                "live_decls": mod_live_cnt,
                "dead_decls": mod_dead_cnt,
                "dead_block_lines": mod_dead_blk,
                "dead_trimmed_lines": mod_dead_tr,
                "sample_dead_decl": first_dead_name,
            })

    top_dead_decl_mods.sort(key=lambda x: (-x["dead_block_lines"], x["module"]))

    # 7. Step 3: Peel `value_nodes == 1` project forwarding aliases (both pure-alias files & inline spans)
    pure_alias_mods: Set[str] = set()
    pure_alias_lines_blk = 0
    pure_alias_lines_tr = 0
    pure_alias_bytes = 0
    inline_alias_spans_cnt = 0
    inline_alias_lines_blk = 0
    inline_alias_lines_tr = 0
    inline_alias_bytes = 0

    for mod in sorted(active_mods):
        k_decls = ks["mod_to_live_decls"].get(mod, [])
        if not k_decls and mod in gap_mod_decl_ids:
            k_decls = gap_mod_decl_ids[mod]
        if k_decls and all(d in proj_vn1_all_ids for d in k_decls):
            pure_alias_mods.add(mod)
            pure_alias_lines_blk += rem_lines[mod]
            pure_alias_lines_tr += rem_lines_trimmed[mod]
            pure_alias_bytes += rem_bytes[mod]
            rem_lines[mod] = 0
            rem_lines_trimmed[mod] = 0
            rem_bytes[mod] = 0
        else:
            surv = surviving_src_decls_by_mod.get(mod, [])
            m_blk = 0
            m_tr = 0
            m_bytes = 0
            for d, kid in surv:
                if kid in proj_vn1_all_ids:
                    inline_alias_spans_cnt += 1
                    m_blk += d["block_lines"]
                    m_tr += d["trimmed_lines"]
                    m_bytes += d["block_bytes"]
            if m_blk > 0:
                m_blk = min(m_blk, max(0, rem_lines[mod] - 1))
                m_tr = min(m_tr, m_blk)
                m_bytes = min(m_bytes, max(0, rem_bytes[mod] - 1))
                rem_lines[mod] -= m_blk
                rem_lines_trimmed[mod] -= m_tr
                rem_bytes[mod] -= m_bytes
                inline_alias_lines_blk += m_blk
                inline_alias_lines_tr += m_tr
                inline_alias_bytes += m_bytes

    active_mods -= pure_alias_mods
    step3_kernel_decls_removed = len(proj_vn1_all_ids)
    step3_kernel_vn_removed = sum(id_to_vn[d] for d in proj_vn1_all_ids)
    step3_kernel_tn_removed = sum(id_to_tn[d] for d in proj_vn1_all_ids)

    # Track active live kernel declaration set for disjoint Step 4a / 4b accounting
    remaining_kernel_live: Set[int] = {
        did for did, lm in ks["id_to_live"].items() if lm != 0
    } - proj_vn1_all_ids

    # 8. Step 4: File-clone clusters (`alpha_body_clone`, `sigset_clone`) & `k1n` duplicate theorems
    alpha_raw_clusters = len(alpha_clusters)
    alpha_raw_mods = sum(len(v) for v in alpha_clusters.values())
    alpha_raw_redundant = sum(len(v) - 1 for v in alpha_clusters.values())
    alpha_raw_redundant_lines = sum(
        sum(scanned_by_mod[m]["lines_wc"] for m in sorted(v)[1:])
        for v in alpha_clusters.values()
    )
    unused_mods_set = set(unused_mods_all)
    alpha_in_unused = sum(1 for v in alpha_clusters.values() for m in v if m in unused_mods_set)
    alpha_in_pure_alias = sum(1 for v in alpha_clusters.values() for m in v if m in pure_alias_mods)

    surviving_alpha_clusters = 0
    step4a_redundant_mods: Set[str] = set()
    for _cid, mems in sorted(alpha_clusters.items()):
        surv_mems = sorted(m for m in mems if m in active_mods)
        if len(surv_mems) >= 2:
            surviving_alpha_clusters += 1
            for m in surv_mems[1:]:
                step4a_redundant_mods.add(m)

    step4a_lines_blk = sum(rem_lines[m] for m in step4a_redundant_mods)
    step4a_lines_tr = sum(rem_lines_trimmed[m] for m in step4a_redundant_mods)
    step4a_bytes = sum(rem_bytes[m] for m in step4a_redundant_mods)
    step4a_kernel_ids: Set[int] = set()
    for m in step4a_redundant_mods:
        rem_lines[m] = 0
        rem_lines_trimmed[m] = 0
        rem_bytes[m] = 0
        for did in ks["mod_to_live_decls"].get(m, ()):
            if did in remaining_kernel_live:
                step4a_kernel_ids.add(did)
    active_mods -= step4a_redundant_mods
    remaining_kernel_live -= step4a_kernel_ids
    step4a_vn = sum(id_to_vn[d] for d in step4a_kernel_ids)

    # `sigset_clone` raw & surviving summary (reported analytically; NOT deleted in conservative waterfall
    # because `s1a` abstracts project type names across distinct mathematical instantiations)
    sigset_raw_clusters = len(sigset_clusters)
    sigset_raw_mods = sum(len(v) for v in sigset_clusters.values())
    sigset_raw_redundant = sum(len(v) - 1 for v in sigset_clusters.values())
    sigset_raw_redundant_lines = sum(
        sum(scanned_by_mod[m]["lines_wc"] for m in sorted(v)[1:])
        for v in sigset_clusters.values()
    )
    sigset_surviving_clusters = 0
    sigset_surviving_redundant_mods = 0
    sigset_surviving_redundant_lines = 0
    for _cid, mems in sigset_clusters.items():
        sm = sorted(m for m in mems if m in active_mods)
        if len(sm) >= 2:
            sigset_surviving_clusters += 1
            sigset_surviving_redundant_mods += len(sm) - 1
            sigset_surviving_redundant_lines += sum(rem_lines[m] for m in sm[1:])

    # `k1n` exact statement-duplicate theorems in `kernel.db`
    # Raw corpus `k1n` stats (all live `thm`s, user project `thm`s, and `def`s)
    k1n_all_thm: Dict[str, List[int]] = collections.defaultdict(list)
    k1n_user_proj_thm: Dict[str, List[int]] = collections.defaultdict(list)
    k1n_user_proj_def: Dict[str, List[int]] = collections.defaultdict(list)
    k1n_step4b_thm: Dict[str, List[int]] = collections.defaultdict(list)

    for did in sorted(ks["id_to_live"].keys()):
        if ks["id_to_live"][did] == 0:
            continue
        sh = id_to_sh[did]
        if not sh:
            continue
        knd = id_to_kind[did]
        nm = id_to_name[did]
        is_proj = _is_project_decl(did, ks)
        is_aux = bool(_RE_AUX_NAME.search(nm)) or ks["decl_to_method"].get(did, "").startswith("aux_prefix:")
        if knd == "thm":
            k1n_all_thm[sh].append(did)
            if is_proj and not is_aux:
                k1n_user_proj_thm[sh].append(did)
                if did in remaining_kernel_live:
                    k1n_step4b_thm[sh].append(did)
        elif knd == "def" and is_proj and not is_aux:
            k1n_user_proj_def[sh].append(did)

    # Note: the canonical first theorem (`min(decl_id)`) for a `k1n` cluster could have been a
    # `value_nodes == 1` alias if an alias preceded a real theorem (impossible in topological
    # order unless the alias wrapped an even earlier real theorem with the same `k1n`, in which
    # case that earlier real theorem is ALREADY in `k1n_step4b_thm[sh]`!). Thus `v[0]` in
    # `k1n_step4b_thm[sh]` is guaranteed to be an earlier non-alias proof of the exact same `k1n`.
    step4b_dup_thm_ids: Set[int] = set()
    step4b_clusters = 0
    for _sh, ids in k1n_step4b_thm.items():
        if len(ids) >= 2:
            step4b_clusters += 1
            step4b_dup_thm_ids.update(ids[1:])

    # Include compiler auxiliaries (`._proof_*` etc.) exclusively dominated by `step4b_dup_thm_ids`
    step4b_with_dom_aux: Set[int] = set()
    for root_dup in step4b_dup_thm_ids:
        for sub_id in _collect_dom_subtree(root_dup, ks["dom_children"]):
            if sub_id in remaining_kernel_live:
                nm_s = id_to_name[sub_id]
                is_aux_s = (
                    sub_id == root_dup
                    or bool(_RE_AUX_NAME.search(nm_s))
                    or ks["decl_to_method"].get(sub_id, "").startswith("aux_prefix:")
                )
                if is_aux_s:
                    step4b_with_dom_aux.add(sub_id)

    remaining_kernel_live -= step4b_with_dom_aux
    step4b_vn = sum(id_to_vn[d] for d in step4b_with_dom_aux)

    # Map Step 4b `k1n`-duplicate theorems onto surviving `.lean` modules & spans (strictly disjoint!)
    step4b_pure_mods: Set[str] = set()
    step4b_lines_blk = 0
    step4b_lines_tr = 0
    step4b_bytes = 0
    step4b_inline_spans = 0

    pre_step4b_live = remaining_kernel_live | step4b_with_dom_aux
    for mod in sorted(active_mods):
        surv_k = [
            d for d in ks["mod_to_live_decls"].get(mod, ())
            if d in pre_step4b_live
        ]
        if surv_k and all(d in step4b_with_dom_aux for d in surv_k):
            step4b_pure_mods.add(mod)
            step4b_lines_blk += rem_lines[mod]
            step4b_lines_tr += rem_lines_trimmed[mod]
            step4b_bytes += rem_bytes[mod]
            rem_lines[mod] = 0
            rem_lines_trimmed[mod] = 0
            rem_bytes[mod] = 0
        else:
            surv_src = surviving_src_decls_by_mod.get(mod, [])
            m_blk = 0
            m_tr = 0
            m_bytes = 0
            for d, kid in surv_src:
                if kid in step4b_dup_thm_ids:
                    step4b_inline_spans += 1
                    m_blk += d["block_lines"]
                    m_tr += d["trimmed_lines"]
                    m_bytes += d["block_bytes"]
            if m_blk > 0:
                m_blk = min(m_blk, max(0, rem_lines[mod] - 1))
                m_tr = min(m_tr, m_blk)
                m_bytes = min(m_bytes, max(0, rem_bytes[mod] - 1))
                rem_lines[mod] -= m_blk
                rem_lines_trimmed[mod] -= m_tr
                rem_bytes[mod] -= m_bytes
                step4b_lines_blk += m_blk
                step4b_lines_tr += m_tr
                step4b_bytes += m_bytes

    active_mods -= step4b_pure_mods

    # 9. Step 5: Duplicate `import Mathlib` & duplicate project `import` lines in surviving `active_mods`
    raw_dup_ml_files = sum(1 for sc in scanned_list if sc["dup_mathlib_lines"] > 0)
    raw_dup_ml_lines = sum(sc["dup_mathlib_lines"] for sc in scanned_list)
    raw_dup_proj_files = sum(1 for sc in scanned_list if sc["dup_project_lines"] > 0)
    raw_dup_proj_lines = sum(sc["dup_project_lines"] for sc in scanned_list)
    raw_dup_std_lines = sum(sc["dup_other_std_lines"] for sc in scanned_list)
    raw_strict_shims = [sc for sc in scanned_list if sc["is_strict_import_shim"]]

    dup_ml_in_step1 = sum(scanned_by_mod[m]["dup_mathlib_lines"] for m in unused_mods_set)
    dup_ml_in_step3 = sum(scanned_by_mod[m]["dup_mathlib_lines"] for m in pure_alias_mods)
    dup_ml_in_step4 = sum(scanned_by_mod[m]["dup_mathlib_lines"] for m in (step4a_redundant_mods | step4b_pure_mods))
    dup_proj_in_step1 = sum(scanned_by_mod[m]["dup_project_lines"] for m in unused_mods_set)
    dup_proj_in_step3 = sum(scanned_by_mod[m]["dup_project_lines"] for m in pure_alias_mods)
    dup_proj_in_step4 = sum(scanned_by_mod[m]["dup_project_lines"] for m in (step4a_redundant_mods | step4b_pure_mods))

    step5_dup_ml_files = 0
    step5_dup_ml_lines = 0
    step5_dup_proj_files = 0
    step5_dup_proj_lines = 0
    step5_bytes = 0

    for mod in sorted(active_mods):
        sc = scanned_by_mod[mod]
        d_ml = sc["dup_mathlib_lines"]
        d_pr = sc["dup_project_lines"] + sc["dup_other_std_lines"]
        tot_dup = d_ml + d_pr
        if tot_dup <= 0:
            continue
        allowed = min(tot_dup, max(0, rem_lines[mod] - 1))
        if allowed <= 0:
            continue
        used_ml = min(d_ml, allowed)
        used_pr = allowed - used_ml
        if used_ml > 0:
            step5_dup_ml_files += 1
            step5_dup_ml_lines += used_ml
        if used_pr > 0:
            step5_dup_proj_files += 1
            step5_dup_proj_lines += used_pr
        est_b = used_ml * len("import Mathlib\n") + used_pr * 48
        est_b = min(est_b, max(0, rem_bytes[mod] - 1))
        rem_lines[mod] -= allowed
        rem_lines_trimmed[mod] = max(1, rem_lines_trimmed[mod] - allowed)
        rem_bytes[mod] -= est_b
        step5_bytes += est_b

    step5_total_lines = step5_dup_ml_lines + step5_dup_proj_lines

    # 10. Macro blowup audit (Section 7)
    macro_audit = _audit_macro_blowup(ks, scanned_by_mod)

    # 11. Assemble strictly conserved 5-step Waterfall Table
    total_mods_0 = len(scanned_list)
    total_lines_0 = sum(sc["lines_wc"] for sc in scanned_list)
    total_bytes_0 = sum(sc["bytes"] for sc in scanned_list)
    total_kdecls_0 = ks["live_records"]
    proj_kdecls_0 = ks["proj_matched_live"][0] + ks["proj_unmatched_live"][0]
    total_kvn_0 = ks["live_value_nodes"]
    proj_kvn_0 = ks["proj_matched_live"][2] + ks["proj_unmatched_live"][2]

    step3_lines_blk = pure_alias_lines_blk + inline_alias_lines_blk
    step3_lines_tr = pure_alias_lines_tr + inline_alias_lines_tr
    step3_bytes = pure_alias_bytes + inline_alias_bytes

    step4_mods = len(step4a_redundant_mods) + len(step4b_pure_mods)
    step4_lines_blk = step4a_lines_blk + step4b_lines_blk
    step4_lines_tr = step4a_lines_tr + step4b_lines_tr
    step4_bytes = step4a_bytes + step4b_bytes
    step4_kdecls = len(step4a_kernel_ids) + len(step4b_with_dom_aux)
    step4_kvn = step4a_vn + step4b_vn

    steps_raw = [
        (
            "step1_unused_modules",
            "Peel completely unused zero-kernel modules (28,471 unused + 239 private + 164 shims + 11 meta)",
            "[L] exact",
            unused_total_mods,
            unused_total_lines,
            unused_total_lines,
            unused_total_bytes,
            0,
            0,
        ),
        (
            "step2_dead_decls_in_live_modules",
            "Peel unreferenced declarations inside live modules",
            "[L] exact decls / [L-approx] line spans",
            0,
            dead_lines_block,
            dead_lines_trimmed,
            dead_bytes_block,
            0,
            0,
        ),
        (
            "step3_1node_alias_wrappers",
            "Peel value_nodes == 1 forwarding alias wrappers (GlobalTheory.T.* + all other namespaces)",
            "[L] exact decls & pure-alias files / [L-approx] inline spans",
            len(pure_alias_mods),
            step3_lines_blk,
            step3_lines_tr,
            step3_bytes,
            step3_kernel_decls_removed,
            step3_kernel_vn_removed,
        ),
        (
            "step4_clones_and_k1n_duplicates",
            "Peel surviving alpha-clone modules (4a) + identical-k1n duplicate project theorems (4b)",
            "[L] exact clone files & k1n decls / [L-approx] inline spans",
            step4_mods,
            step4_lines_blk,
            step4_lines_tr,
            step4_bytes,
            step4_kdecls,
            step4_kvn,
        ),
        (
            "step5_duplicate_imports",
            "Peel surviving duplicate `import Mathlib` & duplicate project `import` lines (shims peeled in Step 1)",
            "[L] exact lines",
            0,
            step5_total_lines,
            step5_total_lines,
            step5_bytes,
            0,
            0,
        ),
    ]

    waterfall_steps: List[Dict[str, Any]] = []
    cur_m = total_mods_0
    cur_l_blk = total_lines_0
    cur_l_tr = total_lines_0
    cur_b = total_bytes_0
    cur_kd = total_kdecls_0
    cur_pkd = proj_kdecls_0
    cur_kvn = total_kvn_0
    cur_pkvn = proj_kvn_0

    for sid, label, precision, dm, dl_blk, dl_tr, db_sz, dkd, dkvn in steps_raw:
        nxt_m = cur_m - dm
        nxt_l_blk = cur_l_blk - dl_blk
        nxt_l_tr = cur_l_tr - dl_tr
        nxt_b = cur_b - db_sz
        nxt_kd = cur_kd - dkd
        nxt_pkd = cur_pkd - dkd
        nxt_kvn = cur_kvn - dkvn
        nxt_pkvn = cur_pkvn - dkvn
        waterfall_steps.append({
            "step_id": sid,
            "label": label,
            "precision": precision,
            "before": {
                "modules": cur_m,
                "lines_wc": cur_l_blk,
                "lines_wc_conservative_nonblank": cur_l_tr,
                "bytes": cur_b,
                "kernel_live_decls": cur_kd,
                "kernel_project_live_decls": cur_pkd,
                "kernel_live_value_nodes": cur_kvn,
                "kernel_project_value_nodes": cur_pkvn,
            },
            "removed": {
                "modules": dm,
                "lines_wc": dl_blk,
                "lines_wc_conservative_nonblank": dl_tr,
                "pct_of_corpus_lines": round(100.0 * dl_blk / max(1, total_lines_0), 2),
                "bytes": db_sz,
                "kernel_live_decls": dkd,
                "kernel_live_value_nodes": dkvn,
                "pct_of_corpus_value_nodes": round(100.0 * dkvn / max(1, total_kvn_0), 2),
            },
            "after": {
                "modules": nxt_m,
                "lines_wc": nxt_l_blk,
                "lines_wc_conservative_nonblank": nxt_l_tr,
                "pct_of_corpus_lines": round(100.0 * nxt_l_blk / max(1, total_lines_0), 2),
                "bytes": nxt_b,
                "kernel_live_decls": nxt_kd,
                "kernel_project_live_decls": nxt_pkd,
                "kernel_live_value_nodes": nxt_kvn,
                "kernel_project_value_nodes": nxt_pkvn,
            },
        })
        cur_m, cur_l_blk, cur_l_tr, cur_b = nxt_m, nxt_l_blk, nxt_l_tr, nxt_b
        cur_kd, cur_pkd, cur_kvn, cur_pkvn = nxt_kd, nxt_pkd, nxt_kvn, nxt_pkvn

    # Sanity conservation assertions
    assert cur_m == len(active_mods), f"module conservation mismatch: {cur_m} vs {len(active_mods)}"
    assert cur_l_blk == sum(rem_lines.values()), f"line conservation mismatch: {cur_l_blk} vs {sum(rem_lines.values())}"
    assert cur_kd == len(remaining_kernel_live), f"kernel decl conservation mismatch: {cur_kd} vs {len(remaining_kernel_live)}"

    # Count remaining compiler auxiliaries inside `remaining_kernel_live` for analytical context
    rem_proj_aux = [
        d for d in remaining_kernel_live
        if _is_project_decl(d, ks)
        and (bool(_RE_AUX_NAME.search(id_to_name[d])) or ks["decl_to_method"].get(d, "").startswith("aux_prefix:"))
    ]

    def _k1n_stat(groups: Dict[str, List[int]]) -> Dict[str, int]:
        multi = {k: v for k, v in groups.items() if len(v) >= 2}
        return {
            "duplicate_clusters": len(multi),
            "total_members_in_clusters": sum(len(v) for v in multi.values()),
            "redundant_decls": sum(len(v) - 1 for v in multi.values()),
            "redundant_value_nodes": sum(sum(id_to_vn[x] for x in v[1:]) for v in multi.values()),
        }

    report: Dict[str, Any] = {
        "schema": SCHEMA_VERSION,
        "provenance": "[L] deterministic read-only virtual proof stripper over pinned 40e56bab source + kernel.db + tier1.db",
        "epistemic_scope": {
            "Layer 1": "Kernel validity of `solution.ndjson.zst` (`5ea74b91...244e`) is unchanged; virtual stripping never alters pinned inputs.",
            "Layer 2": "Semantic TCB (`5` headline roots, `2,570` defcone, `209,608` external Mathlib/Lean library decls) is held 100% invariant.",
            "Layer 3": "Quantifies dead modules, dead intra-module decls, 1-node aliases, clones, duplicate `k1n` proofs, phantom struct slots, and macro blowup.",
            "Layer 4": "Virtual size bounds are engineering/architecture measurements, not a referee verdict on mathematical novelty or peer consensus.",
        },
        "pins": {
            "mirror_commit": "40e56bab026552e089d7afcfeff08d2defb9c005",
            "solution_uncompressed_sha256": "5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e",
            "src_dir": _rel_repo_path(src_dir),
            "kernel_db": _rel_repo_path(kernel_db_path),
            "leanre_db": _rel_repo_path(leanre_db_path) if leanre_db_path and os.path.isfile(leanre_db_path) else None,
            "tier1_db": _rel_repo_path(tier1_db_path) if tier1_db_path and os.path.isfile(tier1_db_path) else None,
            "workers_used": workers,
            "elapsed_seconds": round(time.time() - t0, 2),
        },
        "baseline": {
            "total_modules": total_mods_0,
            "total_lines_wc": total_lines_0,
            "total_bytes": total_bytes_0,
            "live_modules_decl_module": len(decl_module_live_mods),
            "live_modules_alignment_gap": len(alignment_gap_mods),
            "live_modules_total": len(live_mods_all),
            "unused_zero_kernel_modules": unused_total_mods,
            "kernel_total_records": ks["total_records"],
            "kernel_dead_records": ks["dead_records"],
            "kernel_live_records": total_kdecls_0,
            "kernel_live_unpacked_constants": ks["live_consts"],
            "kernel_live_type_nodes": ks["live_type_nodes"],
            "kernel_live_value_nodes": total_kvn_0,
            "kernel_project_matched_live": {
                "decls": ks["proj_matched_live"][0],
                "type_nodes": ks["proj_matched_live"][1],
                "value_nodes": ks["proj_matched_live"][2],
            },
            "kernel_project_unmatched_live": {
                "decls": ks["proj_unmatched_live"][0],
                "type_nodes": ks["proj_unmatched_live"][1],
                "value_nodes": ks["proj_unmatched_live"][2],
            },
            "kernel_external_library_live": {
                "decls": ks["ext_live"][0],
                "type_nodes": ks["ext_live"][1],
                "value_nodes": ks["ext_live"][2],
            },
            "kernel_live_by_kind": ks["live_by_kind"],
        },
        "c1_unused_modules": {
            "provenance": "[L] exact",
            "zero_decl_module_total": {
                "modules": unused_total_mods + len(alignment_gap_mods),
                "lines_wc": unused_total_lines + sum(scanned_by_mod[m]["lines_wc"] for m in alignment_gap_mods),
                "bytes": unused_total_bytes + sum(scanned_by_mod[m]["bytes"] for m in alignment_gap_mods),
            },
            "alignment_gap_kept_live": {
                "modules": len(alignment_gap_mods),
                "lines_wc": sum(scanned_by_mod[m]["lines_wc"] for m in alignment_gap_mods),
                "bytes": sum(scanned_by_mod[m]["bytes"] for m in alignment_gap_mods),
            },
            "truly_unused_peeled": {
                "modules": unused_total_mods,
                "pct_of_corpus_modules": round(100.0 * unused_total_mods / max(1, total_mods_0), 2),
                "lines_wc": unused_total_lines,
                "pct_of_corpus_lines": round(100.0 * unused_total_lines / max(1, total_lines_0), 2),
                "bytes": unused_total_bytes,
                "pct_of_corpus_bytes": round(100.0 * unused_total_bytes / max(1, total_bytes_0), 2),
            },
            "buckets": unused_bucket_summary,
            "meta_only_modules": sorted(meta_only_mods),
        },
        "c2_dead_decls_in_live_modules": {
            "provenance": "[L] exact declaration match against kernel.db (`live_mask != 0`); [L-approx] declaration line spans",
            "live_modules_scanned_decl_module": len(decl_module_live_mods),
            "live_modules_scanned_with_alignment_gap": len(live_mods_all),
            "modules_with_at_least_one_dead_decl": mods_with_dead_decls,
            "live_source_decls_total": int(sum(live_decls_by_kind_src.values())),
            "live_source_decls_by_kind": dict(sorted(live_decls_by_kind_src.items())),
            "dead_decls_in_146283_live_modules": dead_decl_in_146283,
            "dead_decls_in_all_live_modules": dead_decl_total,
            "dead_decls_by_kind": dict(sorted(dead_decls_by_kind.items())),
            "dead_lines_in_146283_block": dead_lines_in_146283_block,
            "dead_lines_in_146283_trimmed_nonblank": dead_lines_in_146283_trimmed,
            "dead_lines_block_with_sep": dead_lines_block,
            "dead_lines_trimmed_nonblank": dead_lines_trimmed,
            "dead_bytes_block": dead_bytes_block,
            "caveat": "Lean 4 exports referenced `private`, `instance`, and `structure` decls to `.olean`/NDJSON, whereas an unreferenced `abbrev` (`dead_decls_by_kind['abbrev']`) may have unfolded cleanly during elaboration.",
            "top_bloated_live_modules": top_dead_decl_mods[:25],
        },
        "c3_forwarding_aliases_vn1": {
            "provenance": "[L] exact in kernel.db (`value_nodes == 1` & `fan_out_value == 1`); [L-approx] inline source spans",
            "all_live_vn1_decls": len(vn1_live_ids),
            "project_thm_vn1_total": len(proj_vn1_thm_ids),
            "project_thm_vn1_module_matched": sum(1 for d in proj_vn1_thm_ids if ks["decl_to_mod"].get(d) is not None),
            "project_thm_vn1_global_theory_T": gt_t_vn1_count,
            "project_thm_vn1_other_namespaces": len(proj_vn1_thm_ids) - gt_t_vn1_count,
            "project_def_vn1_total": len(proj_vn1_def_ids),
            "external_library_vn1_kept": len(ext_vn1_thm_ids) + len(ext_vn1_def_ids),
            "project_vn1_type_nodes": step3_kernel_tn_removed,
            "project_vn1_value_nodes": step3_kernel_vn_removed,
            "chain_resolution": {
                "hop_length_histogram": {str(k): v for k, v in sorted(hop_hist.items())},
                "same_k1n_as_1hop_target": same_k1n_1hop,
                "defeq_type_synonym_change_1hop": defeq_type_change_1hop,
                "distinct_non_alias_ultimate_targets": len(ultimate_targets),
                "multi_hop_examples": sample_alias_chains,
            },
            "top_project_namespaces_vn1_thm": [
                {"namespace_2comp": ns, "count": cnt} for ns, cnt in ns2_vn1_thm.most_common(25)
            ],
            "source_footprint_disjoint_after_step2": {
                "pure_alias_live_modules_removed": len(pure_alias_mods),
                "pure_alias_module_lines_removed": pure_alias_lines_blk,
                "inline_alias_spans_in_mixed_modules": inline_alias_spans_cnt,
                "inline_alias_block_lines_removed": inline_alias_lines_blk,
                "inline_alias_trimmed_lines_removed": inline_alias_lines_tr,
                "total_lines_removed_step3": step3_lines_blk,
            },
        },
        "c4_duplicate_imports_and_shims": {
            "provenance": "[L] exact",
            "corpus_raw_totals": {
                "modules_with_duplicate_mathlib_import": raw_dup_ml_files,
                "duplicate_mathlib_import_lines": raw_dup_ml_lines,
                "modules_with_duplicate_project_import": raw_dup_proj_files,
                "duplicate_project_import_lines": raw_dup_proj_lines,
                "duplicate_other_stdlib_import_lines": raw_dup_std_lines,
                "duplicate_all_import_lines": raw_dup_ml_lines + raw_dup_proj_lines + raw_dup_std_lines,
                "strict_import_only_shims": len(raw_strict_shims),
                "strict_import_only_shim_lines": sum(x["lines_wc"] for x in raw_strict_shims),
                "reexport_or_scope_only_shims_total": unused_bucket_summary["import_shim_reexport"]["modules"],
                "reexport_or_scope_only_shim_lines": unused_bucket_summary["import_shim_reexport"]["lines_wc"],
            },
            "stage_accounting_for_all_duplicate_imports": {
                "dup_mathlib_peeled_in_step1_unused_files": dup_ml_in_step1,
                "dup_mathlib_peeled_in_step3_pure_alias_files": dup_ml_in_step3,
                "dup_mathlib_peeled_in_step4_clone_dup_files": dup_ml_in_step4,
                "dup_mathlib_peeled_in_step5_surviving_core": step5_dup_ml_lines,
                "dup_project_peeled_in_step1_unused_files": dup_proj_in_step1,
                "dup_project_peeled_in_step3_pure_alias_files": dup_proj_in_step3,
                "dup_project_peeled_in_step4_clone_dup_files": dup_proj_in_step4,
                "dup_project_peeled_in_step5_surviving_core": step5_dup_proj_lines,
            },
            "disjoint_residual_peeled_in_step5": {
                "surviving_modules_with_dup_mathlib": step5_dup_ml_files,
                "dup_mathlib_lines_removed": step5_dup_ml_lines,
                "surviving_modules_with_dup_project": step5_dup_proj_files,
                "dup_project_lines_removed": step5_dup_proj_lines,
                "total_dup_import_lines_removed": step5_total_lines,
                "pure_shims_residual_lines": 0,
            },
        },
        "c5_clones_and_k1n_duplicates": {
            "provenance": "[L] exact cluster & k1n counts; [L-approx] inline duplicate theorem spans",
            "alpha_body_clone": {
                "raw_clusters": alpha_raw_clusters,
                "raw_member_modules": alpha_raw_mods,
                "raw_redundant_modules": alpha_raw_redundant,
                "raw_redundant_lines_wc": alpha_raw_redundant_lines,
                "members_already_in_step1_unused": alpha_in_unused,
                "members_already_in_step3_pure_alias": alpha_in_pure_alias,
                "step4a_surviving_clusters": surviving_alpha_clusters,
                "step4a_redundant_modules_removed": len(step4a_redundant_mods),
                "step4a_lines_removed": step4a_lines_blk,
                "step4a_kernel_decls_removed": len(step4a_kernel_ids),
                "step4a_kernel_value_nodes_removed": step4a_vn,
            },
            "sigset_clone_header_heuristic": {
                "raw_clusters": sigset_raw_clusters,
                "raw_member_modules": sigset_raw_mods,
                "raw_redundant_modules": sigset_raw_redundant,
                "raw_redundant_lines_wc": sigset_raw_redundant_lines,
                "surviving_live_clusters_after_step4a": sigset_surviving_clusters,
                "surviving_live_redundant_modules": sigset_surviving_redundant_mods,
                "surviving_live_redundant_lines": sigset_surviving_redundant_lines,
                "statement_wrapper_modules_corpus_total": len(stmt_wrapper_mods),
                "note": "Header `s1a` sigset clones abstract project type names; reported as structural upper-bound context, NOT blindly deleted in conservative waterfall.",
            },
            "kernel_k1n_type_duplicates": {
                "all_live_thm": _k1n_stat(k1n_all_thm),
                "user_project_non_aux_thm": _k1n_stat(k1n_user_proj_thm),
                "user_project_non_aux_def_type_collision_only": _k1n_stat(k1n_user_proj_def),
                "step4b_disjoint_after_step3_and_4a": {
                    "clusters": step4b_clusters,
                    "redundant_user_thms": len(step4b_dup_thm_ids),
                    "redundant_thms_plus_exclusive_dom_aux": len(step4b_with_dom_aux),
                    "kernel_value_nodes_removed": step4b_vn,
                    "pure_k1n_dup_modules_removed": len(step4b_pure_mods),
                    "inline_k1n_dup_spans_in_mixed_modules": step4b_inline_spans,
                    "source_lines_removed": step4b_lines_blk,
                },
                "caveat": "Per docs/SIGHASH.md, equal `k1n` on `Prop`-valued `thm`s matches normalized kernel statement AST (modulo binder `()/[]/{}` and N1 `_private` prefix), and earliest `decl_id` substitution preserves DAG acyclicity (`dst < src`). Equal `k1n` on `def`s only means equal type, so `def`s are never deduplicated in Step 4b.",
            },
        },
        "c6_unread_phantom_struct_fields": phantom_audit,
        "c7_macro_proof_term_blowup": macro_audit,
        "c8_waterfall": {
            "steps": waterfall_steps,
            "irreducible_core_estimate": {
                "modules": cur_m,
                "pct_of_corpus_modules": round(100.0 * cur_m / max(1, total_mods_0), 2),
                "lines_wc": cur_l_blk,
                "lines_wc_conservative_nonblank": cur_l_tr,
                "pct_of_corpus_lines": round(100.0 * cur_l_blk / max(1, total_lines_0), 2),
                "bytes": cur_b,
                "pct_of_corpus_bytes": round(100.0 * cur_b / max(1, total_bytes_0), 2),
                "kernel_live_decls_total": cur_kd,
                "kernel_project_live_decls": cur_pkd,
                "kernel_project_non_aux_core_decls": cur_pkd - len(rem_proj_aux),
                "kernel_project_remaining_aux_decls": len(rem_proj_aux),
                "kernel_external_library_decls": ks["ext_live"][0],
                "kernel_live_value_nodes_total": cur_kvn,
                "kernel_project_value_nodes": cur_pkvn,
                "pct_of_corpus_value_nodes": round(100.0 * cur_kvn / max(1, total_kvn_0), 2),
            },
            "further_refactoring_headroom_not_in_main_waterfall": {
                "unread_LiteratureCMHypothesis_dom_subtree_decls": phantom_audit["LiteratureCMHypothesis"]["builder_subtree"].get("dom_subtree_decls", 0),
                "unread_LiteratureCMHypothesis_exclusive_lines": phantom_audit["LiteratureCMHypothesis"]["builder_subtree"].get("exclusive_lines_wc", 0),
                "unread_LiteratureCMHypothesis_value_nodes": phantom_audit["LiteratureCMHypothesis"]["builder_subtree"].get("dom_subtree_value_nodes", 0),
                "copy_cases_lam_plus_sigSpan_value_nodes": macro_audit["copy_cases"]["top2_pair_value_nodes"],
                "surviving_sigset_clone_heuristic_lines": sigset_surviving_redundant_lines,
            },
        },
    }

    if out_path:
        os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
        with open(out_path, "w", encoding="utf-8") as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
            f.write("\n")

    return report


def format_waterfall_text(rep: Dict[str, Any]) -> str:
    """Render a crisp, zero-slop plain-text waterfall table from a `leanre.trim/1` report."""
    b = rep["baseline"]
    w = rep["c8_waterfall"]
    core = w["irreducible_core_estimate"]
    lines = [
        f"leanre trim ({rep['schema']}) — pinned to {rep['pins']['mirror_commit'][:8]}",
        "",
        f"{'Stage':<46} {'Modules':>10} {'wc -l Lines':>14} {'Live Decls':>13} {'Value Nodes':>16}",
        "-" * 103,
        f"{'0. Raw corpus / solution.ndjson.zst [L]':<46} "
        f"{b['total_modules']:>10,} {b['total_lines_wc']:>14,} "
        f"{b['kernel_live_records']:>13,} {b['kernel_live_value_nodes']:>16,}",
    ]
    short_names = {
        "step1_unused_modules": "1. - Unused zero-kernel files [L]",
        "step2_dead_decls_in_live_modules": "2. - Dead decls in live files [L-approx]",
        "step3_1node_alias_wrappers": "3. - 1-node alias wrappers [L / L-approx]",
        "step4_clones_and_k1n_duplicates": "4. - Surviving clones & k1n dups [L-approx]",
        "step5_duplicate_imports": "5. - Surviving duplicate imports [L]",
    }
    for st in w["steps"]:
        rem = st["removed"]
        aft = st["after"]
        nm = short_names.get(st["step_id"], st["step_id"])
        lines.append(
            f"{nm:<46} {-rem['modules']:>10,} {-rem['lines_wc']:>14,} "
            f"{-rem['kernel_live_decls']:>13,} {-rem['kernel_live_value_nodes']:>16,}"
        )
        lines.append(
            f"{'   -> remaining':<46} {aft['modules']:>10,} {aft['lines_wc']:>14,} "
            f"{aft['kernel_live_decls']:>13,} {aft['kernel_live_value_nodes']:>16,}"
        )
    lines.append("-" * 103)
    lines.append(
        f"{'= Irreducible core estimate':<46} {core['modules']:>10,} {core['lines_wc']:>14,} "
        f"{core['kernel_live_decls_total']:>13,} {core['kernel_live_value_nodes_total']:>16,}"
    )
    lines.append(
        f"  (conservative non-blank line bound: {core['lines_wc_conservative_nonblank']:,} lines; "
        f"project live decls: {core['kernel_project_live_decls']:,} "
        f"[{core['kernel_project_non_aux_core_decls']:,} user + {core['kernel_project_remaining_aux_decls']:,} aux] "
        f"+ {core['kernel_external_library_decls']:,} Mathlib/Lean library)"
    )
    return "\n".join(lines)


def _cmd_trim(args: argparse.Namespace) -> int:
    if args.from_report:
        if not os.path.isfile(args.from_report):
            print(f"error: report not found: {args.from_report}", file=sys.stderr)
            return 1
        with open(args.from_report, "r", encoding="utf-8") as f:
            rep = json.load(f)
    else:
        try:
            rep = run_trim(
                src_dir=args.src,
                kernel_db_path=args.kernel_db,
                leanre_db_path=args.leanre_db,
                tier1_db_path=args.tier1_db,
                compute_atlas_path=args.compute_atlas,
                out_path=args.out,
                workers=args.workers,
                verbose=args.verbose,
            )
        except FileNotFoundError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1

    if args.json:
        print(json.dumps(rep, indent=2, ensure_ascii=False))
    else:
        print(format_waterfall_text(rep))
    return 0


def register_cli(sub: Any, dest: str = "trim_func") -> argparse.ArgumentParser:
    """Attach `leanre trim` subcommand to `leanre/leanre.py` argparse subparsers."""
    p = sub.add_parser(
        "trim",
        help="Read-only virtual proof stripper & disjoint bloat waterfall",
    )
    p.add_argument("--src", default=DEFAULT_SRC, help="Path to Lean src/ directory (default: data/rh_mirror/src)")
    p.add_argument("--kernel-db", default=DEFAULT_KERNEL_DB, help="Path to outputs/kernel/kernel.db (mode=ro)")
    p.add_argument("--leanre-db", default=DEFAULT_LEANRE_DB, help="Optional outputs/leanre.db (mode=ro)")
    p.add_argument("--tier1-db", default=DEFAULT_TIER1_DB, help="Optional outputs/flirt/tier1.db (mode=ro)")
    p.add_argument("--compute-atlas", default=DEFAULT_COMPUTE_ATLAS, help="Optional outputs/decomp/compute_atlas.json")
    p.add_argument("--out", default=None, help="Optional path to write trim_report.json")
    p.add_argument("--from-report", default=None, help="Render waterfall directly from an existing trim_report.json")
    p.add_argument("--workers", type=int, default=MAX_WORKERS, help="Parallel worker count (capped at <= 16)")
    p.add_argument("--json", action="store_true", help="Print full JSON report to stdout")
    p.add_argument("-v", "--verbose", action="store_true", help="Verbose progress to stderr")
    p.set_defaults(**{dest: _cmd_trim})
    return p


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(prog="leanre-trim", description="Virtual proof stripper for Lean 4 exports")
    sub = ap.add_subparsers(dest="cmd", required=True)
    register_cli(sub, dest="trim_func")
    argv_list = list(sys.argv[1:] if argv is None else argv)
    if argv_list and argv_list[0] not in ("trim", "-h", "--help"):
        argv_list = ["trim"] + argv_list
    elif not argv_list:
        argv_list = ["trim"]
    args = ap.parse_args(argv_list)
    return int(args.trim_func(args))


if __name__ == "__main__":
    sys.exit(main())
