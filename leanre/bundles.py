#!/usr/bin/env python3
"""leanre.bundles — Exact source-and-kernel 1-constructor structure unread-field auditor.

Combines read-only (`mode=ro`) kernel DAG inspection (`outputs/kernel/kernel.db`) with
optional namespace-aware `.lean` source parsing (`data/rh_mirror/src`) to audit all live
1-constructor project inductives (`structure` / `class` / `inductive`).

Key capabilities:
  - Separates `: Prop` vs `: Type*` structures and resolves `extends` subobjects.
  - Distinguishes true auto-generated field projections from helper theorems sharing the
    `<Struct>.*` prefix (e.g., `Used.adm`, `geometricLemma`, `eSer`, `psi_read`).
  - Checks `casesOn` / `recOn` / `rec` fan-in to eliminate pattern-matched false positives.
  - Flags empty `0`-field `Type` placeholders (e.g., `LPTiedPlaceholder`, `NTiedGPlaceholder`).
  - Detects `abbrev := True` / `def := True` trivial slots (e.g., `UnusedSlot72`) and
    literal `: True` / `:= True` structure fields.

Guardrails:
  - Strictly read-only (`mode=ro`, `PRAGMA query_only=1`) on SQLite inputs.
  - Symlink-safe path resolution under `--src-root`; refuses symlink targets on `--out`.
  - Never emits raw multi-line `.lean` proof bodies or absolute home paths.
  - Python 3.11+ stdlib only; zero third-party dependencies.
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
import tomllib
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple, Union

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import sighash  # noqa: E402

SCHEMA_VERSION = "leanre.bundles/1"
INSTANTIATIONS_SCHEMA_VERSION = "leanre.bundles.instantiations/1"
EDGE_KIND_LABELS = {1: "type", 2: "value", 3: "both"}

DEFAULT_KERNEL_DB = os.path.join(_REPO_ROOT, "outputs", "kernel", "kernel.db")
DEFAULT_SRC_ROOT = os.path.join(_REPO_ROOT, "data", "rh_mirror", "src")

ELIM_NAMES = frozenset({"casesOn", "recOn", "rec"})
AUTO_AUX_NAMES = frozenset({
    "noConfusion",
    "noConfusionType",
    "below",
    "ibelow",
    "brecOn",
    "binductionOn",
})
DECL_MODIFIERS = frozenset({
    "private",
    "protected",
    "noncomputable",
    "nonrec",
    "unsafe",
    "partial",
    "scoped",
    "local",
})

_OPEN_BRACKETS = "([{⦃⟨"
_CLOSE_BRACKETS = ")]}⦄⟩"

_RE_LINE_CMT = re.compile(r"--[^\n]*")
_RE_NS = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.'\u2080-\u2089\u2090-\u209c]*)")
_RE_SEC = re.compile(r"^section(?:\s+([A-Za-z_][A-Za-z0-9_.'\u2080-\u2089\u2090-\u209c]*))?\b")
_RE_END = re.compile(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_.'\u2080-\u2089\u2090-\u209c]*))?\b")
_RE_TOP_CMD = re.compile(
    r"^(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque|example|"
    r"attribute|open|export|variable|variables|universe|universes|set_option|section|end|"
    r"namespace|deriving|omit|include|mutual|import|macro|macro_rules|syntax|elab|elab_rules|"
    r"notation|prefix|infix|infixl|infixr|postfix|declare_syntax_cat|register_simp_attr|"
    r"initialize|run_cmd|run_tac|#)\b"
)
_RE_IDENT_MOD = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)\b")
_RE_STRUCT_KW = re.compile(r"^(structure|class|inductive)\b\s*(.*)$")
_RE_STRUCT_NAME = re.compile(r"^([^\s:(\[⦃⟨]+?)(?:\.\{[^}]*\})?(?=[\s:({\[⦃⟨]|$)")
_RE_CTOR_MARKER = re.compile(r"^[^\s:]+\s*::$")
_RE_CTOR_PREFIX = re.compile(r"^[^\s:]+\s*::\s*")
_RE_FIELD_NAME = re.compile(r"^([^\s:()\[\]{}⦃⦄]+)")
_RE_TRUE_PROP = re.compile(r"(?:^|\s)True(?:\s|$)")
_RE_TRUE_BODY = re.compile(r"^:=\s*(?:fun\b[^=]*=>\s*)?True\b")


def connect_ro(path: str) -> sqlite3.Connection:
    """Open an existing SQLite database strictly in read-only URI mode (`mode=ro`)."""
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"Missing SQLite database: {path}")
    conn = sqlite3.connect(f"file:{real}?mode=ro", uri=True)
    conn.execute("PRAGMA query_only=1")
    return conn


def _rel_repo_path(path: Optional[str]) -> Optional[str]:
    """Format a path relative to repository root so no host/home path leaks."""
    if not path:
        return None
    ap = os.path.abspath(path)
    try:
        rel = os.path.relpath(ap, _REPO_ROOT)
        if not rel.startswith(".."):
            return rel.replace(os.sep, "/")
    except ValueError:
        pass
    return os.path.basename(ap)


def _infer_anchor_prefix(real_src_root: Optional[str]) -> str:
    """Infer relative anchor path prefix (e.g. 'src/' or '') from leanre.toml or Lake root."""
    if not real_src_root:
        return ""
    cur = real_src_root
    for _ in range(5):
        toml_p = os.path.join(cur, "leanre.toml")
        if os.path.isfile(toml_p):
            try:
                with open(toml_p, "rb") as f:
                    cfg_data = tomllib.load(f)
                src_dir = str((cfg_data.get("project") or {}).get("src_dir") or "src").strip()
                cand = os.path.realpath(os.path.join(cur, src_dir))
                if cand == real_src_root or cur == real_src_root:
                    rel = os.path.relpath(real_src_root, os.path.realpath(cur))
                    return "" if rel == "." else rel.replace(os.sep, "/").strip("/") + "/"
            except Exception:
                pass
        for marker in ("lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json"):
            if os.path.exists(os.path.join(cur, marker)):
                rel = os.path.relpath(real_src_root, os.path.realpath(cur))
                return "" if rel == "." else rel.replace(os.sep, "/").strip("/") + "/"
        if os.path.exists(os.path.join(cur, ".git")):
            break
        parent = os.path.dirname(cur)
        if not parent or parent == cur:
            break
        cur = parent
    if os.path.basename(real_src_root) == "src":
        return "src/"
    return ""


def _format_anchor(anchor_prefix: str, mod: Optional[str], line_no: Optional[int]) -> Optional[str]:
    """Format `<anchor_prefix><Module/Path>.lean:<line>` when module and line are known."""
    if not mod or line_no is None:
        return None
    return f"{anchor_prefix}{mod.replace('.', '/')}.lean:{line_no}"


def _safe_resolve_module(real_root: str, module_name: str) -> Optional[str]:
    """Resolve `module_name` to a regular `.lean` file strictly inside `real_root`."""
    if not module_name:
        return None
    parts = module_name.split(".")
    if any(not p or p in (".", "..") or "/" in p or "\\" in p for p in parts):
        return None
    cand = os.path.join(real_root, *parts) + ".lean"
    try:
        real_cand = os.path.realpath(cand)
        if os.path.commonpath([real_root, real_cand]) != real_root:
            return None
    except (OSError, ValueError):
        return None
    if not os.path.isfile(real_cand):
        return None
    return real_cand


def _safe_write_json(out_path: str, payload: Any) -> None:
    """Write JSON report to `out_path`, refusing symlink targets."""
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    parent = os.path.dirname(os.path.abspath(out_path))
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, ensure_ascii=False)
        f.write("\n")


def _strip_comments(text: str) -> str:
    """Remove `-- ...` and nested `/- ... -/` comments while preserving line numbers."""
    if "/-" not in text:
        if "--" in text:
            return _RE_LINE_CMT.sub("", text)
        return text
    out: List[str] = []
    i = 0
    n = len(text)
    depth = 0
    in_str = False
    while i < n:
        c = text[i]
        if depth == 0 and c == '"' and (i == 0 or text[i - 1] != "\\"):
            in_str = not in_str
            out.append(c)
            i += 1
            continue
        if in_str:
            out.append(c)
            i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            if c == "\n":
                out.append("\n")
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(c)
        i += 1
    return "".join(out)


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
        m = _RE_IDENT_MOD.match(stmt[pos:])
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


def _depth0_find(s: str, ch: str) -> int:
    depth = 0
    in_str = False
    for i, c in enumerate(s):
        if c == '"' and (i == 0 or s[i - 1] != "\\"):
            in_str = not in_str
        elif not in_str:
            if c in _OPEN_BRACKETS:
                depth += 1
            elif c in _CLOSE_BRACKETS:
                depth = max(0, depth - 1)
            elif depth == 0 and c == ch and not s.startswith(":=", i):
                return i
    return -1


def _depth0_split(s: str, ch: str) -> List[str]:
    out: List[str] = []
    depth = 0
    cur: List[str] = []
    in_str = False
    for i, c in enumerate(s):
        if c == '"' and (i == 0 or s[i - 1] != "\\"):
            in_str = not in_str
        elif not in_str:
            if c in _OPEN_BRACKETS:
                depth += 1
            elif c in _CLOSE_BRACKETS:
                depth = max(0, depth - 1)
        if not in_str and depth == 0 and c == ch:
            out.append("".join(cur))
            cur = []
        else:
            cur.append(c)
    out.append("".join(cur))
    return out


def _is_kw_at(text: str, idx: int, kw: str) -> bool:
    if not text.startswith(kw, idx):
        return False
    before = idx == 0 or not (text[idx - 1].isalnum() or text[idx - 1] in "_.'")
    end = idx + len(kw)
    after = end >= len(text) or not (text[end].isalnum() or text[end] in "_.'")
    return before and after


def _split_header_body(blk: str) -> Tuple[str, str, str]:
    depth = 0
    in_str = False
    i = 0
    n = len(blk)
    while i < n:
        ch = blk[i]
        if ch == '"' and (i == 0 or blk[i - 1] != "\\"):
            in_str = not in_str
        elif not in_str:
            if ch in _OPEN_BRACKETS:
                depth += 1
            elif ch in _CLOSE_BRACKETS:
                depth = max(0, depth - 1)
            elif depth == 0:
                if _is_kw_at(blk, i, "where"):
                    return blk[:i], "where", blk[i + 5 :]
                if blk.startswith(":=", i):
                    return blk[:i], ":=", blk[i + 2 :]
                if ch == "\n":
                    j = i + 1
                    while j < n and blk[j] in " \t":
                        j += 1
                    if j < n and blk[j] == "|":
                        return blk[:i], "|", blk[j:]
        i += 1
    return blk, "", ""


def _parse_extends_names(extends_entries: Sequence[str]) -> List[str]:
    """Derive expected Lean subobject projection names (`to<Parent>`) from `extends` clauses."""
    subobjs: List[str] = []
    for entry in extends_entries:
        j = _depth0_find(entry, ":")
        if j >= 0:
            explicit = entry[:j].strip().split()[0]
            if explicit:
                subobjs.append(explicit)
            continue
        head = entry.strip().split()[0] if entry.strip() else ""
        head = head.split("(", 1)[0].split("{", 1)[0].split("[", 1)[0].rstrip(".")
        if head:
            leaf = head.rsplit(".", 1)[-1]
            subobjs.append(f"to{leaf}")
    return subobjs


def _parse_header_info(hdr: str) -> Tuple[bool, List[str], List[str]]:
    rest, _, _ = _strip_leading_attrs_and_mods(hdr.strip())
    m = _RE_STRUCT_KW.match(rest)
    tail = m.group(2) if m else rest
    if tail.startswith("inductive "):
        tail = tail[10:].lstrip()
    nm_m = _RE_STRUCT_NAME.match(tail)
    after_nm = tail[nm_m.end() :] if nm_m else tail

    typ: Optional[str] = None
    extends_raw: List[str] = []
    depth = 0
    in_str = False
    i = 0
    n = len(after_nm)
    while i < n:
        c = after_nm[i]
        if c == '"' and (i == 0 or after_nm[i - 1] != "\\"):
            in_str = not in_str
        elif not in_str:
            if c in _OPEN_BRACKETS:
                depth += 1
            elif c in _CLOSE_BRACKETS:
                depth = max(0, depth - 1)
            elif depth == 0:
                if c == ":" and not after_nm.startswith(":=", i):
                    typ = after_nm[i + 1 :].strip()
                    break
                if _is_kw_at(after_nm, i, "extends"):
                    ext = after_nm[i + 7 :]
                    j = _depth0_find(ext, ":")
                    ext_part = ext if j < 0 else ext[:j]
                    typ = None if j < 0 else ext[j + 1 :].strip()
                    extends_raw = [e.strip() for e in _depth0_split(ext_part, ",") if e.strip()]
                    break
        i += 1

    if typ:
        depth = 0
        in_str = False
        for k, c in enumerate(typ):
            if c == '"' and (k == 0 or typ[k - 1] != "\\"):
                in_str = not in_str
            elif not in_str:
                if c in _OPEN_BRACKETS:
                    depth += 1
                elif c in _CLOSE_BRACKETS:
                    depth = max(0, depth - 1)
                elif depth == 0 and _is_kw_at(typ, k, "extends"):
                    ext_part = typ[k + 7 :].strip()
                    typ = typ[:k].strip()
                    extends_raw = [e.strip() for e in _depth0_split(ext_part, ",") if e.strip()]
                    break

    t_norm = " ".join((typ or "").split())
    is_prop = bool(t_norm == "Prop" or re.search(r"(?:→|->)\s*Prop\s*$", t_norm))
    return is_prop, extends_raw, _parse_extends_names(extends_raw)


def _is_literal_true_field(field_text: str) -> bool:
    """Return True if a structure field declares literal `: True` or default `:= True`."""
    j = _depth0_find(field_text, ":")
    if j >= 0:
        rhs = field_text[j + 1 :].strip()
        k = rhs.find(":=")
        if k >= 0 and _depth0_find(rhs[:k] + " ", ":") < 0:
            typ_part = rhs[:k].strip()
            dflt_part = rhs[k + 2 :].strip()
            if typ_part == "True" or dflt_part == "True":
                return True
        elif rhs == "True":
            return True
    else:
        k = field_text.find(":=")
        if k >= 0 and field_text[k + 2 :].strip() == "True":
            return True
    return False


def _parse_where_fields(body: str) -> Tuple[List[str], List[str]]:
    raw_lines = body.splitlines()
    lines: List[str] = []
    for idx, ln in enumerate(raw_lines):
        if idx == 0:
            s = ln.strip()
            if not s or _RE_CTOR_MARKER.match(s):
                continue
            if "::" in s and _RE_CTOR_PREFIX.match(s):
                s = _RE_CTOR_PREFIX.sub("", s)
                if s:
                    lines.append("  " + s)
                continue
            lines.append("  " + s)
            continue
        lines.append(ln)

    blocks: List[List[str]] = []
    base: Optional[int] = None
    for ln in lines:
        s = ln.strip()
        if not s:
            continue
        ind = len(ln) - len(ln.lstrip(" "))
        if base is None:
            if _RE_CTOR_MARKER.match(s):
                continue
            base = ind
        if ind < base and s.startswith("deriving"):
            break
        if ind <= base:
            if _RE_CTOR_MARKER.match(s):
                continue
            blocks.append([s])
        elif blocks:
            blocks[-1].append(s)

    fields: List[str] = []
    literal_true_fields: List[str] = []
    for b in blocks:
        txt = " ".join(b)
        if txt.startswith("deriving"):
            continue
        if txt[0] in "([{" and txt[-1] in ")]}":
            inner = txt[1:-1].strip()
        elif txt[0] in "([{":
            inner = txt[1:].strip()
        else:
            inner = txt
        m = _RE_FIELD_NAME.match(inner)
        if m:
            fname = m.group(1)
            fields.append(fname)
            if _is_literal_true_field(inner):
                literal_true_fields.append(fname)
    return fields, literal_true_fields


def _parse_ind_fields(body: str) -> List[str]:
    m = re.match(r"^\|\s*([^\s:()\[\]{}⦃⦄]+)\s*(.*)$", body.strip(), re.S)
    if not m:
        return []
    rest = m.group(2)
    depth = 0
    in_str = False
    start: Optional[int] = None
    fields: List[str] = []
    for i, c in enumerate(rest):
        if c == '"' and (i == 0 or rest[i - 1] != "\\"):
            in_str = not in_str
        elif not in_str:
            if c in _OPEN_BRACKETS:
                if depth == 0:
                    start = i
                depth += 1
            elif c in _CLOSE_BRACKETS:
                depth = max(0, depth - 1)
                if depth == 0 and start is not None:
                    bhead = rest[start + 1 : i].strip().split(":", 1)[0].strip()
                    for tok in bhead.split():
                        if tok != "_":
                            fields.append(tok)
                    start = None
            elif depth == 0 and c == ":":
                break
    return fields


def _multi_line_header_extent(lines: Sequence[str], start_idx: int, max_lines: int = 80) -> str:
    parts: List[str] = []
    depth = 0
    for idx in range(start_idx, min(len(lines), start_idx + max_lines)):
        s = lines[idx].strip()
        if not s:
            break
        parts.append(s)
        for ch in s:
            if ch in "[({":
                depth += 1
            elif ch in "])}":
                depth = max(0, depth - 1)
        if depth == 0 and not s.startswith("@["):
            break
        if idx > start_idx and depth == 0 and not s.endswith("]"):
            break
    return " ".join(parts)


def parse_lean_structures_in_text(text: str, module_name: str) -> Dict[str, Dict[str, Any]]:
    """Parse all `structure` / `class` / `inductive` declarations in one `.lean` module."""
    lines = _strip_comments(text).splitlines()
    n = len(lines)
    ns_stack: List[Tuple[str, List[str]]] = []
    out: Dict[str, Dict[str, Any]] = {}
    i = 0
    while i < n:
        raw = lines[i]
        s = raw.strip()
        if not s:
            i += 1
            continue

        m_ns = _RE_NS.match(s)
        if m_ns and (not raw[0].isspace() or ns_stack):
            ns_stack.append(("ns", m_ns.group(1).split(".")))
            i += 1
            continue

        m_sec = _RE_SEC.match(s)
        if m_sec and (not raw[0].isspace() or ns_stack):
            sec_nm = [m_sec.group(1)] if m_sec.group(1) else []
            ns_stack.append(("sec", sec_nm))
            i += 1
            continue

        if s == "mutual" and (not raw[0].isspace() or ns_stack):
            ns_stack.append(("mutual", []))
            i += 1
            continue

        m_end = _RE_END.match(s)
        if m_end and (s == "end" or re.match(r"^end\s+[A-Za-z_]", s)) and (not raw[0].isspace() or ns_stack):
            _pop_end_stack(ns_stack, m_end.group(1))
            i += 1
            continue

        indent = len(raw) - len(raw.lstrip(" "))
        if indent == 0 or (ns_stack and indent <= 2):
            rest, _attrs, mods = _strip_leading_attrs_and_mods(s)
            if not rest and s.startswith("@["):
                hdr = _multi_line_header_extent(lines, i)
                rest, _attrs, mods = _strip_leading_attrs_and_mods(hdr)

            m = _RE_STRUCT_KW.match(rest)
            if m and not (m.group(1) == "class" and m.group(2).startswith("abbrev ")):
                kw = m.group(1)
                tail = m.group(2)
                if kw == "class" and tail.startswith("inductive "):
                    kw = "inductive"
                    tail = tail[10:].lstrip()

                j = i + 1
                while j < n:
                    lnj = lines[j]
                    sj = lnj.strip()
                    if sj:
                        indj = len(lnj) - len(lnj.lstrip(" "))
                        if indj <= indent:
                            r2, _, _ = _strip_leading_attrs_and_mods(sj)
                            if (
                                _RE_NS.match(sj)
                                or _RE_SEC.match(sj)
                                or _RE_END.match(sj)
                                or sj == "mutual"
                                or _RE_TOP_CMD.match(r2)
                                or sj.startswith("@[")
                            ):
                                break
                    j += 1

                blk = "\n".join(lines[i:j])
                nm_m = _RE_STRUCT_NAME.match(tail)
                raw_nm = nm_m.group(1).rstrip(".") if nm_m else ""
                fqn = _normalize_fqn(_current_ns(ns_stack), raw_nm)
                fqn_priv = f"_private.{module_name}.0.{fqn}" if "private" in mods else fqn

                hdr_part, term, body = _split_header_body(blk)
                is_prop, extends_raw, subobj_names = _parse_header_info(hdr_part)
                literal_true_fields: List[str] = []
                if kw in ("structure", "class") and term == "where":
                    fields, literal_true_fields = _parse_where_fields(body)
                elif kw == "inductive" and term == "|":
                    fields = _parse_ind_fields(body)
                else:
                    fields = []

                rec = {
                    "source_kind": kw,
                    "line": i + 1,
                    "is_prop": is_prop,
                    "extends": extends_raw,
                    "subobject_names": subobj_names,
                    "fields": fields,
                    "literal_true_fields": literal_true_fields,
                }
                out[fqn] = rec
                if fqn_priv != fqn:
                    out[fqn_priv] = rec
                i = j
                continue

        i += 1
    return out


def parse_true_defs_in_text(text: str, module_name: str) -> Dict[str, Dict[str, Any]]:
    """Extract `abbrev` / `def` declarations whose body is trivially `True`."""
    lines = _strip_comments(text).splitlines()
    n = len(lines)
    ns_stack: List[Tuple[str, List[str]]] = []
    out: Dict[str, Dict[str, Any]] = {}
    i = 0
    while i < n:
        raw = lines[i]
        s = raw.strip()
        if not s:
            i += 1
            continue
        m_ns = _RE_NS.match(s)
        if m_ns and (not raw[0].isspace() or ns_stack):
            ns_stack.append(("ns", m_ns.group(1).split(".")))
            i += 1
            continue
        m_sec = _RE_SEC.match(s)
        if m_sec and (not raw[0].isspace() or ns_stack):
            ns_stack.append(("sec", [m_sec.group(1)] if m_sec.group(1) else []))
            i += 1
            continue
        if s == "mutual" and (not raw[0].isspace() or ns_stack):
            ns_stack.append(("mutual", []))
            i += 1
            continue
        m_end = _RE_END.match(s)
        if m_end and (s == "end" or re.match(r"^end\s+[A-Za-z_]", s)) and (not raw[0].isspace() or ns_stack):
            _pop_end_stack(ns_stack, m_end.group(1))
            i += 1
            continue

        indent = len(raw) - len(raw.lstrip(" "))
        if indent == 0 or (ns_stack and indent <= 2):
            rest, _attrs, mods = _strip_leading_attrs_and_mods(s)
            m = re.match(r"^(abbrev|def)\b\s*(.*)$", rest)
            if m:
                kw = m.group(1)
                tail = m.group(2)
                j = i + 1
                while j < n:
                    lnj = lines[j]
                    sj = lnj.strip()
                    if sj:
                        indj = len(lnj) - len(lnj.lstrip(" "))
                        if indj <= indent:
                            r2, _, _ = _strip_leading_attrs_and_mods(sj)
                            if _RE_NS.match(sj) or _RE_SEC.match(sj) or _RE_END.match(sj) or sj == "mutual" or _RE_TOP_CMD.match(r2) or sj.startswith("@["):
                                break
                    j += 1
                blk = " ".join(ln.strip() for ln in lines[i:j] if ln.strip())
                nm_m = _RE_STRUCT_NAME.match(tail)
                raw_nm = nm_m.group(1).rstrip(".") if nm_m else ""
                fqn = _normalize_fqn(_current_ns(ns_stack), raw_nm)
                fqn_priv = f"_private.{module_name}.0.{fqn}" if "private" in mods else fqn
                _hdr, term, body = _split_header_body(blk)
                if term == ":=" and _RE_TRUE_BODY.match(":=" + body):
                    rec = {"source_kind": kw, "line": i + 1, "is_trivial_true": True}
                    out[fqn] = rec
                    if fqn_priv != fqn:
                        out[fqn_priv] = rec
                i = j
                continue
        i += 1
    return out


def _detect_true_slots(
    kconn: sqlite3.Connection,
    struct_ids: Sequence[int],
    id_to_struct_name: Dict[int, str],
    real_src_root: Optional[str],
    mod_file_cache: Dict[str, Optional[str]],
    anchor_prefix: str = "src/",
) -> List[Dict[str, Any]]:
    """Detect `abbrev := True` / `def := True` slots and referencing structures."""
    row_true = kconn.execute("SELECT id FROM decls WHERE name = 'True'").fetchone()
    if row_true is None:
        return []
    true_id = int(row_true[0])

    cands = kconn.execute(
        """
        SELECT d.id, d.name, d.type_nodes, d.value_nodes, d.fan_in, d.fan_out_value,
               dm.module, COALESCE(r.depth, -1)
        FROM edges e
        JOIN decls d ON e.src = d.id
        LEFT JOIN decl_module dm ON dm.decl_id = d.id
        LEFT JOIN reach r ON r.root_id = 0 AND r.decl_id = d.id
        WHERE e.dst = ? AND e.kind IN (2, 3) AND d.kind = 'def' AND d.live_mask != 0
          AND (dm.module IS NOT NULL OR dm.method LIKE 'unmatched:project%')
        ORDER BY d.fan_in DESC, d.id
        """,
        (true_id,),
    ).fetchall()

    confirmed: Dict[int, Dict[str, Any]] = {}
    src_text_cache: Dict[str, Dict[str, Dict[str, Any]]] = {}

    for did, nm, tn, vn, fi, fov, mod, rh_dep in cands:
        is_exact_vn1 = (vn == 1 and fov == 1)
        src_kind = "abbrev/def"
        line_no: Optional[int] = None
        src_hit = False

        if real_src_root and mod:
            if mod not in src_text_cache:
                fpath = mod_file_cache.get(mod)
                if fpath is None and mod not in mod_file_cache:
                    fpath = _safe_resolve_module(real_src_root, mod)
                    mod_file_cache[mod] = fpath
                if fpath:
                    with open(fpath, "r", encoding="utf-8", errors="replace") as f:
                        src_text_cache[mod] = parse_true_defs_in_text(f.read(), mod)
                else:
                    src_text_cache[mod] = {}
            sinfo = src_text_cache[mod].get(nm)
            if sinfo:
                src_hit = True
                src_kind = sinfo["source_kind"]
                line_no = sinfo["line"]

        if is_exact_vn1 or src_hit:
            anchor = _format_anchor(anchor_prefix, mod, line_no)
            rdep = None if rh_dep < 0 else int(rh_dep)
            confirmed[did] = {
                "decl_id": did,
                "name": nm,
                "source_kind": src_kind,
                "value_nodes": vn,
                "type_nodes": tn,
                "fan_in": fi,
                "root_depth": rdep,
                "rh_depth": rdep,
                "module": mod,
                "anchor": anchor,
                "referenced_by_structures": [],
            }

    if confirmed and struct_ids:
        slot_ids = sorted(confirmed.keys())
        slot_qs = ",".join("?" for _ in slot_ids)
        for i in range(0, len(struct_ids), 900):
            chunk = struct_ids[i : i + 900]
            s_qs = ",".join("?" for _ in chunk)
            for src_sid, dst_slot in kconn.execute(
                f"SELECT src, dst FROM edges WHERE dst IN ({slot_qs}) AND src IN ({s_qs})",
                (*slot_ids, *chunk),
            ):
                sname = id_to_struct_name.get(src_sid)
                if sname and sname not in confirmed[dst_slot]["referenced_by_structures"]:
                    confirmed[dst_slot]["referenced_by_structures"].append(sname)

    out = list(confirmed.values())
    for item in out:
        item["referenced_by_structures"].sort()
    out.sort(key=lambda x: (-x["fan_in"], x["name"]))
    return out


def _matches_structure_filter(name: str, query: str, exact: bool = False) -> int:
    """Return match priority (exact-case before case-insensitive):
    6=exact-case FQN, 5=exact-case dot-suffix, 4=exact-case substring,
    3=ci FQN, 2=ci dot-suffix, 1=ci substring, 0=no match.
    Substring priorities (4, 1) are disabled when `exact=True`.
    """
    if name == query:
        return 6
    if name.endswith("." + query):
        return 5
    if not exact and query in name:
        return 4
    nl = name.lower()
    ql = query.lower()
    if nl == ql:
        return 3
    if nl.endswith("." + ql):
        return 2
    if not exact and ql in nl:
        return 1
    return 0


def _normalize_structure_queries(structure: Optional[Union[str, Sequence[str]]]) -> List[str]:
    """Normalize single, comma-separated, or repeatable `--structure`/`--instantiations` args."""
    if structure is None:
        return []
    raw_items: Sequence[str] = [structure] if isinstance(structure, str) else list(structure)
    out: List[str] = []
    seen: Set[str] = set()
    for item in raw_items:
        if not item:
            continue
        for part in str(item).split(","):
            q = part.strip()
            if q and q not in seen:
                seen.add(q)
                out.append(q)
    return out


def _is_one_ctor_decl(kconn: sqlite3.Connection, decl_id: int) -> bool:
    """Check in O(1) via `consts_decl` index whether `decl_id` has exactly 1 constructor."""
    row = kconn.execute(
        "SELECT COUNT(*) FROM consts WHERE decl_id = ? AND ckind = 'ctor'",
        (decl_id,),
    ).fetchone()
    return bool(row and int(row[0]) == 1)


def _resolve_targeted_one_ctor(
    kconn: sqlite3.Connection,
    queries: Sequence[str],
    allow_dead_fallback: bool = False,
    exact: bool = False,
) -> Tuple[List[Tuple[Any, ...]], Dict[str, List[int]]]:
    """Resolve one or more structure queries without scanning all 2.5M `consts` or `.lean` files."""
    if not queries:
        return [], {}

    per_query_rows: Dict[str, List[Tuple[Any, ...]]] = {}
    unresolved: List[str] = []

    # Fast Path A: O(1) index lookup on `decls_name` for exact FQN queries
    for q in queries:
        row = kconn.execute(
            """
            SELECT d.id, d.name, d.fan_in, d.type_nodes, d.value_nodes, dm.module, dm.method, d.live_mask
            FROM decls d
            JOIN decl_module dm ON d.id = dm.decl_id
            WHERE d.name = ? AND d.live_mask != 0 AND d.kind = 'inductive'
              AND (dm.module IS NOT NULL OR dm.method LIKE 'unmatched:project%')
            """,
            (q,),
        ).fetchone()
        if row is not None and _is_one_ctor_decl(kconn, int(row[0])):
            per_query_rows[q] = [row]
        else:
            unresolved.append(q)

    # Fast Path B: single inductive header pass for suffix / (optional) substring queries
    if unresolved:
        live_ind_rows = kconn.execute(
            """
            SELECT d.id, d.name, d.fan_in, d.type_nodes, d.value_nodes, dm.module, dm.method, d.live_mask
            FROM decls d
            JOIN decl_module dm ON d.id = dm.decl_id
            WHERE d.live_mask != 0 AND d.kind = 'inductive'
              AND (dm.module IS NOT NULL OR dm.method LIKE 'unmatched:project%')
            ORDER BY d.id
            """
        ).fetchall()
        ctor_memo: Dict[int, bool] = {}

        def _check_1c(did: int) -> bool:
            res = ctor_memo.get(did)
            if res is None:
                res = _is_one_ctor_decl(kconn, did)
                ctor_memo[did] = res
            return res

        still_missing: List[str] = []
        priorities = (6, 5, 3, 2) if exact else (6, 5, 4, 3, 2, 1)
        for q in unresolved:
            buckets: Dict[int, List[Tuple[Any, ...]]] = {p: [] for p in range(1, 7)}
            for r in live_ind_rows:
                p = _matches_structure_filter(r[1], q, exact=exact)
                if p > 0:
                    buckets[p].append(r)
            matched_q: List[Tuple[Any, ...]] = []
            for p in priorities:
                if buckets[p]:
                    cands = [r for r in buckets[p] if _check_1c(int(r[0]))]
                    if cands:
                        matched_q = cands
                        break
            if matched_q:
                per_query_rows[q] = matched_q
            else:
                still_missing.append(q)

        if still_missing and allow_dead_fallback:
            dead_ind_rows = kconn.execute(
                """
                SELECT d.id, d.name, d.fan_in, d.type_nodes, d.value_nodes, dm.module, dm.method, d.live_mask
                FROM decls d
                JOIN decl_module dm ON d.id = dm.decl_id
                WHERE d.live_mask = 0 AND d.kind = 'inductive'
                  AND (dm.module IS NOT NULL OR dm.method LIKE 'unmatched:project%')
                ORDER BY d.id
                """
            ).fetchall()
            for q in still_missing:
                buckets_d: Dict[int, List[Tuple[Any, ...]]] = {p: [] for p in range(1, 7)}
                for r in dead_ind_rows:
                    p = _matches_structure_filter(r[1], q, exact=exact)
                    if p > 0:
                        buckets_d[p].append(r)
                for p in priorities:
                    if buckets_d[p]:
                        cands = [r for r in buckets_d[p] if _check_1c(int(r[0]))]
                        if cands:
                            per_query_rows[q] = cands
                            break

    unique_rows: List[Tuple[Any, ...]] = []
    seen_ids: Set[int] = set()
    query_map: Dict[str, List[int]] = {}
    for q in queries:
        q_rows = per_query_rows.get(q, [])
        query_map[q] = [int(r[0]) for r in q_rows]
        for r in q_rows:
            did = int(r[0])
            if did not in seen_ids:
                seen_ids.add(did)
                unique_rows.append(r)
    return unique_rows, query_map


def _strip_outer_parens_str(s: str) -> str:
    s = s.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0
        in_str = False
        matched = True
        for idx, c in enumerate(s):
            if c == '"' and (idx == 0 or s[idx - 1] != "\\"):
                in_str = not in_str
            elif not in_str:
                if c in _OPEN_BRACKETS:
                    depth += 1
                elif c in _CLOSE_BRACKETS:
                    depth = max(0, depth - 1)
                    if depth == 0 and idx < len(s) - 1:
                        matched = False
                        break
        if matched:
            s = s[1:-1].strip()
        else:
            break
    return s


def _split_depth0_and(body: str) -> List[str]:
    """Split a Prop expression at top-level `∧` / `/\\` into conjuncts."""
    s = _strip_outer_parens_str(body)
    if not s or re.match(r"^(?:∀|∃|λ|(?:forall|exists|fun)\b)", s):
        return []
    parts: List[str] = []
    cur: List[str] = []
    depth = 0
    in_str = False
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c == '"' and (i == 0 or s[i - 1] != "\\"):
            in_str = not in_str
            cur.append(c)
            i += 1
            continue
        if in_str:
            cur.append(c)
            i += 1
            continue
        if c in _OPEN_BRACKETS:
            depth += 1
        elif c in _CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif depth == 0:
            if c == "∧":
                part = _strip_outer_parens_str(" ".join("".join(cur).split()))
                if part:
                    parts.append(part)
                cur = []
                i += 1
                continue
            if s.startswith("/\\", i):
                part = _strip_outer_parens_str(" ".join("".join(cur).split()))
                if part:
                    parts.append(part)
                cur = []
                i += 2
                continue
        cur.append(c)
        i += 1
    last = _strip_outer_parens_str(" ".join("".join(cur).split()))
    if last:
        parts.append(last)
    return parts if len(parts) > 1 else []


def parse_prop_defs_in_text(text: str, module_name: str) -> Dict[str, Dict[str, Any]]:
    """Parse `def` / `abbrev` declarations in one module and identify `Prop`-valued ones."""
    lines = _strip_comments(text).splitlines()
    n = len(lines)
    ns_stack: List[Tuple[str, List[str]]] = []
    out: Dict[str, Dict[str, Any]] = {}
    i = 0
    while i < n:
        raw = lines[i]
        s = raw.strip()
        if not s:
            i += 1
            continue
        m_ns = _RE_NS.match(s)
        if m_ns and (not raw[0].isspace() or ns_stack):
            ns_stack.append(("ns", m_ns.group(1).split(".")))
            i += 1
            continue
        m_sec = _RE_SEC.match(s) or _RE_NONCOMP_SEC.match(s)
        if m_sec and (not raw[0].isspace() or ns_stack):
            ns_stack.append(("sec", [m_sec.group(1)] if m_sec.group(1) else []))
            i += 1
            continue
        if s == "mutual" and (not raw[0].isspace() or ns_stack):
            ns_stack.append(("mutual", []))
            i += 1
            continue
        m_end = _RE_END.match(s)
        if m_end and (s == "end" or re.match(r"^end\s+[A-Za-z_]", s)) and (not raw[0].isspace() or ns_stack):
            _pop_end_stack(ns_stack, m_end.group(1))
            i += 1
            continue

        indent = len(raw) - len(raw.lstrip(" "))
        if indent == 0 or (ns_stack and indent <= 2):
            rest, _attrs, mods = _strip_leading_attrs_and_mods(s)
            if not rest and s.startswith("@["):
                hdr0 = _multi_line_header_extent(lines, i)
                rest, _attrs, mods = _strip_leading_attrs_and_mods(hdr0)
            m = re.match(r"^(abbrev|def)\b\s*(.*)$", rest)
            if m:
                kw = m.group(1)
                tail = m.group(2)
                j = i + 1
                while j < n:
                    lnj = lines[j]
                    sj = lnj.strip()
                    if sj:
                        indj = len(lnj) - len(lnj.lstrip(" "))
                        if indj <= indent:
                            r2, _, _ = _strip_leading_attrs_and_mods(sj)
                            if (
                                _RE_NS.match(sj)
                                or _RE_SEC.match(sj)
                                or _RE_NONCOMP_SEC.match(sj)
                                or _RE_END.match(sj)
                                or sj == "mutual"
                                or _RE_TOP_CMD.match(r2)
                                or sj.startswith("@[")
                            ):
                                break
                    j += 1
                blk = "\n".join(lines[i:j])
                nm_m = _RE_STRUCT_NAME.match(tail)
                raw_nm = nm_m.group(1).rstrip(".") if nm_m else ""
                fqn = _normalize_fqn(_current_ns(ns_stack), raw_nm)
                fqn_priv = f"_private.{module_name}.0.{fqn}" if "private" in mods else fqn
                hdr_part, term, body = _split_header_body(blk)
                hdr_1line = " ".join(hdr_part.split())
                hd = sighash.split_header(hdr_1line)
                has_explicit_prop = False
                has_empty_type = False
                if hd:
                    entries: List[Tuple[str, List[str]]] = []
                    for b in hd["binders"]:
                        entries.extend(sighash._binder_entries(b))
                    concl = sighash._hoist(list(hd["type"]), entries)
                    has_explicit_prop = (concl == ["Prop"])
                    has_empty_type = not hd["type"]
                conjuncts = _split_depth0_and(body) if term == ":=" else []
                clean_hdr = hdr_1line if len(hdr_1line) <= 220 else hdr_1line[:219] + "…"
                rec = {
                    "source_kind": kw,
                    "line": i + 1,
                    "has_explicit_prop": has_explicit_prop,
                    "has_empty_type": has_empty_type,
                    "conjuncts": [c if len(c) <= 140 else c[:139] + "…" for c in conjuncts],
                    "header": clean_hdr,
                }
                out[fqn] = rec
                if fqn_priv != fqn:
                    out[fqn_priv] = rec
                i = j
                continue
        i += 1
    return out


def _is_prop_def_row(
    kconn: sqlite3.Connection,
    did: int,
    nm: str,
    mod: Optional[str],
    real_src_root: Optional[str],
    prop_mod_cache: Dict[str, Dict[str, Dict[str, Any]]],
    mod_file_cache: Dict[str, Optional[str]],
) -> Tuple[bool, Optional[Dict[str, Any]]]:
    """Check whether a `def` declaration is a `Prop`-valued definition/abbrev."""
    pinfo: Optional[Dict[str, Any]] = None
    if real_src_root and mod:
        if mod not in prop_mod_cache:
            fpath = mod_file_cache.get(mod)
            if fpath is None and mod not in mod_file_cache:
                fpath = _safe_resolve_module(real_src_root, mod)
                mod_file_cache[mod] = fpath
            if fpath:
                with open(fpath, "r", encoding="utf-8", errors="replace") as f:
                    prop_mod_cache[mod] = parse_prop_defs_in_text(f.read(), mod)
            else:
                prop_mod_cache[mod] = {}
        pinfo = prop_mod_cache[mod].get(nm)
        if pinfo is not None:
            if pinfo["has_explicit_prop"]:
                return True, pinfo
            if not pinfo["has_empty_type"]:
                return False, None
    has_thm_in = kconn.execute(
        """
        SELECT 1 FROM edges e
        JOIN decls d ON e.src = d.id
        WHERE e.dst = ? AND e.kind IN (1, 3) AND d.kind = 'thm'
        LIMIT 1
        """,
        (did,),
    ).fetchone()
    if has_thm_in is not None:
        return True, pinfo
    return False, None


def _diagnose_unmatched_queries(
    kconn: sqlite3.Connection,
    unmatched_qs: Sequence[str],
    exact: bool = False,
    real_src_root: Optional[str] = None,
) -> List[Dict[str, Any]]:
    """Classify why targeted `--structure` queries failed to match a live 1-ctor project structure."""
    if not unmatched_qs:
        return []

    ctor_memo: Dict[int, int] = {}
    prop_mod_cache: Dict[str, Dict[str, Dict[str, Any]]] = {}
    mod_file_cache: Dict[str, Optional[str]] = {}

    def _ctor_count(did: int) -> int:
        cnt = ctor_memo.get(did)
        if cnt is None:
            row = kconn.execute(
                "SELECT COUNT(*) FROM consts WHERE decl_id = ? AND ckind = 'ctor'",
                (did,),
            ).fetchone()
            cnt = int(row[0]) if row else 0
            ctor_memo[did] = cnt
        return cnt

    def _is_project_decl(mod: Optional[str], meth: Optional[str]) -> bool:
        return bool(mod is not None or (meth and meth.startswith("unmatched:project")))

    details: List[Dict[str, Any]] = []
    for q in unmatched_qs:
        exact_row = kconn.execute(
            """
            SELECT d.id, d.name, d.kind, d.live_mask, d.fan_in, dm.module, dm.method
            FROM decls d
            LEFT JOIN decl_module dm ON dm.decl_id = d.id
            WHERE d.name = ?
            """,
            (q,),
        ).fetchone()
        if exact_row is not None:
            cands = [(6, exact_row)]
        else:
            raw_rows = kconn.execute(
                """
                SELECT d.id, d.name, d.kind, d.live_mask, d.fan_in, dm.module, dm.method
                FROM decls d
                LEFT JOIN decl_module dm ON dm.decl_id = d.id
                WHERE instr(lower(d.name), lower(?)) > 0
                """,
                (q,),
            ).fetchall()
            cands = []
            for r in raw_rows:
                p = _matches_structure_filter(r[1], q, exact=False)
                if p > 0:
                    cands.append((p, r))

        strict_cands = [(p, r) for p, r in cands if p in (6, 5, 3, 2)]
        sub_cands = [(p, r) for p, r in cands if p in (4, 1)]

        chosen_list = strict_cands if strict_cands else ([] if exact else sub_cands)
        if not chosen_list:
            sub_1c = sorted({
                r[1]
                for _p, r in sub_cands
                if r[2] == "inductive"
                and int(r[3]) != 0
                and _is_project_decl(r[5], r[6])
                and _ctor_count(int(r[0])) == 1
            })
            if exact and sub_1c:
                detail = (
                    f"no exact FQN or terminal-name match (omit --exact for {len(sub_1c)} "
                    f"substring match(es), e.g. {', '.join(sub_1c[:3])})"
                )
            elif exact:
                detail = "no exact FQN or terminal-name match in kernel.db"
            else:
                detail = "not found in kernel.db"
            item: Dict[str, Any] = {
                "query": q,
                "reason": "not_found",
                "decl_kind": None,
                "matched_name": None,
                "detail": detail,
            }
            if exact and sub_1c:
                item["substring_suggestions"] = sub_1c[:5]
            details.append(item)
            continue

        # Prefer highest priority (exact-case before ci), project decls, live decls, inductives, highest fan_in
        chosen_list.sort(
            key=lambda pr: (
                -pr[0],
                not _is_project_decl(pr[1][5], pr[1][6]),
                int(pr[1][3]) == 0,
                pr[1][2] != "inductive",
                -int(pr[1][4]),
                str(pr[1][1]),
            )
        )
        did, nm, kind, lm, _fi, mod, meth = chosen_list[0][1]
        did_i = int(did)
        lm_i = int(lm)
        if kind != "inductive":
            is_pdef = False
            pinfo: Optional[Dict[str, Any]] = None
            if kind == "def" and _is_project_decl(mod, meth):
                is_pdef, pinfo = _is_prop_def_row(
                    kconn, did_i, nm, mod, real_src_root, prop_mod_cache, mod_file_cache
                )
            if is_pdef:
                conj = list(pinfo["conjuncts"]) if pinfo else []
                conj_note = f", {len(conj)} And-conjuncts" if conj else ""
                item_pd: Dict[str, Any] = {
                    "query": q,
                    "reason": "non_structure",
                    "decl_kind": kind,
                    "is_prop_def": True,
                    "matched_name": nm,
                    "live_mask": lm_i,
                    "conjunct_count": len(conj),
                    "hint": f"leanre bundles --instantiations {q}",
                    "detail": (
                        f"Prop-valued {pinfo['source_kind'] if pinfo else 'def'} ({nm}{conj_note}); "
                        f"run `leanre bundles --instantiations {q}` for producer/consumer & conjunct analysis"
                    ),
                }
                if conj:
                    item_pd["conjuncts"] = conj
                details.append(item_pd)
            else:
                details.append({
                    "query": q,
                    "reason": "non_structure",
                    "decl_kind": kind,
                    "matched_name": nm,
                    "live_mask": lm_i,
                    "detail": f"declaration is {kind!r}, not a 1-constructor structure ({nm})",
                })
        elif not _is_project_decl(mod, meth):
            details.append({
                "query": q,
                "reason": "non_project_inductive",
                "decl_kind": kind,
                "matched_name": nm,
                "live_mask": lm_i,
                "detail": f"inductive is external/non-project ({nm})",
            })
        else:
            ccnt = _ctor_count(did_i)
            if ccnt != 1:
                details.append({
                    "query": q,
                    "reason": "zero_ctor_inductive" if ccnt == 0 else "multi_ctor_inductive",
                    "decl_kind": kind,
                    "matched_name": nm,
                    "ctor_count": ccnt,
                    "live_mask": lm_i,
                    "detail": f"inductive has {ccnt} constructors, expected 1 ({nm})",
                })
            elif lm_i == 0:
                details.append({
                    "query": q,
                    "reason": "dead_structure",
                    "decl_kind": kind,
                    "matched_name": nm,
                    "live_mask": 0,
                    "detail": f"1-ctor structure is dead (live_mask=0) ({nm})",
                })
            else:
                details.append({
                    "query": q,
                    "reason": "unmatched",
                    "decl_kind": kind,
                    "matched_name": nm,
                    "live_mask": lm_i,
                    "detail": f"unmatched ({nm})",
                })
    return details


def _format_unmatched_item(item: Dict[str, Any]) -> str:
    q = item["query"]
    reason = item.get("reason")
    nm = item.get("matched_name")
    kind = item.get("decl_kind")
    if reason == "non_structure":
        if item.get("is_prop_def"):
            cc = int(item.get("conjunct_count") or 0)
            conj_txt = f", {cc} conjuncts" if cc else ""
            return f"{q} (Prop-def {nm}{conj_txt} — use --instantiations {q})"
        return f"{q} (non-structure {kind}: {nm})"
    if reason == "dead_structure":
        return f"{q} (dead structure, live_mask=0: {nm})"
    if reason in ("zero_ctor_inductive", "multi_ctor_inductive"):
        return f"{q} ({item.get('ctor_count', '?')}-ctor inductive: {nm})"
    if reason == "non_project_inductive":
        return f"{q} (non-project inductive: {nm})"
    if reason == "not_found":
        sugg = item.get("substring_suggestions")
        if sugg:
            return f"{q} (not found as exact FQN/terminal; substring hits: {', '.join(sugg[:3])})"
        return f"{q} ({item.get('detail') or 'not found in kernel.db'})"
    return f"{q} ({item.get('detail') or reason or 'unmatched'})"


def _detect_true_slots_targeted(
    kconn: sqlite3.Connection,
    struct_ids: Sequence[int],
    id_to_struct_name: Dict[int, str],
    real_src_root: Optional[str],
    mod_file_cache: Dict[str, Optional[str]],
    anchor_prefix: str = "src/",
) -> List[Dict[str, Any]]:
    """Fast targeted `:= True` slot check restricted to defs referenced by `struct_ids`."""
    if not struct_ids:
        return []
    row_true = kconn.execute("SELECT id FROM decls WHERE name = 'True'").fetchone()
    if row_true is None:
        return []
    true_id = int(row_true[0])
    s_qs = ",".join("?" for _ in struct_ids)
    # Step 1: O(fan_out) lookup via PRIMARY KEY(src, dst) — avoids scanning `True` incoming edges!
    ref_pairs = kconn.execute(
        f"SELECT src, dst FROM edges WHERE src IN ({s_qs})",
        tuple(struct_ids),
    ).fetchall()
    if not ref_pairs:
        return []
    dst_to_structs: Dict[int, List[int]] = collections.defaultdict(list)
    for src_sid, dst_did in ref_pairs:
        dst_to_structs[int(dst_did)].append(int(src_sid))

    cand_dst_ids = sorted(dst_to_structs.keys())
    cands: List[Tuple[Any, ...]] = []
    for i in range(0, len(cand_dst_ids), 900):
        chunk = cand_dst_ids[i : i + 900]
        c_qs = ",".join("?" for _ in chunk)
        cands.extend(
            kconn.execute(
                f"""
                SELECT d.id, d.name, d.type_nodes, d.value_nodes, d.fan_in, d.fan_out_value,
                       dm.module, COALESCE(r.depth, -1)
                FROM edges et
                JOIN decls d ON et.src = d.id
                LEFT JOIN decl_module dm ON dm.decl_id = d.id
                LEFT JOIN reach r ON r.root_id = 0 AND r.decl_id = d.id
                WHERE et.src IN ({c_qs}) AND et.dst = ? AND et.kind IN (2, 3)
                  AND d.kind = 'def' AND d.live_mask != 0
                  AND (dm.module IS NOT NULL OR dm.method LIKE 'unmatched:project%')
                ORDER BY d.fan_in DESC, d.id
                """,
                (*chunk, true_id),
            ).fetchall()
        )

    confirmed: Dict[int, Dict[str, Any]] = {}
    src_text_cache: Dict[str, Dict[str, Dict[str, Any]]] = {}
    for did, nm, tn, vn, fi, fov, mod, rh_dep in cands:
        did_i = int(did)
        is_exact_vn1 = (vn == 1 and fov == 1)
        src_kind = "abbrev/def"
        line_no: Optional[int] = None
        src_hit = False
        if real_src_root and mod:
            if mod not in src_text_cache:
                fpath = mod_file_cache.get(mod)
                if fpath is None and mod not in mod_file_cache:
                    fpath = _safe_resolve_module(real_src_root, mod)
                    mod_file_cache[mod] = fpath
                if fpath:
                    with open(fpath, "r", encoding="utf-8", errors="replace") as f:
                        src_text_cache[mod] = parse_true_defs_in_text(f.read(), mod)
                else:
                    src_text_cache[mod] = {}
            sinfo = src_text_cache[mod].get(nm)
            if sinfo:
                src_hit = True
                src_kind = sinfo["source_kind"]
                line_no = sinfo["line"]
        if is_exact_vn1 or src_hit:
            anchor = _format_anchor(anchor_prefix, mod, line_no)
            ref_snames = sorted({
                id_to_struct_name[sid]
                for sid in dst_to_structs.get(did_i, [])
                if sid in id_to_struct_name
            })
            rdep = None if rh_dep < 0 else int(rh_dep)
            confirmed[did_i] = {
                "decl_id": did_i,
                "name": nm,
                "source_kind": src_kind,
                "value_nodes": vn,
                "type_nodes": tn,
                "fan_in": fi,
                "root_depth": rdep,
                "rh_depth": rdep,
                "module": mod,
                "anchor": anchor,
                "referenced_by_structures": ref_snames,
            }

    out = list(confirmed.values())
    out.sort(key=lambda x: (-x["fan_in"], x["name"]))
    return out


def run_bundles(
    kernel_db_path: str = DEFAULT_KERNEL_DB,
    src_root: Optional[str] = DEFAULT_SRC_ROOT,
    top: Optional[int] = 35,
    min_fields: Optional[int] = None,
    sort_by: str = "dom",
    only: str = "all",
    structure: Optional[Union[str, Sequence[str]]] = None,
    include_eliminated: bool = False,
    exact: bool = False,
) -> Dict[str, Any]:
    """Audit live 1-constructor project inductives in `kernel.db` (+ optional `.lean` source).

    When `structure` is provided (single string, comma-separated string, or sequence of
    queries), executes a fast targeted single-pass lookup over only the matched structures
    and their exact `.lean` source modules (`< 0.5s` instead of scanning all 5,497 modules).
    """
    t0 = time.time()
    if sort_by not in ("ratio", "unread", "dom", "cone"):
        raise ValueError(f"Unsupported sort key: {sort_by!r}")
    if only not in ("prop", "type", "placeholder", "all"):
        raise ValueError(f"Unsupported --only filter: {only!r}")

    queries = _normalize_structure_queries(structure)
    struct_filter_mode = bool(queries)

    real_src_root: Optional[str] = None
    if src_root:
        if os.path.isdir(src_root):
            real_src_root = os.path.realpath(src_root)
        elif os.path.abspath(src_root) != os.path.abspath(DEFAULT_SRC_ROOT):
            raise FileNotFoundError(f"Missing --src-root directory: {src_root}")
    anchor_prefix = _infer_anchor_prefix(real_src_root)

    kconn = connect_ro(kernel_db_path)
    try:
        query_id_order: Dict[str, List[int]] = {}
        unmatched_queries: List[str] = []
        unmatched_details: List[Dict[str, Any]] = []
        if struct_filter_mode:
            raw_targeted, query_id_order = _resolve_targeted_one_ctor(
                kconn, queries, exact=exact
            )
            one_ctor = [r[:7] for r in raw_targeted]
            unmatched_queries = [q for q in queries if not query_id_order.get(q)]
            if unmatched_queries:
                unmatched_details = _diagnose_unmatched_queries(
                    kconn, unmatched_queries, exact=exact, real_src_root=real_src_root
                )
        else:
            # 1. All live 1-constructor project inductives (full-corpus mode)
            rows = kconn.execute(
                """
                SELECT d.id, d.name, d.fan_in, d.type_nodes, d.value_nodes, dm.module, dm.method
                FROM decls d
                JOIN decl_module dm ON d.id = dm.decl_id
                WHERE d.live_mask != 0 AND d.kind = 'inductive'
                  AND (dm.module IS NOT NULL OR dm.method LIKE 'unmatched:project%')
                ORDER BY d.id
                """
            ).fetchall()

            ctor_counts: collections.Counter[int] = collections.Counter()
            for (did,) in kconn.execute("SELECT decl_id FROM consts WHERE ckind = 'ctor'"):
                ctor_counts[did] += 1

            one_ctor = [r for r in rows if ctor_counts[r[0]] == 1]

        struct_ids = [r[0] for r in one_ctor]
        id_to_struct_name = {r[0]: r[1] for r in one_ctor}

        # 2. Direct single-component children (`S.<leaf>`) via `decls_name` index range scan
        children: Dict[str, Dict[str, Tuple[int, str, int]]] = collections.defaultdict(dict)
        elims: Dict[str, Dict[str, int]] = collections.defaultdict(dict)
        for _did, nm, _fi, _tn, _vn, _mod, _meth in one_ctor:
            lo = nm + "."
            hi = nm + "/"
            lo_len = len(lo)
            for cdid, cnm, cknd, cfi in kconn.execute(
                "SELECT id, name, kind, fan_in FROM decls WHERE name >= ? AND name < ? AND live_mask != 0",
                (lo, hi),
            ):
                leaf = cnm[lo_len:]
                if "." in leaf:
                    continue
                if leaf in ELIM_NAMES:
                    elims[nm][leaf] = int(cfi)
                else:
                    children[nm][leaf] = (int(cdid), cknd, int(cfi))

        # 3. Parse source files for unique referenced project modules
        mod_file_cache: Dict[str, Optional[str]] = {}
        parsed_by_mod: Dict[str, Dict[str, Dict[str, Any]]] = {}
        if real_src_root:
            unique_mods = sorted({r[5] for r in one_ctor if r[5] is not None})
            for mod in unique_mods:
                fpath = _safe_resolve_module(real_src_root, mod)
                mod_file_cache[mod] = fpath
                if fpath:
                    with open(fpath, "r", encoding="utf-8", errors="replace") as f:
                        parsed_by_mod[mod] = parse_lean_structures_in_text(f.read(), mod)
                else:
                    parsed_by_mod[mod] = {}

        # 4. Build initial audit records across all 1-constructor inductives
        source_kinds: collections.Counter[str] = collections.Counter()
        prop_part = collections.Counter()
        type_part = collections.Counter()

        all_records: List[Dict[str, Any]] = []
        literal_true_field_hits: List[Dict[str, Any]] = []

        for did, nm, fi, tn, vn, mod, _meth in one_ctor:
            s_info = parsed_by_mod.get(mod, {}).get(nm) if (real_src_root and mod) else None
            ch = children[nm]
            el = elims[nm]
            cases_fi = el.get("casesOn", 0)
            rec_on_fi = el.get("recOn", 0)
            rec_fi = el.get("rec", 0)
            is_eliminated = (cases_fi > 0 or rec_on_fi > 0 or rec_fi > 0)

            if s_info is not None:
                source_kind = s_info["source_kind"]
                is_prop: Optional[bool] = bool(s_info["is_prop"])
                extends_raw = s_info["extends"]
                subobj_set = set(s_info["subobject_names"])
                own_fields = s_info["fields"]
                anchor = _format_anchor(anchor_prefix, mod, s_info["line"])
                lit_true = s_info["literal_true_fields"]
            else:
                source_kind = "inductive"
                # Kernel-only fallback: infer Prop vs Type* from non-aux projection decl kind (`thm` vs `def`)
                non_aux_ch = {k: v for k, v in ch.items() if k not in AUTO_AUX_NAMES}
                if any(v[1] == "thm" for v in non_aux_ch.values()):
                    is_prop = True
                elif any(v[1] == "def" for v in non_aux_ch.values()):
                    is_prop = False
                else:
                    is_prop = None
                extends_raw = []
                subobj_set = set()
                own_fields = sorted(non_aux_ch.keys())
                anchor = None
                lit_true = []

            source_kinds[source_kind] += 1
            own_set = set(own_fields)
            projected_own = [f for f in own_fields if f in ch]
            unread_own = [f for f in own_fields if f not in ch]
            subobj_projected = sorted(leaf for leaf in ch if leaf in subobj_set)
            # Only skip AUTO_AUX_NAMES (e.g. `noConfusion`, `below`) when they are not declared own fields.
            helpers_excluded = sorted(
                leaf for leaf in ch
                if leaf not in own_set and leaf not in subobj_set and leaf not in AUTO_AUX_NAMES
            )
            has_named_non_aux_proj = any(
                leaf in own_set or leaf in subobj_set or leaf not in AUTO_AUX_NAMES
                for leaf in ch
            )

            tot = len(own_fields)
            proj_cnt = len(projected_own)
            unr_cnt = len(unread_own)
            is_placeholder = (s_info is not None and tot == 0 and not extends_raw) or (
                s_info is None and tot == 0 and not has_named_non_aux_proj and not is_eliminated and tn <= 32
            )

            if is_prop is True:
                st = prop_part
            else:
                st = type_part
            st["total"] += 1
            if is_placeholder:
                st["zero_field"] += 1
            elif proj_cnt == tot:
                st["full_own"] += 1
            elif proj_cnt == 0 and not has_named_non_aux_proj:
                st["zero_proj_cases" if is_eliminated else "zero_proj_nocases"] += 1
            else:
                st["partial_cases" if is_eliminated else "partial_nocases"] += 1

            if lit_true:
                literal_true_field_hits.append({"structure": nm, "fields": lit_true, "anchor": anchor})

            raw_ratio = (unr_cnt / tot) if tot > 0 else 0.0
            ratio = round(raw_ratio, 4)
            rec_obj: Dict[str, Any] = {
                "decl_id": did,
                "name": nm,
                "module": mod,
                "anchor": anchor,
                "source_kind": source_kind,
                "universe_kind": "Prop" if is_prop is True else ("Type*" if is_prop is False else "Unknown"),
                "is_prop": is_prop,
                "extends": extends_raw,
                "total_fields": tot,
                "projected_fields": proj_cnt,
                "unread_fields": unr_cnt,
                "unread_ratio": ratio,
                "_raw_ratio": raw_ratio,
                "fan_in": int(fi),
                "casesOn_fan_in": cases_fi,
                "recOn_fan_in": rec_on_fi,
                "rec_fan_in": rec_fi,
                "is_eliminated": is_eliminated,
                "is_placeholder": is_placeholder,
                "subobject_projections": subobj_projected,
                "helper_subdecls_excluded": helpers_excluded,
                "unread_field_names": unread_own,
                "projected_field_names": projected_own,
                "literal_true_fields": lit_true,
                "max_caller_dom_sub": 0,
                "top_caller": None,
                "root_depth": None,
                "rh_depth": None,
                "weighted_score": 0.0,
                "cone_score": round(raw_ratio * int(fi), 1),
            }
            all_records.append(rec_obj)

        # 5. Select candidates needing caller `dom` / `reach` enrichment
        by_id: Dict[int, Dict[str, Any]] = {r["decl_id"]: r for r in all_records}
        matched_records: List[Dict[str, Any]] = []
        if struct_filter_mode:
            seen_mid: Set[int] = set()
            for q in queries:
                for did in query_id_order.get(q, []):
                    if did in by_id and did not in seen_mid:
                        seen_mid.add(did)
                        matched_records.append(by_id[did])
        else:
            matched_records = all_records

        filtered: List[Dict[str, Any]] = []
        for r in matched_records:
            if only == "prop" and r["is_prop"] is not True:
                continue
            if only == "type" and r["is_prop"] is not False:
                continue
            if only == "placeholder" and not r["is_placeholder"]:
                continue

            if not struct_filter_mode:
                if not include_eliminated and r["is_eliminated"] and not r["is_placeholder"]:
                    continue
                if only == "all":
                    if not ((r["unread_fields"] > 0 and not r["is_eliminated"]) or r["is_placeholder"]):
                        continue
                elif only in ("prop", "type"):
                    if r["unread_fields"] <= 0:
                        continue

            if min_fields is not None and r["total_fields"] < min_fields:
                continue
            filtered.append(r)

        # Also enrich placeholders and top eliminated bundles for summary sections
        placeholders = [r for r in all_records if r["is_placeholder"]]
        elim_cands = [r for r in all_records if r["is_eliminated"] and r["unread_fields"] > 0]
        enrich_ids = sorted({
            r["decl_id"]
            for r in (filtered + placeholders + elim_cands)
        })

        # 6. Targeted caller `dom` subtree + `reach` depth query
        max_dom: Dict[int, int] = {}
        top_caller: Dict[int, str] = {}
        root_depth: Dict[int, int] = {}

        for i in range(0, len(enrich_ids), 900):
            chunk = enrich_ids[i : i + 900]
            qs = ",".join("?" for _ in chunk)
            for dst, cnm, sub in kconn.execute(
                f"""
                SELECT e.dst, d.name, COALESCE(dm.subtree_size, 0)
                FROM edges e
                JOIN decls d ON e.src = d.id
                LEFT JOIN dom dm ON dm.tree_id = 0 AND dm.decl_id = e.src
                WHERE e.dst IN ({qs}) AND d.live_mask != 0
                """,
                chunk,
            ):
                if sub > max_dom.get(dst, -1):
                    max_dom[dst] = int(sub)
                    top_caller[dst] = cnm
            for did, dep in kconn.execute(
                f"SELECT decl_id, depth FROM reach WHERE root_id = 0 AND decl_id IN ({qs})",
                chunk,
            ):
                root_depth[did] = int(dep)

        for r in all_records:
            did = r["decl_id"]
            raw_ratio = r.pop("_raw_ratio")
            if did in max_dom:
                r["max_caller_dom_sub"] = max_dom[did]
                r["top_caller"] = top_caller.get(did)
                r["weighted_score"] = round(raw_ratio * max_dom[did], 1)
            if did in root_depth:
                r["root_depth"] = root_depth[did]
                r["rh_depth"] = root_depth[did]

        # 7. Sort & slice
        def _sort_key(r: Dict[str, Any]) -> Tuple[Any, ...]:
            if sort_by == "ratio":
                return (-r["unread_ratio"], -r["unread_fields"], -r["weighted_score"], -r["fan_in"], r["name"])
            if sort_by == "unread":
                return (-r["unread_fields"], -r["unread_ratio"], -r["weighted_score"], -r["fan_in"], r["name"])
            if sort_by == "cone":
                return (-r["cone_score"], -r["fan_in"], -r["max_caller_dom_sub"], -r["unread_fields"], r["name"])
            return (-r["weighted_score"], -r["max_caller_dom_sub"], -r["unread_fields"], -r["fan_in"], r["name"])

        if struct_filter_mode and len(queries) > 1:
            # Preserve explicit multi-query order while sorting multiple hits within each query
            filtered_set = {r["decl_id"] for r in filtered}
            ordered_filtered: List[Dict[str, Any]] = []
            seen_f: Set[int] = set()
            for q in queries:
                q_recs = [
                    by_id[did]
                    for did in query_id_order.get(q, [])
                    if did in filtered_set and did not in seen_f
                ]
                q_recs.sort(key=_sort_key)
                for rec_item in q_recs:
                    seen_f.add(rec_item["decl_id"])
                    ordered_filtered.append(rec_item)
            filtered = ordered_filtered
        else:
            filtered.sort(key=_sort_key)

        placeholders.sort(key=lambda r: (-r["fan_in"], -r["max_caller_dom_sub"], r["name"]))
        elim_cands.sort(key=lambda r: (-r["max_caller_dom_sub"], -r["unread_fields"], r["name"]))

        if struct_filter_mode and top == 35 and len(filtered) > 35 and len(queries) > 35:
            shown = filtered
        else:
            shown = filtered[:top] if (top is not None and top > 0) else filtered

        # 8. Detect `abbrev := True` / `def := True` slots
        if struct_filter_mode:
            true_slots = _detect_true_slots_targeted(
                kconn, struct_ids, id_to_struct_name, real_src_root, mod_file_cache, anchor_prefix=anchor_prefix
            )
        else:
            true_slots = _detect_true_slots(
                kconn, struct_ids, id_to_struct_name, real_src_root, mod_file_cache, anchor_prefix=anchor_prefix
            )

        query_struct_field: Optional[Union[str, List[str]]] = None
        if len(queries) == 1:
            query_struct_field = queries[0]
        elif len(queries) > 1:
            query_struct_field = list(queries)

        elapsed = round(time.time() - t0, 3 if struct_filter_mode else 2)
        return {
            "schema": SCHEMA_VERSION,
            "pins": {
                "kernel_db": _rel_repo_path(kernel_db_path),
                "src_root": _rel_repo_path(real_src_root) if real_src_root else None,
                "source_mode": "source+kernel" if real_src_root else "kernel_only",
                "targeted": struct_filter_mode,
                "elapsed_seconds": elapsed,
            },
            "query": {
                "top": top,
                "min_fields": min_fields,
                "sort": sort_by,
                "only": only,
                "structure": query_struct_field,
                "structures": list(queries),
                "exact": bool(exact),
                "include_eliminated": include_eliminated,
                "total_matching": len(filtered),
                "returned": len(shown),
                "unmatched_queries": unmatched_queries,
                "unmatched_details": unmatched_details,
            },
            "unmatched_queries": unmatched_queries,
            "summary": {
                "targeted_mode": struct_filter_mode,
                "total_live_1ctor_project_inductives": len(one_ctor),
                "source_kinds": dict(sorted(source_kinds.items())),
                "prop_partition": {
                    "total": prop_part["total"],
                    "zero_field": prop_part["zero_field"],
                    "full_own": prop_part["full_own"],
                    "partial_nocases": prop_part["partial_nocases"],
                    "partial_cases": prop_part["partial_cases"],
                    "zero_proj_nocases": prop_part["zero_proj_nocases"],
                    "zero_proj_cases": prop_part["zero_proj_cases"],
                },
                "type_partition": {
                    "total": type_part["total"],
                    "zero_field": type_part["zero_field"],
                    "full_own": type_part["full_own"],
                    "partial_nocases": type_part["partial_nocases"],
                    "partial_cases": type_part["partial_cases"],
                    "zero_proj_nocases": type_part["zero_proj_nocases"],
                    "zero_proj_cases": type_part["zero_proj_cases"],
                },
                "eliminated_cases_on_count": len(elim_cands),
                "empty_placeholders_count": len(placeholders),
                "literal_true_field_hits_count": len(literal_true_field_hits),
                "true_abbrev_slots_count": len(true_slots),
            },
            "bundles": shown,
            "placeholders": placeholders,
            "true_slots": true_slots,
            "literal_true_field_hits": literal_true_field_hits,
            "eliminated_top": elim_cands[:15],
        }
    finally:
        kconn.close()


# ---------------------------------------------------------------------------
# Live Constructor / Producer Finder (`--instantiations`)
# ---------------------------------------------------------------------------

_RE_COMPILER_AUX = re.compile(
    r"\.(?:_proof_|_simp_|_abel_|_ring_|_omega_|_linarith_|_norm_num_|"
    r"match_|eq_|_eq_|_unary|_mutual|_sunfold|_cstage|_brec_|_wf)"
)
_RE_NONCOMP_SEC = re.compile(
    r"^noncomputable\s+section(?:\s+([A-Za-z_][A-Za-z0-9_.'\u2080-\u2089\u2090-\u209c]*))?\b"
)
_RE_ANY_DECL_KW = re.compile(
    r"^(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b\s*(.*)$"
)
_RE_VAR_CMD = re.compile(r"^variables?\b\s*(.*)$")


def _tok_matches_struct(tok: str, s_fqn: str, s_leaf: str) -> bool:
    if tok.startswith("@"):
        tok = tok[1:]
    if tok.startswith("_root_."):
        tok = tok[7:]
    return tok == s_leaf or tok == s_fqn or s_fqn.endswith("." + tok)


def _tokens_mention_struct(toks: Sequence[str], s_fqn: str, s_leaf: str) -> bool:
    return any(_tok_matches_struct(t, s_fqn, s_leaf) for t in toks)


def _check_positive_conclusion(toks: Sequence[str], s_fqn: str, s_leaf: str) -> Optional[str]:
    """Return positive witness kind if conclusion `toks` constructs or proves existence of `S`."""
    cur = sighash._hoist(list(toks), [])
    if not cur:
        return None

    # Positive conjunction / product: `A ∧ B` or `A × B`
    depth = 0
    for idx, t in enumerate(cur):
        if t in sighash._OPEN:
            depth += 1
        elif t in sighash._CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and t in ("∧", "×"):
            lhit = _check_positive_conclusion(cur[:idx], s_fqn, s_leaf)
            if lhit:
                return lhit
            return _check_positive_conclusion(cur[idx + 1 :], s_fqn, s_leaf)

    head = cur[0]
    if _tok_matches_struct(head, s_fqn, s_leaf):
        return "return_type"
    if head == "@" and len(cur) > 1 and _tok_matches_struct(cur[1], s_fqn, s_leaf):
        return "return_type"

    if head in ("Nonempty", "Inhabited", "Trunc", "Unique"):
        arg = sighash._strip_parens(list(cur[1:]))
        if arg and (
            _tok_matches_struct(arg[0], s_fqn, s_leaf)
            or (arg[0] == "@" and len(arg) > 1 and _tok_matches_struct(arg[1], s_fqn, s_leaf))
        ):
            return head.lower()

    if head in ("∃", "Σ"):
        depth, comma = 0, -1
        for j in range(1, len(cur)):
            tj = cur[j]
            if tj in sighash._OPEN:
                depth += 1
            elif tj in sighash._CLOSE:
                depth = max(0, depth - 1)
            elif tj == "," and depth == 0:
                comma = j
                break
        if comma > 0:
            span = cur[1:comma]
            k = 0
            while k < len(span):
                tk = span[k]
                if tk in sighash._BINDER_OPEN:
                    cl = sighash._match_close(span, k)
                    for _nm, bty in sighash._binder_entries(span[k : cl + 1]):
                        bty_s = sighash._strip_parens(list(bty))
                        if bty_s and (
                            _tok_matches_struct(bty_s[0], s_fqn, s_leaf)
                            or (bty_s[0] == "@" and len(bty_s) > 1 and _tok_matches_struct(bty_s[1], s_fqn, s_leaf))
                        ):
                            return "exists"
                    k = cl + 1
                elif tk == ":":
                    bty_s = sighash._strip_parens(list(span[k + 1 :]))
                    if bty_s and (
                        _tok_matches_struct(bty_s[0], s_fqn, s_leaf)
                        or (bty_s[0] == "@" and len(bty_s) > 1 and _tok_matches_struct(bty_s[1], s_fqn, s_leaf))
                    ):
                        return "exists"
                    break
                else:
                    k += 1
            bhit = _check_positive_conclusion(cur[comma + 1 :], s_fqn, s_leaf)
            if bhit:
                return bhit if bhit.startswith("exists") else f"exists_{bhit}"

    if head in ("Exists", "Sigma", "PSigma", "Subtype"):
        if _tokens_mention_struct(cur[1:], s_fqn, s_leaf):
            return "subtype" if head == "Subtype" else "exists"

    if head == "{" and len(cur) >= 5:
        c = sighash._split_colon(cur[1:-1])
        if c > 0:
            rest_sub = cur[1 + c + 1 : -1]
            for idx2, ts in enumerate(rest_sub):
                if ts in ("//", "|"):
                    bty_s = sighash._strip_parens(rest_sub[:idx2])
                    if bty_s and _tok_matches_struct(bty_s[0], s_fqn, s_leaf):
                        return "subtype"
                    break

    return None


def _extract_brace_assigned_fields(body: str) -> List[Set[str]]:
    """Extract per-`{ ... }` record-literal depth-1 assigned field sets (`<field> :=`)."""
    groups: List[Set[str]] = []
    stack: List[Tuple[str, List[str]]] = []
    in_str = False
    i = 0
    n = len(body)
    while i < n:
        ch = body[i]
        if ch == '"' and (i == 0 or body[i - 1] != "\\"):
            in_str = not in_str
            if stack:
                stack[-1][1].append(ch)
            i += 1
            continue
        if in_str:
            if stack:
                stack[-1][1].append(ch)
            i += 1
            continue
        if ch in _OPEN_BRACKETS:
            stack.append((ch, []))
        elif ch in _CLOSE_BRACKETS:
            if stack:
                op, chars = stack.pop()
                if op == "{" and ch == "}":
                    seg = "".join(chars)
                    fset: Set[str] = set()
                    for fm in re.finditer(
                        r"(?:^|[,;\n])\s*([A-Za-z_][A-Za-z0-9_'\u2080-\u2089\u2090-\u209c]*)\s*"
                        r"(?:[^:=\n{}()\[\]]{0,60}):=",
                        seg,
                    ):
                        fset.add(fm.group(1))
                    if fset:
                        groups.append(fset)
                if stack:
                    stack[-1][1].append(" ")
        else:
            if stack:
                stack[-1][1].append(ch)
        i += 1
    return groups


_PATTERN_PREV_WORDS = frozenset({
    "obtain", "rcases", "rintro", "intro", "fun", "|", "have", "let", "match", "for", "∃", "Σ",
})
_RE_PATTERN_LINE_PREFIX = re.compile(r"^(?:obtain|rintro|rcases|intro|fun|\|)\b")
_RE_IDENT_TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'.\u2080-\u2089\u2090-\u209c]*")


def _extract_expr_anon_ctors(body: str) -> List[Tuple[int, bool, List[str]]]:
    """Extract `(arity, has_hole, preceding_idents)` for expression-position `⟨...⟩` in `body`."""
    if "⟨" not in body:
        return []
    res: List[Tuple[int, bool, List[str]]] = []
    n = len(body)
    i = 0
    in_str = False
    while i < n:
        c = body[i]
        if c == '"' and (i == 0 or body[i - 1] != "\\"):
            in_str = not in_str
            i += 1
            continue
        if in_str:
            i += 1
            continue
        if c == "⟨":
            j = i - 1
            while j >= 0 and body[j].isspace():
                j -= 1
            k = j
            while k >= 0 and (body[k].isalnum() or body[k] in "_'.|"):
                k -= 1
            prev_word = body[k + 1 : j + 1]
            line_start = body.rfind("\n", 0, i) + 1
            line_prefix = body[line_start:i].strip()
            is_pattern = (
                prev_word in _PATTERN_PREV_WORDS
                or _RE_PATTERN_LINE_PREFIX.match(line_prefix) is not None
                or (re.match(r"^(?:have|let)\b", line_prefix) is not None and ":=" not in line_prefix)
            )
            depth = 1
            p = i + 1
            arity = 1
            empty = True
            sub_in_str = False
            while p < n and depth > 0:
                pc = body[p]
                if pc == '"' and (p == 0 or body[p - 1] != "\\"):
                    sub_in_str = not sub_in_str
                elif not sub_in_str:
                    if pc in _OPEN_BRACKETS:
                        depth += 1
                        empty = False
                    elif pc in _CLOSE_BRACKETS:
                        depth = max(0, depth - 1)
                        if depth == 0:
                            break
                    elif pc == "," and depth == 1:
                        arity += 1
                    elif not pc.isspace():
                        empty = False
                p += 1
            if empty and arity == 1:
                arity = 0
            # Check if followed immediately by `=>` or `:=` (binder pattern)
            q = p + 1
            while q < n and body[q].isspace():
                q += 1
            if body.startswith("=>", q) or body.startswith(":=", q):
                is_pattern = True
            if not is_pattern:
                inner = body[i : p + 1]
                has_hole = "?_" in inner
                ctx_start = max(0, i - 250)
                ctx = body[ctx_start:i]
                for sep in (":=", ";", "=>"):
                    sp = ctx.rfind(sep)
                    if sp >= 0:
                        ctx = ctx[sp + len(sep) :]
                bm = re.search(r"\bby\b", ctx)
                if bm:
                    ctx = ctx[bm.end() :]
                prev_idents = _RE_IDENT_TOKEN.findall(ctx)
                res.append((arity, has_hole, prev_idents))
        i += 1
    return res


def _rhs_constructs_struct(
    body: str,
    type_end: int,
    s_fqn: str,
    s_leaf: str,
    mk_re: re.Pattern[str],
) -> bool:
    """Return True iff the `:= <rhs>` following a `have`/`let x : S` constructs `S` inline."""
    n = len(body)
    depth = 0
    in_str = False
    i = type_end
    assign_idx = -1
    while i < n:
        c = body[i]
        if c == '"' and (i == 0 or body[i - 1] != "\\"):
            in_str = not in_str
        elif not in_str:
            if c in _OPEN_BRACKETS:
                depth += 1
            elif c in _CLOSE_BRACKETS:
                depth = max(0, depth - 1)
            elif depth == 0:
                if body.startswith(":=", i):
                    assign_idx = i + 2
                    break
                if c == "\n":
                    # Stop if next line isn't indented deeper or starts a new tactic
                    nxt = body[i + 1 :].lstrip(" \t")
                    if re.match(r"^(?:have|let|obtain|exact|refine|rw|simp|intro|apply|cases|induction)\b", nxt):
                        break
        i += 1
    if assign_idx < 0:
        return False
    rhs = body[assign_idx : assign_idx + 240].lstrip()
    while rhs.startswith("("):
        rhs = rhs[1:].lstrip()
    if rhs.startswith("by"):
        rhs_after_by = rhs[2:].lstrip()
        if rhs_after_by and (len(rhs) == 2 or rhs[2].isspace()):
            rhs = rhs_after_by
    if rhs.startswith(("{", "⟨")):
        return True
    if re.match(r"^(?:exact|refine)\s+⟨", rhs):
        return True
    if re.match(r"^(?:exact|refine)\s+\{", rhs):
        return True
    mm = mk_re.match(rhs)
    if mm and _tok_matches_struct(mm.group(1), s_fqn, s_leaf):
        return True
    return False


_POOL_CONS_EXACT: Set[str] = set()
_POOL_CONS_SUFFIXES: Set[str] = set()


def _init_inst_pool(cons_exact: Set[str], cons_suffixes: Set[str]) -> None:
    global _POOL_CONS_EXACT, _POOL_CONS_SUFFIXES
    _POOL_CONS_EXACT = cons_exact
    _POOL_CONS_SUFFIXES = cons_suffixes


def _scan_instantiation_chunk(
    args: Tuple[
        str,
        List[Tuple[str, Dict[str, int]]],
        str,
        str,
        Set[str],
        Set[str],
        Optional[re.Pattern[bytes]],
        Optional[re.Pattern[bytes]],
        Optional[List[bytes]],
        int,
        bool,
        Optional[Set[str]],
        Optional[Set[str]],
    ],
) -> List[Tuple[str, str, int, str, str, bool, bool, str, bool]]:
    """Worker scanning candidate `.lean` modules for producer / constructor sites of `s_fqn`."""
    (
        real_root,
        items,
        s_fqn,
        s_leaf,
        own_fields,
        subobjs,
        binder_rx_bytes,
        word_rx_bytes,
        field_probe_bytes,
        exp_arity,
        is_prop_def_target,
        cons_exact_arg,
        cons_suffixes_arg,
    ) = args
    cons_exact = _POOL_CONS_EXACT if cons_exact_arg is None else cons_exact_arg
    cons_suffixes = _POOL_CONS_SUFFIXES if cons_suffixes_arg is None else cons_suffixes_arg
    allowed_fields = own_fields | subobjs
    quant_re = re.compile(rb"(?:\xe2\x88\x83|Exists|\xce\xa3|Sigma|PSigma|Nonempty|Inhabited|Trunc|Subtype)\s*$")
    mk_re = re.compile(
        r"(?<![A-Za-z0-9_'.])((?:_root_\.)?(?:[A-Za-z0-9_']+\.)*" + re.escape(s_leaf) + r")\.mk(?![A-Za-z0-9_'])"
    )
    anon_ascr_re = re.compile(
        r"⟨[^⟩]*⟩\s*:\s*@?((?:_root_\.)?(?:[A-Za-z0-9_']+\.)*"
        + re.escape(s_leaf)
        + r")(?![A-Za-z0-9_'.])"
    )
    binding_re = re.compile(
        r"\b(?:have|let)\s+[^\s:]+\s*:\s*@?((?:_root_\.)?(?:[A-Za-z0-9_']+\.)*"
        + re.escape(s_leaf)
        + r")(?![A-Za-z0-9_'.])"
    )
    hits: List[Tuple[str, str, int, str, str, bool, bool, str, bool]] = []

    for mod, want_map in items:
        fpath = _safe_resolve_module(real_root, mod)
        if not fpath:
            continue
        try:
            with open(fpath, "rb") as fb:
                raw = fb.read()
        except OSError:
            continue

        if binder_rx_bytes is not None and word_rx_bytes is not None:
            keep = False
            if field_probe_bytes and all(fp in raw for fp in field_probe_bytes):
                keep = True
            elif (
                not is_prop_def_target
                and exp_arity >= 1
                and 2 in want_map.values()
                and b"\xe2\x9f\xa8" in raw
                and raw.count(b",") >= exp_arity - 1
            ):
                keep = True
            elif word_rx_bytes.search(raw):
                plain_spans: List[Tuple[int, int]] = []
                for bm in binder_rx_bytes.finditer(raw):
                    pref = raw[max(0, bm.start() - 48) : bm.start()]
                    if not quant_re.search(pref):
                        plain_spans.append((bm.start(), bm.end()))
                for wm in word_rx_bytes.finditer(raw):
                    ws, we = wm.start(), wm.end()
                    if not any(ps <= ws and we <= pe for ps, pe in plain_spans):
                        keep = True
                        break
            if not keep:
                continue

        text = raw.decode("utf-8", errors="replace")
        lines = _strip_comments(text).splitlines()
        n = len(lines)
        ns_stack: List[Tuple[str, List[str]]] = []
        scope_self_vars: List[Set[str]] = [set()]
        i = 0
        while i < n:
            ln = lines[i]
            s = ln.strip()
            if not s:
                i += 1
                continue

            m_ns = _RE_NS.match(s)
            if m_ns and (not ln[0].isspace() or ns_stack):
                parts_ns = m_ns.group(1).split(".")
                ns_stack.append(("ns", parts_ns))
                scope_self_vars.append(set())
                i += 1
                continue

            m_sec = _RE_SEC.match(s) or _RE_NONCOMP_SEC.match(s)
            if m_sec and (not ln[0].isspace() or ns_stack):
                ns_stack.append(("sec", [m_sec.group(1)] if m_sec.group(1) else []))
                scope_self_vars.append(set())
                i += 1
                continue

            if s == "mutual" and (not ln[0].isspace() or ns_stack):
                ns_stack.append(("mutual", []))
                scope_self_vars.append(set())
                i += 1
                continue

            m_end = _RE_END.match(s)
            if m_end and (s == "end" or re.match(r"^end\s+[A-Za-z_]", s)) and (not ln[0].isspace() or ns_stack):
                prev_len = len(ns_stack)
                _pop_end_stack(ns_stack, m_end.group(1))
                popped = prev_len - len(ns_stack)
                for _ in range(popped):
                    if len(scope_self_vars) > 1:
                        scope_self_vars.pop()
                i += 1
                continue

            m_var = _RE_VAR_CMD.match(s)
            if m_var and (not ln[0].isspace() or ns_stack):
                vbuf = [m_var.group(1)]
                vj = i + 1
                while vj < n and lines[vj][:1].isspace() and lines[vj].strip():
                    vbuf.append(lines[vj].strip())
                    vj += 1
                vtoks = sighash.lex(" ".join(vbuf))
                vk = 0
                while vk < len(vtoks):
                    if vtoks[vk] in sighash._BINDER_OPEN:
                        ve = sighash._match_close(vtoks, vk)
                        for vnm, vbty in sighash._binder_entries(vtoks[vk : ve + 1]):
                            if vnm != "_" and _tokens_mention_struct(vbty, s_fqn, s_leaf):
                                scope_self_vars[-1].add(vnm)
                        vk = ve + 1
                    else:
                        vk += 1
                i = vj
                continue

            indent = len(ln) - len(ln.lstrip(" "))
            if indent == 0 or (ns_stack and indent <= 2):
                rest, _attrs, mods = _strip_leading_attrs_and_mods(s)
                if not rest and s.startswith("@["):
                    hdr0 = _multi_line_header_extent(lines, i)
                    rest, _attrs, mods = _strip_leading_attrs_and_mods(hdr0)
                m = _RE_ANY_DECL_KW.match(rest)
                if m:
                    kw = m.group(1)
                    tail = m.group(2)
                    j = i + 1
                    while j < n:
                        lnj = lines[j]
                        sj = lnj.strip()
                        if sj:
                            indj = len(lnj) - len(lnj.lstrip(" "))
                            if indj <= indent:
                                r2, _, _ = _strip_leading_attrs_and_mods(sj)
                                if (
                                    _RE_NS.match(sj)
                                    or _RE_SEC.match(sj)
                                    or _RE_NONCOMP_SEC.match(sj)
                                    or _RE_END.match(sj)
                                    or sj == "mutual"
                                    or _RE_TOP_CMD.match(r2)
                                    or sj.startswith("@[")
                                ):
                                    break
                        j += 1

                    nm_m = _RE_STRUCT_NAME.match(tail)
                    raw_nm = nm_m.group(1).rstrip(".") if nm_m else ""
                    fqn = _normalize_fqn(_current_ns(ns_stack), raw_nm)
                    fqn_priv = f"_private.{mod}.0.{fqn}" if "private" in mods else fqn
                    target_key = fqn_priv if fqn_priv in want_map else (fqn if fqn in want_map else None)
                    if target_key and kw not in ("structure", "class", "inductive"):
                        blk = "\n".join(lines[i:j])
                        hdr_part, term, body = _split_header_body(blk)
                        hdr_1line = " ".join(hdr_part.split())
                        hd = sighash.split_header(hdr_1line)
                        if hd:
                            entries: List[Tuple[str, List[str]]] = []
                            for b in hd["binders"]:
                                entries.extend(sighash._binder_entries(b))
                            concl = sighash._hoist(list(hd["type"]), entries)
                            local_bound = {enm for enm, _ in entries if enm != "_"}
                            takes_self = any(
                                _tokens_mention_struct(bty, s_fqn, s_leaf) for _enm, bty in entries
                            )
                            if not takes_self:
                                active_svars = {v for sv in scope_self_vars for v in sv} - local_bound
                                if active_svars:
                                    hdr_toks = [t for b in hd["binders"] for t in b] + list(hd["type"])
                                    for t in hdr_toks:
                                        if t.split(".", 1)[0] in active_svars:
                                            takes_self = True
                                            break
                                    if not takes_self and body:
                                        for t in sighash.lex(body):
                                            if t.split(".", 1)[0] in active_svars:
                                                takes_self = True
                                                break

                            pkind = _check_positive_conclusion(concl, s_fqn, s_leaf)
                            is_local_witness = False
                            if pkind == "return_type":
                                if term == "where":
                                    pkind = "where_ctor"
                                elif "{" in body and ":=" in body:
                                    pkind = "record_literal"
                                elif "⟨" in body:
                                    if re.search(r"\brefine\s+⟨", body):
                                        pkind = "refine_anon_ctor"
                                    elif re.search(r"\bexact\s+⟨", body):
                                        pkind = "exact_anon_ctor"
                                    elif _extract_expr_anon_ctors(body):
                                        pkind = "anon_ctor"

                            is_prop_def = False
                            if pkind is None and kw in ("def", "abbrev") and concl == ["Prop"] and term == ":=":
                                prop_entries = list(entries)
                                prop_concl = sighash._hoist(sighash.lex(body), prop_entries)
                                pp = _check_positive_conclusion(prop_concl, s_fqn, s_leaf)
                                if pp and not any(
                                    _tokens_mention_struct(bty, s_fqn, s_leaf) for _enm, bty in prop_entries
                                ):
                                    is_prop_def = True
                                    pkind = f"prop_spec:{pp}"

                            if pkind is None and want_map[target_key] in (2, 3):
                                if not is_prop_def_target and any(
                                    _tok_matches_struct(mm.group(1), s_fqn, s_leaf) for mm in mk_re.finditer(body)
                                ):
                                    pkind = "body_mk"
                                    is_local_witness = True
                                elif any(
                                    _tok_matches_struct(am.group(1), s_fqn, s_leaf)
                                    for am in anon_ascr_re.finditer(body)
                                ):
                                    pkind = "body_anon_ctor"
                                    is_local_witness = True
                                elif (
                                    not is_prop_def_target
                                    and own_fields
                                    and "{" in body
                                    and not (kw in ("def", "abbrev", "instance") and concl and concl != ["Prop"])
                                ):
                                    need_f = min(2, len(own_fields))
                                    for fset in _extract_brace_assigned_fields(body):
                                        if len(fset) >= need_f and fset <= allowed_fields and (
                                            len(own_fields) >= 2 or not takes_self
                                        ):
                                            pkind = "body_record"
                                            is_local_witness = True
                                            break

                                if pkind is None and not is_prop_def_target and exp_arity >= 1 and want_map[target_key] == 2 and "⟨" in body:
                                    for ar, has_hole, prev_idents in _extract_expr_anon_ctors(body):
                                        if ar == exp_arity and not has_hole and prev_idents:
                                            matched_callee = False
                                            for tok_id in prev_idents:
                                                tok_clean = tok_id[1:] if tok_id.startswith("@") else tok_id
                                                if tok_clean.startswith("_root_."):
                                                    tok_clean = tok_clean[7:]
                                                if tok_clean in cons_exact or tok_clean in cons_suffixes:
                                                    matched_callee = True
                                                    break
                                            if matched_callee:
                                                pkind = "inline_anon_ctor"
                                                is_local_witness = True
                                                break

                                if pkind is None:
                                    has_binding_match = False
                                    for b_m in binding_re.finditer(body):
                                        if _tok_matches_struct(b_m.group(1), s_fqn, s_leaf):
                                            has_binding_match = True
                                            if _rhs_constructs_struct(body, b_m.end(), s_fqn, s_leaf, mk_re):
                                                pkind = "local_witness"
                                                is_local_witness = True
                                                break
                                    if pkind is None and has_binding_match:
                                        pkind = "__consumer_binding__"

                            if pkind:
                                clean_hdr = hdr_1line if len(hdr_1line) <= 220 else hdr_1line[:219] + "…"
                                hits.append(
                                    (target_key, mod, i + 1, kw, pkind, takes_self, is_prop_def, clean_hdr, is_local_witness)
                                )
                    i = j
                    continue
            i += 1
    return hits


def _extract_decl_headers_in_modules(
    real_root: str,
    by_mod: Dict[str, Set[str]],
    anchor_prefix: str = "src/",
) -> Dict[str, Tuple[str, str, str]]:
    """Fetch `(anchor, source_kind, header)` for a small set of top declarations."""
    out: Dict[str, Tuple[str, str, str]] = {}
    for mod, want in sorted(by_mod.items()):
        fpath = _safe_resolve_module(real_root, mod)
        if not fpath:
            continue
        try:
            with open(fpath, "r", encoding="utf-8", errors="replace") as f:
                lines = _strip_comments(f.read()).splitlines()
        except OSError:
            continue
        n = len(lines)
        ns_stack: List[Tuple[str, List[str]]] = []
        i = 0
        while i < n and len(out) < sum(len(v) for v in by_mod.values()):
            ln = lines[i]
            s = ln.strip()
            if not s:
                i += 1
                continue
            m_ns = _RE_NS.match(s)
            if m_ns and (not ln[0].isspace() or ns_stack):
                ns_stack.append(("ns", m_ns.group(1).split(".")))
                i += 1
                continue
            m_sec = _RE_SEC.match(s) or _RE_NONCOMP_SEC.match(s)
            if m_sec and (not ln[0].isspace() or ns_stack):
                ns_stack.append(("sec", [m_sec.group(1)] if m_sec.group(1) else []))
                i += 1
                continue
            if s == "mutual" and (not ln[0].isspace() or ns_stack):
                ns_stack.append(("mutual", []))
                i += 1
                continue
            m_end = _RE_END.match(s)
            if m_end and (s == "end" or re.match(r"^end\s+[A-Za-z_]", s)) and (not ln[0].isspace() or ns_stack):
                _pop_end_stack(ns_stack, m_end.group(1))
                i += 1
                continue
            indent = len(ln) - len(ln.lstrip(" "))
            if indent == 0 or (ns_stack and indent <= 2):
                rest, _attrs, mods = _strip_leading_attrs_and_mods(s)
                if not rest and s.startswith("@["):
                    hdr0 = _multi_line_header_extent(lines, i)
                    rest, _attrs, mods = _strip_leading_attrs_and_mods(hdr0)
                m = _RE_ANY_DECL_KW.match(rest)
                if m:
                    kw, tail = m.group(1), m.group(2)
                    j = i + 1
                    while j < n:
                        lnj = lines[j]
                        sj = lnj.strip()
                        if sj:
                            indj = len(lnj) - len(lnj.lstrip(" "))
                            if indj <= indent:
                                r2, _, _ = _strip_leading_attrs_and_mods(sj)
                                if (
                                    _RE_NS.match(sj)
                                    or _RE_SEC.match(sj)
                                    or _RE_NONCOMP_SEC.match(sj)
                                    or _RE_END.match(sj)
                                    or sj == "mutual"
                                    or _RE_TOP_CMD.match(r2)
                                    or sj.startswith("@[")
                                ):
                                    break
                        j += 1
                    nm_m = _RE_STRUCT_NAME.match(tail)
                    raw_nm = nm_m.group(1).rstrip(".") if nm_m else ""
                    fqn = _normalize_fqn(_current_ns(ns_stack), raw_nm)
                    fqn_priv = f"_private.{mod}.0.{fqn}" if "private" in mods else fqn
                    key = fqn_priv if fqn_priv in want else (fqn if fqn in want else None)
                    if key and key not in out:
                        hdr_part, _t, _b = _split_header_body("\n".join(lines[i:j]))
                        h1 = " ".join(hdr_part.split())
                        if len(h1) > 220:
                            h1 = h1[:219] + "…"
                        out[key] = (_format_anchor(anchor_prefix, mod, i + 1) or "", kw, h1)
                    i = j
                    continue
            i += 1
    return out


def _resolve_prop_def_candidates(
    kconn: sqlite3.Connection,
    queries: Sequence[str],
    real_src_root: Optional[str],
    allow_dead_fallback: bool = False,
    exact: bool = False,
) -> Tuple[Dict[str, Tuple[int, List[Tuple[Any, ...]]]], Dict[str, Optional[Dict[str, Any]]]]:
    """Resolve queries matching `Prop`-valued `def` / `abbrev` project declarations."""
    if not queries:
        return {}, {}

    prop_mod_cache: Dict[str, Dict[str, Dict[str, Any]]] = {}
    mod_file_cache: Dict[str, Optional[str]] = {}
    pinfo_by_id: Dict[int, Optional[Dict[str, Any]]] = {}
    per_query_best: Dict[str, Tuple[int, List[Tuple[Any, ...]]]] = {}
    unresolved: List[str] = []

    # Fast Path A: exact FQN via `decls_name` index
    for q in queries:
        row = kconn.execute(
            """
            SELECT d.id, d.name, d.fan_in, d.type_nodes, d.value_nodes, dm.module, dm.method, d.live_mask
            FROM decls d
            JOIN decl_module dm ON d.id = dm.decl_id
            WHERE d.name = ? AND d.kind = 'def'
              AND (d.live_mask != 0 OR ?)
              AND (dm.module IS NOT NULL OR dm.method LIKE 'unmatched:project%')
            """,
            (q, 1 if allow_dead_fallback else 0),
        ).fetchone()
        if row is not None:
            ok, pinfo = _is_prop_def_row(
                kconn, int(row[0]), row[1], row[5], real_src_root, prop_mod_cache, mod_file_cache
            )
            if ok:
                pinfo_by_id[int(row[0])] = pinfo
                per_query_best[q] = (6, [row])
                continue
        unresolved.append(q)

    if unresolved:
        live_cond = "1=1" if allow_dead_fallback else "d.live_mask != 0"
        like_clauses = " OR ".join("instr(lower(d.name), lower(?)) > 0" for _ in unresolved)
        rows = kconn.execute(
            f"""
            SELECT d.id, d.name, d.fan_in, d.type_nodes, d.value_nodes, dm.module, dm.method, d.live_mask
            FROM decls d
            JOIN decl_module dm ON d.id = dm.decl_id
            WHERE d.kind = 'def' AND {live_cond}
              AND (dm.module IS NOT NULL OR dm.method LIKE 'unmatched:project%')
              AND ({like_clauses})
            ORDER BY d.live_mask = 0, d.fan_in DESC, d.id
            """,
            tuple(unresolved),
        ).fetchall()

        priorities = (6, 5, 3, 2) if exact else (6, 5, 4, 3, 2, 1)
        for q in unresolved:
            buckets: Dict[int, List[Tuple[Any, ...]]] = {p: [] for p in range(1, 7)}
            for r in rows:
                p = _matches_structure_filter(r[1], q, exact=exact)
                if p > 0:
                    buckets[p].append(r)
            for p in priorities:
                if not buckets[p]:
                    continue
                # Prefer live over dead if allow_dead_fallback=True
                live_b = [r for r in buckets[p] if int(r[7]) != 0]
                pool = live_b if live_b else buckets[p]
                confirmed: List[Tuple[Any, ...]] = []
                for r in pool:
                    did_i = int(r[0])
                    ok, pinfo = _is_prop_def_row(
                        kconn, did_i, r[1], r[5], real_src_root, prop_mod_cache, mod_file_cache
                    )
                    if ok:
                        pinfo_by_id[did_i] = pinfo
                        confirmed.append(r)
                if confirmed:
                    per_query_best[q] = (p, confirmed)
                    break

    return per_query_best, pinfo_by_id


def _resolve_instantiation_targets(
    kconn: sqlite3.Connection,
    queries: Sequence[str],
    real_src_root: Optional[str],
    allow_dead_fallback: bool = False,
    exact: bool = False,
) -> Tuple[List[Tuple[Any, ...]], Dict[str, List[int]], Dict[int, str], Dict[int, Optional[Dict[str, Any]]]]:
    """Resolve 1-ctor project inductives OR `Prop`-valued `def`/`abbrev` targets (exact-case first)."""
    ind_rows, ind_qmap = _resolve_targeted_one_ctor(
        kconn, queries, allow_dead_fallback=allow_dead_fallback, exact=exact
    )
    ind_by_id = {int(r[0]): r for r in ind_rows}

    need_def_qs: List[str] = []
    ind_prio: Dict[str, int] = {}
    for q in queries:
        q_ids = ind_qmap.get(q, [])
        best_p = max((_matches_structure_filter(ind_by_id[did][1], q, exact=exact) for did in q_ids), default=0)
        ind_prio[q] = best_p
        if best_p < 4:
            need_def_qs.append(q)

    def_best, pinfo_by_id = _resolve_prop_def_candidates(
        kconn, need_def_qs, real_src_root, allow_dead_fallback=allow_dead_fallback, exact=exact
    )

    unique_rows: List[Tuple[Any, ...]] = []
    seen_ids: Set[int] = set()
    query_map: Dict[str, List[int]] = {}
    dkind_by_id: Dict[int, str] = {}

    for q in queries:
        p_ind = ind_prio.get(q, 0)
        p_def, def_rows = def_best.get(q, (0, []))
        if p_ind >= 4 or (p_ind > 0 and p_ind >= p_def):
            q_rows = [ind_by_id[did] for did in ind_qmap.get(q, [])]
            chosen_kind = "inductive"
        elif p_def > 0:
            q_rows = def_rows
            chosen_kind = "def"
        else:
            q_rows = []
            chosen_kind = "inductive"
        query_map[q] = [int(r[0]) for r in q_rows]
        for r in q_rows:
            did = int(r[0])
            dkind_by_id[did] = chosen_kind
            if did not in seen_ids:
                seen_ids.add(did)
                unique_rows.append(r)

    return unique_rows, query_map, dkind_by_id, pinfo_by_id


def run_instantiations(
    kernel_db_path: str = DEFAULT_KERNEL_DB,
    src_root: Optional[str] = DEFAULT_SRC_ROOT,
    instantiations: Optional[Union[str, Sequence[str]]] = None,
    live_only: bool = False,
    limit: int = 25,
    exact: bool = False,
) -> Dict[str, Any]:
    """Separate live/total incoming edges to structure(s) or Prop-def(s) `S` into producers, consumers, and projections/helpers."""
    t0 = time.time()
    queries = _normalize_structure_queries(instantiations)
    if not queries:
        raise ValueError("--instantiations requires at least one structure or Prop-def name")

    real_src_root: Optional[str] = None
    if src_root:
        if os.path.isdir(src_root):
            real_src_root = os.path.realpath(src_root)
        elif os.path.abspath(src_root) != os.path.abspath(DEFAULT_SRC_ROOT):
            raise FileNotFoundError(f"Missing --src-root directory: {src_root}")
    anchor_prefix = _infer_anchor_prefix(real_src_root)

    kconn = connect_ro(kernel_db_path)
    try:
        matched_rows, query_map, dkind_by_id, prop_info_by_id = _resolve_instantiation_targets(
            kconn, queries, real_src_root, allow_dead_fallback=not live_only, exact=exact
        )
        missing_qs = [q for q in queries if not query_map.get(q)]
        if missing_qs:
            q0 = missing_qs[0]
            hint = ""
            if "." in q0:
                leaf_q = q0.rsplit(".", 1)[-1]
                sugg, _, _, _ = _resolve_instantiation_targets(
                    kconn, [leaf_q], real_src_root, allow_dead_fallback=True, exact=exact
                )
                if sugg:
                    sugg_names = ", ".join(r[1] for r in sugg[:4])
                    hint = f" (did you mean: {sugg_names}?)"
            elif exact:
                sugg, _, _, _ = _resolve_instantiation_targets(
                    kconn, [q0], real_src_root, allow_dead_fallback=True, exact=False
                )
                if sugg:
                    sugg_names = ", ".join(r[1] for r in sugg[:4])
                    hint = f" (substring matches exist without --exact: {sugg_names})"
            raise ValueError(f"No 1-constructor project structure or Prop def/abbrev matching {q0!r}{hint}")

        # Order matched targets per query by descending `fan_in` so primary interfaces
        # (e.g. `GlobalTheory.KZ.Tower` for `--instantiations Tower`) surface first.
        row_by_id = {int(r[0]): r for r in matched_rows}
        ordered_structs: List[Tuple[Any, ...]] = []
        seen_sids: Set[int] = set()
        for q in queries:
            q_srows = [row_by_id[sid] for sid in query_map[q] if sid in row_by_id and sid not in seen_sids]
            q_srows.sort(key=lambda r: (-int(r[2]), str(r[1])))
            for sr in q_srows:
                seen_sids.add(int(sr[0]))
                ordered_structs.append(sr)

        wrap_ids = [
            int(r[0])
            for r in kconn.execute(
                "SELECT id FROM decls WHERE name IN ('Exists', 'Nonempty', 'Inhabited', 'Trunc', 'Subtype')"
            ).fetchall()
        ]

        parsed_struct_mod_cache: Dict[str, Dict[str, Dict[str, Any]]] = {}
        targets_out: List[Dict[str, Any]] = []

        for sid, s_fqn, fan_in, _tn, _vn, smod, _smeth, s_live_mask in ordered_structs:
            sid = int(sid)
            s_leaf = s_fqn.rsplit(".", 1)[-1]
            target_dkind = dkind_by_id.get(sid, "inductive")
            is_prop_def_target = (target_dkind == "def")
            conjuncts_list: List[str] = []

            if is_prop_def_target:
                pinfo = prop_info_by_id.get(sid)
                source_kind = pinfo["source_kind"] if pinfo else "def"
                is_prop = True
                conjuncts_list = list(pinfo["conjuncts"]) if pinfo else []
                own_field_list = list(conjuncts_list)
                subobj_set = set()
                s_anchor = _format_anchor(anchor_prefix, smod, pinfo["line"]) if (pinfo and smod) else None
                s_info = None
                child_decls: Dict[str, Tuple[int, str, int]] = {}
                elim_fan_in: Dict[str, int] = {}
                exp_arity = 0
            else:
                s_info = None
                if real_src_root and smod:
                    if smod not in parsed_struct_mod_cache:
                        sfpath = _safe_resolve_module(real_src_root, smod)
                        if sfpath:
                            with open(sfpath, "r", encoding="utf-8", errors="replace") as f:
                                parsed_struct_mod_cache[smod] = parse_lean_structures_in_text(f.read(), smod)
                        else:
                            parsed_struct_mod_cache[smod] = {}
                    s_info = parsed_struct_mod_cache[smod].get(s_fqn)

                if s_info is not None:
                    source_kind = s_info["source_kind"]
                    is_prop = bool(s_info["is_prop"])
                    own_field_list = list(s_info["fields"])
                    subobj_set = set(s_info["subobject_names"])
                    s_anchor = _format_anchor(anchor_prefix, smod, s_info["line"])
                else:
                    source_kind = "inductive"
                    is_prop = None
                    own_field_list = []
                    subobj_set = set()
                    s_anchor = None

                # Also inspect `S.<leaf>` children in `decls` for kernel-only projection fallback
                lo_c, hi_c = s_fqn + ".", s_fqn + "/"
                lo_len_c = len(lo_c)
                child_decls = {}
                elim_fan_in = {}
                for cdid, cnm, cknd, cfi in kconn.execute(
                    "SELECT id, name, kind, fan_in FROM decls WHERE name >= ? AND name < ?",
                    (lo_c, hi_c),
                ):
                    leaf = cnm[lo_len_c:]
                    if "." in leaf:
                        continue
                    if leaf in ELIM_NAMES:
                        elim_fan_in[leaf] = int(cfi)
                    else:
                        child_decls[leaf] = (int(cdid), cknd, int(cfi))

                if s_info is None:
                    non_aux = {k: v for k, v in child_decls.items() if k not in AUTO_AUX_NAMES}
                    if any(v[1] == "thm" for v in non_aux.values()):
                        is_prop = True
                    elif any(v[1] == "def" for v in non_aux.values()):
                        is_prop = False
                    own_field_list = sorted(non_aux.keys())
                exp_arity = len(own_field_list) + len(subobj_set)

            lo, hi = s_fqn + ".", s_fqn + "/"
            lo_len = len(lo)
            own_field_set = set() if is_prop_def_target else set(own_field_list)

            # Query incoming kernel edges to `sid`
            in_rows = kconn.execute(
                """
                SELECT d.id, d.name, d.kind, e.kind, d.live_mask, dm.module,
                       COALESCE(dom.subtree_size, 0), COALESCE(r.depth, -1)
                FROM edges e
                JOIN decls d ON e.src = d.id
                LEFT JOIN decl_module dm ON dm.decl_id = d.id
                LEFT JOIN dom ON dom.tree_id = 0 AND dom.decl_id = d.id
                LEFT JOIN reach r ON r.root_id = 0 AND r.decl_id = d.id
                WHERE e.dst = ?
                """,
                (sid,),
            ).fetchall()

            edge_totals = {1: 0, 2: 0, 3: 0}
            edge_live = {1: 0, 2: 0, 3: 0}
            for _did, _nm, _dk, ek, lm, _mod, _sub, _dep in in_rows:
                ek_i = int(ek)
                if ek_i in edge_totals:
                    edge_totals[ek_i] += 1
                    if int(lm) != 0:
                        edge_live[ek_i] += 1

            working_rows = [r for r in in_rows if (not live_only or int(r[4]) != 0)]

            # Separate projections / eliminators / auto-aux / compiler-aux
            field_projs_hit: List[str] = []
            subobj_projs_hit: List[str] = []
            elim_hits: Dict[str, int] = {}
            helper_subdecls: List[str] = []
            auto_aux_count = 0
            compiler_aux_count = 0

            info_by_name: Dict[str, Tuple[int, str, str, int, int, Optional[str], int, Optional[int]]] = {}
            by_mod_scan: Dict[str, Dict[str, int]] = collections.defaultdict(dict)

            for did, nm, dk, ek, lm, mod, sub, dep in working_rows:
                did_i = int(did)
                ek_i = int(ek)
                lm_i = int(lm)
                sub_i = int(sub)
                dep_opt = None if int(dep) < 0 else int(dep)

                if _RE_COMPILER_AUX.search(nm):
                    compiler_aux_count += 1
                    continue

                if nm.startswith(lo):
                    leaf = nm[lo_len:]
                    if "." not in leaf:
                        if leaf in own_field_set:
                            field_projs_hit.append(leaf)
                            continue
                        if leaf in subobj_set:
                            subobj_projs_hit.append(leaf)
                            continue
                        if leaf in ELIM_NAMES:
                            elim_hits[leaf] = elim_fan_in.get(leaf, 0)
                            continue
                        if leaf in AUTO_AUX_NAMES:
                            auto_aux_count += 1
                            continue
                    if leaf.startswith(("mk.", "rec.", "casesOn.", "recOn.", "noConfusion")):
                        auto_aux_count += 1
                        continue

                info_by_name[nm] = (did_i, nm, dk, ek_i, lm_i, mod, sub_i, dep_opt)
                if real_src_root and dk != "inductive" and mod:
                    by_mod_scan[mod][nm] = ek_i

            producers_map: Dict[str, Dict[str, Any]] = {}
            prop_specs_list: List[Dict[str, Any]] = []
            consumer_bindings_set: Set[str] = set()

            if real_src_root and by_mod_scan:
                mod_items = sorted(by_mod_scan.items())
                has_e2_scan = any(ek == 2 for cmap in by_mod_scan.values() for ek in cmap.values())
                cons_exact: Set[str] = set()
                cons_suffixes: Set[str] = set()
                if has_e2_scan and not is_prop_def_target and exp_arity >= 1:
                    for c_nm, c_inf in info_by_name.items():
                        if c_inf[3] in (1, 3):
                            cons_exact.add(c_nm)
                            leaf_c = c_nm.rsplit(".", 1)[-1]
                            if len(leaf_c) >= 4:
                                cons_suffixes.add(leaf_c)

                binder_rx: Optional[re.Pattern[bytes]] = None
                word_rx: Optional[re.Pattern[bytes]] = None
                f_probe: Optional[List[bytes]] = None
                if len(mod_items) >= 500:
                    s_bytes = re.escape(s_leaf).encode("utf-8")
                    binder_rx = re.compile(
                        rb"[\(\{\[]\s*[A-Za-z0-9_'\xc0-\xff]+(?:\s+[A-Za-z0-9_'\xc0-\xff]+)*\s*:\s*"
                        rb"(?:_root_\.)?(?:[A-Za-z0-9_']+\.)*" + s_bytes + rb"\s*[\)\}\]]"
                    )
                    word_rx = re.compile(rb"(?<![A-Za-z0-9_'])" + s_bytes + rb"(?![A-Za-z0-9_'])")
                    if len(own_field_list) >= 2 and not is_prop_def_target:
                        f_probe = [f.encode("utf-8") + b" :=" for f in own_field_list[:2]]

                if len(mod_items) >= 400:
                    workers = min(16, os.cpu_count() or 4)
                    bsz = max(64, (len(mod_items) + workers * 4 - 1) // (workers * 4))
                    batches = [
                        (
                            real_src_root,
                            mod_items[k : k + bsz],
                            s_fqn,
                            s_leaf,
                            own_field_set,
                            subobj_set,
                            binder_rx,
                            word_rx,
                            f_probe,
                            exp_arity,
                            is_prop_def_target,
                            None,
                            None,
                        )
                        for k in range(0, len(mod_items), bsz)
                    ]
                    global _POOL_CONS_EXACT, _POOL_CONS_SUFFIXES
                    _POOL_CONS_EXACT = cons_exact
                    _POOL_CONS_SUFFIXES = cons_suffixes
                    try:
                        if "fork" in multiprocessing.get_all_start_methods():
                            ctx = multiprocessing.get_context("fork")
                            with ctx.Pool(processes=workers) as pool:
                                raw_hits = [h for chunk_res in pool.map(_scan_instantiation_chunk, batches) for h in chunk_res]
                        else:
                            with multiprocessing.Pool(
                                processes=workers, initializer=_init_inst_pool, initargs=(cons_exact, cons_suffixes)
                            ) as pool:
                                raw_hits = [h for chunk_res in pool.map(_scan_instantiation_chunk, batches) for h in chunk_res]
                    finally:
                        _POOL_CONS_EXACT = set()
                        _POOL_CONS_SUFFIXES = set()
                else:
                    raw_hits = _scan_instantiation_chunk(
                        (
                            real_src_root,
                            mod_items,
                            s_fqn,
                            s_leaf,
                            own_field_set,
                            subobj_set,
                            None,
                            None,
                            None,
                            exp_arity,
                            is_prop_def_target,
                            cons_exact,
                            cons_suffixes,
                        )
                    )

                prop_def_ids: List[int] = []
                for tkey, mod, line_no, kw, pkind, takes_self, is_prop_def, hdr, is_local_witness in raw_hits:
                    if pkind == "__consumer_binding__":
                        consumer_bindings_set.add(tkey)
                        continue
                    inf = info_by_name.get(tkey)
                    if inf is None:
                        continue
                    anchor = _format_anchor(anchor_prefix, mod, line_no)
                    role = "self->S" if takes_self else ("local_witness" if is_local_witness else "root")
                    entry = {
                        "decl_id": inf[0],
                        "name": inf[1],
                        "decl_kind": inf[2],
                        "source_kind": kw,
                        "producer_kind": pkind,
                        "role": role,
                        "is_local_witness": is_local_witness,
                        "takes_self_param": takes_self,
                        "edge_kind": EDGE_KIND_LABELS.get(inf[3], str(inf[3])),
                        "live_mask": inf[4],
                        "dom_subtree_size": inf[6],
                        "root_depth": inf[7],
                        "rh_depth": inf[7],
                        "module": inf[5],
                        "anchor": anchor,
                        "header": hdr,
                    }
                    if is_prop_def:
                        prop_specs_list.append(entry)
                        prop_def_ids.append(inf[0])
                    else:
                        producers_map[tkey] = entry

                # Pass 2: theorems proving a `Prop` existential spec alias (e.g. `towerEx : TowerEx`)
                if prop_def_ids:
                    pqs = ",".join("?" for _ in prop_def_ids)
                    for _did2, nm2, ddef_nm in kconn.execute(
                        f"""
                        SELECT d.id, d.name, ddef.name
                        FROM edges e
                        JOIN decls d ON e.src = d.id
                        JOIN decls ddef ON e.dst = ddef.id
                        WHERE e.dst IN ({pqs}) AND e.kind IN (1, 3) AND d.kind = 'thm'
                        """,
                        prop_def_ids,
                    ):
                        if nm2 in info_by_name and nm2 not in producers_map:
                            inf2 = info_by_name[nm2]
                            mod2 = inf2[5]
                            if mod2:
                                def_leaf = ddef_nm.rsplit(".", 1)[-1]
                                r2 = _scan_instantiation_chunk(
                                    (
                                        real_src_root,
                                        [(mod2, {nm2: inf2[3]})],
                                        ddef_nm,
                                        def_leaf,
                                        set(),
                                        set(),
                                        None,
                                        None,
                                        None,
                                        0,
                                        True,
                                        set(),
                                        set(),
                                    )
                                )
                                for h2 in r2:
                                    if h2[4] in (
                                        "return_type",
                                        "where_ctor",
                                        "record_literal",
                                        "anon_ctor",
                                        "exact_anon_ctor",
                                        "refine_anon_ctor",
                                    ):
                                        hd2 = sighash.split_header(h2[7])
                                        ts2 = h2[5]
                                        if not ts2 and hd2:
                                            ent2: List[Tuple[str, List[str]]] = []
                                            for b2 in hd2["binders"]:
                                                ent2.extend(sighash._binder_entries(b2))
                                            sighash._hoist(list(hd2["type"]), ent2)
                                            ts2 = any(
                                                _tokens_mention_struct(bty2, s_fqn, s_leaf)
                                                for _n2, bty2 in ent2
                                            )
                                        producers_map[nm2] = {
                                            "decl_id": inf2[0],
                                            "name": inf2[1],
                                            "decl_kind": inf2[2],
                                            "source_kind": h2[3],
                                            "producer_kind": f"proves_spec({def_leaf})",
                                            "role": "self->S" if ts2 else "root",
                                            "is_local_witness": False,
                                            "takes_self_param": ts2,
                                            "edge_kind": EDGE_KIND_LABELS.get(inf2[3], str(inf2[3])),
                                            "live_mask": inf2[4],
                                            "dom_subtree_size": inf2[6],
                                            "root_depth": inf2[7],
                                            "rh_depth": inf2[7],
                                            "module": mod2,
                                            "anchor": _format_anchor(anchor_prefix, mod2, h2[2]),
                                            "header": h2[7],
                                        }
            elif not real_src_root and info_by_name:
                # Kernel-only fallback (`--no-src`): identify wrapper-backed existence theorems & value-only defs
                cand_ids = [v[0] for v in info_by_name.values()]
                has_wrap: Set[int] = set()
                if wrap_ids and cand_ids:
                    wqs = ",".join("?" for _ in wrap_ids)
                    for idx_c in range(0, len(cand_ids), 900):
                        chk = cand_ids[idx_c : idx_c + 900]
                        cqs = ",".join("?" for _ in chk)
                        for (sdid,) in kconn.execute(
                            f"SELECT DISTINCT src FROM edges WHERE src IN ({cqs}) AND dst IN ({wqs}) AND kind IN (1, 3)",
                            (*chk, *wrap_ids),
                        ):
                            has_wrap.add(int(sdid))
                for nm, inf in info_by_name.items():
                    if nm.startswith(lo):
                        continue
                    if (inf[2] == "thm" and inf[0] in has_wrap) or (inf[2] == "def" and inf[3] in (1, 2)):
                        producers_map[nm] = {
                            "decl_id": inf[0],
                            "name": inf[1],
                            "decl_kind": inf[2],
                            "source_kind": inf[2],
                            "producer_kind": "kernel_candidate",
                            "role": "root",
                            "is_local_witness": False,
                            "takes_self_param": False,
                            "edge_kind": EDGE_KIND_LABELS.get(inf[3], str(inf[3])),
                            "live_mask": inf[4],
                            "dom_subtree_size": inf[6],
                            "root_depth": inf[7],
                            "rh_depth": inf[7],
                            "module": inf[5],
                            "anchor": None,
                            "header": None,
                        }

            prop_spec_names = {p["name"] for p in prop_specs_list}
            consumers_raw: List[Tuple[int, str, str, int, int, Optional[str], int, Optional[int]]] = []
            consumer_edge_counts = {"type": 0, "value": 0, "both": 0}
            inductive_carriers_count = 0

            for nm, inf in info_by_name.items():
                if nm in producers_map or nm in prop_spec_names:
                    continue
                if nm.startswith(lo):
                    helper_subdecls.append(nm[lo_len:])
                    continue
                consumers_raw.append(inf)
                ek_lbl = EDGE_KIND_LABELS.get(inf[3], "both")
                consumer_edge_counts[ek_lbl] = consumer_edge_counts.get(ek_lbl, 0) + 1
                if inf[2] == "inductive":
                    inductive_carriers_count += 1

            producers_all = sorted(
                producers_map.values(),
                key=lambda p: (
                    p["live_mask"] == 0,
                    bool(p["takes_self_param"]),
                    bool(p.get("is_local_witness")),
                    -int(p["dom_subtree_size"]),
                    p["name"],
                ),
            )
            prop_specs_list.sort(key=lambda p: (p["live_mask"] == 0, -int(p["dom_subtree_size"]), p["name"]))
            consumers_raw.sort(key=lambda c: (c[4] == 0, -c[6], c[1]))

            producers_shown = producers_all[:limit] if (limit and limit > 0) else producers_all
            top_cons_slice = consumers_raw[:limit] if (limit and limit > 0) else consumers_raw

            cons_hdr_map: Dict[str, Tuple[str, str, str]] = {}
            if real_src_root and top_cons_slice:
                top_by_mod: Dict[str, Set[str]] = collections.defaultdict(set)
                for c in top_cons_slice:
                    if c[5]:
                        top_by_mod[c[5]].add(c[1])
                cons_hdr_map = _extract_decl_headers_in_modules(
                    real_src_root, top_by_mod, anchor_prefix=anchor_prefix
                )

            top_consumers: List[Dict[str, Any]] = []
            for c in top_cons_slice:
                hinfo = cons_hdr_map.get(c[1])
                top_consumers.append(
                    {
                        "decl_id": c[0],
                        "name": c[1],
                        "decl_kind": c[2],
                        "source_kind": hinfo[1] if hinfo else c[2],
                        "consumer_role": "consumer_binding" if c[1] in consumer_bindings_set else "consumer",
                        "edge_kind": EDGE_KIND_LABELS.get(c[3], str(c[3])),
                        "live_mask": c[4],
                        "dom_subtree_size": c[6],
                        "root_depth": c[7],
                        "rh_depth": c[7],
                        "module": c[5],
                        "anchor": hinfo[0] if hinfo else None,
                        "header": hinfo[2] if hinfo else None,
                    }
                )

            proj_total_count = (
                len(field_projs_hit)
                + len(subobj_projs_hit)
                + len(elim_hits)
                + len(helper_subdecls)
                + auto_aux_count
                + compiler_aux_count
            )

            target_obj: Dict[str, Any] = {
                "decl_id": sid,
                "name": s_fqn,
                "module": smod,
                "anchor": s_anchor,
                "source_kind": source_kind,
                "universe_kind": "Prop" if is_prop is True else ("Type*" if is_prop is False else "Unknown"),
                "is_prop": is_prop,
                "total_fields": len(own_field_list),
                "fan_in": int(fan_in),
                "live_mask": int(s_live_mask),
                "incoming_edges": {
                    "total": len(in_rows),
                    "live": sum(1 for r in in_rows if int(r[4]) != 0),
                    "analyzed": len(working_rows),
                    "by_edge_kind": {
                        "type": {"total": edge_totals[1], "live": edge_live[1]},
                        "value": {"total": edge_totals[2], "live": edge_live[2]},
                        "both": {"total": edge_totals[3], "live": edge_live[3]},
                    },
                },
                "producers": {
                    "total_count": len(producers_all),
                    "root_count": sum(
                        1 for p in producers_all if not p["takes_self_param"] and not p.get("is_local_witness")
                    ),
                    "local_witness_count": sum(
                        1 for p in producers_all if not p["takes_self_param"] and p.get("is_local_witness")
                    ),
                    "self_transform_count": sum(1 for p in producers_all if p["takes_self_param"]),
                    "live_count": sum(1 for p in producers_all if p["live_mask"] != 0),
                    "prop_spec_defs_count": len(prop_specs_list),
                    "returned": len(producers_shown),
                    "sites": producers_shown,
                    "prop_spec_defs": prop_specs_list,
                },
                "consumers": {
                    "total_count": len(consumers_raw),
                    "live_count": sum(1 for c in consumers_raw if c[4] != 0),
                    "consumer_bindings_count": sum(1 for c in consumers_raw if c[1] in consumer_bindings_set),
                    "by_edge_kind": consumer_edge_counts,
                    "inductive_carriers_count": inductive_carriers_count,
                    "returned_top": len(top_consumers),
                    "top_examples": top_consumers,
                },
                "projections_and_helpers": {
                    "total_count": proj_total_count,
                    "field_projections": sorted(field_projs_hit),
                    "subobject_projections": sorted(subobj_projs_hit),
                    "eliminators": dict(sorted(elim_hits.items())),
                    "helper_subdecls": sorted(helper_subdecls),
                    "auto_aux_count": auto_aux_count,
                    "compiler_aux_count": compiler_aux_count,
                },
            }
            if is_prop_def_target:
                target_obj["is_prop_def"] = True
                target_obj["conjuncts"] = conjuncts_list
            targets_out.append(target_obj)

        elapsed = round(time.time() - t0, 3)
        return {
            "schema": INSTANTIATIONS_SCHEMA_VERSION,
            "pins": {
                "kernel_db": _rel_repo_path(kernel_db_path),
                "src_root": _rel_repo_path(real_src_root) if real_src_root else None,
                "source_mode": "source+kernel" if real_src_root else "kernel_only",
                "elapsed_seconds": elapsed,
            },
            "query": {
                "instantiations": queries[0] if len(queries) == 1 else list(queries),
                "queries": list(queries),
                "exact": bool(exact),
                "live_only": live_only,
                "limit": limit,
                "targets_matched": len(targets_out),
            },
            "targets": targets_out,
        }
    finally:
        kconn.close()


def format_instantiations_text(rep: Dict[str, Any]) -> str:
    """Render a concise plain-text report for `leanre bundles --instantiations`."""
    pins = rep["pins"]
    q = rep["query"]
    lines: List[str] = [
        (
            f"leanre bundles --instantiations ({rep['schema']}) — "
            f"mode={pins['source_mode']}, live_only={q['live_only']} ({pins['elapsed_seconds']}s)"
        ),
        "",
    ]
    for t in rep["targets"]:
        ie = t["incoming_edges"]
        bek = ie["by_edge_kind"]
        pr = t["producers"]
        cs = t["consumers"]
        ph = t["projections_and_helpers"]

        lbl = "conjuncts" if t.get("is_prop_def") else "fields"
        lines.append(
            f"[{t['universe_kind']} / {t['source_kind']}] {t['name']} "
            f"(id={t['decl_id']}, {lbl}={t['total_fields']}, live_mask={t['live_mask']})"
        )
        if t["anchor"]:
            lines.append(f"  anchor         : {t['anchor']}")
        if t.get("conjuncts"):
            sample_c = ", ".join(t["conjuncts"][:6])
            if len(t["conjuncts"]) > 6:
                sample_c += ", …"
            lines.append(f"  conjuncts ({len(t['conjuncts'])}) : {sample_c}")
        lines.append(
            f"  incoming edges : {ie['total']:,} total / {ie['live']:,} live "
            f"(type={bek['type']['total']:,}, value={bek['value']['total']:,}, both={bek['both']['total']:,})"
        )
        lw_cnt = int(pr.get("local_witness_count") or 0)
        cb_cnt = int(cs.get("consumer_bindings_count") or 0)
        lines.append(
            f"  partition      : producers={pr['total_count']:,} "
            f"(root={pr['root_count']:,}"
            + (f", local_witness={lw_cnt:,}" if lw_cnt else "")
            + f", self->S={pr['self_transform_count']:,}, live={pr['live_count']:,}"
            + (f", prop_specs={pr['prop_spec_defs_count']}" if pr["prop_spec_defs_count"] else "")
            + f") | consumers={cs['total_count']:,}"
            + (f" (bindings={cb_cnt:,})" if cb_cnt else "")
            + f" | projections/helpers={ph['total_count']:,}"
        )
        lines.append(
            f"  excl. bucket   : field_projs={len(ph['field_projections'])}, "
            f"subobjs={len(ph['subobject_projections'])}, "
            f"elims={len(ph['eliminators'])}, "
            f"helpers={len(ph['helper_subdecls'])}, "
            f"compiler_aux={ph['compiler_aux_count']:,}"
        )
        if ph["helper_subdecls"]:
            sample_h = ", ".join(ph["helper_subdecls"][:8])
            if len(ph["helper_subdecls"]) > 8:
                sample_h += ", …"
            lines.append(f"  helpers excl.  : {sample_h}")

        lines.append(
            f"  Producers / constructor sites ({pr['returned']} / {pr['total_count']} shown):"
        )
        if not pr["sites"]:
            lines.append("    (none found)")
        for idx, s in enumerate(pr["sites"], 1):
            role = s.get("role") or ("self->S" if s["takes_self_param"] else "root")
            lines.append(
                f"    {idx:>2}. [{role} | {s['producer_kind']} | edge={s['edge_kind']} | "
                f"live={s['live_mask']} | dom={s['dom_subtree_size']:,}] {s['name']}"
            )
            if s["anchor"]:
                lines.append(f"        anchor: {s['anchor']}")
            if s["header"]:
                lines.append(f"        header: {s['header']}")

        if pr["prop_spec_defs"]:
            lines.append(f"  Existential Prop spec defs ({len(pr['prop_spec_defs'])}):")
            for ps in pr["prop_spec_defs"][:5]:
                lines.append(
                    f"    - [live={ps['live_mask']} | dom={ps['dom_subtree_size']:,}] "
                    f"{ps['name']} ({ps['anchor'] or 'no-anchor'})"
                )

        lines.append(
            f"  Consumers / parameter sites ({cs['total_count']:,} total; top {cs['returned_top']} by dom):"
        )
        for idx, c in enumerate(cs["top_examples"][:10], 1):
            loc = f" @ {c['anchor']}" if c["anchor"] else ""
            crole = " | consumer_binding" if c.get("consumer_role") == "consumer_binding" else ""
            lines.append(
                f"    {idx:>2}. [dom={c['dom_subtree_size']:,} | edge={c['edge_kind']} | "
                f"live={c['live_mask']}{crole}] {c['name']}{loc}"
            )
        lines.append("")

    return "\n".join(lines).rstrip()


def format_bundles_text(rep: Dict[str, Any]) -> str:
    """Render a concise plain-text report from a `leanre.bundles/1` result."""
    s = rep["summary"]
    q = rep["query"]
    pins = rep["pins"]
    pp = s["prop_partition"]
    tp = s["type_partition"]

    unmatched_qs = q.get("unmatched_queries") or rep.get("unmatched_queries") or []
    unmatched_details = q.get("unmatched_details") or []

    if s.get("targeted_mode"):
        q_list = q.get("structures") or ([q["structure"]] if q.get("structure") else [])
        unmatched_suffix = f", {len(unmatched_qs)} unmatched" if unmatched_qs else ""
        summary_line = (
            f"Targeted batch: {s['total_live_1ctor_project_inductives']:,} live 1-ctor structure(s) matched "
            f"across {len(q_list)} query target(s){unmatched_suffix} (: Prop {pp['total']:,} | : Type* {tp['total']:,})"
        )
    else:
        summary_line = (
            f"Corpus: {s['total_live_1ctor_project_inductives']:,} live 1-ctor project inductives "
            f"(: Prop {pp['total']:,} [full={pp['full_own']:,}, partial_nocases={pp['partial_nocases']:,}, "
            f"0proj_nocases={pp['zero_proj_nocases']:,}, elim={pp['partial_cases']+pp['zero_proj_cases']:,}] | "
            f": Type* {tp['total']:,} [empty={tp['zero_field']:,}, full={tp['full_own']:,}, "
            f"partial_nocases={tp['partial_nocases']:,}, 0proj_nocases={tp['zero_proj_nocases']:,}])"
        )

    lines: List[str] = [
        f"leanre bundles ({rep['schema']}) — mode={pins['source_mode']} ({pins['elapsed_seconds']}s)",
        summary_line,
    ]
    if unmatched_details:
        lines.append(
            "WARNING: unmatched / non-structure targets: "
            + "; ".join(_format_unmatched_item(item) for item in unmatched_details)
        )
    elif unmatched_qs:
        lines.append(
            "WARNING: unmatched / non-structure targets: " + ", ".join(unmatched_qs)
        )
    lines.append("")

    bundles = rep["bundles"]
    if q.get("structure") and not bundles:
        lines.append("(no matching live 1-constructor project structures)")
    elif q.get("structure") and bundles:
        for b in bundles:
            elim_tag = (
                f"ELIMINATED (casesOn={b['casesOn_fan_in']}, recOn={b['recOn_fan_in']}, rec={b['rec_fan_in']})"
                if b["is_eliminated"]
                else "casesOn/recOn=0"
            )
            lines.append(f"[{b['universe_kind']} / {b['source_kind']}] {b['name']} (id={b['decl_id']})")
            if b["anchor"]:
                lines.append(f"  anchor         : {b['anchor']}")
            lines.append(
                f"  own fields     : {b['projected_fields']}/{b['total_fields']} projected, "
                f"{b['unread_fields']}/{b['total_fields']} unread ({100.0*b['unread_ratio']:.1f}%)"
            )
            lines.append(
                f"  impact         : fan_in={b['fan_in']:,}, max_caller_dom={b['max_caller_dom_sub']:,}, "
                f"score={b['weighted_score']:,.1f}, root_depth={b.get('root_depth', b.get('rh_depth'))}"
            )
            lines.append(f"  eliminators    : {elim_tag}")
            if b["helper_subdecls_excluded"]:
                lines.append(f"  helpers excl.  : {', '.join(b['helper_subdecls_excluded'])}")
            if b["subobject_projections"]:
                lines.append(f"  extends subobj : {', '.join(b['subobject_projections'])}")
            if b["unread_field_names"]:
                lines.append(f"  unread fields  : {', '.join(b['unread_field_names'])}")
            if b["top_caller"]:
                lines.append(f"  top caller     : {b['top_caller']}")
            lines.append("")
    else:
        lines.append(
            f"Showing {q['returned']} / {q['total_matching']} "
            f"(only={q['only']}, sort={q['sort']}, min_fields={q['min_fields']})"
        )
        lines.append(
            f"{'#':>3}  {'Kind':<5} {'Proj/Tot':>8} {'Unr':>4} {'fi':>6} {'MaxDom':>8} "
            f"{'Score':>10}  {'Structure'} (excluded helpers / unread sample)"
        )
        lines.append("-" * 105)
        for idx, b in enumerate(bundles, 1):
            frac = f"{b['projected_fields']}/{b['total_fields']}"
            extra_parts: List[str] = []
            if b["is_placeholder"]:
                extra_parts.append("[0-field placeholder]")
            if b["helper_subdecls_excluded"]:
                extra_parts.append("excl:" + ",".join(b["helper_subdecls_excluded"][:3]))
            if b["unread_field_names"]:
                sample = ",".join(b["unread_field_names"][:4])
                if len(b["unread_field_names"]) > 4:
                    sample += ",…"
                extra_parts.append("unread:" + sample)
            extra = f"  ({'; '.join(extra_parts)})" if extra_parts else ""
            lines.append(
                f"{idx:>3}  {b['universe_kind']:<5} {frac:>8} {b['unread_fields']:>4} "
                f"{b['fan_in']:>6,} {b['max_caller_dom_sub']:>8,} {b['weighted_score']:>10,.1f}  "
                f"{b['name']}{extra}"
            )

    if rep["placeholders"] and q.get("only") != "placeholder" and not q.get("structure"):
        lines.append("")
        lines.append(f"Empty 0-field placeholders ({len(rep['placeholders'])}):")
        for p in rep["placeholders"]:
            lines.append(
                f"  - [{p['universe_kind']}] {p['name']} (fi={p['fan_in']}, "
                f"max_caller_dom={p['max_caller_dom_sub']}, root_depth={p.get('root_depth', p.get('rh_depth'))}) {p['anchor'] or ''}"
            )

    if rep["true_slots"] and not q.get("structure"):
        lines.append("")
        lines.append(f"`abbrev/def := True` slots ({len(rep['true_slots'])}):")
        for ts in rep["true_slots"][:10]:
            refs = f" refs={','.join(ts['referenced_by_structures'][:3])}" if ts["referenced_by_structures"] else ""
            lines.append(
                f"  - [{ts['source_kind']}] {ts['name']} (fi={ts['fan_in']}, vn={ts['value_nodes']}, "
                f"root_depth={ts.get('root_depth', ts.get('rh_depth'))}){refs} {ts['anchor'] or ''}"
            )

    return "\n".join(lines)


def _cmd_bundles(args: argparse.Namespace) -> int:
    inst_targets = getattr(args, "instantiations", None)
    struct_targets = getattr(args, "structure", None)
    if inst_targets is not None and struct_targets is not None:
        print(
            "error: cannot combine --structure and --instantiations in one command",
            file=sys.stderr,
        )
        return 2

    exact = bool(getattr(args, "exact", False))
    try:
        if inst_targets:
            rep = run_instantiations(
                kernel_db_path=args.kernel_db,
                src_root=None if args.no_src else args.src_root,
                instantiations=inst_targets,
                live_only=bool(getattr(args, "live_only", False)),
                limit=int(getattr(args, "limit", 25)),
                exact=exact,
            )
        else:
            rep = run_bundles(
                kernel_db_path=args.kernel_db,
                src_root=None if args.no_src else args.src_root,
                top=args.top,
                min_fields=args.min_fields,
                sort_by=args.sort,
                only=args.only,
                structure=struct_targets,
                include_eliminated=args.include_eliminated,
                exact=exact,
            )
    except (FileNotFoundError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    unmatched_details = (rep.get("query") or {}).get("unmatched_details") or []
    if unmatched_details:
        parts = [_format_unmatched_item(item) for item in unmatched_details]
        print(
            f"warning: {len(parts)} unmatched --structure target(s): {'; '.join(parts)}",
            file=sys.stderr,
        )

    if args.out:
        try:
            _safe_write_json(args.out, rep)
        except ValueError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1

    if args.json:
        print(json.dumps(rep, indent=2, ensure_ascii=False))
    elif inst_targets:
        print(format_instantiations_text(rep))
    else:
        print(format_bundles_text(rep))
    return 0


def register_cli(sub: Any, dest: str = "bundles_func") -> argparse.ArgumentParser:
    """Attach `leanre bundles` subcommand to `leanre/leanre.py` argparse subparsers."""
    p = sub.add_parser(
        "bundles",
        help="Exact source-and-kernel 1-constructor structure unread-field & instantiation audit",
    )
    p.add_argument(
        "--kernel-db",
        default=DEFAULT_KERNEL_DB,
        help="Path to outputs/kernel/kernel.db (opened strictly mode=ro)",
    )
    p.add_argument(
        "--src-root",
        "--src",
        dest="src_root",
        default=DEFAULT_SRC_ROOT,
        help="Optional Lean src/ root for exact structure/class parsing (default: data/rh_mirror/src)",
    )
    p.add_argument(
        "--no-src",
        action="store_true",
        help="Skip .lean source parsing and run in kernel-only mode",
    )
    p.add_argument("--top", type=int, default=35, help="Show top N bundles (0 for all; default: 35)")
    p.add_argument(
        "--min-fields",
        type=int,
        default=None,
        help="Minimum declared own fields required (default: no minimum)",
    )
    p.add_argument(
        "--sort",
        choices=("ratio", "unread", "dom", "cone"),
        default="dom",
        help="Sort order: dom (weighted caller dom score, default), cone (weighted fan-in), ratio, unread",
    )
    p.add_argument(
        "--only",
        choices=("prop", "type", "placeholder", "all"),
        default="all",
        help="Filter partition: prop, type, placeholder, or all (default: all)",
    )
    p.add_argument(
        "--structure",
        action="extend",
        nargs="+",
        default=None,
        metavar="STRUCT",
        help="Inspect one or more structures by exact FQN, suffix, or substring (repeatable or comma-separated)",
    )
    p.add_argument(
        "--exact",
        action="store_true",
        help="Match --structure (or --instantiations) only by exact FQN or exact terminal name (no substring fallback)",
    )
    p.add_argument(
        "--instantiations",
        action="extend",
        nargs="+",
        default=None,
        metavar="STRUCT",
        help="Find constructor/producer sites vs parameter consumers for structure(s)",
    )
    p.add_argument(
        "--live-only",
        action="store_true",
        help="Restrict --instantiations to live declarations (live_mask != 0)",
    )
    p.add_argument(
        "--limit",
        type=int,
        default=25,
        help="Max producer / top consumer examples per structure in --instantiations (0 for all; default: 25)",
    )
    p.add_argument(
        "--include-eliminated",
        action="store_true",
        help="Include bundles with casesOn/recOn/rec fan-in > 0 in ranked output",
    )
    p.add_argument("--json", action="store_true", help="Emit full JSON report to stdout")
    p.add_argument("--out", default=None, help="Optional path to write JSON report")
    p.set_defaults(**{dest: _cmd_bundles})
    return p


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        prog="leanre-bundles",
        description="Exact source-and-kernel structure unread-field auditor",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    register_cli(sub, dest="bundles_func")
    argv_list = list(sys.argv[1:] if argv is None else argv)
    if argv_list and argv_list[0] not in ("bundles", "-h", "--help"):
        argv_list = ["bundles"] + argv_list
    elif not argv_list:
        argv_list = ["bundles"]
    args = ap.parse_args(argv_list)
    return int(args.bundles_func(args))


if __name__ == "__main__":
    sys.exit(main())
