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
  - Python 3.13 stdlib only; zero third-party dependencies.
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sqlite3
import sys
import time
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))

SCHEMA_VERSION = "leanre.bundles/1"

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
            anchor = None
            if mod and line_no is not None:
                anchor = f"src/{mod.replace('.', '/')}.lean:{line_no}"
            confirmed[did] = {
                "decl_id": did,
                "name": nm,
                "source_kind": src_kind,
                "value_nodes": vn,
                "type_nodes": tn,
                "fan_in": fi,
                "rh_depth": None if rh_dep < 0 else int(rh_dep),
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


def _matches_structure_filter(name: str, query: str) -> int:
    """Return match priority: 3=exact, 2=dot-suffix, 1=substring, 0=no match."""
    if name == query:
        return 3
    if name.endswith("." + query):
        return 2
    if query in name:
        return 1
    return 0


def run_bundles(
    kernel_db_path: str = DEFAULT_KERNEL_DB,
    src_root: Optional[str] = DEFAULT_SRC_ROOT,
    top: Optional[int] = 35,
    min_fields: Optional[int] = None,
    sort_by: str = "dom",
    only: str = "all",
    structure: Optional[str] = None,
    include_eliminated: bool = False,
) -> Dict[str, Any]:
    """Audit all live 1-constructor project inductives in `kernel.db` (+ optional source)."""
    t0 = time.time()
    if sort_by not in ("ratio", "unread", "dom", "cone"):
        raise ValueError(f"Unsupported sort key: {sort_by!r}")
    if only not in ("prop", "type", "placeholder", "all"):
        raise ValueError(f"Unsupported --only filter: {only!r}")

    real_src_root: Optional[str] = None
    if src_root:
        if os.path.isdir(src_root):
            real_src_root = os.path.realpath(src_root)
        elif os.path.abspath(src_root) != os.path.abspath(DEFAULT_SRC_ROOT):
            raise FileNotFoundError(f"Missing --src-root directory: {src_root}")

    kconn = connect_ro(kernel_db_path)
    try:
        # 1. All live 1-constructor project inductives
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
                anchor = f"src/{mod.replace('.', '/')}.lean:{s_info['line']}" if mod else None
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
                "rh_depth": None,
                "weighted_score": 0.0,
                "cone_score": round(raw_ratio * int(fi), 1),
            }
            all_records.append(rec_obj)

        # 5. Select candidates needing caller `dom` / `reach` enrichment
        struct_filter_mode = bool(structure)
        matched_records: List[Dict[str, Any]] = []
        if structure:
            prios = [_matches_structure_filter(r["name"], structure) for r in all_records]
            best_p = max(prios, default=0)
            if best_p > 0:
                matched_records = [r for r, p in zip(all_records, prios) if p == best_p]
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
        rh_depth: Dict[int, int] = {}

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
                rh_depth[did] = int(dep)

        for r in all_records:
            did = r["decl_id"]
            raw_ratio = r.pop("_raw_ratio")
            if did in max_dom:
                r["max_caller_dom_sub"] = max_dom[did]
                r["top_caller"] = top_caller.get(did)
                r["weighted_score"] = round(raw_ratio * max_dom[did], 1)
            if did in rh_depth:
                r["rh_depth"] = rh_depth[did]

        # 7. Sort & slice
        def _sort_key(r: Dict[str, Any]) -> Tuple[Any, ...]:
            if sort_by == "ratio":
                return (-r["unread_ratio"], -r["unread_fields"], -r["weighted_score"], -r["fan_in"], r["name"])
            if sort_by == "unread":
                return (-r["unread_fields"], -r["unread_ratio"], -r["weighted_score"], -r["fan_in"], r["name"])
            if sort_by == "cone":
                return (-r["cone_score"], -r["fan_in"], -r["max_caller_dom_sub"], -r["unread_fields"], r["name"])
            return (-r["weighted_score"], -r["max_caller_dom_sub"], -r["unread_fields"], -r["fan_in"], r["name"])

        filtered.sort(key=_sort_key)
        placeholders.sort(key=lambda r: (-r["fan_in"], -r["max_caller_dom_sub"], r["name"]))
        elim_cands.sort(key=lambda r: (-r["max_caller_dom_sub"], -r["unread_fields"], r["name"]))

        shown = filtered[:top] if (top is not None and top > 0) else filtered

        # 8. Detect `abbrev := True` / `def := True` slots
        true_slots = _detect_true_slots(
            kconn, struct_ids, id_to_struct_name, real_src_root, mod_file_cache
        )

        elapsed = round(time.time() - t0, 2)
        return {
            "schema": SCHEMA_VERSION,
            "pins": {
                "kernel_db": _rel_repo_path(kernel_db_path),
                "src_root": _rel_repo_path(real_src_root) if real_src_root else None,
                "source_mode": "source+kernel" if real_src_root else "kernel_only",
                "elapsed_seconds": elapsed,
            },
            "query": {
                "top": top,
                "min_fields": min_fields,
                "sort": sort_by,
                "only": only,
                "structure": structure,
                "include_eliminated": include_eliminated,
                "total_matching": len(filtered),
                "returned": len(shown),
            },
            "summary": {
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


def format_bundles_text(rep: Dict[str, Any]) -> str:
    """Render a concise plain-text report from a `leanre.bundles/1` result."""
    s = rep["summary"]
    q = rep["query"]
    pins = rep["pins"]
    pp = s["prop_partition"]
    tp = s["type_partition"]

    lines: List[str] = [
        f"leanre bundles ({rep['schema']}) — mode={pins['source_mode']} ({pins['elapsed_seconds']}s)",
        (
            f"Corpus: {s['total_live_1ctor_project_inductives']:,} live 1-ctor project inductives "
            f"(: Prop {pp['total']:,} [full={pp['full_own']:,}, partial_nocases={pp['partial_nocases']:,}, "
            f"0proj_nocases={pp['zero_proj_nocases']:,}, elim={pp['partial_cases']+pp['zero_proj_cases']:,}] | "
            f": Type* {tp['total']:,} [empty={tp['zero_field']:,}, full={tp['full_own']:,}, "
            f"partial_nocases={tp['partial_nocases']:,}, 0proj_nocases={tp['zero_proj_nocases']:,}])"
        ),
        "",
    ]

    bundles = rep["bundles"]
    if q.get("structure") and bundles:
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
                f"score={b['weighted_score']:,.1f}, rh_depth={b['rh_depth']}"
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
                f"max_caller_dom={p['max_caller_dom_sub']}, rh_depth={p['rh_depth']}) {p['anchor'] or ''}"
            )

    if rep["true_slots"] and not q.get("structure"):
        lines.append("")
        lines.append(f"`abbrev/def := True` slots ({len(rep['true_slots'])}):")
        for ts in rep["true_slots"][:10]:
            refs = f" refs={','.join(ts['referenced_by_structures'][:3])}" if ts["referenced_by_structures"] else ""
            lines.append(
                f"  - [{ts['source_kind']}] {ts['name']} (fi={ts['fan_in']}, vn={ts['value_nodes']}, "
                f"rh_depth={ts['rh_depth']}){refs} {ts['anchor'] or ''}"
            )

    return "\n".join(lines)


def _cmd_bundles(args: argparse.Namespace) -> int:
    try:
        rep = run_bundles(
            kernel_db_path=args.kernel_db,
            src_root=None if args.no_src else args.src_root,
            top=args.top,
            min_fields=args.min_fields,
            sort_by=args.sort,
            only=args.only,
            structure=args.structure,
            include_eliminated=args.include_eliminated,
        )
    except (FileNotFoundError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if args.out:
        try:
            _safe_write_json(args.out, rep)
        except ValueError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1

    if args.json:
        print(json.dumps(rep, indent=2, ensure_ascii=False))
    else:
        print(format_bundles_text(rep))
    return 0


def register_cli(sub: Any, dest: str = "bundles_func") -> argparse.ArgumentParser:
    """Attach `leanre bundles` subcommand to `leanre/leanre.py` argparse subparsers."""
    p = sub.add_parser(
        "bundles",
        help="Exact source-and-kernel 1-constructor structure unread-field & placeholder audit",
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
        default=None,
        help="Inspect a specific structure by exact FQN, suffix, or substring",
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
