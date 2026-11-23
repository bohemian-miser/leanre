"""Source-level contract reader for `data/rh_mirror/src` (pinned Deicyde/riemann-hypothesis @ 40e56bab).

Extracts, for one declaration:
  * the exact *header* (keyword, name, binders, statement type) -- never a theorem's proof body;
  * `structure` / `class` fields and `inductive` constructors (name + type);
  * for `def` / `abbrev` only: the defining expression (`:= ...`), because for a `Prop`-valued
    definition the body *is* the contract.  Callers that persist output into git must pass it
    through `one_line()` (fair-use <= 1 line) -- see schema.py.

The parser is a small bracket-aware scanner, not a Lean parser; it is good enough for headers
because Lean headers end at the first depth-0 `:=` / `where` / `|`.
"""
from __future__ import annotations

import os
import re
from dataclasses import dataclass, field, asdict
from functools import lru_cache
from typing import Optional

KEYWORDS = ("theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "instance",
            "opaque", "axiom")
_MODS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped)\s+)*"
_DECL_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?" + _MODS + r"(" + "|".join(KEYWORDS) + r")\b\s*(\S*)")
_OPEN = "([{⦃⟨"
_CLOSE = ")]}⦄⟩"
_IDENT_RE = re.compile(r"[A-Za-z_\u0370-\u03ff\u1d00-\u1dbf\u2100-\u214f𝒜-𝔷][\w'.!?\u0370-\u03ff₀-₉ᵢ-ᵪ\u2100-\u214f𝒜-𝔷]*")


@dataclass
class Field:
    name: str
    type: str
    default: bool = False


@dataclass
class Contract:
    name: str
    keyword: str
    file: str
    line: int
    header: str                      # collapsed one-line header (keyword .. statement), no body
    binders: list[str] = field(default_factory=list)
    type: Optional[str] = None       # statement / result type after the depth-0 ':'
    extends: list[str] = field(default_factory=list)
    fields: list[Field] = field(default_factory=list)
    body: Optional[str] = None       # def/abbrev only; collapsed
    body_kind: Optional[str] = None  # 'term' | 'where' | None
    namespace: Optional[str] = None  # enclosing `namespace` stack at the decl
    variables: list[str] = field(default_factory=list)  # `variable` binders in scope (become leading params)

    @property
    def anchor(self) -> str:
        return f"src/{self.file}:{self.line}"

    def to_json(self, max_len: int = 400, with_body: bool = False) -> dict:
        d = asdict(self)
        d["header"] = one_line(self.header, max_len)
        d["type"] = one_line(self.type, max_len) if self.type else None
        b_len = 0 if max_len <= 0 else 200
        v_len = 0 if max_len <= 0 else 300
        f_len = 0 if max_len <= 0 else 240
        d["binders"] = [one_line(b, b_len) for b in self.binders]
        d["variables"] = [one_line(v, v_len) for v in self.variables]
        d["fields"] = [{"name": f.name, "type": one_line(f.type, f_len), "default": f.default} for f in self.fields]
        d["anchor"] = self.anchor
        if not with_body:
            d.pop("body")
        elif self.body is not None:
            d["body"] = one_line(self.body, max_len)
        return d


def one_line(s: Optional[str], max_len: int = 400) -> Optional[str]:
    if s is None:
        return None
    s = " ".join(s.split())
    if max_len <= 0 or len(s) <= max_len:
        return s
    return s[: max_len - 1] + "…"


def strip_comments(text: str) -> str:
    """Remove `/- ... -/` (nested) and `-- ...` comments, preserving newlines for line accounting."""
    out = []
    i, n, depth = 0, len(text), 0
    in_str = False
    while i < n:
        c = text[i]
        if depth == 0 and c == '"' and (i == 0 or text[i - 1] != "\\"):
            in_str = not in_str
            out.append(c); i += 1; continue
        if in_str:
            out.append(c); i += 1; continue
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if c == "\n":
                out.append("\n")
            i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(c); i += 1
    return "".join(out)


@lru_cache(maxsize=4096)
def _file_lines(path: str) -> tuple[str, ...]:
    with open(path, encoding="utf-8", errors="replace") as f:
        return tuple(strip_comments(f.read()).split("\n"))


def _name_matches(found: str, full: str) -> bool:
    found = found.removeprefix("_root_.")
    return full == found or full.endswith("." + found)


def find_decl_line(lines: tuple[str, ...], full_name: str, hint: Optional[int] = None) -> Optional[tuple[int, str]]:
    """Return (1-based line, keyword) of the declaration of `full_name` (namespace-aware suffix match)."""
    order: list[int]
    n = len(lines)
    if hint:
        h = hint - 1
        order = list(range(max(0, h - 3), min(n, h + 60))) + list(range(0, n))
    else:
        order = list(range(n))
    seen = set()
    for i in order:
        if i in seen:
            continue
        seen.add(i)
        m = _DECL_RE.match(lines[i])
        if m and m.group(2) and _name_matches(m.group(2).rstrip(":"), full_name):
            return i + 1, m.group(1)
    return None


def _scan_header(text: str) -> tuple[str, int, str]:
    """Scan from decl keyword; return (header_text, end_index, terminator) with terminator in
    {':=', 'where', '|', 'eof', 'blank'}."""
    depth = 0
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in _OPEN:
            depth += 1
        elif c in _CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0:
            if text.startswith(":=", i):
                return text[:i], i + 2, ":="
            if text.startswith("where", i) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_.'")) and \
                    (i + 5 >= n or not (text[i + 5].isalnum() or text[i + 5] in "_'")):
                return text[:i], i + 5, "where"
            if c == "\n":
                j = i + 1
                while j < n and text[j] in " \t":
                    j += 1
                if j < n and text[j] == "|":
                    return text[:i], j, "|"
                if j < n and text[j] == "\n":
                    k = j + 1
                    while k < n and text[k] in " \t\n":
                        k += 1
                    if k >= n or (text[k - 1] == "\n" and not text.startswith((":=", "where", "|"), k)):
                        return text[:i], j, "blank"
                if j < n and j == i + 1 and _DECL_RE.match(text[j:text.find("\n", j) if text.find("\n", j) >= 0 else n]):
                    return text[:i], j, "blank"
                if text.startswith("deriving", j):
                    return text[:i], j, "blank"
        i += 1
    return text, n, "eof"


def split_header(header: str) -> tuple[str, str, list[str], Optional[str], list[str]]:
    """header -> (keyword, name, binders, type, extends)."""
    m = _DECL_RE.match(header)
    if not m:
        return "", "", [], None, []
    kw, name = m.group(1), m.group(2)
    rest = header[m.end():]
    binders: list[str] = []
    typ: Optional[str] = None
    extends: list[str] = []
    depth, start, i, n = 0, None, 0, len(rest)
    while i < n:
        c = rest[i]
        if c in _OPEN:
            if depth == 0:
                start = i
            depth += 1
        elif c in _CLOSE:
            depth = max(0, depth - 1)
            if depth == 0 and start is not None:
                binders.append(rest[start:i + 1])
                start = None
        elif depth == 0:
            if c == ":" and not rest.startswith(":=", i):
                typ = rest[i + 1:].strip()
                break
            if rest.startswith("extends", i):
                ext = rest[i + 7:]
                j = _depth0_find(ext, ":")
                ext_part, typ = (ext, None) if j < 0 else (ext[:j], ext[j + 1:].strip() or None)
                extends = [e.strip() for e in _depth0_split(ext_part, ",") if e.strip()]
                break
        i += 1
    if name.endswith(":"):
        name = name[:-1]
    return kw, name, binders, typ, extends


def _depth0_find(s: str, ch: str) -> int:
    depth = 0
    for i, c in enumerate(s):
        if c in _OPEN:
            depth += 1
        elif c in _CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and c == ch and not s.startswith(":=", i):
            return i
    return -1


def _depth0_split(s: str, ch: str) -> list[str]:
    out, depth, cur = [], 0, []
    for c in s:
        if c in _OPEN:
            depth += 1
        elif c in _CLOSE:
            depth = max(0, depth - 1)
        if c == ch and depth == 0:
            out.append("".join(cur)); cur = []
        else:
            cur.append(c)
    out.append("".join(cur))
    return out


_FIELD_RE = re.compile(r"^(\s+)([^\s:()\[\]{}⦃⦄]+)\s*(.*)$")


def _parse_fields(lines: list[str]) -> list[Field]:
    """Parse indented `name binders* : type [:= default]` field blocks (structure/class)."""
    blocks: list[list[str]] = []
    base: Optional[int] = None
    for ln in lines:
        if not ln.strip():
            continue
        ind = len(ln) - len(ln.lstrip())
        if base is None:
            base = ind
        if ind <= base:
            blocks.append([ln.strip()])
        elif blocks:
            blocks[-1].append(ln.strip())
    out: list[Field] = []
    for b in blocks:
        text = " ".join(b)
        if text.endswith("::") or re.match(r"^\S+\s*::$", text):  # custom constructor name `mk ::`
            continue
        m = re.match(r"^([^\s:()\[\]{}⦃⦄]+)\s*(.*)$", text)
        if not m:
            continue
        fname, rest = m.group(1), m.group(2)
        j = _depth0_find(rest, ":")
        if j < 0:
            k = rest.find(":=")
            out.append(Field(fname, rest[k + 2:].strip() if k >= 0 else rest, default=k >= 0))
            continue
        binders, typ = rest[:j].strip(), rest[j + 1:].strip()
        dflt = False
        k = typ.find(":=")
        if k >= 0 and _depth0_find(typ[:k] + " ", ":") < 0:
            typ, dflt = typ[:k].strip(), True
        out.append(Field(fname, (binders + " → " + typ) if binders else typ, default=dflt))
    return out


def _parse_ctors(text: str) -> list[Field]:
    out = []
    for part in re.split(r"(?:^|\n)\s*\|", "\n" + text)[1:]:
        part = " ".join(part.split())
        m = re.match(r"^([^\s:()\[\]{}⦃⦄]+)\s*(.*)$", part)
        if m:
            out.append(Field(m.group(1), m.group(2).lstrip(": ").strip()))
    return out


_SCOPE_RE = re.compile(r"^(namespace|section|end|variable|noncomputable section)\b\s*(.*)$")


def scope_at(lines: tuple[str, ...], line_no: int) -> tuple[Optional[str], list[str]]:
    """(namespace, variable-binder lines) in scope just before 1-based `line_no` (approximate Lean scoping)."""
    stack: list[tuple[str, str, list[str]]] = [("root", "", [])]
    pending_in: list[str] = []
    i = 0
    while i < line_no - 1:
        ln = lines[i]
        m = _SCOPE_RE.match(ln)
        if m and ln[:1] not in (" ", "\t"):
            kw, rest = m.group(1), m.group(2).strip()
            if kw == "namespace":
                stack.append(("namespace", rest, []))
            elif kw in ("section", "noncomputable section"):
                stack.append(("section", rest, []))
            elif kw == "end" and len(stack) > 1:
                stack.pop()
            elif kw == "variable":
                buf = [rest]
                while i + 1 < line_no - 1 and lines[i + 1][:1] in (" ", "\t") and lines[i + 1].strip():
                    i += 1
                    buf.append(lines[i].strip())
                v = " ".join(" ".join(buf).split())
                if v.endswith(" in") or v == "in":  # `variable ... in` scopes over the next command only
                    pending_in.append(v[:-3].strip())
                else:
                    stack[-1][2].append(v)
                i += 1
                continue
        if ln[:1] not in ("", " ", "\t") and not ln.startswith("@["):
            pending_in = []
        i += 1
    ns = ".".join(n for k, n, _ in stack if k == "namespace" and n) or None
    return ns, [v for _, _, vs in stack for v in vs] + [f"{v} (variable … in)" for v in pending_in]


def read_contract(src_root: str, rel_file: str, full_name: str, hint: Optional[int] = None,
                  max_lines: int = 400, include_thm: bool = False) -> Optional[Contract]:
    path = os.path.join(src_root, rel_file)
    if not os.path.exists(path):
        return None
    lines = _file_lines(path)
    loc = find_decl_line(lines, full_name, hint)
    if loc is None:
        return None
    line_no, kw = loc
    # take the declaration chunk: until the next depth-0 line starting a new top-level command.
    chunk: list[str] = []
    for j in range(line_no - 1, min(len(lines), line_no - 1 + max_lines)):
        ln = lines[j]
        if j > line_no - 1 and ln and not ln[0].isspace() and (
                ln == "end" or _DECL_RE.match(ln) or ln.startswith((
                    "end ", "namespace ", "section", "open ", "variable",
                    "theorem", "@[", "attribute", "#", "noncomputable section",
                    "set_option", "universe", "/-", "example", "mutual",
                    "deriving", "export ", "notation", "infix", "prefix", "postfix",
                ))):
            break
        chunk.append(ln)
    text = "\n".join(chunk)
    m = _DECL_RE.match(text)
    header_raw, end, term = _scan_header(text[m.start(1):] if m else text)
    off = m.start(1) if m else 0
    header = " ".join(header_raw.split())
    keyword, name, binders, typ, extends = split_header(header)
    c = Contract(name=full_name, keyword=keyword or kw, file=rel_file, line=line_no, header=header,
                 binders=binders, type=typ, extends=extends)
    c.namespace, c.variables = scope_at(lines, line_no)
    tail = text[off + end:]
    if c.keyword in ("structure", "class") and term == "where":
        c.fields = _parse_fields(tail.split("\n")[1:] if not tail.split("\n")[0].strip() else
                                 ["  " + tail.split("\n")[0].strip()] + tail.split("\n")[1:])
    elif c.keyword in ("structure", "class") and term == ":=":
        tail_lines = tail.split("\n")
        fld_lines = tail_lines[1:] if not tail_lines[0].strip() else ["  " + tail_lines[0].strip()] + tail_lines[1:]
        if "::" in tail or any(_depth0_find(ln.strip(), ":") >= 0 for ln in fld_lines if ln.strip()):
            c.fields = _parse_fields(fld_lines)
        c.body_kind = "term"
        c.body = " ".join(tail.split())
    elif c.keyword in ("structure", "class", "inductive") and term in ("|", "where"):
        c.fields = _parse_ctors(tail if term == "where" else "|" + tail[1:])
    elif c.keyword == "inductive" and term == "|":
        c.fields = _parse_ctors("|" + tail[1:])
    elif c.keyword in ("def", "abbrev", "instance", "opaque") and term in (":=", "where", "|"):
        c.body_kind = "term" if term == ":=" else ("where" if term == "where" else "match")
        c.body = " ".join(tail.split())
        if term == "where":  # structure-instance body: keep data fields, hide proof obligations
            c.fields = [f if not _proofish(f.type) else Field(f.name, "<proof>", True)
                        for f in _parse_fields(tail.split("\n")[1:])]
    elif include_thm and c.keyword in ("theorem", "lemma") and term in (":=", "where", "|"):
        c.body_kind = "term" if term == ":=" else ("where" if term == "where" else "match")
        c.body = " ".join(tail.split())
    return c


def _proofish(v: str) -> bool:
    return bool(re.search(r"(^|[\s(⟨])by\b", v)) or v.lstrip().startswith(("fun _", "⟨", "rfl", "by"))


def identifiers(s: Optional[str]) -> set[str]:
    """Identifier tokens (dotted names) appearing in a header fragment."""
    if not s:
        return set()
    return {t.rstrip(".") for t in _IDENT_RE.findall(s)}
