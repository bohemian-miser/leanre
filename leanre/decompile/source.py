"""Source-level contract reader for Lean 4 source trees (configured via `leanre.toml` or `--src`).

Extracts, for one declaration:
  * the exact *header* (keyword, name, binders, statement type) -- never a theorem's proof body
    unless `include_thm=True` is explicitly passed;
  * `structure` / `class` fields and `inductive` constructors (name + type);
  * for `def` / `abbrev` only (by default): the defining expression (`:= ...`), because for a
    `Prop`-valued definition the body *is* the contract.  Callers that persist output into git must
    pass it through `one_line()` (fair-use <= 1 line) -- see schema.py.

The parser is a small bracket-aware scanner, not a Lean parser; it is good enough for headers
because Lean headers end at the first depth-0 `:=` / `where` / `|`.
"""
from __future__ import annotations

import os
import re
import textwrap
import tomllib
from dataclasses import dataclass, field, asdict
from functools import lru_cache
from pathlib import Path
from typing import Any, Optional, Sequence, Union

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO = os.path.dirname(os.path.dirname(_HERE))

KEYWORDS = ("theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "instance",
            "opaque", "axiom")
_MODS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
_DECL_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*" + _MODS + r"(" + "|".join(KEYWORDS) + r")\b\s*(\S*)")
_OPEN = "([{⦃⟨"
_CLOSE = ")]}⦄⟩"
_IDENT_RE = re.compile(r"[A-Za-z_\u0370-\u03ff\u1d00-\u1dbf\u2100-\u214f𝒜-𝔷][\w'.!?\u0370-\u03ff₀-₉ᵢ-ᵪ\u2100-\u214f𝒜-𝔷]*")


def _load_toml_dict(path: str) -> Optional[dict]:
    try:
        with open(path, "rb") as f:
            data = tomllib.load(f)
        return data if isinstance(data, dict) else None
    except (OSError, tomllib.TOMLDecodeError):
        return None


def _prefix_from_src_dir(src_dir: Optional[str]) -> str:
    if src_dir is None:
        return "src/"
    clean = src_dir.strip().strip("/")
    return "" if clean in ("", ".") else f"{clean}/"


@lru_cache(maxsize=256)
def resolve_source_config(src_root: Optional[str] = None, config_path: Optional[str] = None) -> dict[str, Any]:
    """Resolve `anchor_prefix`, `src_root`, and upstream URL metadata from `leanre.toml` or Lake layout.

    Precedence:
      1. Explicit `config_path` (`--config <leanre.toml>`).
      2. `<src_root>/leanre.toml` or `<parent(src_root)>/leanre.toml` when `<parent>` is a Lake root
         or matches `<src_dir>`.
      3. Lake project markers (`lakefile.toml`, `lakefile.lean`, `lean-toolchain`) directly inside
         `src_root` (when `basename(src_root) != 'src'`) -> `anchor_prefix = ''`.
      4. `<REPO>/leanre.toml` when `src_root` resides under this workspace (preserves RH default `src/`).
      5. Default fallback `anchor_prefix = 'src/'`.
    """
    cfg_data: Optional[dict] = None
    cfg_file: Optional[str] = None

    if config_path:
        abs_cfg = os.path.abspath(config_path)
        if not os.path.isfile(abs_cfg):
            raise FileNotFoundError(f"config file not found: {config_path}")
        cfg_data = _load_toml_dict(abs_cfg)
        cfg_file = abs_cfg
    elif src_root:
        abs_src = os.path.abspath(src_root)
        direct_toml = os.path.join(abs_src, "leanre.toml")
        parent_dir = os.path.dirname(abs_src)
        parent_toml = os.path.join(parent_dir, "leanre.toml")
        if os.path.isfile(direct_toml):
            cfg_data = _load_toml_dict(direct_toml)
            cfg_file = direct_toml
        elif os.path.isfile(parent_toml):
            cand = _load_toml_dict(parent_toml)
            if cand is not None:
                p_src_dir = str((cand.get("project") or {}).get("src_dir", "src")).strip("/")
                if os.path.basename(abs_src) == p_src_dir or p_src_dir in ("", "."):
                    cfg_data = cand
                    cfg_file = parent_toml
        if cfg_data is None:
            has_lake_here = any(
                os.path.isfile(os.path.join(abs_src, marker))
                for marker in ("lakefile.toml", "lakefile.lean", "lean-toolchain")
            )
            if has_lake_here and os.path.basename(abs_src) != "src":
                return {
                    "anchor_prefix": "",
                    "src_dir": ".",
                    "resolved_src_root": abs_src,
                    "pinned_commit": "",
                    "upstream_url_template": "",
                    "project_name": os.path.basename(abs_src),
                    "config_path": None,
                }
            if os.path.basename(abs_src) == "src":
                repo_toml = os.path.join(_REPO, "leanre.toml")
                real_repo = os.path.realpath(_REPO)
                real_src = os.path.realpath(abs_src)
                if os.path.isfile(repo_toml) and (
                    abs_src.startswith(os.path.abspath(_REPO) + os.sep)
                    or real_src.startswith(real_repo + os.sep)
                ):
                    cfg_data = _load_toml_dict(repo_toml)
                    cfg_file = repo_toml

    if cfg_data is not None:
        proj = cfg_data.get("project") or {}
        src_dir = str(proj.get("src_dir", "src"))
        anchor_prefix = _prefix_from_src_dir(src_dir)
        resolved_src = src_root
        if cfg_file and not src_root:
            base = Path(cfg_file).resolve().parent
            cand_src = base if src_dir.strip("/") in ("", ".") else (base / src_dir)
            resolved_src = str(cand_src)
        return {
            "anchor_prefix": anchor_prefix,
            "src_dir": src_dir,
            "resolved_src_root": resolved_src,
            "pinned_commit": str(proj.get("pinned_commit", "")),
            "upstream_url_template": str(proj.get("upstream_url_template", "")),
            "project_name": str(proj.get("name", "")),
            "config_path": cfg_file,
        }

    return {
        "anchor_prefix": "src/",
        "src_dir": "src",
        "resolved_src_root": src_root,
        "pinned_commit": "",
        "upstream_url_template": "",
        "project_name": "",
        "config_path": None,
    }


def format_anchor(rel_file: str, line: int, anchor_prefix: str = "src/") -> str:
    rel = rel_file.lstrip("/")
    if anchor_prefix and rel.startswith(anchor_prefix):
        return f"{rel}:{line}"
    return f"{anchor_prefix}{rel}:{line}"


@dataclass
class Field:
    name: str
    type: str
    default: bool = False
    line: Optional[int] = None


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
    body: Optional[str] = None       # def/abbrev only by default; collapsed unless preserve_lines=True
    body_kind: Optional[str] = None  # 'term' | 'where' | 'match' | None
    namespace: Optional[str] = None  # enclosing `namespace` stack at the decl
    variables: list[str] = field(default_factory=list)  # `variable` binders in scope (become leading params)
    anchor_prefix: str = "src/"
    body_lines: list[tuple[int, str]] = field(default_factory=list, repr=False)
    parent_info: Optional[dict[str, Any]] = field(default=None, repr=False)

    @property
    def anchor(self) -> str:
        return format_anchor(self.file, self.line, self.anchor_prefix)

    def upstream_url(self, url_template: str, commit: str = "") -> Optional[str]:
        if not url_template:
            return None
        try:
            return url_template.format(commit=commit or "HEAD", path=self.file.lstrip("/"), line=self.line)
        except (KeyError, ValueError):
            return None

    def to_json(self, max_len: int = 400, with_body: bool = False, preserve_lines: bool = False) -> dict:
        d = asdict(self)
        d.pop("anchor_prefix", None)
        d.pop("body_lines", None)
        parent_info = d.pop("parent_info", None)
        d["header"] = one_line(self.header, max_len)
        d["type"] = one_line(self.type, max_len) if self.type else None
        b_len = 0 if max_len <= 0 else 200
        v_len = 0 if max_len <= 0 else 300
        f_len = 0 if max_len <= 0 else 240
        d["binders"] = [one_line(b, b_len) for b in self.binders]
        d["variables"] = [one_line(v, v_len) for v in self.variables]
        d["fields"] = [
            {
                "name": f.name,
                "type": one_line(f.type, f_len),
                "default": f.default,
                **({"line": f.line} if f.line is not None else {}),
            }
            for f in self.fields
        ]
        d["anchor"] = self.anchor
        if parent_info:
            if parent_info.get("is_constructor"):
                d["ctor_of"] = parent_info
            elif parent_info.get("auto_instance"):
                d["auto_instance"] = parent_info
            else:
                d["field_of"] = parent_info
        if not with_body:
            d.pop("body", None)
        elif self.body is not None:
            d["body"] = preserve_truncate(self.body, max_len) if preserve_lines else one_line(self.body, max_len)
        return d


def one_line(s: Optional[str], max_len: int = 400) -> Optional[str]:
    if s is None:
        return None
    s = " ".join(s.split())
    if max_len <= 0 or len(s) <= max_len:
        return s
    return s[: max_len - 1] + "…"


def preserve_truncate(s: Optional[str], max_len: int = 400) -> Optional[str]:
    """Truncate `s` to `max_len` without collapsing newlines or indentation."""
    if s is None:
        return None
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


def _split_field_default(typ: str) -> tuple[str, bool]:
    """Split a structure field's trailing `:= default` without truncating `letI := ...;` / `let ... in` types."""
    depth = 0
    seg_start = 0
    in_let_val = False
    i, n = 0, len(typ)
    while i < n:
        c = typ[i]
        if c in _OPEN:
            depth += 1
        elif c in _CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0:
            if in_let_val:
                if c == ";":
                    in_let_val = False
                    seg_start = i + 1
                elif typ.startswith("in", i) and (i == 0 or typ[i - 1].isspace()) and (
                    i + 2 < n and typ[i + 2].isspace()
                ):
                    in_let_val = False
                    seg_start = i + 2
                    i += 2
                    continue
            elif typ.startswith(":=", i):
                prefix_seg = typ[seg_start:i]
                if re.search(r"(?:^|[\s;])(?:letI?|haveI?)\b", prefix_seg):
                    in_let_val = True
                    i += 2
                    continue
                if _depth0_find(prefix_seg + " ", ":") < 0:
                    return typ[:i].strip(), True
                i += 2
                continue
        i += 1
    return typ, False


def _parse_fields(lines: Sequence[Union[str, tuple[Optional[int], str]]]) -> list[Field]:
    """Parse indented `name binders* : type [:= default]` field blocks (structure/class)."""
    blocks: list[tuple[Optional[int], list[str]]] = []
    base: Optional[int] = None
    for item in lines:
        if isinstance(item, tuple):
            ln_no, ln = item
        else:
            ln_no, ln = None, item
        s = ln.strip()
        if not s:
            continue
        if base is None and re.match(r"^\S+\s*::$", s):  # custom constructor name `mk ::`
            continue
        ind = len(ln) - len(ln.lstrip())
        if base is None:
            base = ind
        if ind <= base:
            blocks.append((ln_no, [s]))
        elif blocks:
            blocks[-1][1].append(s)
    out: list[Field] = []
    for blk_line, b in blocks:
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
            out.append(Field(fname, rest[k + 2:].strip() if k >= 0 else rest, default=k >= 0, line=blk_line))
            continue
        binders, typ = rest[:j].strip(), rest[j + 1:].strip()
        typ, dflt = _split_field_default(typ)
        out.append(Field(fname, (binders + " → " + typ) if binders else typ, default=dflt, line=blk_line))
    return out


def _parse_ctors(text: str, start_line: Optional[int] = None) -> list[Field]:
    out = []
    norm = "\n" + text
    for m_bar in re.finditer(r"(?:^|\n)\s*\|", norm):
        bar_pos = m_bar.end()
        nxt = re.search(r"(?:^|\n)\s*\|", norm[bar_pos:])
        raw_part = norm[bar_pos: bar_pos + nxt.start()] if nxt else norm[bar_pos:]
        ctor_line = (start_line + text[:max(0, m_bar.start() - 1)].count("\n")) if start_line is not None else None
        if start_line is not None and m_bar.group(0).startswith("\n"):
            ctor_line = start_line + text[:m_bar.start()].count("\n")
        part = " ".join(raw_part.split())
        m = re.match(r"^([^\s:()\[\]{}⦃⦄]+)\s*(.*)$", part)
        if m:
            out.append(Field(m.group(1), m.group(2).lstrip(": ").strip(), line=ctor_line))
    return out


def _extract_body_lines(tail: str, term: str, tail_start_line: int, decl_indent: int = 0) -> list[tuple[int, str]]:
    """Return `(1-based .lean file line_no, formatted_line_text)` pairs for `tail`."""
    indexed = [(tail_start_line + idx, ln.rstrip()) for idx, ln in enumerate(tail.split("\n"))]
    while indexed and not indexed[-1][1].strip():
        indexed.pop()
    if not indexed:
        return []
    first_inline = bool(indexed[0][1].strip())
    while indexed and not indexed[0][1].strip():
        indexed.pop(0)
    if not indexed:
        return []
    if first_inline:
        head_ln, head_txt = indexed[0][0], indexed[0][1].lstrip()
        rest = indexed[1:]
        if not rest:
            return [(head_ln, head_txt)]
        if term == "|":
            non_empty_ind = [len(ln) - len(ln.lstrip()) for _, ln in rest if ln.strip()]
            cut = min(non_empty_ind) if non_empty_ind else 0
            fmt_rest = [(lno, ln[cut:] if len(ln) >= cut else ln.lstrip()) for lno, ln in rest]
        elif decl_indent > 0:
            fmt_rest = [
                (lno, ln[decl_indent:] if ln[:decl_indent].isspace() and len(ln) >= decl_indent else ln)
                for lno, ln in rest
            ]
        else:
            fmt_rest = rest
        return [(head_ln, head_txt), *fmt_rest]
    dedented = textwrap.dedent("\n".join(ln for _, ln in indexed)).split("\n")
    out = [(indexed[i][0], dedented[i].rstrip()) for i in range(min(len(indexed), len(dedented)))]
    while out and not out[-1][1].strip():
        out.pop()
    return out


def _format_body(tail: str, term: str, preserve_lines: bool, decl_indent: int = 0,
                 tail_start_line: int = 1) -> tuple[str, list[tuple[int, str]]]:
    blines = _extract_body_lines(tail, term, tail_start_line, decl_indent)
    if not preserve_lines:
        return " ".join(tail.split()), blines
    return "\n".join(txt for _, txt in blines), blines


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


def _parse_contract_at_line(
    lines: tuple[str, ...],
    rel_file: str,
    full_name: str,
    line_no: int,
    kw_fallback: str,
    *,
    max_lines: int = 2500,
    include_thm: bool = False,
    preserve_lines: bool = False,
    anchor_prefix: str = "src/",
    include_scope: bool = True,
) -> Contract:
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
    decl_indent = (len(chunk[0]) - len(chunk[0].lstrip())) if chunk else 0
    m = _DECL_RE.match(text)
    off = m.start(1) if m else 0
    header_raw, end, term = _scan_header(text[off:])
    header = " ".join(header_raw.split())
    keyword, _name, binders, typ, extends = split_header(header)
    c = Contract(name=full_name, keyword=keyword or kw_fallback, file=rel_file, line=line_no, header=header,
                 binders=binders, type=typ, extends=extends, anchor_prefix=anchor_prefix)
    if include_scope:
        c.namespace, c.variables = scope_at(lines, line_no)
    tail = text[off + end:]
    tail_start_line = line_no + text[:off + end].count("\n")

    def _tail_line_pairs(t_lines: list[str]) -> list[tuple[Optional[int], str]]:
        if not t_lines[0].strip():
            return [(tail_start_line + idx, ln) for idx, ln in enumerate(t_lines[1:], 1)]
        return [(tail_start_line, "  " + t_lines[0].strip())] + [
            (tail_start_line + idx, ln) for idx, ln in enumerate(t_lines[1:], 1)
        ]

    if c.keyword in ("structure", "class") and term == "where":
        c.fields = _parse_fields(_tail_line_pairs(tail.split("\n")))
    elif c.keyword in ("structure", "class") and term == ":=":
        fld_pairs = _tail_line_pairs(tail.split("\n"))
        if "::" in tail or any(_depth0_find(ln.strip(), ":") >= 0 for _, ln in fld_pairs if ln.strip()):
            c.fields = _parse_fields(fld_pairs)
        c.body_kind = "term"
        c.body, c.body_lines = _format_body(tail, term, preserve_lines, decl_indent, tail_start_line)
    elif c.keyword in ("structure", "class", "inductive") and term in ("|", "where"):
        ctor_txt = tail if term == "where" else "|" + tail[1:]
        c.fields = _parse_ctors(ctor_txt, start_line=tail_start_line)
    elif c.keyword == "inductive" and term == "|":
        c.fields = _parse_ctors("|" + tail[1:], start_line=tail_start_line)
    elif c.keyword in ("def", "abbrev", "instance", "opaque") and term in (":=", "where", "|"):
        c.body_kind = "term" if term == ":=" else ("where" if term == "where" else "match")
        c.body, c.body_lines = _format_body(tail, term, preserve_lines, decl_indent, tail_start_line)
        if term == "where":  # structure-instance body: keep data fields, hide proof obligations
            fld_pairs = [(tail_start_line + idx, ln) for idx, ln in enumerate(tail.split("\n")[1:], 1)]
            c.fields = [f if not _proofish(f.type) else Field(f.name, "<proof>", True, line=f.line)
                        for f in _parse_fields(fld_pairs)]
    elif include_thm and c.keyword in ("theorem", "lemma") and term in (":=", "where", "|"):
        c.body_kind = "term" if term == ":=" else ("where" if term == "where" else "match")
        c.body, c.body_lines = _format_body(tail, term, preserve_lines, decl_indent, tail_start_line)
    return c


def read_contract(src_root: str, rel_file: str, full_name: str, hint: Optional[int] = None,
                  max_lines: int = 2500, include_thm: bool = False,
                  preserve_lines: bool = False,
                  anchor_prefix: Optional[str] = None,
                  include_scope: bool = True) -> Optional[Contract]:
    path = os.path.join(src_root, rel_file)
    if not os.path.exists(path):
        return None
    if anchor_prefix is None:
        anchor_prefix = resolve_source_config(src_root)["anchor_prefix"]
    lines = _file_lines(path)
    loc = find_decl_line(lines, full_name, hint)
    if loc is None:
        return None
    line_no, kw = loc
    return _parse_contract_at_line(
        lines,
        rel_file,
        full_name,
        line_no,
        kw,
        max_lines=max_lines,
        include_thm=include_thm,
        preserve_lines=preserve_lines,
        anchor_prefix=anchor_prefix,
        include_scope=include_scope,
    )


def locate_auto_instance_contract(
    src_root: str,
    rel_file: str,
    inst_name: str,
    *,
    carrier_stems: Sequence[str] = (),
    type_stems: Sequence[str] = (),
    line_hints: Sequence[int] = (),
    include_thm: bool = False,
    preserve_lines: bool = False,
    anchor_prefix: Optional[str] = None,
    include_scope: bool = True,
) -> Optional[Contract]:
    """Locate an elaborated Lean 4 anonymous `instance : Class (Carrier ...)` or `deriving` clause
    in `rel_file` for an auto-named instance like `Formalism.GaloisCohomology.instTopologicalSpaceQZ`."""
    path = os.path.join(src_root, rel_file)
    if not os.path.exists(path):
        return None
    if anchor_prefix is None:
        anchor_prefix = resolve_source_config(src_root)["anchor_prefix"]
    lines = _file_lines(path)
    n = len(lines)

    inst_last = inst_name.rsplit(".", 1)[-1]
    inst_core_lo = re.sub(r"^(?:inst|_inst_)", "", inst_last).lower()

    # Candidate 1-based line numbers of `instance` commands in `rel_file`
    cand_lines: list[int] = []
    seen_ln: set[int] = set()
    for lh in line_hints:
        if 1 <= lh <= n and lh not in seen_ln:
            m = _DECL_RE.match(lines[lh - 1])
            if m and m.group(1) == "instance":
                seen_ln.add(lh)
                cand_lines.append(lh)
    for idx, ln in enumerate(lines, 1):
        if idx in seen_ln:
            continue
        m = _DECL_RE.match(ln)
        if m and m.group(1) == "instance":
            seen_ln.add(idx)
            cand_lines.append(idx)

    best_score = 0
    best_line: Optional[int] = None
    c_set = [s for s in carrier_stems if s]
    t_set = [s for s in type_stems if s and s not in c_set]

    for lno in cand_lines:
        c_try = _parse_contract_at_line(
            lines,
            rel_file,
            inst_name,
            lno,
            "instance",
            include_thm=False,
            preserve_lines=False,
            anchor_prefix=anchor_prefix,
            include_scope=False,
        )
        hdr_typ = c_try.type or c_try.header
        ids = identifiers(hdr_typ)
        id_tails = {tok.rsplit(".", 1)[-1] for tok in ids}
        if c_set and not any(cs in id_tails or cs in hdr_typ for cs in c_set):
            continue
        score = 0
        head_cls = (_head_ident(hdr_typ) or "").rsplit(".", 1)[-1]
        if head_cls and head_cls.lower() in inst_core_lo:
            score += 20 + len(head_cls)
        for ts in t_set:
            if ts.lower() in inst_core_lo and (ts in id_tails or ts in hdr_typ):
                score += 5 + len(ts)
        for tok in id_tails:
            if len(tok) >= 3 and tok.lower() in inst_core_lo and tok not in c_set:
                score += 3 + len(tok)
        if c_set and any(cs.lower() in inst_core_lo for cs in c_set):
            score += 4
        if score > best_score:
            best_score = score
            best_line = lno

    if best_line is not None and best_score >= 6:
        c_res = _parse_contract_at_line(
            lines,
            rel_file,
            inst_name,
            best_line,
            "instance",
            include_thm=include_thm,
            preserve_lines=preserve_lines,
            anchor_prefix=anchor_prefix,
            include_scope=include_scope,
        )
        c_res.parent_info = {
            "auto_instance": True,
            "elaborated_name": inst_name,
            "source_kind": "anonymous_instance",
        }
        return c_res

    # Fallback: `deriving Class1, Class2` line in the same file
    for idx, ln in enumerate(lines, 1):
        s = ln.strip()
        if s.startswith("deriving "):
            for tok in identifiers(s[9:]):
                t_last = tok.rsplit(".", 1)[-1]
                if len(t_last) >= 3 and t_last.lower() in inst_core_lo:
                    ns, vs = scope_at(lines, idx) if include_scope else (None, [])
                    return Contract(
                        name=inst_name,
                        keyword="instance",
                        file=rel_file,
                        line=idx,
                        header=f"instance {inst_last} ({s})",
                        namespace=ns,
                        variables=vs,
                        anchor_prefix=anchor_prefix,
                        parent_info={
                            "auto_instance": True,
                            "elaborated_name": inst_name,
                            "source_kind": "deriving",
                        },
                    )
    return None


def find_dead_in_src(
    src_root: str,
    query: str,
    include_thm: bool = False,
    preserve_lines: bool = False,
    limit: int = 20,
    anchor_prefix: Optional[str] = None,
    *,
    exact_case: bool = False,
) -> list[Contract]:
    """Scan `.lean` files under `src_root` for a declaration matching `query` by exact FQN,
    module-qualified `<Mod>.<Decl>`, or `.suffix` (exact-case preferred over case-insensitive)."""
    if not src_root or not os.path.isdir(src_root):
        return []
    q = query.strip()
    if not q:
        return []
    if q.startswith("_root_."):
        q = q[7:]
    stem = q.rsplit(".", 1)[-1]
    if not stem:
        return []
    if anchor_prefix is None:
        anchor_prefix = resolve_source_config(src_root)["anchor_prefix"]

    real_root = os.path.realpath(src_root)
    exact_hits: list[Contract] = []
    suffix_hits: list[Contract] = []
    ci_hits: list[Contract] = []
    stem_lo = stem.lower()
    q_lo = q.lower()

    for dirpath, dirnames, filenames in os.walk(real_root):
        dirnames[:] = sorted(d for d in dirnames if d not in (".git", ".lake", "build", "outputs"))
        filenames.sort()
        for fn in filenames:
            if not fn.endswith(".lean"):
                continue
            full_path = os.path.join(dirpath, fn)
            try:
                with open(full_path, encoding="utf-8", errors="replace") as f:
                    raw_text = f.read()
            except OSError:
                continue
            if stem_lo not in raw_text.lower():
                continue
            rel_file = os.path.relpath(full_path, real_root).replace(os.sep, "/")
            mod_name = rel_file[:-5].replace("/", ".")
            lines = _file_lines(full_path)
            for idx, ln in enumerate(lines):
                m = _DECL_RE.match(ln)
                if not m or not m.group(2):
                    continue
                raw_decl = m.group(2).rstrip(":")
                raw_last = raw_decl.rsplit(".", 1)[-1]
                if raw_last.lower() != stem_lo:
                    continue
                ns, _ = scope_at(lines, idx + 1)
                if raw_decl.startswith("_root_."):
                    fqn = raw_decl[7:]
                elif ns:
                    fqn = f"{ns}.{raw_decl}"
                else:
                    fqn = raw_decl

                matched_exact = fqn == q
                matched_mod = False
                if not matched_exact and "." in q:
                    parts = q.split(".")
                    for split_idx in range(len(parts) - 1, 0, -1):
                        mod_cand = ".".join(parts[:split_idx])
                        tail_cand = ".".join(parts[split_idx:])
                        if fqn == tail_cand and (mod_name == mod_cand or mod_name.endswith("." + mod_cand)):
                            matched_mod = True
                            break
                matched_suffix = (not matched_exact and not matched_mod) and fqn.endswith("." + q)
                matched_ci = (
                    not exact_case
                    and not matched_exact
                    and not matched_mod
                    and not matched_suffix
                    and (fqn.lower() == q_lo or fqn.lower().endswith("." + q_lo))
                )
                if not (matched_exact or matched_mod or matched_suffix or matched_ci):
                    continue
                c = read_contract(
                    src_root,
                    rel_file,
                    fqn,
                    hint=idx + 1,
                    include_thm=include_thm,
                    preserve_lines=preserve_lines,
                    anchor_prefix=anchor_prefix,
                )
                if c is not None:
                    if matched_exact or matched_mod:
                        exact_hits.append(c)
                    elif matched_suffix:
                        suffix_hits.append(c)
                    else:
                        ci_hits.append(c)
                if len(exact_hits) + len(suffix_hits) >= limit:
                    break
            if len(exact_hits) >= limit:
                break
    return (exact_hits or suffix_hits or ci_hits)[:limit]


def _proofish(v: str) -> bool:
    return bool(re.search(r"(^|[\s(⟨])by\b", v)) or v.lstrip().startswith(("fun _", "⟨", "rfl", "by"))


def identifiers(s: Optional[str]) -> set[str]:
    """Identifier tokens (dotted names) appearing in a header fragment."""
    if not s:
        return set()
    return {t.rstrip(".") for t in _IDENT_RE.findall(s)}


# ---- Body line slicing & regex search (`contract --body-lines` / `--grep` / `--fields-grep`) ----

_SLICE_RE = re.compile(r"^\s*([Ll+]?)(\d*)\s*:\s*([Ll+]?)(\d*)\s*$")
_BARE_INT_RE = re.compile(r"^\s*(\d+)\s*$")


def slice_body_lines(
    body_lines: Sequence[tuple[int, str]],
    spec: str,
    decl_line: int = 1,
) -> tuple[list[tuple[int, int, str]], str]:
    """Slice `body_lines` (`[(file_line, text), ...]`) by inclusive `A:B` (or bare `N` -> `1:N`).

    Addressing modes:
      * `1:30` / `+1:30` / `30` (default): 1-based body line offset (`1` = first line of body).
      * `L700:715` / `L700:L715`: explicit 1-based `.lean` file line numbers.
      * Auto file-line mode when neither `L` nor `+` is given and `A >= decl_line` with `A > len(body_lines)`.

    Returns `(rows, mode)` where each row is `(file_line, offset_1based, text)` and `mode` in `{'offset', 'file'}`.
    """
    m_bare = _BARE_INT_RE.match(spec or "")
    norm_spec = f"1:{m_bare.group(1)}" if m_bare else (spec or "")
    m = _SLICE_RE.match(norm_spec)
    if not m or (not m.group(2) and not m.group(4)):
        raise ValueError(f"invalid --body-lines {spec!r} (expected A:B or N, e.g. 1:30, 30, or L700:715)")
    p1, s1, p2, s2 = m.group(1), m.group(2), m.group(3), m.group(4)
    a = int(s1) if s1 else None
    b = int(s2) if s2 else None
    if a is not None and a < 1:
        raise ValueError(f"invalid --body-lines {spec!r}: start line must be >= 1")
    if b is not None and b < 1:
        raise ValueError(f"invalid --body-lines {spec!r}: end line must be >= 1")
    if a is not None and b is not None and a > b:
        raise ValueError(f"invalid --body-lines {spec!r}: start {a} > end {b}")

    n = len(body_lines)
    if n == 0:
        return [], "file" if (p1.upper() == "L" or p2.upper() == "L") else "offset"

    force_file = p1.upper() == "L" or p2.upper() == "L"
    force_off = p1 == "+" or p2 == "+"
    auto_file = (
        not force_file
        and not force_off
        and a is not None
        and a >= decl_line
        and a > n
    )
    mode = "file" if (force_file or auto_file) else "offset"
    if mode == "file":
        lo = a if a is not None else body_lines[0][0]
        hi = b if b is not None else body_lines[-1][0]
        return [
            (fl, idx, txt)
            for idx, (fl, txt) in enumerate(body_lines, 1)
            if lo <= fl <= hi
        ], mode
    lo = a if a is not None else 1
    hi = b if b is not None else n
    return [
        (fl, idx, txt)
        for idx, (fl, txt) in enumerate(body_lines, 1)
        if lo <= idx <= hi
    ], mode


def grep_body_lines(
    body_lines: Sequence[tuple[int, str]],
    pattern: str,
    context: int = 0,
) -> list[list[tuple[int, int, str, bool]]]:
    """Search `body_lines` for regex `pattern` with `context` surrounding lines.

    Returns merged hunks: `[[(file_line, offset_1based, text, is_match), ...], ...]`.
    """
    if context < 0:
        raise ValueError(f"invalid --context {context}: must be >= 0")
    try:
        rx = re.compile(pattern)
    except re.error as e:
        raise ValueError(f"invalid --grep regex {pattern!r}: {e}") from e

    n = len(body_lines)
    hit_idxs = [i for i, (_, txt) in enumerate(body_lines) if rx.search(txt)]
    if not hit_idxs:
        return []
    hit_set = set(hit_idxs)
    spans: list[list[int]] = []
    for idx in hit_idxs:
        lo = max(0, idx - context)
        hi = min(n - 1, idx + context)
        if spans and lo <= spans[-1][1] + 1:
            spans[-1][1] = max(spans[-1][1], hi)
        else:
            spans.append([lo, hi])

    hunks: list[list[tuple[int, int, str, bool]]] = []
    for lo, hi in spans:
        hunk = [
            (body_lines[j][0], j + 1, body_lines[j][1], j in hit_set)
            for j in range(lo, hi + 1)
        ]
        hunks.append(hunk)
    return hunks


def grep_fields(
    fields: Sequence[Field],
    pattern: str,
    context: int = 0,
) -> list[list[tuple[Field, int, bool]]]:
    """Search `structure`/`class`/`inductive` `fields` for regex `pattern` with `context` surrounding fields.

    Returns merged hunks: `[[(Field, index_1based, is_match), ...], ...]`.
    """
    if context < 0:
        raise ValueError(f"invalid --context {context}: must be >= 0")
    try:
        rx = re.compile(pattern)
    except re.error as e:
        raise ValueError(f"invalid field grep regex {pattern!r}: {e}") from e

    n = len(fields)
    if n == 0:
        return []
    hit_idxs = [
        i
        for i, f in enumerate(fields)
        if rx.search(f".{f.name} : {' '.join(f.type.split())}") or rx.search(f"{f.name} : {' '.join(f.type.split())}")
    ]
    if not hit_idxs:
        return []
    hit_set = set(hit_idxs)
    spans: list[list[int]] = []
    for idx in hit_idxs:
        lo = max(0, idx - context)
        hi = min(n - 1, idx + context)
        if spans and lo <= spans[-1][1] + 1:
            spans[-1][1] = max(spans[-1][1], hi)
        else:
            spans.append([lo, hi])
    return [
        [(fields[j], j + 1, j in hit_set) for j in range(lo, hi + 1)]
        for lo, hi in spans
    ]


# ---- Codomain producer analysis & `horn --have-wiring` ----

def _strip_outer_parens(s: str) -> str:
    s = s.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0
        ok = True
        for i, c in enumerate(s):
            if c in _OPEN:
                depth += 1
            elif c in _CLOSE:
                depth -= 1
                if depth == 0 and i < len(s) - 1:
                    ok = False
                    break
        if ok and depth == 0:
            s = s[1:-1].strip()
        else:
            break
    return s


def _arrow_split_depth0(t: str) -> list[str]:
    out, depth, cur = [], 0, []
    i, n = 0, len(t)
    while i < n:
        ch = t[i]
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth = max(0, depth - 1)
        if depth == 0 and ch == "→":
            out.append("".join(cur)); cur = []; i += 1; continue
        if depth == 0 and t.startswith("->", i):
            out.append("".join(cur)); cur = []; i += 2; continue
        cur.append(ch)
        i += 1
    out.append("".join(cur))
    return [x.strip() for x in out if x.strip()]


def _split_top_binop(t: str, ops: tuple[str, ...]) -> list[str]:
    out, depth, cur = [], 0, []
    i, n = 0, len(t)
    while i < n:
        ch = t[i]
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth = max(0, depth - 1)
        if depth == 0:
            matched_op = None
            for op in ops:
                if t.startswith(op, i):
                    matched_op = op
                    break
            if matched_op is not None:
                out.append("".join(cur).strip())
                cur = []
                i += len(matched_op)
                continue
        cur.append(ch)
        i += 1
    out.append("".join(cur).strip())
    return [x for x in out if x]


def _has_depth0_rel_op(s: str) -> bool:
    """True if `s` has a top-level binary relation (`=`, `≠`, `<`, `≤`, `>`, `≥`, `∈`, `∉`, `⊆`, `⊂`)
    outside any `fun ... =>` / `λ ... ,` binder."""
    depth = 0
    i, n = 0, len(s)
    while i < n:
        ch = s[i]
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0:
            if (
                s.startswith("fun", i)
                and (i == 0 or not s[i - 1].isalnum())
                and (i + 3 < n and s[i + 3].isspace())
            ) or (ch == "λ" and (i == 0 or not s[i - 1].isalnum())):
                break
            if ch in ("≠", "≤", "≥", "∈", "∉", "⊆", "⊂"):
                return True
            if ch == "=" and not s.startswith(("=>", "=="), i) and (i == 0 or s[i - 1] not in ":!<>=~"):
                return True
            if ch == "<" and not s.startswith(("<-", "<=", "<->"), i):
                return True
            if ch == ">" and (i == 0 or s[i - 1] not in "-="):
                return True
        i += 1
    return False


def _head_ident(expr: str) -> Optional[str]:
    s = _strip_outer_parens(expr).lstrip("@")
    if not s or _has_depth0_rel_op(s):
        return None
    m = _IDENT_RE.match(s)
    if m:
        return m.group(0).rstrip(".")
    # Dot-notation on a bracketed receiver, e.g. `(M.data N CH etaB eB ηv ev).DIV C`
    if s[0] in _OPEN:
        depth = 0
        i, n = 0, len(s)
        while i < n:
            if s[i] in _OPEN:
                depth += 1
            elif s[i] in _CLOSE:
                depth -= 1
                if depth == 0:
                    rest = s[i + 1:]
                    if rest.startswith("."):
                        m_dot = _IDENT_RE.match(rest[1:])
                        if m_dot:
                            return "." + m_dot.group(0).rstrip(".")
                    break
            i += 1
    return None


def _matches_target_ident(ident: Optional[str], target_name: str) -> bool:
    if not ident:
        return False
    tgt = target_name.removeprefix("_root_.")
    stem = tgt.rsplit(".", 1)[-1]
    if ident.startswith("."):
        dot_tail = ident[1:]
        return dot_tail == stem or dot_tail.endswith("." + stem) or tgt.endswith("." + dot_tail)
    clean = ident.removeprefix("_root_.")
    if clean == tgt or clean == stem or tgt.endswith("." + clean):
        return True
    # Dot-notation on a receiver variable / projection chain (`d.DIV C`, `M.toData.DIV C`)
    if "." in tgt and clean.endswith("." + stem):
        return True
    return False


def _extract_binder_types(binder_blob: str) -> list[str]:
    """Extract type annotations inside existential binders like `(x : Foo D) (y : Bar)` or `x : Foo D`."""
    types: list[str] = []
    b = binder_blob.strip()
    if not b:
        return types
    j0 = _depth0_find(b, ":")
    if j0 >= 0:
        types.append(b[j0 + 1:].strip())
        return types
    depth, start = 0, None
    for i, c in enumerate(b):
        if c in "([{⦃":
            if depth == 0:
                start = i + 1
            depth += 1
        elif c in ")]}⦄":
            depth = max(0, depth - 1)
            if depth == 0 and start is not None:
                inner = b[start:i]
                k = _depth0_find(inner, ":")
                if k >= 0:
                    types.append(inner[k + 1:].strip())
                start = None
    return types


def classify_codomain_producer(typ: Optional[str], target_name: str) -> Optional[str]:
    """Return producer role (`'direct'`, `'exists'`, `'exists_witness'`, `'conjunct'`,
    `'nonempty'`, `'wrapped'`, `'iff'`) if `typ` produces `target_name` in its codomain,
    or `None` if `target_name` only appears in hypotheses/premises/arguments."""
    if not typ:
        return None

    def _check(expr: str, role_hint: str = "direct") -> Optional[str]:
        s = _strip_outer_parens(expr)
        if not s:
            return None
        # 1. Strip depth-0 `→` premises and `∀` universal binders iteratively.
        changed = True
        while changed:
            changed = False
            segs = _arrow_split_depth0(s)
            if len(segs) > 1:
                s = _strip_outer_parens(segs[-1])
                changed = True
            if s.startswith("∀") or re.match(r"^forall\b", s):
                comma = _depth0_find(s, ",")
                if comma >= 0:
                    s = _strip_outer_parens(s[comma + 1:])
                    changed = True

        # 2. Existential / Sigma (`∃ ..., body` or `Σ ..., body`): witness types + body are positive outputs!
        if s.startswith(("∃", "Σ")) or re.match(r"^(?:Exists|Sigma|PSigma)\b", s):
            if s.startswith(("∃", "Σ")):
                comma = _depth0_find(s, ",")
                if comma >= 0:
                    b_blob = s[1:comma]
                    for bt in _extract_binder_types(b_blob):
                        if _check(bt, "exists_witness") is not None:
                            return "exists_witness"
                    return _check(s[comma + 1:], "exists" if role_hint == "direct" else role_hint)

        # 3. Conjunction / Product (`∧`, `×`)
        conj_parts = _split_top_binop(s, ("∧", "×"))
        if len(conj_parts) > 1:
            for part in conj_parts:
                hit = _check(part, "conjunct")
                if hit is not None:
                    return "conjunct" if hit == "direct" else hit
            return None

        # 4. Equivalence (`↔`)
        iff_parts = _split_top_binop(s, ("↔",))
        if len(iff_parts) > 1:
            for part in iff_parts:
                if _check(part, "iff") is not None:
                    return "iff"
            return None

        # 5. Direct head identifier check
        head = _head_ident(s)
        if _matches_target_ident(head, target_name):
            return role_hint

        # 6. `Nonempty (...)` / `Inhabited (...)` wrapper around a Type/structure
        if head in ("Nonempty", "Inhabited"):
            rest = s[len(head):].strip()
            if _check(rest, "nonempty") is not None:
                return "nonempty"

        # 7. Trailing lambda wrapper (e.g. `Closed 𝒞 fun Fm _ => LinkG Fm`)
        m_fun = re.search(r"\bfun\b[^=]*=>\s*(.+)$", s)
        if m_fun:
            if _check(m_fun.group(1), "wrapped") is not None:
                return "wrapped"
        m_lam = re.search(r"λ\b[^,]*,\s*(.+)$", s)
        if m_lam:
            if _check(m_lam.group(1), "wrapped") is not None:
                return "wrapped"
        return None

    return _check(typ, "direct")


# ---- `horn --have-wiring` tactic/term step extractor ----

_HAVE_LET_RE = re.compile(r"^(have|let)\s+(.*)$")
_OBTAIN_RE = re.compile(r"^(?:obtain|rcases)\s+(.+?)\s*(?::=|with)\s*(.+)$")
_INTRO_RE = re.compile(r"^(?:intro|rintro)\s+(.+)$")
_EXACT_RE = re.compile(r"^(exact|refine'?|apply)\s+(.+)$")
_LEAN_STOPWORDS = {
    "by", "fun", "let", "have", "in", "show", "from", "match", "with", "if", "then", "else",
    "do", "return", "where", "forall", "exists", "Prop", "Type", "Sort", "true", "false",
    "True", "False", "rfl", "le_rfl", "trivial", "linarith", "omega", "positivity", "simp",
    "ring", "norm_num", "aesop", "exact", "refine", "apply", "intro", "obtain", "rcases",
}


def _parse_binder_names(binders: Sequence[str]) -> list[dict[str, str]]:
    out: list[dict[str, str]] = []
    for b in binders:
        s = b.strip()
        if len(s) >= 2 and s[0] in "([{⦃" and s[-1] in ")]}⦄":
            inner = s[1:-1].strip()
        else:
            inner = s
        j = _depth0_find(inner, ":")
        if j < 0:
            continue
        names_part, typ_part = inner[:j].strip(), " ".join(inner[j + 1:].split())
        for nm in names_part.split():
            nm_clean = nm.strip()
            if nm_clean and nm_clean != "_" and _IDENT_RE.fullmatch(nm_clean):
                out.append({"name": nm_clean, "type": typ_part})
    return out


def _group_tactic_blocks(body_lines: Sequence[tuple[int, str]]) -> list[tuple[int, str]]:
    """Group multi-line tactic statements by indentation so multi-line `have` / `exact` stay intact."""
    cleaned = [(ln, txt) for ln, txt in body_lines if txt.strip()]
    if not cleaned:
        return []
    start_idx = 0
    first_s = cleaned[0][1].strip()
    if first_s == "by":
        start_idx = 1
    elif first_s.startswith("by "):
        cleaned = [(cleaned[0][0], first_s[3:]), *cleaned[1:]]

    blocks: list[tuple[int, list[str], int]] = []
    base_ind: Optional[int] = None
    for ln, raw in cleaned[start_idx:]:
        s = raw.strip()
        if not s:
            continue
        ind = len(raw) - len(raw.lstrip())
        if base_ind is None:
            base_ind = ind
        starts_new = ind <= base_ind or (
            blocks
            and ind <= blocks[-1][2]
            and re.match(
                r"^(?:have|let|obtain|rcases|intro|rintro|exact|exact_mod_cast|refine'?|apply|suffices|calc|"
                r"rw|rwa|simp|dsimp|unfold|set|choose|cases|by_cases|linarith|nlinarith|omega|positivity|ring|norm_num|·)\b",
                s,
            )
            and not blocks[-1][1][-1].rstrip().endswith((":=", "=>", ",", "←"))
        )
        if not blocks or starts_new:
            blocks.append((ln, [s], ind))
        else:
            blocks[-1][1].append(s)
    return [(ln, " ".join(parts)) for ln, parts, _ in blocks]


def _resolve_short(ident: Optional[str], mapping: Optional[dict[str, str]]) -> Optional[str]:
    if not ident:
        return None
    clean = ident.removeprefix("_root_.")
    if not mapping:
        return clean
    if clean in mapping:
        return mapping[clean]
    last = clean.rsplit(".", 1)[-1]
    return mapping.get(last, clean)


def _rhs_primary_head(rhs: str) -> Optional[str]:
    s = rhs.strip()
    s = re.sub(r"^by\s+(?:exact|apply|refine'?)\s+", "", s)
    if s.startswith("by ") or s == "by":
        m_tac = re.match(r"^by\s+([A-Za-z_][\w']*)", s)
        return f"by {m_tac.group(1)}" if m_tac else "by <tactic>"
    s = _strip_outer_parens(s).lstrip("@")
    m = _IDENT_RE.match(s)
    return m.group(0).rstrip(".") if m else None


_SCALAR_BINDER_TYPES = {"ℝ", "ℕ", "ℤ", "ℚ", "ℂ", "Nat", "Int", "Rat", "Real", "Complex", "Bool", "Type", "Type*", "Prop"}


def _is_scalar_param_type(typ: str) -> bool:
    s = typ.strip()
    return s in _SCALAR_BINDER_TYPES or bool(re.fullmatch(r"(?:Type|Sort)\s*\S*", s))


def extract_have_wiring(
    contract: Contract,
    *,
    known_lemmas: Optional[dict[str, str]] = None,
    known_types: Optional[dict[str, str]] = None,
) -> dict[str, Any]:
    """Extract hypothesis binders, `intro`/`obtain` bindings, `have`/`let` steps, and terminal
    `exact`/`refine` wiring from `contract.body_lines`."""
    binder_list = _parse_binder_names(contract.binders)
    hyp_types: dict[str, Optional[str]] = {b["name"]: b["type"] for b in binder_list}
    hyp_roots: dict[str, list[str]] = {
        b["name"]: [b["name"]]
        for b in binder_list
        if not _is_scalar_param_type(b["type"])
    }

    arrow_segs = _arrow_split_depth0(contract.type or "")
    arrow_premises = arrow_segs[:-1] if len(arrow_segs) > 1 else []
    premise_cursor = 0

    intros: list[dict[str, Any]] = []
    destructured: list[dict[str, Any]] = []
    steps: list[dict[str, Any]] = []
    step_roots: dict[str, set[str]] = {}
    terminal: Optional[dict[str, Any]] = None

    blocks = _group_tactic_blocks(contract.body_lines)
    for ln, stmt in blocks:
        m_in = _INTRO_RE.match(stmt)
        if m_in:
            toks = [t for t in re.findall(r"[A-Za-z_][\w']*", m_in.group(1)) if t != "_"]
            for tok in toks:
                ptyp = arrow_premises[premise_cursor] if premise_cursor < len(arrow_premises) else None
                premise_cursor += 1
                hyp_types.setdefault(tok, ptyp)
                hyp_roots.setdefault(tok, [tok])
                intros.append({"line": ln, "name": tok, "type": one_line(ptyp, 180)})
            continue

        m_ob = _OBTAIN_RE.match(stmt)
        if m_ob:
            pat, src_expr = m_ob.group(1).strip(), m_ob.group(2).strip()
            vars_out = [
                v for v in re.findall(r"[A-Za-z_][\w']*", pat)
                if v != "_" and v not in _LEAN_STOPWORDS
            ]
            src_ids = identifiers(src_expr)
            roots: set[str] = set()
            for sid in src_ids:
                base = sid.split(".", 1)[0]
                if base in hyp_roots:
                    roots.update(hyp_roots[base])
                elif base in step_roots:
                    roots.update(step_roots[base])
            src_head = _head_ident(src_expr) or src_expr
            for v in vars_out:
                tag_roots = sorted(f"{r}.{v}" if r == src_head else r for r in roots) or [v]
                hyp_roots[v] = tag_roots
                hyp_types.setdefault(v, f"from {src_head}")
            destructured.append({
                "line": ln,
                "pattern": one_line(pat, 120),
                "vars": vars_out,
                "from": one_line(src_expr, 120),
                "root_hyps": sorted(roots),
            })
            continue

        m_hv = _HAVE_LET_RE.match(stmt)
        if m_hv:
            kw, rest = m_hv.group(1), m_hv.group(2).strip()
            eq_pos = _depth0_find_assign(rest)
            if eq_pos < 0:
                continue
            lhs, rhs = rest[:eq_pos].strip(), rest[eq_pos + 2:].strip()
            colon_pos = _depth0_find(lhs, ":")
            if colon_pos >= 0:
                raw_name = lhs[:colon_pos].strip()
                step_type: Optional[str] = " ".join(lhs[colon_pos + 1:].split())
            else:
                raw_name = lhs
                step_type = None

            bound_vars = [
                v for v in re.findall(r"[A-Za-z_][\w']*", raw_name.split()[0] if raw_name and raw_name[0] not in "⟨(" else raw_name)
                if v != "_" and v not in _LEAN_STOPWORDS
            ]
            step_name = bound_vars[0] if len(bound_vars) == 1 else (raw_name if len(raw_name) <= 40 else (bound_vars[0] if bound_vars else "_"))

            rhs_ids = identifiers(rhs)
            used_steps = sorted(s_nm for s_nm in step_roots if _token_in_ids(s_nm, rhs_ids))
            used_hyps = sorted(h_nm for h_nm in hyp_roots if _token_in_ids(h_nm, rhs_ids))

            t_roots: set[str] = set()
            for h_nm in used_hyps:
                t_roots.update(hyp_roots[h_nm])
            for s_nm in used_steps:
                t_roots.update(step_roots[s_nm])

            for bv in (bound_vars or [step_name]):
                step_roots[bv] = set(t_roots)

            t_head_raw = _head_ident(step_type) if step_type else None
            t_head = _resolve_short(t_head_raw, known_types)
            via_raw = _rhs_primary_head(rhs)
            via = _resolve_short(via_raw, known_lemmas) if via_raw and not via_raw.startswith("by ") else via_raw
            lemmas_hit = _match_known_lemmas(rhs_ids, known_lemmas)

            steps.append({
                "line": ln,
                "kind": kw,
                "name": step_name,
                "type": one_line(step_type, 200),
                "type_head": t_head,
                "via": via,
                "lemmas": lemmas_hit,
                "uses_steps": used_steps,
                "uses_hyps": used_hyps,
                "root_hyps": sorted(t_roots),
            })
            continue

        m_ex = _EXACT_RE.match(stmt)
        if m_ex:
            tac, rhs = m_ex.group(1), m_ex.group(2).strip()
            rhs_ids = identifiers(rhs)
            used_steps = sorted(s_nm for s_nm in step_roots if _token_in_ids(s_nm, rhs_ids))
            used_hyps = sorted(h_nm for h_nm in hyp_roots if _token_in_ids(h_nm, rhs_ids))
            t_roots = set()
            for h_nm in used_hyps:
                t_roots.update(hyp_roots[h_nm])
            for s_nm in used_steps:
                t_roots.update(step_roots[s_nm])
            via_raw = _rhs_primary_head(rhs)
            terminal = {
                "line": ln,
                "tactic": tac,
                "via": _resolve_short(via_raw, known_lemmas),
                "lemmas": _match_known_lemmas(rhs_ids, known_lemmas),
                "uses_steps": used_steps,
                "uses_hyps": used_hyps,
                "root_hyps": sorted(t_roots),
            }
            terminal_rhs = (ln, rhs)

    # Extract term-mode / direct-application / record-literal / `where`-field wiring
    all_local_vars: set[str] = {b["name"] for b in binder_list} | {i["name"] for i in intros} | set(hyp_roots) | set(step_roots)
    term_wiring: Optional[dict[str, Any]] = None

    if contract.body_kind == "where" and contract.body_lines:
        term_wiring = _extract_where_field_wiring(
            contract,
            hyp_roots=hyp_roots,
            step_roots=step_roots,
            known_lemmas=known_lemmas,
            known_types=known_types,
        )
    elif "terminal_rhs" in locals():
        t_ln, t_rhs = terminal_rhs
        term_wiring = _extract_expr_wiring(
            t_rhs,
            line_no=t_ln,
            contract_type=contract.type,
            all_locals=all_local_vars,
            hyp_roots=hyp_roots,
            step_roots=step_roots,
            known_lemmas=known_lemmas,
            known_types=known_types,
        )
    elif terminal is None and not steps and not destructured and contract.body_lines:
        first_txt = contract.body_lines[0][1].strip()
        if not (first_txt == "by" or first_txt.startswith("by ")):
            raw_term = " ".join(txt.strip() for _, txt in contract.body_lines if txt.strip())
            t_ln = contract.body_lines[0][0]
            lam_vars, inner_term = _strip_leading_lambdas(raw_term)
            for lv in lam_vars:
                ptyp = arrow_premises[premise_cursor] if premise_cursor < len(arrow_premises) else None
                premise_cursor += 1
                hyp_types.setdefault(lv, ptyp)
                hyp_roots.setdefault(lv, [lv])
                all_local_vars.add(lv)
                intros.append({"line": t_ln, "name": lv, "type": one_line(ptyp, 180)})
            term_wiring = _extract_expr_wiring(
                inner_term,
                line_no=t_ln,
                contract_type=contract.type,
                all_locals=all_local_vars,
                hyp_roots=hyp_roots,
                step_roots=step_roots,
                known_lemmas=known_lemmas,
                known_types=known_types,
            )
            if term_wiring is not None:
                rhs_ids = identifiers(inner_term)
                used_steps = sorted(s_nm for s_nm in step_roots if _token_in_ids(s_nm, rhs_ids))
                used_hyps = sorted(h_nm for h_nm in hyp_roots if _token_in_ids(h_nm, rhs_ids))
                t_roots = set()
                for h_nm in used_hyps:
                    t_roots.update(hyp_roots[h_nm])
                for s_nm in used_steps:
                    t_roots.update(step_roots[s_nm])
                via_raw = _rhs_primary_head(inner_term)
                terminal = {
                    "line": t_ln,
                    "tactic": "term",
                    "via": term_wiring.get("callee") or _resolve_short(via_raw, known_lemmas),
                    "lemmas": _match_known_lemmas(rhs_ids, known_lemmas),
                    "uses_steps": used_steps,
                    "uses_hyps": used_hyps,
                    "root_hyps": sorted(t_roots),
                }

    out_hw: dict[str, Any] = {
        "binders": binder_list,
        "intros": intros,
        "destructured": destructured,
        "steps": steps,
        "terminal": terminal,
    }
    if term_wiring is not None:
        out_hw["term_wiring"] = term_wiring
    return out_hw


def _strip_leading_lambdas(expr: str) -> tuple[list[str], str]:
    """Unwrap leading `fun x y => body` / `λ x y, body` in term-mode proofs."""
    s = expr.strip()
    vars_bound: list[str] = []
    while True:
        if s.startswith("fun") and len(s) > 3 and s[3].isspace():
            depth = 0
            arrow_pos = -1
            for i in range(3, len(s) - 1):
                if s[i] in _OPEN:
                    depth += 1
                elif s[i] in _CLOSE:
                    depth = max(0, depth - 1)
                elif depth == 0 and (s.startswith("=>", i) or s[i] == "↦"):
                    arrow_pos = i
                    break
            if arrow_pos < 0:
                break
            b_part = s[3:arrow_pos].strip()
            step_len = 2 if s.startswith("=>", arrow_pos) else 1
            for tok in re.findall(r"[A-Za-z_][\w']*", b_part):
                if tok != "_" and tok not in _LEAN_STOPWORDS:
                    vars_bound.append(tok)
            s = s[arrow_pos + step_len:].strip()
            continue
        if s.startswith("λ") and len(s) > 1:
            comma_pos = _depth0_find(s, ",")
            if comma_pos < 0:
                break
            b_part = s[1:comma_pos].strip()
            for tok in re.findall(r"[A-Za-z_][\w']*", b_part):
                if tok != "_" and tok not in _LEAN_STOPWORDS:
                    vars_bound.append(tok)
            s = s[comma_pos + 1:].strip()
            continue
        break
    return vars_bound, s


def _split_app_spine(expr: str) -> list[str]:
    """Split a depth-0 Lean 4 application `f a1 (a2 x) {named := v} (r).s` into spine tokens."""
    s = _strip_outer_parens(expr.strip())
    tokens: list[str] = []
    cur: list[str] = []
    depth = 0
    in_str = False
    i, n = 0, len(s)
    while i < n:
        ch = s[i]
        if ch == '"' and (i == 0 or s[i - 1] != "\\"):
            in_str = not in_str
            cur.append(ch)
            i += 1
            continue
        if in_str:
            cur.append(ch)
            i += 1
            continue
        if ch in _OPEN:
            if depth == 0 and cur:
                tokens.append("".join(cur))
                cur = []
            depth += 1
            cur.append(ch)
            i += 1
            continue
        if ch in _CLOSE:
            depth = max(0, depth - 1)
            cur.append(ch)
            if depth == 0:
                # Attach immediate `.field` / `.1` projection chains to the closed group!
                while i + 1 < n and s[i + 1] == ".":
                    j = i + 2
                    while j < n and (s[j].isalnum() or s[j] in "_'₀₁₂₃₄₅₆₇₈₉"):
                        j += 1
                    if j > i + 2:
                        cur.append(s[i + 1:j])
                        i = j - 1
                    else:
                        break
                tokens.append("".join(cur))
                cur = []
            i += 1
            continue
        if depth == 0 and ch.isspace():
            if cur:
                tokens.append("".join(cur))
                cur = []
            i += 1
            continue
        cur.append(ch)
        i += 1
    if cur:
        tokens.append("".join(cur))
    return [t for t in tokens if t]


def _classify_arg_token(
    tok: str,
    *,
    all_locals: set[str],
    hyp_roots: dict[str, list[str]],
    step_roots: dict[str, set[str]],
    known_lemmas: Optional[dict[str, str]],
) -> dict[str, Any]:
    raw = tok.strip()
    named: Optional[str] = None
    val = raw
    if len(raw) >= 4 and ((raw[0] == "(" and raw[-1] == ")") or (raw[0] == "{" and raw[-1] == "}")):
        inner = raw[1:-1].strip()
        eq_p = _depth0_find_assign(inner)
        if eq_p > 0:
            cand_nm = inner[:eq_p].strip()
            if _IDENT_RE.fullmatch(cand_nm):
                named = cand_nm
                val = inner[eq_p + 2:].strip()

    unwrapped = _strip_outer_parens(val)
    ids = identifiers(unwrapped)
    used_steps = sorted(s_nm for s_nm in step_roots if _token_in_ids(s_nm, ids))
    used_hyps = sorted(h_nm for h_nm in hyp_roots if _token_in_ids(h_nm, ids))
    roots: set[str] = set()
    for h_nm in used_hyps:
        roots.update(hyp_roots[h_nm])
    for s_nm in used_steps:
        roots.update(step_roots[s_nm])
    if not roots:
        for lid in all_locals:
            if _token_in_ids(lid, ids):
                roots.add(lid)

    via_raw = _rhs_primary_head(unwrapped)
    via_resolved = _resolve_short(via_raw, known_lemmas) if (via_raw and not via_raw.startswith("by ")) else via_raw

    if unwrapped in ("_", "?_") or unwrapped.startswith("?_"):
        akind = "hole"
    elif unwrapped in ("rfl", "Eq.refl", "HEq.rfl"):
        akind = "rfl"
    elif unwrapped == "by" or unwrapped.startswith("by "):
        akind = "tactic"
    elif unwrapped in all_locals or unwrapped in step_roots:
        akind = "step" if unwrapped in step_roots else "passthrough"
        via_resolved = None
    elif re.match(r"^\(.+\)\.[A-Za-z0-9_']+$", val) or (
        "." in unwrapped and unwrapped.split(".", 1)[0] in all_locals
    ):
        akind = "projection"
    elif via_raw and via_raw not in _LEAN_STOPWORDS and (" " in unwrapped or via_raw != unwrapped or via_resolved != via_raw):
        akind = "call"
    else:
        akind = "term"

    out: dict[str, Any] = {
        "kind": akind,
        "expr": one_line(val, 200),
    }
    if named is not None:
        out["named"] = named
    if via_resolved and akind in ("call", "tactic", "projection"):
        out["via"] = via_resolved
    if used_steps:
        out["uses_steps"] = used_steps
    if roots:
        out["root_hyps"] = sorted(roots)
    return out


def _extract_where_field_wiring(
    contract: Contract,
    *,
    hyp_roots: dict[str, list[str]],
    step_roots: dict[str, set[str]],
    known_lemmas: Optional[dict[str, str]],
    known_types: Optional[dict[str, str]],
) -> Optional[dict[str, Any]]:
    blocks: list[tuple[int, list[str]]] = []
    base: Optional[int] = None
    for ln, raw in contract.body_lines:
        s = raw.strip()
        if not s:
            continue
        ind = len(raw) - len(raw.lstrip())
        if base is None:
            base = ind
        if ind <= base:
            blocks.append((ln, [s]))
        elif blocks:
            blocks[-1][1].append(s)

    fields_out: list[dict[str, Any]] = []
    for ln, parts in blocks:
        stmt = " ".join(parts)
        eq_pos = _depth0_find_assign(stmt)
        if eq_pos < 0:
            continue
        lhs = stmt[:eq_pos].strip()
        rhs = stmt[eq_pos + 2:].strip()
        fname = lhs.split()[0] if lhs else "_"
        rhs_ids = identifiers(rhs)
        used_steps = sorted(s_nm for s_nm in step_roots if _token_in_ids(s_nm, rhs_ids))
        used_hyps = sorted(h_nm for h_nm in hyp_roots if _token_in_ids(h_nm, rhs_ids))
        roots: set[str] = set()
        for h_nm in used_hyps:
            roots.update(hyp_roots[h_nm])
        for s_nm in used_steps:
            roots.update(step_roots[s_nm])
        via_raw = _rhs_primary_head(rhs)
        via = _resolve_short(via_raw, known_lemmas) if (via_raw and not via_raw.startswith("by ")) else via_raw
        fields_out.append({
            "field": fname,
            "line": ln,
            "expr": one_line(rhs, 200),
            "via": None if rhs in hyp_roots else via,
            "passthrough": rhs in hyp_roots,
            "uses_steps": used_steps,
            "root_hyps": sorted(roots),
        })
    if not fields_out:
        return None
    t_head = _resolve_short(_head_ident(contract.type) if contract.type else None, known_types)
    return {
        "mode": "where_fields",
        "line": contract.body_lines[0][0],
        "callee": t_head,
        "fields": fields_out,
    }


def _extract_expr_wiring(
    expr: str,
    *,
    line_no: int,
    contract_type: Optional[str],
    all_locals: set[str],
    hyp_roots: dict[str, list[str]],
    step_roots: dict[str, set[str]],
    known_lemmas: Optional[dict[str, str]],
    known_types: Optional[dict[str, str]],
) -> Optional[dict[str, Any]]:
    s = _strip_outer_parens(expr.strip())
    if not s:
        return None

    # 1. Record literal `{ f1 := v1, f2 := v2, ... }`
    if s.startswith("{") and s.endswith("}") and ":=" in s:
        inner = s[1:-1].strip()
        # Strip optional `..base,` spread or split top-level `,` / `;`
        raw_entries = [e.strip() for part in _depth0_split(inner, ";") for e in _depth0_split(part, ",") if e.strip()]
        fields_out: list[dict[str, Any]] = []
        for entry in raw_entries:
            eq_p = _depth0_find_assign(entry)
            if eq_p < 0:
                continue
            lhs = entry[:eq_p].strip()
            rhs = entry[eq_p + 2:].strip()
            fname = lhs.split()[0] if lhs else "_"
            info = _classify_arg_token(
                rhs,
                all_locals=all_locals,
                hyp_roots=hyp_roots,
                step_roots=step_roots,
                known_lemmas=known_lemmas,
            )
            fields_out.append({
                "field": fname,
                "expr": info["expr"],
                "kind": info["kind"],
                "via": info.get("via"),
                "root_hyps": info.get("root_hyps", []),
            })
        if fields_out:
            concl_segs = _arrow_split_depth0(contract_type or "")
            t_head = _resolve_short(_head_ident(concl_segs[-1]) if concl_segs else None, known_types)
            return {
                "mode": "record_literal",
                "line": line_no,
                "callee": t_head,
                "fields": fields_out,
            }

    # 2. Anonymous constructor `⟨e1, e2, ...⟩`
    if s.startswith("⟨") and s.endswith("⟩"):
        elems = [e.strip() for e in _depth0_split(s[1:-1], ",") if e.strip()]
        args_out = []
        for idx, el in enumerate(elems, 1):
            info = _classify_arg_token(
                el,
                all_locals=all_locals,
                hyp_roots=hyp_roots,
                step_roots=step_roots,
                known_lemmas=known_lemmas,
            )
            args_out.append({"index": idx, **info})
        concl_segs = _arrow_split_depth0(contract_type or "")
        t_head = _resolve_short(_head_ident(concl_segs[-1]) if concl_segs else None, known_types)
        return {
            "mode": "anon_ctor",
            "line": line_no,
            "callee": t_head,
            "args": args_out,
        }

    # 3. Direct application `callee arg1 arg2 ...`
    tokens = _split_app_spine(s)
    if not tokens:
        return None
    head_raw = tokens[0]
    explicit_at = head_raw.startswith("@")
    head_clean = head_raw.lstrip("@").removeprefix("_root_.")
    if len(tokens) == 1:
        # Bare trivial tactics/constants (`trivial`, `rfl`) or single local variable passthrough
        if head_clean in _LEAN_STOPWORDS or head_clean in all_locals or head_clean in step_roots:
            return None
    callee = _resolve_short(head_clean, known_lemmas) or _resolve_short(head_clean, known_types) or head_clean
    args_out = []
    pos_idx = 0
    for tok in tokens[1:]:
        info = _classify_arg_token(
            tok,
            all_locals=all_locals,
            hyp_roots=hyp_roots,
            step_roots=step_roots,
            known_lemmas=known_lemmas,
        )
        if "named" in info:
            args_out.append({"index": None, **info})
        else:
            pos_idx += 1
            args_out.append({"index": pos_idx, **info})
    return {
        "mode": "application",
        "line": line_no,
        "callee": callee,
        "explicit_at": explicit_at,
        "args": args_out,
    }


def _expand_forall_explicit_slots(blob: str, include_implicit: bool = False) -> list[dict[str, Optional[str]]]:
    """Expand `∀ 𝒮 𝒮' : Slots` or `∀ (n : ℕ) {k : ℕ} [Group G], ...` binder blob into positional slots."""
    s = blob.strip()
    if not s:
        return []
    j0 = _depth0_find(s, ":")
    if j0 >= 0 and not s.startswith(("(", "{", "[", "⦃")):
        names = [nm for nm in s[:j0].split() if nm]
        typ = " ".join(s[j0 + 1:].split())
        return [{"name": None if nm == "_" else nm, "type": typ} for nm in names]
    if not any(ch in s for ch in "([{⦃"):
        return [{"name": None if nm == "_" else nm, "type": None} for nm in s.split() if nm]

    slots: list[dict[str, Optional[str]]] = []
    depth = 0
    start: Optional[int] = None
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c in "([{⦃":
            if depth == 0:
                start = i
            depth += 1
        elif c in ")]}⦄":
            depth = max(0, depth - 1)
            if depth == 0 and start is not None:
                br_open = s[start]
                inner = s[start + 1:i].strip()
                if br_open == "(" or include_implicit:
                    k = _depth0_find(inner, ":")
                    if k >= 0:
                        names = [nm for nm in inner[:k].split() if nm]
                        typ = " ".join(inner[k + 1:].split())
                        for nm in (names or ["_"]):
                            slots.append({"name": None if nm == "_" else nm, "type": typ})
                    else:
                        slots.append({"name": None, "type": " ".join(inner.split())})
                start = None
        elif depth == 0 and not c.isspace():
            m = _IDENT_RE.match(s[i:])
            if m:
                nm = m.group(0)
                slots.append({"name": None if nm == "_" else nm, "type": None})
                i += len(nm)
                continue
        i += 1
    return slots


def explicit_callee_params(callee: Contract, explicit_all: bool = False) -> list[dict[str, Optional[str]]]:
    """Extract ordered positional parameter/premise slots from `callee.binders` + `callee.type`."""
    slots: list[dict[str, Optional[str]]] = []
    for b in callee.binders:
        bs = b.strip()
        if not bs:
            continue
        is_expl = bs.startswith("(")
        if not (is_expl or explicit_all):
            continue
        inner = bs[1:-1].strip() if (len(bs) >= 2 and bs[0] in "([{⦃" and bs[-1] in ")]}⦄") else bs
        k = _depth0_find(inner, ":")
        if k >= 0:
            names = [nm for nm in inner[:k].split() if nm]
            typ = " ".join(inner[k + 1:].split())
            for nm in (names or ["_"]):
                slots.append({"name": None if nm == "_" else nm, "type": typ})
        else:
            slots.append({"name": None, "type": " ".join(inner.split())})

    rem = _strip_outer_parens(callee.type or "")
    while rem:
        if rem.startswith("∀") or re.match(r"^forall\b", rem):
            kw_len = 1 if rem.startswith("∀") else 6
            comma = _depth0_find(rem, ",")
            if comma < 0:
                break
            slots.extend(_expand_forall_explicit_slots(rem[kw_len:comma], include_implicit=explicit_all))
            rem = _strip_outer_parens(rem[comma + 1:])
            continue
        segs = _arrow_split_depth0(rem)
        if len(segs) <= 1:
            break
        first_seg = segs[0].strip()
        if len(first_seg) >= 2 and first_seg[0] == "(" and first_seg[-1] == ")":
            inner = first_seg[1:-1].strip()
            k = _depth0_find(inner, ":")
            if k > 0 and all(_IDENT_RE.fullmatch(x) for x in inner[:k].split()):
                names = inner[:k].split()
                typ = " ".join(inner[k + 1:].split())
                for nm in names:
                    slots.append({"name": None if nm == "_" else nm, "type": typ})
            else:
                slots.append({"name": None, "type": " ".join(first_seg.split())})
        else:
            slots.append({"name": None, "type": " ".join(first_seg.split())})
        rem = " → ".join(segs[1:])
    return slots


def enrich_term_wiring_with_callee(term_wiring: dict[str, Any], callee: Contract) -> None:
    """Attach `param_name` and `param_type` from `callee` onto positional `term_wiring['args']`."""
    if term_wiring.get("mode") != "application":
        return
    explicit_all = bool(term_wiring.get("explicit_at"))
    params = explicit_callee_params(callee, explicit_all=explicit_all)
    if not params:
        return
    for arg in term_wiring.get("args") or ():
        idx = arg.get("index")
        if isinstance(idx, int) and 1 <= idx <= len(params):
            pslot = params[idx - 1]
            if pslot.get("name"):
                arg["param_name"] = pslot["name"]
            if pslot.get("type"):
                arg["param_type"] = one_line(pslot["type"], 140)


def _depth0_find_assign(s: str) -> int:
    depth = 0
    for i, c in enumerate(s):
        if c in _OPEN:
            depth += 1
        elif c in _CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and s.startswith(":=", i):
            return i
    return -1


def _token_in_ids(var_name: str, id_set: set[str]) -> bool:
    if var_name in id_set:
        return True
    pref = var_name + "."
    return any(tok.startswith(pref) for tok in id_set)


def _match_known_lemmas(rhs_ids: set[str], known_lemmas: Optional[dict[str, str]]) -> list[str]:
    if not known_lemmas:
        return []
    found: set[str] = set()
    for tok in rhs_ids:
        clean = tok.removeprefix("_root_.")
        if clean in known_lemmas:
            found.add(known_lemmas[clean])
            continue
        last = clean.rsplit(".", 1)[-1]
        if last in known_lemmas:
            found.add(known_lemmas[last])
    return sorted(found)
