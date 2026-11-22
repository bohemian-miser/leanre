#!/usr/bin/env python3
"""FLIRT Tier 2 -- source-level declaration signature extractor (no Lean toolchain needed).

Reads `.lean` text and yields one record per named declaration with its *effective
signature*: the `variable` binders Lean would auto-include, followed by the declaration's
own binders and result type. Proof bodies are never emitted (everything from the first
top-level `:=` / `where` / `|` on is dropped), so the output is body-independent by
construction.

This is a text approximation of elaboration, and it is deliberately the SAME code path for
the external corpora and for the proof mirror, so both sides are distorted identically.
Known, measured limits (see docs/FLIRT.md, Tier 2):
  * no name resolution: `open`/namespace-relative references are hashed as written;
  * `variable` inclusion is approximated by the Lean 4 rule "mentioned in the statement
    (theorems) or anywhere in the declaration (defs)", instance binders when every variable
    they mention is included;
  * `@[to_additive]`/`alias`/`macro`-generated declarations have no source header and are
    not extracted; `example`s and anonymous instances are skipped (nothing to key on).
"""
from __future__ import annotations

import os
import re
from typing import Dict, Iterator, List, Optional, Set, Tuple

OPEN_BR = "([{⦃⟨"
CLOSE_BR = ")]}⦄⟩"
_PAIR = dict(zip(OPEN_BR, CLOSE_BR))

DECL_KINDS = (
    "theorem", "lemma", "def", "abbrev", "instance", "structure", "class",
    "inductive", "opaque", "axiom",
)
_MODIFIERS = (
    "private", "protected", "noncomputable", "unsafe", "partial", "nonrec",
    "scoped", "local", "public", "meta", "@[expose]",
)
# Column-0 words that start a new command (and therefore end the previous declaration).
_COMMAND_WORDS = set(DECL_KINDS) | set(_MODIFIERS) | {
    "namespace", "section", "end", "variable", "universe", "open", "export", "import",
    "set_option", "attribute", "alias", "example", "omit", "include", "notation",
    "macro", "macro_rules", "syntax", "elab", "elab_rules", "infix", "infixl", "infixr",
    "prefix", "postfix", "mutual", "initialize", "deriving", "run_cmd", "assert_not_exists",
    "module", "suppress_compilation", "unsuppress_compilation", "irreducible_def",
    "add_decl_doc", "library_note", "theorem", "class", "declare_syntax_cat", "unseal",
    "seal", "compile_inductive", "builtin_initialize", "register_simp_attr",
}

_RE_WORD0 = re.compile(r"[A-Za-z_@#][\w#\[\]]*")
# Lean identifier (dotted). `\w` is unicode-aware (Greek, subscripts, ...).
RE_IDENT = re.compile(r"(?:«[^»]*»|[^\W\d][\w'!?]*)(?:\.(?:«[^»]*»|[^\W\d][\w'!?]*))*")
_RE_DECL_HEAD = re.compile(
    r"(" + "|".join(DECL_KINDS) + r")\b(?:\s+((?:«[^»]*»|[^\s:({\[⦃«]+)+))?"
)


def strip_comments(text: str) -> str:
    """Remove `--` line comments and nested `/- -/` blocks; keep newlines and strings."""
    if "--" not in text and "/-" not in text:
        return text
    out: List[str] = []
    i, n, depth, in_str = 0, len(text), 0, False
    while i < n:
        ch = text[i]
        if depth:
            if ch == "/" and text.startswith("/-", i):
                depth += 1
                i += 2
            elif ch == "-" and text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if ch == "\n":
                    out.append("\n")
                i += 1
        elif in_str:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if ch == '"':
                in_str = False
            i += 1
        elif ch == '"':
            in_str = True
            out.append(ch)
            i += 1
        elif ch == "/" and text.startswith("/-", i):
            depth = 1
            i += 2
        elif ch == "-" and text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                break
            i = j
        else:
            out.append(ch)
            i += 1
    return "".join(out)


_RE_LET_TAIL = re.compile(r":\s*(?:let|have|letI|haveI)\s+[^:;]*(?::[^:;]*)?$")


def _skip_attrs_mods(s: str) -> Tuple[str, List[str]]:
    """Strip leading `@[...]` attribute blocks and modifiers. Returns (rest, modifiers)."""
    mods: List[str] = []
    while True:
        s = s.lstrip()
        if s.startswith("@["):
            depth = 0
            for k, ch in enumerate(s):
                if ch == "[":
                    depth += 1
                elif ch == "]":
                    depth -= 1
                    if depth == 0:
                        s = s[k + 1:]
                        break
            else:
                return "", mods
            continue
        for m in _MODIFIERS:
            if s.startswith(m) and (len(s) == len(m) or s[len(m)].isspace()):
                mods.append(m)
                s = s[len(m):]
                break
        else:
            return s, mods


def split_header(text: str, ctor_pipe: bool = False) -> Tuple[str, str]:
    """Split declaration text (after the name) into (signature, body) at the first
    bracket-depth-0 `:=`, ` where`, or line-leading `|`."""
    depth = 0
    i, n = 0, len(text)
    in_str = False
    line_start = False
    while i < n:
        ch = text[i]
        if in_str:
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                in_str = False
        elif ch == '"':
            in_str = True
        elif ch in OPEN_BR:
            depth += 1
        elif ch in CLOSE_BR:
            depth = max(0, depth - 1)
        elif depth == 0:
            if ch == ":" and text.startswith(":=", i):
                head = text[:i].rstrip()
                if head.endswith(("letI", "haveI")) or _RE_LET_TAIL.search(head):
                    # `theorem t : letI := e; P` -- a `let` inside the statement; the
                    # statement cannot be cut reliably, so report "no type".
                    k = head.rfind(":")
                    return text[:k + 1] if k >= 0 else "", text[i + 2:]
                return text[:i], text[i + 2:]
            if ch == "|" and line_start:
                # match alternative (`| 0 => ...`) or constructor, not `|x|` notation
                eol = text.find("\n", i)
                seg = text[i:eol if eol >= 0 else n]
                if ctor_pipe or "=>" in seg:
                    return text[:i], text[i:]
            if ch == "w" and text.startswith("where", i) and (i == 0 or text[i - 1].isspace()) \
                    and (i + 5 == n or text[i + 5].isspace()):
                return text[:i], text[i + 5:]
        if ch == "\n":
            line_start = True
        elif not ch.isspace():
            line_start = False
        i += 1
    return text, ""


def split_binders(sig: str) -> Tuple[List[str], str]:
    """Split a signature into (leading top-level binder groups, result type text).
    The result type is whatever follows the first depth-0 `:` ('' when absent)."""
    groups: List[str] = []
    i, n = 0, len(sig)
    while i < n:
        ch = sig[i]
        if ch.isspace():
            i += 1
            continue
        if ch in "([{⦃":
            close = _PAIR[ch]
            depth = 0
            j = i
            while j < n:
                c = sig[j]
                if c in OPEN_BR:
                    depth += 1
                elif c in CLOSE_BR:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if j >= n or sig[j] != close:
                return groups, sig[i:].strip()
            groups.append(sig[i:j + 1])
            i = j + 1
            continue
        if ch == ":":
            return groups, sig[i + 1:].strip()
        # bare binder names before the colon (`theorem foo x y : ...`) or junk: stop
        j = sig.find(":", i)
        k = i
        depth = 0
        while k < n:
            c = sig[k]
            if c in OPEN_BR:
                depth += 1
            elif c in CLOSE_BR:
                depth -= 1
            elif c == ":" and depth == 0 and not sig.startswith(":=", k):
                break
            k += 1
        bare = sig[i:k].split()
        if k < n and bare and all(RE_IDENT.fullmatch(b) or b == "_" for b in bare):
            groups.append("(" + " ".join(bare) + ")")
            return groups, sig[k + 1:].strip()
        return groups, sig[i:].strip() if j < 0 else sig[i:].strip()
    return groups, ""


def parse_binder(group: str) -> Tuple[str, List[str], str]:
    """`(a b : T)` -> ('(', ['a','b'], 'T'); `[Foo a]` -> ('[', [], 'Foo a');
    `[i : Foo a]` -> ('[', ['i'], 'Foo a'); `{a b}` -> ('{', ['a','b'], '')."""
    kind = group[0]
    inner = group[1:-1].strip()
    depth = 0
    for k, c in enumerate(inner):
        if c in OPEN_BR:
            depth += 1
        elif c in CLOSE_BR:
            depth -= 1
        elif c == ":" and depth == 0 and not inner.startswith(":=", k):
            names = inner[:k].split()
            ty = inner[k + 1:].strip()
            # drop default values / auto-params `(x : T := v)`
            d2 = 0
            for q, c2 in enumerate(ty):
                if c2 in OPEN_BR:
                    d2 += 1
                elif c2 in CLOSE_BR:
                    d2 -= 1
                elif d2 == 0 and ty.startswith(":=", q):
                    ty = ty[:q].strip()
                    break
            return kind, names, ty
    if kind == "[":
        return kind, [], inner
    return kind, inner.split(), ""


def idents(text: str) -> Set[str]:
    """Identifier heads mentioned in `text` (`x.foo` mentions `x` and `x.foo`)."""
    out: Set[str] = set()
    for m in RE_IDENT.finditer(text):
        t = m.group(0)
        out.add(t)
        dot = t.find(".")
        if dot > 0:
            out.add(t[:dot])
    return out


_RE_INNER_BINDER = re.compile(r"(?:∀|∃!?|\bfun\b|λ|∑'?|∏'?|∫⁻?|⨆|⨅|⋃|⋂)\s*([^,↦:∈]*?)(?:,|=>|↦|:|∈)")


def _inner_bound(text: str) -> Set[str]:
    """Names bound by binder notation inside the statement (`∀ a ∈ s, ...`): these are not
    mentions of same-named section variables. Approximation: a name bound anywhere in the
    signature is treated as bound everywhere in it."""
    out: Set[str] = set()
    for m in _RE_INNER_BINDER.finditer(text):
        for t in m.group(1).replace("(", " ").replace("{", " ").replace("⦃", " ").split():
            if RE_IDENT.fullmatch(t) and "." not in t:
                out.add(t)
    return out


class _Scope:
    __slots__ = ("kind", "name", "n_ns", "vars", "include", "opens")

    def __init__(self, kind: str, name: str, n_ns: int):
        self.kind = kind
        self.name = name
        self.n_ns = n_ns          # how many namespace components this scope pushed
        self.vars: List[List] = []  # [kind, names, type, idents(type)]
        self.include: Set[str] = set()
        self.opens: List[str] = []


def _parse_opens(rest: str) -> List[str]:
    """Extract namespace names from an `open [scoped] A B [hiding ...]` command."""
    toks = rest.split()[1:]
    out: List[str] = []
    for t in toks:
        if t == "scoped":
            continue
        if t in ("hiding", "renaming", "in") or t.startswith("("):
            break
        if RE_IDENT.fullmatch(t):
            out.append(t)
    return out


def _effective_variables(
    scopes: List[_Scope], own_groups: List[str], mention_text: str,
    omit: Set[str], extra_include: Set[str],
) -> List[str]:
    """Approximate Lean's `variable` auto-inclusion; returns binder group strings."""
    allv: List[List] = [v for sc in scopes for v in sc.vars]
    if not allv:
        return []
    own_names: Set[str] = set()
    for g in own_groups:
        own_names.update(parse_binder(g)[1])
    mentioned = idents(mention_text) - own_names - _inner_bound(mention_text)
    for sc in scopes:
        mentioned |= sc.include
    mentioned |= extra_include
    var_names: Set[str] = set()
    for v in allv:
        var_names.update(v[1])
    inc_names: Set[str] = set()
    changed = True
    while changed:
        changed = False
        for v in allv:
            if v[2] is None:
                continue
            for nm in v[1]:
                if nm in mentioned and nm not in inc_names and nm not in own_names:
                    inc_names.add(nm)
                    mentioned |= v[3]
                    changed = True
        # instance binders pull in nothing new by themselves, but once included their
        # own mentions are already variables that are included, so no extra pass needed
    kind_of: Dict[str, str] = {}
    for v in allv:
        if v[2] is None:
            for nm in v[1]:
                kind_of[nm] = v[0]
    out: List[str] = []
    for v in allv:
        kind, names, ty, tyids = v
        if ty is None:
            continue
        if kind == "[":
            if " ".join(ty.split()) in omit:
                continue
            deps = tyids & var_names
            if any(nm in inc_names for nm in names) or (deps and deps <= inc_names):
                pre = (" ".join(names) + " : ") if names else ""
                out.append(f"[{pre}{ty}]")
            continue
        for nm in names:
            if nm in inc_names:
                k = kind_of.get(nm, kind)
                out.append(f"{k}{nm}{(' : ' + ty) if ty else ''}{_PAIR[k]}")
    return out


def _add_variables(scope: _Scope, scopes: List[_Scope], text: str) -> None:
    groups, _rest = split_binders(text)
    for g in groups:
        kind, names, ty = parse_binder(g)
        if kind != "[" and not ty and names:
            # `variable (R)` / `variable {R}`: binder-kind update of an existing variable.
            # Recorded as an override entry (type None); position stays with the original.
            known = {nm for sc in scopes for v in sc.vars for nm in v[1]}
            upd = [nm for nm in names if nm in known]
            new = [nm for nm in names if nm not in known]
            if upd:
                scope.vars.append([kind, upd, None, set()])
            if new:
                scope.vars.append([kind, new, "", set()])
            continue
        scope.vars.append([kind, names, ty, idents(ty)])


def extract_decls(text: str) -> Iterator[Dict]:
    """Yield declaration records from one file's text.

    Record keys: name (namespace-qualified), short, kind, line (1-based), private (0/1),
    var_binders (list[str]), own_binders (list[str]), type (str), has_body (0/1).
    """
    clean = strip_comments(text)
    lines = clean.split("\n")
    n = len(lines)
    # 1. chunk into commands: a command starts at a column-0 line whose first word is a
    #    command word (or `@[`), and runs until the next such line.
    starts: List[int] = []
    for i, ln in enumerate(lines):
        if not ln or ln[0].isspace():
            continue
        m = _RE_WORD0.match(ln)
        if not m:
            continue
        w = m.group(0)
        if w.startswith("@["):
            w = "@["
        if w == "@[" or w in _COMMAND_WORDS:
            starts.append(i)
    starts.append(n)

    scopes: List[_Scope] = [_Scope("root", "", 0)]
    ns: List[str] = []
    pending_prefix = ""       # `open X in` / `omit [..] in` / attribute-only lines
    pending_line: Optional[int] = None

    for si in range(len(starts) - 1):
        a, b = starts[si], starts[si + 1]
        chunk = "\n".join(lines[a:b]).rstrip()
        if pending_prefix:
            chunk = pending_prefix + "\n" + chunk
            line0 = pending_line if pending_line is not None else a
        else:
            line0 = a
        pending_prefix, pending_line = "", None
        first = chunk.split(None, 1)[0] if chunk.split() else ""

        # attribute-only line: glue to the next command
        rest, mods = _skip_attrs_mods(chunk)
        if not rest.strip():
            pending_prefix, pending_line = chunk, line0
            continue

        # `<cmd> ... in` prefixes apply to the next command only
        omit: Set[str] = set()
        extra_inc: Set[str] = set()
        extra_opens: List[str] = []
        while True:
            w = rest.split(None, 1)[0] if rest.split() else ""
            if w in ("open", "omit", "include", "set_option", "variable", "universe",
                     "attribute", "unseal", "seal"):
                m_in = re.search(r"(?:^|\s)in\s*(?:\n|$)", rest)
                if not m_in:
                    break
                head, tail = rest[:m_in.start()], rest[m_in.end():]
                if w == "omit":
                    for g in split_binders(head[4:])[0]:
                        if g[0] == "[":
                            omit.add(" ".join(parse_binder(g)[2].split()))
                elif w == "include":
                    extra_inc.update(head.split()[1:])
                elif w == "open":
                    extra_opens.extend(_parse_opens(head))
                if not tail.strip():
                    pending_prefix, pending_line = chunk, line0
                    rest = ""
                    break
                rest, mods2 = _skip_attrs_mods(tail)
                mods += mods2
                continue
            break
        if not rest:
            continue
        w = rest.split(None, 1)[0]

        if w == "open":
            scopes[-1].opens.extend(_parse_opens(rest))
            continue

        if w == "namespace":
            parts = rest.split()
            name = parts[1] if len(parts) > 1 else ""
            comps = [c for c in name.split(".") if c] if name else []
            scopes.append(_Scope("namespace", name, len(comps)))
            ns.extend(comps)
            continue
        if w == "section":
            parts = rest.split()
            scopes.append(_Scope("section", parts[1] if len(parts) > 1 else "", 0))
            continue
        if w == "end":
            if len(scopes) > 1:
                sc = scopes.pop()
                if sc.n_ns:
                    del ns[len(ns) - sc.n_ns:]
            continue
        if w == "variable":
            _add_variables(scopes[-1], scopes, rest[len("variable"):])
            continue
        if w == "include":
            scopes[-1].include.update(rest.split()[1:])
            continue
        if w == "omit":
            continue  # section-level omit: rare; ignored (documented limit)
        if w == "mutual":
            # declarations inside `mutual` are indented or column-0; column-0 ones are
            # picked up as their own chunks.
            continue

        m = _RE_DECL_HEAD.match(rest)
        if not m:
            continue
        kind, short = m.group(1), m.group(2)
        after = rest[m.end():]
        if kind == "instance":
            # `instance (priority := 100) name : T` / `instance : T` / `instance name : T`
            m_pr = re.match(r"\s*\(priority\s*:=[^)]*\)", rest[len("instance"):])
            if m_pr:
                tail = rest[len("instance") + m_pr.end():]
                m2 = re.match(r"\s+((?:«[^»]*»|[^\s:({\[⦃«]+)+)", tail)
                short = m2.group(1) if m2 else None
                after = tail[m2.end():] if m2 else tail
        if not short:
            continue  # anonymous instance / malformed
        sig, body = split_header(after, kind in ("inductive", "structure", "class"))
        own_groups, ty = split_binders(sig)
        mention = sig if kind in ("theorem", "lemma") else (sig + " " + body)
        var_groups = _effective_variables(scopes, own_groups, mention, omit, extra_inc)

        if short.startswith("_root_."):
            full = short[len("_root_."):]
        elif ns:
            full = ".".join(ns) + "." + short
        else:
            full = short
        all_opens: List[str] = []
        for sc in scopes:
            all_opens.extend(sc.opens)
        if extra_opens:
            all_opens.extend(extra_opens)
        yield {
            "name": full,
            "short": short,
            "namespace": ".".join(ns),
            "opens": tuple(all_opens),
            "kind": kind,
            "line": line0 + 1,
            "private": 1 if "private" in mods else 0,
            "var_binders": var_groups,
            "own_binders": own_groups,
            "type": " ".join(ty.split()),
            "has_body": 1 if body.strip() else 0,
        }


def discover(root: str, subdirs: Optional[List[str]] = None) -> List[Tuple[str, str]]:
    """Deterministic list of (module_name, abs_path) for `.lean` files under root."""
    out: List[Tuple[str, str]] = []
    bases = [os.path.join(root, s) for s in subdirs] if subdirs else [root]
    for base in bases:
        if os.path.isfile(base):
            rel = os.path.relpath(base, root)
            out.append((rel[:-5].replace(os.sep, "."), base))
            continue
        for dp, dns, fns in os.walk(base):
            dns[:] = sorted(d for d in dns if d not in (".lake", ".git", "build", "node_modules"))
            for fn in sorted(fns):
                if fn.endswith(".lean"):
                    full = os.path.join(dp, fn)
                    rel = os.path.relpath(full, root)
                    out.append((rel[:-5].replace(os.sep, "."), full))
    out.sort()
    return out
