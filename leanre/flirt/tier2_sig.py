#!/usr/bin/env python3
"""FLIRT Tier 2 -- signature hashing adapter.

The normalized signature hash is specified by docs/SIGHASH.md and implemented in
leanre/sighash.py (owner: `flirt`). This module is the single place where Tier 2 calls it:

    sig_hashes(binders, type_text) -> SigHash(s1n, s1t, n_tokens)

`s1n` = identifiers as written, `s1t` = non-bound identifiers reduced to their last
dot-component. Both drop the declaration's own name, binder names and binder kinds, so
they are stable under renaming the declaration, alpha-renaming binders, universe renaming,
whitespace and proof-body changes. They are SOURCE-TEXT hashes: no elaboration, no name
resolution -- "same normalized statement shape", never "same mathematics proved".

If leanre/sighash.py does not (yet) expose a compatible entry point, a local fallback
implementing the same published rules is used and the scheme tag says so (`s0n`/`s0t`), so
fallback hashes can never be confused with spec hashes.
"""
from __future__ import annotations

import hashlib
import os
import re
import sys
from typing import Callable, List, NamedTuple, Optional, Sequence, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_LEANRE = os.path.dirname(_HERE)
if _LEANRE not in sys.path:
    sys.path.insert(0, _LEANRE)

try:  # package-relative or flat import, whichever the caller set up
    from .tier2_extract import OPEN_BR, CLOSE_BR, RE_IDENT, parse_binder
except ImportError:  # pragma: no cover
    from tier2_extract import OPEN_BR, CLOSE_BR, RE_IDENT, parse_binder


class SigHash(NamedTuple):
    s1n: str
    s1t: str
    s1a: str
    n_tokens: int
    n_local: int


_RE_TOKEN = re.compile(
    r"(?:«[^»]*»|[^\W\d][\w'!?]*)(?:\.(?:«[^»]*»|[^\W\d][\w'!?]*))*"   # identifier
    r"|\d+(?:\.\d+)?"                                                   # numeral
    r"|\"(?:\\.|[^\"\\])*\""                                            # string
    r"|:=|=>|->|<->|<=|>=|!=|\.\.|\S",                                   # symbols
    re.UNICODE,
)
# Binder-introducing notations: names after these (up to the delimiter) are bound.
_BINDER_HEADS = {"∀", "∃", "∃!", "fun", "λ", "∑", "∏", "∫", "⨆", "⨅", "⋃", "⋂", "∑'", "∏'", "∮", "∫⁻"}
_BINDER_STOPS = {",", "=>", ":", "∈", "in", "<", "≤", ">", "≥", "≠", "∉", "⊆", "⊂", "↦"}
_SORTS = {"Type", "Sort"}
_RE_UNIV_INST = re.compile(r"\.\{([^{}]*)\}")
_ASCII_ALIASES = {"->": "→", "<->": "↔", "<=": "≤", ">=": "≥", "!=": "≠", "λ": "fun", "=>": "↦"}


def tokenize(text: str) -> List[str]:
    return _RE_TOKEN.findall(text)


def canonical_tokens(binders: Sequence[str], type_text: str) -> Tuple[List[str], List[bool]]:
    """Canonical token stream + mask saying which tokens are free identifiers.

    Telescope form: each binder name contributes `Π <type tokens> ;`, then `⊢ <result>`.
    Bound names become `#k` (k = order of introduction), universe names after Type/Sort
    become `u#k`. Binder kinds and names never appear.
    """
    bound: dict = {}
    univ: dict = {}
    # universe names: `Type u` / `Sort u` handled in-stream; `Foo.{u, v}` pre-registered so
    # an explicit universe instantiation before the first `Type u` is still a universe.
    for m in _RE_UNIV_INST.finditer(" ".join(binders) + " " + type_text):
        for u in re.split(r"[\s,]+", m.group(1).strip()):
            if u and RE_IDENT.fullmatch(u) and u not in ("max", "imax"):
                univ.setdefault(u, len(univ))
    out: List[str] = []
    free: List[bool] = []

    def emit_expr(toks: List[str]) -> None:
        i, n = 0, len(toks)
        while i < n:
            t = toks[i]
            t = _ASCII_ALIASES.get(t, t)
            if t in _BINDER_HEADS:
                out.append(t)
                free.append(False)
                i += 1
                while i < n:
                    u = toks[i]
                    if u in _BINDER_STOPS:
                        break
                    if len(u) == 1 and u in "([{⦃":
                        d2, j = 1, i + 1
                        while j < n and d2 > 0:
                            if len(toks[j]) == 1 and toks[j] in OPEN_BR:
                                d2 += 1
                            elif len(toks[j]) == 1 and toks[j] in CLOSE_BR:
                                d2 -= 1
                            j += 1
                        inner = toks[i + 1:j - 1]
                        out.append("(")
                        free.append(False)
                        if ":" in inner and all(
                                RE_IDENT.fullmatch(x) for x in inner[:inner.index(":")]):
                            k = inner.index(":")
                            for x in inner[:k]:
                                bound.setdefault(x, len(bound))
                                out.append("#%d" % bound[x])
                                free.append(False)
                            out.append(":")
                            free.append(False)
                            emit_expr(inner[k + 1:])
                        elif inner and all(RE_IDENT.fullmatch(x) and "." not in x for x in inner):
                            for x in inner:                 # `∀ {a b}, ...`
                                bound.setdefault(x, len(bound))
                                out.append("#%d" % bound[x])
                                free.append(False)
                        else:
                            emit_expr(inner)
                        out.append(")")
                        free.append(False)
                        i = j
                        continue
                    if RE_IDENT.fullmatch(u) and "." not in u and u != "_":
                        bound.setdefault(u, len(bound))
                        out.append("#%d" % bound[u])
                        free.append(False)
                        i += 1
                        continue
                    out.append(u)
                    free.append(False)
                    i += 1
                continue
            if t in _SORTS and i + 1 < n and RE_IDENT.fullmatch(toks[i + 1]) \
                    and "." not in toks[i + 1] and toks[i + 1] not in bound:
                out.append(t)
                free.append(False)
                u = toks[i + 1]
                univ.setdefault(u, len(univ))
                out.append("u#%d" % univ[u])
                free.append(False)
                i += 2
                continue
            if RE_IDENT.fullmatch(t):
                head, dot, rest = t.partition(".")
                if t in bound:
                    out.append("#%d" % bound[t])
                    free.append(False)
                elif dot and head in bound:
                    # `x.foo` projection/generalised field notation on a bound variable
                    out.append("#%d" % bound[head])
                    free.append(False)
                    out.append("." + rest)
                    free.append(True)
                elif t in univ:
                    out.append("u#%d" % univ[t])
                    free.append(False)
                else:
                    out.append(t)
                    free.append(True)
            else:
                out.append(t)
                free.append(False)
            i += 1

    for g in binders:
        kind, names, ty = parse_binder(g)
        ttoks = tokenize(ty)
        if kind == "[" or not names:
            out.append("Π")
            free.append(False)
            emit_expr(ttoks)
            out.append(";")
            free.append(False)
            for nm in names:
                bound.setdefault(nm, len(bound))
            continue
        for nm in names:
            out.append("Π")
            free.append(False)
            emit_expr(ttoks)
            out.append(";")
            free.append(False)
            if nm != "_":
                bound[nm] = len(bound)
    out.append("⊢")
    free.append(False)
    emit_expr(tokenize(type_text))
    return out, free


def _h(scheme: str, toks: Sequence[str]) -> str:
    return scheme + ":" + hashlib.sha256("\x1f".join(toks).encode("utf-8")).hexdigest()[:32]


def _last(t: str) -> str:
    if t.startswith("."):
        return "." + t.rsplit(".", 1)[-1]
    return t.rsplit(".", 1)[-1]


def _fallback(
    binders: Sequence[str],
    type_text: str,
    resolve: Optional[Callable[[str], Optional[str]]] = None,
) -> SigHash:
    toks, free = canonical_tokens(binders, type_text)
    s1n = _h("s0n", toks)
    t_toks = [(_last(t) if f else t) for t, f in zip(toks, free)]
    s1t = _h("s0t", t_toks)
    if resolve is None:
        s1a = _h("s0a", t_toks)
        n_local = 0
    else:
        l_idx: dict = {}
        a_toks: List[str] = []
        for t, f in zip(toks, free):
            if f:
                hit = resolve(t)
                if hit is not None:
                    a_toks.append("L#%d" % l_idx.setdefault(hit, len(l_idx)))
                else:
                    a_toks.append(_last(t))
            else:
                a_toks.append(t)
        s1a = _h("s0a", a_toks)
        n_local = len(l_idx)
    return SigHash(s1n, s1t, s1a, len(toks), n_local)


_impl = None
IMPL_NAME = "tier2_sig.fallback (s0n/s0t/s0a)"


def _bind() -> None:
    """Bind to leanre/sighash.py when it exposes the agreed entry point."""
    global _impl, IMPL_NAME
    try:
        import sighash  # type: ignore
    except Exception:
        _impl = _fallback
        return
    fn = getattr(sighash, "source_sig", None)
    if fn is None:
        _impl = _fallback
        return

    def _spec(
        binders: Sequence[str],
        type_text: str,
        resolve: Optional[Callable[[str], Optional[str]]] = None,
    ) -> SigHash:
        r = fn(list(binders), type_text, resolve=resolve)
        return SigHash(r["s1n"], r["s1t"], r["s1a"], int(r["n_tokens"]), int(r["n_local"]))

    _impl = _spec
    IMPL_NAME = "sighash.source_sig (docs/SIGHASH.md spec v%s)" % getattr(sighash, "SPEC_VERSION", "?")


def sig_hashes(
    binders: Sequence[str],
    type_text: str,
    resolve: Optional[Callable[[str], Optional[str]]] = None,
) -> SigHash:
    if _impl is None:
        _bind()
    return _impl(binders, type_text, resolve)  # type: ignore[misc]
