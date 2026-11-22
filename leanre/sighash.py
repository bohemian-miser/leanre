#!/usr/bin/env python3
"""leanre.sighash -- normalized signature hashes for Lean 4 declarations.

Normative spec: docs/SIGHASH.md (version 1).  This file is the reference
implementation; the Rust kernel extractor must reproduce the `k1n` / `k1a`
digests bit-for-bit (see `selftest` and the vectors in docs/SIGHASH.md).

Two hash *spaces* that are never compared with each other:

* kernel  (`k1n`, `k1a`)        -- Merkle hash of the kernel type expression
                                   taken from a lean4export NDJSON stream.
* source  (`s1n`, `s1t`, `s1a`) -- hash of a canonical token stream built from
                                   the source-text signature (no elaboration).

Every digest is SHA-256 truncated to 16 bytes, printed `<scheme>:<32 hex>`.
Only signatures are hashed: never a proof term, a definition body or the
declaration's own name.  stdlib only.
"""
from __future__ import annotations

import argparse
import array
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from typing import (Any, Callable, Dict, IO, Iterable, Iterator, List,
                    Optional, Sequence, Set, Tuple)

SPEC_VERSION = "1"
DIGEST_BYTES = 16
SIZE_CAP = 0xFFFFFFFF  # sig_size saturates here

KERNEL_SCHEMES = ("k1n", "k1a")
SOURCE_SCHEMES = ("s1n", "s1t", "s1a")


def H(data: bytes) -> bytes:
    """Node hash: SHA-256 truncated to 16 raw bytes."""
    return hashlib.sha256(data).digest()[:DIGEST_BYTES]


def fmt(scheme: str, digest: bytes) -> str:
    return scheme + ":" + digest.hex()


def _dec(n: int) -> bytes:
    return str(n).encode("ascii")


# ---------------------------------------------------------------------------
# Constant-name normalization and the project-local lexicon
# ---------------------------------------------------------------------------
def norm_const_name(name: str) -> str:
    """Rule N1: `_private.<module path>.0.<rest>` -> `<rest>`.

    The module path of a private name changes when a declaration moves to
    another file; the signature hash must not.
    """
    if name.startswith("_private."):
        parts = name.split(".")
        for i in range(1, len(parts)):
            if parts[i] == "0":
                rest = parts[i + 1:]
                if rest:
                    return ".".join(rest)
                break
    return name


class Lexicon:
    """A pinned set of project-declared constant names (rule L1).

    A constant is *project-local* iff, after N1, its name is in the set or a
    proper dot-prefix of its name is in the set (auxiliaries such as
    `foo._proof_1`, `Foo.mk`, `Foo.rec`, `foo.match_1`).  File format: UTF-8,
    one name per line, sorted, `\n`-terminated.  `id` = first 16 hex of the
    SHA-256 of exactly those bytes.
    """

    def __init__(self, names: Iterable[str]):
        self.names = frozenset(n for n in names if n)
        self._id: Optional[str] = None
        self._cache: Dict[str, bool] = {}

    @classmethod
    def load(cls, path: str) -> "Lexicon":
        with open(path, "r", encoding="utf-8") as f:
            return cls(line.rstrip("\n") for line in f)

    def to_bytes(self) -> bytes:
        return ("\n".join(sorted(self.names)) + "\n").encode("utf-8") if self.names else b""

    def save(self, path: str) -> None:
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        with open(path, "wb") as f:
            f.write(self.to_bytes())

    @property
    def id(self) -> str:
        if self._id is None:
            self._id = hashlib.sha256(self.to_bytes()).hexdigest()[:16]
        return self._id

    def __len__(self) -> int:
        return len(self.names)

    def is_local(self, const_name: str) -> bool:
        """Kernel-side predicate (exact name or proper dot-prefix, after N1)."""
        hit = self._cache.get(const_name)
        if hit is not None:
            return hit
        n = norm_const_name(const_name)
        names = self.names
        res = n in names
        while not res:
            i = n.rfind(".")
            if i <= 0:
                break
            n = n[:i]
            res = n in names
        self._cache[const_name] = res
        return res

    def resolve_source(self, ident: str, namespace: str = "",
                       opens: Sequence[str] = ()) -> Optional[str]:
        """Source-side predicate (rule L2): resolve an identifier *as written*.

        Candidates are `P.ident` for P in: "", every prefix of the current
        namespace (longest first), every `open`ed namespace (as written and
        relative to each namespace prefix).  A candidate hits when it is in
        the lexicon, or when `P.<proper prefix of ident>` is (field / ctor /
        auxiliary access).  Returns the lexicon name that hit, else None.
        """
        if ident.startswith("_root_."):
            ident = ident[7:]
            prefixes: List[str] = [""]
        else:
            ns_parts = namespace.split(".") if namespace else []
            ns_prefixes = [".".join(ns_parts[:k]) for k in range(len(ns_parts), 0, -1)]
            prefixes = list(ns_prefixes) + [""]
            for o in opens:
                for p in ns_prefixes:
                    prefixes.append(p + "." + o)
                prefixes.append(o)
        names = self.names
        parts = ident.split(".")
        for k in range(len(parts), 0, -1):
            tail = ".".join(parts[:k])
            for p in prefixes:
                cand = p + "." + tail if p else tail
                if cand in names:
                    return cand
        return None


# ---------------------------------------------------------------------------
# Kernel form (k1n / k1a)
# ---------------------------------------------------------------------------
T_BVAR, T_SORT, T_CONST, T_APP, T_LAM, T_PI, T_LET, T_PROJ, T_NAT, T_STR, T_MDATA = range(11)

F_PARAM = 1   # subtree mentions a universe parameter
F_LOCAL = 2   # subtree mentions a project-local constant

_H_EMPTY_US = H(b"u")


class KernelSigHasher:
    """Incremental hasher over lean4export NDJSON (format 3.x) records.

    Feed every record with `feed(obj)`; declaration records return a list of
    per-constant result dicts:
        {name, role, k1n, k1a, sig_size, n_local}
    (`k1n`/`k1a` are raw 16-byte digests; use `fmt`).
    """

    def __init__(self, lexicon: Optional[Lexicon] = None):
        self.lex = lexicon
        self.names: List[str] = [""]
        self.name_local = bytearray(b"\x00")      # 0 unknown, 1 no, 2 yes
        # levels: tag in b"zspmi"; a, b operands (level ids or name id)
        self.l_tag = bytearray(b"z")
        self.l_a = array.array("Q", [0])
        self.l_b = array.array("Q", [0])
        self.l_flag = bytearray(b"\x00")
        self.l_memo: Dict[int, bytes] = {0: H(b"z")}
        # expressions
        self.e_tag = bytearray()
        self.e_a = array.array("Q")
        self.e_b = array.array("Q")
        self.e_c = array.array("Q")
        self.e_flag = bytearray()
        self.e_us: Dict[int, Tuple[int, ...]] = {}
        self.e_lit: Dict[int, str] = {}
        self.g_memo: Dict[int, Tuple[bytes, int]] = {}   # closed (flag==0) nodes only
        self.name_digest: Dict[int, bytes] = {}
        self.meta: Dict[str, Any] = {}

    # -- tables -------------------------------------------------------------
    def _is_local(self, nid: int) -> bool:
        st = self.name_local[nid]
        if st == 0:
            st = 2 if (self.lex is not None and self.lex.is_local(self.names[nid])) else 1
            self.name_local[nid] = st
        return st == 2

    def _ensure_expr(self, eid: int) -> None:
        cur = len(self.e_tag)
        if eid >= cur:
            grow = eid - cur + 1
            self.e_tag.extend(b"\x00" * grow)
            self.e_flag.extend(b"\x00" * grow)
            z = array.array("Q", bytes(8 * grow))
            self.e_a.extend(z)
            self.e_b.extend(z)
            self.e_c.extend(z)

    def _ensure_level(self, lid: int) -> None:
        cur = len(self.l_tag)
        if lid >= cur:
            grow = lid - cur + 1
            self.l_tag.extend(b"z" * grow)
            self.l_flag.extend(b"\x00" * grow)
            z = array.array("Q", bytes(8 * grow))
            self.l_a.extend(z)
            self.l_b.extend(z)

    def feed(self, obj: Dict[str, Any]) -> Optional[List[Dict[str, Any]]]:
        if "ie" in obj:
            self._feed_expr(obj)
            return None
        if "in" in obj:
            nid = obj["in"]
            names = self.names
            if nid >= len(names):
                names.extend([""] * (nid - len(names) + 1))
                self.name_local.extend(b"\x00" * (nid + 1 - len(self.name_local)))
            if "str" in obj:
                s = obj["str"]
                pre = names[s["pre"]]
                names[nid] = pre + "." + s["str"] if pre else s["str"]
            else:
                nu = obj["num"]
                pre = names[nu["pre"]]
                names[nid] = pre + "." + str(nu["i"]) if pre else str(nu["i"])
            return None
        if "il" in obj:
            lid = obj["il"]
            self._ensure_level(lid)
            if "succ" in obj:
                a = obj["succ"]
                self.l_tag[lid] = 0x73
                self.l_a[lid] = a
                self.l_flag[lid] = self.l_flag[a]
            elif "max" in obj:
                a, b = obj["max"]
                self.l_tag[lid] = 0x6D
                self.l_a[lid] = a
                self.l_b[lid] = b
                self.l_flag[lid] = self.l_flag[a] | self.l_flag[b]
            elif "imax" in obj:
                a, b = obj["imax"]
                self.l_tag[lid] = 0x69
                self.l_a[lid] = a
                self.l_b[lid] = b
                self.l_flag[lid] = self.l_flag[a] | self.l_flag[b]
            elif "param" in obj:
                self.l_tag[lid] = 0x70
                self.l_a[lid] = obj["param"]
                self.l_flag[lid] = F_PARAM
            return None
        if "meta" in obj:
            self.meta = obj["meta"]
            return None
        for key in ("thm", "def", "opaque", "axiom", "quot"):
            if key in obj:
                d = obj[key]
                return [self._plain(d["name"], key, d["type"])]
        if "inductive" in obj:
            return self._inductive(obj["inductive"])
        return None

    def _feed_expr(self, obj: Dict[str, Any]) -> None:
        eid = obj["ie"]
        tag, flag, a, b, c = T_BVAR, 0, 0, 0, 0
        ef = self.e_flag
        if "app" in obj:
            d = obj["app"]
            tag, a, b = T_APP, d["fn"], d["arg"]
            flag = ef[a] | ef[b]
        elif "bvar" in obj:
            tag, a = T_BVAR, obj["bvar"]
        elif "const" in obj:
            d = obj["const"]
            tag, a = T_CONST, d["name"]
            us = d.get("us") or ()
            if us:
                self.e_us[eid] = tuple(us)
                for u in us:
                    flag |= self.l_flag[u]
            if self._is_local(a):
                flag |= F_LOCAL
        elif "forallE" in obj:
            d = obj["forallE"]
            tag, a, b = T_PI, d["type"], d["body"]
            flag = ef[a] | ef[b]
        elif "lam" in obj:
            d = obj["lam"]
            tag, a, b = T_LAM, d["type"], d["body"]
            flag = ef[a] | ef[b]
        elif "sort" in obj:
            tag, a = T_SORT, obj["sort"]
            flag = self.l_flag[a]
        elif "letE" in obj:
            d = obj["letE"]
            tag, a, b, c = T_LET, d["type"], d["value"], d["body"]
            flag = ef[a] | ef[b] | ef[c]
        elif "proj" in obj:
            d = obj["proj"]
            tag, a, b, c = T_PROJ, d["typeName"], d["struct"], d["idx"]
            flag = ef[b] | (F_LOCAL if self._is_local(a) else 0)
        elif "natVal" in obj:
            tag = T_NAT
            self.e_lit[eid] = str(obj["natVal"])
        elif "strVal" in obj:
            tag = T_STR
            self.e_lit[eid] = obj["strVal"]
        elif "mdata" in obj:
            d = obj["mdata"]
            tag, a = T_MDATA, d["expr"]
            flag = ef[a]
        else:
            raise ValueError("unknown expr record: %r" % sorted(obj.keys()))
        if eid == len(ef):          # the exporter emits dense, increasing ids
            self.e_tag.append(tag)
            self.e_a.append(a)
            self.e_b.append(b)
            self.e_c.append(c)
            ef.append(flag)
            return
        self._ensure_expr(eid)
        self.e_tag[eid] = tag
        self.e_a[eid] = a
        self.e_b[eid] = b
        self.e_c[eid] = c
        ef[eid] = flag

    # -- numbering pass (rule K3) --------------------------------------------
    def _number_level(self, lid: int, lv: Dict[int, int]) -> None:
        stack = [lid]
        l_tag, l_a, l_b, l_flag = self.l_tag, self.l_a, self.l_b, self.l_flag
        while stack:
            x = stack.pop()
            if not l_flag[x]:
                continue
            t = l_tag[x]
            if t == 0x70:
                nid = l_a[x]
                if nid not in lv:
                    lv[nid] = len(lv)
            elif t == 0x73:
                stack.append(l_a[x])
            else:
                stack.append(l_b[x])
                stack.append(l_a[x])

    def _number(self, roots: Sequence[int], selfmap: Dict[int, int]
                ) -> Tuple[Dict[int, int], Dict[int, int]]:
        lv: Dict[int, int] = {}
        lc: Dict[int, int] = {}
        seen: Set[int] = set()
        e_tag, e_a, e_b, e_c, e_flag = self.e_tag, self.e_a, self.e_b, self.e_c, self.e_flag
        for root in roots:
            stack = [root]
            while stack:
                e = stack.pop()
                if not e_flag[e] or e in seen:
                    continue
                seen.add(e)
                t = e_tag[e]
                if t == T_APP or t == T_LAM or t == T_PI:
                    stack.append(e_b[e])
                    stack.append(e_a[e])
                elif t == T_CONST:
                    nid = e_a[e]
                    if nid not in selfmap and nid not in lc and self._is_local(nid):
                        lc[nid] = len(lc)
                    for u in self.e_us.get(e, ()):
                        self._number_level(u, lv)
                elif t == T_SORT:
                    self._number_level(e_a[e], lv)
                elif t == T_LET:
                    stack.append(e_c[e])
                    stack.append(e_b[e])
                    stack.append(e_a[e])
                elif t == T_PROJ:
                    nid = e_a[e]
                    if nid not in selfmap and nid not in lc and self._is_local(nid):
                        lc[nid] = len(lc)
                    stack.append(e_b[e])
                elif t == T_MDATA:
                    stack.append(e_a[e])
        return lv, lc

    # -- hash pass (rules K1, K2) -------------------------------------------
    def _hlevel(self, lid: int, lv: Dict[int, int], memo: Dict[int, bytes]) -> bytes:
        if not self.l_flag[lid]:
            h = self.l_memo.get(lid)
            if h is not None:
                return h
        else:
            h = memo.get(lid)
            if h is not None:
                return h
        t = self.l_tag[lid]
        if t == 0x7A:
            h = H(b"z")
        elif t == 0x70:
            h = H(b"p" + _dec(lv[self.l_a[lid]]))
        elif t == 0x73:
            h = H(b"s" + self._hlevel(self.l_a[lid], lv, memo))
        elif t == 0x6D:
            h = H(b"m" + self._hlevel(self.l_a[lid], lv, memo) + self._hlevel(self.l_b[lid], lv, memo))
        else:
            h = H(b"i" + self._hlevel(self.l_a[lid], lv, memo) + self._hlevel(self.l_b[lid], lv, memo))
        if not self.l_flag[lid]:
            self.l_memo[lid] = h
        else:
            memo[lid] = h
        return h

    def _name_ref(self, nid: int) -> bytes:
        h = self.name_digest.get(nid)
        if h is None:
            h = H(b"n" + norm_const_name(self.names[nid]).encode("utf-8"))
            self.name_digest[nid] = h
        return h

    def _hash(self, root: int, lv: Dict[int, int], lc: Dict[int, int],
              selfmap: Dict[int, int], memo: Dict[int, Tuple[bytes, bytes, int]],
              lmemo: Dict[int, bytes]) -> Tuple[bytes, bytes, int]:
        """Return (digest_named, digest_anon, tree_size) of expr `root`."""
        e_tag, e_a, e_b, e_c, e_flag = self.e_tag, self.e_a, self.e_b, self.e_c, self.e_flag
        g = self.g_memo if not selfmap else None   # self-refs make closed nodes block-dependent

        def get(e: int) -> Optional[Tuple[bytes, bytes, int]]:
            if g is not None and not e_flag[e]:
                r = g.get(e)
                if r is not None:
                    return (r[0], r[0], r[1])
                return None
            return memo.get(e)

        def put(e: int, hn: bytes, ha: bytes, size: int) -> None:
            if size > SIZE_CAP:
                size = SIZE_CAP
            if g is not None and not e_flag[e]:
                g[e] = (hn, size)
            else:
                memo[e] = (hn, ha, size)

        stack = [root]
        while stack:
            e = stack[-1]
            if get(e) is not None:
                stack.pop()
                continue
            t = e_tag[e]
            if t == T_APP or t == T_LAM or t == T_PI:
                ra = get(e_a[e])
                rb = get(e_b[e])
                if ra is None or rb is None:
                    if rb is None:
                        stack.append(e_b[e])
                    if ra is None:
                        stack.append(e_a[e])
                    continue
                tb = b"A" if t == T_APP else (b"F" if t == T_LAM else b"P")
                hn = H(tb + ra[0] + rb[0])
                ha = hn if (ra[1] is ra[0] and rb[1] is rb[0]) else H(tb + ra[1] + rb[1])
                put(e, hn, ha, 1 + ra[2] + rb[2])
            elif t == T_CONST:
                us = self.e_us.get(e)
                hu = H(b"u" + b"".join(self._hlevel(u, lv, lmemo) for u in us)) if us else _H_EMPTY_US
                nid = e_a[e]
                j = selfmap.get(nid)
                if j is not None:
                    hn = ha = H(b"C" + H(b"r" + _dec(j)) + hu)
                else:
                    hn = H(b"C" + self._name_ref(nid) + hu)
                    li = lc.get(nid)
                    ha = hn if li is None else H(b"C" + H(b"l" + _dec(li)) + hu)
                put(e, hn, ha, 1)
            elif t == T_BVAR:
                hn = H(b"v" + _dec(e_a[e]))
                put(e, hn, hn, 1)
            elif t == T_SORT:
                hn = H(b"S" + self._hlevel(e_a[e], lv, lmemo))
                put(e, hn, hn, 1)
            elif t == T_LET:
                ra, rb, rc = get(e_a[e]), get(e_b[e]), get(e_c[e])
                if ra is None or rb is None or rc is None:
                    if rc is None:
                        stack.append(e_c[e])
                    if rb is None:
                        stack.append(e_b[e])
                    if ra is None:
                        stack.append(e_a[e])
                    continue
                hn = H(b"T" + ra[0] + rb[0] + rc[0])
                ha = H(b"T" + ra[1] + rb[1] + rc[1])
                put(e, hn, ha, 1 + ra[2] + rb[2] + rc[2])
            elif t == T_PROJ:
                rs = get(e_b[e])
                if rs is None:
                    stack.append(e_b[e])
                    continue
                nid = e_a[e]
                idx = _dec(e_c[e])
                j = selfmap.get(nid)
                if j is not None:
                    rn = ra_ = H(b"r" + _dec(j))
                else:
                    rn = self._name_ref(nid)
                    li = lc.get(nid)
                    ra_ = rn if li is None else H(b"l" + _dec(li))
                hn = H(b"J" + rn + rs[0] + idx)
                ha = H(b"J" + ra_ + rs[1] + idx)
                put(e, hn, ha, 1 + rs[2])
            elif t == T_NAT:
                hn = H(b"N" + self.e_lit[e].encode("ascii"))
                put(e, hn, hn, 1)
            elif t == T_STR:
                hn = H(b"X" + self.e_lit[e].encode("utf-8"))
                put(e, hn, hn, 1)
            elif t == T_MDATA:
                r = get(e_a[e])
                if r is None:
                    stack.append(e_a[e])
                    continue
                put(e, r[0], r[1], r[2])
            else:  # pragma: no cover
                raise ValueError("bad expr tag %d" % t)
        res = get(root)
        assert res is not None
        return res

    # -- per-constant signatures (rule K4) -----------------------------------
    def _plain(self, name_id: int, role: str, type_eid: int,
               selfmap: Optional[Dict[int, int]] = None) -> Dict[str, Any]:
        sm = selfmap or {}
        lv, lc = self._number([type_eid], sm)
        hn, ha, size = self._hash(type_eid, lv, lc, sm, {}, {})
        return {"name": self.names[name_id], "role": role, "k1n": hn, "k1a": ha,
                "sig_size": size, "n_local": len(lc)}

    def _inductive(self, ind: Dict[str, Any]) -> List[Dict[str, Any]]:
        types = ind.get("types", [])
        ctors = ind.get("ctors", [])
        recs = ind.get("recs", [])
        selfmap = {t["name"]: j for j, t in enumerate(types)}
        out: List[Dict[str, Any]] = []
        for t in types:
            mine = sorted((c for c in ctors if c["induct"] == t["name"]), key=lambda c: c["cidx"])
            roots = [t["type"]] + [c["type"] for c in mine]
            lv, lc = self._number(roots, selfmap)
            memo: Dict[int, Tuple[bytes, bytes, int]] = {}
            lmemo: Dict[int, bytes] = {}
            parts = [self._hash(r, lv, lc, selfmap, memo, lmemo) for r in roots]
            hn = H(b"I" + parts[0][0] + H(b"c" + b"".join(p[0] for p in parts[1:])))
            ha = H(b"I" + parts[0][1] + H(b"c" + b"".join(p[1] for p in parts[1:])))
            size = min(SIZE_CAP, sum(p[2] for p in parts))
            out.append({"name": self.names[t["name"]], "role": "ind", "k1n": hn, "k1a": ha,
                        "sig_size": size, "n_local": len(lc)})
        for c in ctors:
            out.append(self._plain(c["name"], "ctor", c["type"], selfmap))
        for r in recs:
            out.append(self._plain(r["name"], "rec", r["type"], selfmap))
        return out


def open_ndjson(path: str) -> Tuple[IO[bytes], Optional[subprocess.Popen]]:
    if path.endswith(".zst"):
        exe = shutil.which("zstd")
        if not exe:
            raise RuntimeError("zstd not found on PATH")
        proc = subprocess.Popen([exe, "-d", "-c", "--long=31", path],
                                stdout=subprocess.PIPE, bufsize=1 << 20)
        assert proc.stdout is not None
        return proc.stdout, proc
    return open(path, "rb"), None


def kernel_sighashes(path: str, lexicon: Optional[Lexicon] = None
                     ) -> Iterator[Dict[str, Any]]:
    """Stream an NDJSON export; yield one result dict per constant, in file order."""
    hasher = KernelSigHasher(lexicon)
    stream, proc = open_ndjson(path)
    try:
        loads = json.loads
        feed = hasher.feed
        ord_ = 0
        for line in stream:
            res = feed(loads(line))
            if res:
                for r in res:
                    r["decl_ord"] = ord_
                    yield r
                ord_ += 1
    finally:
        stream.close()
        if proc is not None:
            proc.wait()


def kernel_tsv_line(r: Dict[str, Any]) -> str:
    return "\t".join((r["name"], r["role"], r["k1n"].hex(), r["k1a"].hex(),
                      str(r["sig_size"]), str(r["n_local"])))


# ---------------------------------------------------------------------------
# Source form (s1n / s1t / s1a)
# ---------------------------------------------------------------------------
_ID_PART = r"(?:«[^»]*»|[^\W\d][\w'!?]*)"
_RE_TOKEN = re.compile(
    r"\s+"
    r"|(?P<str>\"(?:\\.|[^\"\\])*\")"
    r"|(?P<id>" + _ID_PART + r"(?:\.(?:" + _ID_PART + r"|\d+))*)"
    r"|(?P<num>0[xX][0-9a-fA-F]+|\d+(?:\.\d+)?)"
    r"|(?P<op>:=|<->|->|=>|<=|>=|!=|::|\+\+|&&|\|\||\|>\.|\|>|<\||\.\.|//)"
    r"|(?P<ch>.)",
    re.S,
)
_RE_IDENT_FULL = re.compile(r"^" + _ID_PART + r"(?:\.(?:" + _ID_PART + r"|\d+))*$")
# Letter-like postfix notations that Python's \w would glue onto an identifier.
_RE_POSTFIX = re.compile(r"([ˣᵀᴴᵒᵖᵐᵃᵈᶜᵛᶠ]+)")

_CANON = {
    "->": "→", "<->": "↔", "<=": "≤", ">=": "≥", "!=": "≠", "=>": "↦",
    "λ": "fun", "forall": "∀", "exists": "∃", "Π": "∀",
    "ℕ": "Nat", "ℤ": "Int", "ℚ": "Rat", "ℝ": "Real", "ℂ": "Complex",
}
_KEYWORDS = frozenset(
    "fun Type Sort Prop if then else let have show from by match with do at in "
    "max imax where _ this deriving extends ᶠ".split())
_OPEN = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩", "⟪": "⟫"}
_CLOSE = frozenset(_OPEN.values())
_BINDER_OPEN = frozenset("({[⦃")
# Prefix notations whose bound variables precede a `,` (or `↦` for fun) and whose
# body extends as far right as possible.
_BINDER_OPS = frozenset("∀ ∃ fun ∑ ∏ ∫ ⨆ ⨅ ⋃ ⋂ Σ ∐ ⨁ ∮".split())
_EXTENDERS = _BINDER_OPS | frozenset("if let have show match".split())
_BINDER_PRED = frozenset("∈ ∉ < ≤ > ≥ ≠ ⊆ ⊂ ⊇ ⊃".split())


def strip_comments(text: str) -> str:
    """Remove `--` line comments and nested `/- -/` blocks (strings respected)."""
    if "--" not in text and "/-" not in text:
        return text
    out: List[str] = []
    i, n, depth, in_str = 0, len(text), 0, False
    while i < n:
        ch = text[i]
        two = text[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
            else:
                if ch == "\n":
                    out.append(ch)
                i += 1
        elif in_str:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 1
            elif ch == '"':
                in_str = False
            i += 1
        elif ch == '"':
            in_str = True
            out.append(ch)
            i += 1
        elif two == "/-":
            depth = 1
            i += 2
        elif two == "--":
            j = text.find("\n", i)
            if j < 0:
                break
            i = j
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def lex(text: str) -> List[str]:
    """Tokenize Lean source text into canonical tokens (rules S1, S2)."""
    text = _RE_POSTFIX.sub(r" \1 ", strip_comments(text).replace("λ", " fun "))
    toks: List[str] = []
    canon = _CANON
    for m in _RE_TOKEN.finditer(text):
        kind = m.lastgroup
        if kind is None:
            continue
        tok = m.group(kind)
        toks.append(canon.get(tok, tok))
    return toks


def _is_ident(tok: str) -> bool:
    return tok not in _KEYWORDS and _RE_IDENT_FULL.match(tok) is not None


def _match_close(toks: Sequence[str], i: int) -> int:
    """Index of the bracket closing toks[i] (len(toks) if unbalanced)."""
    depth = 0
    for j in range(i, len(toks)):
        t = toks[j]
        if t in _OPEN:
            depth += 1
        elif t in _CLOSE:
            depth -= 1
            if depth == 0:
                return j
    return len(toks)


def _split_colon(toks: Sequence[str]) -> int:
    """Index of the first depth-0 `:` (or -1)."""
    depth = 0
    for j, t in enumerate(toks):
        if t in _OPEN:
            depth += 1
        elif t in _CLOSE:
            depth -= 1
        elif t == ":" and depth == 0:
            return j
    return -1


Entry = Tuple[str, List[str]]   # (binder name or "_", type tokens)


def _binder_entries(toks: Sequence[str]) -> List[Entry]:
    """Expand one binder group (already lexed) into single-name entries (rule S3)."""
    if not toks:
        return []
    if toks[0] in _BINDER_OPEN and _match_close(toks, 0) == len(toks) - 1:
        inner = list(toks[1:-1])
        instance = toks[0] == "["
    else:
        inner, instance = list(toks), False
    depth = 0
    for q, t in enumerate(inner):      # drop a default value / auto-param `:= …`
        if t in _OPEN:
            depth += 1
        elif t in _CLOSE:
            depth -= 1
        elif t == ":=" and depth == 0:
            inner = inner[:q]
            break
    c = _split_colon(inner)
    if c < 0:
        if instance:
            return [("_", inner)]
        return [(t, []) for t in inner if _is_ident(t) or t == "_"]
    names = [t for t in inner[:c] if _is_ident(t) or t == "_"] or ["_"]
    ty = inner[c + 1:]
    return [(nm, list(ty)) for nm in names]


def _strip_parens(toks: List[str]) -> List[str]:
    while len(toks) >= 2 and toks[0] == "(" and _match_close(toks, 0) == len(toks) - 1:
        if _split_colon(toks[1:-1]) >= 0:
            break  # `(x : T)` is a binder / ascription, not redundant parentheses
        toks = toks[1:-1]
    return toks


def _hoist(tt: List[str], entries: List[Entry]) -> List[str]:
    """Telescope normal form (rule S4): move leading `∀` binders and top-level
    `A →` antecedents of the result type into the binder list."""
    while True:
        tt = _strip_parens(tt)
        if not tt:
            return tt
        if tt[0] == "∀":
            # find the depth-0 comma ending the binder list
            depth, comma = 0, -1
            for j in range(1, len(tt)):
                t = tt[j]
                if t in _OPEN:
                    depth += 1
                elif t in _CLOSE:
                    depth -= 1
                elif t == "," and depth == 0:
                    comma = j
                    break
            if comma < 0:
                return tt
            span = tt[1:comma]
            j = 0
            bare: List[str] = []
            new: List[Entry] = []
            ok = True
            while j < len(span):
                t = span[j]
                if t in _BINDER_OPEN:
                    k = _match_close(span, j)
                    new.extend((nm, []) for nm in bare)
                    bare = []
                    new.extend(_binder_entries(span[j:k + 1]))
                    j = k + 1
                elif _is_ident(t) or t == "_":
                    bare.append(t)
                    j += 1
                elif t == ":" and bare:
                    ty = span[j + 1:]
                    new.extend((nm, list(ty)) for nm in bare)
                    bare = []
                    j = len(span)
                elif t in _BINDER_PRED and bare:
                    rhs = span[j:]
                    new.extend((nm, []) for nm in bare)
                    new.extend(("_", [nm] + list(rhs)) for nm in bare)
                    bare = []
                    j = len(span)
                else:
                    ok = False
                    break
            if not ok:
                return tt
            new.extend((nm, []) for nm in bare)
            entries.extend(new)
            tt = tt[comma + 1:]
            continue
        # top-level arrow split
        # `→` is right-associative and binds tighter than `↔`; a binder-like
        # prefix (`∀ ∃ fun ∑ …`) swallows everything to its right.
        depth, arrow, blocked = 0, -1, False
        for j, t in enumerate(tt):
            if t in _OPEN:
                depth += 1
            elif t in _CLOSE:
                depth -= 1
            elif depth == 0:
                if t in _EXTENDERS:
                    break
                if t == "→":
                    if arrow < 0:
                        arrow = j
                elif t == "↔" or t == "↦" or t == "," or t == "<|":
                    blocked = True
                    break
        if blocked or arrow <= 0:
            return tt
        seg = tt[:arrow]
        if (seg[0] in _BINDER_OPEN and seg[0] != "[" and _match_close(seg, 0) == len(seg) - 1
                and _split_colon(seg[1:-1]) >= 0):
            entries.extend(_binder_entries(seg))      # dependent arrow `(x : A) → B`
        else:
            entries.append(("_", _strip_parens(list(seg))))
        tt = tt[arrow + 1:]


def _inner_sites(toks: Sequence[str]) -> Set[int]:
    """Indices of tokens that *bind* a name inside a term (rule S5): binders of
    `∀ ∃ fun ∑ …`, set-builder / subtype braces, and dependent-arrow / sigma
    binder groups."""
    out: Set[int] = set()
    n = len(toks)
    for i, t in enumerate(toks):
        if t in _BINDER_OPS:
            j, depth, bare_ok = i + 1, 0, True
            while j < n:
                u = toks[j]
                if depth == 0 and (u == "," or u == "↦"):
                    break
                if u in _OPEN:
                    if depth == 0:
                        k = _match_close(toks, j)
                        grp = toks[j + 1:k]
                        c = _split_colon(grp)
                        for q in range(c if c >= 0 else len(grp)):
                            if _is_ident(grp[q]):
                                out.add(j + 1 + q)
                        j = k + 1
                        continue
                    depth += 1
                elif u in _CLOSE:
                    depth -= 1
                    if depth < 0:
                        break
                elif depth == 0 and bare_ok:
                    if _is_ident(u):
                        out.add(j)
                    elif u != "!" and u != "_" and u != "ᶠ":
                        bare_ok = False
                j += 1
        elif t == "{" and i + 2 < n and _is_ident(toks[i + 1]):
            u = toks[i + 2]
            if u in ("|", ":", "//") or u in _BINDER_PRED:
                k = _match_close(toks, i)
                depth = 0
                for g in toks[i + 1:k]:
                    if g in _OPEN:
                        depth += 1
                    elif g in _CLOSE:
                        depth -= 1
                    elif depth == 0 and (g == "|" or g == "//"):
                        out.add(i + 1)
                        break
        elif t in _BINDER_OPEN and t != "[":
            k = _match_close(toks, i)
            if k + 1 < n and toks[k + 1] in ("→", "×"):
                grp = toks[i + 1:k]
                c = _split_colon(grp)
                if c > 0 and all(_is_ident(g) or g == "_" for g in grp[:c]):
                    out.update(i + 1 + q for q in range(c) if grp[q] != "_")
    return out


def _universes(toks: Sequence[str], bound: Set[str], out: Set[str]) -> None:
    """Collect universe names (rule S6): after `Type`/`Sort`, and inside `.{…}`."""
    n = len(toks)
    for i, t in enumerate(toks):
        if t in ("Type", "Sort") and i + 1 < n:
            u = toks[i + 1]
            if u == "(":
                k = _match_close(toks, i + 1)
                for g in toks[i + 2:k]:
                    if _is_ident(g) and g not in bound:
                        out.add(g)
            elif _is_ident(u) and u not in bound:
                out.add(u)
        elif t == "." and i + 1 < n and toks[i + 1] == "{":
            k = _match_close(toks, i + 1)
            for g in toks[i + 2:k]:
                if _is_ident(g):
                    out.add(g)


def _head(tok: str) -> Tuple[str, str]:
    """Split an identifier into (first component, rest incl. leading dot)."""
    if tok.startswith("«"):
        j = tok.find("»")
        return tok[:j + 1], tok[j + 1:]
    j = tok.find(".")
    return (tok, "") if j < 0 else (tok[:j], tok[j:])


def _tail(tok: str) -> str:
    j = tok.rfind(".")
    return tok if j < 0 else tok[j + 1:]


def _as_tokens(x: Any) -> List[str]:
    return lex(x) if isinstance(x, str) else list(x)


def source_sig(binders: Sequence[Any], type_: Any,
               resolve: Optional[Callable[[str], Optional[str]]] = None) -> Dict[str, Any]:
    """Canonical source signature (docs/SIGHASH.md §3).

    binders : ordered binder groups, each a string such as `(a b : ℕ)`,
              `{α : Type*}`, `[Ring R]`, `x` (auto-included `variable` binders
              first, then the declaration's own).
    type_   : result-type text ("" when the declaration states none).
    resolve : identifier-as-written -> project-local full name or None
              (e.g. functools.partial(Lexicon.resolve_source, …)); None means
              "no project-local names", in which case s1a == s1t.

    Returns {s1n, s1t, s1a (formatted strings), n_tokens, n_local, n_binders,
             tokens_n, tokens_t, tokens_a}.
    """
    entries: List[Entry] = []
    for b in binders:
        entries.extend(_binder_entries(_as_tokens(b)))
    result = _hoist(_as_tokens(type_), entries)

    lists: List[List[str]] = [ty for _, ty in entries] + [result]
    sites = [_inner_sites(l) for l in lists]
    bound: Set[str] = {nm for nm, _ in entries if nm != "_"}
    for l, st in zip(lists, sites):
        bound.update(l[q] for q in st)
    univ: Set[str] = set()
    for l in lists:
        _universes(l, bound, univ)

    # a telescope binder whose name is never referenced is anonymous
    used: Set[str] = set()
    for l in lists:
        for t in l:
            if t not in _KEYWORDS:
                used.add(_head(t)[0])

    stream: List[Tuple[str, bool]] = []     # (token, is_binding_site)
    for (nm, ty), st in zip(entries, sites):
        stream.append(("(", False))
        stream.append((nm, True) if nm in used else ("_", False))
        if ty:
            stream.append((":", False))
            stream.extend((t, q in st) for q, t in enumerate(ty))
        stream.append((")", False))
    if result:
        stream.append((":", False))
        st = sites[-1]
        stream.extend((t, q in st) for q, t in enumerate(result))

    # Bound names: every binding site gets a fresh index; a reference resolves
    # to the latest preceding site of that name (rule S5).
    cur: Dict[str, int] = {}
    n_sites = 0
    u_idx: Dict[str, int] = {}
    l_idx: Dict[str, int] = {}
    tn: List[str] = []
    tt: List[str] = []
    ta: List[str] = []
    for tok, site in stream:
        if site:
            cur[tok] = n_sites
            s = "#%d" % n_sites
            n_sites += 1
        elif tok in _KEYWORDS or not _RE_IDENT_FULL.match(tok):
            s = tok
        else:
            head, rest = _head(tok)
            k = cur.get(head)
            if k is not None:
                s = "#%d%s" % (k, rest)
            elif tok in univ:
                s = "u#%d" % u_idx.setdefault(tok, len(u_idx))
            else:
                tn.append(tok)
                tl = _tail(tok)
                tt.append(tl)
                full = resolve(tok) if resolve is not None else None
                ta.append(tl if full is None else "L#%d" % l_idx.setdefault(full, len(l_idx)))
                continue
        tn.append(s)
        tt.append(s)
        ta.append(s)

    def dg(toks: List[str]) -> bytes:
        return H(" ".join(toks).encode("utf-8"))

    return {
        "s1n": fmt("s1n", dg(tn)), "s1t": fmt("s1t", dg(tt)), "s1a": fmt("s1a", dg(ta)),
        "n_tokens": len(tn), "n_local": len(l_idx), "n_binders": len(entries),
        "tokens_n": tn, "tokens_t": tt, "tokens_a": ta,
    }


def source_hash(binders: Sequence[Any], type_: Any,
                resolve: Optional[Callable[[str], Optional[str]]] = None
                ) -> Tuple[str, str, int]:
    """xrepo-facing shorthand: (exact `s1n`, name-independent `s1a`, n_tokens)."""
    r = source_sig(binders, type_, resolve)
    return r["s1n"], r["s1a"], r["n_tokens"]


# -- header splitting --------------------------------------------------------
DECL_KINDS = ("theorem", "lemma", "def", "abbrev", "structure", "class", "instance",
              "inductive", "opaque", "axiom", "example", "alias")
_MODIFIERS = frozenset("private protected noncomputable unsafe partial nonrec scoped local "
                       "public meta".split())
_TYPE_STOP = frozenset((":=", "where", "|", "extends", "deriving"))


def split_header(text: Any) -> Optional[Dict[str, Any]]:
    """Split a declaration header into kind / name / binder groups / result type.

    `text` runs from the (optional) attributes and modifiers up to, at most,
    the `:=` / `where` / first `|`; anything after is ignored, so passing a
    whole declaration never leaks its body into the hash.
    Returns {kind, name, binders: [token lists], type: token list} or None.
    """
    toks = _as_tokens(text)
    i, n = 0, len(toks)
    while i < n:
        t = toks[i]
        if t == "@" and i + 1 < n and toks[i + 1] == "[":
            i = _match_close(toks, i + 1) + 1
        elif t in _MODIFIERS:
            i += 1
        else:
            break
    if i >= n or toks[i] not in DECL_KINDS:
        return None
    kind = toks[i]
    i += 1
    if kind == "class" and i < n and toks[i] in ("inductive", "abbrev"):
        i += 1
    if kind == "instance" and i < n and toks[i] == "(":      # (priority := …)
        i = _match_close(toks, i) + 1
    name = ""
    if i < n and _RE_IDENT_FULL.match(toks[i]) and toks[i] not in _KEYWORDS:
        name = toks[i]
        i += 1
        if i + 1 < n and toks[i] == "." and toks[i + 1] == "{":   # explicit universes
            i = _match_close(toks, i + 1) + 1
    binders: List[List[str]] = []
    while i < n:
        t = toks[i]
        if t in _BINDER_OPEN:
            k = _match_close(toks, i)
            binders.append(toks[i:k + 1])
            i = k + 1
        elif _is_ident(t) or t == "_":
            binders.append([t])
            i += 1
        else:
            break
    ty: List[str] = []
    if i < n and toks[i] == ":":
        i += 1
        depth = 0
        while i < n:
            t = toks[i]
            if t in _OPEN:
                depth += 1
            elif t in _CLOSE:
                depth -= 1
            elif depth == 0 and t in _TYPE_STOP:
                break
            ty.append(t)
            i += 1
    return {"kind": kind, "name": name, "binders": binders, "type": ty}


def source_hash_header(text: Any, extra_binders: Sequence[Any] = (),
                       resolve: Optional[Callable[[str], Optional[str]]] = None
                       ) -> Optional[Dict[str, Any]]:
    """Hash a raw header line; `extra_binders` are auto-included `variable`s."""
    hd = split_header(text)
    if hd is None:
        return None
    r = source_sig(list(extra_binders) + hd["binders"], hd["type"], resolve)
    r["kind"] = hd["kind"]
    r["name"] = hd["name"]
    return r


# ---------------------------------------------------------------------------
# Source scanning (scopes, `variable`, `open`) -- used for the lexicon, Tier 1/3
# ---------------------------------------------------------------------------
_RE_CMD = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local|public|meta)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom|example|alias"
    r"|namespace|section|end|open|variable|universe|mutual|export)\b")
_RE_IDENT = re.compile(_ID_PART + r"(?:\." + _ID_PART + r")*")


def _header_extent(lines: Sequence[str], i: int, max_lines: int = 400) -> Tuple[str, int]:
    """Text of the command starting at line i, cut before the first depth-0
    `:=` / ` where` / line-initial `|`; never includes a body.  Returns
    (header text, index of the last line consumed)."""
    buf: List[str] = []
    depth = 0
    j = i
    n = len(lines)
    while j < n and j - i < max_lines:
        ln = lines[j]
        if j > i and ln and not ln[0].isspace():
            j -= 1
            break
        if j > i and ln.lstrip().startswith("|") and depth == 0:
            j -= 1
            break
        k, m = 0, len(ln)
        cut = -1
        while k < m:
            ch = ln[k]
            if ch in "([{⦃⟨":
                depth += 1
            elif ch in ")]}⦄⟩":
                depth = max(0, depth - 1)
            elif depth == 0:
                if ch == ":" and k + 1 < m and ln[k + 1] == "=":
                    cut = k
                    break
                if ch == "w" and ln.startswith("where", k) and (k == 0 or not (ln[k - 1].isalnum() or ln[k - 1] in "_.'")) \
                        and (k + 5 >= m or not (ln[k + 5].isalnum() or ln[k + 5] in "_'")):
                    cut = k
                    break
            k += 1
        if cut >= 0:
            buf.append(ln[:cut])
            return " ".join(buf), j
        buf.append(ln)
        j += 1
    return " ".join(buf), min(j, n - 1)


class _Scope:
    __slots__ = ("kind", "name", "opens", "variables")

    def __init__(self, kind: str, name: str):
        self.kind = kind
        self.name = name
        self.opens: List[str] = []
        self.variables: List[List[str]] = []   # binder groups (token lists)


def _included_variables(var_groups: Sequence[List[str]], header_toks: Sequence[str]
                        ) -> List[List[str]]:
    """Rule V1: which in-scope `variable` binders a header pulls in."""
    entries: List[Tuple[str, List[str], bool]] = []   # (name, type, is_instance)
    for g in var_groups:
        inst = bool(g) and g[0] == "["
        for nm, ty in _binder_entries(g):
            entries.append((nm, ty, inst))
    if not entries:
        return []
    var_names = {nm for nm, _, _ in entries if nm != "_"}
    mentioned = {_head(t)[0] for t in header_toks if t not in _KEYWORDS}
    inc = [nm != "_" and nm in mentioned and not inst for nm, _, inst in entries]
    changed = True
    while changed:
        changed = False
        have = {entries[k][0] for k in range(len(entries)) if inc[k]}
        need: Set[str] = set()
        for k, (nm, ty, inst) in enumerate(entries):
            if inc[k]:
                need.update(_head(t)[0] for t in ty if t not in _KEYWORDS)
        for k, (nm, ty, inst) in enumerate(entries):
            if inc[k]:
                continue
            if not inst and nm in need and nm in var_names:
                inc[k] = True
                changed = True
            elif inst or nm == "_":
                deps = {_head(t)[0] for t in ty if t not in _KEYWORDS} & var_names
                if deps and deps <= have:
                    inc[k] = True
                    changed = True
    out: List[List[str]] = []
    for k, (nm, ty, inst) in enumerate(entries):
        if inc[k]:
            out.append((["[", nm, ":"] if inst else ["(", nm, ":"]) + ty + (["]"] if inst else [")"])
                       if ty else ["(", nm, ")"])
    return out


def iter_source_decls(text: str, with_sig: bool = True) -> Iterator[Dict[str, Any]]:
    """Scan one Lean file; yield a dict per named declaration:

        {name (fully qualified), kind, line, namespace, opens, header (token
         list, body-free), var_binders (auto-included `variable` groups)}

    Scopes: `namespace`/`section`/`mutual` push, `end` pops (multi-component
    `end A.B` pops until two components are closed).  `_root_.X` is honoured.
    Only column-0 commands are recognised (true for machine-emitted corpora
    and for Mathlib style).
    """
    lines = strip_comments(text).split("\n")
    scopes: List[_Scope] = [_Scope("file", "")]
    pending_open: List[str] = []
    i, n = 0, len(lines)
    while i < n:
        ln = lines[i]
        if not ln or ln[0].isspace():
            i += 1
            continue
        m = _RE_CMD.match(ln)
        if m is None:
            i += 1
            continue
        cmd = m.group(1)
        rest = ln[m.end():].strip()
        if cmd == "namespace":
            scopes.append(_Scope("ns", rest.split()[0] if rest else ""))
        elif cmd == "section":
            scopes.append(_Scope("sec", rest.split()[0] if rest else ""))
        elif cmd == "mutual":
            scopes.append(_Scope("mutual", ""))
        elif cmd == "end":
            want = len(rest.split()[0].split(".")) if rest else 1
            got = 0
            while len(scopes) > 1 and got < want:
                sc = scopes.pop()
                got += max(1, len(sc.name.split("."))) if sc.name else 1
        elif cmd == "open":
            toks = rest.split()
            one_shot = bool(toks) and toks[-1] == "in"
            if one_shot:
                toks = toks[:-1]
            names: List[str] = []
            for t in toks:
                if t in ("scoped", "hiding", "renaming") or t.startswith("("):
                    if t != "scoped":
                        break
                    continue
                if _RE_IDENT.fullmatch(t):
                    names.append(t)
            if one_shot:
                pending_open.extend(names)
            else:
                scopes[-1].opens.extend(names)
        elif cmd == "variable":
            hdr, j = _header_extent(lines, i)
            toks = lex(hdr[hdr.find("variable") + 8:])
            k = 0
            while k < len(toks):
                if toks[k] in _BINDER_OPEN:
                    e = _match_close(toks, k)
                    scopes[-1].variables.append(toks[k:e + 1])
                    k = e + 1
                else:
                    k += 1
            i = j
        elif cmd in ("universe", "export"):
            pass
        else:
            hdr, j = _header_extent(lines, i)
            hd = split_header(hdr) if with_sig else None
            if with_sig:
                raw_name = hd["name"] if hd else ""
            else:
                if cmd == "class" and rest.startswith(("inductive ", "abbrev ")):
                    rest = rest.split(None, 1)[1]
                m2 = _RE_IDENT.match(rest)
                raw_name = m2.group(0) if m2 else ""
                if raw_name in _KEYWORDS:
                    raw_name = ""
            if raw_name and cmd != "example":
                ns = ".".join(s.name for s in scopes if s.kind == "ns" and s.name)
                if raw_name.startswith("_root_."):
                    full = raw_name[7:]
                else:
                    full = ns + "." + raw_name if ns else raw_name
                rec: Dict[str, Any] = {"name": full, "kind": cmd, "line": i + 1, "namespace": ns}
                if with_sig and hd is not None:
                    opens: List[str] = []
                    var_groups: List[List[str]] = []
                    for s in scopes:
                        opens.extend(s.opens)
                        var_groups.extend(s.variables)
                    opens.extend(pending_open)
                    flat = [t for b in hd["binders"] for t in b] + hd["type"]
                    rec["opens"] = opens
                    rec["binders"] = hd["binders"]
                    rec["type"] = hd["type"]
                    rec["var_binders"] = _included_variables(var_groups, flat)
                yield rec
            pending_open = []
            i = j
        i += 1


def source_decl_hashes(text: str, lexicon: Optional[Lexicon] = None) -> Iterator[Dict[str, Any]]:
    """`iter_source_decls` + s1n/s1t/s1a per declaration (token lists dropped)."""
    for d in iter_source_decls(text):
        resolve = None
        if lexicon is not None:
            ns, opens = d["namespace"], d["opens"]
            resolve = (lambda ident, _ns=ns, _op=opens:
                       lexicon.resolve_source(ident, _ns, _op))
        r = source_sig(d["var_binders"] + d["binders"], d["type"], resolve)
        yield {"name": d["name"], "kind": d["kind"], "line": d["line"],
               "s1n": r["s1n"], "s1t": r["s1t"], "s1a": r["s1a"],
               "n_tokens": r["n_tokens"], "n_local": r["n_local"]}


# ---------------------------------------------------------------------------
# Lexicon builder
# ---------------------------------------------------------------------------
def _lexicon_worker(paths: List[str]) -> List[str]:
    out: List[str] = []
    for p in paths:
        with open(p, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
        for d in iter_source_decls(text, with_sig=False):
            out.append(d["name"])
    return out


def list_lean_files(src_dir: str) -> List[str]:
    files: List[str] = []
    for dirpath, dirnames, filenames in os.walk(src_dir):
        dirnames[:] = sorted(d for d in dirnames if d not in (".lake", ".git", "build"))
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                files.append(os.path.join(dirpath, fn))
    files.sort()
    return files


def build_lexicon(src_dir: str, workers: int = 16) -> Tuple[Lexicon, int]:
    """Scan every .lean file under `src_dir`; returns (Lexicon, file count)."""
    import multiprocessing
    files = list_lean_files(src_dir)
    chunk = 500
    batches = [files[k:k + chunk] for k in range(0, len(files), chunk)]
    names: Set[str] = set()
    if workers <= 1 or len(batches) <= 1:
        for b in batches:
            names.update(_lexicon_worker(b))
    else:
        with multiprocessing.Pool(workers) as pool:
            for res in pool.imap_unordered(_lexicon_worker, batches):
                names.update(res)
    return Lexicon(names), len(files)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def _main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="leanre signature hashes (docs/SIGHASH.md)")
    sub = ap.add_subparsers(dest="cmd", required=True)

    k = sub.add_parser("kernel", help="k1n/k1a for every constant of an NDJSON export")
    k.add_argument("ndjson")
    k.add_argument("--lexicon")
    k.add_argument("--out", help="TSV: name role k1n k1a sig_size n_local (file order)")
    k.add_argument("--grep", action="append", default=[], help="print rows for these exact names")

    b = sub.add_parser("build-lexicon", help="project-local lexicon from a source tree")
    b.add_argument("--src", required=True)
    b.add_argument("--out", required=True)
    b.add_argument("--workers", type=int, default=16)
    b.add_argument("--expect-files", type=int)

    s = sub.add_parser("source", help="s1n/s1t/s1a for one header given as text")
    s.add_argument("header")
    s.add_argument("--tokens", action="store_true")

    a = ap.parse_args(argv)
    if a.cmd == "kernel":
        lex_ = Lexicon.load(a.lexicon) if a.lexicon else None
        want = set(a.grep)
        sha = hashlib.sha256()
        n = 0
        out = open(a.out, "w", encoding="utf-8") if a.out else None
        try:
            for r in kernel_sighashes(a.ndjson, lex_):
                line = kernel_tsv_line(r) + "\n"
                sha.update(line.encode("utf-8"))
                n += 1
                if out:
                    out.write(line)
                if r["name"] in want:
                    sys.stdout.write(line)
        finally:
            if out:
                out.close()
        print("constants=%d lexicon=%s tsv_sha256=%s" % (
            n, lex_.id if lex_ else "none", sha.hexdigest()))
        return 0
    if a.cmd == "build-lexicon":
        lx, nfiles = build_lexicon(a.src, a.workers)
        if a.expect_files is not None and nfiles != a.expect_files:
            print("ERROR: %d .lean files, expected %d" % (nfiles, a.expect_files), file=sys.stderr)
            return 2
        lx.save(a.out)
        print("files=%d names=%d lexicon_id=%s sha256=%s -> %s" % (
            nfiles, len(lx), lx.id, hashlib.sha256(lx.to_bytes()).hexdigest(), a.out))
        return 0
    if a.cmd == "source":
        r = source_hash_header(a.header)
        if r is None:
            print("not a declaration header", file=sys.stderr)
            return 2
        print(r["s1n"], r["s1t"], r["s1a"], "n_tokens=%d" % r["n_tokens"])
        if a.tokens:
            print(" ".join(r["tokens_n"]))
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(_main())
