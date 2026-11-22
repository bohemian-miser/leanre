#!/usr/bin/env python3
"""Tests for leanre/sighash.py (docs/SIGHASH.md v1).

All fixtures are synthetic (hand-built NDJSON records and made-up headers);
no proof source is embedded.  Set LEANRE_SLOW=1 to also run the real-data
regression over data/challenge.ndjson.zst.
"""
from __future__ import annotations

import hashlib
import os
import random
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import sighash as S  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# ---------------------------------------------------------------------------
# Synthetic NDJSON builder + an independent tree-walking oracle
# ---------------------------------------------------------------------------
class NB:
    """Builds lean4export-style records from nested tuple terms."""

    def __init__(self, share: bool = True):
        self.recs = []
        self.names = {"": 0}
        self.levels = {("z",): 0}
        self.n_expr = 0
        self.share = share
        self._memo = {}

    def name(self, s):
        if s in self.names:
            return self.names[s]
        pre, _, last = s.rpartition(".")
        pid = self.name(pre) if pre else 0
        nid = len(self.names)
        self.names[s] = nid
        if last.isdigit():
            self.recs.append({"in": nid, "num": {"pre": pid, "i": int(last)}})
        else:
            self.recs.append({"in": nid, "str": {"pre": pid, "str": last}})
        return nid

    def level(self, l):
        if l in self.levels:
            return self.levels[l]
        if l[0] == "p":
            rec = {"param": self.name(l[1])}
        elif l[0] == "s":
            rec = {"succ": self.level(l[1])}
        elif l[0] == "m":
            rec = {"max": [self.level(l[1]), self.level(l[2])]}
        else:
            rec = {"imax": [self.level(l[1]), self.level(l[2])]}
        lid = len(self.levels)
        self.levels[l] = lid
        rec["il"] = lid
        self.recs.append(rec)
        return lid

    def expr(self, t, binder="x", info="default"):
        key = id(t)
        if self.share and key in self._memo:
            return self._memo[key]
        k = t[0]
        if k == "bvar":
            rec = {"bvar": t[1]}
        elif k == "sort":
            rec = {"sort": self.level(t[1])}
        elif k == "const":
            rec = {"const": {"name": self.name(t[1]), "us": [self.level(u) for u in t[2]]}}
        elif k == "app":
            rec = {"app": {"fn": self.expr(t[1], binder, info), "arg": self.expr(t[2], binder, info)}}
        elif k in ("lam", "pi"):
            rec = {("lam" if k == "lam" else "forallE"): {
                "binderInfo": info, "name": self.name(binder),
                "type": self.expr(t[1], binder, info), "body": self.expr(t[2], binder, info)}}
        elif k == "let":
            rec = {"letE": {"name": self.name(binder), "nondep": False,
                            "type": self.expr(t[1], binder, info),
                            "value": self.expr(t[2], binder, info),
                            "body": self.expr(t[3], binder, info)}}
        elif k == "proj":
            rec = {"proj": {"typeName": self.name(t[1]), "idx": t[2],
                            "struct": self.expr(t[3], binder, info)}}
        elif k == "nat":
            rec = {"natVal": t[1]}
        elif k == "str":
            rec = {"strVal": t[1]}
        else:
            raise ValueError(k)
        eid = self.n_expr
        self.n_expr += 1
        rec["ie"] = eid
        self.recs.append(rec)
        if self.share:
            self._memo[key] = eid
        return eid

    def thm(self, name, ty, value=("nat", "0"), lps=(), **kw):
        self.recs.append({"thm": {"name": self.name(name), "levelParams": [self.name(p) for p in lps],
                                  "type": self.expr(ty, **kw), "value": self.expr(value), "all": []}})

    def defn(self, name, ty, value=("nat", "0"), **kw):
        self.recs.append({"def": {"name": self.name(name), "levelParams": [],
                                  "type": self.expr(ty, **kw), "value": self.expr(value), "all": []}})

    def inductive(self, types, ctors):
        """types: [(name, type)], ctors: [(name, induct, cidx, type)]"""
        self.recs.append({"inductive": {
            "types": [{"name": self.name(n), "type": self.expr(t), "all": []} for n, t in types],
            "ctors": [{"name": self.name(n), "induct": self.name(i), "cidx": c, "type": self.expr(t)}
                      for n, i, c, t in ctors],
            "recs": []}})


def run(nb, lexicon=None):
    h = S.KernelSigHasher(lexicon)
    out = {}
    for rec in nb.recs:
        res = h.feed(rec)
        if res:
            for r in res:
                out[r["name"]] = r
    return out


def oracle(ty, local=lambda n: False):
    """Independent reference: plain recursion over the *tree*, straight from
    the wording of docs/SIGHASH.md §2.  Returns (k1n, k1a, size, n_local)."""
    H = lambda b: hashlib.sha256(b).digest()[:16]
    lv, lc = {}, {}

    def num_l(l):
        if l[0] == "p":
            lv.setdefault(l[1], len(lv))
        elif l[0] == "s":
            num_l(l[1])
        elif l[0] in "mi":
            num_l(l[1])
            num_l(l[2])

    def num(t):
        k = t[0]
        if k == "const":
            n = S.norm_const_name(t[1])
            if local(n):
                lc.setdefault(t[1], len(lc))
            for u in t[2]:
                num_l(u)
        elif k == "sort":
            num_l(t[1])
        elif k in ("app", "lam", "pi"):
            num(t[1])
            num(t[2])
        elif k == "let":
            num(t[1])
            num(t[2])
            num(t[3])
        elif k == "proj":
            if local(S.norm_const_name(t[1])):
                lc.setdefault(t[1], len(lc))
            num(t[3])

    def hl(l):
        if l[0] == "z":
            return H(b"z")
        if l[0] == "p":
            return H(b"p" + str(lv[l[1]]).encode())
        if l[0] == "s":
            return H(b"s" + hl(l[1]))
        return H(l[0].encode() + hl(l[1]) + hl(l[2]))

    def ref(name, anon):
        if anon and name in lc:
            return H(b"l" + str(lc[name]).encode())
        return H(b"n" + S.norm_const_name(name).encode("utf-8"))

    def hx(t, anon):
        k = t[0]
        if k == "bvar":
            return H(b"v" + str(t[1]).encode()), 1
        if k == "sort":
            return H(b"S" + hl(t[1])), 1
        if k == "const":
            return H(b"C" + ref(t[1], anon) + H(b"u" + b"".join(hl(u) for u in t[2]))), 1
        if k in ("app", "lam", "pi"):
            a, sa = hx(t[1], anon)
            b, sb = hx(t[2], anon)
            return H({"app": b"A", "lam": b"F", "pi": b"P"}[k] + a + b), 1 + sa + sb
        if k == "let":
            a, sa = hx(t[1], anon)
            b, sb = hx(t[2], anon)
            c, sc = hx(t[3], anon)
            return H(b"T" + a + b + c), 1 + sa + sb + sc
        if k == "proj":
            s, ss = hx(t[3], anon)
            return H(b"J" + ref(t[1], anon) + s + str(t[2]).encode()), 1 + ss
        if k == "nat":
            return H(b"N" + t[1].encode()), 1
        return H(b"X" + t[1].encode("utf-8")), 1

    num(ty)
    hn, size = hx(ty, False)
    ha, _ = hx(ty, True)
    return hn, ha, size, len(lc)


Z = ("z",)
U = lambda n: ("p", n)
PROP = ("sort", Z)
TYPE = ("sort", ("s", Z))
C = lambda n, *us: ("const", n, list(us))
APP = lambda f, *xs: _app(f, xs)


def _app(f, xs):
    for x in xs:
        f = ("app", f, x)
    return f


def rand_term(rng, depth, pool, consts, lparams):
    if pool and rng.random() < 0.25:
        return rng.choice(pool)                      # shared subterm -> DAG
    if depth <= 0 or rng.random() < 0.2:
        r = rng.random()
        if r < 0.3:
            t = ("bvar", rng.randrange(4))
        elif r < 0.75:
            t = ("const", rng.choice(consts), [rand_level(rng, 2, lparams) for _ in range(rng.randrange(3))])
        elif r < 0.85:
            t = ("sort", rand_level(rng, 2, lparams))
        elif r < 0.95:
            t = ("nat", str(rng.randrange(1000)))
        else:
            t = ("str", "s%d" % rng.randrange(5))
    else:
        r = rng.random()
        sub = lambda: rand_term(rng, depth - 1, pool, consts, lparams)
        if r < 0.5:
            t = ("app", sub(), sub())
        elif r < 0.7:
            t = ("pi", sub(), sub())
        elif r < 0.85:
            t = ("lam", sub(), sub())
        elif r < 0.93:
            t = ("let", sub(), sub(), sub())
        else:
            t = ("proj", rng.choice(consts), rng.randrange(3), sub())
    pool.append(t)
    return t


def rand_level(rng, depth, lparams):
    r = rng.random()
    if depth <= 0 or r < 0.3:
        return Z if rng.random() < 0.4 else ("p", rng.choice(lparams))
    if r < 0.6:
        return ("s", rand_level(rng, depth - 1, lparams))
    return ("m" if r < 0.8 else "i", rand_level(rng, depth - 1, lparams), rand_level(rng, depth - 1, lparams))


class KernelSigHashTests(unittest.TestCase):
    def setUp(self):
        # ∀ (a b : N), Eq.{1} N (add a b) (add b a)
        self.N = C("N")
        self.comm = ("pi", self.N, ("pi", self.N, APP(C("Eq", ("s", Z)), self.N,
                                                      APP(C("add"), ("bvar", 1), ("bvar", 0)),
                                                      APP(C("add"), ("bvar", 0), ("bvar", 1)))))

    def one(self, ty, name="t", lexicon=None, **kw):
        nb = NB()
        nb.thm(name, ty, **kw)
        return run(nb, lexicon)[name]

    def test_digest_shape_and_pinned_vector(self):
        r = self.one(self.comm)
        self.assertEqual(len(r["k1n"]), 16)
        self.assertRegex(S.fmt("k1n", r["k1n"]), r"^k1n:[0-9a-f]{32}$")
        # frozen vector: any change to the byte layout must bump the scheme (k2n)
        self.assertEqual(S.fmt("k1n", r["k1n"]), "k1n:" + oracle(self.comm)[0].hex())
        self.assertEqual(r["k1n"].hex(), "a4dc0c28c0e2b642663c58f5ad1da06c")
        self.assertEqual(r["sig_size"], oracle(self.comm)[2])

    def test_stable_under_proof_body_binder_names_binder_info_own_name(self):
        base = self.one(self.comm)
        self.assertEqual(base["k1n"], self.one(self.comm, value=("str", "another proof"))["k1n"])
        self.assertEqual(base["k1n"], self.one(self.comm, binder="zzz")["k1n"])
        self.assertEqual(base["k1n"], self.one(self.comm, info="implicit")["k1n"])
        self.assertEqual(base["k1n"], self.one(self.comm, name="Other.name")["k1n"])

    def test_sensitive_to_statement(self):
        other = ("pi", self.N, ("pi", self.N, APP(C("Eq", ("s", Z)), self.N,
                                                  APP(C("mul"), ("bvar", 1), ("bvar", 0)),
                                                  APP(C("mul"), ("bvar", 0), ("bvar", 1)))))
        swapped = ("pi", self.N, ("pi", self.N, APP(C("Eq", ("s", Z)), self.N,
                                                    APP(C("add"), ("bvar", 0), ("bvar", 1)),
                                                    APP(C("add"), ("bvar", 0), ("bvar", 1)))))
        self.assertNotEqual(self.one(self.comm)["k1n"], self.one(other)["k1n"])
        self.assertNotEqual(self.one(self.comm)["k1n"], self.one(swapped)["k1n"])

    def test_universe_renaming_and_order(self):
        mk = lambda a, b: ("pi", ("sort", U(a)), ("pi", ("sort", U(b)), APP(C("F", U(a), U(b)), ("bvar", 1))))
        r1 = self.one(mk("u", "v"), lps=("u", "v"))
        r2 = self.one(mk("w", "u_1"), lps=("u_1", "w"))      # renamed AND levelParams reordered
        self.assertEqual(r1["k1n"], r2["k1n"])
        same = ("pi", ("sort", U("u")), ("pi", ("sort", U("u")), APP(C("F", U("u"), U("u")), ("bvar", 1))))
        self.assertNotEqual(r1["k1n"], self.one(same, lps=("u",))["k1n"])

    def test_private_prefix_stripped(self):
        a = self.one(("pi", C("_private.Proj.Mod.A.0.Ns.helper"), PROP))
        b = self.one(("pi", C("_private.Proj.Other.File.0.Ns.helper"), PROP))
        c = self.one(("pi", C("Ns.helper"), PROP))
        self.assertEqual(a["k1n"], b["k1n"])
        self.assertEqual(a["k1n"], c["k1n"])
        self.assertEqual(S.norm_const_name("_private.A.B.0.x.y"), "x.y")
        self.assertEqual(S.norm_const_name("A._private.0.x"), "A._private.0.x")

    def test_anon_variant(self):
        lex = S.Lexicon(["Proj.P", "Proj.Q", "Proj2.P", "Proj2.Q"])
        mk = lambda p, q: ("pi", APP(C(p), C("N")), ("pi", APP(C(q), C("N")), APP(C(p), C("N"))))
        a = self.one(mk("Proj.P", "Proj.Q"), lexicon=lex)
        b = self.one(mk("Proj2.Q", "Proj2.P"), lexicon=lex)      # consistently renamed
        c = self.one(mk("Proj.P", "Proj.P"), lexicon=lex)        # different sharing pattern
        self.assertNotEqual(a["k1n"], b["k1n"])
        self.assertEqual(a["k1a"], b["k1a"])
        self.assertNotEqual(a["k1a"], c["k1a"])
        self.assertEqual((a["n_local"], c["n_local"]), (2, 1))
        # auxiliaries of a project declaration are local via the dot-prefix rule
        d = self.one(mk("Proj.P._proof_1", "Proj.Q.match_1"), lexicon=lex)
        self.assertEqual(a["k1a"], d["k1a"])
        # no local constant => k1a == k1n; and k1n never depends on the lexicon
        e = self.one(self.comm, lexicon=lex)
        self.assertEqual(e["k1a"], e["k1n"])
        self.assertEqual(a["k1n"], self.one(mk("Proj.P", "Proj.Q"))["k1n"])
        self.assertEqual(self.one(mk("Proj.P", "Proj.Q"))["n_local"], 0)

    def test_dag_equals_tree_and_oracle(self):
        rng = random.Random(20261122)
        consts = ["A", "B.c", "Loc.x", "Loc.y", "_private.M.0.Loc.z", "Lib.f"]
        lex = S.Lexicon(["Loc.x", "Loc.y", "Loc.z"])
        local = lambda n: n in ("Loc.x", "Loc.y", "Loc.z")
        for trial in range(300):
            pool = []
            ty = rand_term(rng, 6, pool, consts, ["u", "v", "w"])
            want = oracle(ty, local)
            for share in (True, False):
                nb = NB(share=share)
                nb.thm("t", ty)
                got = run(nb, lex)["t"]
                self.assertEqual((got["k1n"], got["k1a"], got["sig_size"], got["n_local"]), want,
                                 "trial %d share=%s" % (trial, share))

    def test_memo_does_not_leak_between_declarations(self):
        # the same shared expr ids are used by declarations with different
        # universe numbering / local numbering
        lex = S.Lexicon(["L.a", "L.b"])
        local = lambda n: n in ("L.a", "L.b")
        x = APP(C("F", U("u"), U("v")), C("L.a"), C("L.b"))
        t1 = ("pi", x, x)
        t2 = ("pi", ("sort", U("v")), ("pi", C("L.b"), x))
        nb = NB()
        nb.thm("t1", t1)
        nb.thm("t2", t2)
        nb.thm("t3", t1)
        got = run(nb, lex)
        for nm, ty in (("t1", t1), ("t2", t2), ("t3", t1)):
            self.assertEqual((got[nm]["k1n"], got[nm]["k1a"]), oracle(ty, local)[:2], nm)

    def test_exponential_tree_is_linear_time(self):
        t = C("X")
        for _ in range(200):
            t = ("app", t, t)        # 2^200 leaves as a tree, 201 DAG nodes
        r = self.one(("pi", t, PROP))
        self.assertEqual(r["sig_size"], S.SIZE_CAP)
        self.assertEqual(len(r["k1n"]), 16)

    def test_inductive_composite_and_self_reference(self):
        def block(tname):
            nb = NB()
            nb.inductive([(tname, TYPE)],
                         [(tname + ".nil", tname, 0, C(tname)),
                          (tname + ".cons", tname, 1, ("pi", C("N"), ("pi", C(tname), C(tname))))])
            return run(nb)
        a, b = block("MyList"), block("Renamed.L")
        self.assertEqual(a["MyList"]["k1n"], b["Renamed.L"]["k1n"])        # own name not hashed
        self.assertEqual(a["MyList.cons"]["k1n"], b["Renamed.L.cons"]["k1n"])
        self.assertEqual(a["MyList"]["role"], "ind")
        self.assertEqual(a["MyList.cons"]["role"], "ctor")
        nb = NB()
        nb.inductive([("MyList", TYPE)],
                     [("MyList.nil", "MyList", 0, C("MyList")),
                      ("MyList.cons", "MyList", 1, ("pi", C("M"), ("pi", C("MyList"), C("MyList"))))])
        self.assertNotEqual(a["MyList"]["k1n"], run(nb)["MyList"]["k1n"])  # a field type changed
        nb = NB()
        nb.inductive([("S1", TYPE)], [("S1.mk", "S1", 0, ("pi", C("N"), C("S1")))])
        nb.inductive([("S2", TYPE)], [("S2.mk", "S2", 0, ("pi", C("M"), C("S2")))])
        r = run(nb)
        self.assertNotEqual(r["S1"]["k1n"], r["S2"]["k1n"])               # same `Type`, different fields

    def test_mdata_transparent_and_literals(self):
        h = S.KernelSigHasher()
        recs = [{"in": 1, "str": {"pre": 0, "str": "c"}}, {"in": 2, "str": {"pre": 0, "str": "t"}},
                {"ie": 0, "const": {"name": 1, "us": []}},
                {"ie": 1, "mdata": {"expr": 0, "data": {}}},
                {"ie": 2, "natVal": "12345678901234567890123"},
                {"thm": {"name": 2, "levelParams": [], "type": 1, "value": 2, "all": []}}]
        res = None
        for r in recs:
            res = h.feed(r) or res
        self.assertEqual(res[0]["k1n"], S.H(b"C" + S.H(b"n" + b"c") + S.H(b"u")))


class SourceSigHashTests(unittest.TestCase):
    def h(self, header, **kw):
        r = S.source_hash_header(header, **kw)
        self.assertIsNotNone(r, header)
        return r

    def same(self, a, b, key="s1n"):
        self.assertEqual(self.h(a)[key], self.h(b)[key], "%s\n%s" % (a, b))

    def differ(self, a, b, key="s1n"):
        self.assertNotEqual(self.h(a)[key], self.h(b)[key], "%s\n%s" % (a, b))

    def test_whitespace_comments_modifiers_attributes_own_name(self):
        base = "theorem foo (a b : ℕ) (h : a ≤ b) : a + 0 = a"
        self.same(base, "theorem   foo\n  (a b : ℕ)\n    (h : a ≤ b) :\n  a + 0 = a")
        self.same(base, "@[simp] private lemma  Other.name (a b : ℕ) (h : a ≤ b) : a + 0 = a")
        self.same(base, "theorem foo (a b : ℕ) /- note -/ (h : a ≤ b) : a + 0 = a -- trailing")
        self.assertRegex(self.h(base)["s1n"], r"^s1n:[0-9a-f]{32}$")

    def test_proof_body_never_hashed(self):
        self.same("theorem foo (a : ℕ) : a + 0 = a := by simp",
                  "theorem foo (a : ℕ) : a + 0 = a := Nat.add_zero a")
        self.same("def f (x : ℕ) : ℕ → ℕ\n  | 0 => 1\n  | n+1 => 2",
                  "def f (x : ℕ) : ℕ → ℕ := fun _ => 0")
        r = self.h("theorem foo (a : ℕ) : a + 0 = a := by simp [secret_lemma]")
        self.assertNotIn("secret_lemma", r["tokens_n"])
        self.assertNotIn("simp", r["tokens_n"])

    def test_alpha_renaming_and_binder_info(self):
        base = "theorem foo (a b : ℕ) (h : a ≤ b) : ∃ c, a + c = b"
        self.same(base, "theorem foo (x y : ℕ) (hxy : x ≤ y) : ∃ z, x + z = y")
        self.same(base, "theorem foo {a b : ℕ} (h : a ≤ b) : ∃ c, a + c = b")
        self.same(base, "theorem foo (a : ℕ) (b : ℕ) (h : a ≤ b) : ∃ c, a + c = b")
        self.differ(base, "theorem foo (a b : ℕ) (h : b ≤ a) : ∃ c, a + c = b")
        self.same(base, "theorem foo (a b : ℕ) (h : a ≤ b := by omega) : ∃ c, a + c = b")
        # sibling scopes may reuse a bound name
        self.same("theorem s (s : Finset ℕ) : ∑ i ∈ s, i = ∑ j ∈ s, j",
                  "theorem s (t : Finset ℕ) : ∑ k ∈ t, k = ∑ k ∈ t, k")
        self.same("theorem sb (x : ℕ) : {y | y < x}.Nonempty", "theorem sb (n : ℕ) : {m | m < n}.Nonempty")
        self.same("theorem fn : (fun x ↦ x + 1) = fun y => y + 1", "theorem fn : (λ a ↦ a + 1) = fun b => b + 1")

    def test_universe_renaming(self):
        self.same("theorem u.{u, v} (α : Type u) (β : Type v) : Nonempty (α → β)",
                  "theorem u.{w, u} (α : Type w) (β : Type u) : Nonempty (α → β)")
        self.differ("theorem u (α : Type u) (β : Type v) : Nonempty (α → β)",
                    "theorem u (α : Type u) (β : Type u) : Nonempty (α → β)")
        self.same("def d (α : Sort (max u v)) : Sort (u + 1)", "def d (α : Sort (max a b)) : Sort (a + 1)")

    def test_telescope_normal_form(self):
        base = "theorem foo (a b : ℕ) (h : a ≤ b) : a + 0 = a"
        self.same(base, "theorem foo : ∀ (a b : ℕ), a ≤ b → a + 0 = a")
        self.same(base, "theorem foo : ∀ a b : Nat, a <= b -> a + 0 = a")
        self.same(base, "theorem foo (a : ℕ) : ∀ b : ℕ, (a ≤ b) → a + 0 = a")
        self.same("theorem bp (s : Set ℕ) : ∀ x ∈ s, 0 ≤ x", "theorem bp (s : Set ℕ) (x : ℕ) (hx : x ∈ s) : 0 ≤ x"
                  .replace("(x : ℕ)", "(x)"))
        self.same("theorem dep : (x : α) → P x → Q x", "theorem dep (y : α) (h : P y) : Q y")
        # `↔` binds looser than `→`: must NOT be split
        r = self.h("theorem iff_ex : A → B ↔ C")
        self.assertEqual(r["n_binders"], 0)
        # an arrow inside a binder body stays inside
        r = self.h("theorem ex : ∃ x, P x → Q x")
        self.assertEqual(r["n_binders"], 0)

    def test_notation_canonicalisation(self):
        self.same("theorem n (x : ℝ) (z : ℂ) (q : ℚ) (k : ℤ) : x ≠ 0 → x ≥ 0 ↔ 0 ≤ x",
                  "theorem n (x : Real) (z : Complex) (q : Rat) (k : Int) : x != 0 -> x >= 0 <-> 0 <= x")

    def test_tail_and_anon_variants(self):
        a = "theorem a (n : ℕ) : Nat.Prime n → Finset.card (Finset.range n) = n"
        b = "theorem b (n : ℕ) : Prime n → card (range n) = n"
        self.differ(a, b, "s1n")
        self.same(a, b, "s1t")
        lex = S.Lexicon(["Proj.Deep.bound", "Proj.Deep.Good", "Other.limit", "Other.Nice"])
        ra = S.source_sig(["(n : ℕ)"], "Good n → bound n ≤ Nat.succ n",
                          lambda t: lex.resolve_source(t, "Proj.Deep", ()))
        rb = S.source_sig(["(m : ℕ)"], "Nice m → limit m ≤ Nat.succ m",
                          lambda t: lex.resolve_source(t, "", ["Other"]))
        self.assertNotEqual(ra["s1t"], rb["s1t"])
        self.assertEqual(ra["s1a"], rb["s1a"])
        self.assertEqual(ra["n_local"], 2)
        self.assertIn("L#0", ra["tokens_a"])
        self.assertIn("succ", ra["tokens_a"])           # library name kept (tail form)
        rc = S.source_sig(["(n : ℕ)"], "Good n → bound n ≤ Nat.succ n")
        self.assertEqual(rc["s1a"][4:], rc["s1t"][4:])  # no lexicon => s1a digest == s1t digest
        self.assertEqual(S.source_hash(["(n : ℕ)"], "0 ≤ n")[2], 9)

    def test_lexicon(self):
        lex = S.Lexicon(["A.B.foo", "A.Str", "root_thing"])
        self.assertTrue(lex.is_local("A.B.foo"))
        self.assertTrue(lex.is_local("A.B.foo._proof_1_2"))
        self.assertTrue(lex.is_local("A.Str.mk"))
        self.assertTrue(lex.is_local("_private.Some.Module.0.A.B.foo"))
        self.assertFalse(lex.is_local("A.B"))
        self.assertFalse(lex.is_local("Nat.add_comm"))
        self.assertEqual(lex.resolve_source("foo", "A.B"), "A.B.foo")
        self.assertEqual(lex.resolve_source("B.foo", "A.C"), "A.B.foo")
        self.assertEqual(lex.resolve_source("Str.mk", "", ["A"]), "A.Str")
        self.assertIsNone(lex.resolve_source("foo", "X"))
        self.assertEqual(lex.resolve_source("_root_.root_thing", "X.Y"), "root_thing")
        self.assertEqual(lex.id, hashlib.sha256(b"A.B.foo\nA.Str\nroot_thing\n").hexdigest()[:16])


FILE = """import Lib

open Lib.Tools

namespace Outer.Inner

variable {R : Type} [Ring R] (n : ℕ) (unused : ℤ)

theorem first (x : R) : x + 0 = x := by
  simp

section
variable (k : ℕ)
theorem second : k + n = n + k := by
  omega
end

theorem _root_.Elsewhere.third : True := trivial

private def helper (m : ℕ) : ℕ :=
  m + 1

end Outer.Inner

namespace Outer
open Lib.More in
lemma fourth : helper 1 = 2 := rfl
instance : Inhabited ℕ := ⟨0⟩
example : True := trivial
structure Pt where
  x : ℕ
end Outer
theorem top_level : True := trivial
"""


class SourceScanTests(unittest.TestCase):
    def test_scopes_names_and_variables(self):
        decls = {d["name"]: d for d in S.iter_source_decls(FILE)}
        self.assertEqual(sorted(decls), sorted([
            "Outer.Inner.first", "Outer.Inner.second", "Elsewhere.third", "Outer.Inner.helper",
            "Outer.fourth", "Outer.Pt", "top_level"]))
        j = lambda groups: [" ".join(g) for g in groups]
        self.assertEqual(j(decls["Outer.Inner.first"]["var_binders"]), ["( R : Type )", "[ _ : Ring R ]"])
        self.assertEqual(j(decls["Outer.Inner.second"]["var_binders"]), ["( n : Nat )", "( k : Nat )"])
        self.assertEqual(decls["top_level"]["var_binders"], [])
        self.assertEqual(decls["Outer.fourth"]["opens"], ["Lib.Tools", "Lib.More"])
        self.assertEqual(decls["Outer.Pt"]["opens"], ["Lib.Tools"])
        self.assertEqual(decls["Outer.Inner.first"]["line"], 9)
        fast = [d["name"] for d in S.iter_source_decls(FILE, with_sig=False)]
        self.assertEqual(fast, [d["name"] for d in S.iter_source_decls(FILE)])

    def test_file_level_hashes_use_variables(self):
        rows = {r["name"]: r for r in S.source_decl_hashes(FILE)}
        direct = S.source_sig(["{R : Type}", "[Ring R]", "(x : R)"], "x + 0 = x")
        self.assertEqual(rows["Outer.Inner.first"]["s1n"], direct["s1n"])

    def test_header_never_contains_body(self):
        for d in S.iter_source_decls(FILE):
            flat = [t for b in d["binders"] for t in b] + d["type"]
            for forbidden in ("simp", "omega", "trivial", "rfl"):
                self.assertNotIn(forbidden, flat)


@unittest.skipUnless(os.environ.get("LEANRE_SLOW") == "1"
                     and os.path.exists(os.path.join(REPO, "data", "challenge.ndjson.zst")),
                     "set LEANRE_SLOW=1 (needs data/challenge.ndjson.zst)")
class ChallengeRegression(unittest.TestCase):
    EXPECT_CONSTANTS = 53722
    EXPECT_SHA_NOLEX = "1c0b8c380ae14e89398f4837fdcd77df1716b1ee1fb2d54d68197848e1e1767e"

    def test_challenge_tsv_sha(self):
        sha = hashlib.sha256()
        n = 0
        for r in S.kernel_sighashes(os.path.join(REPO, "data", "challenge.ndjson.zst")):
            sha.update((S.kernel_tsv_line(r) + "\n").encode("utf-8"))
            n += 1
        self.assertEqual(n, self.EXPECT_CONSTANTS)
        self.assertEqual(sha.hexdigest(), self.EXPECT_SHA_NOLEX)


if __name__ == "__main__":
    unittest.main(verbosity=2)
