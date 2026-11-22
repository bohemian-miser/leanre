#!/usr/bin/env python3
"""Tests for FLIRT Tier 2 (cross-repo signature matching).

    python3 -m unittest discover -s leanre -v          # whole suite
    python3 -m unittest leanre/test_tier2.py -v        # just this file (from repo root)

Synthetic fixtures only (clearly fake Lean snippets written here); the real-data class is
skipped when outputs/flirt/tier2.db has not been built.
"""
from __future__ import annotations

import json
import os
import random
import sqlite3
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
for p in (HERE, os.path.join(HERE, "flirt")):
    if p not in sys.path:
        sys.path.insert(0, p)

import tier2  # noqa: E402
import tier2_corpora  # noqa: E402
import tier2_kernel  # noqa: E402
import tier2_sig  # noqa: E402
from tier2_extract import extract_decls, split_header, strip_comments  # noqa: E402

SYNTH = '''
/- block comment with theorem fake : False := sorry -/
universe u
namespace Foo
variable {R : Type u} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] {n m : ℕ}
variable (R)

/-- doc mentioning := and theorem -/
@[simp]
theorem bar (x : R) (h : x = 0 := by simp) :
    x * 1 = x := by
  simp -- trailing comment
omit [CommRing R] in
lemma baz : n + 0 = n := rfl
protected def qux (y : M) : M := y + (0 : M)
instance (priority := 100) inst1 : Inhabited ℕ := ⟨0⟩
instance : Inhabited ℕ := ⟨0⟩
theorem pm : ∀ k : ℕ, k = k
  | 0 => rfl
  | _ + 1 => rfl
theorem absval (a : ℤ) :
    |a| = |a| := rfl
theorem bnd (s : Finset ℕ) : ∀ n ∈ s, n = n := fun _ _ => rfl
structure S (α : Type) where
  x : α
end Foo
theorem _root_.top (a : ℕ) : a = a := rfl
'''


def _by_name(text):
    return {d["name"]: d for d in extract_decls(text)}


class ExtractTest(unittest.TestCase):
    def setUp(self):
        self.d = _by_name(SYNTH)

    def test_names_and_namespaces(self):
        for nm in ("Foo.bar", "Foo.baz", "Foo.qux", "Foo.inst1", "Foo.pm", "Foo.absval",
                   "Foo.S", "top"):
            self.assertIn(nm, self.d)
        self.assertNotIn("fake", self.d)           # inside a comment
        self.assertEqual(len(self.d), 9)           # anonymous instance skipped

    def test_variable_inclusion(self):
        # `variable (R)` flips the binder kind; [CommRing R] follows R; M/n/m not mentioned
        self.assertEqual(self.d["Foo.bar"]["var_binders"], ["(R : Type u)", "[CommRing R]"])
        self.assertEqual(self.d["Foo.baz"]["var_binders"], ["{n : ℕ}"])
        self.assertEqual(self.d["Foo.qux"]["var_binders"], ["(M : Type*)", "[AddCommGroup M]"])
        # `∀ n ∈ s` binds its own n: the section variable n is NOT included
        self.assertEqual(self.d["Foo.bnd"]["var_binders"], [])

    def test_no_proof_body_ever(self):
        for d in self.d.values():
            blob = " ".join(d["var_binders"] + d["own_binders"]) + d["type"]
            for leak in ("simp", "rfl", "⟨0⟩", "=>", "trailing"):
                if d["name"] == "Foo.bar" and leak == "simp":
                    continue  # `(h : x = 0 := by simp)` default value is part of the header
                self.assertNotIn(leak, blob, (d["name"], leak))

    def test_header_cut_points(self):
        self.assertEqual(self.d["Foo.bar"]["type"], "x * 1 = x")
        self.assertEqual(self.d["Foo.pm"]["type"], "∀ k : ℕ, k = k")       # match-alternatives cut
        self.assertEqual(self.d["Foo.absval"]["type"], "|a| = |a|")        # |a| is not an alternative
        self.assertEqual(self.d["Foo.inst1"]["type"], "Inhabited ℕ")
        self.assertEqual(split_header(" (x : Nat := 3) : x = x := rfl")[0].strip(),
                         "(x : Nat := 3) : x = x")

    def test_strip_comments_keeps_lines(self):
        s = "a -- c\n/- x\n y -/ b \"--not\"\n"
        out = strip_comments(s)
        self.assertEqual(out.count("\n"), s.count("\n"))
        self.assertIn('"--not"', out)
        self.assertNotIn("c", out.split("\n")[0])


class SigHashTest(unittest.TestCase):
    def h(self, binders, ty):
        return tier2_sig.sig_hashes(binders, ty)

    def test_invariances(self):
        base = self.h(["{α : Type u}", "(l : List α)", "(h : l ≠ [])"], "0 < l.length")
        same = [
            (["(β : Type v)", "{xs : List β}", "{hne : xs ≠ []}"], "0 < xs.length"),   # names, kinds, universe
            (["{α : Type u}", "(l : List α)", "(h   :   l ≠ [])"], "0 <\n   l.length"),  # whitespace
        ]
        for b, t in same:
            self.assertEqual(self.h(b, t).s1n, base.s1n)
        self.assertEqual(self.h(["{a b : ℕ}"], "a + b = b + a").s1n,
                         self.h(["{x : ℕ}", "{y : ℕ}"], "x + y = y + x").s1n)

    def test_sensitivity(self):
        base = self.h(["(a b : ℕ)"], "a + b = b + a")
        self.assertNotEqual(base.s1n, self.h(["(a b : ℕ)"], "a + b = a + b").s1n)   # binding structure
        self.assertNotEqual(base.s1n, self.h(["(a b : ℤ)"], "a + b = b + a").s1n)   # constant
        self.assertNotEqual(base.s1n, self.h(["(a b : ℕ)"], "a * b = b * a").s1n)

    def test_last_component_variant(self):
        a = self.h(["(l : List ℕ)"], "List.length l = l.length")
        b = self.h(["(l : List ℕ)"], "length l = l.length")
        self.assertNotEqual(a.s1n, b.s1n)
        self.assertEqual(a.s1t, b.s1t)

    def test_scheme_tag_and_width(self):
        a = self.h(["(a : ℕ)"], "a = a")
        for x in (a.s1n, a.s1t, a.s1a):
            scheme, _, hexpart = x.partition(":")
            self.assertRegex(scheme, r"^s[01][nta]$")
            self.assertRegex(hexpart, r"^[0-9a-f]{32}$")
        self.assertGreater(a.n_tokens, 0)
        self.assertEqual(a.n_local, 0)

    def test_name_independent_s1a(self):
        # Two different local defs abstracted via per-repo resolvers produce identical s1a
        res_a = lambda tok: "ProjA.myNorm" if tok in ("myNorm", "ProjA.myNorm") else None
        res_b = lambda tok: "ProjB.theirNorm" if tok in ("theirNorm", "ProjB.theirNorm") else None
        ha = tier2_sig.sig_hashes(["(x : ℝ)"], "0 ≤ myNorm x", resolve=res_a)
        hb = tier2_sig.sig_hashes(["(y : ℝ)"], "0 ≤ theirNorm y", resolve=res_b)
        self.assertNotEqual(ha.s1n, hb.s1n)
        self.assertNotEqual(ha.s1t, hb.s1t)
        self.assertEqual(ha.s1a, hb.s1a)
        self.assertEqual((ha.n_local, hb.n_local), (1, 1))

    def test_restatement_is_hash_stable(self):
        rng = random.Random(7)
        n = 0
        for d in extract_decls(SYNTH):
            if d["kind"] not in ("theorem", "lemma"):
                continue
            want = self.h(d["var_binders"] + d["own_binders"], d["type"])
            for trial in range(8):
                text = tier2.restate(d, 1000 + trial, rng)
                got = [x for x in extract_decls(text) if x["short"].startswith("restated_")]
                self.assertEqual(len(got), 1, text)
                g = got[0]
                self.assertNotEqual(g["name"], d["name"])
                self.assertEqual(self.h(g["var_binders"] + g["own_binders"], g["type"]).s1n,
                                 want.s1n, (d["name"], text))
                n += 1
        self.assertGreaterEqual(n, 40)


CORPUS_A = '''
namespace Lib
variable {α : Type*} [LinearOrder α]
def libHelper (x : ℝ) : ℝ := x
theorem max_comm' (a b : α) : max a b = max b a := by simp [max_comm]
theorem long_one (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (N : ℕ) : 0 ≤ ∑ i ∈ Finset.range N, f i := by positivity
theorem local_shape (x y : ℝ) (hx : 0 ≤ x) : libHelper (x + y) = libHelper x + libHelper y := by sorry
def width (x : ℝ) : ℝ := x
end Lib
'''
PROOF_A = '''
namespace Proj.Deep
def projHelper (z : ℝ) : ℝ := z
theorem renamed_copy {β : Type*} [LinearOrder β] (x y : β) : max x y = max y x := by
  exact max_comm x y
theorem same_long (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (M : ℕ) : 0 ≤ ∑ j ∈ Finset.range M, g j := by
  positivity
theorem renamed_local_shape (u v : ℝ) (hu : 0 ≤ u) : projHelper (u + v) = projHelper u + projHelper v := by sorry
theorem novel (g : ℕ → ℝ) (M : ℕ) : projLocalThing g M = 0 := by sorry
def breadth (t : ℝ) : ℝ := t + 1
end Proj.Deep
'''
PROOF_B = "theorem other (a b c : ℕ) : a + b + c = c + b + a := by omega\n" \
          "theorem other2 (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩\n"


class EndToEndTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        t = cls.tmp.name
        os.makedirs(os.path.join(t, "corpus", "Lib"))
        os.makedirs(os.path.join(t, "proof", "Proj"))
        with open(os.path.join(t, "corpus", "Lib", "A.lean"), "w", encoding="utf-8") as f:
            f.write(CORPUS_A)
        with open(os.path.join(t, "proof", "Proj", "A.lean"), "w", encoding="utf-8") as f:
            f.write(PROOF_A)
        with open(os.path.join(t, "proof", "Proj", "B.lean"), "w", encoding="utf-8") as f:
            f.write(PROOF_B)
        cls.db = os.path.join(t, "tier2.db")
        cls.commit = "a" * 40
        tier2.build(cls.db, threads=2, mirror_src=os.path.join(t, "proof"), verbose=False, corpora=[{
            "name": "synthlib", "url": "https://example.invalid/synthlib", "commit": cls.commit,
            "license": "Apache-2.0", "root": os.path.join(t, "corpus"), "subdirs": ["Lib"]}])
        cls.conn = sqlite3.connect(cls.db)

    @classmethod
    def tearDownClass(cls):
        cls.conn.close()
        cls.tmp.cleanup()

    def q(self, sql, *a):
        return self.conn.execute(sql, a).fetchall()

    def test_matches_have_evidence(self):
        rows = dict(self.q(
            "SELECT p.name, m.corpus_name FROM matches m JOIN proof_sigs p ON p.id=m.proof_id "
            "WHERE m.variant='s1n'"))
        self.assertEqual(rows.get("Proj.Deep.renamed_copy"), "Lib.max_comm'")
        self.assertEqual(rows.get("Proj.Deep.same_long"), "Lib.long_one")
        self.assertNotIn("Proj.Deep.renamed_local_shape", rows)   # different local constant name
        self.assertNotIn("Proj.Deep.novel", rows)
        self.assertNotIn("other", rows)
        # s1a matches renamed_local_shape -> Lib.local_shape via per-repo lexicon abstraction
        rows_a = dict(self.q(
            "SELECT p.name, m.corpus_name FROM matches m JOIN proof_sigs p ON p.id=m.proof_id "
            "WHERE m.variant='s1a'"))
        self.assertEqual(rows_a.get("Proj.Deep.renamed_local_shape"), "Lib.local_shape")
        for repo, commit, lic, sighash, prov in self.q(
                "SELECT repo, commit_sha, license, sighash, provenance FROM matches"):
            self.assertEqual((repo, commit, lic, prov), ("synthlib", self.commit, "Apache-2.0", "L"))
            self.assertRegex(sighash, r"^s[01][nta]:[0-9a-f]{32}$")
        self.assertEqual(self.q("SELECT COUNT(*) FROM matches m LEFT JOIN match_candidates c "
                                "USING (proof_id, variant) WHERE c.corpus_id IS NULL"), [(0,)])
        # matches_view exposes joined evidence for workbench
        v_cnt = self.q("SELECT COUNT(*) FROM matches_view")[0][0]
        self.assertEqual(v_cnt, self.q("SELECT COUNT(*) FROM matches")[0][0])

    def test_defs_are_never_strong(self):
        g = self.q("SELECT m.grade FROM matches m JOIN proof_sigs p ON p.id=m.proof_id "
                   "WHERE p.name='Proj.Deep.breadth'")
        self.assertTrue(g and all(x == ("defsig",) for x in g))
        self.assertEqual(self.q("SELECT COUNT(*) FROM matches m JOIN proof_sigs p ON "
                                "p.id=m.proof_id WHERE m.grade IN ('strong','weak') AND "
                                "p.kind NOT IN ('theorem','lemma')"), [(0,)])

    def test_no_proof_text_stored(self):
        cols = [r[1] for r in self.q("PRAGMA table_info(proof_sigs)")]
        self.assertEqual(cols, ["id", "module", "line_no", "kind", "name",
                                "s1n", "s1t", "s1a", "n_tokens", "n_local"])
        dump = "\n".join(self.conn.iterdump())
        for leak in ("projLocalThing", "omega", "exact max_comm x y"):
            self.assertNotIn(leak, dump)

    def test_controls_recorded(self):
        kinds = {r[0] for r in self.q("SELECT DISTINCT control FROM controls")}
        self.assertEqual(kinds, {"neg_swap", "neg_perm", "fdr_estimate", "restate_selfmatch"})
        n, tp, fp, fn = self.q("SELECT n, tp, fp, fn FROM controls WHERE "
                               "control='restate_selfmatch' AND variant='s1n' AND min_tokens=1")[0]
        self.assertEqual(n, tp + fp + fn)
        # negative-control signatures must differ from the originals they were built from
        self.assertEqual(self.q("SELECT COUNT(*) FROM control_sigs c JOIN proof_sigs p ON "
                                "p.id=c.proof_id WHERE c.s1n=p.s1n"), [(0,)])

    def test_summary_wording(self):
        s = tier2.summary(self.db, out_path=None)
        self.assertIn("NOT evidence that the same mathematics is proved", s["meaning_of_a_match"])
        self.assertTrue(s["provenance"].startswith("[L]"))
        json.dumps(s)

    def test_deterministic_rebuild(self):
        db2 = os.path.join(self.tmp.name, "again.db")
        t = self.tmp.name
        tier2.build(db2, threads=1, mirror_src=os.path.join(t, "proof"), verbose=False, corpora=[{
            "name": "synthlib", "url": "https://example.invalid/synthlib", "commit": self.commit,
            "license": "Apache-2.0", "root": os.path.join(t, "corpus"), "subdirs": ["Lib"]}])
        c2 = sqlite3.connect(db2)
        for tbl in ("corpus_sigs", "proof_sigs", "matches", "control_sigs", "controls"):
            self.assertEqual(self.q(f"SELECT * FROM {tbl} ORDER BY 1,2,3"),
                             c2.execute(f"SELECT * FROM {tbl} ORDER BY 1,2,3").fetchall(), tbl)
        c2.close()


class KernelMatchTest(unittest.TestCase):
    """End-to-end test of tier2_kernel against a synthetic kernel.db matching docs/KERNEL.md."""

    def test_kernel_matching_and_ground_truth_controls(self):
        with tempfile.TemporaryDirectory() as t:
            os.makedirs(os.path.join(t, "corpus", "Mathlib"))
            os.makedirs(os.path.join(t, "proof", "Proj"))
            with open(os.path.join(t, "corpus", "Mathlib", "A.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Nat\n"
                    "theorem add_comm_m (a b : ℕ) : a + b = b + a := by omega\n"
                    "theorem mul_comm_m (a b : ℕ) : a * b = b * a := by omega\n"
                    "theorem ambiguous_m (a : ℕ) : foo a = a := rfl\n"
                    "end Nat\n"
                )
            with open(os.path.join(t, "proof", "Proj", "A.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Proj\n"
                    "theorem my_add_comm (x y : ℕ) : x + y = y + x := by omega\n"
                    "theorem my_mul_rephrased (x y : ℕ) : y * x = x * y := by omega\n"
                    "theorem my_ambiguous (z : ℕ) : foo z = z := rfl\n"
                    "theorem my_novel (z : ℕ) : z + 42 = 42 + z := by omega\n"
                    "end Proj\n"
                )
            tdb = os.path.join(t, "tier2.db")
            kdb = os.path.join(t, "kernel.db")
            tier2.build(tdb, threads=1, mirror_src=os.path.join(t, "proof"), verbose=False, corpora=[{
                "name": "mathlib4", "url": "https://example.invalid/m", "commit": "b" * 40,
                "license": "Apache-2.0", "root": os.path.join(t, "corpus"), "subdirs": ["Mathlib"]}])
            # Build synthetic kernel.db matching kernel's schema (#12)
            kc = sqlite3.connect(kdb)
            kc.executescript("""
                CREATE TABLE meta (key TEXT PRIMARY KEY, value_json TEXT NOT NULL);
                CREATE TABLE decls (id INTEGER PRIMARY KEY, name TEXT UNIQUE, kind TEXT,
                    type_nodes INTEGER, live_mask INTEGER, stmt_mask INTEGER,
                    sighash TEXT, sighash_anon TEXT);
                CREATE TABLE consts (name TEXT PRIMARY KEY, decl_id INTEGER, ckind TEXT,
                    sighash TEXT, sighash_anon TEXT);
                CREATE TABLE decl_module (decl_id INTEGER PRIMARY KEY, module TEXT,
                    method TEXT, src_decl_id INTEGER);
            """)
            kc.execute("INSERT INTO meta VALUES ('schema_version', '1')")
            k_add = "k1n:" + "1" * 32
            k_mul = "k1n:" + "2" * 32
            k_amb_lib = "k1n:" + "3" * 32
            k_amb_proj = "k1n:" + "4" * 32  # same source text, DIFFERENT kernel type -> source FP!
            k_nov = "k1n:" + "5" * 32
            k_nov_a = "k1a:" + "6" * 32
            rows_d = [
                (0, "Nat.add_comm_m", "thm", 20, 1, 0, k_add, "k1a:" + "1" * 32),
                (1, "Nat.mul_comm_m", "thm", 22, 1, 0, k_mul, "k1a:" + "2" * 32),
                (2, "Nat.ambiguous_m", "thm", 15, 1, 0, k_amb_lib, "k1a:" + "3" * 32),
                (3, "Proj.my_add_comm", "thm", 20, 1, 0, k_add, "k1a:" + "1" * 32),
                (4, "Proj.my_mul_rephrased", "thm", 22, 1, 0, k_mul, "k1a:" + "2" * 32),
                (5, "Proj.my_ambiguous", "thm", 15, 1, 0, k_amb_proj, "k1a:" + "4" * 32),
                (6, "Proj.my_novel", "thm", 18, 1, 0, k_nov, k_nov_a),
            ]
            kc.executemany("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?)", rows_d)
            kc.executemany("INSERT INTO consts VALUES (?,?,?,?,?)",
                           [(r[1], r[0], r[2], r[6], r[7]) for r in rows_d])
            kc.executemany("INSERT INTO decl_module VALUES (?,?,?,?)", [
                (0, None, "unmatched:mathlib", None),
                (1, None, "unmatched:mathlib", None),
                (2, None, "unmatched:mathlib", None),
                (3, "Proj.A", "exact", 1),
                (4, "Proj.A", "exact", 2),
                (5, "Proj.A", "exact", 3),
                (6, "Proj.A", "exact", 4),
            ])
            kc.commit()
            kc.close()

            res = tier2_kernel.run(tdb, kdb, verbose=False)
            self.assertEqual(res["matches"]["k1n_thm_all"]["project_consts"], 2)
            # Recall: 2 kernel-identical pairs (my_add_comm + my_mul_rephrased); source caught 1/2
            by_ctl = {(c["control"], c["variant"], c["min_tokens"]): c for c in res["controls"]}
            rec = by_ctl[("kernel_source_recall", "s1t", 0)]
            self.assertEqual((rec["n"], rec["tp"], rec["fn"]), (2, 1, 1))
            self.assertAlmostEqual(rec["recall"], 0.5)
            # Precision: 2 source matches both in kernel.db (my_add_comm TP, my_ambiguous FP) -> 1/2
            prec = by_ctl[("kernel_source_precision", "s1t_all", 0)]
            self.assertEqual((prec["n"], prec["tp"], prec["fp"]), (2, 1, 1))
            self.assertAlmostEqual(prec["precision"], 0.5)
            # Coverage: all 3 library theorems found in mathlib4 corpus
            cov = by_ctl[("kernel_lib_coverage", "thm_only", 0)]
            self.assertEqual((cov["n"], cov["tp"]), (3, 3))
            # Summary embeds kernel block cleanly
            s = tier2.summary(tdb, out_path=None)
            self.assertIn("kernel", s)
            self.assertEqual(s["kernel"]["matches"]["k1n_thm_all"]["project_consts"], 2)


@unittest.skipUnless(os.path.exists(tier2.DB_PATH) and os.path.exists(tier2_corpora.MANIFEST),
                     "outputs/flirt/tier2.db not built")
class RealDataTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.conn = sqlite3.connect("file:%s?mode=ro" % tier2.DB_PATH, uri=True)

    @classmethod
    def tearDownClass(cls):
        cls.conn.close()

    def one(self, sql, *a):
        return self.conn.execute(sql, a).fetchone()[0]

    def test_mathlib_pin_is_the_proofs_pin(self):
        with open(tier2_corpora.MANIFEST, encoding="utf-8") as f:
            man = json.load(f)
        rows = {c["name"]: c for c in man["corpora"]}
        self.assertEqual(rows["mathlib4"]["commit"], man["proof_mirror"]["mathlib_rev"])
        if os.path.exists(os.path.join(tier2_corpora.MIRROR, "lake-manifest.json")):
            self.assertEqual(rows["mathlib4"]["commit"], tier2_corpora.proof_pins()["mathlib"])
        for c in man["corpora"]:
            self.assertRegex(c["commit"], r"^[0-9a-f]{40}$")
            self.assertNotEqual(c["license"], "UNKNOWN")
            self.assertEqual(self.one("SELECT commit_sha FROM corpora WHERE repo=?", c["name"]),
                             c["commit"])
        for need in ("mathlib4", "PrimeNumberTheoremAnd", "FLT", "carleson"):
            self.assertIn(need, rows)

    def test_every_match_carries_evidence(self):
        self.assertEqual(self.one(
            "SELECT COUNT(*) FROM matches m LEFT JOIN corpus_sigs s ON s.id=m.corpus_id "
            "LEFT JOIN corpora c ON c.repo=m.repo WHERE s.id IS NULL OR c.repo IS NULL OR "
            "m.commit_sha<>c.commit_sha OR m.license<>c.license OR m.provenance<>'L' OR "
            "(m.variant='s1n' AND m.sighash<>s.s1n) OR "
            "(m.variant='s1t' AND m.sighash<>s.s1t) OR "
            "(m.variant='s1a' AND m.sighash<>s.s1a)"), 0)
        self.assertEqual(self.one(
            "SELECT COUNT(*) FROM matches m JOIN proof_sigs p ON p.id=m.proof_id WHERE "
            "m.grade='strong' AND p.kind NOT IN ('theorem','lemma')"), 0)

    def test_proof_side_is_complete_and_textless(self):
        self.assertEqual(json.loads(self.one("SELECT value_json FROM meta WHERE key='proof_files'")),
                         175187)
        cols = [r[1] for r in self.conn.execute("PRAGMA table_info(proof_sigs)")]
        self.assertNotIn("sig_text", cols)

    def test_controls_are_present_and_consistent(self):
        for control in ("neg_swap", "neg_perm", "restate_selfmatch", "fdr_estimate"):
            self.assertGreater(self.one("SELECT COUNT(*) FROM controls WHERE control=?", control), 0)
        T_map = json.loads(self.one("SELECT value_json FROM meta WHERE key='strong_min_tokens_by_variant'"))
        tgt = json.loads(self.one("SELECT value_json FROM meta WHERE key='fdr_target'"))
        for var, T in T_map.items():
            if self.one("SELECT COUNT(*) FROM matches WHERE variant=? AND grade='strong'", var):
                fdr = self.one("SELECT fpr FROM controls WHERE control='fdr_estimate' "
                               "AND variant=? AND min_tokens=?", var, T)
                self.assertLessEqual(fdr, tgt)
        self.assertEqual(self.one("SELECT COUNT(*) FROM controls WHERE control='restate_selfmatch' "
                                  "AND n <> tp+fp+fn"), 0)

    def test_kernel_matches_if_populated(self):
        has_km = self.one(
            "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='kernel_matches'")
        if not has_km:
            self.skipTest("kernel_matches not yet populated (run tier2.py kernel)")
        self.assertGreater(self.one("SELECT COUNT(*) FROM kernel_matches WHERE variant='k1n'"), 0)
        # Every kernel match has valid k1n/k1a sighash, provenance 'L', and pinned commit when lib_repo set
        self.assertEqual(self.one(
            "SELECT COUNT(*) FROM kernel_matches WHERE provenance<>'L' "
            "OR (variant='k1n' AND sighash NOT LIKE 'k1n:%') "
            "OR (variant='k1a' AND sighash NOT LIKE 'k1a:%') "
            "OR (lib_repo IS NOT NULL AND lib_commit_sha IS NULL)"), 0)
        for ctl in ("kernel_lib_coverage", "kernel_source_recall", "kernel_source_precision"):
            self.assertGreater(self.one("SELECT COUNT(*) FROM controls WHERE control=?", ctl), 0)
        # No compiler-generated ._proof_ or ._simp_ marked as is_aux=0
        self.assertEqual(self.one(
            "SELECT COUNT(*) FROM kernel_matches WHERE is_aux=0 AND "
            "(instr(const_name, '._proof_') > 0 OR instr(const_name, '._simp_') > 0)"), 0)


if __name__ == "__main__":
    unittest.main()
