"""Tests for leanre/decompile (gate D1).  Run: python3 -m unittest leanre.test_decompile -v
(or `python3 -m unittest discover -s leanre -p 'test_decompile.py' -v`).
Real-DB spot checks are skipped when outputs/kernel/kernel.db or data/rh_mirror/src are absent."""
from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from decompile import schema  # noqa: E402
from decompile.kdb import DEFAULT_KERNEL_DB, DEFAULT_SRC  # noqa: E402
from decompile.source import read_contract, strip_comments, one_line, split_header, scope_at  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HAVE_DB = os.path.exists(DEFAULT_KERNEL_DB) and os.path.isdir(DEFAULT_SRC)

LEAN = """import Mathlib

/-! module doc -/
namespace Foo.Bar

variable {E : Type} [Field E]

/-- a docstring mentioning theorem fake : False -/
def Good (n : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ n → -- trailing comment
    m < n + 1

structure Pack (x : E) : Prop where
  first : Good 3
  second (k : ℕ) : k = k ∧
    Good k
  dflt : True := trivial

inductive Col where
  | red : Col
  | blue (n : ℕ) : Col

variable (z : ℕ) in
theorem good_three (h : Good 2) : Good 3 := by
  intro m hm
  omega

theorem secret_proof : Good 1 :=
  fun m hm => by omega

end Bar
end Foo
"""


class TestSource(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.root = cls.tmp.name
        os.makedirs(os.path.join(cls.root, "Foo"))
        with open(os.path.join(cls.root, "Foo", "Bar.lean"), "w") as f:
            f.write(LEAN)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def rc(self, name):
        c = read_contract(self.root, "Foo/Bar.lean", name)
        self.assertIsNotNone(c, name)
        return c

    def test_strip_comments_keeps_lines(self):
        s = strip_comments("a -- x\n/- b\n c -/d\n")
        self.assertEqual(s.count("\n"), 3)
        self.assertNotIn("x", s)
        self.assertIn("d", s)

    def test_def_header_and_body(self):
        c = self.rc("Foo.Bar.Good")
        self.assertEqual(c.keyword, "def")
        self.assertEqual(c.header, "def Good (n : ℕ) : Prop")
        self.assertEqual(c.type, "Prop")
        self.assertEqual(c.binders, ["(n : ℕ)"])
        self.assertEqual(c.body, "∀ m : ℕ, m ≤ n → m < n + 1")
        self.assertEqual(c.namespace, "Foo.Bar")
        self.assertEqual(c.variables, ["{E : Type} [Field E]"])
        self.assertTrue(c.anchor.startswith("src/Foo/Bar.lean:"))

    def test_docstring_decl_not_matched(self):
        self.assertIsNone(read_contract(self.root, "Foo/Bar.lean", "Foo.Bar.fake"))

    def test_structure_fields(self):
        c = self.rc("Foo.Bar.Pack")
        self.assertEqual(c.keyword, "structure")
        self.assertEqual([f.name for f in c.fields], ["first", "second", "dflt"])
        self.assertEqual(c.fields[1].type, "(k : ℕ) → k = k ∧ Good k")
        self.assertTrue(c.fields[2].default)
        self.assertEqual(c.fields[2].type, "True")

    def test_inductive_ctors(self):
        c = self.rc("Foo.Bar.Col")
        self.assertEqual([f.name for f in c.fields], ["red", "blue"])

    def test_theorem_never_returns_proof(self):
        for n in ("Foo.Bar.good_three", "Foo.Bar.secret_proof"):
            c = self.rc(n)
            self.assertIsNone(c.body)
            js = json.dumps(c.to_json(with_body=True))
            self.assertNotIn("omega", js)
        c = self.rc("Foo.Bar.good_three")
        self.assertEqual(c.header, "theorem good_three (h : Good 2) : Good 3")
        self.assertIn("(z : ℕ) (variable … in)", c.variables)

    def test_split_header_extends(self):
        kw, name, b, t, ext = split_header("structure S (x : ℕ) extends A x, B : Prop")
        self.assertEqual((kw, name, b, t, ext), ("structure", "S", ["(x : ℕ)"], "Prop", ["A x", "B"]))

    def test_one_line(self):
        self.assertEqual(one_line("a\n  b"), "a b")
        self.assertEqual(len(one_line("x" * 1000, 50)), 50)


class TestSchema(unittest.TestCase):
    def good(self):
        d = json.loads(json.dumps(schema.TEMPLATE))
        d["root"] = "allChi"
        d["nodes"] = [{"id": "allChi", "kid": 1468387, "kind": "thm", "module": "M", "anchor": "src/A/B.lean:7",
                       "header": "theorem allChi : X", "dom": {"depth": 0, "subtree": 5, "idom": None},
                       "role": "theorem", "status": "READ", "verdict": "real", "tag": "L", "summary": "s",
                       "fields": []},
                      {"id": "X", "kind": "def", "role": "contract", "status": "OPAQUE", "verdict": "unknown",
                       "tag": "L", "summary": "", "fields": []}]
        d["edges"] = [{"src": "allChi", "dst": "X", "rel": "type", "tag": "L"}]
        d["horn"] = [{"concl": "X", "hyps": [], "via": "allChi", "tag": "L"}]
        d["claims"] = [{"text": "t", "tag": "L", "anchors": [], "nodes": ["allChi"]}]
        d["opaque"] = ["X"]
        return d

    def test_valid(self):
        self.assertEqual(schema.validate(self.good()), [])

    def test_errors(self):
        d = self.good(); d["nodes"][0]["tag"] = "Q"
        self.assertTrue(any(".tag" in e for e in schema.validate(d)))
        d = self.good(); d["nodes"][0]["header"] = "theorem x :=\n  by simp"
        self.assertTrue(any("multi-line" in e for e in schema.validate(d)))
        d = self.good(); d["opaque"] = []
        self.assertTrue(any("OPAQUE nodes missing" in e for e in schema.validate(d)))
        d = self.good(); d["edges"][0]["rel"] = "uses"
        self.assertTrue(any("bad rel" in e for e in schema.validate(d)))
        d = self.good(); d["schema"] = "v0"
        self.assertTrue(schema.validate(d))


class TestCLIHook(unittest.TestCase):
    def test_register_cli(self):
        from decompile.cli import register_cli
        ap = argparse.ArgumentParser()
        sub = ap.add_subparsers(dest="cmd")
        register_cli(sub)
        a = ap.parse_args(["decompile", "unfold", "allChi", "--depth", "3"])
        self.assertEqual((a.cmd, a.decompile_cmd, a.name, a.depth), ("decompile", "unfold", "allChi", 3))
        self.assertTrue(callable(a.decompile_func))


@unittest.skipUnless(HAVE_DB, "kernel.db / rh_mirror not available")
class TestRealDB(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from decompile import Decompiler
        cls.D = Decompiler()
        cls.k = cls.D.kdb

    def test_ro(self):
        with self.assertRaises(Exception):
            self.k.k.execute("CREATE TABLE _x(a)")

    def test_top_spine_counts(self):
        ec = self.k.decl("UpperTheory.FinalTheorems.everyCharacter")
        self.assertEqual(self.k.dom(ec).subtree_size, 1_409_556)
        self.assertEqual(self.k.dom("allChi").subtree_size, 1_409_557)
        st = self.k.dom_child_stats(ec)
        self.assertEqual(st["children"], 110_900)
        self.assertEqual(st["children_subtree_total"], 1_409_555)
        row = self.k.dom("UpperTheory.FinalTheorems.everyCharacter_of_row").subtree_size
        gal = self.k.dom("UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter").subtree_size
        self.assertEqual((row, gal), (982_855, 95_102))
        self.assertEqual(st["children_subtree_total"] - row - gal, 331_598)
        n_all = self.k.k.execute("SELECT n_nodes FROM dom_trees WHERE label='ALL'").fetchone()[0]
        self.assertEqual(n_all - 1_409_557, 58_857)

    def test_contracts(self):
        c = self.D.contract("UpperTheory.FinalTheorems.everyCharacter_of_row")
        self.assertIn("Row0b", c.header)
        self.assertEqual(c.type, "UpperTheory.EveryCharacter")
        self.assertIsNone(c.body)
        c = self.D.contract("UpperTheory.LiteratureTheorems.OpenLiteratureStatements")
        self.assertEqual([f.name for f in c.fields],
                         ["caraianiLocalGlobalDual", "localLanglandsExists", "galoisRepOfPolarizedPairLit"])
        c = self.D.contract("UpperTheory.Gal.Int.recT")
        self.assertEqual(" ".join(c.body.split()), "fun h rc => UpperTheory.Zero.LLC.IsRecT h rc")
        self.assertIsNone(self.D.contract("RiemannHypothesis"))  # Mathlib ground

    def test_horn(self):
        h = self.D.horn("UpperTheory.FinalTheorems.everyCharacter_of_row")
        self.assertIn("UpperTheory.GalStar.Row0b", h["hyps"])
        self.assertEqual(h["concl"], ["UpperTheory.EveryCharacter"])
        self.assertEqual(h["lemmas_project"], ["UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
                                               "UpperTheory.One.vwin_of_row", "UpperTheory.Zero.LLC.recTExists"])

    def test_unfold_reaches_ground(self):
        u = self.D.unfold("UpperTheory.EveryCharacter", 1)
        self.assertIn("DirichletCharacter.LFunction", u["ground_deps"])

    def test_spine_map_valid(self):
        p = os.path.join(REPO, "outputs", "decomp", "spine_map.json")
        if not os.path.exists(p):
            self.skipTest("spine_map.json not generated")
        self.assertEqual(schema.validate_file(p, self.k), [])


if __name__ == "__main__":
    unittest.main()
