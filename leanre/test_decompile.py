"""Tests for leanre/decompile (gate D1).  Run: python3 -m unittest leanre.test_decompile -v
(or `python3 -m unittest discover -s leanre -p 'test_decompile.py' -v`).
Real-DB spot checks are skipped when outputs/kernel/kernel.db or data/rh_mirror/src are absent."""
from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
import sqlite3
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from decompile import Decompiler, KernelDB, schema  # noqa: E402
from decompile.cli import main as decompile_main  # noqa: E402
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

def MatchDef : ℕ → ℕ
  | 0 => 1
  | n + 1 => n

def BlankBeforeBody (x : ℕ) : Prop

  := x + 1 > 0

def BeforeBareEnd : Prop :=
  True

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
        self.assertEqual(one_line("x" * 1000, 0), "x" * 1000)

    def test_multiline_and_match_defs_and_include_thm(self):
        m = self.rc("Foo.Bar.MatchDef")
        self.assertEqual(m.body, "| 0 => 1 | n + 1 => n")
        b = self.rc("Foo.Bar.BlankBeforeBody")
        self.assertEqual(b.body, "x + 1 > 0")
        e = self.rc("Foo.Bar.BeforeBareEnd")
        self.assertEqual(e.body, "True")
        ct = read_contract(self.root, "Foo/Bar.lean", "Foo.Bar.good_three", include_thm=True)
        self.assertIsNotNone(ct)
        self.assertEqual(ct.body, "by intro m hm omega")
        js = ct.to_json(max_len=0, with_body=True)
        self.assertEqual(js["body"], "by intro m hm omega")


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

    def test_new_features_live_spot(self):
        hits = self.k.resolve("Main.riemannHypothesis", limit=5)
        self.assertTrue(hits)
        self.assertEqual(hits[0].decl.name, "riemannHypothesis")
        rows = self.k.search_rows("Smooth", limit=10, project_only=True, no_aux=True, kind="thm", sort_by="dom")
        self.assertEqual(len(rows), 10)
        self.assertFalse(any(d.ground or d.is_aux or d.kind != "thm" for d, *_ in rows))
        ct = self.D.contract("GlobalTheory.T.pAdicMonodromyTheorem_matrixForm", include_thm=True)
        self.assertIsNotNone(ct.body)
        self.assertIn("matThm_holds", ct.body)
        sp = self.D.dom_spine("GlobalTheory.T.weightZero_potentiallySemistable_of_sen_theorem", depth=3, min_size=500)
        self.assertEqual(sp["children"], [])
        self.assertEqual(sp["pruned_count"], 1)
        self.assertEqual(sp["pruned_reason"], "pruned_below_min_size")
        pth = self.D.shortest_path("allChi", "UpperTheory.One.vwin_of_row")
        self.assertIsNotNone(pth)
        self.assertEqual(pth[0]["id"], "allChi")
        self.assertEqual(pth[-1]["id"], "UpperTheory.One.vwin_of_row")


class TestSyntheticDecompileUpgrades(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.root = cls.tmp.name
        cls.src = os.path.join(cls.root, "src")
        os.makedirs(os.path.join(cls.src, "Demo"))
        with open(os.path.join(cls.root, "lake-manifest.json"), "w", encoding="utf-8") as f:
            json.dump({
                "version": "1.2.0",
                "packages": [{"name": "mathlib", "rev": "deadbeef1234", "url": "https://example.org/mathlib4"}],
            }, f)
        with open(os.path.join(cls.src, "Demo", "Core.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace Demo\n"
                "structure MegaStruct : Prop where\n"
                "  f1 : Nat\n"
                "  f2 : Nat\n"
                "  f3 : Nat\n"
                "  f4_long : " + ("A" * 300) + "\n"
                "def MidDef (x : MegaStruct) : Prop :=\n"
                "  x.f1 = 0 ∧ " + ("B" * 450) + "\n"
                "theorem TopThm (x : MegaStruct) : MidDef x := by\n"
                "  exact helper_thm x\n"
                "theorem RootThm : True := trivial\n"
                "end Demo\n"
            )
        cls.db_path = os.path.join(cls.root, "kernel.db")
        con = sqlite3.connect(cls.db_path)
        con.executescript(
            """
            CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
               type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
               fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
               live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
               sighash TEXT, sighash_anon TEXT);
            CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL);
            CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
            CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
            CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
            CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
            CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
            """
        )
        decls = [
            (1, "Demo.RootThm", "thm", 1, 2, 3, 0, 1, 0, 1, 0, 1, 1, 1, 0),
            (2, "Demo.TopThm", "thm", 1, 5, 100, 1, 2, 1, 1, 0, 1, 1, 1, 0),
            (3, "Demo.MidDef", "def", 1, 4, 25, 2, 2, 1, 1, 0, 1, 1, 1, 0),
            (4, "Demo.MegaStruct", "inductive", 1, 10, 10, 5, 1, 1, 0, 0, 1, 1, 1, 0),
            (5, "Mathlib.ExtLemma", "thm", 1, 12, 8, 99, 0, 0, 0, 2, 31, 1, 1, 0),
            (6, "Demo.TopThm._proof_1", "thm", 1, 1, 2, 1, 0, 0, 0, 0, 1, 1, 1, 0),
            (7, "Demo.Helper_rarg", "def", 1, 1, 2, 1, 0, 0, 0, 0, 1, 1, 1, 0),
            (8, "Demo.Isolated", "def", 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0),
        ]
        for row in decls:
            con.execute(
                "INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NULL,NULL)",
                row,
            )
        mods = [
            (1, "Demo.Core", "leanre_db:exact", None),
            (2, "Demo.Core", "leanre_db:exact", None),
            (3, "Demo.Core", "leanre_db:exact", None),
            (4, "Demo.Core", "leanre_db:exact", None),
            (5, None, "unmatched:library_or_external", None),
            (6, "Demo.Core", "aux_prefix:leanre_db", None),
            (7, "Demo.Core", "leanre_db:exact", None),
            (8, "Demo.Other", "leanre_db:exact", None),
        ]
        con.executemany("INSERT INTO decl_module VALUES (?,?,?,?)", mods)
        edges = [
            (1, 2, 2),
            (2, 3, 1),
            (2, 4, 1),
            (2, 5, 2),
            (3, 4, 3),
            (3, 5, 1),
        ]
        con.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
        con.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'all', '[1]', 8)")
        dom_rows = [
            (0, 1, None, 0, 5),
            (0, 2, 1, 1, 4),
            (0, 3, 2, 2, 1),
            (0, 4, 2, 2, 1),
            (0, 5, 2, 2, 1),
            (0, 8, None, 0, 1),
        ]
        con.executemany("INSERT INTO dom VALUES (?,?,?,?,?)", dom_rows)
        con.commit()
        con.close()

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _run_cli(self, *args: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        argv = [args[0], "--kernel-db", self.db_path, "--leanre-db", os.path.join(self.root, "none.db"), "--src", self.src, *args[1:]]
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = decompile_main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_resolve_and_graceful_errors(self):
        rc, out, _ = self._run_cli("resolve", "Demo.Missing.TopThm", "--json")
        self.assertEqual(rc, 0)
        data = json.loads(out)
        self.assertFalse(data["exact"])
        self.assertEqual(data["candidates"][0]["name"], "Demo.TopThm")

        for subcmd in ("contract", "unfold", "dom", "path", "horn", "node"):
            rc, _, err = self._run_cli(subcmd, "Demo.Wrong.MidDef")
            self.assertEqual(rc, 1, subcmd)
            self.assertIn("Demo.MidDef", err)

    def test_contract_batch_thm_and_external(self):
        rc, out, _ = self._run_cli("contract", "Demo.MidDef", "--body", "--max-len", "0")
        self.assertEqual(rc, 0)
        self.assertIn("x.f1 = 0 ∧ " + ("B" * 450), out)

        rc, out, _ = self._run_cli("contract", "Demo.TopThm", "--body")
        self.assertEqual(rc, 0)
        self.assertNotIn("helper_thm", out)

        rc, out, _ = self._run_cli("contract", "Demo.TopThm", "--body", "--include-thm", "--max-len", "0")
        self.assertEqual(rc, 0)
        self.assertIn("exact helper_thm x", out)

        rc, out, _ = self._run_cli("contract", "Mathlib.ExtLemma")
        self.assertEqual(rc, 0)
        self.assertIn("live_mask=31", out)
        self.assertIn("fan_in=99", out)
        self.assertIn("of_decide", out)
        self.assertIn("deadbeef1234", out)

        rc, out, _ = self._run_cli("contract", "Demo.TopThm", "Demo.MidDef", "--table", "--json")
        self.assertEqual(rc, 0)
        rows = json.loads(out)
        self.assertEqual([r["name"] for r in rows], ["Demo.TopThm", "Demo.MidDef"])

    def test_unfold_flags(self):
        rc, out, _ = self._run_cli("unfold", "Demo.TopThm", "--depth", "2", "--max-len", "0", "--full-fields", "--json")
        self.assertEqual(rc, 0)
        u = json.loads(out)
        mid = next(d for d in u["deps"] if d["id"] == "Demo.MidDef")
        self.assertNotIn("…", mid["body"])
        mega = next(d for d in u["deps"] if d["id"] == "Demo.MegaStruct")
        self.assertEqual(len(mega["fields"]), 4)
        self.assertNotIn("…", mega["fields"][3]["type"])

        rc, out, _ = self._run_cli("unfold", "Demo.TopThm", "--depth", "2", "--stop-at", "MegaStruct", "--json")
        self.assertEqual(rc, 0)
        u2 = json.loads(out)
        mega2 = next(d for d in u2["deps"] if d["id"] == "Demo.MegaStruct")
        self.assertTrue(mega2.get("stopped"))
        self.assertEqual(mega2.get("fields_count"), 4)
        self.assertNotIn("fields", mega2)

        rc, out, _ = self._run_cli("unfold", "Demo.TopThm", "--depth", "2", "--max-fields", "2", "--json")
        self.assertEqual(rc, 0)
        u3 = json.loads(out)
        mega3 = next(d for d in u3["deps"] if d["id"] == "Demo.MegaStruct")
        self.assertEqual(len(mega3["fields"]), 2)
        self.assertEqual(mega3["fields_truncated"], 2)

    def test_search_filters(self):
        rc, out, _ = self._run_cli("search", "Demo", "--project-only", "--no-aux", "--case-sensitive", "--kind", "thm,def", "--module", "Core", "--sort-by", "vn", "--json")
        self.assertEqual(rc, 0)
        names = [r["name"] for r in json.loads(out)]
        self.assertEqual(names, ["Demo.TopThm", "Demo.MidDef", "Demo.RootThm"])

    def test_dom_batch_pruned_and_cone(self):
        rc, out, _ = self._run_cli("dom", "Demo.TopThm", "Demo.RootThm", "--depth", "1", "--min-subtree", "10", "--with-cone")
        self.assertEqual(rc, 0)
        res = json.loads(out)
        self.assertEqual(len(res), 2)
        self.assertEqual(res[0]["pruned_count"], 3)
        self.assertEqual(res[0]["pruned_reason"], "pruned_below_min_size")
        self.assertEqual(res[0]["full_cone"], 4)
        self.assertEqual(res[0]["proj_cone"], 3)

    def test_path_two_args(self):
        rc, out, _ = self._run_cli("path", "Demo.RootThm", "Demo.MegaStruct")
        self.assertEqual(rc, 0)
        p = json.loads(out)
        self.assertTrue(p["found"])
        self.assertEqual([x["id"] for x in p["path"]], ["Demo.RootThm", "Demo.TopThm", "Demo.MegaStruct"])

        rc, out, _ = self._run_cli("path", "Demo.RootThm", "Demo.MegaStruct", "--kind", "type")
        self.assertEqual(rc, 0)
        self.assertFalse(json.loads(out)["found"])

        rc, out, _ = self._run_cli("path", "Demo.RootThm", "Demo.Isolated")
        self.assertEqual(rc, 0)
        self.assertFalse(json.loads(out)["found"])


if __name__ == "__main__":
    unittest.main()
