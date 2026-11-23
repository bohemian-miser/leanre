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

    @classmethod
    def tearDownClass(cls):
        cls.k.close()

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

    def test_loop5_live_spot(self):
        d_lo, _ = self.k.resolve_unique("zFRDirichlet")
        d_hi, _ = self.k.resolve_unique("ZFRDirichlet")
        self.assertEqual(d_lo.name, "Formalism.ZeroFreeDirichlet.zFRDirichlet")
        self.assertEqual(d_hi.name, "Formalism.ZeroFreeDirichlet.ZFRDirichlet")
        d_main, _ = self.k.resolve_unique("MAIN", near="Formalism.LFunctionChainParameters.characterSumData.ASK")
        self.assertEqual(d_main.name, "Formalism.LFunctionChainParameters.characterSumData.MAIN")
        vwin_prods = self.D.producers("UpperTheory.Top.VWin", live_only=True)
        self.assertGreaterEqual(vwin_prods["live_count"], 5)
        self.assertEqual(vwin_prods["producers"][0]["name"], "UpperTheory.One.vwin_of_row")
        hw = self.D.horn("Formalism.MainNotions.linkGLOBAL7_items", have_wiring=True)["have_wiring"]
        step_names = [s["name"] for s in hw["steps"]]
        self.assertIn("hSN", step_names)
        self.assertIn("hFr", step_names)
        self.assertEqual(hw["terminal"]["via"], "Formalism.MainNotions.Lnk.linkCore")

    def test_loop6_live_spot(self):
        # 1. `producers Data.DIV` finds dot-notation codomain producer `Lnk.Mod.data_DIV`
        div_prods = self.D.producers("Data.DIV", live_only=True)
        div_names = [p["name"] for p in div_prods["producers"]]
        self.assertIn("Formalism.MainNotions.Lnk.Mod.data_DIV", div_names)

        # 2. Partial-prefix / infix resolution `Deduction.IdentU` -> `Deduction.CH.IdentU`
        d_ident, rf_ident = self.k.resolve_unique("Deduction.IdentU")
        self.assertEqual(d_ident.name, "Deduction.CH.IdentU")
        self.assertEqual(rf_ident, "Deduction.IdentU")

        # 3. `dom --contains` batch check under StageU root
        root_d, _ = self.k.resolve_unique("GlobalTheory.T.large_unramified_exponent_bundles_exist_alt")
        q_out, _ = self.k.resolve_unique("exists_ranks_rankVal_frame")
        q_in, _ = self.k.resolve_unique("memberE_closing_alt_alt")
        q_shared, _ = self.k.resolve_unique("RankVal")
        dc = self.D.dom_contains(
            root_d,
            [
                ("exists_ranks_rankVal_frame", q_out, "exists_ranks_rankVal_frame"),
                ("memberE_closing_alt_alt", q_in, "memberE_closing_alt_alt"),
                ("RankVal", q_shared, "RankVal"),
            ],
        )
        by_q = {r["query"]: r for r in dc["results"]}
        self.assertFalse(by_q["exists_ranks_rankVal_frame"]["dom_in"])
        self.assertFalse(by_q["exists_ranks_rankVal_frame"]["cone_in"])
        self.assertEqual(by_q["exists_ranks_rankVal_frame"]["status"], "outside")
        self.assertTrue(by_q["memberE_closing_alt_alt"]["dom_in"])
        self.assertTrue(by_q["memberE_closing_alt_alt"]["cone_in"])
        self.assertEqual(by_q["memberE_closing_alt_alt"]["status"], "dominated")
        self.assertFalse(by_q["RankVal"]["dom_in"])
        self.assertTrue(by_q["RankVal"]["cone_in"])
        self.assertEqual(by_q["RankVal"]["status"], "shared_in_cone")

        # 4. Case-fold tracking + `--exact-case` refusal on `SizeData₂.IO` -> `SizeData₂.io`
        res_cf = self.k.resolve_unique_detail("SizeData₂.IO")
        self.assertEqual(res_cf.decl.name, "Formalism.BasicNotions.SizeData₂.io")
        self.assertTrue(res_cf.case_folded)
        with self.assertRaises(LookupError):
            self.k.resolve_unique("SizeData₂.IO", exact_case=True)

        # 5. `--near` refuses zero-proximity tie-break on unrelated `SizeT`
        with self.assertRaises(LookupError) as ctx_err:
            self.k.resolve_unique("SizeT", near="GlobalTheory.Mem.Top.Ctx")
        self.assertIn("ambiguous", str(ctx_err.exception).lower())

        # 6. Mutual co-inductive `OrderCertificate` resolves as live & reads its own contract
        d_oc, _ = self.k.resolve_unique("OrderCertificate")
        self.assertEqual(d_oc.name, "FunctorialResolution.EmbeddedResolution.OrderCertificate")
        c_oc = self.D.contract(d_oc)
        self.assertIsNotNone(c_oc)
        self.assertEqual(c_oc.line, 41)
        self.assertIn("descend", [f.name for f in c_oc.fields])

        # 7. `Formalism.HC.Frame` `letI := grp; ...` field types are not truncated at `:=`
        c_fr = self.D.contract("Formalism.HC.Frame")
        self.assertIsNotNone(c_fr)
        fld_map = {f.name: f.type for f in c_fr.fields}
        self.assertIn("Additive", fld_map["h0"])
        self.assertFalse(any(f.default for f in c_fr.fields if f.name == "h0"))

    def test_loop7_live_spot(self):
        # 1. `readers` on structure field (`ParameterChoice'.k_low`) & `∧`-conjuncts (`SizeKRel` #1 & #5, `Win_at` #14)
        r_klow = self.D.readers("ParameterChoice'", field="k_low", live_only=True)
        klow_names = [r["name"] for r in r_klow["readers"]]
        self.assertIn("Formalism.MainNotions.S.standing_hypotheses_of_bounds", klow_names)
        self.assertIn("Formalism.MainNotions.BridgeLemma.ev_kLow", klow_names)

        r_skr1 = self.D.readers("Formalism.MainNotions.SizeKRel", conjunct=1, live_only=True)
        skr1_names = {r["name"]: r["line"] for r in r_skr1["readers"]}
        self.assertEqual(skr1_names.get("Formalism.MainNotions.S.standing_hypotheses_of_bounds"), 1426)

        r_win14 = self.D.readers("Win_at", conjunct=14, live_only=True)
        win14_names = [r["name"] for r in r_win14["readers"]]
        self.assertIn("Formalism.MainNotions.Lnk.linkCore", win14_names)

        # 2. `.mk` constructor resolution & `QZ` auto-instance source location (`R6B-03`, `R6B-04`)
        d_mk, _ = self.k.resolve_unique("OpenImageCondition.mk", near="UpperTheory.One.vwin_of_row")
        self.assertEqual(d_mk.name, "UpperTheory.LiteratureTheorems.OpenImageCondition.mk")
        self.assertEqual(d_mk.kind, "ctor")
        c_mk = self.D.contract(d_mk)
        self.assertIsNotNone(c_mk)
        self.assertEqual(c_mk.keyword, "ctor")
        self.assertTrue(c_mk.parent_info.get("is_constructor"))

        c_qz_top = self.D.contract("Formalism.GaloisCohomology.instTopologicalSpaceQZ")
        self.assertIsNotNone(c_qz_top)
        self.assertEqual(c_qz_top.line, 19)
        self.assertIn("TopologicalSpace", c_qz_top.header)

        # 3. Term-mode `horn --have-wiring` on `memberE_closing_alt_alt` & `jointWin_of_counts`
        hw_mem = self.D.horn("memberE_closing_alt_alt", have_wiring=True)["have_wiring"]
        tw_mem = hw_mem["term_wiring"]
        self.assertEqual(tw_mem["mode"], "application")
        self.assertEqual(tw_mem["callee"], "GlobalTheory.T.exists_member_of_construction_steps_secondPass")
        self.assertEqual(len(tw_mem["args"]), 18)
        self.assertEqual(tw_mem["args"][4].get("param_name"), "𝒮")
        self.assertEqual(tw_mem["args"][7]["via"], "GlobalTheory.T.has4_of_has3_of_lv3Mv")

        hw_jw = self.D.horn("jointWin_of_counts", have_wiring=True)["have_wiring"]
        self.assertEqual(hw_jw["term_wiring"]["callee"], "UpperTheory.V.jointWin_of")
        self.assertEqual(len(hw_jw["term_wiring"]["args"]), 3)

        # 4. `producers` premise/wrapper hints on 0-producer `Prop`-defs (`OnePlace`, `ThinScales`)
        p_thin = self.D.producers("ThinScales")
        self.assertEqual(p_thin["total_count"], 0)
        self.assertGreaterEqual(p_thin.get("premise_consumers_count", 0), 3)
        wp_names = [w["name"] for w in p_thin.get("wrapper_producers", ())]
        self.assertIn("Formalism.MainNotions.Lnk.char_at", wp_names)


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


class TestDecompileLoop3(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.root = cls.tmp.name
        cls.src = os.path.join(cls.root, "src")
        os.makedirs(os.path.join(cls.src, "Demo"))
        with open(os.path.join(cls.src, "Demo", "Alpha.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace Demo.Ns\n"
                "structure Box : Type where\n"
                "  firstField : Nat\n"
                "  secondField : Bool\n"
                "  thirdField (k : Nat) : k = k\n"
                "def MultiBody (n : Nat) : Prop :=\n"
                "  ∀ m : Nat,\n"
                "    m ≤ n →\n"
                "    m < n + 1\n"
                "theorem MultiProof (n : Nat) : MultiBody n := by\n"
                "  intro m hm\n"
                "  omega\n"
                "theorem AmbigName : True := trivial\n"
                "def DeadOnlyDecl (x : Nat) : Prop :=\n"
                "  x = x\n"
                "end Demo.Ns\n"
            )
        with open(os.path.join(cls.src, "Demo", "Beta.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace Demo.Other\n"
                "theorem AmbigName : True := trivial\n"
                "def BetaTarget : Prop := True\n"
                "def DeadSrcOnlyNoDb (y : Nat) : Prop := y > 0\n"
                "end Demo.Other\n"
            )

        # Place kernel.db under outputs/kernel/kernel.db and leanre.db under outputs/leanre.db
        # to verify auto-detection alongside --kernel-db.
        cls.out_dir = os.path.join(cls.root, "outputs")
        cls.kdir = os.path.join(cls.out_dir, "kernel")
        os.makedirs(cls.kdir)
        cls.kdb_path = os.path.join(cls.kdir, "kernel.db")
        cls.ldb_path = os.path.join(cls.out_dir, "leanre.db")

        kcon = sqlite3.connect(cls.kdb_path)
        kcon.executescript(
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
            (1, "Demo.Ns.MultiProof", "thm", 1, 4, 20, 0, 1, 1, 0, 0, 1, 1, 1, 0),
            (2, "Demo.Ns.MultiBody", "def", 1, 3, 10, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (3, "Demo.Ns.Box", "inductive", 1, 5, 5, 2, 0, 0, 0, 0, 1, 1, 1, 0),
            (4, "Demo.Ns.Box.secondField", "def", 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (5, "Demo.Ns.AmbigName", "thm", 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0),
            (6, "Demo.Other.AmbigName", "thm", 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0),
            (7, "Demo.Other.BetaTarget", "def", 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0),
            (8, "Demo.Ns.MultiProof._proof_1", "thm", 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0),
        ]
        for row in decls:
            kcon.execute("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NULL,NULL)", row)
        mods = [
            (1, "Demo.Alpha", "leanre_db:exact", None),
            (2, "Demo.Alpha", "leanre_db:exact", None),
            (3, "Demo.Alpha", "leanre_db:exact", None),
            (4, "Demo.Alpha", "aux_prefix:leanre_db", None),
            (5, "Demo.Alpha", "leanre_db:exact", None),
            (6, "Demo.Beta", "leanre_db:exact", None),
            (7, "Demo.Beta", "leanre_db:exact", None),
            (8, "Demo.Alpha", "aux_prefix:leanre_db", None),
        ]
        kcon.executemany("INSERT INTO decl_module VALUES (?,?,?,?)", mods)
        kcon.executemany("INSERT INTO edges VALUES (?,?,?)", [(1, 2, 1), (2, 3, 1), (4, 3, 1)])
        kcon.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'all', '[1]', 8)")
        kcon.executemany(
            "INSERT INTO dom VALUES (?,?,?,?,?)",
            [(0, 1, None, 0, 4), (0, 2, 1, 1, 3), (0, 3, 2, 2, 1), (0, 4, 2, 2, 1)],
        )
        kcon.commit()
        kcon.close()

        lcon = sqlite3.connect(cls.ldb_path)
        lcon.executescript(
            """
            CREATE TABLE modules(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL, file_path TEXT NOT NULL);
            CREATE TABLE declarations(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, module TEXT NOT NULL,
                line_no INTEGER NOT NULL, signature_snippet TEXT NOT NULL, horn_requires_json TEXT NOT NULL, horn_proves TEXT);
            """
        )
        lcon.execute("INSERT INTO modules VALUES (1, 'Demo.Alpha', 'Demo/Alpha.lean')")
        lcon.execute(
            "INSERT INTO declarations VALUES (1, 'Demo.Ns.DeadOnlyDecl', 'def', 'Demo.Alpha', 14, 'def DeadOnlyDecl (x : Nat) : Prop', '[]', NULL)"
        )
        lcon.commit()
        lcon.close()

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _cli(self, *args: str, use_leanre_db: Optional[str] = None) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        argv = [args[0], "--kernel-db", self.kdb_path, "--src-root", self.src]
        if use_leanre_db is not None:
            argv.extend(["--source-db", use_leanre_db])
        argv.extend(args[1:])
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = decompile_main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_multi_arg_resolve(self):
        rc, out, _ = self._cli("resolve", "MultiBody", "BetaTarget", "--json")
        self.assertEqual(rc, 0)
        res = json.loads(out)
        self.assertEqual(len(res), 2)
        self.assertEqual(res[0]["candidates"][0]["name"], "Demo.Ns.MultiBody")
        self.assertEqual(res[1]["candidates"][0]["name"], "Demo.Other.BetaTarget")

        rc, out, _ = self._cli("resolve", "DeadOnlyDecl", "--json")
        self.assertEqual(rc, 0)
        res_dead = json.loads(out)
        self.assertEqual(res_dead["candidates"][0]["status"], "dead_source_only")
        self.assertEqual(res_dead["candidates"][0]["name"], "Demo.Ns.DeadOnlyDecl")

    def test_unique_suffix_across_commands_and_ambiguity(self):
        rc, out, _ = self._cli("contract", "MultiBody", "--json")
        self.assertEqual(rc, 0)
        c = json.loads(out)
        self.assertEqual(c["decl"]["name"], "Demo.Ns.MultiBody")
        self.assertEqual(c["resolved_from"], "MultiBody")

        rc, out, _ = self._cli("unfold", "MultiProof", "--depth", "1", "--json")
        self.assertEqual(rc, 0)
        self.assertEqual(json.loads(out)["id"], "Demo.Ns.MultiProof")

        rc, out, _ = self._cli("dom", "MultiProof", "--min-size", "1")
        self.assertEqual(rc, 0)
        self.assertEqual(json.loads(out)["id"], "Demo.Ns.MultiProof")

        rc, out, _ = self._cli("node", "MultiBody")
        self.assertEqual(rc, 0)
        self.assertEqual(json.loads(out)["id"], "Demo.Ns.MultiBody")

        rc, out, _ = self._cli("horn", "MultiProof")
        self.assertEqual(rc, 0)
        self.assertEqual(json.loads(out)["via"], "Demo.Ns.MultiProof")

        rc, out, _ = self._cli("path", "MultiProof", "Box")
        self.assertEqual(rc, 0)
        p = json.loads(out)
        self.assertTrue(p["found"])
        self.assertEqual([x["id"] for x in p["path"]], ["Demo.Ns.MultiProof", "Demo.Ns.MultiBody", "Demo.Ns.Box"])

        # Ambiguous suffix must still fail (unless --continue-on-error)
        rc, _, err = self._cli("contract", "AmbigName")
        self.assertEqual(rc, 1)
        self.assertIn("ambiguous", err.lower())

    def test_continue_on_error(self):
        rc, out, _ = self._cli("contract", "MultiBody", "NoSuchDecl99", "BetaTarget", "--continue-on-error", "--json")
        self.assertEqual(rc, 0)
        data = json.loads(out)
        self.assertEqual([x["decl"]["name"] for x in data["results"]], ["Demo.Ns.MultiBody", "Demo.Other.BetaTarget"])
        self.assertEqual(data["missing"], ["NoSuchDecl99"])
        self.assertEqual(len(data["errors"]), 1)
        self.assertEqual(data["errors"][0]["query"], "NoSuchDecl99")

        rc, out, _ = self._cli("contract", "MultiBody", "AmbigName", "--table", "--continue-on-error", "--json")
        self.assertEqual(rc, 0)
        tdata = json.loads(out)
        self.assertEqual([r["name"] for r in tdata["results"]], ["Demo.Ns.MultiBody"])
        self.assertEqual(tdata["missing"], ["AmbigName"])
        self.assertTrue(tdata["errors"][0]["ambiguous"])

        rc, out, _ = self._cli("dom", "MultiProof", "NoSuchDecl99", "--min-size", "1", "--continue-on-error")
        self.assertEqual(rc, 0)
        ddata = json.loads(out)
        self.assertEqual(ddata["results"][0]["id"], "Demo.Ns.MultiProof")
        self.assertEqual(ddata["missing"], ["NoSuchDecl99"])

        rc, out, _ = self._cli("path", "MultiProof", "NoSuchDst", "--continue-on-error")
        self.assertEqual(rc, 0)
        pdata = json.loads(out)
        self.assertFalse(pdata["found"])
        self.assertEqual(pdata["missing"], ["NoSuchDst"])

    def test_preserve_lines_and_field_anchor(self):
        # Default collapses lines
        rc, out, _ = self._cli("contract", "MultiBody", "--body", "--json")
        self.assertEqual(rc, 0)
        self.assertNotIn("\n", json.loads(out)["contract"]["body"])

        # --preserve-lines keeps multi-line body in JSON and text
        rc, out, _ = self._cli("contract", "MultiBody", "--body", "--preserve-lines", "--json")
        self.assertEqual(rc, 0)
        body = json.loads(out)["contract"]["body"]
        self.assertIn("\n", body)
        self.assertEqual(body, "∀ m : Nat,\n  m ≤ n →\n  m < n + 1")

        rc, out, _ = self._cli("contract", "MultiProof", "--body", "--include-thm", "--preserve-lines")
        self.assertEqual(rc, 0)
        self.assertIn(":= by\n", out)
        self.assertIn("intro m hm", out)
        self.assertIn("omega", out)

        # Field projection anchors to the field's own line (line 4), NOT structure header (line 2)
        rc, out, _ = self._cli("contract", "Demo.Ns.Box.secondField", "--json")
        self.assertEqual(rc, 0)
        fc = json.loads(out)["contract"]
        self.assertEqual(fc["line"], 4)
        self.assertEqual(fc["anchor"], "src/Demo/Alpha.lean:4")

    def test_dead_decl_fallback(self):
        # Auto-detected outputs/leanre.db beside outputs/kernel/kernel.db
        rc, out, _ = self._cli("contract", "DeadOnlyDecl", "--body", "--json")
        self.assertEqual(rc, 0)
        d = json.loads(out)
        self.assertEqual(d["status"], "dead_source_only")
        self.assertEqual(d["file"], "Demo/Alpha.lean")
        self.assertEqual(d["line"], 14)
        self.assertEqual(d["anchor"], "src/Demo/Alpha.lean:14")
        self.assertIn("def DeadOnlyDecl", d["header"])
        self.assertEqual(d["contract"]["body"], "x = x")

        # Fallback to --src-root when leanre.db is absent
        rc, out, _ = self._cli("contract", "DeadSrcOnlyNoDb", "--json", use_leanre_db=os.path.join(self.root, "absent.db"))
        self.assertEqual(rc, 0)
        d2 = json.loads(out)
        self.assertEqual(d2["status"], "dead_source_only")
        self.assertEqual(d2["file"], "Demo/Beta.lean")
        self.assertEqual(d2["line"], 4)

    def test_search_regex_include_aux_and_search_module(self):
        # --regex with | alternation
        rc, out, _ = self._cli("search", "MultiBody|BetaTarget", "--regex", "--json")
        self.assertEqual(rc, 0)
        names = {r["name"] for r in json.loads(out)}
        self.assertEqual(names, {"Demo.Ns.MultiBody", "Demo.Other.BetaTarget"})

        # --include-aux overrides --no-aux
        rc, out, _ = self._cli("search", "MultiProof", "--no-aux", "--include-aux", "--json")
        self.assertEqual(rc, 0)
        names_aux = {r["name"] for r in json.loads(out)}
        self.assertIn("Demo.Ns.MultiProof._proof_1", names_aux)

        # --search-module matches across module + decl name
        rc, out, _ = self._cli("search", "Alpha.*Box", "--regex", "--search-module", "--json")
        self.assertEqual(rc, 0)
        names_mod = {r["name"] for r in json.loads(out)}
        self.assertIn("Demo.Ns.Box", names_mod)

        # Invalid regex returns exit 2
        rc, _, err = self._cli("search", "[unclosed", "--regex")
        self.assertEqual(rc, 2)
        self.assertIn("invalid --regex", err)


class TestDecompileLoop5UX(unittest.TestCase):
    """Comprehensive unit tests for Loop 5A UX & resolution upgrades:
    1. Exact-case-first resolution + `--near <decl>` disambiguation
    2. `contract --grep REGEX -C N`, `--body-lines A:B`, `--deps-headers`, instance summary & unfold hint
    3. `producers <Target>` (direct, exists, conjunct, nonempty, wrapped, rejecting consumers)
    4. `search --kind instance`
    5. `horn --have-wiring` (JSON & `--text` DAG extraction)
    6. `XREPO-06` (`leanre.toml` / Lake-root anchor prefix vs RH `src/` default)
    """

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.root = cls.tmp.name
        cls.src = os.path.join(cls.root, "src")
        os.makedirs(os.path.join(cls.src, "PillarA"))
        os.makedirs(os.path.join(cls.src, "PillarB"))
        os.makedirs(os.path.join(cls.src, "Hidden"))

        with open(os.path.join(cls.src, "Hidden", "Defs.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace Hidden\n"
                "abbrev E0 := Nat × Nat\n"
                "def InPhi (x : E0) : Prop := x.1 = x.2\n"
                "end Hidden\n"
            )

        with open(os.path.join(cls.src, "PillarA", "Chain.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace PillarA.Sub\n"
                "open Hidden\n"
                "def ZFRDirichlet : Prop := True\n"
                "theorem zFRDirichlet : ZFRDirichlet := trivial\n"
                "def MAIN (x : E0) : Prop := InPhi x\n"
                "def ASK (x : E0) : Prop := InPhi x ∧ ZFRDirichlet ∧ True\n"
                "structure MyBundle : Type where\n"
                "  val : Nat\n"
                "  ok : val = val\n"
                "instance : Nonempty MyBundle := ⟨⟨0, rfl⟩⟩\n"
                "def TargetProp (n : Nat) : Prop := n = n\n"
                "def AuxConjA (n : Nat) : Prop := n ≥ 0\n"
                "def AuxConjB (n : Nat) : Prop := n ≤ n + 1\n"
                "def BigConjDef (n : Nat) : Prop := TargetProp n ∧ AuxConjA n ∧ AuxConjB n\n"
                "theorem prod_direct (n : Nat) : TargetProp n := rfl\n"
                "theorem prod_exists : ∃ k : Nat, ∀ m ≥ k, TargetProp m := ⟨0, fun _ _ => rfl⟩\n"
                "theorem prod_conj (n : Nat) : AuxConjA n ∧ TargetProp n := ⟨Nat.zero_le _, rfl⟩\n"
                "theorem prod_nonempty : Nonempty MyBundle := ⟨⟨1, rfl⟩⟩\n"
                "theorem prod_wrapped : ClosedWrap (fun n => TargetProp n) := trivial\n"
                "theorem consumer_only (n : Nat) (h : TargetProp n) : AuxConjA n := Nat.zero_le _\n"
                "theorem consumer_forall : ∀ (n : Nat) (h : TargetProp n), AuxConjB n := fun _ _ => Nat.le_succ _\n"
                "theorem link_wiring (n : Nat) (hA : AuxConjA n) (hPair : AuxConjA n ∧ AuxConjB n) :\n"
                "    TargetProp n → BigConjDef n := by\n"
                "  intro hT\n"
                "  obtain ⟨pA, pB⟩ := hPair\n"
                "  have s1 : AuxConjA n :=\n"
                "    step_lemma_a n hA\n"
                "  have s2 : AuxConjB n := step_lemma_b n s1 pB\n"
                "  exact combine_big n hT s1 s2\n"
                "end PillarA.Sub\n"
            )

        with open(os.path.join(cls.src, "PillarB", "Other.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace PillarB.Other\n"
                "theorem main : True := trivial\n"
                "def MAIN : Prop := False\n"
                "def OnlyUpperCase : Prop := True\n"
                "instance namedInstBundle : Inhabited PillarA.Sub.MyBundle := ⟨⟨0, rfl⟩⟩\n"
                "end PillarB.Other\n"
            )

        cls.kdb_path = os.path.join(cls.root, "kernel.db")
        cls.ldb_path = os.path.join(cls.root, "leanre.db")
        kcon = sqlite3.connect(cls.kdb_path)
        kcon.executescript(
            """
            CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
               type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
               fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
               live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
               sighash TEXT, sighash_anon TEXT);
            CREATE UNIQUE INDEX decls_name ON decls(name);
            CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL);
            CREATE UNIQUE INDEX consts_name ON consts(name);
            CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
            CREATE INDEX edges_dst ON edges(dst, src);
            CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
            CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
            CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
            CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
            """
        )
        decls = [
            (1, "Hidden.E0", "def", 1, 2, 2, 3, 0, 0, 0, 0, 1, 1, 1, 0),
            (2, "Hidden.InPhi", "def", 1, 3, 3, 2, 1, 1, 0, 0, 1, 1, 1, 0),
            (3, "PillarA.Sub.ZFRDirichlet", "def", 1, 1, 1, 2, 0, 0, 0, 0, 1, 1, 1, 0),
            (4, "PillarA.Sub.zFRDirichlet", "thm", 1, 2, 5, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (5, "PillarA.Sub.MAIN", "def", 1, 2, 4, 1, 2, 1, 1, 0, 1, 1, 1, 0),
            (6, "PillarA.Sub.ASK", "def", 1, 2, 6, 1, 3, 1, 2, 0, 1, 1, 1, 0),
            (7, "PillarB.Other.main", "thm", 1, 1, 1, 9, 0, 0, 0, 0, 1, 1, 1, 0),
            (8, "PillarB.Other.MAIN", "def", 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0),
            (9, "PillarB.Other.OnlyUpperCase", "def", 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0),
            (10, "PillarA.Sub.MyBundle", "inductive", 1, 4, 4, 3, 0, 0, 0, 0, 1, 1, 1, 0),
            (11, "PillarA.Sub.MyBundle.val", "def", 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (12, "PillarA.Sub.instNonemptyMyBundle", "thm", 1, 2, 3, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (13, "PillarB.Other.namedInstBundle", "def", 1, 2, 3, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (14, "PillarA.Sub.TargetProp", "def", 1, 2, 2, 8, 0, 0, 0, 0, 1, 1, 1, 0),
            (15, "PillarA.Sub.AuxConjA", "def", 1, 2, 2, 4, 0, 0, 0, 0, 1, 1, 1, 0),
            (16, "PillarA.Sub.AuxConjB", "def", 1, 2, 2, 4, 0, 0, 0, 0, 1, 1, 1, 0),
            (17, "PillarA.Sub.BigConjDef", "def", 1, 3, 6, 2, 3, 0, 3, 0, 1, 1, 1, 0),
            (18, "PillarA.Sub.prod_direct", "thm", 1, 3, 4, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (19, "PillarA.Sub.prod_exists", "thm", 1, 4, 5, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (20, "PillarA.Sub.prod_conj", "thm", 1, 4, 5, 1, 2, 2, 0, 0, 1, 1, 1, 0),
            (21, "PillarA.Sub.prod_nonempty", "thm", 1, 2, 3, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (22, "PillarA.Sub.prod_wrapped", "thm", 1, 3, 3, 1, 1, 1, 0, 0, 0, 0, 0, 0),  # non-live producer
            (23, "PillarA.Sub.consumer_only", "thm", 1, 4, 4, 1, 2, 2, 0, 0, 1, 1, 1, 0),
            (24, "PillarA.Sub.consumer_forall", "thm", 1, 4, 4, 1, 2, 2, 0, 0, 1, 1, 1, 0),
            (25, "PillarA.Sub.step_lemma_a", "thm", 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (26, "PillarA.Sub.step_lemma_b", "thm", 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (27, "PillarA.Sub.combine_big", "thm", 1, 3, 3, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (28, "PillarA.Sub.link_wiring", "thm", 1, 6, 30, 1, 7, 4, 3, 0, 1, 1, 1, 0),
            (29, "Mathlib.instTopologicalSpaceNat", "def", 1, 2, 2, 50, 0, 0, 0, 0, 1, 1, 1, 0),
        ]
        for row in decls:
            kcon.execute("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NULL,NULL)", row)

        mods = [
            (1, "Hidden.Defs", "leanre_db:exact", 1),
            (2, "Hidden.Defs", "leanre_db:exact", 2),
            (3, "PillarA.Chain", "leanre_db:exact", 3),
            (4, "PillarA.Chain", "leanre_db:exact", 4),
            (5, "PillarA.Chain", "leanre_db:exact", 5),
            (6, "PillarA.Chain", "leanre_db:exact", 6),
            (7, "PillarB.Other", "leanre_db:exact", 7),
            (8, "PillarB.Other", "leanre_db:exact", 8),
            (9, "PillarB.Other", "leanre_db:exact", 9),
            (10, "PillarA.Chain", "leanre_db:exact", 10),
            (11, "PillarA.Chain", "aux_prefix:leanre_db", None),
            (12, None, "unmatched:project_auto_instance", None),
            (13, "PillarB.Other", "leanre_db:exact", 13),
            (14, "PillarA.Chain", "leanre_db:exact", 14),
            (15, "PillarA.Chain", "leanre_db:exact", 15),
            (16, "PillarA.Chain", "leanre_db:exact", 16),
            (17, "PillarA.Chain", "leanre_db:exact", 17),
            (18, "PillarA.Chain", "leanre_db:exact", 18),
            (19, "PillarA.Chain", "leanre_db:exact", 19),
            (20, "PillarA.Chain", "leanre_db:exact", 20),
            (21, "PillarA.Chain", "leanre_db:exact", 21),
            (22, "PillarA.Chain", "leanre_db:exact", 22),
            (23, "PillarA.Chain", "leanre_db:exact", 23),
            (24, "PillarA.Chain", "leanre_db:exact", 24),
            (25, "PillarA.Chain", "leanre_db:exact", None),
            (26, "PillarA.Chain", "leanre_db:exact", None),
            (27, "PillarA.Chain", "leanre_db:exact", None),
            (28, "PillarA.Chain", "leanre_db:exact", 28),
            (29, None, "unmatched:challenge_library", None),
        ]
        kcon.executemany("INSERT INTO decl_module VALUES (?,?,?,?)", mods)

        edges = [
            (2, 1, 1),
            (4, 3, 1),
            (5, 1, 1), (5, 2, 2),
            (6, 1, 1), (6, 2, 2), (6, 3, 2),
            (11, 10, 1),
            (12, 10, 1),
            (13, 10, 1),
            (17, 14, 2), (17, 15, 2), (17, 16, 2),
            (18, 14, 1),
            (19, 14, 1),
            (20, 15, 1), (20, 14, 1),
            (21, 10, 1),
            (22, 14, 1),
            (23, 14, 1), (23, 15, 1),
            (24, 14, 1), (24, 16, 1),
            (28, 14, 1), (28, 15, 3), (28, 16, 3), (28, 17, 1),
            (28, 25, 2), (28, 26, 2), (28, 27, 2),
        ]
        kcon.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
        kcon.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'all', '[4]', 29)")
        dom_rows = [
            (0, 7, None, 0, 9999),  # huge lowercase `main` must NOT hide exact-case `MAIN`
            (0, 5, None, 0, 50),
            (0, 8, None, 0, 10),
            (0, 4, None, 0, 80),
            (0, 3, 4, 1, 5),
            (0, 18, None, 0, 500),
            (0, 19, None, 0, 200),
            (0, 20, None, 0, 100),
            (0, 21, None, 0, 75),
            (0, 23, None, 0, 9000),  # consumer with huge dom must NOT appear in `producers`
            (0, 24, None, 0, 8000),  # consumer with huge dom must NOT appear in `producers`
        ]
        kcon.executemany("INSERT INTO dom VALUES (?,?,?,?,?)", dom_rows)
        kcon.commit()
        kcon.close()

        lcon = sqlite3.connect(cls.ldb_path)
        lcon.executescript(
            """
            CREATE TABLE modules(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL, file_path TEXT NOT NULL);
            CREATE TABLE declarations(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, module TEXT NOT NULL,
                line_no INTEGER NOT NULL, signature_snippet TEXT NOT NULL, horn_requires_json TEXT NOT NULL, horn_proves TEXT);
            """
        )
        lcon.executemany(
            "INSERT INTO modules VALUES (?,?,?)",
            [
                (1, "Hidden.Defs", "Hidden/Defs.lean"),
                (2, "PillarA.Chain", "PillarA/Chain.lean"),
                (3, "PillarB.Other", "PillarB/Other.lean"),
            ],
        )
        lcon.executemany(
            "INSERT INTO declarations VALUES (?,?,?,?,?,?,?,?)",
            [
                (10, "PillarA.Sub.MyBundle", "structure", "PillarA.Chain", 7, "structure MyBundle : Type", "[]", None),
                (120, "PillarA.Sub._anon_10", "instance", "PillarA.Chain", 10, "instance : Nonempty MyBundle", "[]", None),
                (13, "PillarB.Other.namedInstBundle", "instance", "PillarB.Other", 5, "instance namedInstBundle : Inhabited PillarA.Sub.MyBundle", "[]", None),
                (99, "PillarA.Sub.dead_producer_target", "theorem", "PillarA.Chain", 15, "theorem prod_direct (n : Nat) : TargetProp n", "[]", "TargetProp"),
            ],
        )
        lcon.commit()
        lcon.close()

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _cli(self, *args: str, extra_flags: tuple[str, ...] = ()) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        argv = [
            args[0],
            "--kernel-db", self.kdb_path,
            "--leanre-db", self.ldb_path,
            "--src", self.src,
            *extra_flags,
            *args[1:],
        ]
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = decompile_main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_exact_case_first_and_near_disambiguation(self):
        # 1. Exact-case `zFRDirichlet` vs `ZFRDirichlet` never collide!
        rc1, out1, _ = self._cli("contract", "zFRDirichlet", "--json")
        self.assertEqual(rc1, 0)
        self.assertEqual(json.loads(out1)["decl"]["name"], "PillarA.Sub.zFRDirichlet")

        rc2, out2, _ = self._cli("contract", "ZFRDirichlet", "--json")
        self.assertEqual(rc2, 0)
        self.assertEqual(json.loads(out2)["decl"]["name"], "PillarA.Sub.ZFRDirichlet")

        # 2. `resolve MAIN --limit 2` ranks both exact-case `.MAIN` decls above dom=9999 `.main`
        rc3, out3, _ = self._cli("resolve", "MAIN", "--limit", "3", "--json")
        self.assertEqual(rc3, 0)
        cands = json.loads(out3)["candidates"]
        self.assertEqual([c["name"] for c in cands[:2]], ["PillarA.Sub.MAIN", "PillarB.Other.MAIN"])
        self.assertEqual(cands[2]["name"], "PillarB.Other.main")
        self.assertEqual(cands[2]["match"], "case_fold")

        # 3. Case-insensitive fallback still works when no exact-case match exists
        rc4, out4, _ = self._cli("contract", "onlyuppercase", "--json")
        self.assertEqual(rc4, 0)
        self.assertEqual(json.loads(out4)["decl"]["name"], "PillarB.Other.OnlyUpperCase")

        # 4. `--near <decl>` disambiguates multi-module `MAIN` toward longest shared namespace
        rc_amb, _, err_amb = self._cli("contract", "MAIN")
        self.assertEqual(rc_amb, 1)
        self.assertIn("PillarA.Sub.MAIN", err_amb)
        self.assertNotIn("PillarB.Other.main", err_amb)  # wrong-case excluded from exact-case ambiguity

        rc_near, out_near, _ = self._cli("contract", "MAIN", "--near", "PillarA.Sub.ASK", "--json")
        self.assertEqual(rc_near, 0)
        self.assertEqual(json.loads(out_near)["decl"]["name"], "PillarA.Sub.MAIN")

        # `--near` via cone membership when constant is in an opened namespace (`E0` used by `ASK`)
        rc_res, out_res, _ = self._cli("resolve", "MAIN", "--near", "PillarB.Other.OnlyUpperCase", "--json")
        self.assertEqual(rc_res, 0)
        self.assertEqual(json.loads(out_res)["candidates"][0]["name"], "PillarB.Other.MAIN")

    def test_contract_grep_body_lines_deps_headers_and_hints(self):
        # `--grep` with `-C 1` auto-enables `--body --include-thm --preserve-lines` and shows real .lean lines
        rc, out, _ = self._cli("contract", "link_wiring", "--grep", "step_lemma_a", "-C", "1")
        self.assertEqual(rc, 0)
        self.assertIn("grep     : /step_lemma_a/ (1 match(es)", out)
        self.assertIn("L26-   have s1 : AuxConjA n :=", out)
        self.assertIn("L27:     step_lemma_a n hA", out)
        self.assertIn("L28-   have s2 : AuxConjB n := step_lemma_b n s1 pB", out)

        # `--body-lines` 1-based offset mode vs explicit `L` file-line mode
        rc_off, out_off, _ = self._cli("contract", "link_wiring", "--body-lines", "2:4")
        self.assertEqual(rc_off, 0)
        self.assertIn("offset mode", out_off)
        self.assertIn("L24:   intro hT", out_off)
        self.assertIn("L25:   obtain ⟨pA, pB⟩ := hPair", out_off)

        rc_fl, out_fl, _ = self._cli("contract", "link_wiring", "--body-lines", "L27:29", "--json")
        self.assertEqual(rc_fl, 0)
        j_fl = json.loads(out_fl)
        self.assertEqual(j_fl["body_slice"]["mode"], "file")
        self.assertEqual([r["line"] for r in j_fl["body_slice"]["lines"]], [27, 28, 29])

        # Invalid `--grep` and `--body-lines` exit 2 cleanly
        rc_bad1, _, _ = self._cli("contract", "link_wiring", "--grep", "[unclosed")
        self.assertEqual(rc_bad1, 2)
        rc_bad2, _, _ = self._cli("contract", "link_wiring", "--body-lines", "9:3")
        self.assertEqual(rc_bad2, 2)

        # `--deps-headers` resolves opened-namespace `Hidden.E0` (with inline abbrev body) and `Hidden.InPhi`
        rc_dh, out_dh, _ = self._cli("contract", "ASK", "--deps-headers")
        self.assertEqual(rc_dh, 0)
        self.assertIn("Hidden.E0 [def]", out_dh)
        self.assertIn("abbrev E0 := Nat × Nat", out_dh)
        self.assertIn("Hidden.InPhi [def]", out_dh)

        # `unfold --depth 2` discoverability hint on multi-dep def + `contract --help` tip + field_of info
        rc_h, out_h, _ = self._cli("contract", "BigConjDef")
        self.assertEqual(rc_h, 0)
        self.assertIn("leanre decompile unfold PillarA.Sub.BigConjDef --depth 2", out_h)

        rc_fld, out_fld, _ = self._cli("contract", "PillarA.Sub.MyBundle.val")
        self.assertEqual(rc_fld, 0)
        self.assertIn("field_of : PillarA.Sub.MyBundle [structure] (2 fields", out_fld)

        # Attached instances summary on `MyBundle`
        rc_mb, out_mb, _ = self._cli("contract", "MyBundle")
        self.assertEqual(rc_mb, 0)
        self.assertIn("instances: 2 attached", out_mb)
        self.assertIn("instance : Nonempty MyBundle", out_mb)

    def test_producers_ranking_and_consumer_rejection(self):
        rc, out, _ = self._cli("producers", "TargetProp", "--json")
        self.assertEqual(rc, 0)
        data = json.loads(out)
        self.assertEqual(data["live_count"], 3)
        self.assertEqual(data["total_count"], 4)
        names = [p["name"] for p in data["producers"]]
        roles = {p["name"]: p["role"] for p in data["producers"]}
        # Ranked by live first, then dom descending: prod_direct (500) > prod_exists (200) > prod_conj (100) > prod_wrapped (non-live)
        self.assertEqual(
            names,
            [
                "PillarA.Sub.prod_direct",
                "PillarA.Sub.prod_exists",
                "PillarA.Sub.prod_conj",
                "PillarA.Sub.prod_wrapped",
            ],
        )
        self.assertEqual(roles["PillarA.Sub.prod_direct"], "direct")
        self.assertEqual(roles["PillarA.Sub.prod_exists"], "exists")
        self.assertEqual(roles["PillarA.Sub.prod_conj"], "conjunct")
        self.assertEqual(roles["PillarA.Sub.prod_wrapped"], "wrapped")
        # Consumers (`consumer_only`, `consumer_forall`, `link_wiring`) and field projections must NEVER be included
        for non_prod in ("PillarA.Sub.consumer_only", "PillarA.Sub.consumer_forall", "PillarA.Sub.link_wiring"):
            self.assertNotIn(non_prod, names)

        # `--live-only` drops `prod_wrapped`
        rc_lo, out_lo, _ = self._cli("producers", "TargetProp", "--live-only", "--json")
        self.assertEqual(rc_lo, 0)
        self.assertEqual(len(json.loads(out_lo)["producers"]), 3)

        # `Nonempty MyBundle` producer detected on `structure`
        rc_ne, out_ne, _ = self._cli("producers", "MyBundle", "--live-only", "--json")
        self.assertEqual(rc_ne, 0)
        ne_names = {p["name"]: p["role"] for p in json.loads(out_ne)["producers"]}
        self.assertEqual(ne_names.get("PillarA.Sub.prod_nonempty"), "nonempty")

    def test_search_kind_instance(self):
        rc, out, _ = self._cli("search", "Bundle", "--kind", "instance", "--project-only", "--json")
        self.assertEqual(rc, 0)
        names = {r["name"] for r in json.loads(out)}
        self.assertEqual(names, {"PillarA.Sub.instNonemptyMyBundle", "PillarB.Other.namedInstBundle"})

        rc_all, out_all, _ = self._cli("search", "TopologicalSpace|Bundle", "--regex", "--kind", "instance", "--json")
        self.assertEqual(rc_all, 0)
        names_all = {r["name"] for r in json.loads(out_all)}
        self.assertIn("Mathlib.instTopologicalSpaceNat", names_all)
        self.assertIn("PillarB.Other.namedInstBundle", names_all)

    def test_horn_have_wiring(self):
        rc, out, _ = self._cli("horn", "link_wiring", "--have-wiring")
        self.assertEqual(rc, 0)
        h = json.loads(out)
        hw = h["have_wiring"]
        self.assertEqual([i["name"] for i in hw["intros"]], ["hT"])
        self.assertEqual(hw["destructured"][0]["vars"], ["pA", "pB"])
        steps = {s["name"]: s for s in hw["steps"]}
        self.assertEqual(steps["s1"]["via"], "PillarA.Sub.step_lemma_a")
        self.assertEqual(steps["s1"]["root_hyps"], ["hA"])
        self.assertEqual(steps["s2"]["uses_steps"], ["s1"])
        self.assertEqual(steps["s2"]["root_hyps"], ["hA", "hPair.pB"])
        self.assertEqual(hw["terminal"]["via"], "PillarA.Sub.combine_big")
        self.assertEqual(hw["terminal"]["uses_steps"], ["s1", "s2"])
        self.assertIn("hT", hw["terminal"]["root_hyps"])

        rc_txt, out_txt, _ = self._cli("horn", "link_wiring", "--have-wiring", "--text")
        self.assertEqual(rc_txt, 0)
        self.assertIn("steps  (2 have/let):", out_txt)
        self.assertIn("have s2 : AuxConjB n", out_txt)
        self.assertIn("close  :", out_txt)

    def test_xrepo06_anchor_prefix_and_config(self):
        # Repo with `src_dir = "."` in `leanre.toml` emits `Bundles.lean:10` (no `src/` prefix!)
        with tempfile.TemporaryDirectory() as td:
            with open(os.path.join(td, "leanre.toml"), "w", encoding="utf-8") as f:
                f.write(
                    '[project]\nname = "demo_root"\nsrc_dir = "."\n'
                    'pinned_commit = "abc1234"\n'
                    'upstream_url_template = "https://example.org/demo/blob/{commit}/{path}#L{line}"\n'
                )
            with open(os.path.join(td, "Bundles.lean"), "w", encoding="utf-8") as f:
                f.write("namespace Demo\nstructure ProofBundle where\n  w : Nat\nend Demo\n")
            c = read_contract(td, "Bundles.lean", "Demo.ProofBundle")
            self.assertIsNotNone(c)
            self.assertEqual(c.anchor, "Bundles.lean:2")
            from decompile.source import resolve_source_config
            cfg = resolve_source_config(td)
            self.assertEqual(cfg["anchor_prefix"], "")
            self.assertEqual(
                c.upstream_url(cfg["upstream_url_template"], cfg["pinned_commit"]),
                "https://example.org/demo/blob/abc1234/Bundles.lean#L2",
            )
            # Schema validator also accepts root-relative `.lean:<line>` anchors
            d = json.loads(json.dumps(schema.TEMPLATE))
            d["root"] = "Demo.ProofBundle"
            d["nodes"] = [{
                "id": "Demo.ProofBundle", "kid": 1, "kind": "inductive", "module": "Bundles",
                "anchor": "Bundles.lean:2", "header": "structure ProofBundle",
                "dom": {"depth": 0, "subtree": 1, "idom": None},
                "role": "structure", "status": "READ", "verdict": "real", "tag": "L",
                "summary": "ok", "fields": [],
            }]
            self.assertEqual(schema.validate(d), [])

        # Real `examples/tiny_demo` check via CLI `--config`
        tiny_toml = os.path.join(REPO, "examples", "tiny_demo", "leanre.toml")
        if os.path.isfile(tiny_toml):
            rc, out, _ = self._cli(
                "contract", "ProofBundle",
                extra_flags=("--config", tiny_toml, "--src", os.path.join(REPO, "examples", "tiny_demo")),
            )
            self.assertEqual(rc, 0)
            self.assertIn("anchor   : Bundles.lean:10", out)
            self.assertNotIn("src/Bundles.lean", out)


class TestDecompileLoop6(unittest.TestCase):
    """Focused synthetic regression tests for Loop 6A upgrades:
    1. `decompile dom --contains X [Y ...] <Root>` (all arg orders, `--text`, JSON, `--continue-on-error`)
    2. `producers` dot-notation codomain (`(M.data ...).DIV C`, `d.DIV C`, rejecting relations) + batch errors
    3. Partial-prefix / infix resolution (`Deduction.IdentU` -> `Deduction.CH.IdentU`)
    4. Loud `[case-fold]` warning on `resolve`/`contract` + `--exact-case` refusal
    5. `--near` refusing zero-score tie-breaks across unrelated namespaces sharing a top-level folder
    6. Mutual co-inductive `consts` (`OrderCertificate`), `letI` field types, and `horn`/`contract` UX hints
    """

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.root = cls.tmp.name
        cls.src = os.path.join(cls.root, "src")
        for sub in (
            os.path.join("Formalism", "Chain"),
            os.path.join("Development", "BranchA"),
            os.path.join("Development", "BranchB"),
            os.path.join("Resolution", "Certs"),
        ):
            os.makedirs(os.path.join(cls.src, sub))

        with open(os.path.join(cls.src, "Formalism", "Chain", "Mean.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace Formalism.Weighted.Data\n"
                "def DIV (d : Nat) (c : Nat) : Prop := d ≤ c\n"
                "def Ga (d : Nat) : Nat := d\n"
                "end Formalism.Weighted.Data\n\n"
                "namespace Formalism.Lnk.Mod\n"
                "theorem data_DIV (c : Nat) : (mkData 1 2).DIV c := by trivial\n"
                "theorem var_DIV (d : Formalism.Weighted.Data) (c : Nat) : d.DIV c := by trivial\n"
                "theorem rel_not_producer (d : Formalism.Weighted.Data) : d.Ga + 1 ≤ 10 := by trivial\n"
                "end Formalism.Lnk.Mod\n\n"
                "namespace Deduction.CH\n"
                "def IdentU : Prop := True\n"
                "end Deduction.CH\n\n"
                "namespace Formalism.Basic.SizeData2\n"
                "def io : Nat := 0\n"
                "end Formalism.Basic.SizeData2\n\n"
                "namespace Formalism.HC\n"
                "structure Frame where\n"
                "  ord : Nat\n"
                "  grp : Nat\n"
                "  h0 : letI := grp; Fin ord → Nat\n"
                "  dfltField : Prop := True\n"
                "end Formalism.HC\n\n"
                "namespace Formalism.MainNotions\n"
                "def SizeT : Prop := True\n"
                "end Formalism.MainNotions\n"
            )

        with open(os.path.join(cls.src, "Development", "BranchA", "CtxMod.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace GlobalTheory.Mem.Top\n"
                "structure Ctx where\n"
                "  n : Nat\n"
                "end GlobalTheory.Mem.Top\n\n"
                "namespace GlobalTheory.Stage\n"
                "def SharedLeaf : Prop := True\n"
                "theorem OutsideConsumer : SharedLeaf := trivial\n"
                "theorem DomChild : SharedLeaf := trivial\n"
                "theorem StageRoot (h : DomChild) : Prop := by\n"
                "  obtain ⟨hE, -, _, hN⟩ := h\n"
                "  exact hN\n"
                "theorem TermProof : SharedLeaf := trivial\n"
                "end GlobalTheory.Stage\n"
            )

        with open(os.path.join(cls.src, "Development", "BranchB", "OtherSize.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace PositivityTheory.E3\n"
                "def SizeT : Prop := False\n"
                "end PositivityTheory.E3\n"
            )

        with open(os.path.join(cls.src, "Resolution", "Certs", "MutualCert.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace Functorial.Res\n"
                "mutual\n"
                "inductive PrincipalCert : Nat → Prop\n"
                "  | base : PrincipalCert 0\n"
                "  | toOrd (n : Nat) (h : OrderCert n) : PrincipalCert n\n\n"
                "inductive OrderCert : Nat → Prop\n"
                "  | memory : OrderCert 0\n"
                "  | descend (n : Nat) : OrderCert (n + 1)\n"
                "end\n"
                "end Functorial.Res\n"
            )

        cls.kdb_path = os.path.join(cls.root, "kernel.db")
        cls.ldb_path = os.path.join(cls.root, "leanre.db")
        kcon = sqlite3.connect(cls.kdb_path)
        kcon.executescript(
            """
            CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
               type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
               fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
               live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
               sighash TEXT, sighash_anon TEXT);
            CREATE UNIQUE INDEX decls_name ON decls(name);
            CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL);
            CREATE UNIQUE INDEX consts_name ON consts(name);
            CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
            CREATE INDEX edges_dst ON edges(dst, src);
            CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
            CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
            CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
            CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
            """
        )
        decls = [
            (1, "Formalism.Weighted.Data.DIV", "def", 1, 2, 2, 3, 0, 0, 0, 0, 1, 1, 1, 0),
            (2, "Formalism.Weighted.Data.Ga", "def", 1, 2, 2, 2, 0, 0, 0, 0, 1, 1, 1, 0),
            (3, "Formalism.Lnk.Mod.data_DIV", "thm", 1, 4, 10, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (4, "Formalism.Lnk.Mod.var_DIV", "thm", 1, 4, 8, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (5, "Formalism.Lnk.Mod.rel_not_producer", "thm", 1, 4, 8, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (6, "Deduction.CH.IdentU", "def", 1, 2, 2, 1, 0, 0, 0, 0, 1, 1, 1, 0),
            (7, "Formalism.Basic.SizeData2.io", "def", 1, 2, 2, 1, 0, 0, 0, 0, 1, 1, 1, 0),
            (8, "Formalism.HC.Frame", "inductive", 1, 6, 6, 2, 0, 0, 0, 0, 1, 1, 1, 0),
            (9, "Formalism.MainNotions.SizeT", "def", 1, 2, 2, 5, 0, 0, 0, 0, 1, 1, 1, 0),
            (10, "PositivityTheory.E3.SizeT", "def", 1, 2, 2, 1, 0, 0, 0, 0, 1, 1, 1, 0),
            (11, "GlobalTheory.Mem.Top.Ctx", "inductive", 1, 3, 3, 4, 0, 0, 0, 0, 1, 1, 1, 0),
            (12, "GlobalTheory.TopEntry", "thm", 1, 2, 10, 0, 2, 0, 2, 0, 1, 1, 1, 0),
            (13, "GlobalTheory.Stage.StageRoot", "thm", 1, 3, 20, 1, 1, 0, 1, 0, 1, 1, 1, 0),
            (14, "GlobalTheory.Stage.DomChild", "thm", 1, 2, 5, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (15, "GlobalTheory.Stage.OutsideConsumer", "thm", 1, 2, 5, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (16, "GlobalTheory.Stage.SharedLeaf", "def", 1, 2, 2, 3, 0, 0, 0, 0, 1, 1, 1, 0),
            (17, "GlobalTheory.Stage.TermProof", "thm", 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (18, "Functorial.Res.PrincipalCert", "inductive", 2, 10, 10, 5, 0, 0, 0, 0, 31, 1, 1, 0),
        ]
        for row in decls:
            kcon.execute("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NULL,NULL)", row)

        kcon.executemany(
            "INSERT INTO consts VALUES (?,?,?,?,?)",
            [
                (100, "Functorial.Res.PrincipalCert", 18, "induct", 0),
                (101, "Functorial.Res.OrderCert", 18, "induct", 1),
                (102, "Functorial.Res.OrderCert.memory", 18, "ctor", 2),
                (103, "Functorial.Res.OrderCert.descend", 18, "ctor", 3),
            ],
        )
        mods = [
            (1, "Formalism.Chain.Mean", "leanre_db:exact", None),
            (2, "Formalism.Chain.Mean", "leanre_db:exact", None),
            (3, "Formalism.Chain.Mean", "leanre_db:exact", None),
            (4, "Formalism.Chain.Mean", "leanre_db:exact", None),
            (5, "Formalism.Chain.Mean", "leanre_db:exact", None),
            (6, "Formalism.Chain.Mean", "leanre_db:exact", None),
            (7, "Formalism.Chain.Mean", "aux_prefix:leanre_db", None),
            (8, "Formalism.Chain.Mean", "leanre_db:exact", None),
            (9, "Formalism.Chain.Mean", "leanre_db:exact", None),
            (10, "Development.BranchB.OtherSize", "leanre_db:exact", None),
            (11, "Development.BranchA.CtxMod", "leanre_db:exact", None),
            (12, "Development.BranchA.CtxMod", "leanre_db:exact", None),
            (13, "Development.BranchA.CtxMod", "leanre_db:exact", None),
            (14, "Development.BranchA.CtxMod", "leanre_db:exact", None),
            (15, "Development.BranchA.CtxMod", "leanre_db:exact", None),
            (16, "Development.BranchA.CtxMod", "leanre_db:exact", None),
            (17, "Development.BranchA.CtxMod", "leanre_db:exact", None),
            (18, "Resolution.Certs.MutualCert", "leanre_db:exact", 1),
        ]
        kcon.executemany("INSERT INTO decl_module VALUES (?,?,?,?)", mods)
        edges = [
            (3, 1, 1),   # data_DIV -> Data.DIV
            (4, 1, 1),   # var_DIV -> Data.DIV
            (5, 2, 3),   # rel_not_producer -> Data.Ga (inequality, NOT producer)
            (12, 13, 2), # TopEntry -> StageRoot
            (12, 15, 2), # TopEntry -> OutsideConsumer
            (13, 14, 2), # StageRoot -> DomChild (dominated by StageRoot)
            (14, 16, 1), # DomChild -> SharedLeaf (in cone of StageRoot, but shared!)
            (15, 16, 1), # OutsideConsumer -> SharedLeaf (makes SharedLeaf idom = TopEntry!)
            (17, 16, 1),
        ]
        kcon.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
        kcon.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'all', '[12]', 18)")
        dom_rows = [
            (0, 12, None, 0, 5),
            (0, 13, 12, 1, 2),
            (0, 14, 13, 2, 1),
            (0, 15, 12, 1, 1),
            (0, 16, 12, 1, 1),
            (0, 3, None, 0, 50),
            (0, 4, None, 0, 20),
            (0, 18, None, 0, 10),
        ]
        kcon.executemany("INSERT INTO dom VALUES (?,?,?,?,?)", dom_rows)
        kcon.commit()
        kcon.close()

        lcon = sqlite3.connect(cls.ldb_path)
        lcon.executescript(
            """
            CREATE TABLE modules(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL, file_path TEXT NOT NULL);
            CREATE TABLE declarations(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, module TEXT NOT NULL,
                line_no INTEGER NOT NULL, signature_snippet TEXT NOT NULL, horn_requires_json TEXT NOT NULL, horn_proves TEXT);
            """
        )
        lcon.execute("INSERT INTO modules VALUES (1, 'Resolution.Certs.MutualCert', 'Resolution/Certs/MutualCert.lean')")
        lcon.executemany(
            "INSERT INTO declarations VALUES (?,?,?,?,?,?,?,?)",
            [
                (1, "Functorial.Res.PrincipalCert", "inductive", "Resolution.Certs.MutualCert", 3, "inductive PrincipalCert : Nat → Prop", "[]", None),
                (2, "Functorial.Res.OrderCert", "inductive", "Resolution.Certs.MutualCert", 7, "inductive OrderCert : Nat → Prop", "[]", None),
            ],
        )
        lcon.commit()
        lcon.close()

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _cli(self, *args: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        argv = [
            args[0],
            "--kernel-db", self.kdb_path,
            "--leanre-db", self.ldb_path,
            "--src", self.src,
            *args[1:],
        ]
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = decompile_main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_dom_contains_all_orders_text_json_and_continue_on_error(self):
        # Order 1: `dom --contains X Y Z --text <Root>`
        rc, out_txt, _ = self._cli(
            "dom", "--contains", "OutsideConsumer", "DomChild", "SharedLeaf", "--text", "StageRoot"
        )
        self.assertEqual(rc, 0)
        self.assertIn("dom --contains under GlobalTheory.Stage.StageRoot", out_txt)
        self.assertIn("no\tno\t-\t-\t1\toutside\tGlobalTheory.Stage.OutsideConsumer", out_txt)
        self.assertIn("yes\tyes\t1\t1\t1\tdominated\tGlobalTheory.Stage.DomChild", out_txt)
        self.assertIn("no\tyes\t2\t-\t1\tshared_in_cone\tGlobalTheory.Stage.SharedLeaf", out_txt)

        # Order 2: `dom <Root> --contains X Y` (JSON default)
        rc2, out_js, _ = self._cli("dom", "StageRoot", "--contains", "DomChild", "SharedLeaf")
        self.assertEqual(rc2, 0)
        doc = json.loads(out_js)
        self.assertEqual(doc["root"]["id"], "GlobalTheory.Stage.StageRoot")
        by_q = {r["query"]: r for r in doc["results"]}
        self.assertTrue(by_q["DomChild"]["dom_in"])
        self.assertEqual(by_q["DomChild"]["cone_dist"], 1)
        self.assertFalse(by_q["SharedLeaf"]["dom_in"])
        self.assertTrue(by_q["SharedLeaf"]["cone_in"])
        self.assertEqual(by_q["SharedLeaf"]["cone_dist"], 2)

        # Order 3: `dom --contains X Y <Root>` (no separating flag!)
        rc3, out_js3, _ = self._cli("dom", "--contains", "DomChild", "OutsideConsumer", "StageRoot")
        self.assertEqual(rc3, 0)
        doc3 = json.loads(out_js3)
        self.assertEqual(doc3["root"]["id"], "GlobalTheory.Stage.StageRoot")
        self.assertEqual([r["query"] for r in doc3["results"]], ["DomChild", "OutsideConsumer"])

        # `--continue-on-error` survives unresolved names in `--contains`
        rc4, out_coe, err_coe = self._cli(
            "dom", "--contains", "DomChild", "NoSuchDecl404", "--continue-on-error", "StageRoot"
        )
        self.assertEqual(rc4, 0)
        doc4 = json.loads(out_coe)
        self.assertEqual([r["query"] for r in doc4["results"]], ["DomChild"])
        self.assertEqual(doc4["missing"], ["NoSuchDecl404"])
        self.assertIn("NoSuchDecl404", err_coe)

        # `--text` on regular `dom` and `path`
        rc_dt, out_dt, _ = self._cli("dom", "TopEntry", "--depth", "1", "--min-size", "1", "--text")
        self.assertEqual(rc_dt, 0)
        self.assertIn("- GlobalTheory.TopEntry [thm]", out_dt)
        self.assertIn("- GlobalTheory.Stage.StageRoot [thm]", out_dt)

        rc_pt, out_pt, _ = self._cli("path", "StageRoot", "SharedLeaf", "--text")
        self.assertEqual(rc_pt, 0)
        self.assertIn("found (length=2, kind=both):", out_pt)
        self.assertIn("--[type]--> GlobalTheory.Stage.SharedLeaf", out_pt)

    def test_producers_dot_notation_and_batch_disambiguation(self):
        rc, out, _ = self._cli("producers", "Data.DIV", "--json")
        self.assertEqual(rc, 0)
        res = json.loads(out)
        names = [p["name"] for p in res["producers"]]
        self.assertEqual(names, ["Formalism.Lnk.Mod.data_DIV", "Formalism.Lnk.Mod.var_DIV"])

        # Relation inequality `d.Ga + 1 ≤ 10` is NOT a codomain producer of `Data.Ga`
        rc_ga, out_ga, _ = self._cli("producers", "Data.Ga", "--json")
        self.assertEqual(rc_ga, 0)
        self.assertEqual(json.loads(out_ga)["producers"], [])

        # Multi-target batch with an ambiguous first target does NOT discard unambiguous second target
        rc_b, out_b, err_b = self._cli("producers", "SizeT", "Data.DIV")
        self.assertEqual(rc_b, 1)
        self.assertIn("Formalism.MainNotions.SizeT", err_b)
        self.assertIn("PositivityTheory.E3.SizeT", err_b)
        self.assertIn("Formalism.Lnk.Mod.data_DIV", out_b)

        rc_b2, out_b2, _ = self._cli("producers", "SizeT", "Data.DIV", "--continue-on-error", "--json")
        self.assertEqual(rc_b2, 0)
        jb2 = json.loads(out_b2)
        self.assertEqual(jb2["missing"], ["SizeT"])
        self.assertEqual(jb2["results"][0]["target"]["name"], "Formalism.Weighted.Data.DIV")

    def test_infix_resolution(self):
        rc, out, _ = self._cli("contract", "Deduction.IdentU", "--json")
        self.assertEqual(rc, 0)
        j = json.loads(out)
        self.assertEqual(j["decl"]["name"], "Deduction.CH.IdentU")
        self.assertEqual(j["resolved_from"], "Deduction.IdentU")

        rc_r, out_r, _ = self._cli("resolve", "Deduction.IdentU", "--json")
        self.assertEqual(rc_r, 0)
        jr = json.loads(out_r)
        self.assertEqual(jr["candidates"][0]["name"], "Deduction.CH.IdentU")
        self.assertEqual(jr["candidates"][0]["match"], "infix")

    def test_case_fold_warning_and_exact_case_flag(self):
        # `contract SizeData2.IO` warns loudly on stderr & text output
        rc_txt, out_txt, err_txt = self._cli("contract", "SizeData2.IO")
        self.assertEqual(rc_txt, 0)
        self.assertIn("[case-fold]", err_txt)
        self.assertIn("[case-fold]", out_txt)
        self.assertIn("Formalism.Basic.SizeData2.io", out_txt)

        # JSON output stays pure JSON on stdout, sets `case_folded: true`, and warns on stderr
        rc_js, out_js, err_js = self._cli("contract", "SizeData2.IO", "--json")
        self.assertEqual(rc_js, 0)
        self.assertIn("[case-fold]", err_js)
        j = json.loads(out_js)
        self.assertTrue(j["case_folded"])
        self.assertEqual(j["decl"]["name"], "Formalism.Basic.SizeData2.io")

        # `--exact-case` refuses case-folding outright!
        rc_ec, _, err_ec = self._cli("contract", "SizeData2.IO", "--exact-case")
        self.assertEqual(rc_ec, 1)
        self.assertIn("--exact-case", err_ec)

        # `resolve` also emits `[case-fold]` warning and honors `--exact-case`
        rc_rv, out_rv, err_rv = self._cli("resolve", "SizeData2.IO", "--json")
        self.assertEqual(rc_rv, 0)
        self.assertIn("[case-fold]", err_rv)
        self.assertTrue(json.loads(out_rv)["case_folded"])

        rc_rv_ec, out_rv_ec, _ = self._cli("resolve", "SizeData2.IO", "--exact-case", "--json")
        self.assertEqual(rc_rv_ec, 1)
        self.assertEqual(json.loads(out_rv_ec)["candidates"], [])

    def test_near_refuses_zero_proximity_tie_break(self):
        # `Ctx` is in `Development.BranchA.CtxMod` (`GlobalTheory.Mem.Top.Ctx`);
        # `PositivityTheory.E3.SizeT` is in `Development.BranchB.OtherSize` (shares ONLY `Development`!).
        # `--near` MUST refuse to silently pick `PositivityTheory.E3.SizeT`!
        rc, _, err = self._cli("contract", "SizeT", "--near", "GlobalTheory.Mem.Top.Ctx")
        self.assertEqual(rc, 1)
        self.assertIn("ambiguous", err.lower())
        self.assertIn("Formalism.MainNotions.SizeT", err)
        self.assertIn("PositivityTheory.E3.SizeT", err)

    def test_mutual_inductive_letI_fields_and_ux_hints(self):
        # 1. Mutual co-inductive `OrderCert` is live (NOT dead_source_only) and reads line 7 contract
        rc_res, out_res, _ = self._cli("resolve", "OrderCert", "--json")
        self.assertEqual(rc_res, 0)
        cand0 = json.loads(out_res)["candidates"][0]
        self.assertEqual(cand0["name"], "Functorial.Res.OrderCert")
        self.assertEqual(cand0["id"], 18)
        self.assertNotEqual(cand0["match"], "dead_source_only")

        rc_oc, out_oc, _ = self._cli("contract", "Functorial.Res.OrderCert", "--json")
        self.assertEqual(rc_oc, 0)
        j_oc = json.loads(out_oc)
        self.assertEqual(j_oc["decl"]["name"], "Functorial.Res.OrderCert")
        self.assertEqual(j_oc["contract"]["line"], 7)
        self.assertEqual([f["name"] for f in j_oc["contract"]["fields"]], ["memory", "descend"])

        # 2. `Frame.h0 : letI := grp; Fin ord → Nat` is NOT truncated at `:=`
        rc_fr, out_fr, _ = self._cli("contract", "Formalism.HC.Frame", "--json")
        self.assertEqual(rc_fr, 0)
        flds = {f["name"]: f for f in json.loads(out_fr)["contract"]["fields"]}
        self.assertEqual(flds["h0"]["type"], "letI := grp; Fin ord → Nat")
        self.assertFalse(flds["h0"]["default"])
        self.assertEqual(flds["dfltField"]["type"], "Prop")
        self.assertTrue(flds["dfltField"]["default"])

        # 3. `horn --have-wiring --text` preserves `-`/`_` placeholders and notes term-mode proofs
        rc_hw, out_hw, _ = self._cli("horn", "StageRoot", "--have-wiring", "--text")
        self.assertEqual(rc_hw, 0)
        self.assertIn("⟨hE, -, _, hN⟩", out_hw)

        rc_tm, out_tm, _ = self._cli("horn", "TermProof", "--have-wiring", "--text")
        self.assertEqual(rc_tm, 0)
        self.assertIn("0 have/obtain steps", out_tm)

        # 4. `contract <thm> --body` without `--include-thm` prints helpful hint
        rc_th, out_th, _ = self._cli("contract", "StageRoot", "--body")
        self.assertEqual(rc_th, 0)
        self.assertIn("--include-thm", out_th)


class TestDecompileLoop7(unittest.TestCase):
    """Focused synthetic regression tests for Loop 7A upgrades:
    1. `decompile readers <Target>` (`--field`, `<Struct>.<field>`, field census, `--conjunct`, wrapper `∧`-defs, conjunct census)
    2. `decompile contract --fields-grep REGEX` + `--grep REGEX -C N` on `structure` fields + bare `--body-lines N`
    3. `dom --contains` batch resilience (both with and without `--continue-on-error`), `.mk` constructor diagnostics, and auto-instance location
    4. `decompile horn --have-wiring` term-mode wiring (direct `exact`, pure term application with callee slot alignment, record literal, `where` fields)
    5. `decompile producers` premise/hypothesis consumer hints, record-field carriers, wrapper producers, and `--include-implications`
    """

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.root = cls.tmp.name
        cls.src = os.path.join(cls.root, "src")
        os.makedirs(os.path.join(cls.src, "Audit"))

        with open(os.path.join(cls.src, "Audit", "Sample.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace Audit.Pkg\n\n"
                "def CarrierType (n : Nat) : Type := Fin (n + 1)\n\n"
                "instance : Nonempty (CarrierType 0) := ⟨⟨0, Nat.zero_lt_one⟩⟩\n"
                "instance : Subsingleton (CarrierType 0) := ⟨fun a b => Subtype.ext (by omega)⟩\n\n"
                "structure AssumedHyps : Prop where\n"
                "  slotAlpha : Nat = Nat\n"
                "  slotBeta : True\n"
                "  slotCond : (∃ k : Nat, k > 0) → AssumedLeaf\n"
                "  slotUnused : True\n"
                "  slotOmega : Bool = Bool\n\n"
                "def AssumedLeaf : Prop := ∀ m : Nat, m = m\n"
                "def CondWrap : Prop := (0 < 1) → AssumedLeaf\n"
                "theorem prove_cond_wrap : CondWrap := fun _ _ => rfl\n"
                "theorem use_assumed_leaf (hL : AssumedLeaf) : 0 = 0 := hL 0\n\n"
                "def CoreBounds (a b c : Nat) : Prop :=\n"
                "  a ≤ b ∧\n"
                "  b ≤ c ∧\n"
                "  a ≤ c\n\n"
                "def AllBounds (a b c : Nat) : Prop :=\n"
                "  True ∧ CoreBounds a b c ∧ c = c\n\n"
                "theorem build_core (a : Nat) : CoreBounds a a a := ⟨le_rfl, le_rfl, le_rfl⟩\n\n"
                "theorem read_field_dot (H : AssumedHyps) : Nat = Nat :=\n"
                "  H.slotAlpha\n\n"
                "theorem read_conj1_via_wrapper (a b c : Nat) (hAll : AllBounds a b c) : a ≤ b := by\n"
                "  obtain ⟨-, hCore, -⟩ := hAll\n"
                "  exact hCore.1\n\n"
                "theorem read_conj2_via_destruct (a b c : Nat) (hC : CoreBounds a b c) : b ≤ c := by\n"
                "  obtain ⟨-, hMid, -⟩ := hC\n"
                "  exact hMid\n\n"
                "theorem read_conj3_tail (a b c : Nat) (hC : CoreBounds a b c) : a ≤ c :=\n"
                "  hC.2.2\n\n"
                "theorem engine_step (p1 : Nat = Nat) (s : Nat) (hMid : s ≤ s) : Bool = Bool := rfl\n\n"
                "theorem closer_exact : (Nat = Nat) → ∀ s : Nat, s ≤ s → Bool = Bool := by\n"
                "  intro p1 s hS\n"
                "  exact engine_step p1 s hS\n\n"
                "theorem closer_term (p1 : Nat = Nat) (k : Nat) : Bool = Bool :=\n"
                "  engine_step p1 k (by omega)\n\n"
                "def mk_hyps_lit (hL : AssumedLeaf) : AssumedHyps :=\n"
                "  { slotAlpha := rfl, slotBeta := trivial, slotCond := fun _ => hL, slotUnused := trivial, slotOmega := rfl }\n\n"
                "def mk_hyps_where (hL : AssumedLeaf) : AssumedHyps where\n"
                "  slotAlpha := rfl\n"
                "  slotBeta := trivial\n"
                "  slotCond := fun _ => hL\n"
                "  slotUnused := trivial\n"
                "  slotOmega := rfl\n\n"
                "end Audit.Pkg\n"
            )

        cls.kdb_path = os.path.join(cls.root, "kernel.db")
        cls.ldb_path = os.path.join(cls.root, "leanre.db")
        kcon = sqlite3.connect(cls.kdb_path)
        kcon.executescript(
            """
            CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
               type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
               fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
               live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
               sighash TEXT, sighash_anon TEXT);
            CREATE UNIQUE INDEX decls_name ON decls(name);
            CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL);
            CREATE UNIQUE INDEX consts_name ON consts(name);
            CREATE INDEX consts_decl ON consts(decl_id);
            CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
            CREATE INDEX edges_dst ON edges(dst, src);
            CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
            CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
            CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
            CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
            """
        )
        decls = [
            (1, "Audit.Pkg.CarrierType", "def", 1, 2, 3, 2, 0, 0, 0, 0, 1, 1, 1, 0),
            (2, "Audit.Pkg.instNonemptyCarrierType", "def", 1, 2, 3, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (3, "Audit.Pkg.instSubsingletonCarrierType", "thm", 1, 2, 3, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (4, "Audit.Pkg.AssumedHyps", "inductive", 2, 6, 6, 4, 1, 1, 0, 0, 1, 1, 1, 0),
            (5, "Audit.Pkg.AssumedHyps.slotAlpha", "def", 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (6, "Audit.Pkg.AssumedHyps.slotCond", "def", 1, 3, 2, 0, 2, 2, 0, 0, 1, 1, 1, 0),
            (7, "Audit.Pkg.AssumedHyps.slotUnused", "def", 1, 2, 2, 0, 1, 1, 0, 0, 1, 1, 1, 0),
            (8, "Audit.Pkg.AssumedLeaf", "def", 1, 2, 2, 4, 0, 0, 0, 0, 1, 1, 1, 0),
            (9, "Audit.Pkg.CondWrap", "def", 1, 2, 2, 1, 1, 0, 1, 0, 1, 1, 1, 0),
            (10, "Audit.Pkg.prove_cond_wrap", "thm", 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (11, "Audit.Pkg.use_assumed_leaf", "thm", 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (12, "Audit.Pkg.CoreBounds", "def", 1, 3, 5, 4, 0, 0, 0, 0, 1, 1, 1, 0),
            (13, "Audit.Pkg.AllBounds", "def", 1, 3, 5, 1, 1, 0, 1, 0, 1, 1, 1, 0),
            (14, "Audit.Pkg.build_core", "thm", 1, 2, 4, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (15, "Audit.Pkg.read_field_dot", "thm", 1, 2, 3, 1, 2, 1, 1, 0, 1, 1, 1, 0),
            (16, "Audit.Pkg.read_conj1_via_wrapper", "thm", 1, 3, 5, 1, 2, 1, 1, 0, 1, 1, 1, 0),
            (17, "Audit.Pkg.read_conj2_via_destruct", "thm", 1, 3, 5, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (18, "Audit.Pkg.read_conj3_tail", "thm", 1, 3, 4, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (19, "Audit.Pkg.engine_step", "thm", 1, 3, 2, 2, 0, 0, 0, 0, 1, 1, 1, 0),
            (20, "Audit.Pkg.closer_exact", "thm", 1, 4, 5, 1, 1, 0, 1, 0, 1, 1, 1, 0),
            (21, "Audit.Pkg.closer_term", "thm", 1, 4, 5, 1, 1, 0, 1, 0, 1, 1, 1, 0),
            (22, "Audit.Pkg.mk_hyps_lit", "def", 1, 3, 5, 1, 2, 2, 0, 0, 1, 1, 1, 0),
            (23, "Audit.Pkg.mk_hyps_where", "def", 1, 3, 5, 1, 2, 2, 0, 0, 1, 1, 1, 0),
            (24, "Nonempty", "inductive", 1, 2, 2, 10, 0, 0, 0, 0, 1, 1, 1, 0),
            (25, "Subsingleton", "inductive", 1, 2, 2, 10, 0, 0, 0, 0, 1, 1, 1, 0),
        ]
        for row in decls:
            kcon.execute("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NULL,NULL)", row)

        kcon.executemany(
            "INSERT INTO consts VALUES (?,?,?,?,?)",
            [
                (100, "Audit.Pkg.AssumedHyps", 4, "induct", 0),
                (101, "Audit.Pkg.AssumedHyps.mk", 4, "ctor", 1),
            ],
        )
        mods = [
            (1, "Audit.Sample", "leanre_db:exact", 1),
            (2, None, "unmatched:project_auto_instance", None),
            (3, None, "unmatched:project_auto_instance", None),
            (4, "Audit.Sample", "leanre_db:exact", 4),
            (5, "Audit.Sample", "aux_prefix:leanre_db", None),
            (6, "Audit.Sample", "aux_prefix:leanre_db", None),
            (7, "Audit.Sample", "aux_prefix:leanre_db", None),
            (8, "Audit.Sample", "leanre_db:exact", 8),
            (9, "Audit.Sample", "leanre_db:exact", 9),
            (10, "Audit.Sample", "leanre_db:exact", 10),
            (11, "Audit.Sample", "leanre_db:exact", 11),
            (12, "Audit.Sample", "leanre_db:exact", 12),
            (13, "Audit.Sample", "leanre_db:exact", 13),
            (14, "Audit.Sample", "leanre_db:exact", 14),
            (15, "Audit.Sample", "leanre_db:exact", 15),
            (16, "Audit.Sample", "leanre_db:exact", 16),
            (17, "Audit.Sample", "leanre_db:exact", 17),
            (18, "Audit.Sample", "leanre_db:exact", 18),
            (19, "Audit.Sample", "leanre_db:exact", 19),
            (20, "Audit.Sample", "leanre_db:exact", 20),
            (21, "Audit.Sample", "leanre_db:exact", 21),
            (22, "Audit.Sample", "leanre_db:exact", 22),
            (23, "Audit.Sample", "leanre_db:exact", 23),
            (24, None, "unmatched:challenge_library", None),
            (25, None, "unmatched:challenge_library", None),
        ]
        kcon.executemany("INSERT INTO decl_module VALUES (?,?,?,?)", mods)
        edges = [
            (2, 1, 3), (2, 24, 3),
            (3, 1, 3), (3, 25, 3),
            (5, 4, 1),
            (6, 4, 1), (6, 8, 1),
            (7, 4, 1),
            (9, 8, 2),
            (10, 9, 1),
            (11, 8, 1),
            (13, 12, 2),
            (14, 12, 1),
            (15, 4, 1), (15, 5, 2),
            (16, 13, 1), (16, 12, 2),
            (17, 12, 3),
            (18, 12, 3),
            (20, 19, 2),
            (21, 19, 2),
            (20, 16, 2),
            (22, 4, 1), (22, 8, 1),
            (23, 4, 1), (23, 8, 1),
        ]
        kcon.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
        kcon.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'all', '[20]', 25)")
        dom_rows = [
            (0, 20, None, 0, 10),
            (0, 16, 20, 1, 3),
            (0, 12, 16, 2, 1),
            (0, 19, 20, 1, 1),
            (0, 15, None, 0, 5),
            (0, 17, None, 0, 4),
            (0, 18, None, 0, 2),
            (0, 10, None, 0, 7),
            (0, 11, None, 0, 6),
        ]
        kcon.executemany("INSERT INTO dom VALUES (?,?,?,?,?)", dom_rows)
        kcon.commit()
        kcon.close()

        lcon = sqlite3.connect(cls.ldb_path)
        lcon.executescript(
            """
            CREATE TABLE modules(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL, file_path TEXT NOT NULL);
            CREATE TABLE declarations(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, module TEXT NOT NULL,
                line_no INTEGER NOT NULL, signature_snippet TEXT NOT NULL, horn_requires_json TEXT NOT NULL, horn_proves TEXT);
            """
        )
        lcon.execute("INSERT INTO modules VALUES (1, 'Audit.Sample', 'Audit/Sample.lean')")
        lcon.executemany(
            "INSERT INTO declarations VALUES (?,?,?,?,?,?,?,?)",
            [
                (1, "Audit.Pkg.CarrierType", "def", "Audit.Sample", 3, "def CarrierType (n : Nat) : Type", "[]", None),
                (201, "Audit.Pkg._anon_5", "instance", "Audit.Sample", 5, "instance : Nonempty (CarrierType 0)", "[]", None),
                (202, "Audit.Pkg._anon_6", "instance", "Audit.Sample", 6, "instance : Subsingleton (CarrierType 0)", "[]", None),
                (4, "Audit.Pkg.AssumedHyps", "structure", "Audit.Sample", 8, "structure AssumedHyps : Prop", "[]", None),
                (8, "Audit.Pkg.AssumedLeaf", "def", "Audit.Sample", 15, "def AssumedLeaf : Prop", "[]", None),
                (9, "Audit.Pkg.CondWrap", "def", "Audit.Sample", 16, "def CondWrap : Prop", "[]", None),
                (10, "Audit.Pkg.prove_cond_wrap", "theorem", "Audit.Sample", 17, "theorem prove_cond_wrap : CondWrap", "[]", "CondWrap"),
                (11, "Audit.Pkg.use_assumed_leaf", "theorem", "Audit.Sample", 18, "theorem use_assumed_leaf (hL : AssumedLeaf) : 0 = 0", "[]", None),
                (12, "Audit.Pkg.CoreBounds", "def", "Audit.Sample", 20, "def CoreBounds (a b c : Nat) : Prop", "[]", None),
                (13, "Audit.Pkg.AllBounds", "def", "Audit.Sample", 25, "def AllBounds (a b c : Nat) : Prop", "[]", None),
                (14, "Audit.Pkg.build_core", "theorem", "Audit.Sample", 28, "theorem build_core (a : Nat) : CoreBounds a a a", "[]", "CoreBounds"),
                (15, "Audit.Pkg.read_field_dot", "theorem", "Audit.Sample", 30, "theorem read_field_dot (H : AssumedHyps) : Nat = Nat", "[]", None),
                (16, "Audit.Pkg.read_conj1_via_wrapper", "theorem", "Audit.Sample", 33, "theorem read_conj1_via_wrapper", "[]", None),
                (17, "Audit.Pkg.read_conj2_via_destruct", "theorem", "Audit.Sample", 37, "theorem read_conj2_via_destruct", "[]", None),
                (18, "Audit.Pkg.read_conj3_tail", "theorem", "Audit.Sample", 41, "theorem read_conj3_tail", "[]", None),
                (19, "Audit.Pkg.engine_step", "theorem", "Audit.Sample", 44, "theorem engine_step", "[]", None),
                (20, "Audit.Pkg.closer_exact", "theorem", "Audit.Sample", 46, "theorem closer_exact", "[]", None),
                (21, "Audit.Pkg.closer_term", "theorem", "Audit.Sample", 50, "theorem closer_term", "[]", None),
                (22, "Audit.Pkg.mk_hyps_lit", "def", "Audit.Sample", 53, "def mk_hyps_lit", "[]", None),
                (23, "Audit.Pkg.mk_hyps_where", "def", "Audit.Sample", 56, "def mk_hyps_where", "[]", None),
            ],
        )
        lcon.commit()
        lcon.close()

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _cli(self, *args: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        argv = [
            args[0],
            "--kernel-db", self.kdb_path,
            "--leanre-db", self.ldb_path,
            "--src", self.src,
            *args[1:],
        ]
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = decompile_main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_readers_field_and_conjuncts(self):
        # 1. Structure field reader lookup (`--field` and `<Struct>.<field>` shorthand)
        rc, out, _ = self._cli("readers", "AssumedHyps", "--field", "slotAlpha", "--json")
        self.assertEqual(rc, 0)
        rf = json.loads(out)
        self.assertEqual(rf["mode"], "field")
        self.assertEqual(rf["live_count"], 1)
        self.assertEqual(rf["readers"][0]["name"], "Audit.Pkg.read_field_dot")
        self.assertEqual(rf["readers"][0]["line"], 31)
        self.assertEqual(rf["readers"][0]["site_kind"], "dot_proj")

        rc_sh, out_sh, _ = self._cli("readers", "AssumedHyps.slotAlpha")
        self.assertEqual(rc_sh, 0)
        self.assertIn("Audit.Pkg.read_field_dot", out_sh)

        # Unread field returns 0 readers cleanly
        rc_un, out_un, _ = self._cli("readers", "AssumedHyps", "--field", "slotUnused", "--json")
        self.assertEqual(rc_un, 0)
        self.assertEqual(json.loads(out_un)["total_count"], 0)

        # Structure field census when `--field` is omitted
        rc_cen, out_cen, _ = self._cli("readers", "AssumedHyps", "--json")
        self.assertEqual(rc_cen, 0)
        cen = json.loads(out_cen)
        self.assertEqual(cen["mode"], "field_census")
        by_fn = {f["field"]: f["live_readers"] for f in cen["fields"]}
        self.assertEqual(by_fn["slotAlpha"], 1)
        self.assertEqual(by_fn["slotUnused"], 0)

        # 2. `∧`-conjunct readers (including wrapper `AllBounds`, `obtain` destructuring, and `.2.2` tail)
        rc_c1, out_c1, _ = self._cli("readers", "CoreBounds", "--conjunct", "1", "--json")
        self.assertEqual(rc_c1, 0)
        c1 = json.loads(out_c1)
        self.assertEqual([r["name"] for r in c1["readers"]], ["Audit.Pkg.read_conj1_via_wrapper"])
        self.assertEqual(c1["readers"][0]["line"], 35)
        # Producer `build_core` must NEVER be falsely reported as a reader!
        self.assertNotIn("Audit.Pkg.build_core", [r["name"] for r in c1["readers"]])

        rc_c2, out_c2, _ = self._cli("readers", "CoreBounds", "--conjunct", "2", "--json")
        self.assertEqual(rc_c2, 0)
        c2 = json.loads(out_c2)
        self.assertEqual([r["name"] for r in c2["readers"]], ["Audit.Pkg.read_conj2_via_destruct"])
        self.assertEqual(c2["readers"][0]["site_kind"], "destructure")
        self.assertEqual(c2["readers"][0]["line"], 39)

        rc_c3, out_c3, _ = self._cli("readers", "CoreBounds", "--conjunct", "3", "--json")
        self.assertEqual(rc_c3, 0)
        c3 = json.loads(out_c3)
        self.assertEqual([r["name"] for r in c3["readers"]], ["Audit.Pkg.read_conj3_tail"])
        self.assertEqual(c3["readers"][0]["line"], 42)

        # Out-of-range `--conjunct` reports error cleanly
        rc_bad, _, err_bad = self._cli("readers", "CoreBounds", "--conjunct", "9")
        self.assertEqual(rc_bad, 1)
        self.assertIn("out of range", err_bad)

    def test_contract_fields_grep_and_structure_grep(self):
        # `--fields-grep` filters structure fields compactly with line numbers
        rc, out, _ = self._cli("contract", "AssumedHyps", "--fields-grep", "Cond|Omega")
        self.assertEqual(rc, 0)
        self.assertIn("fields   : /Cond|Omega/ (2/5 field(s) matched)", out)
        self.assertIn(".slotCond :", out)
        self.assertIn(".slotOmega :", out)
        self.assertNotIn(".slotAlpha :", out)

        # `--grep` on a `structure` ALSO filters fields with `-C` instead of dumping all fields unfiltered!
        rc_g, out_g, _ = self._cli("contract", "AssumedHyps", "--grep", "slotCond", "-C", "1", "--json")
        self.assertEqual(rc_g, 0)
        jg = json.loads(out_g)
        self.assertEqual(jg["fields_grep"]["match_count"], 1)
        self.assertEqual([f["name"] for f in jg["contract"]["fields"]], ["slotBeta", "slotCond", "slotUnused"])

        # Bare `--body-lines N` works as `1:N`
        rc_bl, out_bl, _ = self._cli("contract", "CoreBounds", "--body-lines", "2", "--json")
        self.assertEqual(rc_bl, 0)
        self.assertEqual(len(json.loads(out_bl)["body_slice"]["lines"]), 2)

    def test_mk_constructor_auto_instances_and_dom_contains_resilience(self):
        # 1. `.mk` constructor resolution & clean diagnostic pointing to parent structure + `bundles --instantiations`
        rc_r, out_r, _ = self._cli("resolve", "AssumedHyps.mk", "--json")
        self.assertEqual(rc_r, 0)
        self.assertEqual(json.loads(out_r)["candidates"][0]["name"], "Audit.Pkg.AssumedHyps.mk")
        self.assertEqual(json.loads(out_r)["candidates"][0]["kind"], "ctor")

        rc_c, out_c, _ = self._cli("contract", "AssumedHyps.mk")
        self.assertEqual(rc_c, 0)
        self.assertIn("ctor_of  : Audit.Pkg.AssumedHyps [structure]", out_c)
        self.assertIn("leanre bundles --instantiations Audit.Pkg.AssumedHyps", out_c)

        # 2. Anonymous auto-instances (`instNonemptyCarrierType`, `instSubsingletonCarrierType`) locate exact source lines
        rc_ai, out_ai, _ = self._cli("contract", "instNonemptyCarrierType", "instSubsingletonCarrierType")
        self.assertEqual(rc_ai, 0)
        self.assertNotIn("OPAQUE", out_ai)
        self.assertIn("Audit/Sample.lean:5", out_ai)
        self.assertIn("Audit/Sample.lean:6", out_ai)
        self.assertIn("instance : Nonempty (CarrierType 0)", out_ai)

        # 3. `dom --contains` WITHOUT `--continue-on-error` does NOT discard valid targets on a typo (exits rc=1 with results + missing)
        rc_dc, out_dc, err_dc = self._cli(
            "dom", "--contains", "Audit.Pkg.TypoMissingDecl", "read_conj1_via_wrapper", "closer_exact"
        )
        self.assertEqual(rc_dc, 1)
        doc_dc = json.loads(out_dc)
        self.assertEqual([r["id"] for r in doc_dc["results"]], ["Audit.Pkg.read_conj1_via_wrapper"])
        self.assertEqual(doc_dc["missing"], ["Audit.Pkg.TypoMissingDecl"])
        self.assertIn("TypoMissingDecl", err_dc)

    def test_horn_term_mode_and_record_wiring(self):
        # 1. Single-`exact` tactical closer aligns positional args with callee's `→` and `∀` slots
        rc_ex, out_ex, _ = self._cli("horn", "closer_exact", "--have-wiring")
        self.assertEqual(rc_ex, 0)
        tw_ex = json.loads(out_ex)["have_wiring"]["term_wiring"]
        self.assertEqual(tw_ex["mode"], "application")
        self.assertEqual(tw_ex["callee"], "Audit.Pkg.engine_step")
        self.assertEqual([a["param_name"] for a in tw_ex["args"]], ["p1", "s", "hMid"])
        self.assertEqual([a["kind"] for a in tw_ex["args"]], ["passthrough", "passthrough", "passthrough"])

        # 2. Pure term-mode application (`closer_term` without `by`) extracts callee + tactic/passthrough args
        rc_tm, out_tm, _ = self._cli("horn", "closer_term", "--have-wiring", "--text")
        self.assertEqual(rc_tm, 0)
        self.assertIn("application -> Audit.Pkg.engine_step (3 arg(s))", out_tm)
        self.assertIn("#3 [tactic] (hMid : s ≤ s) <- (by omega)", out_tm)

        # 3. Record literal `{ f := ... }` and `where` fields
        rc_rl, out_rl, _ = self._cli("horn", "mk_hyps_lit", "--have-wiring")
        self.assertEqual(rc_rl, 0)
        tw_rl = json.loads(out_rl)["have_wiring"]["term_wiring"]
        self.assertEqual(tw_rl["mode"], "record_literal")
        self.assertEqual(len(tw_rl["fields"]), 5)

        rc_wh, out_wh, _ = self._cli("horn", "mk_hyps_where", "--have-wiring")
        self.assertEqual(rc_wh, 0)
        tw_wh = json.loads(out_wh)["have_wiring"]["term_wiring"]
        self.assertEqual(tw_wh["mode"], "where_fields")
        self.assertEqual([f["field"] for f in tw_wh["fields"]], ["slotAlpha", "slotBeta", "slotCond", "slotUnused", "slotOmega"])

    def test_producers_premise_and_wrapper_hints(self):
        rc, out_js, _ = self._cli("producers", "AssumedLeaf", "--json")
        self.assertEqual(rc, 0)
        data = json.loads(out_js)
        self.assertEqual(data["total_count"], 0)
        self.assertGreaterEqual(data["premise_consumers_count"], 1)
        p_names = [x["name"] for x in data["premise_consumers"]]
        self.assertIn("Audit.Pkg.use_assumed_leaf", p_names)
        rf_names = [x["field"] for x in data["record_field_carriers"]]
        self.assertIn("Audit.Pkg.AssumedHyps.slotCond", rf_names)
        self.assertTrue(data["record_field_carriers"][0]["conditional"])
        wp_names = [x["name"] for x in data["wrapper_producers"]]
        self.assertIn("Audit.Pkg.prove_cond_wrap", wp_names)

        rc_txt, out_txt, _ = self._cli("producers", "AssumedLeaf")
        self.assertEqual(rc_txt, 0)
        self.assertIn("wrapper producer(s)", out_txt)
        self.assertIn("premise/hypothesis uses:", out_txt)
        self.assertIn("record-field carrier(s)", out_txt)


class TestDecompileLoop9(unittest.TestCase):
    """Loop 9 regressions:
    1. `decompile dom --contains X -- ROOT --text` trailing option reparsing
    2. `decompile readers --field` following `extends` (parent + child projections)
    3. `decompile contract` multi-line signature headers with `|...|` conclusion
    4. `--continue-on-error` resilience on ambiguous short names in batch commands
    """

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.root = cls.tmp.name
        cls.src = os.path.join(cls.root, "src")
        os.makedirs(os.path.join(cls.src, "Ext"))

        with open(os.path.join(cls.src, "Ext", "Base.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace Ext.Base\n\n"
                "structure BaseData (n : Nat) where\n"
                "  baseVal : Nat\n"
                "  baseProp : baseVal = baseVal\n\n"
                "theorem use_base_val (d : BaseData 1) : Nat :=\n"
                "  d.baseVal\n\n"
                "end Ext.Base\n"
            )

        with open(os.path.join(cls.src, "Ext", "Child.lean"), "w", encoding="utf-8") as f:
            f.write(
                "namespace Ext.Child\n\n"
                "structure ChildData (n : Nat) extends Ext.Base.BaseData n where\n"
                "  childVal : Nat\n\n"
                "structure WrapperOnly (n : Nat) extends ChildData n\n\n"
                "theorem use_child_inherited (c : ChildData 1) : Nat :=\n"
                "  c.baseVal + c.childVal\n\n"
                "theorem abs_multiline_bound {a b : Int} (h : a ≤ b) :\n"
                "    |a - b| ≤ 10 := by\n"
                "  omega\n\n"
                "def match_still_splits : Nat → Nat\n"
                "  | 0 => 1\n"
                "  | k + 1 => k\n\n"
                "def AmbigShort : Prop := True\n"
                "end Ext.Child\n\n"
                "namespace Ext.Other\n"
                "def AmbigShort : Prop := False\n"
                "end Ext.Other\n"
            )

        cls.kdb_path = os.path.join(cls.root, "kernel.db")
        cls.ldb_path = os.path.join(cls.root, "leanre.db")
        kcon = sqlite3.connect(cls.kdb_path)
        kcon.executescript(
            """
            CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
               type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
               fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
               live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
               sighash TEXT, sighash_anon TEXT);
            CREATE UNIQUE INDEX decls_name ON decls(name);
            CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL);
            CREATE UNIQUE INDEX consts_name ON consts(name);
            CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
            CREATE INDEX edges_dst ON edges(dst, src);
            CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
            CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
            CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
            CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
            """
        )
        decls = [
            (1, "Ext.Base.BaseData", "inductive", 1, 3, 3, 4, 0, 0, 0, 0, 1, 1, 1, 0),
            (2, "Ext.Base.BaseData.baseVal", "def", 1, 2, 2, 2, 1, 1, 0, 0, 1, 1, 1, 0),
            (3, "Ext.Base.use_base_val", "thm", 1, 2, 3, 1, 2, 1, 1, 0, 1, 1, 1, 0),
            (4, "Ext.Child.ChildData", "inductive", 1, 3, 3, 3, 1, 1, 0, 0, 1, 1, 1, 0),
            (5, "Ext.Child.ChildData.childVal", "def", 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (6, "Ext.Child.WrapperOnly", "inductive", 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 1, 0),
            (7, "Ext.Child.use_child_inherited", "thm", 1, 2, 4, 1, 3, 1, 2, 0, 1, 1, 1, 0),
            (8, "Ext.Child.abs_multiline_bound", "thm", 1, 3, 4, 0, 1, 0, 1, 0, 1, 1, 1, 0),
            (9, "Ext.Child.match_still_splits", "def", 1, 2, 3, 0, 0, 0, 0, 0, 1, 1, 1, 0),
            (10, "Ext.Child.AmbigShort", "def", 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0),
            (11, "Ext.Other.AmbigShort", "def", 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0),
        ]
        for row in decls:
            kcon.execute("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NULL,NULL)", row)
        mods = [
            (1, "Ext.Base", "leanre_db:exact", None),
            (2, "Ext.Base", "aux_prefix:leanre_db", None),
            (3, "Ext.Base", "leanre_db:exact", None),
            (4, "Ext.Child", "leanre_db:exact", None),
            (5, "Ext.Child", "aux_prefix:leanre_db", None),
            (6, "Ext.Child", "leanre_db:exact", None),
            (7, "Ext.Child", "leanre_db:exact", None),
            (8, "Ext.Child", "leanre_db:exact", None),
            (9, "Ext.Child", "leanre_db:exact", None),
            (10, "Ext.Child", "leanre_db:exact", None),
            (11, "Ext.Other", "leanre_db:exact", None),
        ]
        kcon.executemany("INSERT INTO decl_module VALUES (?,?,?,?)", mods)
        edges = [
            (2, 1, 1),
            (3, 1, 1), (3, 2, 2),
            (4, 1, 1),
            (5, 4, 1),
            (6, 4, 1),
            (7, 4, 1), (7, 2, 2), (7, 5, 2),
            (8, 7, 2),
        ]
        kcon.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
        kcon.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'all', '[8]', 11)")
        dom_rows = [
            (0, 8, None, 0, 4),
            (0, 7, 8, 1, 3),
            (0, 4, 7, 2, 1),
            (0, 2, 7, 2, 1),
        ]
        kcon.executemany("INSERT INTO dom VALUES (?,?,?,?,?)", dom_rows)
        kcon.commit()
        kcon.close()

        lcon = sqlite3.connect(cls.ldb_path)
        lcon.executescript(
            """
            CREATE TABLE modules(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL, file_path TEXT NOT NULL);
            CREATE TABLE declarations(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, module TEXT NOT NULL,
                line_no INTEGER NOT NULL, signature_snippet TEXT NOT NULL, horn_requires_json TEXT NOT NULL, horn_proves TEXT);
            """
        )
        lcon.executemany(
            "INSERT INTO modules VALUES (?,?,?)",
            [(1, "Ext.Base", "Ext/Base.lean"), (2, "Ext.Child", "Ext/Child.lean")],
        )
        lcon.commit()
        lcon.close()

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _cli(self, *args: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        argv = [args[0], "--kernel-db", self.kdb_path, "--leanre-db", self.ldb_path, "--src", self.src, *args[1:]]
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = decompile_main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_dom_contains_double_dash_trailing_root_and_flags(self):
        rc, out, _ = self._cli(
            "dom", "--contains", "use_child_inherited", "BaseData.baseVal", "--", "abs_multiline_bound", "--text"
        )
        self.assertEqual(rc, 0)
        self.assertIn("dom --contains under Ext.Child.abs_multiline_bound", out)
        self.assertIn("yes\tyes\t1\t1\t3\tdominated\tExt.Child.use_child_inherited", out)
        self.assertIn("yes\tyes\t2\t2\t1\tdominated\tExt.Base.BaseData.baseVal", out)

        rc2, out2, _ = self._cli(
            "dom", "--contains", "use_child_inherited", "--", "--text", "--project-only", "abs_multiline_bound"
        )
        self.assertEqual(rc2, 0)
        self.assertIn("dom --contains under Ext.Child.abs_multiline_bound", out2)

    def test_readers_field_follows_extends(self):
        # 1-hop inherited field (`ChildData --field baseVal`)
        rc, out, _ = self._cli("readers", "ChildData", "--field", "baseVal", "--json")
        self.assertEqual(rc, 0)
        res = json.loads(out)
        self.assertEqual(res["target"]["inherited_from"], "Ext.Base.BaseData")
        self.assertEqual(res["target"]["field_anchor"], "src/Ext/Base.lean:4")
        names = [r["name"] for r in res["readers"]]
        self.assertIn("Ext.Child.use_child_inherited", names)
        self.assertIn("Ext.Base.use_base_val", names)

        # 2-hop wrapper structure with 0 own fields (`WrapperOnly --field baseVal`) & census
        rc_w, out_w, _ = self._cli("readers", "WrapperOnly", "--field", "baseVal", "--text")
        self.assertEqual(rc_w, 0)
        self.assertIn("inherited_from: Ext.Base.BaseData", out_w)
        self.assertIn("Ext.Child.use_child_inherited", out_w)

        rc_cen, out_cen, _ = self._cli("readers", "WrapperOnly", "--json")
        self.assertEqual(rc_cen, 0)
        cen = json.loads(out_cen)
        fmap = {f["field"]: f for f in cen["fields"]}
        self.assertEqual(fmap["childVal"]["inherited_from"], "Ext.Child.ChildData")
        self.assertEqual(fmap["baseVal"]["inherited_from"], "Ext.Base.BaseData")
        self.assertEqual(fmap["baseVal"]["live_readers"], 2)

    def test_multiline_abs_signature_header_and_match_def(self):
        rc, out, _ = self._cli("contract", "abs_multiline_bound", "--json")
        self.assertEqual(rc, 0)
        j = json.loads(out)
        self.assertEqual(
            j["contract"]["header"],
            "theorem abs_multiline_bound {a b : Int} (h : a ≤ b) : |a - b| ≤ 10",
        )
        self.assertEqual(j["contract"]["type"], "|a - b| ≤ 10")

        rc_m, out_m, _ = self._cli("contract", "match_still_splits", "--body", "--json")
        self.assertEqual(rc_m, 0)
        jm = json.loads(out_m)
        self.assertEqual(jm["contract"]["header"], "def match_still_splits : Nat → Nat")
        self.assertEqual(jm["contract"]["body"], "| 0 => 1 | k + 1 => k")

    def test_continue_on_error_short_name_ambiguity(self):
        rc_c, out_c, err_c = self._cli("contract", "AmbigShort", "abs_multiline_bound", "--continue-on-error")
        self.assertEqual(rc_c, 0)
        self.assertIn("ambiguous", err_c.lower())
        self.assertIn("Ext.Child.abs_multiline_bound", out_c)
        self.assertIn("missing (1): AmbigShort", out_c)

        rc_d, out_d, _ = self._cli("dom", "AmbigShort", "use_child_inherited", "--min-size", "1", "--continue-on-error")
        self.assertEqual(rc_d, 0)
        jd = json.loads(out_d)
        self.assertEqual(jd["missing"], ["AmbigShort"])
        self.assertEqual([r["id"] for r in jd["results"]], ["Ext.Child.use_child_inherited"])

        rc_r, out_r, _ = self._cli("readers", "AmbigShort", "ChildData", "--field", "childVal", "--continue-on-error", "--json")
        self.assertEqual(rc_r, 0)
        jr = json.loads(out_r)
        self.assertEqual(jr["missing"], ["AmbigShort"])
        self.assertEqual(jr["results"][0]["target"]["name"], "Ext.Child.ChildData")


if __name__ == "__main__":
    unittest.main()
