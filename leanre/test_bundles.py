#!/usr/bin/env python3
"""Unit & integration test suite for `leanre.bundles` (`leanre bundles`).

Covers:
  1. Helper-theorem prefix filtering (`Used.adm`, `geometricLemma`) and `extends` subobjects.
  2. `casesOn` / `recOn` / `rec` eliminator fan-in exclusion (eliminating false positives).
  3. Empty `0`-field `Type*` placeholder detection (`LPTiedPlaceholder`).
  4. `abbrev := True` / `def := True` slot detection (`UnusedSlot72`, `fun _ => True`)
     and literal `: True` / `:= True` field detection.
  5. Sorting (`ratio|unread|dom|cone`), filtering (`--only`, `--min-fields`, `--top`, `--structure`),
     kernel-only fallback (`--no-src`), and JSON output schema (`leanre.bundles/1`).
  6. Symlink & strict read-only (`mode=ro`, `chmod 0444/0555`, `--out` symlink refusal) safety.
  7. CLI wiring in `leanre.py` (`leanre bundles`) and optional live-DB benchmark gates.
"""
from __future__ import annotations

import argparse
import importlib.util
import io
import json
import os
import sqlite3
import stat
import sys
import tempfile
import time
import unittest
from contextlib import redirect_stderr, redirect_stdout

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import bundles  # noqa: E402


def _load_leanre_cli():
    spec = importlib.util.spec_from_file_location("leanre_cli_entry", os.path.join(_HERE, "leanre.py"))
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


leanre_cli = _load_leanre_cli()


def _build_synthetic_bundles_fixture(td: str) -> dict:
    """Create a synthetic Lean source tree + `kernel.db` exercising every bundle scenario."""
    src = os.path.join(td, "src")
    os.makedirs(os.path.join(src, "Pkg"), exist_ok=True)

    files = {
        "Main.lean": (
            "import Pkg.Defs\n"
            "\n"
            "theorem main_goal : True :=\n"
            "  trivial\n"
        ),
        "Pkg/Defs.lean": (
            "namespace Pkg\n"
            "\n"
            "abbrev UnusedSlotTest : Prop := True\n"
            "def anyPred (_ : Nat) : Prop := fun _ => True\n"
            "\n"
            "structure BaseHyp : Prop where\n"
            "  base_ok : True\n"
            "\n"
            "-- 1. Prop structure with helper theorem sharing prefix + extends + abbrev := True slot\n"
            "structure KatoUsed (n : Nat) : Prop extends toBase : BaseHyp where\n"
            "  f1 : Nat = Nat\n"
            "  f2 : UnusedSlotTest\n"
            "  f3 : n = n\n"
            "  f4 : n + 0 = n\n"
            "\n"
            "theorem KatoUsed.helperAdm {n : Nat} (h : KatoUsed n) : n = n := h.f1.symm.trans h.f1\n"
            "\n"
            "-- 2. Prop structure with casesOn > 0 (must be eliminated from unread false-positives)\n"
            "structure DestructuredHyp : Prop where\n"
            "  p1 : Nat = Nat\n"
            "  p2 : 1 = 1\n"
            "  p3 : 2 = 2\n"
            "\n"
            "-- 3. Type* structure with partial named projections\n"
            "structure DataCarrier where\n"
            "  carrier : Type\n"
            "  [instAdd : Nat]\n"
            "  extra_unused : Nat\n"
            "  extra_unused2 : Nat\n"
            "\n"
            "-- 4. Empty 0-field Type placeholder\n"
            "structure EmptyPlaceholder (n : Nat) : Type\n"
            "\n"
            "-- 5. Fully projected Prop structure with := True default\n"
            "structure FullWithDefault : Prop where\n"
            "  ok : 1 = 1 := True\n"
            "\n"
            "-- 6. Type* structure with genuine field named `below` (must not be dropped as AUTO_AUX_NAMES)\n"
            "structure WindowLD where\n"
            "  above : Nat\n"
            "  below : Nat\n"
            "\n"
            "end Pkg\n"
        ),
    }

    for rel, content in files.items():
        full = os.path.join(src, rel)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w", encoding="utf-8") as f:
            f.write(content)

    kdb = os.path.join(td, "kernel.db")
    ck = sqlite3.connect(kdb)
    ck.executescript(
        """
        CREATE TABLE decls(
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            kind TEXT NOT NULL,
            n_consts INTEGER NOT NULL,
            type_nodes INTEGER NOT NULL,
            value_nodes INTEGER NOT NULL,
            fan_in INTEGER NOT NULL,
            fan_out INTEGER NOT NULL,
            fan_out_type INTEGER NOT NULL,
            fan_out_value INTEGER NOT NULL,
            flags INTEGER NOT NULL,
            live_mask INTEGER NOT NULL,
            stmt_mask INTEGER NOT NULL,
            defcone_mask INTEGER NOT NULL,
            attrs INTEGER NOT NULL,
            sighash TEXT,
            sighash_anon TEXT
        );
        CREATE TABLE consts(
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            decl_id INTEGER NOT NULL,
            ckind TEXT NOT NULL,
            ord INTEGER NOT NULL,
            sighash TEXT,
            sighash_anon TEXT,
            sig_size INTEGER,
            n_local INTEGER
        );
        CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src, dst)) WITHOUT ROWID;
        CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
        CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
        CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id, decl_id)) WITHOUT ROWID;
        CREATE TABLE reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, depth INTEGER NOT NULL, parent INTEGER, PRIMARY KEY(root_id, decl_id)) WITHOUT ROWID;
        CREATE UNIQUE INDEX decls_name ON decls(name);
        CREATE INDEX edges_dst ON edges(dst, src);
        """
    )

    decls = [
        # (id, name, kind, tn, vn, fi, fo, fot, fov, live, mod, meth, is_ctor)
        (0, "True", "inductive", 1, 2, 10, 0, 0, 0, 1, None, "unmatched:challenge_library", True),
        (1, "main_goal", "thm", 2, 10, 0, 5, 1, 4, 1, "Main", "leanre_db:exact", False),
        (2, "Pkg.UnusedSlotTest", "def", 1, 1, 4, 1, 0, 1, 1, "Pkg.Defs", "leanre_db:exact", False),
        (3, "Pkg.anyPred", "def", 3, 5, 2, 2, 1, 2, 1, "Pkg.Defs", "leanre_db:exact", False),
        (4, "Pkg.BaseHyp", "inductive", 4, 4, 3, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", True),
        (5, "Pkg.BaseHyp.base_ok", "thm", 3, 4, 1, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        # KatoUsed: 4 own fields (f1, f2, f3, f4); f1 + f2 projected, toBase subobj projected, helperAdm excluded!
        (10, "Pkg.KatoUsed", "inductive", 20, 20, 5, 2, 2, 0, 1, "Pkg.Defs", "leanre_db:exact", True),
        (11, "Pkg.KatoUsed.toBase", "thm", 5, 4, 2, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        (12, "Pkg.KatoUsed.f1", "thm", 5, 4, 1, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        (13, "Pkg.KatoUsed.f2", "thm", 5, 4, 1, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        (14, "Pkg.KatoUsed.helperAdm", "thm", 40, 25, 3, 2, 1, 1, 1, "Pkg.Defs", "leanre_db:exact", False),
        # DestructuredHyp: 3 own fields, 1 projected + casesOn fan_in=2 -> eliminated!
        (20, "Pkg.DestructuredHyp", "inductive", 15, 15, 3, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", True),
        (21, "Pkg.DestructuredHyp.p1", "thm", 4, 4, 1, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        (22, "Pkg.DestructuredHyp.casesOn", "def", 20, 18, 2, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        # DataCarrier: Type*, 4 own fields, 1 projected (carrier) -> 3/4 unread (75%), fan_in=30
        (30, "Pkg.DataCarrier", "inductive", 12, 12, 30, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", True),
        (31, "Pkg.DataCarrier.carrier", "def", 4, 4, 4, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        # EmptyPlaceholder: 0-field Type*, fan_in=24
        (40, "Pkg.EmptyPlaceholder", "inductive", 10, 8, 24, 0, 0, 0, 1, "Pkg.Defs", "leanre_db:exact", True),
        # FullWithDefault: 1/1 projected Prop with := True default
        (50, "Pkg.FullWithDefault", "inductive", 6, 6, 2, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", True),
        (51, "Pkg.FullWithDefault.ok", "thm", 4, 4, 1, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        # WindowLD: 2/2 projected Type* with genuine field named `below` + undeclared `noConfusion` auto-aux
        (52, "Pkg.WindowLD", "inductive", 8, 8, 3, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", True),
        (53, "Pkg.WindowLD.above", "def", 4, 4, 1, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        (54, "Pkg.WindowLD.below", "def", 4, 4, 4, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        (55, "Pkg.WindowLD.noConfusion", "def", 10, 10, 1, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        # Callers for max_caller_dom_sub differentiation
        (60, "Pkg.caller_big", "thm", 4, 10, 1, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        (61, "Pkg.caller_med", "thm", 4, 10, 1, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        (62, "Pkg.caller_small", "thm", 4, 10, 1, 1, 1, 0, 1, "Pkg.Defs", "leanre_db:exact", False),
        # Dead structure (must be ignored because live_mask=0)
        (70, "Pkg.DeadStruct", "inductive", 6, 6, 0, 0, 0, 0, 0, "Pkg.Defs", "leanre_db:exact", True),
    ]
    for did, nm, knd, tn, vn, fi, fo, fot, fov, lm, mod, meth, is_ctor in decls:
        ck.execute(
            "INSERT INTO decls VALUES (?,?,?,1,?,?,?,?,?,?,0,?,0,0,0,'','')",
            (did, nm, knd, tn, vn, fi, fo, fot, fov, lm),
        )
        if is_ctor:
            ck.execute("INSERT INTO consts VALUES (?,?,?,'induct',0,'','',1,0)", (did * 10, nm, did))
            ck.execute("INSERT INTO consts VALUES (?,?,?,'ctor',1,'','',1,0)", (did * 10 + 1, nm + ".mk", did))
        else:
            ck.execute("INSERT INTO consts VALUES (?,?,?,'thm',0,'','',1,0)", (did * 10, nm, did))
        ck.execute("INSERT INTO decl_module VALUES (?,?,?,NULL)", (did, mod, meth))

    edges = [
        (2, 0, 2),   # UnusedSlotTest -> True (value)
        (3, 0, 2),   # anyPred -> True (value)
        (10, 2, 1),  # KatoUsed -> UnusedSlotTest
        (4, 0, 1),   # BaseHyp -> True
        (60, 10, 3), # caller_big -> KatoUsed
        (60, 20, 3), # caller_big -> DestructuredHyp
        (61, 30, 3), # caller_med -> DataCarrier
        (62, 40, 2), # caller_small -> EmptyPlaceholder
    ]
    ck.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
    ck.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '1', 10)")
    dom_rows = [
        (0, 1, None, 0, 5000),
        (0, 60, 1, 1, 1000),
        (0, 61, 1, 1, 200),
        (0, 62, 1, 1, 50),
        (0, 10, 1, 1, 2),
        (0, 20, 1, 1, 1),
        (0, 30, 1, 1, 1),
        (0, 40, 1, 1, 1),
        (0, 2, 1, 1, 1),
    ]
    ck.executemany("INSERT INTO dom VALUES (?,?,?,?,?)", dom_rows)
    reach_rows = [
        (0, 10, 4, 60),
        (0, 40, 7, 62),
        (0, 2, 5, 10),
        (0, 3, 6, 10),
    ]
    ck.executemany("INSERT INTO reach VALUES (?,?,?,?)", reach_rows)
    ck.commit()
    ck.close()

    return {"src": src, "kernel_db": kdb}


class TestBundlesUnitAndSynthetic(unittest.TestCase):
    def test_helper_filtering_eliminators_placeholders_and_true_slots(self):
        with tempfile.TemporaryDirectory() as td:
            fx = _build_synthetic_bundles_fixture(td)
            out_json = os.path.join(td, "bundles_report.json")
            rep = bundles.run_bundles(
                kernel_db_path=fx["kernel_db"],
                src_root=fx["src"],
                top=35,
                sort_by="dom",
                only="all",
            )
            bundles._safe_write_json(out_json, rep)
            self.assertTrue(os.path.isfile(out_json))

            # Schema & OPSEC hygiene (no absolute paths in pins)
            self.assertEqual(rep["schema"], "leanre.bundles/1")
            self.assertEqual(rep["pins"]["source_mode"], "source+kernel")
            self.assertFalse(os.path.isabs(rep["pins"]["kernel_db"]))
            self.assertFalse(os.path.isabs(rep["pins"]["src_root"]))

            # Summary partition conservation: 7 live 1-ctor project inductives (DeadStruct excluded)
            s = rep["summary"]
            self.assertEqual(s["total_live_1ctor_project_inductives"], 7)
            pp = s["prop_partition"]
            tp = s["type_partition"]
            self.assertEqual(pp["total"], 4)  # BaseHyp, KatoUsed, DestructuredHyp, FullWithDefault
            self.assertEqual(tp["total"], 3)  # DataCarrier, EmptyPlaceholder, WindowLD
            self.assertEqual(tp["full_own"], 1)  # WindowLD (above + below both projected; noConfusion skipped)
            self.assertEqual(
                pp["zero_field"] + pp["full_own"] + pp["partial_nocases"]
                + pp["partial_cases"] + pp["zero_proj_nocases"] + pp["zero_proj_cases"],
                pp["total"],
            )
            self.assertEqual(
                tp["zero_field"] + tp["full_own"] + tp["partial_nocases"]
                + tp["partial_cases"] + tp["zero_proj_nocases"] + tp["zero_proj_cases"],
                tp["total"],
            )
            self.assertEqual(s["eliminated_cases_on_count"], 1)
            self.assertEqual(s["empty_placeholders_count"], 1)

            # Default --only all excludes DestructuredHyp (casesOn > 0) & full structures, includes KatoUsed, DataCarrier, EmptyPlaceholder
            names = [b["name"] for b in rep["bundles"]]
            self.assertNotIn("Pkg.DestructuredHyp", names)
            self.assertNotIn("Pkg.BaseHyp", names)
            self.assertEqual(names, ["Pkg.KatoUsed", "Pkg.DataCarrier", "Pkg.EmptyPlaceholder"])

            # Verify KatoUsed: 2/4 projected (f1, f2), 2/4 unread (f3, f4), helperAdm excluded, toBase subobject tracked
            kato = rep["bundles"][0]
            self.assertEqual(kato["projected_fields"], 2)
            self.assertEqual(kato["total_fields"], 4)
            self.assertEqual(kato["unread_fields"], 2)
            self.assertEqual(kato["unread_field_names"], ["f3", "f4"])
            self.assertEqual(kato["helper_subdecls_excluded"], ["helperAdm"])
            self.assertEqual(kato["subobject_projections"], ["toBase"])
            self.assertEqual(kato["max_caller_dom_sub"], 1000)
            self.assertEqual(kato["weighted_score"], 500.0)

            # Verify EmptyPlaceholder
            self.assertEqual(len(rep["placeholders"]), 1)
            ph = rep["placeholders"][0]
            self.assertEqual(ph["name"], "Pkg.EmptyPlaceholder")
            self.assertEqual(ph["total_fields"], 0)
            self.assertEqual(ph["fan_in"], 24)
            self.assertTrue(ph["is_placeholder"])

            # Verify abbrev := True / def := True slot detection & literal : True / := True fields
            slot_names = {x["name"]: x for x in rep["true_slots"]}
            self.assertIn("Pkg.UnusedSlotTest", slot_names)
            self.assertEqual(slot_names["Pkg.UnusedSlotTest"]["source_kind"], "abbrev")
            self.assertEqual(slot_names["Pkg.UnusedSlotTest"]["referenced_by_structures"], ["Pkg.KatoUsed"])
            self.assertIn("Pkg.anyPred", slot_names)
            lit_structs = {x["structure"]: x["fields"] for x in rep["literal_true_field_hits"]}
            self.assertEqual(lit_structs["Pkg.BaseHyp"], ["base_ok"])
            self.assertEqual(lit_structs["Pkg.FullWithDefault"], ["ok"])

    def test_sorting_filtering_structure_and_kernel_only(self):
        with tempfile.TemporaryDirectory() as td:
            fx = _build_synthetic_bundles_fixture(td)

            # --sort ratio puts DataCarrier (0.75) ahead of KatoUsed (0.50)
            r_ratio = bundles.run_bundles(fx["kernel_db"], fx["src"], sort_by="ratio", only="all", min_fields=1)
            self.assertEqual([b["name"] for b in r_ratio["bundles"]], ["Pkg.DataCarrier", "Pkg.KatoUsed"])

            # --sort unread puts DataCarrier (3) ahead of KatoUsed (2)
            r_unr = bundles.run_bundles(fx["kernel_db"], fx["src"], sort_by="unread", only="all", min_fields=1)
            self.assertEqual([b["name"] for b in r_unr["bundles"]], ["Pkg.DataCarrier", "Pkg.KatoUsed"])

            # --sort cone puts DataCarrier (0.75 * 30 = 22.5) ahead of KatoUsed (0.5 * 5 = 2.5)
            r_cone = bundles.run_bundles(fx["kernel_db"], fx["src"], sort_by="cone", only="all")
            self.assertEqual([b["name"] for b in r_cone["bundles"]], ["Pkg.DataCarrier", "Pkg.KatoUsed", "Pkg.EmptyPlaceholder"])

            # --only prop / type / placeholder
            self.assertEqual([b["name"] for b in bundles.run_bundles(fx["kernel_db"], fx["src"], only="prop")["bundles"]], ["Pkg.KatoUsed"])
            self.assertEqual([b["name"] for b in bundles.run_bundles(fx["kernel_db"], fx["src"], only="type")["bundles"]], ["Pkg.DataCarrier"])
            self.assertEqual([b["name"] for b in bundles.run_bundles(fx["kernel_db"], fx["src"], only="placeholder")["bundles"]], ["Pkg.EmptyPlaceholder"])

            # --top 1
            r_top = bundles.run_bundles(fx["kernel_db"], fx["src"], top=1, only="all")
            self.assertEqual(len(r_top["bundles"]), 1)
            self.assertEqual(r_top["query"]["total_matching"], 3)

            # --structure finds eliminated DestructuredHyp even though casesOn > 0
            r_elim = bundles.run_bundles(fx["kernel_db"], fx["src"], structure="DestructuredHyp")
            self.assertEqual(len(r_elim["bundles"]), 1)
            self.assertTrue(r_elim["bundles"][0]["is_eliminated"])
            self.assertEqual(r_elim["bundles"][0]["casesOn_fan_in"], 2)

            # --structure WindowLD verifies declared field `below` is preserved and `noConfusion` stays skipped
            r_ld = bundles.run_bundles(fx["kernel_db"], fx["src"], structure="WindowLD")
            self.assertEqual(len(r_ld["bundles"]), 1)
            wld = r_ld["bundles"][0]
            self.assertEqual((wld["projected_fields"], wld["total_fields"], wld["unread_fields"]), (2, 2, 0))
            self.assertEqual(wld["projected_field_names"], ["above", "below"])
            self.assertEqual(wld["helper_subdecls_excluded"], [])

            # Multi-structure targeted batch mode (comma-separated, list, and repeatable CLI flags)
            r_batch = bundles.run_bundles(
                fx["kernel_db"], fx["src"], structure="KatoUsed,DestructuredHyp,WindowLD"
            )
            self.assertTrue(r_batch["pins"]["targeted"])
            self.assertTrue(r_batch["summary"]["targeted_mode"])
            self.assertEqual(
                [b["name"] for b in r_batch["bundles"]],
                ["Pkg.KatoUsed", "Pkg.DestructuredHyp", "Pkg.WindowLD"],
            )
            self.assertEqual(r_batch["bundles"][0]["helper_subdecls_excluded"], ["helperAdm"])
            self.assertEqual(r_batch["bundles"][1]["casesOn_fan_in"], 2)
            self.assertEqual([x["name"] for x in r_batch["true_slots"]], ["Pkg.UnusedSlotTest"])

            buf_cli = io.StringIO()
            with redirect_stdout(buf_cli):
                rc_batch = leanre_cli.main([
                    "bundles",
                    "--kernel-db", fx["kernel_db"],
                    "--src-root", fx["src"],
                    "--structure", "WindowLD,KatoUsed",
                    "--structure", "EmptyPlaceholder",
                    "--json",
                ])
            self.assertEqual(rc_batch, 0)
            cli_batch_rep = json.loads(buf_cli.getvalue())
            self.assertEqual(
                [b["name"] for b in cli_batch_rep["bundles"]],
                ["Pkg.WindowLD", "Pkg.KatoUsed", "Pkg.EmptyPlaceholder"],
            )

            # Kernel-only fallback (--no-src) still identifies placeholders & vn=1 := True slot
            r_ko = bundles.run_bundles(fx["kernel_db"], src_root=None, only="placeholder")
            self.assertEqual(r_ko["pins"]["source_mode"], "kernel_only")
            self.assertEqual([b["name"] for b in r_ko["bundles"]], ["Pkg.EmptyPlaceholder"])
            self.assertEqual([x["name"] for x in r_ko["true_slots"]], ["Pkg.UnusedSlotTest"])

    def test_instantiations_producers_consumers_and_helpers_synthetic(self):
        with tempfile.TemporaryDirectory() as td:
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Inst"), exist_ok=True)
            with open(os.path.join(src, "Inst", "Core.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Inst\n\n"
                    "structure Witness (n : Nat) where\n"
                    "  val : Nat\n"
                    "  ok : val = n\n\n"
                    "theorem Witness.helperLem {n : Nat} (w : Witness n) : w.val = n := w.ok\n\n"
                    "def buildWhere (n : Nat) : Witness n where\n"
                    "  val := n\n"
                    "  ok := rfl\n\n"
                    "def buildBrace : Witness 0 := { val := 0, ok := rfl }\n\n"
                    "def buildMk (n : Nat) : Nat → Witness n := fun _ => Witness.mk n rfl\n\n"
                    "theorem witness_nonempty (n : Nat) : Nonempty (Witness n) := ⟨buildWhere n⟩\n\n"
                    "theorem exists_witness : ∃ (n : Nat) (w : Witness n), w.val = n := ⟨0, buildBrace, rfl⟩\n\n"
                    "def WitnessSpec : Prop := ∀ n : Nat, Nonempty (Witness n)\n\n"
                    "theorem witnessSpec_holds : WitnessSpec := fun n => witness_nonempty n\n\n"
                    "def tweakWitness {n : Nat} (w : Witness n) : Witness n := { val := w.val, ok := w.ok }\n\n"
                    "def deadBuilder : Witness 9 := { val := 9, ok := rfl }\n\n"
                    "theorem consumeParam {n : Nat} (w : Witness n) : Nat = Nat := rfl\n\n"
                    "theorem refuteImpossible : Nonempty (Witness 1) → False := sorry\n\n"
                    "end Inst\n"
                )

            kdb = os.path.join(td, "kernel.db")
            ck = sqlite3.connect(kdb)
            ck.executescript(
                """
                CREATE TABLE decls(
                    id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
                    n_consts INTEGER NOT NULL, type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL,
                    fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL, fan_out_type INTEGER NOT NULL,
                    fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL, live_mask INTEGER NOT NULL,
                    stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT
                );
                CREATE TABLE consts(
                    id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL,
                    ckind TEXT NOT NULL, ord INTEGER NOT NULL, sighash TEXT, sighash_anon TEXT,
                    sig_size INTEGER, n_local INTEGER
                );
                CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src, dst)) WITHOUT ROWID;
                CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
                CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
                CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id, decl_id)) WITHOUT ROWID;
                CREATE TABLE reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, depth INTEGER NOT NULL, parent INTEGER, PRIMARY KEY(root_id, decl_id)) WITHOUT ROWID;
                CREATE UNIQUE INDEX decls_name ON decls(name);
                CREATE INDEX consts_decl ON consts(decl_id);
                CREATE INDEX edges_dst ON edges(dst, src);
                """
            )
            decls_rows = [
                (1, "Exists", "inductive", 1, None, "unmatched:lib", False),
                (2, "Nonempty", "inductive", 1, None, "unmatched:lib", False),
                (10, "Inst.Witness", "inductive", 1, "Inst.Core", "leanre_db:exact", True),
                (11, "Inst.Witness.val", "def", 1, "Inst.Core", "leanre_db:exact", False),
                (12, "Inst.Witness.ok", "thm", 1, "Inst.Core", "leanre_db:exact", False),
                (13, "Inst.Witness.casesOn", "def", 1, "Inst.Core", "leanre_db:exact", False),
                (14, "Inst.Witness.noConfusion", "def", 1, "Inst.Core", "leanre_db:exact", False),
                (15, "Inst.Witness.helperLem", "thm", 1, "Inst.Core", "leanre_db:exact", False),
                (20, "Inst.buildWhere", "def", 1, "Inst.Core", "leanre_db:exact", False),
                (21, "Inst.buildBrace", "def", 1, "Inst.Core", "leanre_db:exact", False),
                (22, "Inst.buildBrace._proof_1", "thm", 1, "Inst.Core", "aux_prefix:leanre_db", False),
                (23, "Inst.buildMk", "def", 1, "Inst.Core", "leanre_db:exact", False),
                (24, "Inst.witness_nonempty", "thm", 1, "Inst.Core", "leanre_db:exact", False),
                (25, "Inst.exists_witness", "thm", 1, "Inst.Core", "leanre_db:exact", False),
                (26, "Inst.WitnessSpec", "def", 1, "Inst.Core", "leanre_db:exact", False),
                (27, "Inst.witnessSpec_holds", "thm", 1, "Inst.Core", "leanre_db:exact", False),
                (28, "Inst.tweakWitness", "def", 1, "Inst.Core", "leanre_db:exact", False),
                (29, "Inst.deadBuilder", "def", 0, "Inst.Core", "leanre_db:exact", False),
                (30, "Inst.consumeParam", "thm", 1, "Inst.Core", "leanre_db:exact", False),
                (31, "Inst.refuteImpossible", "thm", 1, "Inst.Core", "leanre_db:exact", False),
            ]
            for did, nm, knd, lm, mod, meth, is_c in decls_rows:
                ck.execute(
                    "INSERT INTO decls VALUES (?,?,?,1,5,5,5,1,1,1,0,?,0,0,0,'','')",
                    (did, nm, knd, lm),
                )
                ck.execute("INSERT INTO consts VALUES (?,?,?,'induct',0,'','',1,0)", (did * 10, nm, did))
                if is_c:
                    ck.execute("INSERT INTO consts VALUES (?,?,?,'ctor',1,'','',1,0)", (did * 10 + 1, nm + ".mk", did))
                ck.execute("INSERT INTO decl_module VALUES (?,?,?,NULL)", (did, mod, meth))

            edges_rows = [
                (11, 10, 3), (12, 10, 3), (13, 10, 3), (14, 10, 3), (15, 10, 3),
                (20, 10, 3), (21, 10, 3), (22, 10, 2), (23, 10, 3),
                (24, 10, 1), (24, 2, 1),
                (25, 10, 3), (25, 1, 3),
                (26, 10, 2), (26, 2, 2),
                (27, 10, 2), (27, 26, 1),
                (28, 10, 3),
                (29, 10, 3),
                (30, 10, 3),
                (31, 10, 1), (31, 2, 1),
            ]
            ck.executemany("INSERT INTO edges VALUES (?,?,?)", edges_rows)
            ck.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '1', 10)")
            ck.executemany(
                "INSERT INTO dom VALUES (0,?,NULL,1,?)",
                [(20, 50), (21, 40), (23, 30), (24, 90), (25, 120), (27, 110), (28, 80), (30, 300), (31, 10)],
            )
            ck.commit()
            ck.close()

            rep_live = bundles.run_instantiations(
                kernel_db_path=kdb, src_root=src, instantiations="Witness", live_only=True
            )
            self.assertEqual(rep_live["schema"], "leanre.bundles.instantiations/1")
            self.assertEqual(len(rep_live["targets"]), 1)
            t = rep_live["targets"][0]
            self.assertEqual(t["name"], "Inst.Witness")

            prod_by_name = {p["name"]: p for p in t["producers"]["sites"]}
            self.assertEqual(
                set(prod_by_name.keys()),
                {
                    "Inst.exists_witness",
                    "Inst.witnessSpec_holds",
                    "Inst.witness_nonempty",
                    "Inst.buildWhere",
                    "Inst.buildBrace",
                    "Inst.buildMk",
                    "Inst.tweakWitness",
                },
            )
            self.assertNotIn("Inst.deadBuilder", prod_by_name)
            self.assertFalse(prod_by_name["Inst.buildWhere"]["takes_self_param"])
            self.assertEqual(prod_by_name["Inst.buildWhere"]["producer_kind"], "where_ctor")
            self.assertEqual(prod_by_name["Inst.buildBrace"]["producer_kind"], "record_literal")
            self.assertEqual(prod_by_name["Inst.witnessSpec_holds"]["producer_kind"], "proves_spec(WitnessSpec)")
            self.assertTrue(prod_by_name["Inst.tweakWitness"]["takes_self_param"])
            # Root producers sort ahead of self-transforms (`tweakWitness` last)
            self.assertEqual(t["producers"]["sites"][-1]["name"], "Inst.tweakWitness")

            # Prop spec def separated cleanly
            self.assertEqual([x["name"] for x in t["producers"]["prop_spec_defs"]], ["Inst.WitnessSpec"])

            # Consumers include consumeParam and refuteImpossible (`Nonempty Witness -> False` is NOT a producer!)
            cons_names = {c["name"] for c in t["consumers"]["top_examples"]}
            self.assertEqual(cons_names, {"Inst.consumeParam", "Inst.refuteImpossible"})
            self.assertEqual(t["consumers"]["top_examples"][0]["name"], "Inst.consumeParam")

            # Projections, eliminators, namespace helpers, and compiler aux excluded into separate bucket
            ph = t["projections_and_helpers"]
            self.assertEqual(ph["field_projections"], ["ok", "val"])
            self.assertEqual(list(ph["eliminators"].keys()), ["casesOn"])
            self.assertEqual(ph["helper_subdecls"], ["helperLem"])
            self.assertEqual(ph["auto_aux_count"], 1)
            self.assertEqual(ph["compiler_aux_count"], 1)
            self.assertEqual(
                t["producers"]["total_count"]
                + t["producers"]["prop_spec_defs_count"]
                + t["consumers"]["total_count"]
                + ph["total_count"],
                t["incoming_edges"]["analyzed"],
            )

            # Without --live-only, deadBuilder appears as dead producer
            rep_all = bundles.run_instantiations(
                kernel_db_path=kdb, src_root=src, instantiations="Witness", live_only=False
            )
            all_pnames = [p["name"] for p in rep_all["targets"][0]["producers"]["sites"]]
            self.assertIn("Inst.deadBuilder", all_pnames)

            # CLI text + JSON smoke for `--instantiations`
            txt_buf = io.StringIO()
            with redirect_stdout(txt_buf):
                rc_inst = leanre_cli.main([
                    "bundles", "--kernel-db", kdb, "--src-root", src,
                    "--instantiations", "Witness", "--live-only", "--limit", "5",
                ])
            self.assertEqual(rc_inst, 0)
            self.assertIn("Inst.exists_witness", txt_buf.getvalue())

    def test_symlink_and_readonly_safety_and_cli_wiring(self):
        with tempfile.TemporaryDirectory() as td:
            fx = _build_synthetic_bundles_fixture(td)
            outside = os.path.join(td, "outside.lean")
            with open(outside, "w", encoding="utf-8") as f:
                f.write("structure Escaped : Prop where\n  bad : True\n")

            # Symlink inside src_root pointing outside src_root must be rejected by _safe_resolve_module
            escape_link = os.path.join(fx["src"], "Pkg", "Escape.lean")
            os.symlink(outside, escape_link)
            self.assertIsNone(bundles._safe_resolve_module(os.path.realpath(fx["src"]), "Pkg.Escape"))
            self.assertIsNone(bundles._safe_resolve_module(os.path.realpath(fx["src"]), "../outside"))

            # Read-only DB & read-only connection check
            ro_conn = bundles.connect_ro(fx["kernel_db"])
            try:
                with self.assertRaises(sqlite3.OperationalError):
                    ro_conn.execute("DELETE FROM decls WHERE id = 0")
            finally:
                ro_conn.close()

            # chmod 0444 DB inside chmod 0555 directory (must succeed with zero sidecar writes)
            ro_dir = os.path.join(td, "ro_db_dir")
            os.makedirs(ro_dir, exist_ok=True)
            ro_db = os.path.join(ro_dir, "kernel.db")
            with open(fx["kernel_db"], "rb") as src_f, open(ro_db, "wb") as dst_f:
                dst_f.write(src_f.read())
            os.chmod(ro_db, stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)
            os.chmod(ro_dir, stat.S_IRUSR | stat.S_IXUSR)
            try:
                rep = bundles.run_bundles(ro_db, fx["src"], only="prop")
                self.assertEqual(rep["bundles"][0]["name"], "Pkg.KatoUsed")
            finally:
                os.chmod(ro_dir, stat.S_IRWXU)
                os.chmod(ro_db, stat.S_IRUSR | stat.S_IWUSR)

            # --out symlink refusal
            sym_out = os.path.join(td, "out_symlink.json")
            target_out = os.path.join(td, "target_out.json")
            with open(target_out, "w", encoding="utf-8") as f:
                f.write("KEEP")
            os.symlink(target_out, sym_out)
            rc = leanre_cli.main([
                "bundles",
                "--kernel-db", fx["kernel_db"],
                "--src-root", fx["src"],
                "--out", sym_out,
            ])
            self.assertEqual(rc, 1)
            with open(target_out, "r", encoding="utf-8") as f:
                self.assertEqual(f.read(), "KEEP")

            # CLI wiring via leanre.py (`--json` + `--out`)
            real_out = os.path.join(td, "cli_out.json")
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc_ok = leanre_cli.main([
                    "bundles",
                    "--kernel-db", fx["kernel_db"],
                    "--src-root", fx["src"],
                    "--structure", "KatoUsed",
                    "--json",
                    "--out", real_out,
                ])
            self.assertEqual(rc_ok, 0)
            parsed_out = json.loads(buf.getvalue())
            self.assertEqual(parsed_out["bundles"][0]["projected_fields"], 2)
            self.assertTrue(os.path.isfile(real_out))

    def test_conflicting_flags_exact_and_unmatched_queries(self):
        with tempfile.TemporaryDirectory() as td:
            fx = _build_synthetic_bundles_fixture(td)

            # 1. Passing both --structure and --instantiations MUST fail with exit 2 and stderr error
            for runner in (leanre_cli.main, bundles.main):
                prefix = ["bundles"] if runner is leanre_cli.main else []
                out_buf = io.StringIO()
                err_buf = io.StringIO()
                with redirect_stdout(out_buf), redirect_stderr(err_buf):
                    rc_conflict = runner(
                        prefix
                        + [
                            "--kernel-db", fx["kernel_db"],
                            "--src-root", fx["src"],
                            "--structure", "KatoUsed",
                            "--instantiations", "KatoUsed",
                        ]
                    )
                self.assertEqual(rc_conflict, 2)
                self.assertEqual(out_buf.getvalue(), "")
                self.assertIn("--structure", err_buf.getvalue())
                self.assertIn("--instantiations", err_buf.getvalue())

            # 2. --exact matches exact FQN / exact terminal name only (no substring sweep)
            r_sub = bundles.run_bundles(fx["kernel_db"], fx["src"], structure="Kato", exact=False)
            self.assertEqual([b["name"] for b in r_sub["bundles"]], ["Pkg.KatoUsed"])
            self.assertEqual(r_sub["unmatched_queries"], [])

            r_exact_miss = bundles.run_bundles(fx["kernel_db"], fx["src"], structure="Kato", exact=True)
            self.assertEqual(r_exact_miss["bundles"], [])
            self.assertEqual(r_exact_miss["unmatched_queries"], ["Kato"])
            self.assertTrue(r_exact_miss["query"]["exact"])
            self.assertEqual(r_exact_miss["query"]["unmatched_details"][0]["reason"], "not_found")
            self.assertIn("Pkg.KatoUsed", r_exact_miss["query"]["unmatched_details"][0]["substring_suggestions"])

            r_exact_term = bundles.run_bundles(fx["kernel_db"], fx["src"], structure="KatoUsed", exact=True)
            self.assertEqual([b["name"] for b in r_exact_term["bundles"]], ["Pkg.KatoUsed"])
            r_exact_fqn = bundles.run_bundles(fx["kernel_db"], fx["src"], structure="Pkg.KatoUsed", exact=True)
            self.assertEqual([b["name"] for b in r_exact_fqn["bundles"]], ["Pkg.KatoUsed"])

            # 3. Unmatched target names reported in JSON (unmatched_queries + unmatched_details) & stderr/text warnings
            out_json = io.StringIO()
            err_json = io.StringIO()
            with redirect_stdout(out_json), redirect_stderr(err_json):
                rc_mix = leanre_cli.main([
                    "bundles",
                    "--kernel-db", fx["kernel_db"],
                    "--src-root", fx["src"],
                    "--structure", "KatoUsed,UnusedSlotTest,DeadStruct,MissingIdent",
                    "--exact",
                    "--json",
                ])
            self.assertEqual(rc_mix, 0)
            rep_mix = json.loads(out_json.getvalue())
            self.assertEqual([b["name"] for b in rep_mix["bundles"]], ["Pkg.KatoUsed"])
            self.assertEqual(rep_mix["unmatched_queries"], ["UnusedSlotTest", "DeadStruct", "MissingIdent"])
            self.assertEqual(rep_mix["query"]["unmatched_queries"], ["UnusedSlotTest", "DeadStruct", "MissingIdent"])
            det = {d["query"]: d for d in rep_mix["query"]["unmatched_details"]}
            self.assertEqual(det["UnusedSlotTest"]["reason"], "non_structure")
            self.assertEqual(det["UnusedSlotTest"]["decl_kind"], "def")
            self.assertEqual(det["UnusedSlotTest"]["matched_name"], "Pkg.UnusedSlotTest")
            self.assertEqual(det["DeadStruct"]["reason"], "dead_structure")
            self.assertEqual(det["DeadStruct"]["live_mask"], 0)
            self.assertEqual(det["MissingIdent"]["reason"], "not_found")
            self.assertIn("UnusedSlotTest", err_json.getvalue())
            self.assertIn("DeadStruct", err_json.getvalue())
            self.assertIn("MissingIdent", err_json.getvalue())

            out_txt = io.StringIO()
            err_txt = io.StringIO()
            with redirect_stdout(out_txt), redirect_stderr(err_txt):
                rc_txt = leanre_cli.main([
                    "bundles",
                    "--kernel-db", fx["kernel_db"],
                    "--src-root", fx["src"],
                    "--structure", "MissingIdent",
                    "--exact",
                ])
            self.assertEqual(rc_txt, 0)
            self.assertIn("WARNING: unmatched / non-structure targets:", out_txt.getvalue())
            self.assertIn("MissingIdent", out_txt.getvalue())
            self.assertIn("(no matching live 1-constructor project structures)", out_txt.getvalue())
            self.assertIn("warning:", err_txt.getvalue())
            self.assertIn("MissingIdent", err_txt.getvalue())

    def test_prop_def_inline_ctors_consumer_guard_exact_case_and_xrepo_anchors(self):
        """Cover BND-01, BND-02, BND-03, exact-case-first resolution, and XREPO-06 anchors/root_depth."""
        with tempfile.TemporaryDirectory() as td:
            # Generic repo root with leanre.toml (src_dir = ".") — NO "src/" anchor prefix
            repo = os.path.join(td, "generic_pkg")
            os.makedirs(os.path.join(repo, "Pkg"), exist_ok=True)
            with open(os.path.join(repo, "leanre.toml"), "w", encoding="utf-8") as f:
                f.write('[project]\nname = "generic_pkg"\nsrc_dir = "."\n')
            with open(os.path.join(repo, "lakefile.toml"), "w", encoding="utf-8") as f:
                f.write('name = "generic_pkg"\n')

            with open(os.path.join(repo, "Pkg", "Core.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Pkg\n\n"
                    "structure LitBundle : Prop where\n"
                    "  a : Nat = Nat\n"
                    "  b : 1 = 1\n"
                    "  c : 2 = 2\n\n"
                    "structure LitBundle.Sub : Prop where\n"
                    "  sub_ok : True\n\n"
                    "def ExactItem : Prop := ∀ n : Nat, n = n\n"
                    "def exactItem : Prop := True\n\n"
                    "def ConjSpec (n : Nat) : Prop := (n = n) ∧ (n + 0 = n)\n\n"
                    "theorem use_lit (L : LitBundle) : True := trivial\n\n"
                    "theorem build_via_inline : True := use_lit ⟨rfl, rfl, rfl⟩\n\n"
                    "def build_exact_anon : LitBundle := by exact ⟨rfl, rfl, rfl⟩\n\n"
                    "theorem build_refine_anon : LitBundle := by refine ⟨rfl, rfl, rfl⟩\n\n"
                    "theorem consumer_obtain_pattern (h : ∃ x y z : Nat, x = y ∧ y = z) : True := by\n"
                    "  obtain ⟨x, y, z, _⟩ := h\n"
                    "  exact trivial\n\n"
                    "theorem consumer_let_cast (L : LitBundle) : True := by\n"
                    "  let L2 : LitBundle := L\n"
                    "  exact use_lit L2\n\n"
                    "theorem consumer_subns_have : True := by\n"
                    "  have hs : LitBundle.Sub := ⟨trivial⟩\n"
                    "  exact hs.sub_ok\n\n"
                    "theorem local_witness_let : True := by\n"
                    "  let lw : LitBundle := ⟨rfl, rfl, rfl⟩\n"
                    "  exact use_lit lw\n\n"
                    "theorem exactItem_holds : ExactItem := fun _ => rfl\n\n"
                    "theorem use_exactItem (h : ExactItem) : Nat = Nat := rfl\n\n"
                    "theorem conjSpec_holds (n : Nat) : ConjSpec n := ⟨rfl, Nat.add_zero n⟩\n\n"
                    "end Pkg\n"
                )

            kdb = os.path.join(td, "kernel.db")
            ck = sqlite3.connect(kdb)
            ck.executescript(
                """
                CREATE TABLE decls(
                    id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
                    n_consts INTEGER NOT NULL, type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL,
                    fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL, fan_out_type INTEGER NOT NULL,
                    fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL, live_mask INTEGER NOT NULL,
                    stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT
                );
                CREATE TABLE consts(
                    id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL,
                    ckind TEXT NOT NULL, ord INTEGER NOT NULL, sighash TEXT, sighash_anon TEXT,
                    sig_size INTEGER, n_local INTEGER
                );
                CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src, dst)) WITHOUT ROWID;
                CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
                CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
                CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id, decl_id)) WITHOUT ROWID;
                CREATE TABLE reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, depth INTEGER NOT NULL, parent INTEGER, PRIMARY KEY(root_id, decl_id)) WITHOUT ROWID;
                CREATE UNIQUE INDEX decls_name ON decls(name);
                CREATE INDEX consts_decl ON consts(decl_id);
                CREATE INDEX edges_dst ON edges(dst, src);
                """
            )
            decls_rows = [
                (10, "Pkg.LitBundle", "inductive", 1, True),
                (11, "Pkg.LitBundle.Sub", "inductive", 1, True),
                (12, "Pkg.ExactItem", "def", 1, False),
                (13, "Pkg.exactItem", "def", 1, False),
                (14, "Pkg.ConjSpec", "def", 1, False),
                (20, "Pkg.use_lit", "thm", 1, False),
                (21, "Pkg.build_via_inline", "thm", 1, False),
                (22, "Pkg.build_exact_anon", "def", 1, False),
                (23, "Pkg.build_refine_anon", "thm", 1, False),
                (24, "Pkg.consumer_obtain_pattern", "thm", 1, False),
                (25, "Pkg.consumer_let_cast", "thm", 1, False),
                (26, "Pkg.consumer_subns_have", "thm", 1, False),
                (27, "Pkg.local_witness_let", "thm", 1, False),
                (28, "Pkg.exactItem_holds", "thm", 1, False),
                (29, "Pkg.use_exactItem", "thm", 1, False),
                (30, "Pkg.conjSpec_holds", "thm", 1, False),
            ]
            for did, nm, knd, lm, is_c in decls_rows:
                ck.execute(
                    "INSERT INTO decls VALUES (?,?,?,1,5,5,5,1,1,1,0,?,0,0,0,'','')",
                    (did, nm, knd, lm),
                )
                ck.execute("INSERT INTO consts VALUES (?,?,?,'induct',0,'','',1,0)", (did * 10, nm, did))
                if is_c:
                    ck.execute("INSERT INTO consts VALUES (?,?,?,'ctor',1,'','',1,0)", (did * 10 + 1, nm + ".mk", did))
                ck.execute("INSERT INTO decl_module VALUES (?,?,?,NULL)", (did, "Pkg.Core", "leanre_db:exact"))

            edges_rows = [
                (20, 10, 3),  # use_lit -> LitBundle (type+value)
                (21, 10, 2),  # build_via_inline -> LitBundle (value-only inline ⟨...⟩)
                (22, 10, 3),  # build_exact_anon -> LitBundle
                (23, 10, 3),  # build_refine_anon -> LitBundle
                (24, 10, 2),  # consumer_obtain_pattern -> LitBundle (pattern ⟨...⟩ must NOT match)
                (25, 10, 3),  # consumer_let_cast -> LitBundle (let cast must stay consumer_binding)
                (26, 10, 2),  # consumer_subns_have -> LitBundle (LitBundle.Sub must NOT match LitBundle)
                (26, 11, 2),  # consumer_subns_have -> LitBundle.Sub
                (27, 10, 2),  # local_witness_let -> LitBundle (local witness, NOT root)
                (28, 12, 1),  # exactItem_holds -> ExactItem
                (29, 12, 3),  # use_exactItem -> ExactItem
                (30, 14, 1),  # conjSpec_holds -> ConjSpec
            ]
            ck.executemany("INSERT INTO edges VALUES (?,?,?)", edges_rows)
            ck.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '10', 10)")
            ck.executemany(
                "INSERT INTO dom VALUES (0,?,NULL,1,?)",
                [(10, 50), (12, 40), (20, 100), (21, 90), (22, 80), (23, 70), (25, 60), (26, 55), (27, 45), (28, 35), (29, 30), (30, 25)],
            )
            ck.executemany(
                "INSERT INTO reach VALUES (0,?,?,NULL)",
                [(10, 2), (21, 3), (28, 4)],
            )
            ck.commit()
            ck.close()

            # 1. XREPO-06: generic repo has NO "src/" prefix and emits both root_depth and rh_depth
            rep_b = bundles.run_bundles(kernel_db_path=kdb, src_root=repo, structure="LitBundle")
            self.assertEqual(len(rep_b["bundles"]), 1)
            lb = rep_b["bundles"][0]
            self.assertEqual(lb["anchor"], "Pkg/Core.lean:3")
            self.assertFalse(lb["anchor"].startswith("src/"))
            self.assertEqual(lb["root_depth"], 2)
            self.assertEqual(lb["rh_depth"], 2)

            # 2. BND-02 + BND-03 on LitBundle
            rep_lit = bundles.run_instantiations(
                kernel_db_path=kdb, src_root=repo, instantiations="LitBundle", live_only=True
            )
            t_lit = rep_lit["targets"][0]
            self.assertEqual(t_lit["anchor"], "Pkg/Core.lean:3")
            prods = {p["name"]: p for p in t_lit["producers"]["sites"]}
            self.assertEqual(
                set(prods.keys()),
                {"Pkg.build_exact_anon", "Pkg.build_refine_anon", "Pkg.build_via_inline", "Pkg.local_witness_let"},
            )
            self.assertEqual(prods["Pkg.build_exact_anon"]["role"], "root")
            self.assertEqual(prods["Pkg.build_exact_anon"]["producer_kind"], "exact_anon_ctor")
            self.assertEqual(prods["Pkg.build_refine_anon"]["role"], "root")
            self.assertEqual(prods["Pkg.build_refine_anon"]["producer_kind"], "refine_anon_ctor")
            self.assertEqual(prods["Pkg.build_via_inline"]["role"], "local_witness")
            self.assertEqual(prods["Pkg.build_via_inline"]["producer_kind"], "inline_anon_ctor")
            self.assertEqual(prods["Pkg.build_via_inline"]["root_depth"], 3)
            self.assertEqual(prods["Pkg.local_witness_let"]["role"], "local_witness")
            self.assertEqual(t_lit["producers"]["root_count"], 2)
            self.assertEqual(t_lit["producers"]["local_witness_count"], 2)

            cons = {c["name"]: c for c in t_lit["consumers"]["top_examples"]}
            self.assertEqual(
                set(cons.keys()),
                {"Pkg.use_lit", "Pkg.consumer_let_cast", "Pkg.consumer_subns_have", "Pkg.consumer_obtain_pattern"},
            )
            self.assertEqual(cons["Pkg.consumer_let_cast"]["consumer_role"], "consumer_binding")
            self.assertEqual(t_lit["consumers"]["consumer_bindings_count"], 1)

            # 3. BND-01 + exact-case-first on ExactItem & ConjSpec
            rep_ex = bundles.run_instantiations(
                kernel_db_path=kdb, src_root=repo, instantiations="ExactItem", exact=True
            )
            self.assertEqual([t["name"] for t in rep_ex["targets"]], ["Pkg.ExactItem"])
            t_ex = rep_ex["targets"][0]
            self.assertTrue(t_ex["is_prop_def"])
            self.assertEqual(t_ex["producers"]["root_count"], 1)
            self.assertEqual(t_ex["producers"]["sites"][0]["name"], "Pkg.exactItem_holds")
            self.assertEqual(t_ex["consumers"]["total_count"], 1)
            self.assertEqual(t_ex["consumers"]["top_examples"][0]["name"], "Pkg.use_exactItem")

            # Case-insensitive fallback when exact-case suffix doesn't exist
            rep_ci = bundles.run_instantiations(
                kernel_db_path=kdb, src_root=repo, instantiations="EXACTITEM", exact=True
            )
            self.assertEqual({t["name"] for t in rep_ci["targets"]}, {"Pkg.ExactItem", "Pkg.exactItem"})

            # ConjSpec extracts And-conjuncts in --instantiations AND emits helpful diagnostic in --structure
            rep_conj = bundles.run_instantiations(
                kernel_db_path=kdb, src_root=repo, instantiations="ConjSpec", exact=True
            )
            t_conj = rep_conj["targets"][0]
            self.assertTrue(t_conj["is_prop_def"])
            self.assertEqual(t_conj["total_fields"], 2)
            self.assertEqual(t_conj["conjuncts"], ["n = n", "n + 0 = n"])
            self.assertEqual(t_conj["producers"]["sites"][0]["name"], "Pkg.conjSpec_holds")

            rep_struct_conj = bundles.run_bundles(
                kernel_db_path=kdb, src_root=repo, structure="ConjSpec", exact=True
            )
            self.assertEqual(rep_struct_conj["bundles"], [])
            det_c = rep_struct_conj["query"]["unmatched_details"][0]
            self.assertEqual(det_c["reason"], "non_structure")
            self.assertTrue(det_c["is_prop_def"])
            self.assertEqual(det_c["conjunct_count"], 2)
            self.assertIn("--instantiations ConjSpec", det_c["detail"])
            self.assertIn("--instantiations ConjSpec", bundles.format_bundles_text(rep_struct_conj))

    def test_nested_ctors_extends_and_cli_flag_orderings(self):
        """Cover CLI-R5B-02 (nested anon/brace ctors, extends propagation, unclassified value notice) & R6-07 CLI flag orders."""
        with tempfile.TemporaryDirectory() as td:
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Nest"), exist_ok=True)
            with open(os.path.join(src, "Nest", "Core.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Nest\n\n"
                    "structure InnerOK : Prop where\n"
                    "  a : 1 = 1\n"
                    "  b : 2 = 2\n"
                    "  c : 3 = 3\n\n"
                    "structure OuterGood : Prop where\n"
                    "  ok : InnerOK\n"
                    "  extra : True\n\n"
                    "theorem make_outer_nested : ∃ n : Nat, OuterGood := by\n"
                    "  refine ⟨0, ⟨⟨rfl, ?_, rfl⟩, trivial⟩⟩\n"
                    "  rfl\n\n"
                    "theorem forward_outer_ok (h : OuterGood) : 1 = 1 := h.ok.a\n\n"
                    "structure BaseCore where\n"
                    "  x1 : Nat\n"
                    "  x2 : Nat\n\n"
                    "structure ChildCore extends BaseCore where\n"
                    "  y1 : Nat\n\n"
                    "structure WrapCore where\n"
                    "  tag : Nat\n"
                    "  core : BaseCore\n\n"
                    "def mkChildWhere : ChildCore where\n"
                    "  x1 := 1\n"
                    "  x2 := 2\n"
                    "  y1 := 3\n\n"
                    "def updateChild (ch : ChildCore) : ChildCore := { ch with x1 := 9 }\n\n"
                    "def mkWrapBrace : WrapCore := { tag := 7, core := { x1 := 4, x2 := 5 } }\n\n"
                    "def mkWrapWhereAnon : WrapCore where\n"
                    "  tag := 8\n"
                    "  core := ⟨6, 7⟩\n\n"
                    "theorem child_only_ex : Nonempty ChildCore := ⟨mkChildWhere⟩\n\n"
                    "structure UnclassifiedVal : Prop where\n"
                    "  u1 : 1 = 1\n"
                    "  u2 : 2 = 2\n\n"
                    "theorem use_unclass (u : UnclassifiedVal) : 1 = 1 := u.u1\n\n"
                    "end Nest\n"
                )

            kdb = os.path.join(td, "kernel.db")
            ck = sqlite3.connect(kdb)
            ck.executescript(
                """
                CREATE TABLE decls(
                    id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
                    n_consts INTEGER NOT NULL, type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL,
                    fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL, fan_out_type INTEGER NOT NULL,
                    fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL, live_mask INTEGER NOT NULL,
                    stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT
                );
                CREATE TABLE consts(
                    id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL,
                    ckind TEXT NOT NULL, ord INTEGER NOT NULL, sighash TEXT, sighash_anon TEXT,
                    sig_size INTEGER, n_local INTEGER
                );
                CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src, dst)) WITHOUT ROWID;
                CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
                CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
                CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id, decl_id)) WITHOUT ROWID;
                CREATE TABLE reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, depth INTEGER NOT NULL, parent INTEGER, PRIMARY KEY(root_id, decl_id)) WITHOUT ROWID;
                CREATE UNIQUE INDEX decls_name ON decls(name);
                CREATE INDEX consts_decl ON consts(decl_id);
                CREATE INDEX edges_dst ON edges(dst, src);
                """
            )
            decls_rows = [
                (1, "Exists", "inductive", 1, None, "unmatched:lib", False),
                (2, "Nonempty", "inductive", 1, None, "unmatched:lib", False),
                (10, "Nest.InnerOK", "inductive", 1, "Nest.Core", "leanre_db:exact", True),
                (11, "Nest.OuterGood", "inductive", 1, "Nest.Core", "leanre_db:exact", True),
                (12, "Nest.OuterGood.ok", "thm", 1, "Nest.Core", "leanre_db:exact", False),
                (13, "Nest.make_outer_nested", "thm", 1, "Nest.Core", "leanre_db:exact", False),
                (14, "Nest.forward_outer_ok", "thm", 1, "Nest.Core", "leanre_db:exact", False),
                (20, "Nest.BaseCore", "inductive", 1, "Nest.Core", "leanre_db:exact", True),
                (21, "Nest.ChildCore", "inductive", 1, "Nest.Core", "leanre_db:exact", True),
                (22, "Nest.ChildCore.toBaseCore", "def", 1, "Nest.Core", "leanre_db:exact", False),
                (23, "Nest.WrapCore", "inductive", 1, "Nest.Core", "leanre_db:exact", True),
                (24, "Nest.WrapCore.core", "def", 1, "Nest.Core", "leanre_db:exact", False),
                (25, "Nest.mkChildWhere", "def", 1, "Nest.Core", "leanre_db:exact", False),
                (26, "Nest.updateChild", "def", 1, "Nest.Core", "leanre_db:exact", False),
                (27, "Nest.mkWrapBrace", "def", 1, "Nest.Core", "leanre_db:exact", False),
                (28, "Nest.mkWrapWhereAnon", "def", 1, "Nest.Core", "leanre_db:exact", False),
                (29, "Nest.child_only_ex", "thm", 1, "Nest.Core", "leanre_db:exact", False),
                (30, "Nest.UnclassifiedVal", "inductive", 1, "Nest.Core", "leanre_db:exact", True),
                (31, "Nest.use_unclass", "thm", 1, "Nest.Core", "leanre_db:exact", False),
            ]
            for did, nm, knd, lm, mod, meth, is_c in decls_rows:
                ck.execute(
                    "INSERT INTO decls VALUES (?,?,?,1,5,5,5,1,1,1,0,?,0,0,0,'','')",
                    (did, nm, knd, lm),
                )
                ck.execute("INSERT INTO consts VALUES (?,?,?,'induct',0,'','',1,0)", (did * 10, nm, did))
                if is_c:
                    ck.execute("INSERT INTO consts VALUES (?,?,?,'ctor',1,'','',1,0)", (did * 10 + 1, nm + ".mk", did))
                ck.execute("INSERT INTO decl_module VALUES (?,?,?,NULL)", (did, mod, meth))

            edges_rows = [
                (11, 10, 3), (12, 10, 1),
                (13, 10, 2), (13, 11, 3), (13, 1, 3),
                (14, 10, 2), (14, 11, 3),
                (21, 20, 3), (22, 20, 1),
                (23, 20, 3), (24, 20, 1),
                (25, 20, 2), (25, 21, 3),
                (26, 20, 2), (26, 21, 3),
                (27, 20, 2), (27, 23, 3),
                (28, 20, 2), (28, 23, 3),
                (29, 21, 1), (29, 2, 1),
                (31, 30, 2),
            ]
            ck.executemany("INSERT INTO edges VALUES (?,?,?)", edges_rows)
            ck.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '10', 10)")
            ck.executemany(
                "INSERT INTO dom VALUES (0,?,NULL,1,?)",
                [(13, 100), (14, 50), (25, 90), (26, 80), (27, 70), (28, 60), (29, 40), (31, 20)],
            )
            ck.commit()
            ck.close()

            # 1. Nested anon ctor (InnerOK inside OuterGood inside Exists)
            rep_ok = bundles.run_instantiations(
                kernel_db_path=kdb, src_root=src, instantiations="InnerOK", live_only=True, exact=True
            )
            t_ok = rep_ok["targets"][0]
            ok_prods = {p["name"]: p for p in t_ok["producers"]["sites"]}
            self.assertEqual(set(ok_prods.keys()), {"Nest.make_outer_nested"})
            self.assertEqual(ok_prods["Nest.make_outer_nested"]["producer_kind"], "nested_anon_ctor")
            self.assertEqual(ok_prods["Nest.make_outer_nested"]["role"], "root")
            self.assertIn("Nest.forward_outer_ok", {c["name"] for c in t_ok["consumers"]["top_examples"]})

            # 2. BaseCore: extends (mkChildWhere, updateChild) + nested brace/anon (mkWrapBrace, mkWrapWhereAnon) + via_extends
            rep_base = bundles.run_instantiations(
                kernel_db_path=kdb, src_root=src, instantiations="BaseCore", live_only=True, exact=True, limit=2
            )
            t_base = rep_base["targets"][0]
            # Wait: pass limit=0 to inspect all 4 direct producers
            rep_base_all = bundles.run_instantiations(
                kernel_db_path=kdb, src_root=src, instantiations="BaseCore", live_only=True, exact=True, limit=0
            )
            t_ba = rep_base_all["targets"][0]
            b_prods = {p["name"]: p for p in t_ba["producers"]["sites"]}
            self.assertEqual(
                set(b_prods.keys()),
                {"Nest.mkChildWhere", "Nest.updateChild", "Nest.mkWrapBrace", "Nest.mkWrapWhereAnon"},
            )
            self.assertEqual(b_prods["Nest.mkChildWhere"]["producer_kind"], "extends_where_ctor(ChildCore)")
            self.assertEqual(b_prods["Nest.mkChildWhere"]["role"], "root")
            self.assertEqual(b_prods["Nest.updateChild"]["producer_kind"], "extends_record_literal(ChildCore)")
            self.assertEqual(b_prods["Nest.updateChild"]["role"], "self->S")
            self.assertEqual(b_prods["Nest.mkWrapBrace"]["producer_kind"], "nested_record")
            self.assertEqual(b_prods["Nest.mkWrapBrace"]["role"], "root")
            self.assertEqual(b_prods["Nest.mkWrapWhereAnon"]["producer_kind"], "nested_anon_ctor")
            self.assertEqual(b_prods["Nest.mkWrapWhereAnon"]["role"], "root")
            # via_extends surfaces ChildCore-only producer (`child_only_ex`) regardless of `limit`
            self.assertEqual(t_base["producers"]["via_extends_count"], 1)
            self.assertEqual(t_ba["producers"]["via_extends_count"], 1)
            self.assertEqual(t_ba["producers"]["via_extends_sites"][0]["name"], "Nest.child_only_ex")
            self.assertEqual(t_ba["producers"]["via_extends_sites"][0]["via_extends_child"], "Nest.ChildCore")
            # Partition conservation holds
            self.assertEqual(
                t_ba["producers"]["total_count"]
                + t_ba["producers"]["prop_spec_defs_count"]
                + t_ba["consumers"]["total_count"]
                + t_ba["projections_and_helpers"]["total_count"],
                t_ba["incoming_edges"]["analyzed"],
            )

            # 3. Unclassified value-edge notice when producers=0 and value consumers>0
            rep_unc = bundles.run_instantiations(
                kernel_db_path=kdb, src_root=src, instantiations="UnclassifiedVal", live_only=True, exact=True
            )
            txt_unc = bundles.format_instantiations_text(rep_unc)
            self.assertIn("0 found (1 value-edge sites unclassified)", txt_unc)

            # 4. R6-07: CLI flag ordering tests (trailing flags, leading flags before target, interleaved targets)
            for argv in (
                ["bundles", "--kernel-db", kdb, "--src-root", src, "--instantiations", "InnerOK", "--live-only", "--exact", "--json"],
                ["bundles", "--kernel-db", kdb, "--src-root", src, "--instantiations", "--live-only", "--exact", "InnerOK", "--json"],
                ["bundles", "--kernel-db", kdb, "--src-root", src, "--instantiations", "InnerOK", "--live-only", "BaseCore", "--exact", "--limit", "5", "--json"],
            ):
                out_b = io.StringIO()
                with redirect_stdout(out_b):
                    rc_b = leanre_cli.main(argv)
                self.assertEqual(rc_b, 0, f"failed argv={argv}")
                parsed_b = json.loads(out_b.getvalue())
                self.assertGreaterEqual(len(parsed_b["targets"]), 1)

            for bad_argv in (
                ["bundles", "--kernel-db", kdb, "--src-root", src, "--instantiations", "--live-only"],
                ["bundles", "--kernel-db", kdb, "--src-root", src, "InnerOK"],
                ["bundles", "--kernel-db", kdb, "--src-root", src, "--instantiations", "--structure", "InnerOK"],
            ):
                err_b = io.StringIO()
                with redirect_stderr(err_b):
                    rc_bad = leanre_cli.main(bad_argv)
                self.assertEqual(rc_bad, 2, f"expected rc=2 for argv={bad_argv}")


class TestRealKernelBundlesSmoke(unittest.TestCase):
    """Verify exact pinned counts on real `outputs/kernel/kernel.db` + `data/rh_mirror/src` when present."""

    def test_real_corpus_smoke_invariants(self):
        kdb = os.path.join(_REPO_ROOT, "outputs", "kernel", "kernel.db")
        src = os.path.join(_REPO_ROOT, "data", "rh_mirror", "src")
        if not (os.path.isfile(kdb) and os.path.isdir(src)):
            self.skipTest("real kernel.db or rh_mirror/src not present")

        rep = bundles.run_bundles(kernel_db_path=kdb, src_root=src, top=35, only="prop", sort_by="dom")
        s = rep["summary"]
        self.assertEqual(s["total_live_1ctor_project_inductives"], 5497)
        self.assertEqual(s["prop_partition"]["total"], 2876)
        self.assertEqual(s["type_partition"]["total"], 2621)
        self.assertEqual(s["type_partition"]["full_own"], 2324)
        self.assertEqual(s["type_partition"]["partial_nocases"], 259)
        self.assertEqual(s["empty_placeholders_count"], 2)

        r_ld = bundles.run_bundles(
            kernel_db_path=kdb,
            src_root=src,
            structure="Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.LD",
        )
        self.assertEqual(len(r_ld["bundles"]), 1)
        ld = r_ld["bundles"][0]
        self.assertEqual((ld["projected_fields"], ld["total_fields"], ld["unread_fields"]), (17, 17, 0))
        self.assertIn("below", ld["projected_field_names"])

        by_name = {b["name"]: b for b in rep["bundles"]}
        self.assertIn("GlobalTheory.FunPr.ThetaLocalInputs", by_name)
        self.assertEqual(by_name["GlobalTheory.FunPr.ThetaLocalInputs"]["projected_fields"], 20)
        self.assertEqual(by_name["GlobalTheory.FunPr.ThetaLocalInputs"]["total_fields"], 53)
        self.assertEqual(by_name["GlobalTheory.FunPr.ThetaLocalInputs"]["unread_fields"], 33)

        self.assertIn("GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses", by_name)
        u3 = by_name["GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses"]
        self.assertEqual((u3["projected_fields"], u3["total_fields"], u3["unread_fields"]), (47, 60, 13))
        self.assertIn("geometricLemma", u3["helper_subdecls_excluded"])

        self.assertIn("UpperTheory.V.Z.Kato.Used", by_name)
        ku = by_name["UpperTheory.V.Z.Kato.Used"]
        self.assertEqual((ku["projected_fields"], ku["total_fields"], ku["unread_fields"]), (10, 22, 12))
        self.assertIn("adm", ku["helper_subdecls_excluded"])

        ph = {p["name"]: p for p in rep["placeholders"]}
        self.assertEqual(ph["Formalism.L2.LPTiedPlaceholder"]["fan_in"], 24)
        self.assertEqual(ph["GlobalTheory.HeightCounting.NTiedGPlaceholder"]["fan_in"], 13)

        slot_names = {x["name"] for x in rep["true_slots"]}
        self.assertIn("GlobalTheory.Published.UnusedSlot72", slot_names)

        # Fast targeted batch mode (`--structure LocPrime,LocAinf,LocTied,PeriodData` in < 0.8s)
        t_b0 = time.time()
        r_mon = bundles.run_bundles(
            kernel_db_path=kdb,
            src_root=src,
            structure="LocPrime,LocAinf,LocTied,PeriodData",
        )
        batch_dt = time.time() - t_b0
        self.assertLess(batch_dt, 0.8)
        mon_by_name = {b["name"]: b for b in r_mon["bundles"]}
        self.assertEqual(mon_by_name["Formalism.BasicNotions.LocPrime"]["projected_fields"], 27)
        self.assertEqual(mon_by_name["Formalism.BasicNotions.LocPrime"]["unread_fields"], 0)
        self.assertEqual(mon_by_name["Formalism.BasicNotions.LocAinf"]["projected_fields"], 19)
        self.assertEqual(mon_by_name["Formalism.BasicNotions.LocAinf"]["unread_fields"], 0)
        self.assertEqual(mon_by_name["Formalism.BasicNotions.LocTied"]["projected_fields"], 12)
        self.assertEqual(mon_by_name["Formalism.BasicNotions.LocTied"]["unread_fields"], 0)
        self.assertEqual(
            mon_by_name["Formalism.WeaklyAdmissibleFiltrations.PeriodData"]["projected_fields"], 32
        )
        self.assertEqual(
            mon_by_name["Formalism.WeaklyAdmissibleFiltrations.PeriodData"]["unread_fields"], 0
        )

        # Live --instantiations smoke: LocPrime, Formalism.BasicNotions.D7, and Kato's Tower
        inst_lp = bundles.run_instantiations(
            kernel_db_path=kdb, src_root=src, instantiations="LocPrime", live_only=True
        )
        lp_prods = {p["name"] for p in inst_lp["targets"][0]["producers"]["sites"]}
        self.assertIn("GlobalTheory.MemLoc.exists_locPrime_tied", lp_prods)
        self.assertIn("GlobalTheory.MemLoc.PrimeEx.prime", lp_prods)

        inst_d7 = bundles.run_instantiations(
            kernel_db_path=kdb,
            src_root=src,
            instantiations="Formalism.BasicNotions.D7",
            live_only=True,
            limit=25,
        )
        d7_prods = {p["name"]: p for p in inst_d7["targets"][0]["producers"]["sites"]}
        self.assertIn("Formalism.BasicNotions.Examples₂.exampleRecordOfData", d7_prods)
        self.assertFalse(
            d7_prods["Formalism.BasicNotions.Examples₂.exampleRecordOfData"]["takes_self_param"]
        )
        self.assertIn("GlobalTheory.MemLoc.record_nonempty", d7_prods)

        inst_tw = bundles.run_instantiations(
            kernel_db_path=kdb, src_root=src, instantiations="Tower", live_only=True, limit=15
        )
        self.assertEqual(inst_tw["targets"][0]["name"], "GlobalTheory.KZ.Tower")
        kz_prods = {p["name"] for p in inst_tw["targets"][0]["producers"]["sites"]}
        self.assertIn("UpperTheory.V.Z.Kato.Joint.towerEx", kz_prods)
        self.assertIn(
            "GlobalTheory.T.exists_modular_function_tower_algebraic_coefficients", kz_prods
        )

        # --exact on live corpus matches only exact terminal name `Frame` (never `FrameBound*`)
        r_frame_exact = bundles.run_bundles(
            kernel_db_path=kdb, src_root=src, structure="Frame", exact=True
        )
        self.assertGreater(len(r_frame_exact["bundles"]), 0)
        self.assertTrue(all(b["name"].endswith(".Frame") for b in r_frame_exact["bundles"]))

        # BND-01..03 live checks: OpenLiteratureStatements, Green, VWin, Host, DivX, HypsAlt
        inst_ols = bundles.run_instantiations(
            kernel_db_path=kdb, src_root=src, instantiations="OpenLiteratureStatements", live_only=True, exact=True
        )
        ols_t = inst_ols["targets"][0]
        self.assertGreaterEqual(ols_t["producers"]["total_count"], 1)
        self.assertIn(
            "UpperTheory.FinalTheorems.everyCharacter_of_row",
            {p["name"] for p in ols_t["producers"]["sites"]},
        )

        inst_green = bundles.run_instantiations(
            kernel_db_path=kdb, src_root=src, instantiations="Green", live_only=True, exact=True
        )
        self.assertEqual([t["name"] for t in inst_green["targets"]], ["GlobalTheory.GLq.Green"])
        gr_t = inst_green["targets"][0]
        self.assertTrue(gr_t["is_prop_def"])
        self.assertEqual(gr_t["total_fields"], 0)
        gr_prods = {p["name"] for p in gr_t["producers"]["sites"]}
        self.assertIn("GlobalTheory.GreenBridge.green_of_regular", gr_prods)
        self.assertNotIn("GlobalTheory.GLq.isCuspOf_label_unique", gr_prods)

        inst_vwin = bundles.run_instantiations(
            kernel_db_path=kdb, src_root=src, instantiations="VWin", live_only=True, exact=True
        )
        self.assertEqual(inst_vwin["targets"][0]["name"], "UpperTheory.Top.VWin")
        self.assertEqual(inst_vwin["targets"][0]["producers"]["root_count"], 9)

        inst_host = bundles.run_instantiations(
            kernel_db_path=kdb, src_root=src, instantiations="Host", live_only=True, exact=True
        )
        host_by_name = {t["name"]: t for t in inst_host["targets"]}
        hv_host = host_by_name["UpperTheory.V.HV.Host"]
        self.assertEqual(hv_host["producers"]["root_count"], 0)
        rec_host_prods = {p["name"] for p in host_by_name["ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host"]["producers"]["sites"]}
        self.assertNotIn("GlobalTheory.Mem.R3.Rw.EvZero.enlargedBase_reading_zero_without_evaluationProperty", rec_host_prods)
        self.assertNotIn("UpperTheory.cuspEvalProperty_indep_of_base_same_pre", rec_host_prods)

        inst_divx = bundles.run_instantiations(
            kernel_db_path=kdb, src_root=src, instantiations="DivX", live_only=True, exact=True
        )
        divx_prods = {p["name"] for p in inst_divx["targets"][0]["producers"]["sites"]}
        self.assertNotIn("GlobalTheory.Mem.R3.Rw.St.idx_zero_off_twisted", divx_prods)
        self.assertNotIn("GlobalTheory.Mem.R3.Rw.St.idx_zero_off_twisted_anyEta", divx_prods)

        # CLI-R5B-02 live checks: ChOK (nested_anon_ctor in ChGood) & FamCore (extends FamP + via_extends)
        inst_chok = bundles.run_instantiations(
            kernel_db_path=kdb, src_root=src, instantiations="GlobalTheory.EX.OB.ChOK", live_only=True, exact=True
        )
        chok_t = inst_chok["targets"][0]
        self.assertGreaterEqual(chok_t["producers"]["total_count"], 1)
        chok_prods = {p["name"]: p for p in chok_t["producers"]["sites"]}
        self.assertIn("GlobalTheory.EX.OB.chGood_of_host", chok_prods)
        self.assertEqual(chok_prods["GlobalTheory.EX.OB.chGood_of_host"]["producer_kind"], "nested_anon_ctor")
        self.assertEqual(chok_prods["GlobalTheory.EX.OB.chGood_of_host"]["role"], "root")
        chok_cons = {c["name"] for c in chok_t["consumers"]["top_examples"]}
        self.assertIn("GlobalTheory.Fc.objCP_and_of_recExP", chok_cons)
        self.assertIn("GlobalTheory.Fc.recExP_of_recAtG", chok_cons)

        inst_fam = bundles.run_instantiations(
            kernel_db_path=kdb, src_root=src, instantiations="Formalism.MainNotions.FamCore", live_only=True, exact=True, limit=5
        )
        fam_t = inst_fam["targets"][0]
        self.assertGreaterEqual(fam_t["producers"]["total_count"], 3)
        fam_prods = {p["name"]: p for p in fam_t["producers"]["sites"]}
        self.assertIn("GlobalTheory.EX.famOfKits", fam_prods)
        self.assertEqual(fam_prods["GlobalTheory.EX.famOfKits"]["role"], "root")
        self.assertIn("UpperTheory.GalC.gd", fam_prods)
        self.assertEqual(fam_prods["UpperTheory.GalC.gd"]["role"], "self->S")
        self.assertIn("Formalism.MainNotions.FamP.raise", fam_prods)
        self.assertEqual(fam_prods["Formalism.MainNotions.FamP.raise"]["role"], "self->S")
        self.assertGreaterEqual(fam_t["producers"]["via_extends_count"], 7)
        via_names = {p["name"] for p in fam_t["producers"]["via_extends_sites"]}
        self.assertIn("GlobalTheory.Top.designExists_of_tuSize_aux4n_litThin", via_names)
        self.assertIn("UpperTheory.Top.designS", via_names)


if __name__ == "__main__":
    unittest.main()
