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
import unittest
from contextlib import redirect_stdout

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

            # Kernel-only fallback (--no-src) still identifies placeholders & vn=1 := True slot
            r_ko = bundles.run_bundles(fx["kernel_db"], src_root=None, only="placeholder")
            self.assertEqual(r_ko["pins"]["source_mode"], "kernel_only")
            self.assertEqual([b["name"] for b in r_ko["bundles"]], ["Pkg.EmptyPlaceholder"])
            self.assertEqual([x["name"] for x in r_ko["true_slots"]], ["Pkg.UnusedSlotTest"])

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


if __name__ == "__main__":
    unittest.main()
