#!/usr/bin/env python3
"""Unit tests for FLIRT Tier 1 (leanre/flirt/tier1.py).

All unit fixtures are synthetic temporary Lean trees; no real proof text is embedded.
"""
from __future__ import annotations

import json
import os
import sqlite3
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
FLIRT_DIR = os.path.join(HERE, "flirt")
if FLIRT_DIR not in sys.path:
    sys.path.insert(0, FLIRT_DIR)

import tier1  # noqa: E402


def _write(root: str, rel: str, content: str) -> None:
    p = os.path.join(root, rel)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as f:
        f.write(content)


class Tier1SyntheticTests(unittest.TestCase):
    def setUp(self):
        self.td = tempfile.TemporaryDirectory()
        self.src = os.path.join(self.td.name, "src")
        self.db = os.path.join(self.td.name, "tier1.db")
        self.summary = os.path.join(self.td.name, "tier1_summary.json")

        # 6 normal AlgebraicGeometry modules under Development/AbelianVarietyTheory/Proofs/DivisorProofs/
        for i in range(6):
            imp = (
                "import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseScheme\n"
                if i > 0 else ""
            )
            _write(
                self.src,
                f"Development/AbelianVarietyTheory/Proofs/DivisorProofs/{'BaseScheme' if i == 0 else f'DivLemma{i}'}.lean",
                f"""import Mathlib.AlgebraicGeometry.Morphisms.Basic
{imp}open AlgebraicGeometry CategoryTheory Limits
namespace Development.AbelianVarietyTheory
theorem div_scheme_ok_{i} (X : Scheme) (L : LocallyRingedSpace) : X = X := rfl
end Development.AbelianVarietyTheory
""",
            )

        # 1 planted misfile: elementary prime-table check hiding under DivisorProofs!
        _write(
            self.src,
            "Development/AbelianVarietyTheory/Proofs/DivisorProofs/PlantedPrimeTable.lean",
            """import Mathlib
open Classical
namespace Foreign.PrimeCheck
def checkPrime (p : ℕ) : Bool := true
theorem table_ok : ∀ n : ℕ, Nat.Prime n → Nat.primeCounting n ≤ n := by
  decide +kernel
theorem table_list (L : List ℕ) : L.length = L.length := rfl
end Foreign.PrimeCheck
""",
        )

        # 2 exact alpha-renamed body clones + identical sigset
        _write(
            self.src,
            "Formalism/Core/CloneA.lean",
            """import Mathlib
namespace Formalism.Core
theorem add_zero_a (a : ℕ) : a + 0 = a := by simp
end Formalism.Core
""",
        )
        _write(
            self.src,
            "Formalism/Core/CloneB.lean",
            """import Mathlib
namespace Formalism.Core
theorem add_zero_b (x : ℕ) : x + 0 = x := by simp
end Formalism.Core
""",
        )

        # 1 different proof body, SAME normalized signature (should join sigset_clone, NOT alpha_body_clone)
        _write(
            self.src,
            "Formalism/Core/SameSigDiffProof.lean",
            """import Mathlib
namespace Formalism.Core
theorem add_zero_c (z : ℕ) : z + 0 = z := by
  induction z with
  | zero => rfl
  | succ k ih => omega
end Formalism.Core
""",
        )

        # 1 import-only shim
        _write(
            self.src,
            "Formalism/Core/Shim.lean",
            "import Formalism.Core.CloneA\nimport Formalism.Core.CloneB\n",
        )

        # 2 *Statement forwarding wrappers with _root_. escape & duplicate import Mathlib
        for k in (1, 2):
            _write(
                self.src,
                f"Development/AbelianVarietyTheory/Proofs/DivisorProofs/Wrap{k}Statement.lean",
                f"""import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseScheme
import Mathlib
open Classical
theorem _root_.GlobalTheory.T.wrap_{k} : True := by
  first | exact trivial | trivial
""",
            )

    def tearDown(self):
        self.td.cleanup()

    def test_misfile_detection_and_boilerplate_collapse(self):
        summary = tier1.run_tier1(
            src_dir=self.src,
            db_path=self.db,
            summary_path=self.summary,
            threads=1,
            expect_files=13,
            kernel_db=None,
            verbose=False,
        )
        self.assertEqual(summary["file_count"], 13)
        self.assertEqual(summary["mathlib_import_stats"]["modules_with_duplicate_mathlib_import"], 2)

        # The planted prime table under DivisorProofs MUST rank #1 in extreme_outlier!
        top = summary["top_misfiles"][0]
        self.assertEqual(
            top["module"],
            "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlantedPrimeTable",
        )
        self.assertEqual(top["declared_ns"], "Foreign.PrimeCheck")
        self.assertEqual(top["flag_decl"], "Foreign.PrimeCheck.table_ok")
        self.assertGreaterEqual(top["score"], 0.90)
        self.assertEqual(top["tier"], "high")
        self.assertEqual(top["band"], "extreme_outlier")
        self.assertIn("decide_kernel", top["reason"])

        # Boilerplate collapse checks:
        # 3 alpha-body clone clusters: 6 DivLemma/BaseScheme, 2 CloneA/B, 2 Wrap1/2
        bs = summary["boilerplate_stats"]
        self.assertEqual(bs["alpha_body_clone"]["clusters"], 3)
        self.assertEqual(bs["alpha_body_clone"]["modules"], 10)
        # SameSigDiffProof shares s1t signature with CloneA and CloneB => 11 modules across 3 sigset clusters!
        self.assertEqual(bs["sigset_clone"]["clusters"], 3)
        self.assertEqual(bs["sigset_clone"]["modules"], 11)
        self.assertEqual(bs["import_shim"]["modules"], 1)
        self.assertEqual(bs["statement_wrapper"]["modules"], 2)
        # Verify CloneA + CloneB + SameSigDiffProof are grouped together in sigset_clone
        sig_clusters = summary["top_boilerplate_clusters"]["sigset_clone"]
        self.assertTrue(
            any(
                set(c["sample_members"]) == {
                    "Formalism.Core.CloneA",
                    "Formalism.Core.CloneB",
                    "Formalism.Core.SameSigDiffProof",
                }
                for c in sig_clusters
            )
        )

        # Dual counting rules in namespace_folder_matrix:
        # Wrap1Statement + Wrap2Statement declare `_root_.GlobalTheory.T.wrap_k`:
        # phase2_literal_2comp -> `_root_.GlobalTheory` (2 decls)
        # lean_scoped_2comp    -> `GlobalTheory.T` (2 decls)
        avt = summary["f1_abelian_variety_split"]
        p2_map = {x["namespace"]: x["decls"] for x in avt["phase2_literal_2comp"]["top_namespaces"]}
        ln_map = {x["namespace"]: x["decls"] for x in avt["lean_scoped_2comp"]["top_namespaces"]}
        self.assertEqual(p2_map.get("_root_.GlobalTheory"), 2)
        self.assertEqual(ln_map.get("GlobalTheory.T"), 2)
        self.assertNotIn("_root_.GlobalTheory", ln_map)

        # Verify SQLite tables & zero raw proof bodies stored
        conn = sqlite3.connect(self.db)
        try:
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM module_fingerprints").fetchone()[0], 13)
            self.assertGreaterEqual(conn.execute("SELECT COUNT(*) FROM misfiles").fetchone()[0], 1)
            self.assertGreaterEqual(conn.execute("SELECT COUNT(*) FROM boilerplate_clusters").fetchone()[0], 4)
        finally:
            conn.close()

        # Verify summary JSON contains zero proof tactic text
        with open(self.summary, encoding="utf-8") as f:
            raw_json = f.read()
        self.assertNotIn("induction z with", raw_json)
        self.assertNotIn("first | exact trivial", raw_json)

    def test_bulk_namespace_remapping_separated_from_misfiles(self):
        # 25 modules under Development.AbelianVarietyTheory all declaring GlobalTheory.Core
        # with matching AlgebraicGeometry domain -> MUST be classified as bulk_namespace_remapping,
        # NOT alertable misfiles, while 1 lone PrimeRecip island MUST still land in extreme_outlier!
        td2 = tempfile.TemporaryDirectory()
        try:
            src2 = os.path.join(td2.name, "src")
            db2 = os.path.join(td2.name, "t1.db")
            for i in range(25):
                imp = "import Development.AbelianVarietyTheory.Proofs.DivisorProofs.M0\n" if i > 0 else ""
                _write(
                    src2,
                    f"Development/AbelianVarietyTheory/Proofs/DivisorProofs/M{i}.lean",
                    f"""import Mathlib.AlgebraicGeometry.Morphisms.Basic
{imp}open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.Core
theorem scheme_lemma_{i} (X : Scheme) (L : LocallyRingedSpace) : X = X := rfl
end GlobalTheory.Core
""",
                )
            _write(
                src2,
                "Development/AbelianVarietyTheory/Proofs/DivisorProofs/LonePrime.lean",
                """import Mathlib
open Classical
namespace GlobalTheory.PrimeRecip
def chk (p : ℕ) : Bool := true
theorem table_ok (n : ℕ) (h : Nat.Prime n) : Nat.primeCounting n ≤ n := by decide +kernel
theorem chk_list (L : List ℕ) : L.length = L.length := rfl
end GlobalTheory.PrimeRecip
""",
            )
            s2 = tier1.run_tier1(src_dir=src2, db_path=db2, summary_path=None, threads=1, expect_files=26, kernel_db=None, verbose=False)
            self.assertEqual(len(s2["bulk_namespace_remappings"]), 1)
            self.assertEqual(s2["bulk_namespace_remappings"][0]["declared_top_ns"], "GlobalTheory")
            bands = s2["misfile_scoring"]["calibrated_bands"]
            self.assertEqual(bands["extreme_outlier"]["count"], 1)
            self.assertEqual(bands["bulk_namespace_remapping"]["count"], 25)
            self.assertEqual(s2["misfile_scoring"]["alertable_misfiles_total"], 1)
            self.assertEqual(s2["top_misfiles"][0]["flag_decl"], "GlobalTheory.PrimeRecip.table_ok")
        finally:
            td2.cleanup()

    def test_expect_files_mismatch_raises(self):
        with self.assertRaises(RuntimeError):
            tier1.run_tier1(
                src_dir=self.src,
                db_path=self.db,
                summary_path=None,
                threads=1,
                expect_files=999,
                kernel_db=None,
                verbose=False,
            )


if __name__ == "__main__":
    unittest.main(verbosity=2)
