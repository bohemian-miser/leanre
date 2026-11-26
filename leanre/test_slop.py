#!/usr/bin/env python3
"""Unit tests for leanre.slop (0–100 Against-the-Grain Lean Slopscore & diff)."""
import json
import os
import tempfile
import unittest

import slop


class TestSlop(unittest.TestCase):
    def test_clean_human_vs_against_grain_ai(self):
        clean_lean = b"""/-!
# Clean algebra helper
Aligns directly with Mathlib rings.
-/
import Mathlib.Algebra.Ring.Basic

/-- Standard commutativity wrapper. -/
theorem clean_comm {R : Type*} [CommRing R] (a b : R) : a * b = b * a :=
  mul_comm a b
"""
        sloppy_lean = b"""import Mathlib

set_option maxHeartbeats 16000000

abbrev UnusedSlot72 : Prop := True

structure MegaBag where
  f1 : Nat
  f2 : Nat
  f3 : Nat
  f4 : Nat
  f5 : Nat
  f6 : Nat
  f7 : Nat
  f8 : Nat
  f9 : Nat
  f10 : Nat
  f11 : Nat
  f12 : Nat

theorem opaque_thm (x : Nat) : x = x := by
  have h1 : x = x := rfl
  have h2 : x = x := rfl
  have h3 : x = x := rfl
  have h4 : x = x := rfl
  have h5 : x = x := rfl
  exact h5
"""
        restate_lean = b"""import Mathlib

theorem foo_restate (n : Nat) : n = n := by first | exact rfl
"""
        f_clean = slop.extract_file_features(clean_lean, "Clean.lean")
        s_clean = slop.score_features(f_clean)
        self.assertLessEqual(s_clean["score"], 15, f"Clean Mathlib file should pass <=15: {s_clean}")

        f_slop = slop.extract_file_features(sloppy_lean, "Sloppy.lean")
        s_slop = slop.score_features(f_slop, dup_max_mult=12, kernel_live_decls=0)
        self.assertGreaterEqual(s_slop["score"], 60, f"Brute-force file should score >=60: {s_slop}")
        self.assertLessEqual(s_slop["hygiene"], 5.0)
        self.assertTrue(any("maxHeartbeats" in r for r in s_slop["reasons"]))
        self.assertTrue(any("structure" in r for r in s_slop["reasons"]))

        f_rest = slop.extract_file_features(restate_lean, "Restate.lean", prev_zdict=restate_lean)
        s_rest = slop.score_features(f_rest)
        self.assertGreaterEqual(s_rest["fragmentation"], 16.0)
        self.assertGreaterEqual(s_rest["score"], 35)

    def test_build_report_and_diff(self):
        with tempfile.TemporaryDirectory() as td:
            d1 = os.path.join(td, "v1")
            d2 = os.path.join(td, "v2")
            os.makedirs(os.path.join(d1, "A"), exist_ok=True)
            os.makedirs(os.path.join(d2, "A"), exist_ok=True)
            with open(os.path.join(d1, "A", "Bad.lean"), "wb") as f:
                f.write(b"import Mathlib\nset_option maxHeartbeats 8000000\ntheorem t (x : Nat) : x + 0 = x := by first | exact Nat.add_zero x\n")
            with open(os.path.join(d2, "A", "Bad.lean"), "wb") as f:
                f.write(b"import Mathlib.Init.Data.Nat.Basic\n/-- Add zero. -/\ntheorem t (x : Nat) : x + 0 = x := Nat.add_zero x\n")
            r1 = slop.build_slop_report(d1, slug="before", workers=1)
            r2 = slop.build_slop_report(d2, slug="after", workers=1)
            diff = slop.diff_slop_reports(r1, r2)
            self.assertEqual(diff["schema"], slop.SLOP_DIFF_SCHEMA)
            self.assertLess(diff["deltas"]["score"], 0, f"Expected score drop: {diff}")

    def test_score_lean_bytes_fast(self):
        self.assertEqual(slop.score_lean_bytes_fast(b"", "Empty.lean"), 0)
        clean = (
            b"import Mathlib.Data.Nat.Basic\n"
            b"/-- Clean helper. -/\n"
            b"theorem ok (n : Nat) : n + 0 = n := Nat.add_zero n\n"
        )
        sloppy = (
            b"import Mathlib\n"
            b"set_option maxHeartbeats 16000000\n"
            b"attribute [local instance] foo\n"
            b"theorem bad (x : Nat) : x = x := by\n"
            b"  have h1 : x = x := rfl\n"
            b"  have h2 : x = x := rfl\n"
            b"  have h3 : x = x := rfl\n"
            b"  have h4 : x = x := rfl\n"
            b"  first | exact h4\n"
        )
        s_clean = slop.score_lean_bytes_fast(clean, "Clean.lean")
        s_sloppy = slop.score_lean_bytes_fast(sloppy, "Bad.lean")
        s_sloppy_dup = slop.score_lean_bytes_fast(sloppy, "Bad2.lean", prev_zdict=sloppy)
        self.assertIsInstance(s_clean, int)
        self.assertLessEqual(s_clean, 15)
        self.assertGreaterEqual(s_sloppy, 50)
        self.assertGreaterEqual(s_sloppy_dup, s_sloppy)
        self.assertLessEqual(s_sloppy_dup, 100)

    def test_compute_cold_gaps(self):
        fake_report = {
            "l3_targets": [
                {"dir": "Development/PillarA/ThetaKernel", "files": 40, "lines": 12000, "score": 68.5},
                {"dir": "Development/PillarB/GaloisTower", "files": 30, "lines": 9000, "score": 62.0},
                {"dir": "Development/PillarC/WindowedSha", "files": 25, "lines": 8000, "score": 58.2},
                {"dir": "Development/PillarD/ArakelovVol", "files": 20, "lines": 6000, "score": 55.1},
            ]
        }
        open_prs = [
            "refactor(Development/PillarA/ThetaKernel): collapse restates",
            "chore: simplify GaloisTower helpers",
        ]
        gaps = slop.compute_cold_gaps(fake_report, open_prs, limit=2)
        self.assertEqual(len(gaps), 2)
        self.assertEqual([g["dir"] for g in gaps], [
            "Development/PillarC/WindowedSha",
            "Development/PillarD/ArakelovVol",
        ])
        self.assertTrue(all(g["open_pr_activity"] == "cold" for g in gaps))

    def test_load_audits_dir(self):
        with tempfile.TemporaryDirectory() as td:
            # Non-existent dir is clean and empty
            empty_bundle, empty_errs = slop.load_audits_dir(os.path.join(td, "missing"))
            self.assertEqual(empty_bundle["schema"], slop.AUDITS_SCHEMA)
            self.assertEqual(empty_bundle["rounds"], [])
            self.assertEqual(empty_errs, [])

            # Valid rounds.json + contrib/*.json
            os.makedirs(os.path.join(td, "contrib"), exist_ok=True)
            with open(os.path.join(td, "rounds.json"), "w", encoding="utf-8") as f:
                json.dump({
                    "schema": slop.AUDITS_SCHEMA,
                    "rounds": [
                        {
                            "id": "r1-base",
                            "round": 1,
                            "project": "riemann-hypothesis",
                            "target": "Development/PillarA",
                            "author": "@reviewer",
                            "date": "2026-11-24",
                            "summary": "Baseline blind reconstruction audit.",
                            "static_slop": 46.3,
                            "blind_slop": 48.0,
                        }
                    ],
                }, f)
            with open(os.path.join(td, "contrib", "r2.json"), "w", encoding="utf-8") as f:
                json.dump({
                    "id": "r2-contrib",
                    "round": 2,
                    "project": "riemann-hypothesis-cleanup",
                    "target": "Development/PillarB",
                    "author": "@alice",
                    "date": "2026-11-25",
                    "summary": "Follow-up cleanup audit round.",
                    "static_slop": 31.2,
                }, f)
            bundle, errs = slop.load_audits_dir(td)
            self.assertEqual(errs, [])
            self.assertEqual(len(bundle["rounds"]), 2)
            self.assertEqual(bundle["rounds"][0]["id"], "r2-contrib")

            # Invalid contrib: duplicate id, missing field, out-of-range score
            with open(os.path.join(td, "contrib", "bad.json"), "w", encoding="utf-8") as f:
                json.dump({
                    "rounds": [
                        {"id": "r1-base", "project": "p", "target": "t", "author": "a", "date": "2026-11-25", "summary": "dup"},
                        {"id": "r3-bad", "project": "p", "target": "t", "author": "a", "date": "2026-11-25", "summary": "", "static_slop": 150},
                    ]
                }, f)
            _b2, errs2 = slop.load_audits_dir(td)
            self.assertGreaterEqual(len(errs2), 3)

    def test_build_rh_evolution_and_lib_new_boundary(self):
        with tempfile.TemporaryDirectory() as td:
            s1 = os.path.join(td, "orig")
            s2 = os.path.join(td, "grh")
            os.makedirs(os.path.join(s1, "Development"), exist_ok=True)
            os.makedirs(os.path.join(s2, "Lib", "Weil"), exist_ok=True)
            os.makedirs(os.path.join(s2, "New", "Reduction"), exist_ok=True)
            with open(os.path.join(s1, "Development", "Big.lean"), "wb") as f:
                f.write(b"import Mathlib\nset_option maxHeartbeats 8000000\ntheorem a (x : Nat) : x = x := by first | exact rfl\n")
            with open(os.path.join(s2, "Statements.lean"), "wb") as f:
                f.write(b"import Mathlib.Data.Nat.Basic\n/-- Statement. -/\ndef stmt : Prop := True\n")
            with open(os.path.join(s2, "Main.lean"), "wb") as f:
                f.write(b"import Statements\nimport New.Reduction.Main\ntheorem main_ok : stmt := trivial\n")
            with open(os.path.join(s2, "Lib", "Weil", "Basic.lean"), "wb") as f:
                f.write(b"import Mathlib.Algebra.Ring.Basic\n-- reusable library\ntheorem lib_ok (n : Nat) : n + 0 = n := Nat.add_zero n\n")
            with open(os.path.join(s2, "New", "Reduction", "Main.lean"), "wb") as f:
                f.write(b"import Lib.Weil.Basic\n-- proof chapter\ntheorem new_ok (n : Nat) : n + 0 = n := lib_ok n\n")
            evo = slop.build_rh_evolution([
                {"stage_num": 1, "slug": "orig", "label": "Orig", "src_dir": s1},
                {"stage_num": 2, "slug": "grh", "label": "GRH", "src_dir": s2, "boundary_mode": "detailed"},
            ], workers=1)
            self.assertEqual(evo["schema"], slop.EVOLUTION_SCHEMA)
            self.assertEqual(len(evo["stages"]), 2)
            self.assertGreater(evo["stages"][1]["comment_pct"], 0.0)
            self.assertLess(evo["stages"][1]["slop_score"], evo["stages"][0]["slop_score"])
            bnd = evo["grh_boundary"]
            self.assertEqual(bnd["lib"]["files"], 1)
            self.assertEqual(bnd["new"]["files"], 1)
            self.assertEqual(bnd["lib"]["new_imports"], 0)
            self.assertEqual(bnd["new"]["lib_imports"], 1)
            self.assertEqual([d["name"] for d in bnd["lib_domains"]], ["Weil"])
            self.assertEqual([c["name"] for c in bnd["new_chapters"]], ["Reduction"])


if __name__ == "__main__":
    unittest.main()
