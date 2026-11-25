#!/usr/bin/env python3
"""Unit tests for `leanre.pulse` (`leanre.pulse/1`)."""
from __future__ import annotations

import os
import sqlite3
import sys
import tempfile
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import pulse  # noqa: E402


class TestPulse(unittest.TestCase):
    def test_strip_nested_block_and_line_comments(self) -> None:
        src = (
            "-- sorry native_decide\n"
            "/- outer /- nested sorry -/ still comment\n"
            "   notation fake -/\n"
            'def s := "sorry -- not comment"\n'
            "theorem real : True := trivial\n"
        )
        code, cchars = pulse.strip_lean_comments_and_strings(src)
        self.assertGreater(cchars, 20)
        self.assertEqual(len(code.splitlines()), len(src.splitlines()))
        self.assertNotIn("sorry", code)
        self.assertNotIn("notation", code)
        self.assertIn("theorem real", code)

    def test_build_pulse_dag_restate_notations_and_kernel_contrast(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Pkg", "Sub"), exist_ok=True)
            with open(os.path.join(src, "Pkg", "Base.lean"), "w", encoding="utf-8") as fh:
                fh.write(
                    "import Mathlib\n"
                    "local notation \"foo\" => Nat\n"
                    "scoped infixl:70 \" ⬝ \" => HMul.hMul\n"
                    "theorem b_thm : 12345678 = 12345678 := by\n"
                    "  have h := rfl\n"
                    "  exact h\n"
                )
            with open(os.path.join(src, "Pkg", "Mid.lean"), "w", encoding="utf-8") as fh:
                fh.write(
                    "import Pkg.Base\n"
                    "theorem mid_restate : True := by first | exact trivial\n"
                )
            with open(os.path.join(src, "Pkg", "Sub", "Extra.lean"), "w", encoding="utf-8") as fh:
                fh.write(
                    "import Pkg.Mid\n"
                    "macro \"myMac\" : tactic => `(tactic| trivial)\n"
                    "theorem dead_one : True := by exact trivial\n"
                )
            with open(os.path.join(src, "Main.lean"), "w", encoding="utf-8") as fh:
                fh.write(
                    "import Pkg.Mid\n"
                    "import Pkg.Sub.Extra\n"
                    "theorem main_t : True := by decide +kernel\n"
                )

            kdb = os.path.join(td, "kernel.db")
            conn = sqlite3.connect(kdb)
            conn.execute("CREATE TABLE decls (id INTEGER PRIMARY KEY, live_mask INTEGER NOT NULL)")
            conn.execute("CREATE TABLE decl_module (decl_id INTEGER PRIMARY KEY, module TEXT)")
            conn.executemany(
                "INSERT INTO decls VALUES (?, ?)",
                [(1, 1), (2, 1), (3, 0), (4, 1)],
            )
            conn.executemany(
                "INSERT INTO decl_module VALUES (?, ?)",
                [(1, "Pkg.Base"), (2, "Pkg.Mid"), (3, "Pkg.Sub.Extra"), (4, "Main")],
            )
            conn.commit()
            conn.close()

            data = pulse.build_pulse(src, slug="demo", kernel_db=kdb, workers=1)
            self.assertEqual(data["schema"], pulse.PULSE_SCHEMA)
            self.assertEqual(data["summary"]["modules"], 4)
            self.assertEqual(data["summary"]["longest_chain_len"], 4)
            self.assertEqual([s["m"] for s in data["longest_chain"]], ["Pkg.Base", "Pkg.Mid", "Pkg.Sub.Extra", "Main"])
            # Notation scopes: 1 local, 1 scoped, 0 global
            self.assertEqual(data["notations"]["local"], 1)
            self.assertEqual(data["notations"]["scoped"], 1)
            self.assertEqual(data["notations"]["global"], 0)
            self.assertEqual(data["macros"]["total"], 1)
            # Restate shim detection
            kinds = {x["kind"]: x["count"] for x in data["module_kinds"]}
            self.assertEqual(kinds.get("restate"), 1)
            # Kernel live vs zero-live contrast: Pkg.Sub.Extra has 0 live decls
            self.assertTrue(data["liveness"]["has_kernel_liveness"])
            self.assertEqual(data["liveness"]["zero_live_kernel_modules"], 1)
            self.assertEqual(data["liveness"]["whole_mathlib_imports"], 1)
            # Long literal check (12345678 occurs twice)
            self.assertEqual(data["numeric_literals"]["long_7plus"], 2)
            # Top transitive dependent should be Pkg.Base with 3 dependents
            self.assertEqual(data["top_transitive_dependents"][0]["mod"], "Pkg.Base")
            self.assertEqual(data["top_transitive_dependents"][0]["dependents"], 3)
            # decide +kernel flag detected
            self.assertEqual(data["special_flags"]["decide_kernel"]["count"], 1)

            out_p = os.path.join(td, "pulse.json")
            self.assertGreater(pulse.write_pulse(data, out_p), 200)
            sym_p = os.path.join(td, "sym.json")
            os.symlink(out_p, sym_p)
            with self.assertRaises(ValueError):
                pulse.write_pulse(data, sym_p)


if __name__ == "__main__":
    unittest.main()
