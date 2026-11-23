#!/usr/bin/env python3
"""Unit & integration test suite for leanre.kernel (Phase 3, gates K1-K7).

Runs fast (<5s) using synthetic NDJSON v3.1.0 exports and, when present,
verifies schema/invariant receipts on `outputs/kernel/kernel.db` and
`outputs/kernel_report.json`.
"""
from __future__ import annotations

import hashlib
import json
import os
import shutil
import sqlite3
import sys
import tempfile
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import kernel
import sighash


def _write_synthetic_export(path: str) -> None:
    """Write a small valid lean4export NDJSON v3.1.0 export with:
    - 1 inductive (`Eq`) with ctor `Eq.refl` and rec `Eq.rec`
    - 1 inductive (`Bool`) with ctors `Bool.false`, `Bool.true` and rec `Bool.rec`
    - 1 axiom (`propext`), 1 axiom (`sorryAx`, unreachable from roots!)
    - 1 def (`of_decide_eq_true`), 1 def (`TargetPred`)
    - 1 thm (`helper_decide`) whose value contains `of_decide_eq_true _ _ (Eq.refl Bool Bool.true)`
    - 1 thm (`dead_thm`) referencing `sorryAx` (dead from roots!)
    - 2 root thms (`RootA`, `RootB`) where `RootA` depends on `helper_decide` (value) and `TargetPred` (type)
    - 1 private decl (`_private.Proj.ModA.0.priv_lemma`)
    - 1 CutCptCopy-like decl (`Formalism.FourierDecayAlt.P.fooCpt`)
    """
    records = [
        {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"}, "format": {"version": "3.1.0"}, "lean": {"githash": "test", "version": "4.33.1"}}},
        # names
        {"in": 1, "str": {"pre": 0, "str": "Eq"}},
        {"in": 2, "str": {"pre": 1, "str": "refl"}},
        {"in": 3, "str": {"pre": 1, "str": "rec"}},
        {"in": 4, "str": {"pre": 0, "str": "Bool"}},
        {"in": 5, "str": {"pre": 4, "str": "false"}},
        {"in": 6, "str": {"pre": 4, "str": "true"}},
        {"in": 7, "str": {"pre": 4, "str": "rec"}},
        {"in": 8, "str": {"pre": 0, "str": "propext"}},
        {"in": 9, "str": {"pre": 0, "str": "sorryAx"}},
        {"in": 10, "str": {"pre": 0, "str": "of_decide_eq_true"}},
        {"in": 11, "str": {"pre": 0, "str": "TargetPred"}},
        {"in": 12, "str": {"pre": 0, "str": "helper_decide"}},
        {"in": 13, "str": {"pre": 0, "str": "dead_thm"}},
        {"in": 14, "str": {"pre": 0, "str": "RootA"}},
        {"in": 15, "str": {"pre": 0, "str": "RootB"}},
        {"in": 16, "str": {"pre": 0, "str": "u"}},
        {"in": 17, "str": {"pre": 0, "str": "_private"}},
        {"in": 18, "str": {"pre": 17, "str": "Proj"}},
        {"in": 19, "str": {"pre": 18, "str": "ModA"}},
        {"in": 20, "num": {"pre": 19, "i": 0}},
        {"in": 21, "str": {"pre": 20, "str": "priv_lemma"}},
        {"in": 22, "str": {"pre": 0, "str": "Formalism"}},
        {"in": 23, "str": {"pre": 22, "str": "FourierDecayAlt"}},
        {"in": 24, "str": {"pre": 23, "str": "P"}},
        {"in": 25, "str": {"pre": 24, "str": "fooCpt"}},
        # levels
        {"il": 1, "param": 16},
        {"il": 2, "succ": 0},
        # exprs
        {"ie": 0, "sort": 0},                              # Prop
        {"ie": 1, "sort": 2},                              # Type 0
        {"ie": 2, "sort": 1},                              # Sort u
        {"ie": 3, "const": {"name": 1, "us": [1]}},        # Eq.{u}
        {"ie": 4, "const": {"name": 2, "us": [2]}},        # Eq.refl.{1}
        {"ie": 5, "const": {"name": 4, "us": []}},         # Bool
        {"ie": 6, "const": {"name": 6, "us": []}},         # Bool.true
        {"ie": 7, "app": {"fn": 4, "arg": 5}},             # Eq.refl Bool
        {"ie": 8, "app": {"fn": 7, "arg": 6}},             # Eq.refl Bool Bool.true
        {"ie": 9, "const": {"name": 10, "us": []}},        # of_decide_eq_true
        {"ie": 10, "app": {"fn": 9, "arg": 0}},            # of_decide_eq_true Prop
        {"ie": 11, "app": {"fn": 10, "arg": 6}},           # of_decide_eq_true Prop true
        {"ie": 12, "app": {"fn": 11, "arg": 8}},           # of_decide_eq_true _ _ (Eq.refl Bool true)
        {"ie": 13, "const": {"name": 8, "us": []}},        # propext
        {"ie": 14, "const": {"name": 9, "us": []}},        # sorryAx
        {"ie": 15, "const": {"name": 11, "us": []}},       # TargetPred
        {"ie": 16, "const": {"name": 12, "us": []}},       # helper_decide
        {"ie": 17, "const": {"name": 21, "us": []}},       # _private.Proj.ModA.0.priv_lemma
        {"ie": 18, "const": {"name": 25, "us": []}},       # Formalism.FourierDecayAlt.P.fooCpt
        {"ie": 19, "app": {"fn": 16, "arg": 17}},          # helper_decide priv_lemma
        {"ie": 20, "app": {"fn": 19, "arg": 18}},          # helper_decide priv_lemma fooCpt
        {"ie": 21, "app": {"fn": 20, "arg": 13}},          # ... propext
        {"ie": 22, "app": {"fn": 12, "arg": 13}},          # helper_decide value using propext + of_decide_eq_true
        {"ie": 23, "forallE": {"binderInfo": "default", "name": 16, "type": 15, "body": 0}},
        # decls (topological order)
        {"inductive": {
            "types": [{"all": [1], "ctors": [2], "isRec": False, "isReflexive": False, "isUnsafe": False, "levelParams": [16], "name": 1, "numIndices": 0, "numNested": 0, "numParams": 0, "type": 2}],
            "ctors": [{"cidx": 0, "induct": 1, "isUnsafe": False, "levelParams": [16], "name": 2, "numFields": 0, "numParams": 0, "type": 3}],
            "recs": [{"all": [1], "isUnsafe": False, "k": True, "levelParams": [16], "name": 3, "numIndices": 0, "numMinors": 1, "numMotives": 1, "numParams": 0, "rules": [{"ctor": 2, "nfields": 0, "rhs": 0}], "type": 3}],
        }},
        {"inductive": {
            "types": [{"all": [4], "ctors": [5, 6], "isRec": False, "isReflexive": False, "isUnsafe": False, "levelParams": [], "name": 4, "numIndices": 0, "numNested": 0, "numParams": 0, "type": 1}],
            "ctors": [
                {"cidx": 0, "induct": 4, "isUnsafe": False, "levelParams": [], "name": 5, "numFields": 0, "numParams": 0, "type": 5},
                {"cidx": 1, "induct": 4, "isUnsafe": False, "levelParams": [], "name": 6, "numFields": 0, "numParams": 0, "type": 5},
            ],
            "recs": [{"all": [4], "isUnsafe": False, "k": False, "levelParams": [], "name": 7, "numIndices": 0, "numMinors": 2, "numMotives": 1, "numParams": 0, "rules": [], "type": 5}],
        }},
        {"axiom": {"isUnsafe": False, "levelParams": [], "name": 8, "type": 0}},
        {"axiom": {"isUnsafe": False, "levelParams": [], "name": 9, "type": 0}},
        {"def": {"all": [10], "hints": "regular", "levelParams": [], "name": 10, "safety": "safe", "type": 0, "value": 5}},
        {"def": {"all": [11], "hints": "regular", "levelParams": [], "name": 11, "safety": "safe", "type": 0, "value": 0}},
        {"thm": {"all": [12], "levelParams": [], "name": 12, "type": 0, "value": 22}},
        {"thm": {"all": [21], "levelParams": [], "name": 21, "type": 0, "value": 13}},
        {"thm": {"all": [25], "levelParams": [], "name": 25, "type": 0, "value": 13}},
        {"thm": {"all": [13], "levelParams": [], "name": 13, "type": 0, "value": 14}},
        {"thm": {"all": [14], "levelParams": [], "name": 14, "type": 23, "value": 21}},
        {"thm": {"all": [15], "levelParams": [], "name": 15, "type": 15, "value": 13}},
    ]
    with open(path, "w", encoding="utf-8") as f:
        for obj in records:
            f.write(json.dumps(obj) + "\n")


def _write_synthetic_leanre_db(path: str) -> None:
    conn = sqlite3.connect(path)
    conn.executescript(
        """
        CREATE TABLE modules(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL);
        CREATE TABLE declarations(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, module TEXT NOT NULL, line_no INTEGER NOT NULL);
        CREATE TABLE forensic_hits(id INTEGER PRIMARY KEY, tag TEXT NOT NULL, severity TEXT NOT NULL, module TEXT NOT NULL, line_no INTEGER NOT NULL, decl_name TEXT, snippet TEXT NOT NULL);
        CREATE TABLE tcb_decls(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL);
        """
    )
    conn.executemany("INSERT INTO modules(id, name) VALUES (?, ?)", [
        (1, "Main"),
        (2, "Proj.ModA"),
        (3, kernel.CUT_CPT_COPY_MODULE),
    ])
    conn.executemany("INSERT INTO declarations(id, name, kind, module, line_no) VALUES (?,?,?,?,?)", [
        (1, "RootA", "theorem", "Main", 1),
        (2, "_root_.RootB", "theorem", "Main", 2),
        (3, "TargetPred", "def", "Proj.ModA", 5),
        (4, "helper_decide", "theorem", "Proj.ModA", 10),
        (5, "Formalism.FourierDecayAlt.P.foo", "theorem", "Proj.ModA", 20),
    ])
    conn.executemany("INSERT INTO forensic_hits(id, tag, severity, module, line_no, decl_name, snippet) VALUES (?,?,?,?,?,?,?)", [
        (1, "kexactB", "audit", "Proj.ModA", 10, "helper_decide", "kexactB"),
        (2, "decide_kernel", "interesting", "Proj.ModA", 10, "helper_decide", "decide +kernel"),
    ])
    conn.executemany("INSERT INTO tcb_decls(id, name) VALUES (?, ?)", [
        (1, "Eq"),
        (2, "Bool"),
        (3, "propext"),
    ])
    conn.commit()
    conn.close()


class TestKernelPipelineSynthetic(unittest.TestCase):
    def test_end_to_end_extract_sighash_taint_align_and_determinism(self):
        if not os.path.exists(kernel.default_binary_path()):
            self.skipTest("leanre-kernel release binary not built")
        with tempfile.TemporaryDirectory() as td:
            nd = os.path.join(td, "syn.ndjson")
            ldb = os.path.join(td, "leanre.db")
            lex_path = os.path.join(td, "lex.txt")
            _write_synthetic_export(nd)
            _write_synthetic_leanre_db(ldb)
            lex = sighash.Lexicon(["TargetPred", "helper_decide"])
            lex.save(lex_path)

            out1 = os.path.join(td, "run1")
            out2 = os.path.join(td, "run2")
            rep1 = os.path.join(td, "rep1.json")
            rep2 = os.path.join(td, "rep2.json")

            r1 = kernel.run_pipeline(
                input_path=nd,
                out_dir=out1,
                leanre_db=ldb,
                lexicon=lex_path,
                report_path=rep1,
                threads=2,
                workers=1,
                oracle_random=20,
                oracle_top=5,
                roots=["RootA:G1", "RootB:G2"],
                auto_build=False,
                verbose=False,
            )
            r2 = kernel.run_pipeline(
                input_path=nd,
                out_dir=out2,
                leanre_db=ldb,
                lexicon=lex_path,
                report_path=rep2,
                threads=2,
                workers=1,
                oracle_random=20,
                oracle_top=5,
                roots=["RootA:G1", "RootB:G2"],
                auto_build=False,
                verbose=False,
            )

            # K2 counts: 12 records, 17 constants (Eq+refl+rec=3, Bool+false+true+rec=4, +10 plain = 17)
            self.assertEqual(r1["k2_counts"]["measured_records"], 12)
            self.assertEqual(r1["k2_counts"]["measured_constants_unpacked"], 17)
            self.assertTrue(r1["k2_counts"]["reconciliation"]["formula_check"])

            # K4 live/dead & axioms: dead_thm and sorryAx are unreachable from {RootA, RootB}
            self.assertEqual(r1["k4_live_dead_and_axioms"]["union"]["live"], 10)
            self.assertEqual(r1["k4_live_dead_and_axioms"]["union"]["dead"], 2)
            self.assertEqual(
                set(r1["k4_live_dead_and_axioms"]["union"]["dead_names_first200"]),
                {"dead_thm", "sorryAx"},
            )
            self.assertEqual(r1["k4_live_dead_and_axioms"]["special"]["sorryAx"]["live_mask"], 0)

            # K5 dominators oracle + taint validation
            self.assertEqual(r1["k5_dominators_and_taint"]["dominator_oracle_failures_total"], 0)
            taint = r1["k5_dominators_and_taint"]["taint_summary"]
            self.assertEqual(taint["validation"]["failures"], 0)
            self.assertGreater(taint["validation"]["paths_validated"], 0)
            self.assertGreater(taint["by_class"]["kexactB"]["paths"], 0)
            self.assertGreater(taint["by_class"]["decide_kernel_pattern"]["paths"], 0)
            self.assertGreater(taint["by_class"]["CutCptCopy"]["paths"], 0)
            # sorryAx is dead -> 0 live taint paths
            self.assertEqual(taint["by_class"]["sorryAx"]["paths"], 0)

            # K6 alignment: exact, strip_root, private_module, CutCptCopy, explicit unmatched
            align = r1["k6_module_alignment"]
            self.assertEqual(align["total_decls"], 12)
            self.assertEqual(align["matched_all"] + align["unmatched_all"], 12)
            bm = align["by_method"]
            self.assertEqual(bm.get("leanre_db:exact"), 3)       # RootA, TargetPred, helper_decide
            self.assertEqual(bm.get("leanre_db:strip_root"), 1)  # RootB
            self.assertEqual(bm.get("private_module"), 1)        # _private.Proj.ModA.0.priv_lemma
            self.assertEqual(bm.get("generated:CutCptCopy"), 1)  # Formalism.FourierDecayAlt.P.fooCpt
            self.assertEqual(bm.get("unmatched:challenge_library"), 3)  # Eq, Bool, propext

            # SIGHASH parity with reference Python sighash.py
            ref_rows = list(sighash.kernel_sighashes(nd, lexicon=lex))
            conn = sqlite3.connect(f"file:{os.path.join(out1, 'kernel.db')}?mode=ro", uri=True)
            try:
                got_rows = conn.execute(
                    "SELECT name, ckind, sighash, sighash_anon, sig_size, n_local FROM consts ORDER BY id"
                ).fetchall()
                self.assertEqual(len(got_rows), len(ref_rows))
                for g, ref in zip(got_rows, ref_rows):
                    self.assertEqual(g[0], ref["name"])
                    self.assertEqual("ind" if g[1] == "induct" else g[1], ref["role"])
                    self.assertEqual(g[2], sighash.fmt("k1n", ref["k1n"]))
                    self.assertEqual(g[3], sighash.fmt("k1a", ref["k1a"]))
                    self.assertEqual(g[4], ref["sig_size"])
                    self.assertEqual(g[5], ref["n_local"])

                # Validate taint path tamper detection: corrupt a copy and verify validator catches it
                bad_db = os.path.join(td, "bad.db")
                with open(os.path.join(out1, "kernel.db"), "rb") as f_in, open(bad_db, "wb") as f_out:
                    f_out.write(f_in.read())
                bconn = sqlite3.connect(bad_db)
                try:
                    bconn.execute("UPDATE taint_paths SET edge_kind = 99 WHERE hop = 1")
                    bconn.commit()
                    vres = kernel.validate_taint_paths(bconn)
                    self.assertGreater(vres["failures"], 0)
                finally:
                    bconn.close()
            finally:
                conn.close()

            # K7 determinism: content hashes identical across two runs
            self.assertEqual(
                r1["k7_performance_and_determinism"]["content_hashes"],
                r2["k7_performance_and_determinism"]["content_hashes"],
            )

    def test_k6_source_rescan_blocks_phase2_anonymous_end_collisions(self):
        """Regression for K6 defect: bogus Phase 2 root names (from anonymous `end` popping
        a namespace) must NOT falsely align core/Mathlib constants when `--src-dir` is given.
        """
        if not os.path.exists(kernel.default_binary_path()):
            self.skipTest("leanre-kernel release binary not built")
        with tempfile.TemporaryDirectory() as td:
            nd = os.path.join(td, "syn.ndjson")
            ldb = os.path.join(td, "leanre.db")
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Proj"), exist_ok=True)
            _write_synthetic_export(nd)
            _write_synthetic_leanre_db(ldb)
            # Plant a bogus Phase 2 root declaration `Eq` in `Proj.ModA` (as if anonymous `end` popped namespace)
            conn = sqlite3.connect(ldb)
            conn.execute(
                "INSERT INTO declarations(id, name, kind, module, line_no) VALUES (99, 'Eq', 'structure', 'Proj.ModA', 30)"
            )
            conn.commit()
            conn.close()
            # Real Lean source files have `Eq` strictly inside `namespace ProjNs` after a `section ... end`
            with open(os.path.join(src, "Main.lean"), "w", encoding="utf-8") as f:
                f.write("theorem RootA : Prop := True\ntheorem _root_.RootB : Prop := True\n")
            with open(os.path.join(src, "Proj", "ModA.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "def TargetPred : Prop := True\n"
                    "theorem helper_decide : Prop := True\n"
                    "theorem Formalism.FourierDecayAlt.P.foo : Prop := True\n"
                    "namespace ProjNs\n"
                    "section\n"
                    "end\n"
                    "structure Eq where\n"
                    "end ProjNs\n"
                )
            out = os.path.join(td, "out")
            rep = kernel.run_pipeline(
                input_path=nd,
                out_dir=out,
                leanre_db=ldb,
                src_dir=src,
                threads=2,
                workers=1,
                oracle_random=10,
                oracle_top=5,
                roots=["RootA:G1", "RootB:G2"],
                auto_build=False,
                verbose=False,
            )
            align = rep["k6_module_alignment"]
            self.assertGreaterEqual(align["phase2_bogus_collisions_avoided"], 1)
            kconn = sqlite3.connect(f"file:{os.path.join(out, 'kernel.db')}?mode=ro", uri=True)
            try:
                row = kconn.execute(
                    "SELECT m.module, m.method FROM decls d JOIN decl_module m ON m.decl_id = d.id WHERE d.name = 'Eq'"
                ).fetchone()
                self.assertIsNone(row[0])
                self.assertEqual(row[1], "unmatched:challenge_library")
            finally:
                kconn.close()


    def test_slice_type_deps_and_lean4lean_aux_taint(self):
        """Unit test for Phase 4 D4: `slice_decl`, `inspect_type_deps`, DOT/JSON export,
        SQLi-safe lookup error, and `lean4lean_timeout` `._proof_1_1` auxiliary attribution.
        """
        if not os.path.exists(kernel.default_binary_path()):
            self.skipTest("leanre-kernel release binary not built")
        with tempfile.TemporaryDirectory() as td:
            nd = os.path.join(td, "syn_d4.ndjson")
            ldb = os.path.join(td, "leanre_d4.db")
            # Build a small export with `loop_run._proof_1_1` (refl_true) -> `loop_run` -> `RootA`
            records = [
                {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"}, "format": {"version": "3.1.0"}, "lean": {"githash": "test", "version": "4.33.1"}}},
                {"in": 1, "str": {"pre": 0, "str": "Eq"}},
                {"in": 2, "str": {"pre": 1, "str": "refl"}},
                {"in": 3, "str": {"pre": 1, "str": "rec"}},
                {"in": 4, "str": {"pre": 0, "str": "Bool"}},
                {"in": 5, "str": {"pre": 4, "str": "false"}},
                {"in": 6, "str": {"pre": 4, "str": "true"}},
                {"in": 7, "str": {"pre": 4, "str": "rec"}},
                {"in": 8, "str": {"pre": 0, "str": "PI"}},
                {"in": 9, "str": {"pre": 8, "str": "loop_run"}},
                {"in": 10, "str": {"pre": 9, "str": "_proof_1_1"}},
                {"in": 11, "str": {"pre": 0, "str": "RootA"}},
                {"in": 12, "str": {"pre": 0, "str": "u"}},
                {"il": 1, "param": 12},
                {"il": 2, "succ": 0},
                {"ie": 0, "sort": 0},
                {"ie": 1, "sort": 2},
                {"ie": 2, "sort": 1},
                {"ie": 3, "const": {"name": 1, "us": [1]}},
                {"ie": 4, "const": {"name": 2, "us": [2]}},
                {"ie": 5, "const": {"name": 4, "us": []}},
                {"ie": 6, "const": {"name": 6, "us": []}},
                {"ie": 7, "app": {"fn": 4, "arg": 5}},
                {"ie": 8, "app": {"fn": 7, "arg": 6}},  # Eq.refl Bool Bool.true (F_REFL_TRUE)
                {"ie": 9, "const": {"name": 10, "us": []}},  # PI.loop_run._proof_1_1
                {"ie": 10, "const": {"name": 9, "us": []}},  # PI.loop_run
                {"ie": 11, "forallE": {"binderInfo": "default", "name": 12, "type": 5, "body": 0}},
                {"inductive": {
                    "types": [{"all": [1], "ctors": [2], "isRec": False, "isReflexive": False, "isUnsafe": False, "levelParams": [12], "name": 1, "numIndices": 0, "numNested": 0, "numParams": 0, "type": 2}],
                    "ctors": [{"cidx": 0, "induct": 1, "isUnsafe": False, "levelParams": [12], "name": 2, "numFields": 0, "numParams": 0, "type": 3}],
                    "recs": [{"all": [1], "isUnsafe": False, "k": True, "levelParams": [12], "name": 3, "numIndices": 0, "numMinors": 1, "numMotives": 1, "numParams": 0, "rules": [{"ctor": 2, "nfields": 0, "rhs": 0}], "type": 3}],
                }},
                {"inductive": {
                    "types": [{"all": [4], "ctors": [5, 6], "isRec": False, "isReflexive": False, "isUnsafe": False, "levelParams": [], "name": 4, "numIndices": 0, "numNested": 0, "numParams": 0, "type": 1}],
                    "ctors": [
                        {"cidx": 0, "induct": 4, "isUnsafe": False, "levelParams": [], "name": 5, "numFields": 0, "numParams": 0, "type": 5},
                        {"cidx": 1, "induct": 4, "isUnsafe": False, "levelParams": [], "name": 6, "numFields": 0, "numParams": 0, "type": 5},
                    ],
                    "recs": [{"all": [4], "isUnsafe": False, "k": False, "levelParams": [], "name": 7, "numIndices": 0, "numMinors": 2, "numMotives": 1, "numParams": 0, "rules": [], "type": 5}],
                }},
                {"thm": {"all": [10], "levelParams": [], "name": 10, "type": 11, "value": 8}},
                {"thm": {"all": [9], "levelParams": [], "name": 9, "type": 11, "value": 9}},
                {"thm": {"all": [11], "levelParams": [], "name": 11, "type": 0, "value": 10}},
            ]
            with open(nd, "w", encoding="utf-8") as f:
                for obj in records:
                    f.write(json.dumps(obj) + "\n")

            conn = sqlite3.connect(ldb)
            conn.executescript(
                """
                CREATE TABLE modules(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL);
                CREATE TABLE module_edges(src TEXT NOT NULL, dst TEXT NOT NULL, PRIMARY KEY(src, dst));
                CREATE TABLE declarations(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, module TEXT NOT NULL, line_no INTEGER NOT NULL);
                CREATE TABLE forensic_hits(id INTEGER PRIMARY KEY, tag TEXT NOT NULL, severity TEXT NOT NULL, module TEXT NOT NULL, line_no INTEGER NOT NULL, decl_name TEXT, snippet TEXT NOT NULL);
                CREATE TABLE tcb_decls(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL);
                """
            )
            conn.executemany("INSERT INTO modules(id, name) VALUES (?, ?)", [
                (1, "Main"), (2, "SmallLoop"), (3, "DeadRun1"),
            ])
            conn.execute("INSERT INTO module_edges(src, dst) VALUES ('Main', 'DeadRun1')")
            conn.executemany("INSERT INTO declarations(id, name, kind, module, line_no) VALUES (?,?,?,?,?)", [
                (1, "RootA", "theorem", "Main", 1),
                (2, "PI.loop_run", "theorem", "SmallLoop", 10),
                (3, "PI.dead_run1", "theorem", "DeadRun1", 5),
            ])
            conn.executemany("INSERT INTO forensic_hits(id, tag, severity, module, line_no, decl_name, snippet) VALUES (?,?,?,?,?,?,?)", [
                (1, "lean4lean_timeout", "interesting", "SmallLoop", 10, "PI.loop_run", "timeout"),
                (2, "lean4lean_timeout", "interesting", "DeadRun1", 5, "PI.dead_run1", "timeout"),
            ])
            conn.executemany("INSERT INTO tcb_decls(id, name) VALUES (?, ?)", [(1, "Eq"), (2, "Bool")])
            conn.commit()
            conn.close()

            out = os.path.join(td, "out")
            rep = kernel.run_pipeline(
                input_path=nd,
                out_dir=out,
                leanre_db=ldb,
                threads=2,
                workers=1,
                oracle_random=10,
                oracle_top=5,
                roots=["RootA:G1"],
                auto_build=False,
                verbose=False,
            )
            kdb = os.path.join(out, "kernel.db")

            # Verify lean4lean_timeout attributed BOTH outer theorem AND ._proof_1_1 auxiliary
            audit = rep["k5_dominators_and_taint"]["lean4lean_timeout_audit"]
            self.assertEqual(audit["total_timeout_modules"], 2)
            self.assertEqual(audit["live_timeout_modules"], 1)
            self.assertEqual(audit["dead_timeout_modules"], 1)
            self.assertEqual(audit["live_decls_across_timeout_modules"], 2)
            by_mod = {m["module"]: m for m in audit["modules"]}
            self.assertTrue(by_mod["SmallLoop"]["timeout_aux_proof_in_kernel"])
            self.assertEqual(by_mod["SmallLoop"]["timeout_aux_proof_flags"], kernel.F_REFL_TRUE)
            self.assertFalse(by_mod["DeadRun1"]["source_decl_in_kernel"])
            self.assertEqual(len(by_mod["DeadRun1"]["import_chain_to_first_live_module"]), 2)

            kconn = sqlite3.connect(f"file:{kdb}?mode=ro", uri=True)
            try:
                ts_names = {
                    r[0]
                    for r in kconn.execute(
                        "SELECT d.name FROM taint_sources s JOIN decls d ON d.id = s.decl_id WHERE s.class = 'lean4lean_timeout'"
                    )
                }
                self.assertEqual(ts_names, {"PI.loop_run", "PI.loop_run._proof_1_1"})
            finally:
                kconn.close()

            # Slice tests: backward, forward, both, edge-kind filters, stop-at, depth, max-nodes, DOT
            sl_back = kernel.slice_decl(kdb, "PI.loop_run", direction="backward", depth=2, edge_kind="both")
            self.assertEqual(sl_back["schema"], "leanre.kernel.slice/1")
            self.assertEqual({n["name"] for n in sl_back["nodes"]}, {"PI.loop_run", "PI.loop_run._proof_1_1", "Bool", "Eq"})
            self.assertFalse(sl_back["truncated"])

            sl_type = kernel.slice_decl(kdb, "PI.loop_run", direction="backward", depth=2, edge_kind="type")
            self.assertEqual({n["name"] for n in sl_type["nodes"]}, {"PI.loop_run", "Bool"})

            sl_val = kernel.slice_decl(kdb, "PI.loop_run", direction="backward", depth=1, edge_kind="value-only")
            self.assertEqual({n["name"] for n in sl_val["nodes"]}, {"PI.loop_run", "PI.loop_run._proof_1_1"})

            sl_fwd = kernel.slice_decl(kdb, "PI.loop_run._proof_1_1", direction="forward", depth=2, edge_kind="both")
            self.assertEqual({n["name"] for n in sl_fwd["nodes"]}, {"PI.loop_run._proof_1_1", "PI.loop_run", "RootA"})

            sl_stop = kernel.slice_decl(kdb, "RootA", direction="backward", depth=5, stop_at=["PI"])
            stop_map = {n["name"]: n["stopped"] for n in sl_stop["nodes"]}
            self.assertEqual(stop_map, {"RootA": False, "PI.loop_run": True})

            sl_cap = kernel.slice_decl(kdb, "RootA", direction="backward", depth=5, max_nodes=2)
            self.assertEqual(sl_cap["node_count"], 2)
            self.assertTrue(sl_cap["truncated"])

            # Constructor fallback resolution (`Eq.refl` -> `Eq`)
            sl_ctor = kernel.slice_decl(kdb, "Eq.refl", direction="forward", depth=1)
            self.assertEqual(sl_ctor["center"]["name"], "Eq")
            self.assertEqual(sl_ctor["center"]["resolved_from_const"], "Eq.refl")

            dot = kernel.format_slice_dot(sl_back)
            self.assertIn("digraph kernel_slice {", dot)
            self.assertIn("\\n[thm hop=0", dot)
            self.assertNotIn("\\\\n", dot)
            txt = kernel.format_slice_text(sl_back)
            self.assertIn("PI.loop_run", txt)

            # inspect_type_deps test
            td_info = kernel.inspect_type_deps(kdb, "PI.loop_run")
            self.assertEqual(td_info["schema"], "leanre.kernel.type_deps/1")
            self.assertEqual([x["name"] for x in td_info["type_deps"]], ["Bool"])
            self.assertEqual([x["name"] for x in td_info["value_only_deps"]], ["PI.loop_run._proof_1_1"])
            self.assertEqual([x["name"] for x in td_info["dependents"]], ["RootA"])
            self.assertTrue(td_info["dominators"]["found"])
            self.assertEqual(td_info["dominators"]["idom"], "RootA")
            self.assertEqual(len(td_info["paths_to_roots"]), 1)
            self.assertEqual([h["name"] for h in td_info["paths_to_roots"][0]["path"]], ["RootA", "PI.loop_run"])
            self.assertIn("PI.loop_run", kernel.format_type_deps_text(td_info))

            # Unknown & SQLi-like decl name cleanly raises LookupError / CLI rc=1
            with self.assertRaises(LookupError):
                kernel.slice_decl(kdb, "'; DROP TABLE decls; --")
            self.assertEqual(kernel.main(["slice", "nonexistent_decl", "--kernel-db", kdb]), 1)
            self.assertEqual(kernel.main(["type-deps", "nonexistent_decl", "--kernel-db", kdb]), 1)
            self.assertEqual(kernel.main(["slice", "PI.loop_run", "--kernel-db", kdb, "--json", "--out", os.path.join(td, "sl.json")]), 0)
            self.assertEqual(kernel.main(["type-deps", "PI.loop_run", "--kernel-db", kdb, "--json", "--out", os.path.join(td, "td.json")]), 0)

    def test_taint_anonymous_example_and_bare_decl_resolution(self):
        """Regression for anonymous `example ... := by decide +kernel` attribution bug:
        - An anonymous `example` line must NEVER be attributed to a preceding theorem/def;
          it is recorded explicitly in `taint_sources` with `decl_id IS NULL`.
        - A bare decl name in `forensic_hits` inside a namespaced lemma resolves via
          enclosing source span + captures `._proof_1_2` auxiliaries.
        """
        if not os.path.exists(kernel.default_binary_path()):
            self.skipTest("leanre-kernel release binary not built")
        with tempfile.TemporaryDirectory() as td:
            nd = os.path.join(td, "syn_ex.ndjson")
            ldb = os.path.join(td, "leanre_ex.db")
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Proj"), exist_ok=True)

            # Export: Eq, Bool, Proj.Ns.sign_thm, Proj.Ns.discr_thm, Proj.Ns.discr_thm._proof_1_2, RootA
            records = [
                {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"}, "format": {"version": "3.1.0"}, "lean": {"githash": "test", "version": "4.33.1"}}},
                {"in": 1, "str": {"pre": 0, "str": "Eq"}},
                {"in": 2, "str": {"pre": 1, "str": "refl"}},
                {"in": 3, "str": {"pre": 1, "str": "rec"}},
                {"in": 4, "str": {"pre": 0, "str": "Bool"}},
                {"in": 5, "str": {"pre": 4, "str": "false"}},
                {"in": 6, "str": {"pre": 4, "str": "true"}},
                {"in": 7, "str": {"pre": 4, "str": "rec"}},
                {"in": 8, "str": {"pre": 0, "str": "Proj"}},
                {"in": 9, "str": {"pre": 8, "str": "Ns"}},
                {"in": 10, "str": {"pre": 9, "str": "sign_thm"}},
                {"in": 11, "str": {"pre": 9, "str": "discr_thm"}},
                {"in": 12, "str": {"pre": 11, "str": "_proof_1_2"}},
                {"in": 13, "str": {"pre": 0, "str": "RootA"}},
                {"in": 14, "str": {"pre": 0, "str": "u"}},
                {"il": 1, "param": 14},
                {"il": 2, "succ": 0},
                {"ie": 0, "sort": 0},
                {"ie": 1, "sort": 2},
                {"ie": 2, "sort": 1},
                {"ie": 3, "const": {"name": 1, "us": [1]}},
                {"ie": 4, "const": {"name": 2, "us": [2]}},
                {"ie": 5, "const": {"name": 4, "us": []}},
                {"ie": 6, "const": {"name": 6, "us": []}},
                {"ie": 7, "app": {"fn": 4, "arg": 5}},
                {"ie": 8, "app": {"fn": 7, "arg": 6}},  # Eq.refl Bool true -> F_REFL_TRUE
                {"ie": 9, "const": {"name": 10, "us": []}},
                {"ie": 10, "const": {"name": 12, "us": []}},
                {"ie": 11, "const": {"name": 11, "us": []}},
                {"ie": 12, "app": {"fn": 9, "arg": 11}},
                {"inductive": {
                    "types": [{"all": [1], "ctors": [2], "isRec": False, "isReflexive": False, "isUnsafe": False, "levelParams": [14], "name": 1, "numIndices": 0, "numNested": 0, "numParams": 0, "type": 2}],
                    "ctors": [{"cidx": 0, "induct": 1, "isUnsafe": False, "levelParams": [14], "name": 2, "numFields": 0, "numParams": 0, "type": 3}],
                    "recs": [{"all": [1], "isUnsafe": False, "k": True, "levelParams": [14], "name": 3, "numIndices": 0, "numMinors": 1, "numMotives": 1, "numParams": 0, "rules": [{"ctor": 2, "nfields": 0, "rhs": 0}], "type": 3}],
                }},
                {"inductive": {
                    "types": [{"all": [4], "ctors": [5, 6], "isRec": False, "isReflexive": False, "isUnsafe": False, "levelParams": [], "name": 4, "numIndices": 0, "numNested": 0, "numParams": 0, "type": 1}],
                    "ctors": [
                        {"cidx": 0, "induct": 4, "isUnsafe": False, "levelParams": [], "name": 5, "numFields": 0, "numParams": 0, "type": 5},
                        {"cidx": 1, "induct": 4, "isUnsafe": False, "levelParams": [], "name": 6, "numFields": 0, "numParams": 0, "type": 5},
                    ],
                    "recs": [{"all": [4], "isUnsafe": False, "k": False, "levelParams": [], "name": 7, "numIndices": 0, "numMinors": 2, "numMotives": 1, "numParams": 0, "rules": [], "type": 5}],
                }},
                {"thm": {"all": [10], "levelParams": [], "name": 10, "type": 0, "value": 5}},
                {"thm": {"all": [12], "levelParams": [], "name": 12, "type": 0, "value": 8}},
                {"thm": {"all": [11], "levelParams": [], "name": 11, "type": 0, "value": 10}},
                {"thm": {"all": [13], "levelParams": [], "name": 13, "type": 0, "value": 12}},
            ]
            with open(nd, "w", encoding="utf-8") as f:
                for obj in records:
                    f.write(json.dumps(obj) + "\n")

            with open(os.path.join(src, "Main.lean"), "w", encoding="utf-8") as f:
                f.write("theorem RootA : Prop := True\n")
            with open(os.path.join(src, "Proj", "ModEx.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Proj.Ns\n"
                    "\n"
                    "theorem sign_thm : True := by\n"
                    "  trivial\n"
                    "\n"
                    "example : 1 + 1 = 2 := by\n"
                    "  decide +kernel\n"
                    "\n"
                    "lemma discr_thm : True := by\n"
                    "  have h : 2 + 2 = 4 := by decide +kernel\n"
                    "  trivial\n"
                    "\n"
                    "end Proj.Ns\n"
                )

            lconn = sqlite3.connect(ldb)
            lconn.executescript(
                """
                CREATE TABLE modules(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL);
                CREATE TABLE declarations(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, module TEXT NOT NULL, line_no INTEGER NOT NULL);
                CREATE TABLE forensic_hits(id INTEGER PRIMARY KEY, tag TEXT NOT NULL, severity TEXT NOT NULL, module TEXT NOT NULL, line_no INTEGER NOT NULL, decl_name TEXT, snippet TEXT NOT NULL);
                CREATE TABLE tcb_decls(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL);
                """
            )
            lconn.executemany("INSERT INTO modules(id, name) VALUES (?, ?)", [(1, "Main"), (2, "Proj.ModEx")])
            lconn.executemany("INSERT INTO declarations(id, name, kind, module, line_no) VALUES (?,?,?,?,?)", [
                (1, "RootA", "theorem", "Main", 1),
                (2, "Proj.Ns.sign_thm", "theorem", "Proj.ModEx", 3),
                (3, "discr_thm", "lemma", "Proj.ModEx", 9),
            ])
            # Plant BOTH historical Phase 2 bugs:
            # 1) line 7 (inside anonymous `example`) falsely tagged with preceding `Proj.Ns.sign_thm`
            # 2) line 10 (inside `Proj.Ns.discr_thm`) tagged with bare name `discr_thm`
            lconn.executemany("INSERT INTO forensic_hits(id, tag, severity, module, line_no, decl_name, snippet) VALUES (?,?,?,?,?,?,?)", [
                (1, "decide_kernel", "interesting", "Proj.ModEx", 7, "Proj.Ns.sign_thm", "decide +kernel"),
                (2, "decide_kernel", "interesting", "Proj.ModEx", 10, "discr_thm", "decide +kernel"),
            ])
            lconn.executemany("INSERT INTO tcb_decls(id, name) VALUES (?, ?)", [(1, "Eq"), (2, "Bool")])
            lconn.commit()
            lconn.close()

            out = os.path.join(td, "out")
            rep = kernel.run_pipeline(
                input_path=nd,
                out_dir=out,
                leanre_db=ldb,
                src_dir=src,
                threads=2,
                workers=1,
                oracle_random=10,
                oracle_top=5,
                roots=["RootA:G1"],
                auto_build=False,
                verbose=False,
            )
            self.assertEqual(rep["k5_dominators_and_taint"]["taint_summary"]["validation"]["failures"], 0)
            kdb = os.path.join(out, "kernel.db")
            kconn = kernel._open_kernel_ro(kdb)
            try:
                rows = kconn.execute(
                    "SELECT s.decl_id, d.name, s.origin, s.module, s.line_no "
                    "FROM taint_sources s LEFT JOIN decls d ON d.id = s.decl_id "
                    "WHERE s.class = 'decide_kernel' ORDER BY s.id"
                ).fetchall()
                named = {r[1] for r in rows if r[0] is not None}
                anon = [r for r in rows if r[0] is None]
                self.assertNotIn("Proj.Ns.sign_thm", named)
                self.assertEqual(named, {"Proj.Ns.discr_thm", "Proj.Ns.discr_thm._proof_1_2"})
                self.assertEqual(len(anon), 1)
                self.assertEqual(anon[0][2], "source-hit:anonymous_example")
                self.assertEqual(anon[0][3], "Proj.ModEx")
                self.assertEqual(anon[0][4], 7)
                # Validator handles NULL decl_id cleanly
                self.assertEqual(kernel.validate_taint_paths(kconn)["failures"], 0)
            finally:
                kconn.close()

    def test_cone_audit_stats_callers_slice_aliases_and_anchor(self):
        """Unit test for co-evolution subcommands: cone-audit, stats, callers,
        slice fwd/bwd + --project-only, suffix/module resolution, and anchor + --verify-md.
        """
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "k.db")
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Proj", "Slope"), exist_ok=True)
            os.makedirs(os.path.join(src, "Proj", "Published"), exist_ok=True)

            # Write synthetic Lean source files for anchor + verify-md tests
            with open(os.path.join(src, "Main.lean"), "w", encoding="utf-8") as f:
                f.write("theorem rootMain : Prop := True\n")
            with open(os.path.join(src, "Proj", "Slope", "Core.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Proj.Slope\n"
                    "opaque secretOp : Nat\n"
                    "@[simp]\n"
                    "theorem slopeLemma : True := by\n"
                    "  trivial\n"
                    "end Proj.Slope\n"
                )
            with open(os.path.join(src, "Proj", "Published", "Ex.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Proj.Published\n"
                    "theorem pubThm : True := trivial\n"
                    "end Proj.Published\n"
                )

            conn = sqlite3.connect(kdb)
            conn.executescript(
                """
                CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
                    type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
                    fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
                    live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT);
                CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT, sig_size INTEGER, n_local INTEGER);
                CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
                CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
                CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
                CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
                CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
                CREATE TABLE taint_sources(id INTEGER PRIMARY KEY, class TEXT NOT NULL, decl_id INTEGER, origin TEXT NOT NULL, module TEXT, line_no INTEGER, detail TEXT NOT NULL);
                CREATE UNIQUE INDEX decls_name ON decls(name);
                CREATE UNIQUE INDEX consts_name ON consts(name);
                CREATE INDEX edges_dst ON edges(dst, src);
                """
            )
            # Nodes:
            # 1: propext (ext axiom)
            # 2: MyCustomAx (proj axiom)
            # 3: ExtDecide (ext thm, flags=F_OF_DECIDE)
            # 4: Proj.Slope.secretOp (proj opaque)
            # 5: Proj.Slope.slopeLemma (proj thm, flags=F_REFL_TRUE|F_OF_DECIDE)
            # 6: Proj.Published.pubThm (proj thm)
            # 7: Examples₂.helper (proj def)
            # 8: rootMain (proj thm in module Main)
            # 9: TopCallerA (proj thm)
            # 10: TopCallerB (proj thm)
            # 11: ExtCaller (ext thm)
            conn.executemany(
                "INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NULL,NULL)",
                [
                    (1, "propext", "axiom", 1, 1, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0),
                    (2, "Proj.MyCustomAx", "axiom", 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0),
                    (3, "Mathlib.ExtDecide", "thm", 1, 5, 10, 1, 1, 0, 1, kernel.F_OF_DECIDE, 1, 0, 0, 0),
                    (4, "Proj.Slope.secretOp", "opaque", 1, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0),
                    (5, "Proj.Slope.slopeLemma", "thm", 1, 4, 20, 3, 4, 1, 3, kernel.F_REFL_TRUE | kernel.F_OF_DECIDE, 1, 0, 0, 0),
                    (6, "Proj.Published.pubThm", "thm", 1, 3, 5, 1, 1, 0, 1, 0, 1, 0, 0, 0),
                    (7, "Proj.Examples₂.helper", "def", 1, 3, 8, 1, 1, 0, 1, 0, 1, 0, 0, 0),
                    (8, "rootMain", "thm", 1, 2, 4, 0, 2, 0, 2, 0, 1, 1, 0, 0),
                    (9, "Proj.TopCallerA", "thm", 1, 2, 4, 0, 1, 0, 1, 0, 1, 0, 0, 0),
                    (10, "Proj.TopCallerB", "thm", 1, 2, 4, 0, 1, 0, 1, 0, 1, 0, 0, 0),
                    (11, "Mathlib.ExtCaller", "thm", 1, 2, 4, 0, 1, 0, 1, 0, 0, 0, 0, 0),
                ],
            )
            conn.executemany(
                "INSERT INTO edges VALUES (?,?,?)",
                [
                    (3, 1, 2),
                    (5, 1, 2),
                    (5, 2, 2),
                    (5, 3, 2),
                    (5, 4, 1),
                    (6, 5, 2),
                    (7, 5, 2),
                    (8, 6, 2),
                    (8, 7, 2),
                    (9, 6, 2),
                    (10, 7, 2),
                    (11, 5, 2),
                ],
            )
            conn.execute("INSERT INTO roots VALUES (0, 'rootMain', 8, 'RH')")
            conn.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '0', 10)")
            conn.executemany(
                "INSERT INTO dom VALUES (0, ?, ?, ?, ?)",
                [
                    (8, None, 0, 8),
                    (6, 8, 1, 10),
                    (7, 8, 1, 2),
                    (5, 8, 1, 5),
                    (9, None, 0, 20),
                    (10, None, 0, 3),
                ],
            )
            conn.executemany(
                "INSERT INTO decl_module VALUES (?,?,?,NULL)",
                [
                    (1, None, "unmatched:challenge_library"),
                    (2, "Proj.Slope.Core", "leanre_db:exact"),
                    (3, None, "unmatched:library_or_external"),
                    (4, "Proj.Slope.Core", "leanre_db:exact"),
                    (5, "Proj.Slope.Core", "leanre_db:exact"),
                    (6, "Proj.Published.Ex", "leanre_db:exact"),
                    (7, "Proj.Published.Ex", "leanre_db:exact"),
                    (8, "Main", "leanre_db:exact"),
                    (9, "Proj.Published.Ex", "leanre_db:exact"),
                    (10, "Proj.Published.Ex", "leanre_db:exact"),
                    (11, None, "unmatched:library_or_external"),
                ],
            )
            conn.executemany(
                "INSERT INTO taint_sources VALUES (?,?,?,?,?,?,?)",
                [
                    (1, "decide_kernel", 5, "source-hit:leanre.db", "Proj.Slope.Core", 4, "hit"),
                    (2, "decide_kernel_pattern", 5, "kernel-pattern", "Proj.Slope.Core", None, "pat"),
                    (3, "decide_kernel_pattern", 3, "kernel-pattern", None, None, "pat"),
                    (4, "decide_kernel", None, "source-hit:anonymous_example", "Proj.Slope.Core", 9, "anon"),
                ],
            )
            conn.commit()
            conn.close()

            # 1. cone-audit: exact cone, project vs external taints, custom axiom, project opaque, filter-mod, flag-prefix, suffix resolution
            ca = kernel.cone_audit_decls(
                kdb,
                ["Main.rootMain", "slopeLemma"],
                filter_mod="Robba|Slope",
                flag_prefixes=["Published.", "Examples₂"],
                top_mods=5,
            )
            self.assertEqual(ca["schema"], "leanre.kernel.cone_audit/1")
            self.assertEqual(len(ca["targets"]), 2)
            self.assertIsNotNone(ca["union"])
            t0 = ca["targets"][0]
            self.assertEqual(t0["target"]["name"], "rootMain")
            self.assertEqual(t0["counts"]["total"], 8)
            self.assertEqual(t0["counts"]["project"], 6)
            self.assertEqual(t0["counts"]["external"], 2)
            self.assertEqual(t0["axioms"]["standard"], ["propext"])
            self.assertEqual(t0["axioms"]["project_custom"], ["Proj.MyCustomAx"])
            self.assertEqual(t0["project_opaques"]["count"], 1)
            self.assertEqual(t0["project_opaques"]["decls"][0]["name"], "Proj.Slope.secretOp")
            self.assertEqual(t0["taints"]["decide_kernel"]["project"], 1)
            self.assertEqual(t0["taints"]["decide_kernel"]["external"], 0)
            self.assertEqual(t0["taints"]["decide_kernel_pattern"]["project"], 1)
            self.assertEqual(t0["taints"]["decide_kernel_pattern"]["external"], 1)
            self.assertEqual(t0["flag_prefix_matches"]["Published."]["count"], 2)
            self.assertEqual(t0["flag_prefix_matches"]["Examples₂"]["count"], 1)
            self.assertEqual(t0["filter_mod"]["matched_modules_count"], 1)
            self.assertEqual(t0["filter_mod"]["matched_decls_count"], 3)
            self.assertIn("Proj.MyCustomAx", kernel.format_cone_audit_text(ca))
            # Bad regex cleanly returns CLI rc=1
            self.assertEqual(kernel.main(["cone-audit", "rootMain", "--kernel-db", kdb, "--filter-mod", "[unclosed"]), 1)

            # 2. stats: batch + module-prefix (`Main.rootMain`) + anchor via `--src-root`
            st = kernel.stats_decls(kdb, ["Main.rootMain", "slopeLemma"], src_root=src)
            self.assertEqual([d["name"] for d in st["decls"]], ["rootMain", "Proj.Slope.slopeLemma"])
            self.assertEqual(st["decls"][0]["anchor"], "src/Main.lean:1")
            self.assertEqual(st["decls"][1]["anchor"], "src/Proj/Slope/Core.lean:4")
            self.assertIn("| rootMain |", kernel.format_stats_text(st, table=True))

            # 3. callers: upward walk, project-only, grouped, sorted by dom
            cl = kernel.callers_decl(kdb, "slopeLemma", depth=2, project_only=True, grouped=True, sort_by="dom")
            self.assertEqual(len(cl["hops"]), 2)
            hop1_names = [x["name"] for x in cl["hops"][0]["groups"][0]["callers"]]
            # Mathlib.ExtCaller excluded by project_only; pubThm (dom=10) before helper (dom=2)
            self.assertEqual(hop1_names, ["Proj.Published.pubThm", "Proj.Examples₂.helper"])
            self.assertIn("parent Proj.Slope.slopeLemma", kernel.format_callers_text(cl, grouped=True))

            # 4. slice ergonomic aliases (`fwd`/`bwd`) + `--project-only`
            sl_bwd_proj = kernel.slice_decl(kdb, "Proj.Slope.slopeLemma", direction="bwd", depth=2, project_only=True)
            self.assertEqual(sl_bwd_proj["params"]["direction"], "backward")
            self.assertTrue(sl_bwd_proj["params"]["project_only"])
            self.assertEqual({n["name"] for n in sl_bwd_proj["nodes"]}, {"Proj.Slope.slopeLemma", "Proj.MyCustomAx", "Proj.Slope.secretOp"})
            sl_fwd = kernel.slice_decl(kdb, "Proj.Slope.slopeLemma", direction="fwd", depth=1, project_only=True)
            self.assertEqual(sl_fwd["params"]["direction"], "forward")
            self.assertEqual({n["name"] for n in sl_fwd["nodes"]}, {"Proj.Slope.slopeLemma", "Proj.Published.pubThm", "Proj.Examples₂.helper"})

            # 5. anchor: decls + --verify-md (valid, broken line, symbol mismatch, raw Linkies, symlink escape)
            anc = kernel.anchor_decls(kdb, ["Main.rootMain", "Proj.Slope.slopeLemma", "propext"], src_root=src)
            self.assertTrue(anc["all_passed"])
            self.assertEqual(anc["decls"][0]["line_no"], 1)
            self.assertEqual(anc["decls"][1]["line_no"], 4)
            self.assertEqual(anc["decls"][2]["status"], "external")

            good_md = os.path.join(td, "good.md")
            with open(good_md, "w", encoding="utf-8") as f:
                f.write(
                    "See [Proj.Slope.slopeLemma](https://github.com/org/repo/blob/deadbeef/src/Proj/Slope/Core.lean#L3) "
                    "and [the main root](https://github.com/org/repo/blob/deadbeef/src/Main.lean#L1).\n"
                )
            self.assertEqual(kernel.main(["anchor", "--verify-md", good_md, "--src-root", src, "--kernel-db", kdb]), 0)

            # Plant symlink outside src_root
            outside = os.path.join(td, "outside.lean")
            with open(outside, "w", encoding="utf-8") as f:
                f.write("theorem leak : True := trivial\n")
            os.symlink(outside, os.path.join(src, "escape.lean"))

            bad_md = os.path.join(td, "bad.md")
            with open(bad_md, "w", encoding="utf-8") as f:
                f.write(
                    "- [Core.lean#L4](https://github.com/org/repo/blob/deadbeef/src/Proj/Slope/Core.lean#L4)\n"
                    "- [wrongSym](https://github.com/org/repo/blob/deadbeef/src/Proj/Slope/Core.lean#L4)\n"
                    "- [rootMain](https://github.com/org/repo/blob/deadbeef/src/Main.lean#L99)\n"
                    "- [leak](https://github.com/org/repo/blob/deadbeef/src/escape.lean#L1)\n"
                    "- [missing](https://github.com/org/repo/blob/deadbeef/src/NoSuch.lean#L1)\n"
                )
            md_res = kernel.verify_markdown_anchors([bad_md], src)
            self.assertFalse(md_res["all_passed"])
            self.assertEqual(md_res["linkies_violations"], 1)
            self.assertEqual(md_res["broken_links"], 4)
            issue_kinds = {iss["kind"] for iss in md_res["files"][0]["issues"]}
            self.assertEqual(issue_kinds, {"raw_linkies_violation", "symbol_mismatch", "line_out_of_bounds", "symlink_escape", "file_not_found"})
            self.assertEqual(kernel.main(["anchor", "--verify-md", bad_md, "--src-root", src, "--kernel-db", kdb]), 1)

            # CLI exit codes for new subcommands
            self.assertEqual(kernel.main(["cone-audit", "Main.rootMain", "--kernel-db", kdb, "--json"]), 0)
            self.assertEqual(kernel.main(["stats", "Main.rootMain", "--kernel-db", kdb, "--table"]), 0)
            self.assertEqual(kernel.main(["callers", "slopeLemma", "--kernel-db", kdb, "--depth", "2", "--grouped"]), 0)
            self.assertEqual(kernel.main(["slice", "slopeLemma", "--kernel-db", kdb, "--dir", "fwd", "--project-only"]), 0)

    def test_cone_audit_flag_prefix_kind_split_and_continue_on_error(self):
        """Unit test for Loop 3 cone-audit upgrades:
        - `--flag-prefix` splits hits by kernel `kind` (`def` vs `thm`/`axiom`/`opaque`/`inductive`)
        - `--continue-on-error` reports missing targets without aborting valid targets in a batch
        """
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "k_ca.db")
            conn = sqlite3.connect(kdb)
            conn.executescript(
                """
                CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
                    type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
                    fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
                    live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT);
                CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT, sig_size INTEGER, n_local INTEGER);
                CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
                CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
                CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
                CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
                CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
                CREATE TABLE reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, parent INTEGER, dist INTEGER NOT NULL, PRIMARY KEY(root_id, decl_id)) WITHOUT ROWID;
                CREATE UNIQUE INDEX decls_name ON decls(name);
                CREATE INDEX edges_dst ON edges(dst, src);
                """
            )
            conn.executemany(
                "INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NULL,NULL)",
                [
                    (1, "Proj.Published.SpecProp", "def", 1, 2, 4, 1, 0, 0, 0, 0, 1, 0, 0, 0),
                    (2, "Proj.Published.AssumedThm", "thm", 1, 2, 4, 1, 0, 0, 0, 0, 1, 0, 0, 0),
                    (3, "Proj.Published.AssumedAx", "axiom", 1, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0),
                    (4, "Proj.Published.PubInd", "inductive", 1, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0),
                    (5, "Proj.Published.PubOpaque", "opaque", 1, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0),
                    (6, "Proj.SpecOnlyTarget", "thm", 1, 2, 4, 0, 1, 1, 0, 0, 1, 1, 0, 0),
                    (7, "Proj.MixedTarget", "thm", 1, 2, 10, 0, 5, 1, 4, 0, 1, 1, 0, 0),
                ],
            )
            conn.executemany(
                "INSERT INTO edges VALUES (?,?,?)",
                [
                    (6, 1, 1),
                    (7, 1, 1),
                    (7, 2, 2),
                    (7, 3, 2),
                    (7, 4, 1),
                    (7, 5, 2),
                ],
            )
            conn.execute("INSERT INTO roots VALUES (0, 'Proj.MixedTarget', 7, 'G')")
            conn.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '0', 7)")
            conn.executemany(
                "INSERT INTO decl_module VALUES (?,?,?,NULL)",
                [
                    (1, "Proj.Published.Defs", "leanre_db:exact"),
                    (2, "Proj.Published.Thms", "leanre_db:exact"),
                    (3, "Proj.Published.Ax", "leanre_db:exact"),
                    (4, "Proj.Published.Ind", "leanre_db:exact"),
                    (5, "Proj.Published.Op", "leanre_db:exact"),
                    (6, "Proj.Main", "leanre_db:exact"),
                    (7, "Proj.Main", "leanre_db:exact"),
                ],
            )
            conn.commit()
            conn.close()

            # 1. Spec-only target: Published. has ONLY def=1, 0 thm/axiom/opaque
            ca_spec = kernel.cone_audit_decls(kdb, ["Proj.SpecOnlyTarget"], flag_prefixes=["Published."])
            fp_spec = ca_spec["targets"][0]["flag_prefix_matches"]["Published."]
            self.assertEqual(fp_spec["count"], 1)
            self.assertEqual(fp_spec["by_kind"]["def"], 1)
            self.assertEqual(fp_spec["by_kind"]["thm"], 0)
            self.assertEqual(fp_spec["by_kind"]["axiom"], 0)
            self.assertEqual(fp_spec["decls_by_kind"], {"def": ["Proj.Published.SpecProp"]})

            # 2. Mixed target: all 5 kinds cleanly separated
            ca_mix = kernel.cone_audit_decls(kdb, ["Proj.MixedTarget"], flag_prefixes=["Published."])
            fp_mix = ca_mix["targets"][0]["flag_prefix_matches"]["Published."]
            self.assertEqual(fp_mix["count"], 5)
            self.assertEqual(fp_mix["by_kind"]["def"], 1)
            self.assertEqual(fp_mix["by_kind"]["thm"], 1)
            self.assertEqual(fp_mix["by_kind"]["axiom"], 1)
            self.assertEqual(fp_mix["by_kind"]["inductive"], 1)
            self.assertEqual(fp_mix["by_kind"]["opaque"], 1)
            self.assertEqual(fp_mix["decls_by_kind"]["def"], ["Proj.Published.SpecProp"])
            self.assertEqual(fp_mix["decls_by_kind"]["thm"], ["Proj.Published.AssumedThm"])
            self.assertEqual(fp_mix["decls_by_kind"]["axiom"], ["Proj.Published.AssumedAx"])
            txt_mix = kernel.format_cone_audit_text(ca_mix)
            self.assertIn("[def (1)]: Proj.Published.SpecProp", txt_mix)
            self.assertIn("[axiom (1)]: Proj.Published.AssumedAx", txt_mix)
            self.assertIn("[thm (1)]: Proj.Published.AssumedThm", txt_mix)

            # 3. Default strict mode fails on missing target; --continue-on-error preserves valid targets
            with self.assertRaises(LookupError):
                kernel.cone_audit_decls(kdb, ["Proj.SpecOnlyTarget", "Proj.NoSuchDecl"])
            self.assertEqual(
                kernel.main(["cone-audit", "Proj.SpecOnlyTarget", "Proj.NoSuchDecl", "--kernel-db", kdb]),
                1,
            )
            ca_cont = kernel.cone_audit_decls(
                kdb,
                ["Proj.SpecOnlyTarget", "Proj.NoSuchDecl", "Proj.MixedTarget"],
                flag_prefixes=["Published."],
                continue_on_error=True,
            )
            self.assertEqual([t["target"]["name"] for t in ca_cont["targets"]], ["Proj.SpecOnlyTarget", "Proj.MixedTarget"])
            self.assertIsNotNone(ca_cont["union"])
            self.assertEqual(len(ca_cont["errors"]), 1)
            self.assertEqual(ca_cont["errors"][0]["query"], "Proj.NoSuchDecl")
            self.assertIn("Unresolved targets (1):", kernel.format_cone_audit_text(ca_cont))
            out_json = os.path.join(td, "ca_cont.json")
            self.assertEqual(
                kernel.main([
                    "cone-audit", "Proj.SpecOnlyTarget", "Proj.NoSuchDecl",
                    "--kernel-db", kdb, "--continue-on-error", "--json", "--out", out_json,
                ]),
                0,
            )
            with open(out_json, "r", encoding="utf-8") as f:
                loaded = json.load(f)
            self.assertEqual(len(loaded["targets"]), 1)
            self.assertEqual(len(loaded["errors"]), 1)
            # All-missing batch with --continue-on-error exits 1
            self.assertEqual(
                kernel.main(["cone-audit", "Proj.NoSuch1", "Proj.NoSuch2", "--kernel-db", kdb, "--continue-on-error", "--out", os.path.join(td, "ca_empty.txt")]),
                1,
            )

    def test_kernel_hygiene_synthetic_and_tiny_demo(self):
        """Unit test for `leanre kernel hygiene`: dropped/unused binders, True/trivial dummy slots,
        And/Prod tuple projection imbalance, --only, --cone-depth, --continue-on-error, and tiny_demo.
        """
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "k_hy.db")
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Proj"), exist_ok=True)

            with open(os.path.join(src, "Proj", "Hygiene.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Proj\n"
                    "\n"
                    "theorem dropIntro : HypA → HypB → ∀ {α : Type} [Inhabited α] (x : α), Goal := by\n"
                    "  intro _ hb α _ x\n"
                    "  exact use hb x\n"
                    "\n"
                    "theorem dropNamed (used : Nat) (unusedHyp : Prop) (_unusedUnder : Prop) (_ : Nat) : used = used := rfl\n"
                    "\n"
                    "theorem dropFun : HypA → HypB → Goal :=\n"
                    "  fun a _ => use a\n"
                    "\n"
                    "theorem trueParams (h : True) : HypA → True → Goal := by\n"
                    "  intro a _\n"
                    "  exact mkGoal a\n"
                    "\n"
                    "theorem trueCaller (a : HypA) : Goal :=\n"
                    "  trueParams True.intro a trivial\n"
                    "\n"
                    "structure TrueStruct where\n"
                    "  realField : Nat\n"
                    "  dummyField : True\n"
                    "\n"
                    "theorem tacticTrivialClean (x : Nat) : x = x := by\n"
                    "  have _ok : True := by\n"
                    "    trivial\n"
                    "  rfl\n"
                    "\n"
                    "theorem pairImbalanced : LegA ∧ LegB :=\n"
                    "  ⟨mkA, mkB⟩\n"
                    "\n"
                    "theorem usePairLeft1 : LegA :=\n"
                    "  pairImbalanced.1\n"
                    "\n"
                    "theorem usePairLeft2 : LegA :=\n"
                    "  (pairImbalanced).left\n"
                    "\n"
                    "theorem pairDiscarded : LegA × LegB :=\n"
                    "  (mkA, mkB)\n"
                    "\n"
                    "theorem usePairDiscard : LegA := by\n"
                    "  let ⟨a, -⟩ := pairDiscarded\n"
                    "  exact a\n"
                    "\n"
                    "theorem pairBalanced : LegA ∧ LegB :=\n"
                    "  ⟨mkA, mkB⟩\n"
                    "\n"
                    "theorem useBal1 : LegA := pairBalanced.1\n"
                    "theorem useBal2 : LegB := pairBalanced.2\n"
                    "\n"
                    "end Proj\n"
                )

            conn = sqlite3.connect(kdb)
            conn.executescript(
                """
                CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
                    type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
                    fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
                    live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT);
                CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT, sig_size INTEGER, n_local INTEGER);
                CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
                CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
                CREATE TABLE reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, parent INTEGER, dist INTEGER NOT NULL, PRIMARY KEY(root_id, decl_id)) WITHOUT ROWID;
                CREATE UNIQUE INDEX decls_name ON decls(name);
                CREATE INDEX edges_dst ON edges(dst, src);
                """
            )
            decl_rows = [
                (1, "True", "inductive", 1, 1, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0),
                (2, "And", "inductive", 1, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0),
                (3, "Prod", "inductive", 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0),
                (10, "Proj.dropIntro", "thm", 1, 5, 5, 0, 1, 0, 1, 0, 1, 0, 0, 0),
                (11, "Proj.dropNamed", "thm", 1, 5, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0),
                (12, "Proj.dropFun", "thm", 1, 5, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0),
                (13, "Proj.trueParams", "thm", 1, 5, 4, 1, 1, 1, 0, 0, 1, 0, 0, 0),
                (14, "Proj.trueCaller", "thm", 1, 3, 5, 0, 2, 0, 2, 0, 1, 0, 0, 0),
                (15, "Proj.TrueStruct", "inductive", 1, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0),
                (16, "Proj.tacticTrivialClean", "thm", 1, 3, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0),
                (17, "Proj.pairImbalanced", "thm", 1, 3, 3, 2, 1, 1, 0, 0, 1, 0, 0, 0),
                (18, "Proj.usePairLeft1", "thm", 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0),
                (19, "Proj.usePairLeft2", "thm", 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0),
                (20, "Proj.pairDiscarded", "thm", 1, 3, 3, 1, 1, 1, 0, 0, 1, 0, 0, 0),
                (21, "Proj.usePairDiscard", "thm", 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0),
                (22, "Proj.pairBalanced", "thm", 1, 3, 3, 2, 1, 1, 0, 0, 1, 0, 0, 0),
                (23, "Proj.useBal1", "thm", 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0),
                (24, "Proj.useBal2", "thm", 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0),
            ]
            conn.executemany("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NULL,NULL)", decl_rows)
            conn.executemany(
                "INSERT INTO edges VALUES (?,?,?)",
                [
                    (10, 14, 2),  # dropIntro -> trueCaller (for cone-depth test)
                    (13, 1, 1),   # trueParams -> True (type)
                    (14, 13, 2),  # trueCaller -> trueParams
                    (14, 1, 2),   # trueCaller -> True (value)
                    (15, 1, 1),   # TrueStruct -> True (type)
                    (16, 1, 2),   # tacticTrivialClean -> True (value)
                    (17, 2, 1),   # pairImbalanced -> And (type)
                    (18, 17, 2),
                    (19, 17, 2),
                    (20, 3, 1),   # pairDiscarded -> Prod (type)
                    (21, 20, 2),
                    (22, 2, 1),   # pairBalanced -> And (type)
                    (23, 22, 2),
                    (24, 22, 2),
                ],
            )
            conn.executemany(
                "INSERT INTO decl_module VALUES (?,?,?,NULL)",
                [
                    (1, None, "unmatched:challenge_library"),
                    (2, None, "unmatched:challenge_library"),
                    (3, None, "unmatched:challenge_library"),
                    *[(d[0], "Proj.Hygiene", "leanre_db:exact") for d in decl_rows if d[0] >= 10],
                ],
            )
            conn.commit()
            conn.close()

            # 1. Dropped binders: intro _, named/underscore/_ header binders, fun _ =>
            r_drop = kernel.hygiene_decls(kdb, ["Proj.dropIntro", "Proj.dropNamed", "Proj.dropFun"], src_root=src, only="dropped")
            self.assertEqual(r_drop["schema"], "leanre.kernel.hygiene/1")
            by_nm = {d["name"]: d for d in r_drop["decls"]}
            # dropIntro: ONLY HypA (slot 0); [Inhabited α] instance `_` and `{α : Type}` NOT flagged!
            f_intro = by_nm["Proj.dropIntro"]["findings"]
            self.assertEqual(len(f_intro), 1)
            self.assertEqual(f_intro[0]["kind"], "intro_wildcard")
            self.assertEqual(f_intro[0]["param_type"], "HypA")
            self.assertEqual(f_intro[0]["confidence"], "heuristic_source")
            # dropNamed: unusedHyp, _unusedUnder, _ (NOT `used`!)
            f_named_binders = {(f["kind"], f["binder"]) for f in by_nm["Proj.dropNamed"]["findings"]}
            self.assertEqual(
                f_named_binders,
                {
                    ("unused_named_binder", "unusedHyp"),
                    ("unused_underscore_binder", "_unusedUnder"),
                    ("explicit_wildcard_binder", "_"),
                },
            )
            # dropFun: fun _ => discards slot 1 (HypB)
            f_fun = by_nm["Proj.dropFun"]["findings"]
            self.assertEqual(len(f_fun), 1)
            self.assertEqual(f_fun[0]["kind"], "fun_wildcard")
            self.assertEqual(f_fun[0]["param_type"], "HypB")

            # 2. True / trivial dummy slots (and standalone tactic `trivial` NOT flagged)
            r_true = kernel.hygiene_decls(
                kdb,
                ["Proj.trueParams", "Proj.trueCaller", "Proj.TrueStruct", "Proj.tacticTrivialClean"],
                src_root=src,
                only="true_slot",
            )
            by_nm_t = {d["name"]: d for d in r_true["decls"]}
            self.assertEqual({f["kind"] for f in by_nm_t["Proj.trueParams"]["findings"]}, {"true_binder", "true_arrow_slot"})
            self.assertEqual({f["kind"] for f in by_nm_t["Proj.trueCaller"]["findings"]}, {"passed_true_intro", "passed_trivial_arg"})
            self.assertEqual({f["kind"] for f in by_nm_t["Proj.TrueStruct"]["findings"]}, {"true_field_slot"})
            self.assertEqual(by_nm_t["Proj.tacticTrivialClean"]["findings"], [])

            # 3. Tuple projection imbalance (imbalanced And, discarded Prod, clean balanced And)
            r_tup = kernel.hygiene_decls(
                kdb,
                ["Proj.pairImbalanced", "Proj.pairDiscarded", "Proj.pairBalanced"],
                src_root=src,
                only="tuple_unread",
            )
            by_nm_u = {d["name"]: d for d in r_tup["decls"]}
            self.assertEqual(len(by_nm_u["Proj.pairImbalanced"]["findings"]), 1)
            self.assertEqual(by_nm_u["Proj.pairImbalanced"]["tuple_summary"]["proj_1_count"], 2)
            self.assertEqual(by_nm_u["Proj.pairImbalanced"]["tuple_summary"]["proj_2_count"], 0)
            self.assertEqual(by_nm_u["Proj.pairImbalanced"]["tuple_summary"]["unread_indices"], [1])
            self.assertEqual(len(by_nm_u["Proj.pairDiscarded"]["findings"]), 1)
            self.assertEqual(by_nm_u["Proj.pairDiscarded"]["tuple_summary"]["discarded_indices"], [1])
            self.assertEqual(by_nm_u["Proj.pairBalanced"]["findings"], [])
            self.assertEqual(by_nm_u["Proj.pairBalanced"]["tuple_summary"]["unread_indices"], [])

            # 4. Shallow --cone-depth + --continue-on-error + CLI JSON/text formatting
            r_cone = kernel.hygiene_decls(
                kdb,
                ["Proj.dropIntro", "Proj.MissingSym"],
                src_root=src,
                cone_depth=2,
                continue_on_error=True,
            )
            audited_names = [d["name"] for d in r_cone["decls"]]
            self.assertEqual(audited_names, ["Proj.dropIntro", "Proj.trueCaller", "Proj.trueParams"])
            self.assertEqual(len(r_cone["errors"]), 1)
            txt_hy = kernel.format_hygiene_text(r_cone)
            self.assertIn("Proj.dropIntro", txt_hy)
            self.assertIn("Unresolved targets (1):", txt_hy)
            self.assertEqual(
                kernel.main([
                    "hygiene", "Proj.dropIntro", "--kernel-db", kdb, "--src-root", src,
                    "--cone-depth", "1", "--json", "--out", os.path.join(td, "hy.json"),
                ]),
                0,
            )
            self.assertEqual(
                kernel.main(["hygiene", "Proj.NoSuch", "--kernel-db", kdb, "--src-root", src]),
                1,
            )

            # 5. Live smoke test on examples/tiny_demo/ (unenriched kernel.db fallback!)
            demo_nd = os.path.join(_REPO_ROOT, "examples", "tiny_demo", "demo.ndjson")
            demo_src = os.path.join(_REPO_ROOT, "examples", "tiny_demo")
            if os.path.exists(kernel.default_binary_path()) and os.path.isfile(demo_nd):
                demo_out = os.path.join(td, "demo_k")
                kernel.run_pipeline(
                    input_path=demo_nd,
                    out_dir=demo_out,
                    threads=2,
                    workers=1,
                    oracle_random=10,
                    oracle_top=5,
                    roots=["TinyDemo.main_theorem:DEMO"],
                    auto_build=False,
                    verbose=False,
                )
                r_demo = kernel.hygiene_decls(
                    os.path.join(demo_out, "kernel.db"),
                    ["TinyDemo.main_theorem"],
                    src_root=demo_src,
                    cone_depth=3,
                )
                self.assertGreaterEqual(r_demo["summary"]["decls_audited"], 5)
                self.assertEqual(r_demo["summary"]["total_findings"], 0)
                self.assertEqual(r_demo["decls"][0]["anchor"], "Main.lean:12")


class TestKernelRealOutputs(unittest.TestCase):
    """If outputs/kernel/kernel.db and outputs/kernel_report.json exist, verify K1-K7 receipts."""

    def test_real_kernel_outputs(self):
        db_path = os.path.join(_REPO_ROOT, "outputs", "kernel", "kernel.db")
        rep_path = os.path.join(_REPO_ROOT, "outputs", "kernel_report.json")
        if not (os.path.exists(db_path) and os.path.exists(rep_path)):
            self.skipTest("full outputs/kernel/kernel.db not generated yet")
        with open(rep_path, "r", encoding="utf-8") as f:
            rep = json.load(f)

        # K1
        self.assertTrue(rep["k1_integrity"]["matches_expected_solution"])
        # K2
        self.assertEqual(rep["k2_counts"]["measured_records"], 1_468_418)
        self.assertEqual(rep["k2_counts"]["measured_constants_unpacked"], 1_484_733)
        self.assertTrue(rep["k2_counts"]["reconciliation"]["formula_check"])
        # K3
        self.assertIsNotNone(rep.get("k3_challenge_regression"))
        self.assertTrue(rep["k3_challenge_regression"]["all_passed"])
        # K4
        self.assertEqual(len(rep["k4_live_dead_and_axioms"]["roots"]), 5)
        # K5
        self.assertEqual(rep["k5_dominators_and_taint"]["dominator_oracle_failures_total"], 0)
        self.assertEqual(rep["k5_dominators_and_taint"]["taint_summary"]["validation"]["failures"], 0)
        # K6
        align = rep["k6_module_alignment"]
        self.assertEqual(align["matched_all"] + align["unmatched_all"], align["total_decls"])
        self.assertEqual(align["total_decls"], 1_468_418)
        # K7
        det = rep["k7_performance_and_determinism"].get("determinism")
        if det is not None:
            self.assertTrue(det["all_content_hashes_identical"])

        # Schema completeness against workbench KERNEL_TABLES
        conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
        try:
            have = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type IN ('table','view')")}
            for tbl in ("meta", "decls", "consts", "edges", "roots", "reach", "stmt_reach", "dom_trees", "dom", "taint_sources", "taint_paths", "decl_module", "axioms"):
                self.assertIn(tbl, have)
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM decls").fetchone()[0], 1_468_418)
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM consts").fetchone()[0], 1_484_733)
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM decl_module").fetchone()[0], 1_468_418)
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM roots").fetchone()[0], 5)
            # K6 regression: core/Mathlib constants must not be falsely aligned via Phase 2 anonymous-end names
            for lib_nm in ("PLift", "PLift.down", "Inter", "Inv", "Std.Antisymm", "Height.mulHeight"):
                row = conn.execute(
                    "SELECT m.module, m.method FROM decls d JOIN decl_module m ON m.decl_id = d.id WHERE d.name = ?",
                    (lib_nm,),
                ).fetchone()
                if row is not None:
                    self.assertIsNone(row[0], f"{lib_nm} falsely aligned to {row}")
                    self.assertTrue(row[1].startswith("unmatched:"), f"{lib_nm} bad method {row}")

            # Phase 4 D4 regression: ChebyshevPrimeBounds.SmallLoop has 9 live decls incl. PI.PC.loop_run._proof_1_1;
            # DyadicPrimeIntervals.Run1..4 have 0 decls in solution.ndjson.zst.
            smallloop_mod = "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop"
            sl_cnt = conn.execute(
                "SELECT COUNT(*) FROM decl_module dm JOIN decls d ON d.id = dm.decl_id WHERE dm.module = ? AND d.live_mask != 0",
                (smallloop_mod,),
            ).fetchone()[0]
            self.assertEqual(sl_cnt, 9)
            timeout_names = {
                r[0]
                for r in conn.execute(
                    "SELECT d.name FROM taint_sources s JOIN decls d ON d.id = s.decl_id WHERE s.class = 'lean4lean_timeout'"
                )
            }
            self.assertEqual(timeout_names, {"PI.PC.loop_run", "PI.PC.loop_run._proof_1_1"})
            for i in range(1, 5):
                run_mod = f"Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run{i}"
                self.assertEqual(conn.execute("SELECT COUNT(*) FROM decl_module WHERE module = ?", (run_mod,)).fetchone()[0], 0)
                self.assertIsNone(conn.execute("SELECT id FROM decls WHERE name = ?", (f"PI.PrimesDyadicRS.K.run{i}",)).fetchone())
        finally:
            conn.close()

        # Phase 4 D4: lean4lean_timeout_audit in report + live slice & type-deps smoke check
        audit = rep["k5_dominators_and_taint"].get("lean4lean_timeout_audit")
        self.assertIsNotNone(audit)
        self.assertEqual(audit["total_timeout_modules"], 5)
        self.assertEqual(audit["live_timeout_modules"], 1)
        self.assertEqual(audit["dead_timeout_modules"], 4)
        self.assertEqual(audit["live_decls_across_timeout_modules"], 9)

        sl = kernel.slice_decl(db_path, "PI.PC.loop_run", direction="backward", depth=1, edge_kind="value-only")
        self.assertEqual({n["name"] for n in sl["nodes"]}, {"PI.PC.loop_run", "PI.PC.loop_run._proof_1_1"})
        td = kernel.inspect_type_deps(db_path, "PI.PC.loop_run._proof_1_1", limit=10)
        self.assertEqual(td["decl"]["flags"], kernel.F_REFL_TRUE)
        self.assertEqual(td["dependents"][0]["name"], "PI.PC.loop_run")
        self.assertEqual(len(td["paths_to_roots"]), 5)

        # Co-evolution smoke checks on live DB & source tree (if mirror present)
        st = kernel.stats_decls(db_path, ["Main.riemannHypothesis"])
        self.assertEqual(st["decls"][0]["name"], "riemannHypothesis")
        cl = kernel.callers_decl(db_path, "UpperTheory.GalStar.AwayB.tame0", depth=2, grouped=True)
        self.assertGreaterEqual(len(cl["hops"]), 2)
        src_root = kernel.default_src_root()
        if os.path.isdir(src_root):
            enc_lsv = kernel.resolve_enclosing_source_decl(
                src_root,
                "Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LoweredSignatureVanishing",
                47,
            )
            self.assertEqual(enc_lsv, ("example", None))
            enc_tw = kernel.resolve_enclosing_source_decl(
                src_root,
                "Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle",
                74,
            )
            self.assertEqual(enc_tw, ("example", None))
            enc_discr = kernel.resolve_enclosing_source_decl(
                src_root,
                "Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary",
                135,
            )
            self.assertEqual(enc_discr, ("lemma", "GlobalTheory.LatticeInvariants.discr_of_cyclic"))

            # Loop 3 live smoke checks: cone-audit kind-split + continue-on-error, and kernel hygiene
            ca_live = kernel.cone_audit_decls(
                db_path,
                ["MainStatements.Hodge.Free.abelianHodgeDeRham'", "NoSuch.MissingDecl"],
                flag_prefixes=["Published."],
                continue_on_error=True,
            )
            self.assertEqual(len(ca_live["targets"]), 1)
            self.assertEqual(len(ca_live["errors"]), 1)
            fp_pub = ca_live["targets"][0]["flag_prefix_matches"]["Published."]
            self.assertEqual(fp_pub["by_kind"]["def"], 1)
            self.assertEqual(fp_pub["by_kind"]["axiom"], 0)
            self.assertIn("GlobalTheory.Published.AbelianHodgeDeRham", fp_pub["decls_by_kind"]["def"])

            hy_hc = kernel.hygiene_decls(
                db_path,
                ["UpperTheory.Lit.I5.unitary_theory_of_harishChandra_langlands_alt"],
                src_root=src_root,
            )
            hc_findings = hy_hc["decls"][0]["findings"]
            self.assertEqual(len(hc_findings), 2)
            self.assertEqual(
                {f["param_type"] for f in hc_findings},
                {
                    "GlobalTheory.Published.HarishChandraAnalyticity",
                    "GlobalTheory.Published.FlathFactorisation",
                },
            )
            hy_true = kernel.hygiene_decls(
                db_path,
                ["GlobalTheory.PsCo.SpecX.specTrace", "GlobalTheory.PsCo.SpecX.main"],
                src_root=src_root,
                only="true_slot",
            )
            self.assertEqual(len(hy_true["decls"][0]["findings"]), 2)
            self.assertEqual(len(hy_true["decls"][1]["findings"]), 2)
            hy_tup = kernel.hygiene_decls(
                db_path,
                ["Formalism.MainNotions.UnusedSlot33.field_lemmas_except_seven"],
                src_root=src_root,
                only="tuple_unread",
            )
            self.assertEqual(hy_tup["decls"][0]["tuple_summary"]["arity"], 8)
            self.assertEqual(hy_tup["decls"][0]["tuple_summary"]["proj_1_count"], 0)
            self.assertEqual(hy_tup["decls"][0]["tuple_summary"]["proj_2_count"], 1)
            self.assertEqual(hy_tup["decls"][0]["tuple_summary"]["unread_indices"], [])
            self.assertTrue(hy_tup["decls"][0]["tuple_summary"]["one_sided_dot_projection"])
            self.assertEqual(len(hy_tup["decls"][0]["findings"]), 0)

            # Loop 5 real-DB regression checks (HYG-01..08, exact-case, type-deps truncation, FamP)
            hy_bl = kernel.hygiene_decls(
                db_path,
                ["GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt"],
                src_root=src_root,
                only="tuple_unread",
            )
            self.assertEqual(len(hy_bl["decls"][0]["findings"]), 1)
            self.assertEqual(hy_bl["decls"][0]["tuple_summary"]["unread_indices"], [1])
            self.assertGreaterEqual(hy_bl["decls"][0]["tuple_summary"]["unwrapped_aliases"], 1)

            hy_all6 = kernel.hygiene_decls(
                db_path,
                [
                    "GlobalTheory.allSixLaws",
                    "GlobalTheory.existsUnique_hom_extension_semiAbelian",
                    "GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers",
                ],
                src_root=src_root,
                only="tuple_unread",
            )
            self.assertEqual(hy_all6["summary"]["total_findings"], 0)

            hy_clean = kernel.hygiene_decls(
                db_path,
                [
                    "GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos",
                    "GlobalTheory.PMon.hyodo",
                    "Formalism.MainNotions.FamP",
                    "Formalism.MainNotions.FamP.Csz",
                ],
                src_root=src_root,
                cone_depth=0,
            )
            self.assertEqual(hy_clean["summary"]["total_findings"], 0)
            hy_derham = kernel.hygiene_decls(
                db_path,
                ["GlobalTheory.deRham_potentiallySemistable"],
                src_root=src_root,
                cone_depth=2,
                max_decls=40,
            )
            self.assertEqual(hy_derham["summary"]["total_findings"], 0)

            # Loop 6 real-DB regression checks: FamP.Large, link_of_local_closed, 5-comp obtain, Hironaka, .mk callers, stats legend
            hy_famp_large = kernel.hygiene_decls(db_path, ["Formalism.MainNotions.FamP.Large"], src_root=src_root)
            self.assertEqual(len(hy_famp_large["decls"][0]["findings"]), 1)
            self.assertEqual(hy_famp_large["decls"][0]["findings"][0]["kind"], "conjunct_true_slot")

            hy_loc = kernel.hygiene_decls(db_path, ["Formalism.L2.G.link_of_local_closed"], src_root=src_root, cone_depth=0)
            self.assertEqual(len(hy_loc["decls"][0]["findings"]), 2)
            self.assertEqual(
                {f["leaf_decl"] for f in hy_loc["decls"][0]["findings"]},
                {"Formalism.MainNotions.G.signs_closed", "Formalism.MainNotions.G.ones_closed"},
            )
            self.assertEqual(sum(len(f["unread_indices"]) for f in hy_loc["decls"][0]["findings"]), 3)

            hy_stageu = kernel.hygiene_decls(
                db_path,
                ["GlobalTheory.Fc.StageOneU.member_bundles_large_unramified_exponents_alt"],
                src_root=src_root,
                cone_depth=2,
            )
            hyps_entry = next(
                (d for d in hy_stageu["decls"] if d["name"] == "GlobalTheory.T.hyps_e_third_layer_ser_n_of_geometric_galois"),
                None,
            )
            self.assertIsNotNone(hyps_entry)
            self.assertEqual(hyps_entry["findings"], [])
            self.assertEqual(hyps_entry["tuple_summary"]["unread_indices"], [])

            hy_hir = kernel.hygiene_decls(
                db_path,
                ["FunctorialResolution.EmbeddedResolution.strongResolutionOfSingularitiesCharZero"],
                src_root=src_root,
                cone_depth=2,
            )
            self.assertEqual(hy_hir["summary"]["by_category"]["true_slot"], 0)
            self.assertLessEqual(hy_hir["summary"]["by_category"]["dropped"], 5)
            self.assertGreaterEqual(hy_hir["summary"]["suppressed_counts"]["by_reason"].get("top_univ_membership", 0), 2)

            hy_true_keep = kernel.hygiene_decls(
                db_path,
                ["GlobalTheory.CompanionTheory.HopfLe.hopfLeSt", "GlobalTheory.Published.UnusedSlot72"],
                src_root=src_root,
                only="true_slot",
            )
            self.assertEqual(hy_true_keep["summary"]["total_findings"], 1)
            self.assertEqual(hy_true_keep["summary"]["suppressed_counts"]["by_reason"].get("activating_premise"), 1)
            hy_true_act = kernel.hygiene_decls(
                db_path,
                ["GlobalTheory.CompanionTheory.HopfLe.hopfLeSt"],
                src_root=src_root,
                only="true_slot",
                include_noisy=True,
            )
            self.assertEqual(hy_true_act["decls"][0]["findings"][0].get("role"), "activating_premise")

            with self.assertRaises(LookupError) as mk_ctx:
                kernel.callers_decl(db_path, "GlobalTheory.EX.OB.ChOK.mk")
            self.assertIn("folded into 'GlobalTheory.EX.OB.ChOK'", str(mk_ctx.exception))

            st_case = kernel.stats_decls(db_path, ["zFRDirichlet", "ZFRDirichlet", "NoSuchDecl"], continue_on_error=True)
            self.assertEqual(st_case["errors_count"], 1)
            self.assertEqual(len(st_case["decls"]), 2)
            self.assertEqual(st_case["decls"][0]["name"], "Formalism.ZeroFreeDirichlet.zFRDirichlet")
            self.assertEqual(st_case["decls"][1]["name"], "Formalism.ZeroFreeDirichlet.ZFRDirichlet")
            self.assertIn("1=riemannHypothesis", kernel.format_stats_text(st_case))

            # Loop 7 real-DB regression checks: Struct.field anchors, Round 6B hygiene cluster, semantic opt-in, alias_of
            anc_fields = kernel.anchor_decls(
                db_path,
                [
                    "Formalism.BasicNotions.ParameterChoice'.k_low",
                    "Formalism.BasicNotions.SizeData₂.Gam_eq",
                    "GlobalTheory.Mem.R3.RealInAlt.seeEval",
                ],
                src_root=src_root,
            )
            self.assertTrue(anc_fields["all_passed"])
            by_anc = {d["name"]: d for d in anc_fields["decls"]}
            self.assertEqual(by_anc["Formalism.BasicNotions.ParameterChoice'.k_low"]["line_no"], 137)
            self.assertEqual(by_anc["Formalism.BasicNotions.ParameterChoice'.k_low"]["match_kind"], "field")
            self.assertEqual(by_anc["Formalism.BasicNotions.ParameterChoice'.k_low"]["parent_line"], 62)
            self.assertEqual(by_anc["Formalism.BasicNotions.SizeData₂.Gam_eq"]["line_no"], 176)
            self.assertEqual(by_anc["Formalism.BasicNotions.SizeData₂.Gam_eq"]["match_kind"], "field")
            self.assertEqual(by_anc["GlobalTheory.Mem.R3.RealInAlt.seeEval"]["line_no"], 47)
            self.assertEqual(by_anc["GlobalTheory.Mem.R3.RealInAlt.seeEval"]["match_kind"], "field")

            hy_r6b = kernel.hygiene_decls(
                db_path,
                [
                    "UpperTheory.V.eventually_winPair_gt_power",
                    "UpperTheory.Kd.K4.mlTOf",
                    "UpperTheory.Top.fieldChi",
                    "GlobalTheory.CompanionTheory.HopfLe.hopfLeSt",
                    "GlobalTheory.CompanionTheory.HopfC.hopfFieldSt",
                    "GlobalTheory.CompanionTheory.NoethApprox.schemeModels",
                    "GroundTheory.ProfCoh.injective_tateGlobalToLocal_iff",
                    "GroundTheory.Arith.SchemeCoh.Scheme.Modules.SupportedIn.univ",
                ],
                src_root=src_root,
            )
            self.assertEqual(hy_r6b["summary"]["by_category"]["true_slot"], 0)
            self.assertEqual(hy_r6b["summary"]["by_category"]["tuple_unread"], 0)
            self.assertEqual(hy_r6b["summary"]["by_category"]["dropped"], 6)
            by_r6b = {d["name"]: d for d in hy_r6b["decls"]}
            for clean_nm in (
                "UpperTheory.V.eventually_winPair_gt_power",
                "UpperTheory.Kd.K4.mlTOf",
                "UpperTheory.Top.fieldChi",
                "GlobalTheory.CompanionTheory.NoethApprox.schemeModels",
                "GroundTheory.ProfCoh.injective_tateGlobalToLocal_iff",
                "GroundTheory.Arith.SchemeCoh.Scheme.Modules.SupportedIn.univ",
            ):
                self.assertEqual(by_r6b[clean_nm]["findings"], [], f"unexpected finding on {clean_nm}")
            self.assertEqual(
                hy_r6b["summary"]["suppressed_counts"]["by_reason"].get("local_class_instance"),
                4,
            )
            self.assertEqual(
                hy_r6b["summary"]["suppressed_counts"]["by_reason"].get("activating_premise"),
                2,
            )
            self.assertEqual(
                [f["slot_index"] for f in by_r6b["GlobalTheory.CompanionTheory.HopfLe.hopfLeSt"]["findings"] if f["kind"] == "intro_wildcard"],
                [0, 1, 2],
            )
            self.assertEqual(
                [f["slot_index"] for f in by_r6b["GlobalTheory.CompanionTheory.HopfC.hopfFieldSt"]["findings"] if f["kind"] == "intro_wildcard"],
                [2],
            )

            hy_sem = kernel.hygiene_decls(
                db_path,
                [
                    "Formalism.IndefR.AutomorphicEvaluation.sEEofTT",
                    "Formalism.L2.GlobalTheoryTheory.Places.places_at_of",
                ],
                src_root=src_root,
                only="semantic",
            )
            self.assertEqual(hy_sem["summary"]["total_findings"], 3)
            by_sem = {d["name"]: d["findings"] for d in hy_sem["decls"]}
            self.assertEqual([f["kind"] for f in by_sem["Formalism.IndefR.AutomorphicEvaluation.sEEofTT"]], ["default_zero_branch"])
            self.assertEqual([f["line_no"] for f in by_sem["Formalism.L2.GlobalTheoryTheory.Places.places_at_of"]], [367, 381])

            st_alias = kernel.stats_decls(db_path, ["Formalism.DivisorInequality.boundsMu"], src_root=src_root, with_alias=True)
            self.assertEqual(st_alias["decls"][0].get("alias_of"), "Formalism.DivisorInequality.slope_bounds")


class TestKernelLoop5PrecisionAndCli(unittest.TestCase):
    """Regression suite for Loop 5 kernel fixes: exact-case & partial-prefix resolution,
    continue-on-error on stats/callers, type-deps truncation notices, hygiene precision
    (HYG-01..08 / R4OPUS-01), and XREPO-03/08 leanre.toml root auto-discovery.
    """

    def test_exact_case_resolution_stats_callers_continue_on_error_and_type_deps_truncation(self):
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "k5.db")
            conn = sqlite3.connect(kdb)
            conn.executescript(
                """
                CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
                    type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
                    fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
                    live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT);
                CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT, sig_size INTEGER, n_local INTEGER);
                CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
                CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
                CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
                CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
                CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
                CREATE TABLE reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, parent INTEGER, dist INTEGER NOT NULL, PRIMARY KEY(root_id, decl_id)) WITHOUT ROWID;
                CREATE UNIQUE INDEX decls_name ON decls(name);
                CREATE INDEX edges_dst ON edges(dst, src);
                """
            )
            # Case pair: zFRDirichlet vs ZFRDirichlet, exact uppercase MAIN vs lowercase *.main, partial prefix A.Sub.leaf
            decl_rows = [
                (1, "Proj.ZeroFree.zFRDirichlet", "thm", 1, 2, 2, 1, 1, 1, 0, 0, 1, 1, 0, 0),
                (2, "Proj.ZeroFree.ZFRDirichlet", "def", 1, 1, 2, 1, 0, 0, 0, 0, 1, 1, 0, 0),
                (3, "Proj.Sum.MAIN", "thm", 1, 2, 2, 0, 1, 0, 1, 0, 1, 1, 0, 0),
                (4, "Proj.Other1.main", "thm", 1, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0),
                (5, "Proj.Other2.main", "thm", 1, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0),
                (6, "Proj.PMon.FLOne.flAt_one", "thm", 1, 2, 2, 0, 1, 0, 1, 0, 1, 0, 0, 0),
                (7, "Proj.Hub", "thm", 1, 2, 2, 25, 25, 25, 0, 0, 1, 1, 0, 0),
            ]
            # 25 deps & 25 dependents on Proj.Hub to test type-deps truncation & limit=0 removal of [:20]
            for idx in range(100, 125):
                decl_rows.append((idx, f"Proj.Dep{idx}", "def", 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0))
            for idx in range(200, 225):
                decl_rows.append((idx, f"Proj.Caller{idx}", "thm", 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0))

            conn.executemany("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NULL,NULL)", decl_rows)
            edges = [(1, 2, 1), (3, 1, 2), (6, 2, 2)]
            edges.extend((7, idx, 1) for idx in range(100, 125))
            edges.extend((idx, 7, 2) for idx in range(200, 225))
            conn.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
            conn.execute("INSERT INTO roots VALUES (0, 'Proj.Sum.MAIN', 3, 'G')")
            conn.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '0', 5)")
            dom_rows = [(3, None, 0, 5), (7, 3, 1, 10)] + [(idx, 7, 2, 1) for idx in range(200, 225)]
            conn.executemany("INSERT INTO dom VALUES (0, ?, ?, ?, ?)", dom_rows)
            dm_rows = [(r[0], "Proj.Mod", "leanre_db:exact") for r in decl_rows]
            conn.executemany("INSERT INTO decl_module VALUES (?,?,?,NULL)", dm_rows)
            conn.commit()

            # 1. Exact-case-first & partial-prefix resolution
            self.assertEqual(kernel._resolve_decl_id(conn, "zFRDirichlet")[1], "Proj.ZeroFree.zFRDirichlet")
            self.assertEqual(kernel._resolve_decl_id(conn, "ZFRDirichlet")[1], "Proj.ZeroFree.ZFRDirichlet")
            self.assertEqual(kernel._resolve_decl_id(conn, "MAIN")[1], "Proj.Sum.MAIN")
            self.assertEqual(kernel._resolve_decl_id(conn, "Proj.PMon.flAt_one")[1], "Proj.PMon.FLOne.flAt_one")
            # Case-insensitive fallback still resolves unique miss in exact case
            self.assertEqual(kernel._resolve_decl_id(conn, "zfrdirichlet") if False else kernel._resolve_decl_id(conn, "flat_one")[1], "Proj.PMon.FLOne.flAt_one")
            conn.close()

            # 2. stats --continue-on-error (partial + all-missing empty-table safety)
            with self.assertRaises(LookupError):
                kernel.stats_decls(kdb, ["zFRDirichlet", "MissingSym"])
            st = kernel.stats_decls(kdb, ["zFRDirichlet", "MissingSym", "main"], continue_on_error=True)
            self.assertEqual(st["errors_count"], 2)
            self.assertEqual([d["name"] for d in st["decls"]], ["Proj.ZeroFree.zFRDirichlet"])
            self.assertIn("Unresolved targets (2):", kernel.format_stats_text(st))
            st_empty = kernel.stats_decls(kdb, ["Missing1", "Missing2"], continue_on_error=True)
            self.assertIn("Unresolved targets (2):", kernel.format_stats_text(st_empty))
            self.assertIn("Unresolved targets (2):", kernel.format_stats_text(st_empty, table=True))
            self.assertEqual(kernel.main(["stats", "zFRDirichlet", "MissingSym", "--kernel-db", kdb, "--continue-on-error"]), 0)
            self.assertEqual(kernel.main(["stats", "Missing1", "--kernel-db", kdb, "--continue-on-error"]), 1)

            # 3. callers batch + --continue-on-error
            cl_batch = kernel.callers_decls(kdb, ["ZFRDirichlet", "MissingSym", "zFRDirichlet"], depth=1, continue_on_error=True)
            self.assertEqual(cl_batch["schema"], "leanre.kernel.callers_batch/1")
            self.assertEqual(len(cl_batch["targets"]), 2)
            self.assertEqual(cl_batch["errors_count"], 1)
            self.assertIn("Unresolved targets (1):", kernel.format_callers_text(cl_batch))
            cl_single_err = kernel.callers_decl(kdb, "MissingSym", continue_on_error=True)
            self.assertEqual(cl_single_err["errors_count"], 1)
            self.assertIn("Unresolved targets (1):", kernel.format_callers_text(cl_single_err))
            self.assertEqual(kernel.main(["callers", "ZFRDirichlet", "MissingSym", "--kernel-db", kdb, "--continue-on-error", "--json"]), 0)
            self.assertEqual(kernel.main(["callers", "Missing1", "Missing2", "--kernel-db", kdb, "--continue-on-error"]), 1)

            # 4. type-deps truncation notices + no [:20] cap when limit=0
            td_trunc = kernel.inspect_type_deps(kdb, "Proj.Hub", limit=5)
            self.assertTrue(td_trunc["truncated"])
            self.assertEqual(td_trunc["total"], 25)
            self.assertTrue(td_trunc["type_deps_truncated"])
            self.assertTrue(td_trunc["dependents_truncated"])
            self.assertTrue(td_trunc["dominators"]["children_truncated"])
            txt_trunc = kernel.format_type_deps_text(td_trunc)
            self.assertIn("showing 5 of 25; pass --limit 0 for all", txt_trunc)

            td_all = kernel.inspect_type_deps(kdb, "Proj.Hub", limit=0)
            self.assertFalse(td_all["truncated"])
            self.assertEqual(len(td_all["dependents"]), 25)
            self.assertEqual(len(td_all["dominators"]["children"]), 25)
            txt_all = kernel.format_type_deps_text(td_all)
            self.assertNotIn("pass --limit 0 for all", txt_all)
            self.assertIn("Proj.Caller224", txt_all)

    def test_hygiene_hyg01_to_hyg08_synthetic(self):
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "k_hy5.db")
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Proj"), exist_ok=True)

            with open(os.path.join(src, "Proj", "Mod.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Proj\n\n"
                    "def InnerProp : Prop := ∀ (m : Nat) [DecidableEq m] (hm : 0 < m), Nat\n"
                    "def OuterProp : Prop := ∀ (A : Type) [Add A] (φ : Equiv (Sum A A)), InnerProp\n\n"
                    "theorem unexpDefThm : OuterProp := by\n"
                    "  intro A _ φ m _ hm\n"
                    "  exact use A φ m hm\n\n"
                    "theorem implAssumption (ha : 0 < x) : 0 < x := by\n"
                    "  intro _; trivial\n\n"
                    "theorem implPositivity (hc : 0 < y) (hpos : 0 < y) : 0 < y + 1 := by\n"
                    "  positivity\n\n"
                    "theorem forwardAt (hd : 0 < d) : Target := by\n"
                    "  first | exact @_root_.Proj.helper | (intros; apply _root_.Proj.helper <;> assumption)\n\n"
                    "theorem litDrop (O : OpenLit) : Goal := mkGoal\n\n"
                    "theorem noisyLambdas (s : Finset Nat) : Nat := by\n"
                    "  have s1 := Finset.sum_le_sum fun ρ _ => le_rfl\n"
                    "  have s2 := Set.sep fun x _ => True\n"
                    "  have s3 := Closed.of_class fun Fm _ _ => 0\n"
                    "  have f_real : Nat → Nat → Nat := fun a _ => Nat.succ a\n"
                    "  have inst1 := fun {Ω} _ _ => mkΩ\n"
                    "  exact s.sum fun _ => 0\n\n"
                    "theorem obtainCheck : Goal := by\n"
                    "  obtain ⟨e, he1, _, he3⟩ := pairSrc\n"
                    "  rcases pairSrc with ⟨a, _, b⟩\n"
                    "  obtain ⟨O', _, _, _, ζ⟩ := instExist\n"
                    "  exact combine he1 he3 a b ζ\n\n"
                    "theorem rootPair : LegA ∧ LegB := ⟨mkA, mkB⟩\n"
                    "theorem aliasPair : LegA ∧ LegB := by\n"
                    "  first | exact @_root_.Proj.rootPair | exact _root_.Proj.rootPair\n"
                    "theorem rootPairConsumer : LegA :=\n"
                    "  (@_root_.Proj.aliasPair).1\n\n"
                    "theorem nestedObtainPair : LegA ∧ (LegB ∧ LegC) := ⟨mkA, ⟨mkB, mkC⟩⟩\n"
                    "theorem nestedObtainUser : LegA ∧ LegB := by\n"
                    "  obtain ⟨hrd, ⟨τ₀⟩, -⟩ := nestedObtainPair\n"
                    "  exact ⟨hrd, τ₀⟩\n"
                    "theorem nestedObtainFull : LegC := nestedObtainPair.2.2\n\n"
                    "theorem allReadTuple : LegA ∧ LegB := ⟨mkA, mkB⟩\n"
                    "theorem allReadC1 : LegA := by\n"
                    "  obtain ⟨a, -⟩ := allReadTuple\n"
                    "  exact a\n"
                    "theorem allReadC2 : LegB := allReadTuple.2\n\n"
                    "structure FamStruct (eps : Nat) extends BaseStruct eps where\n"
                    "  csz : Nat\n\n"
                    "end Proj\n"
                )

            conn = sqlite3.connect(kdb)
            conn.executescript(
                """
                CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
                    type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
                    fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
                    live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT);
                CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT, sig_size INTEGER, n_local INTEGER);
                CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
                CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
                CREATE TABLE reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, parent INTEGER, dist INTEGER NOT NULL, PRIMARY KEY(root_id, decl_id)) WITHOUT ROWID;
                CREATE UNIQUE INDEX decls_name ON decls(name);
                CREATE INDEX edges_dst ON edges(dst, src);
                """
            )
            decls = [
                (1, "And", "inductive"),
                (2, "Proj.InnerProp", "def"),
                (3, "Proj.OuterProp", "def"),
                (4, "Proj.unexpDefThm", "thm"),
                (5, "Proj.implAssumption", "thm"),
                (6, "Proj.implPositivity", "thm"),
                (7, "Proj.forwardAt", "thm"),
                (8, "Proj.litDrop", "thm"),
                (9, "Proj.noisyLambdas", "thm"),
                (10, "Proj.obtainCheck", "thm"),
                (11, "Proj.rootPair", "thm"),
                (12, "Proj.aliasPair", "thm"),
                (13, "Proj.rootPairConsumer", "thm"),
                (14, "Proj.nestedObtainPair", "thm"),
                (15, "Proj.nestedObtainUser", "thm"),
                (16, "Proj.nestedObtainFull", "thm"),
                (17, "Proj.allReadTuple", "thm"),
                (18, "Proj.allReadC1", "thm"),
                (19, "Proj.allReadC2", "thm"),
                (20, "Proj.FamStruct", "inductive"),
                (21, "Proj.FamStruct.csz", "def"),
                (22, "Proj.FamStruct.toBaseStruct", "def"),
            ]
            conn.executemany(
                "INSERT INTO decls VALUES (?,?,?,1,2,2,0,0,0,0,0,1,0,0,0,NULL,NULL)",
                decls,
            )
            edges = [
                (3, 2, 2),   # OuterProp -> InnerProp (value)
                (4, 3, 1),   # unexpDefThm -> OuterProp (type)
                (11, 1, 1),
                (12, 11, 2),
                (12, 1, 1),
                (13, 12, 2),
                (14, 1, 1),
                (15, 14, 2),
                (16, 14, 2),
                (17, 1, 1),
                (18, 17, 2),
                (19, 17, 2),
            ]
            conn.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
            conn.executemany(
                "INSERT INTO decl_module VALUES (?,?,?,NULL)",
                [(1, None, "unmatched:external")] + [(d[0], "Proj.Mod", "leanre_db:exact") for d in decls if d[0] >= 2],
            )
            conn.commit()
            conn.close()

            # HYG-03: 2-hop DefProp + Equiv (...) binder avoids all [Inst] FPs cleanly
            r_unexp = kernel.hygiene_decls(kdb, ["Proj.unexpDefThm"], src_root=src, only="dropped")
            self.assertEqual(r_unexp["summary"]["total_findings"], 0)

            # HYG-02 & HYG-07: implicit-ctx suppressed by default, shown via --strict-binders, litDrop preserved!
            r_imp = kernel.hygiene_decls(kdb, ["Proj.implPositivity", "Proj.forwardAt", "Proj.litDrop"], src_root=src, only="dropped")
            self.assertEqual([d["name"] for d in r_imp["decls"] if d["findings"]], ["Proj.litDrop"])
            self.assertGreaterEqual(r_imp["summary"]["suppressed_counts"]["by_reason"].get("implicit_ctx_tactic", 0), 3)
            r_strict = kernel.hygiene_decls(kdb, ["Proj.implPositivity", "Proj.forwardAt", "Proj.litDrop"], src_root=src, only="dropped", strict_binders=True)
            self.assertEqual(len([d for d in r_strict["decls"] if d["findings"]]), 3)

            # HYG-03 & HYG-06: combinator/membership/instance lambdas suppressed; genuine f_real kept; binder_pos set
            r_lam = kernel.hygiene_decls(kdb, ["Proj.noisyLambdas"], src_root=src, only="dropped")
            lam_findings = r_lam["decls"][0]["findings"]
            self.assertEqual(len(lam_findings), 1)
            self.assertEqual(lam_findings[0]["kind"], "combinator_fun_wildcard")
            self.assertIn("#1", lam_findings[0]["binder_pos"])
            self.assertGreaterEqual(r_lam["summary"]["suppressed_counts"]["total"], 5)
            r_lam_noisy = kernel.hygiene_decls(kdb, ["Proj.noisyLambdas"], src_root=src, only="dropped", include_noisy=True)
            self.assertGreaterEqual(len(r_lam_noisy["decls"][0]["findings"]), 6)

            # obtain_discarded catches obtain + rcases, ignores [Inst] run ⟨O', _, _, _, ζ⟩
            r_obt = kernel.hygiene_decls(kdb, ["Proj.obtainCheck"], src_root=src, only="dropped")
            obt_findings = [f for f in r_obt["decls"][0]["findings"] if f["kind"] == "obtain_discarded"]
            self.assertEqual(len(obt_findings), 2)
            self.assertEqual([f["positions"] for f in obt_findings], [[2], [1]])

            # HYG-01 & HYG-08: @_root_. + 1-hop pure alias wrapper caught!
            r_root = kernel.hygiene_decls(kdb, ["Proj.rootPair"], src_root=src, only="tuple_unread")
            self.assertEqual(len(r_root["decls"][0]["findings"]), 1)
            self.assertEqual(r_root["decls"][0]["tuple_summary"]["unread_indices"], [1])
            self.assertEqual(r_root["decls"][0]["tuple_summary"]["unwrapped_aliases"], 1)

            # HYG-04: nested obtain ⟨hrd, ⟨τ₀⟩, -⟩ + allReadTuple (unread_indices == []) emit 0 findings
            r_h4 = kernel.hygiene_decls(kdb, ["Proj.nestedObtainPair", "Proj.allReadTuple"], src_root=src, only="tuple_unread")
            self.assertEqual(r_h4["decls"][0]["tuple_summary"]["unread_indices"], [])
            self.assertEqual(r_h4["decls"][1]["tuple_summary"]["unread_indices"], [])
            self.assertEqual(r_h4["summary"]["total_findings"], 0)

            # HYG-05: FamStruct + child projections produce 0 duplicated findings
            r_fam = kernel.hygiene_decls(kdb, ["Proj.FamStruct", "Proj.FamStruct.csz", "Proj.FamStruct.toBaseStruct"], src_root=src)
            self.assertEqual(r_fam["summary"]["total_findings"], 0)

    def test_xrepo_auto_config_discovery_and_clean_report(self):
        demo_nd = os.path.join(_REPO_ROOT, "examples", "tiny_demo", "demo.ndjson")
        demo_toml = os.path.join(_REPO_ROOT, "examples", "tiny_demo", "leanre.toml")
        if not (os.path.exists(kernel.default_binary_path()) and os.path.isfile(demo_nd) and os.path.isfile(demo_toml)):
            self.skipTest("tiny_demo fixtures unavailable")
        with tempfile.TemporaryDirectory() as td:
            out_dir = os.path.join(td, "demo_out")
            rep_path = os.path.join(td, "demo_report.json")
            # Call WITHOUT roots or src_dir: auto-discovers examples/tiny_demo/leanre.toml
            rep = kernel.run_pipeline(
                input_path=demo_nd,
                out_dir=out_dir,
                report_path=rep_path,
                threads=2,
                workers=1,
                oracle_random=10,
                oracle_top=5,
                auto_build=False,
                verbose=False,
            )
            self.assertEqual(rep["k4_live_dead_and_axioms"]["union"]["live"], 10)
            self.assertEqual(rep["k4_live_dead_and_axioms"]["union"]["dead"], 7)
            self.assertNotIn("is_full_solution", rep)
            self.assertNotIn("matches_expected_solution", rep["k1_integrity"])
            self.assertNotIn("con_leche_reference", rep["k2_counts"]["reconciliation"])
            self.assertNotIn("nanoda_reference_nasqret", rep["k2_counts"]["reconciliation"])
            self.assertTrue(rep["k2_counts"]["reconciliation"]["formula_check"])
            self.assertNotIn("dyadic_smallloop_disambiguation", rep["k5_dominators_and_taint"]["taint_summary"])
            by_cls = rep["k5_dominators_and_taint"]["taint_summary"]["by_class"]
            for rh_only_tag in ("CutCptCopy", "kexactB", "kcopy", "slow_con_leche", "lean4lean_timeout", "addDecl"):
                self.assertNotIn(rh_only_tag, by_cls)
            for gen_tag in ("ofReduceBool", "ofReduceNat", "trustCompiler", "sorryAx", "decide_kernel_pattern"):
                self.assertIn(gen_tag, by_cls)

            # Also verify CLI `--config` flag on an isolated copy of demo.ndjson
            iso_dir = os.path.join(td, "iso")
            os.makedirs(iso_dir, exist_ok=True)
            iso_nd = os.path.join(iso_dir, "other.ndjson")
            shutil.copy2(demo_nd, iso_nd)
            iso_out = os.path.join(td, "iso_out")
            iso_rep = os.path.join(td, "iso_report.json")
            rc = kernel.main([
                "extract", "--input", iso_nd, "--out-dir", iso_out, "--config", demo_toml,
                "--report", iso_rep, "--threads", "2", "--workers", "1", "--oracle-random", "10", "--oracle-top", "5",
            ])
            self.assertEqual(rc, 0)
            with open(iso_rep, "r", encoding="utf-8") as f:
                loaded_rep = json.load(f)
            self.assertEqual(loaded_rep["k4_live_dead_and_axioms"]["union"]["live"], 10)
            self.assertEqual(loaded_rep["k4_live_dead_and_axioms"]["union"]["dead"], 7)


class TestKernelLoop6HygieneAndCallers(unittest.TestCase):
    """Regression suite for Loop 6 kernel fixes: conjunct_true_slot, Closed.and/Ev.and
    projection chains, 5-component ∃-destructuring, R5HIR-01/02, .mk callers, and live mask legend.
    """

    def test_conjunct_true_slot_and_chain_existential_and_hironaka_hygiene(self):
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "k_hy6.db")
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Proj"), exist_ok=True)

            with open(os.path.join(src, "Proj", "Loop6.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Proj\n\n"
                    "def PropWithMidTrue (x : Nat) : Prop :=\n"
                    "  (0 < x) ∧ True ∧ (x < 10)\n\n"
                    "abbrev AbbrevNestedTrue : Prop :=\n"
                    "  (0 < 1) ∧ (True ∧ (1 < 2))\n\n"
                    "def HarmlessFunTrue : Nat → Prop :=\n"
                    "  fun _ => True\n\n"
                    "def ClosedFunTrue : Prop :=\n"
                    "  Closed (fun _ => True)\n\n"
                    "def BareTrue : Prop := True\n\n"
                    "abbrev UnivPolyRule.{u} : Type (u + 1) :=\n"
                    "  ∀ (k : Type u) [Field k] [CharZero k] (n : Nat), Goal k n\n\n"
                    "def WrapperRule : Prop := UnivPolyRule.{0}\n\n"
                    "theorem polyThm : WrapperRule := by\n"
                    "  intro k _ _ n\n"
                    "  exact mkGoal k n\n\n"
                    "theorem topUnivTrivial1 : Prop := by\n"
                    "  intro x\n"
                    "  refine ⟨⊤, trivial, rfl⟩\n\n"
                    "theorem topUnivTrivial2 : Prop := by\n"
                    "  exact (show x ∈ (⊤ : Opens) from trivial)\n\n"
                    "theorem setUnivTrivial : Prop := by\n"
                    "  refine ⟨Set.univ, _, isOpen_univ, trivial⟩\n\n"
                    "theorem genuineHopfTrivial : Prop := by\n"
                    "  obtain ⟨a, b⟩ := hb trivial\n"
                    "  exact a\n\n"
                    "theorem genuineInScopeTrivial : Prop := by\n"
                    "  refine ⟨h1, h2, trivial⟩\n\n"
                    "theorem hypsExist : A ∧ B ∧ C ∧ (∃ hL : T, P hL) := ⟨mkA, mkB, mkC, ⟨mkL, mkP⟩⟩\n\n"
                    "theorem hypsExistCaller5 : Goal := by\n"
                    "  obtain ⟨a, -, -, hL', hN⟩ := hypsExist\n"
                    "  exact use a hN\n\n"
                    "theorem hypsExistCallerOther : Goal := by\n"
                    "  obtain ⟨_, b, c, _⟩ := hypsExist\n"
                    "  exact pair b c\n\n"
                    "theorem hypsExistRcases5 : Goal := by\n"
                    "  rcases hypsExist with ⟨a, -, -, hL', hN⟩\n"
                    "  exact use a hN\n\n"
                    "theorem signsClosed : Closed C fun Fm _ => CondA Fm ∧ CondB Fm := mkSigns\n"
                    "theorem onesClosed : Closed C fun Fm _ => Cond1 Fm ∧ Cond2 Fm ∧ Cond3 Fm := mkOnes\n"
                    "theorem allUsedClosed : Closed C fun Fm _ => Used1 Fm ∧ Used2 Fm := mkUsed\n\n"
                    "theorem consumerClosed : Closed C fun Fm _ => Goal Fm :=\n"
                    "  (((allUsedClosed.and signsClosed).and onesClosed).and hRest).imp fun Fm _ _ h =>\n"
                    "    combine h.1.1.1.1 h.1.1.1.2 h.1.1.2.1 h.1.2.2.2 h.2\n\n"
                    "theorem consumerEv (x0 : Nat) : Ev Goal := by\n"
                    "  obtain ⟨x1, h⟩ := (allUsedClosed.and signsClosed).and onesClosed\n"
                    "  exact ⟨x1, fun x hx i => combine (h x hx i).1.1.1 (h x hx i).1.1.2 (h x hx i).1.2.1 (h x hx i).2.2.2⟩\n\n"
                    "end Proj\n"
                )

            conn = sqlite3.connect(kdb)
            conn.executescript(
                """
                CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
                    type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
                    fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
                    live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT);
                CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT, sig_size INTEGER, n_local INTEGER);
                CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
                CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
                CREATE TABLE reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, parent INTEGER, dist INTEGER NOT NULL, PRIMARY KEY(root_id, decl_id)) WITHOUT ROWID;
                CREATE UNIQUE INDEX decls_name ON decls(name);
                CREATE INDEX edges_dst ON edges(dst, src);
                """
            )
            decl_rows = [
                (1, "True", "inductive"),
                (2, "And", "inductive"),
                (10, "Proj.PropWithMidTrue", "def"),
                (11, "Proj.AbbrevNestedTrue", "def"),
                (12, "Proj.HarmlessFunTrue", "def"),
                (13, "Proj.ClosedFunTrue", "def"),
                (14, "Proj.BareTrue", "def"),
                (20, "Proj.UnivPolyRule", "def"),
                (21, "Proj.WrapperRule", "def"),
                (22, "Proj.polyThm", "thm"),
                (30, "Proj.topUnivTrivial1", "thm"),
                (31, "Proj.topUnivTrivial2", "thm"),
                (32, "Proj.setUnivTrivial", "thm"),
                (33, "Proj.genuineHopfTrivial", "thm"),
                (34, "Proj.genuineInScopeTrivial", "thm"),
                (40, "Proj.hypsExist", "thm"),
                (41, "Proj.hypsExistCaller5", "thm"),
                (42, "Proj.hypsExistCallerOther", "thm"),
                (43, "Proj.hypsExistRcases5", "thm"),
                (50, "Proj.signsClosed", "thm"),
                (51, "Proj.onesClosed", "thm"),
                (52, "Proj.allUsedClosed", "thm"),
                (53, "Proj.consumerClosed", "thm"),
                (54, "Proj.consumerEv", "thm"),
            ]
            conn.executemany(
                "INSERT INTO decls VALUES (?,?,?,1,2,2,0,0,0,0,0,1,0,0,0,NULL,NULL)",
                decl_rows,
            )
            edges = [
                (10, 1, 2),
                (11, 1, 2),
                (21, 20, 2),
                (22, 21, 1),
                (40, 2, 1),
                (41, 40, 2),
                (42, 40, 2),
                (43, 40, 2),
                (50, 2, 1),
                (51, 2, 1),
                (52, 2, 1),
                (53, 50, 2),
                (53, 51, 2),
                (53, 52, 2),
                (54, 50, 2),
                (54, 51, 2),
                (54, 52, 2),
            ]
            conn.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
            conn.executemany(
                "INSERT INTO decl_module VALUES (?,?,?,NULL)",
                [(1, None, "unmatched:external"), (2, None, "unmatched:external")]
                + [(d[0], "Proj.Loop6", "leanre_db:exact") for d in decl_rows if d[0] >= 10],
            )
            conn.commit()
            conn.close()

            # 1. conjunct_true_slot vs harmless fun _ => True / BareTrue
            r_ct = kernel.hygiene_decls(
                kdb,
                ["Proj.PropWithMidTrue", "Proj.AbbrevNestedTrue", "Proj.HarmlessFunTrue", "Proj.ClosedFunTrue", "Proj.BareTrue"],
                src_root=src,
                only="true_slot",
            )
            by_ct = {d["name"]: d["findings"] for d in r_ct["decls"]}
            self.assertEqual([f["kind"] for f in by_ct["Proj.PropWithMidTrue"]], ["conjunct_true_slot"])
            self.assertEqual(by_ct["Proj.PropWithMidTrue"][0]["conjunct_index"], 1)
            self.assertEqual([f["kind"] for f in by_ct["Proj.AbbrevNestedTrue"]], ["conjunct_true_slot"])
            self.assertEqual(by_ct["Proj.AbbrevNestedTrue"][0]["conjunct_index"], 1)
            self.assertEqual(by_ct["Proj.HarmlessFunTrue"], [])
            self.assertEqual(by_ct["Proj.ClosedFunTrue"], [])
            self.assertEqual([f["kind"] for f in by_ct["Proj.BareTrue"]], ["true_def_body"])

            # 2. R5HIR-01: 2-hop def -> universe-polymorphic abbrev.{0} suppresses [Inst] intro wildcards
            r_poly = kernel.hygiene_decls(kdb, ["Proj.polyThm"], src_root=src, only="dropped")
            self.assertEqual(r_poly["summary"]["total_findings"], 0)

            # 3. R5HIR-02: x ∈ ⊤ / Set.univ trivial suppressed as noisy, genuine trivial kept visible
            r_triv = kernel.hygiene_decls(
                kdb,
                ["Proj.topUnivTrivial1", "Proj.topUnivTrivial2", "Proj.setUnivTrivial", "Proj.genuineHopfTrivial", "Proj.genuineInScopeTrivial"],
                src_root=src,
                only="true_slot",
            )
            by_tv = {d["name"]: d["findings"] for d in r_triv["decls"]}
            self.assertEqual(by_tv["Proj.topUnivTrivial1"], [])
            self.assertEqual(by_tv["Proj.topUnivTrivial2"], [])
            self.assertEqual(by_tv["Proj.setUnivTrivial"], [])
            self.assertEqual([f["kind"] for f in by_tv["Proj.genuineHopfTrivial"]], ["passed_trivial_arg"])
            self.assertEqual([f["kind"] for f in by_tv["Proj.genuineInScopeTrivial"]], ["passed_trivial_arg"])
            self.assertEqual(r_triv["summary"]["suppressed_counts"]["by_reason"].get("top_univ_membership"), 3)
            r_triv_noisy = kernel.hygiene_decls(kdb, ["Proj.topUnivTrivial2"], src_root=src, only="true_slot", include_noisy=True)
            self.assertEqual(r_triv_noisy["decls"][0]["findings"][0]["noise_tier"], "noisy")

            # 4. 5-component ∃-destructuring (obtain + rcases)
            r_ex5 = kernel.hygiene_decls(kdb, ["Proj.hypsExist"], src_root=src, only="tuple_unread")
            self.assertEqual(r_ex5["summary"]["total_findings"], 0)
            self.assertEqual(r_ex5["decls"][0]["tuple_summary"]["unread_indices"], [])

            # 5. Closed.and / Ev.and projection chains (both producer-side & consumer-side)
            r_and_prod = kernel.hygiene_decls(
                kdb, ["Proj.signsClosed", "Proj.onesClosed", "Proj.allUsedClosed"], src_root=src, only="tuple_unread"
            )
            by_ap = {d["name"]: d for d in r_and_prod["decls"]}
            self.assertEqual(by_ap["Proj.signsClosed"]["tuple_summary"]["unread_indices"], [1])
            self.assertEqual(by_ap["Proj.onesClosed"]["tuple_summary"]["unread_indices"], [0, 1])
            self.assertEqual(by_ap["Proj.allUsedClosed"]["tuple_summary"]["unread_indices"], [])
            self.assertEqual(len(by_ap["Proj.allUsedClosed"]["findings"]), 0)

            r_and_cons = kernel.hygiene_decls(
                kdb, ["Proj.consumerClosed", "Proj.consumerEv"], src_root=src, only="tuple_unread"
            )
            for cd in r_and_cons["decls"]:
                self.assertEqual(
                    {f["leaf_decl"]: f["unread_indices"] for f in cd["findings"]},
                    {"Proj.signsClosed": [1], "Proj.onesClosed": [0, 1]},
                )

    def test_callers_mk_resolution_and_stats_live_legend(self):
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "k_mk.db")
            conn = sqlite3.connect(kdb)
            conn.executescript(
                """
                CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
                    type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
                    fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
                    live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT);
                CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL,
                    sighash TEXT, sighash_anon TEXT, sig_size INTEGER, n_local INTEGER);
                CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
                CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
                CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
                CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
                CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
                CREATE UNIQUE INDEX decls_name ON decls(name);
                CREATE UNIQUE INDEX consts_name ON consts(name);
                CREATE INDEX edges_dst ON edges(dst, src);
                """
            )
            conn.executemany(
                "INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,NULL,NULL)",
                [
                    (1, "Proj.MyStruct", "inductive", 3, 2, 0, 2, 0, 0, 0, 0, 3, 1, 0, 0),
                    (2, "Proj.Wrapper.mk", "def", 1, 2, 2, 1, 1, 0, 1, 0, 1, 0, 0, 0),
                    (3, "Proj.RootOne", "thm", 1, 2, 4, 0, 2, 0, 2, 0, 1, 1, 0, 0),
                    (4, "Proj.RootTwo", "thm", 1, 2, 4, 0, 1, 0, 1, 0, 2, 1, 0, 0),
                ],
            )
            conn.executemany(
                "INSERT INTO consts VALUES (?,?,?,?,?,NULL,NULL,10,0)",
                [
                    (1, "Proj.MyStruct", 1, "induct", 0),
                    (2, "Proj.MyStruct.mk", 1, "ctor", 1),
                    (3, "Proj.MyStruct.rec", 1, "rec", 2),
                    (4, "Proj.Wrapper.mk", 2, "def", 0),
                ],
            )
            conn.executemany("INSERT INTO edges VALUES (?,?,?)", [(2, 1, 2), (3, 1, 2), (3, 2, 2), (4, 1, 1)])
            conn.executemany("INSERT INTO roots VALUES (?,?,?,?)", [(0, "Proj.RootOne", 3, "G1"), (1, "Proj.RootTwo", 4, "G2")])
            conn.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '0,1', 4)")
            conn.executemany("INSERT INTO decl_module VALUES (?, 'Proj.Mod', 'leanre_db:exact', NULL)", [(1,), (2,), (3,), (4,)])
            conn.commit()
            conn.close()

            # 1. `.mk` folded constructor does NOT silently return parent inductive's callers
            for q in ("Proj.MyStruct.mk", "MyStruct.mk"):
                with self.assertRaises(LookupError) as ctx:
                    kernel.callers_decl(kdb, q)
                self.assertIn("folded into 'Proj.MyStruct'", str(ctx.exception))
                self.assertIn("bundles --instantiations Proj.MyStruct", str(ctx.exception))
            self.assertEqual(kernel.main(["callers", "Proj.MyStruct.mk", "--kernel-db", kdb]), 1)

            # 2. Absent `.mk` does NOT silently strip `.mk`
            with self.assertRaises(LookupError) as ctx2:
                kernel.callers_decl(kdb, "Proj.MissingStruct.mk")
            self.assertIn("Proj.MissingStruct.mk", str(ctx2.exception))

            # 3. Standalone `def Wrapper.mk` resolves normally
            cl_wrap = kernel.callers_decl(kdb, "Proj.Wrapper.mk", depth=1)
            self.assertEqual(cl_wrap["center"]["name"], "Proj.Wrapper.mk")
            self.assertEqual([c["name"] for c in cl_wrap["hops"][0]["groups"][0]["callers"]], ["Proj.RootOne"])

            # 4. Batch `--continue-on-error` keeps valid targets while reporting `.mk` error
            cl_batch = kernel.callers_decls(kdb, ["Proj.MyStruct.mk", "Proj.MyStruct"], depth=1, continue_on_error=True)
            self.assertEqual(cl_batch["errors_count"], 1)
            self.assertEqual([t["center"]["name"] for t in cl_batch["targets"]], ["Proj.MyStruct"])

            # 5. `slice_decl` still resolves constructor constant cleanly (backward compatibility)
            sl = kernel.slice_decl(kdb, "Proj.MyStruct.mk", direction="forward", depth=1)
            self.assertEqual(sl["center"]["name"], "Proj.MyStruct")
            self.assertEqual(sl["center"]["resolved_from_const"], "Proj.MyStruct.mk")

            # 6. `kernel stats` live bitmask legend (plain text, markdown table, JSON, and --help)
            st = kernel.stats_decls(kdb, ["Proj.MyStruct", "Proj.Wrapper.mk"])
            self.assertEqual(st["decls"][0]["live_roots"], ["Proj.RootOne", "Proj.RootTwo"])
            self.assertEqual(len(st["live_roots_legend"]), 2)
            txt = kernel.format_stats_text(st)
            self.assertIn("live bitmask (0=dead, 3=all 2 roots): 1=Proj.RootOne, 2=Proj.RootTwo", txt)
            tbl = kernel.format_stats_text(st, table=True)
            self.assertIn("live bitmask (0=dead, 3=all 2 roots): 1=Proj.RootOne, 2=Proj.RootTwo", tbl)

            import contextlib, io
            help_buf = io.StringIO()
            with contextlib.redirect_stdout(help_buf), self.assertRaises(SystemExit) as sys_ex:
                kernel.main(["stats", "--help"])
            self.assertEqual(sys_ex.exception.code, 0)
            self.assertIn("bitmask over roots", help_buf.getvalue())


class TestKernelLoop7PrecisionAndAnchors(unittest.TestCase):
    """Regression suite for Loop 7 kernel fixes: Struct.field anchors & --verify-md warnings,
    delayed obtain / choose / 14-comp tuple_unread, AllFin higher-order telescope expansion,
    non-bracketed local typeclass instances, true_slot premise/univ suppression, opt-in
    semantic flags (--semantic), and 1-hop stats alias_of hints (--with-alias).
    """

    @staticmethod
    def _create_mini_db(db_path: str, decl_rows: list, edges: list, dm_rows: list, consts: list = ()):
        conn = sqlite3.connect(db_path)
        conn.executescript(
            """
            CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
                type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
                fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
                live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                sighash TEXT, sighash_anon TEXT);
            CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL,
                sighash TEXT, sighash_anon TEXT, sig_size INTEGER, n_local INTEGER);
            CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
            CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
            CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
            CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
            CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
            CREATE UNIQUE INDEX decls_name ON decls(name);
            CREATE INDEX edges_dst ON edges(dst, src);
            """
        )
        conn.executemany(
            "INSERT INTO decls VALUES (?,?,?,1,2,?,?,?,0,?,0,1,0,0,0,NULL,NULL)",
            decl_rows,
        )
        conn.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '', 0)")
        conn.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
        conn.executemany("INSERT INTO decl_module VALUES (?,?,?,NULL)", dm_rows)
        if consts:
            conn.executemany("INSERT INTO consts VALUES (?,?,?,?,?,NULL,NULL,10,0)", consts)
        conn.commit()
        conn.close()

    def test_struct_field_anchors_and_verify_md_structure_warning(self):
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "k_anc7.db")
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Proj"), exist_ok=True)
            lean_file = os.path.join(src, "Proj", "StructMod.lean")
            with open(lean_file, "w", encoding="utf-8") as f:
                f.write(
                    "namespace Proj\n\n"
                    "structure Size₂ (n : Nat) where\n"
                    "  /-- docstring -/\n"
                    "  base_bound : 0 ≤ n\n"
                    "  gam_eq : n = n\n\n"
                    "inductive BranchTag where\n"
                    "  | leftCase\n"
                    "  | rightCase\n\n"
                    "end Proj\n"
                )
            decls = [
                (1, "Proj.Size₂", "inductive", 2, 0, 0, 0),
                (2, "Proj.Size₂.base_bound", "thm", 2, 1, 0, 1),
                (3, "Proj.Size₂.gam_eq", "thm", 2, 1, 0, 1),
                (4, "Proj.BranchTag", "inductive", 2, 0, 0, 0),
                (5, "Proj.BranchTag.rightCase", "ctor", 2, 0, 0, 0),
            ]
            dm = [(d[0], "Proj.StructMod", "leanre_db:exact") for d in decls]
            self._create_mini_db(kdb, decls, [], dm)

            res = kernel.anchor_decls(
                kdb,
                ["Proj.Size₂.base_bound", "Proj.Size₂.gam_eq", "Proj.BranchTag.rightCase"],
                src_root=src,
            )
            self.assertTrue(res["all_passed"])
            by_nm = {d["name"]: d for d in res["decls"]}
            self.assertEqual(by_nm["Proj.Size₂.base_bound"]["line_no"], 5)
            self.assertEqual(by_nm["Proj.Size₂.base_bound"]["match_kind"], "field")
            self.assertEqual(by_nm["Proj.Size₂.base_bound"]["parent_line"], 3)
            self.assertEqual(by_nm["Proj.Size₂.gam_eq"]["line_no"], 6)
            self.assertEqual(by_nm["Proj.BranchTag.rightCase"]["line_no"], 10)
            self.assertEqual(by_nm["Proj.BranchTag.rightCase"]["match_kind"], "ctor")

            st = kernel.stats_decls(kdb, ["Proj.Size₂.gam_eq"], src_root=src)
            self.assertEqual(st["decls"][0]["anchor"], "src/Proj/StructMod.lean:6")

            md_path = os.path.join(td, "note.md")
            with open(md_path, "w", encoding="utf-8") as mf:
                mf.write(
                    "See [field link](https://github.com/o/r/blob/main/src/Proj/StructMod.lean#L3) for `gam_eq`.\n"
                    "Exact [field link ok](https://github.com/o/r/blob/main/src/Proj/StructMod.lean#L6) for `gam_eq`.\n"
                )
            vmd = kernel.anchor_decls(kdb, [], src_root=src, verify_md=[md_path])
            self.assertTrue(vmd["all_passed"])
            self.assertEqual(vmd["verify_md"]["warnings_count"], 1)
            wrn = vmd["verify_md"]["files"][0]["warnings"][0]
            self.assertEqual(wrn["kind"], "structure_header_for_field")
            self.assertEqual(wrn["expected_line"], 6)
            self.assertIn("warning(s)", kernel.format_anchor_text(vmd))

    def test_tuple_unread_delayed_obtain_choose_and_wide14(self):
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "k_tup7.db")
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Proj"), exist_ok=True)
            with open(os.path.join(src, "Proj", "Tup7.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Proj\n\n"
                    "theorem delayedProd (a : Nat) : 0 < a → ∃ x0 : Nat, ∀ n, x0 ≤ n →\n"
                    "    (0 < n) ∧ (1 < n) ∧ (a < n) ∧ (2 < n) := by\n"
                    "  intro _; exact ⟨3, fun _ _ => sorry⟩\n\n"
                    "theorem delayedCaller (a b : Nat) (ha : 0 < a) : 0 < 1 := by\n"
                    "  obtain ⟨x0, hx⟩ := delayedProd a ha\n"
                    "  have m := x0 + b\n"
                    "  obtain ⟨p1, p2, p3, p4⟩ := hx m le_rfl\n"
                    "  exact use4 p1 p2 p3 p4\n\n"
                    "theorem nestedExProd (n : Nat) : 1 ≤ n → ∃ c1 : Nat, ∀ c0 : Nat, c1 ≤ c0 →\n"
                    "    ∃ Y : ∀ r : Nat, Nat → Nat, P0 Y ∧ P1 Y ∧ P2 Y ∧ P3 Y ∧ P4 Y := by\n"
                    "  intro _; exact ⟨1, fun _ _ => ⟨fun _ x => x, sorry⟩⟩\n\n"
                    "theorem chooseCaller (n : Nat) (hn : 1 ≤ n) : Goal := by\n"
                    "  obtain ⟨c1, hc1⟩ := nestedExProd n hn\n"
                    "  have hY' := fun x : Nat => hc1 (x + c1) (by omega)\n"
                    "  choose Y' q0 q1 q2 q3 q4 using hY'\n"
                    "  exact combine5 (q0 0) (q1 0) (q2 0) (q3 0) (q4 0)\n\n"
                    "theorem nestedExUnread (n : Nat) : 1 ≤ n → ∃ c1 : Nat, ∀ c0 : Nat, c1 ≤ c0 →\n"
                    "    ∃ Y : ∀ r : Nat, Nat → Nat, Q0 Y ∧ Q1 Y ∧ Q2 Y := by\n"
                    "  intro _; exact ⟨1, fun _ _ => ⟨fun _ x => x, sorry⟩⟩\n\n"
                    "theorem chooseUnreadCaller (n : Nat) (hn : 1 ≤ n) : Goal := by\n"
                    "  obtain ⟨c1, hc1⟩ := nestedExUnread n hn\n"
                    "  choose Y q0 _ q2 using hc1 n le_rfl\n"
                    "  exact pair (q0) (q2)\n\n"
                    "theorem wideEx14 : ∃ (a b : Nat), R0 ∧ R1 ∧ R2 ∧ R3 ∧ R4 ∧ R5 ∧\n"
                    "    R6 ∧ R7 ∧ R8 ∧ R9 ∧ R10 ∧ R11 := by\n"
                    "  exact ⟨0, 0, sorry⟩\n\n"
                    "theorem wideEx14Caller : Goal := by\n"
                    "  obtain ⟨a, b, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := wideEx14\n"
                    "  exact use12 a b r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11\n\n"
                    "end Proj\n"
                )
            decls = [
                (1, "And", "inductive", 2, 0, 0, 0),
                (10, "Proj.delayedProd", "thm", 2, 2, 0, 1),
                (11, "Proj.delayedCaller", "thm", 2, 2, 0, 1),
                (12, "Proj.nestedExProd", "thm", 2, 2, 0, 1),
                (13, "Proj.chooseCaller", "thm", 2, 2, 0, 1),
                (14, "Proj.nestedExUnread", "thm", 2, 2, 0, 1),
                (15, "Proj.chooseUnreadCaller", "thm", 2, 2, 0, 1),
                (16, "Proj.wideEx14", "thm", 2, 2, 0, 1),
                (17, "Proj.wideEx14Caller", "thm", 2, 2, 0, 1),
            ]
            edges = [
                (10, 1, 1), (11, 10, 2),
                (12, 1, 1), (13, 12, 2),
                (14, 1, 1), (15, 14, 2),
                (16, 1, 1), (17, 16, 2),
            ]
            dm = [(1, None, "unmatched:external")] + [(d[0], "Proj.Tup7", "leanre_db:exact") for d in decls[1:]]
            self._create_mini_db(kdb, decls, edges, dm)

            hy = kernel.hygiene_decls(
                kdb,
                ["Proj.delayedProd", "Proj.nestedExProd", "Proj.nestedExUnread", "Proj.wideEx14"],
                src_root=src,
                only="tuple_unread",
            )
            by_nm = {d["name"]: d for d in hy["decls"]}
            self.assertEqual(by_nm["Proj.delayedProd"]["findings"], [])
            self.assertEqual(by_nm["Proj.delayedProd"]["tuple_summary"]["unread_indices"], [])
            self.assertEqual(by_nm["Proj.nestedExProd"]["findings"], [])
            self.assertEqual(by_nm["Proj.nestedExProd"]["tuple_summary"]["exists_depth"], 2)
            self.assertEqual(by_nm["Proj.nestedExProd"]["tuple_summary"]["unread_indices"], [])
            self.assertEqual(by_nm["Proj.wideEx14"]["findings"], [])
            self.assertEqual(by_nm["Proj.wideEx14"]["tuple_summary"]["exists_depth"], 2)
            self.assertEqual(by_nm["Proj.wideEx14"]["tuple_summary"]["arity"], 12)
            self.assertEqual(by_nm["Proj.wideEx14"]["tuple_summary"]["unread_indices"], [])
            # Negative control: discarded leg inside `choose` must still trigger
            self.assertEqual(len(by_nm["Proj.nestedExUnread"]["findings"]), 1)
            self.assertEqual(by_nm["Proj.nestedExUnread"]["tuple_summary"]["unread_indices"], [1])

    def test_allfin_local_classes_and_true_noise(self):
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "k_hy7.db")
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Proj"), exist_ok=True)
            with open(os.path.join(src, "Proj", "Hy7.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Proj\n\n"
                    "class CustomLocalProp (x : Nat) : Prop where\n"
                    "  valid : x = x\n\n"
                    "structure CustomNonClass (x : Nat) : Prop where\n"
                    "  ok : 0 ≤ x\n\n"
                    "def AllFin (Q : ∀ (R : Type) [CommRing R] (F : Nat), Prop) : Prop :=\n"
                    "  ∀ (R : Type) [CommRing R] (F : Nat), Q R F\n\n"
                    "def Stein (F : Nat) : Prop := F = F\n"
                    "def Hopf (F : Nat) (b : Prop) : Prop := b → F = F\n\n"
                    "def HopfLeSt : Prop := AllFin fun R _ F ↦ ∀ g : Nat, Stein F → Hopf F True → g = g\n\n"
                    "theorem hopfThm : Stein 0 → HopfLeSt := by\n"
                    "  intro _ R _ F g hSt hH\n"
                    "  have _ := hSt\n"
                    "  exact mkProof R F g hH\n\n"
                    "theorem classBinders (n : Nat) (hv : ∀ k, Subsingleton (List k))\n"
                    "    (hc : CustomLocalProp n) (hbad : CustomNonClass n) : 0 = 0 := by\n"
                    "  intro\n"
                    "  exact rfl\n\n"
                    "theorem univDisjoint (U : Set Nat) : SupportedIn U Set.univ := by\n"
                    "  intro hU\n"
                    "  exact fun hx => Set.disjoint_left.1 hU hx trivial\n\n"
                    "theorem actPremise (hH : True → Nat ∧ Nat) : Nat := by\n"
                    "  obtain ⟨a, _⟩ := hH trivial\n"
                    "  exact a\n\n"
                    "end Proj\n"
                )
            decls = [
                (1, "Subsingleton", "inductive", 1, 0, 0, 0),
                (2, "True", "inductive", 1, 0, 0, 0),
                (10, "Proj.CustomLocalProp", "inductive", 1, 0, 0, 0),
                (11, "Proj.CustomNonClass", "inductive", 1, 0, 0, 0),
                (12, "Proj.AllFin", "def", 2, 2, 0, 0),
                (13, "Proj.Stein", "def", 2, 2, 0, 0),
                (14, "Proj.Hopf", "def", 2, 2, 0, 0),
                (15, "Proj.HopfLeSt", "def", 2, 2, 0, 0),
                (16, "Proj.hopfThm", "thm", 2, 2, 0, 1),
                (17, "Proj.classBinders", "thm", 2, 2, 0, 1),
                (18, "Proj.univDisjoint", "thm", 2, 2, 0, 1),
                (19, "Proj.actPremise", "thm", 2, 2, 0, 1),
            ]
            edges = [
                (15, 12, 2), (16, 15, 1),
                (17, 1, 1), (17, 10, 1), (17, 11, 1),
                (18, 2, 2), (19, 2, 3),
            ]
            dm = [(1, None, "unmatched:external"), (2, None, "unmatched:external")] + [
                (d[0], "Proj.Hy7", "leanre_db:exact") for d in decls[2:]
            ]
            self._create_mini_db(kdb, decls, edges, dm)

            # 1. AllFin shifts avoided: only slot #0 (`Stein 0`), NOT `Stein F` or `Hopf F True`
            r_allfin = kernel.hygiene_decls(kdb, ["Proj.hopfThm"], src_root=src, only="dropped")
            f_af = r_allfin["decls"][0]["findings"]
            self.assertEqual(len(f_af), 1)
            self.assertEqual(f_af[0]["slot_index"], 0)
            self.assertIn("Stein 0", f_af[0]["param_type"])

            # 2. Local typeclass binders suppressed; non-class structure kept
            r_cls = kernel.hygiene_decls(kdb, ["Proj.classBinders"], src_root=src, only="dropped")
            f_cls = r_cls["decls"][0]["findings"]
            self.assertEqual([f["binder"] for f in f_cls], ["hbad"])
            self.assertEqual(r_cls["summary"]["suppressed_counts"]["by_reason"].get("local_class_instance"), 2)
            r_cls_noisy = kernel.hygiene_decls(kdb, ["Proj.classBinders"], src_root=src, only="dropped", include_noisy=True)
            self.assertEqual({f["binder"] for f in r_cls_noisy["decls"][0]["findings"]}, {"hv", "hc", "hbad"})

            # 3. Set.univ disjoint + activating_premise suppressed by default, revealed with --include-noisy
            r_triv = kernel.hygiene_decls(kdb, ["Proj.univDisjoint", "Proj.actPremise"], src_root=src, only="true_slot")
            self.assertEqual(r_triv["summary"]["total_findings"], 0)
            self.assertEqual(r_triv["summary"]["suppressed_counts"]["by_reason"].get("top_univ_membership"), 1)
            self.assertEqual(r_triv["summary"]["suppressed_counts"]["by_reason"].get("activating_premise"), 1)
            r_triv_n = kernel.hygiene_decls(kdb, ["Proj.actPremise"], src_root=src, only="true_slot", include_noisy=True)
            self.assertEqual(r_triv_n["decls"][0]["findings"][0].get("role"), "activating_premise")
            self.assertEqual(r_triv_n["decls"][0]["findings"][0].get("premise_callee"), "hH")

    def test_semantic_flags_and_stats_with_alias(self):
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "k_sem7.db")
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Proj"), exist_ok=True)
            with open(os.path.join(src, "Proj", "Sem7.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "namespace Proj\n\n"
                    "def sEEFallback (x : Nat) : Nat :=\n"
                    "  if h : x > 0 then x + 1 else 0\n\n"
                    "def normalBranch (x : Nat) : Nat :=\n"
                    "  if x = 0 then 1 else 0\n\n"
                    "theorem placesClosure (a b : Nat) (h : a ≤ b) : ∃ u v, a ≤ b ∧ a ≤ a ∧ b ≤ b := by\n"
                    "  refine ⟨a, b, h, le_refl _, le_rfl⟩\n\n"
                    "theorem cleanRefl (a : Nat) : a ≤ a := by\n"
                    "  exact le_refl a\n\n"
                    "theorem targetCore : 0 = 0 := rfl\n"
                    "theorem vn1Alias : 0 = 0 := targetCore\n"
                    "theorem wrappedAlias (k : Nat) : 0 = 0 := targetCore\n\n"
                    "end Proj\n"
                )
            decls = [
                (10, "Proj.sEEFallback", "def", 1, 2, 0, 0),
                (11, "Proj.normalBranch", "def", 1, 2, 0, 0),
                (12, "Proj.placesClosure", "thm", 1, 4, 0, 0),
                (13, "Proj.cleanRefl", "thm", 1, 2, 0, 0),
                (20, "Proj.targetCore", "thm", 1, 1, 0, 0),
                (21, "Proj.vn1Alias", "thm", 1, 0, 1, 1),
                (22, "Proj.wrappedAlias", "thm", 4, 0, 1, 1),
            ]
            edges = [(21, 20, 2), (22, 20, 2)]
            dm = [(d[0], "Proj.Sem7", "leanre_db:exact") for d in decls]
            self._create_mini_db(kdb, decls, edges, dm)

            # Default excludes semantic findings but counts hints
            hy_def = kernel.hygiene_decls(
                kdb,
                ["Proj.sEEFallback", "Proj.normalBranch", "Proj.placesClosure", "Proj.cleanRefl"],
                src_root=src,
            )
            self.assertEqual(sorted(hy_def["summary"]["by_category"].keys()), ["dropped", "true_slot", "tuple_unread"])
            self.assertEqual(hy_def["summary"]["total_findings"], 0)
            self.assertEqual(hy_def["summary"].get("semantic_hints_available"), 2)
            self.assertIn("--semantic to inspect", kernel.format_hygiene_text(hy_def))

            # --semantic & CLI --only semantic reveal only the 2 high-signal patterns
            hy_sem = kernel.hygiene_decls(
                kdb,
                ["Proj.sEEFallback", "Proj.normalBranch", "Proj.placesClosure", "Proj.cleanRefl"],
                src_root=src,
                only="semantic",
            )
            self.assertEqual(hy_sem["summary"]["by_category"]["semantic"], 2)
            by_sem = {d["name"]: d["findings"] for d in hy_sem["decls"]}
            self.assertEqual([f["kind"] for f in by_sem["Proj.sEEFallback"]], ["default_zero_branch"])
            self.assertEqual(by_sem["Proj.normalBranch"], [])
            self.assertEqual([f["kind"] for f in by_sem["Proj.placesClosure"]], ["le_refl_closure"])
            self.assertEqual(by_sem["Proj.placesClosure"][0]["count"], 2)
            self.assertEqual(by_sem["Proj.cleanRefl"], [])

            import contextlib, io
            out_buf = io.StringIO()
            with contextlib.redirect_stdout(out_buf):
                rc = kernel.main([
                    "hygiene", "Proj.sEEFallback",
                    "--kernel-db", kdb,
                    "--src-root", src,
                    "--semantic", "--json",
                ])
            self.assertEqual(rc, 0)
            self.assertEqual(json.loads(out_buf.getvalue())["summary"]["by_category"]["semantic"], 1)

            # stats alias_of: default handles vn==1, --with-alias handles wrapped forwarding
            st_no_flag = kernel.stats_decls(kdb, ["Proj.vn1Alias", "Proj.wrappedAlias"], src_root=src, with_alias=False)
            self.assertEqual(st_no_flag["decls"][0].get("alias_of"), "Proj.targetCore")
            self.assertNotIn("alias_of", st_no_flag["decls"][1])
            st_flag_buf = io.StringIO()
            with contextlib.redirect_stdout(st_flag_buf):
                rc2 = kernel.main([
                    "stats", "Proj.vn1Alias", "Proj.wrappedAlias",
                    "--kernel-db", kdb, "--src-root", src, "--with-alias", "--table",
                ])
            self.assertEqual(rc2, 0)
            self.assertIn("alias_of: Proj.wrappedAlias := Proj.targetCore", st_flag_buf.getvalue())


if __name__ == "__main__":
    unittest.main()
