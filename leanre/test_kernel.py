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


if __name__ == "__main__":
    unittest.main()
