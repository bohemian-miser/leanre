#!/usr/bin/env python3
"""Unit tests for FLIRT Phase 4 coarse blueprint clustering (leanre/flirt/cluster.py).

Uses synthetic in-temp SQLite kernel.db + tier1.db fixtures; zero real proof text.
"""
from __future__ import annotations

import json
import os
import sqlite3
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
FLIRT_DIR = os.path.join(HERE, "flirt")
for _p in (HERE, FLIRT_DIR):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import cluster  # noqa: E402


class ClusterSyntheticTests(unittest.TestCase):
    def setUp(self):
        self.td = tempfile.TemporaryDirectory()
        self.kdb = os.path.join(self.td.name, "kernel.db")
        self.t1db = os.path.join(self.td.name, "tier1.db")
        self.out = os.path.join(self.td.name, "clusters.json")

        ck = sqlite3.connect(self.kdb)
        ck.executescript("""
            CREATE TABLE decls(id INT PRIMARY KEY, name TEXT, kind TEXT, sighash TEXT, flags INT, live_mask INT, fan_in INT);
            CREATE TABLE decl_module(decl_id INT PRIMARY KEY, module TEXT, method TEXT);
            CREATE TABLE dom(tree_id INT, decl_id INT, idom INT, depth INT, subtree_size INT);
            CREATE TABLE edges(src INT, dst INT, kind INT);
            CREATE TABLE taint_sources(class TEXT, decl_id INT);
        """)
        # Tree rooted at id=0 (`allChi`, sz=11):
        #   0 allChi (root, sz=11)
        #     -> 1 pillar_a (sz=5): 2 coreA, 3 coreA._proof_1 (aux), 4 dupA (same k1n as 2), 5 CutCptCopy.c (copy)
        #     -> 6 pillar_b (sz=4): 7 coreB, 8 wrapB (statement wrapper), 9 coreB2
        #     -> 10 small_res (sz=1)
        # Plus 11 lib_tcb (root, sz=1)
        # Plus 12 dead_decl (live_mask=0, must NOT be included!)
        decls = [
            (0, "allChi", "thm", "k1n:00", 0, 31, 1),
            (1, "UpperTheory.Lit.every_character_of_theta_integrals_local_matching", "thm", "k1n:01", 0, 31, 1),
            (2, "Proj.A.core", "thm", "k1n:aa", 0, 31, 2),
            (3, "Proj.A.core._proof_1", "thm", "k1n:a1", 0, 31, 1),
            (4, "Proj.A.dup", "thm", "k1n:aa", 0, 31, 1),
            (5, "Proj.CutCptCopy.lam_copy", "thm", "k1n:cc", 0, 31, 1),
            (6, "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter", "thm", "k1n:06", 0, 31, 1),
            (7, "Proj.B.core", "thm", "k1n:bb", 0, 31, 2),
            (8, "Proj.B.wrap", "thm", "k1n:w8", 0, 31, 1),
            (9, "Proj.B.core2", "def", "k1n:b9", 0, 31, 1),
            (10, "Proj.Shared.leaf", "thm", "k1n:10", 0, 31, 3),
            (11, "Nat.add_comm", "thm", "k1n:11", 0, 31, 5),
            (12, "Dead.unused", "thm", "k1n:12", 0, 0, 0),
        ]
        ck.executemany("INSERT INTO decls VALUES (?,?,?,?,?,?,?)", decls)
        dmods = [
            (0, "Main", "exact"),
            (1, "Dev.Theta.Root", "exact"),
            (2, "Dev.Theta.Core", "exact"),
            (3, "Dev.Theta.Core", "aux_prefix:leanre_db"),
            (4, "Dev.Theta.Dup", "exact"),
            (5, "Dev.Theta.CutCptCopy", "exact"),
            (6, "Dev.Galois.Root", "exact"),
            (7, "Dev.Galois.Core", "exact"),
            (8, "Dev.Galois.WrapStatement", "exact"),
            (9, "Dev.Galois.Core", "exact"),
            (10, "Dev.Shared.Leaf", "exact"),
            (11, None, "unmatched:library"),
        ]
        ck.executemany("INSERT INTO decl_module VALUES (?,?,?)", dmods)
        doms = [
            (0, 0, None, 0, 11),
            (0, 1, 0, 1, 5),
            (0, 2, 1, 2, 1),
            (0, 3, 1, 2, 1),
            (0, 4, 1, 2, 1),
            (0, 5, 1, 2, 1),
            (0, 6, 0, 1, 4),
            (0, 7, 6, 2, 1),
            (0, 8, 6, 2, 1),
            (0, 9, 6, 2, 1),
            (0, 10, 0, 1, 1),
            (0, 11, None, 0, 1),
        ]
        ck.executemany("INSERT INTO dom VALUES (?,?,?,?,?)", doms)
        edges = [
            (0, 1, 2), (0, 6, 2), (0, 10, 2),
            (1, 2, 2), (1, 10, 1), (6, 7, 2), (6, 10, 3),
            (2, 11, 1), (7, 11, 2),
        ]
        ck.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
        ck.execute("INSERT INTO taint_sources VALUES ('CutCptCopy', 5)")
        ck.commit()
        ck.close()

        c1 = sqlite3.connect(self.t1db)
        c1.execute("CREATE TABLE module_fingerprints(module TEXT PRIMARY KEY, lines_wc INT, is_statement_wrapper INT, top_domain TEXT)")
        c1.executemany("INSERT INTO module_fingerprints VALUES (?,?,?,?)", [
            ("Main", 10, 0, "analytic_nt_zeta"),
            ("Dev.Theta.Root", 50, 0, "measure_integration"),
            ("Dev.Theta.Core", 100, 0, "measure_integration"),
            ("Dev.Theta.Dup", 40, 0, "measure_integration"),
            ("Dev.Theta.CutCptCopy", 30, 0, "meta_lean_elab"),
            ("Dev.Galois.Root", 60, 0, "algebra_rings_poly"),
            ("Dev.Galois.Core", 80, 0, "algebra_rings_poly"),
            ("Dev.Galois.WrapStatement", 6, 1, "algebra_rings_poly"),
            ("Dev.Shared.Leaf", 20, 0, "linear_matrix_rep"),
            ("Dev.Dead.Unused", 15, 0, "none"),
        ])
        c1.commit()
        c1.close()

    def tearDown(self):
        self.td.cleanup()

    def test_exact_partition_boilerplate_collapse_and_inter_cluster_edges(self):
        res = cluster.build_clusters(
            kernel_db=self.kdb,
            tier1_db=self.t1db,
            out_path=self.out,
            split_threshold=8,
            min_dom_cluster=3,
            min_residual_cluster=5,
            verbose=False,
        )
        t = res["totals"]
        # Exact 100% partition of the 12 live decls (dead id=12 excluded!)
        self.assertEqual(t["live_decls"], 12)
        self.assertEqual(sum(c["live_decls"] for c in res["clusters"]), 12)
        # Mutually exclusive boilerplate collapse counts:
        # aux=1 (id=3), copy=1 (id=5), stmt_wrapper=1 (id=8), k1n_dup=1 (id=4), core=8
        self.assertEqual(t["aux_collapsed"], 1)
        self.assertEqual(t["copy_shell_collapsed"], 1)
        self.assertEqual(t["stmt_wrapper_collapsed"], 1)
        self.assertEqual(t["k1n_dup_collapsed"], 1)
        self.assertEqual(t["effective_core_decls"], 8)
        self.assertEqual(t["dead_modules_not_in_kernel"], 1)

        # Pillar attribution
        by_root = {c["root_decl"]: c for c in res["clusters"]}
        self.assertEqual(by_root["UpperTheory.Lit.every_character_of_theta_integrals_local_matching"]["pillar"], "pillar_theta")
        self.assertEqual(by_root["UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter"]["pillar"], "pillar_galois")
        # Inter-cluster edges present
        self.assertGreaterEqual(len(res["edges"]), 4)
        # Output file valid JSON
        with open(self.out, encoding="utf-8") as f:
            loaded = json.load(f)
        self.assertEqual(loaded["schema"], cluster.SCHEMA_VERSION)


if __name__ == "__main__":
    unittest.main(verbosity=2)
