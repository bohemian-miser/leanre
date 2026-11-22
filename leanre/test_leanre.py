#!/usr/bin/env python3
"""Unit & integration test suite for leanre (Python 3.9 stdlib unittest)."""
from __future__ import annotations

import json
import os
import random
import sqlite3
import sys
import tempfile
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from forensics import diff_snapshots
from graph import (
    bfs_shortest_paths,
    bottom_depths_dag,
    compute_rev_reach_exact,
    dominators_chk,
    reconstruct_path_to_root,
)
from ndjson import parse_ndjson_export, run_ndjson_to_db
from scanner import normalize_for_clone, parse_horn_header, run_scan, strip_lean_comments


def _brute_reach(n, adj, src, removed=frozenset()):
    if src in removed:
        return set()
    seen = {src}
    st = [src]
    while st:
        u = st.pop()
        for w in adj[u]:
            if w not in seen and w not in removed:
                seen.add(w)
                st.append(w)
    return seen


class TestGraphAlgorithms(unittest.TestCase):
    def test_dominators_and_bfs_against_brute_force(self):
        rnd = random.Random(20261121)
        for trial in range(120):
            n = rnd.randint(4, 11)
            is_dag = (trial % 3 != 0)
            adj = [[] for _ in range(n)]
            for u in range(n):
                for v in range(n):
                    if u != v and rnd.random() < 0.30 and (v > u or not is_dag):
                        adj[u].append(v)
            radj = [[] for _ in range(n)]
            for u in range(n):
                for v in adj[u]:
                    radj[v].append(u)

            full = _brute_reach(n, adj, 0)
            adj_l = [adj[v] if v in full else [] for v in range(n)]
            radj_l = [[u for u in radj[v] if u in full] if v in full else [] for v in range(n)]

            idom, rpo, sub_sz, sub_w, _ch = dominators_chk(0, adj_l, radj_l, n)
            self.assertEqual(set(rpo), full)
            self.assertEqual(sub_sz[0], len(full))
            self.assertEqual(sub_w[0], len(full))

            for v in full:
                if v == 0:
                    continue
                brute_doms = {d for d in full if d != v and v not in _brute_reach(n, adj, 0, {d})}
                chain = set()
                cur = v
                while cur != 0:
                    cur = idom[cur]
                    chain.add(cur)
                self.assertEqual(chain, brute_doms)

            dist, parent = bfs_shortest_paths([0], adj, n)
            for v in range(n):
                if v in full:
                    self.assertGreaterEqual(dist[v], 0)
                    path = reconstruct_path_to_root(v, parent)
                    self.assertEqual(path[0], v)
                    self.assertEqual(path[-1], 0)
                    self.assertEqual(len(path) - 1, dist[v])
                else:
                    self.assertEqual(dist[v], -1)

    def test_bottom_depths_and_rev_reach_exact(self):
        rnd = random.Random(99)
        for _ in range(40):
            n = rnd.randint(5, 16)
            adj = [[] for _ in range(n)]
            for u in range(n):
                for v in range(u + 1, n):
                    if rnd.random() < 0.35:
                        adj[u].append(v)
            bdepth = bottom_depths_dag(adj, n)
            for u in range(n):
                exp = 0 if not adj[u] else 1 + max(bdepth[w] for w in adj[u])
                self.assertEqual(bdepth[u], exp)

            rr = compute_rev_reach_exact(adj, n, batch_size=3)
            for v in range(n):
                brute = sum(1 for u in range(n) if u != v and v in _brute_reach(n, adj, u))
                self.assertEqual(rr[v], brute)


class TestLeanParsers(unittest.TestCase):
    def test_strip_lean_comments(self):
        src = "import Mathlib -- line comment\n/- outer /- nested -/ end -/\ntheorem foo : Prop := by sorry\n"
        out = strip_lean_comments(src)
        self.assertNotIn("line comment", out)
        self.assertNotIn("nested", out)
        self.assertIn("theorem foo", out)
        self.assertEqual(src.count("\n"), out.count("\n"))

    def test_horn_header_parser(self):
        reqs, prov = parse_horn_header(
            "(hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin) "
            "(h : Nonempty (Hyps (fun x => Closed x) DRS)) : UpperTheory.EveryCharacter"
        )
        self.assertEqual(reqs, ["GlobalTheory.GLq.Green", "UpperTheory.Top.VWin", "Hyps"])
        self.assertEqual(prov, "UpperTheory.EveryCharacter")

        reqs2, prov2 = parse_horn_header(
            "(h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.EveryCharacter"
        )
        self.assertEqual(reqs2, ["UpperTheory.GalStar.Row0b"])
        self.assertEqual(prov2, "UpperTheory.EveryCharacter")

        # Arrow-form proposition implication + non-prop filtering
        reqs3, prov3 = parse_horn_header("(N : ℕ) [NeZero N] : UpperTheory.EveryCharacter → RiemannHypothesis")
        self.assertEqual(reqs3, ["UpperTheory.EveryCharacter"])
        self.assertEqual(prov3, "RiemannHypothesis")

        # Relation conclusion should not emit a named proposition
        reqs4, prov4 = parse_horn_header("(s : ℂ) (h0 : 0 < s.re) : s.re = 1 / 2")
        self.assertEqual(reqs4, [])
        self.assertIsNone(prov4)

    def test_clone_normalization(self):
        a = normalize_for_clone(["theorem foo1 (x : Nat) : x = 1 := by", "  exact rfl"])
        b = normalize_for_clone(["theorem bar2 (y : Nat) : y = 99 := by", "  exact rfl"])
        self.assertEqual(a, b)


class TestEndToEndSynthetic(unittest.TestCase):
    def test_mini_scan_ndjson_and_diff(self):
        with tempfile.TemporaryDirectory() as td:
            src = os.path.join(td, "src")
            os.makedirs(os.path.join(src, "Sub"), exist_ok=True)
            with open(os.path.join(src, "Main.lean"), "w") as f:
                f.write("import Sub.Hub\nimport Statements\ntheorem riemannHypothesis : RiemannHypothesis := hub\n")
            with open(os.path.join(src, "Statements.lean"), "w") as f:
                f.write("import Mathlib\ndef RiemannZetaZerosOnLine : Prop := True\n")
            with open(os.path.join(src, "Sub", "Hub.lean"), "w") as f:
                f.write("import Sub.LeafA\nimport Sub.LeafA\nimport Sub.Shim\ntheorem hub (h : Row0b) : RiemannHypothesis := by kexactB h\n")
            with open(os.path.join(src, "Sub", "Shim.lean"), "w") as f:
                f.write("import Sub.LeafB\n")
            with open(os.path.join(src, "Sub", "LeafA.lean"), "w") as f:
                f.write("import Mathlib\ndef Row0b : Prop := True\ntheorem leafA : Row0b := by decide +kernel\n")
            with open(os.path.join(src, "Sub", "LeafB.lean"), "w") as f:
                f.write("import Mathlib\ntheorem leafB : True := trivial\n")

            db = os.path.join(td, "test.db")
            stats = run_scan(src, db, root_module="Main", workers=1, verbose=False)
            self.assertEqual(stats["modules"], 6)
            self.assertEqual(stats["import_only_shims"], 1)
            self.assertEqual(stats["duplicate_import_lines"], 1)
            self.assertEqual(stats["forensic_module_counts"].get("kexactB"), 1)
            self.assertEqual(stats["forensic_module_counts"].get("decide_kernel"), 1)
            self.assertGreaterEqual(stats["horn_edges"], 1)

            # Synthetic NDJSON v3.1.0 round-trip
            nd = os.path.join(td, "mini.ndjson")
            nd_lines = [
                {"meta": {"format": {"version": "3.1.0"}}},
                {"in": 1, "str": {"pre": 0, "str": "PropType"}},
                {"in": 2, "str": {"pre": 0, "str": "riemannZeta"}},
                {"in": 3, "str": {"pre": 0, "str": "RiemannHypothesis"}},
                {"in": 4, "str": {"pre": 0, "str": "riemannHypothesis"}},
                {"in": 5, "str": {"pre": 0, "str": "sorryAx"}},
                {"ie": 0, "sort": 0},
                {"ie": 1, "const": {"name": 2, "us": []}},
                {"ie": 2, "const": {"name": 3, "us": []}},
                {"ie": 3, "const": {"name": 5, "us": []}},
                {"axiom": {"name": 5, "type": 0, "levelParams": [], "isUnsafe": False}},
                {"def": {"name": 2, "type": 0, "value": 0, "levelParams": [], "safety": "safe"}},
                {"def": {"name": 3, "type": 0, "value": 1, "levelParams": [], "safety": "safe"}},
                {"thm": {"name": 4, "type": 2, "value": 3, "levelParams": []}},
            ]
            with open(nd, "w") as f:
                for obj in nd_lines:
                    f.write(json.dumps(obj) + "\n")

            tcb = run_ndjson_to_db(nd, db, verbose=False)
            self.assertEqual(tcb["decl_count"], 4)
            self.assertFalse(tcb["sorry_in_statement_closure"])
            self.assertEqual(tcb["reachable_from_rh"], 3)

            # BinDiff sanity check (identical snapshot -> 0 deltas)
            snap_a = {"counts": {"modules": 100}, "digests": {"a": "111"}, "top_components": [], "horn_spine_edges": []}
            snap_b = {"counts": {"modules": 40}, "digests": {"a": "222"}, "top_components": [], "horn_spine_edges": []}
            d = diff_snapshots(snap_a, snap_b)
            self.assertEqual(d["count_deltas"]["modules"]["delta"], -60)
            self.assertFalse(d["identical_digests"])


class TestRealOutputsAcceptanceGates(unittest.TestCase):
    """If outputs/leanre.db and outputs/forensics_report.json exist, verify every mandatory gate."""

    def test_real_acceptance_gates(self):
        rep_path = os.path.abspath(os.path.join(_HERE, "..", "outputs", "forensics_report.json"))
        db_path = os.path.abspath(os.path.join(_HERE, "..", "outputs", "leanre.db"))
        if not (os.path.exists(rep_path) and os.path.exists(db_path)):
            self.skipTest("real outputs not generated yet")
        with open(rep_path, "r", encoding="utf-8") as f:
            rep = json.load(f)
        gates = rep["meta"]["acceptance_gates"]
        self.assertTrue(gates["all_passed"], f"Failed acceptance gates: {gates}")
        self.assertEqual(gates["modules_175187"]["actual"], 175187)
        self.assertEqual(gates["project_import_edges_753261"]["actual"], 753261)
        self.assertEqual(gates["hub_dominates_175185"]["actual"], 175185)
        self.assertEqual(gates["top_level_components_47060"]["actual"], 47060)
        self.assertEqual(gates["singleton_components_37001"]["actual"], 37001)
        self.assertEqual(gates["import_only_shims_150"]["actual"], 150)
        self.assertEqual(gates["duplicate_project_imports_308"]["actual"], 308)
        self.assertEqual(gates["challenge_decls_51692"]["actual"], 51692)

        conn = sqlite3.connect(db_path)
        try:
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM modules").fetchone()[0], 175187)
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM module_edges").fetchone()[0], 753261)
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM tcb_decls").fetchone()[0], 51692)
        finally:
            conn.close()


if __name__ == "__main__":
    unittest.main()
