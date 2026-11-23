#!/usr/bin/env python3
"""Unit tests for `leanre.atlas` (synthetic DB, determinism, stdlib fallback, PNG & OPSEC)."""
from __future__ import annotations

import copy
import json
import os
import sqlite3
import struct
import tempfile
import unittest
from unittest import mock
import zlib

try:
    from leanre import atlas
except ImportError:  # pragma: no cover
    import atlas  # type: ignore[no-redef]


def _build_synthetic_kernel_db(path: str) -> None:
    """Create a compact, realistic synthetic `kernel.db` for deterministic testing."""
    con = sqlite3.connect(path)
    con.executescript(
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
        CREATE TABLE edges(
            src INTEGER NOT NULL,
            dst INTEGER NOT NULL,
            kind INTEGER NOT NULL,
            PRIMARY KEY(src, dst)
        ) WITHOUT ROWID;
        CREATE TABLE dom(
            tree_id INTEGER NOT NULL,
            decl_id INTEGER NOT NULL,
            idom INTEGER,
            depth INTEGER NOT NULL,
            subtree_size INTEGER NOT NULL,
            PRIMARY KEY(tree_id, decl_id)
        ) WITHOUT ROWID;
        CREATE TABLE decl_module(
            decl_id INTEGER PRIMARY KEY,
            module TEXT,
            method TEXT NOT NULL,
            src_decl_id INTEGER
        );
        """
    )

    # Declarations (topological order: src > dst on edges)
    # 0..7: external library base lemmas & definitions
    decls = [
        (0, "Nat.base0", "def", 1, 10, 5, 5, 0, 0, 0, 0, 1, 1, 1, 0, "k1n:lib0", "k1a:lib0"),
        (1, "Nat.base1", "def", 1, 12, 6, 5, 0, 0, 0, 0, 1, 1, 1, 0, "k1n:lib1", "k1a:lib1"),
        (2, "Algebra.lemA", "thm", 1, 14, 18, 5, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:lib2", "k1a:lib2"),
        (3, "Algebra.lemB", "thm", 1, 15, 20, 5, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:lib3", "k1a:lib3"),
        (4, "Algebra.lemC", "thm", 1, 16, 22, 5, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:lib4", "k1a:lib4"),
        (5, "Topology.lemD", "thm", 1, 18, 25, 5, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:lib5", "k1a:lib5"),
        (6, "Topology.lemE", "thm", 1, 19, 25, 5, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:lib6", "k1a:lib6"),
        # 7: Mathlib theorem in cross-repo alien collision bucket `k1n:cross_alien`
        (7, "Mathlib.Ring.isMaximal_prime", "thm", 1, 32, 40, 2, 3, 1, 2, 0, 1, 0, 0, 0, "k1n:cross_alien", "k1a:cross_alien"),
        # 8, 9: Trivial `type_nodes <= 3` shells (must be excluded!)
        (8, "Proj.Triv.shell1", "thm", 1, 2, 30, 1, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:triv_shell", "k1a:triv_shell"),
        (9, "Proj.Triv.shell2", "thm", 1, 3, 30, 1, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:triv_shell", "k1a:triv_shell"),
        # 10, 11: Clone pair (J = 4/4 = 1.0 >= 0.70)
        (10, "Proj.ModA.clone_lhs", "thm", 1, 24, 35, 1, 4, 0, 4, 0, 1, 0, 0, 0, "k1n:clone_sig", "k1a:clone_sig"),
        (11, "Proj.ModB.clone_rhs", "thm", 1, 24, 36, 1, 4, 0, 4, 0, 1, 0, 0, 0, "k1n:clone_sig", "k1a:clone_sig"),
        # 12, 13: Variant pair (E_V = {0,1,2} vs {1,2,3,4} -> J = 2/5 = 0.40)
        (12, "Proj.ModA.var_lhs", "thm", 1, 28, 32, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:var_sig", "k1a:var_sig"),
        (13, "Proj.ModB.var_rhs", "thm", 1, 28, 34, 1, 4, 0, 4, 0, 1, 0, 0, 0, "k1n:var_sig", "k1a:var_sig"),
        # 14, 15: Intra-project Alien-Proof pair (E_V = {0,2,3} vs {1,5,6} -> J = 0/6 = 0.0)
        (14, "Proj.Geom.torsion_analytic", "thm", 1, 45, 55, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:intra_alien", "k1a:intra_alien"),
        (15, "Proj.Moduli.torsion_isogeny", "thm", 1, 45, 62, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:intra_alien", "k1a:intra_alien"),
        # 16: Project twin of Mathlib decl 7 (`k1n:cross_alien`, E_V = {4,5,6} vs {0,1,2} -> J = 0/6 = 0.0)
        (16, "Proj.Arith.isMaximal_prime_alt", "thm", 1, 32, 48, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:cross_alien", "k1a:cross_alien"),
        # 17, 18, 19: 2-hop relay delegation (19 -> 18 -> 17; must NOT rank as independent alien twin!)
        (17, "Proj.Relay.core_thm", "thm", 1, 50, 90, 1, 5, 0, 5, 0, 1, 0, 0, 0, "k1n:relay_sig", "k1a:relay_sig"),
        (18, "Proj.Relay.mid_shim", "thm", 1, 50, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:relay_sig", "k1a:relay_sig"),
        (19, "Proj.Consumer.outer_alias", "thm", 1, 50, 22, 1, 2, 0, 2, 0, 1, 0, 0, 0, "k1n:relay_sig", "k1a:relay_sig"),
        # 20..22: Collinear synteny streak matching lib2, lib3, lib4 via k1a
        (20, "Proj.Syn.s2", "thm", 1, 14, 20, 1, 1, 1, 0, 0, 1, 0, 0, 0, "k1n:ps2", "k1a:lib2"),
        (21, "Proj.Syn.s3", "thm", 1, 15, 20, 1, 1, 1, 0, 0, 1, 0, 0, 0, "k1n:ps3", "k1a:lib3"),
        (22, "Proj.Syn.s4", "thm", 1, 16, 20, 1, 1, 1, 0, 0, 1, 0, 0, 0, "k1n:ps4", "k1a:lib4"),
        # 23: Apex root
        (23, "allChi", "thm", 1, 18, 30, 0, 6, 2, 4, 0, 1, 1, 0, 0, "k1n:apex", "k1a:apex"),
        # 24: Dead non-live declaration (live_mask=0, not in dom tree 0)
        (24, "Proj.Dead.unused", "thm", 1, 10, 10, 0, 1, 1, 0, 0, 0, 0, 0, 0, "k1n:dead", "k1a:dead"),
        # 6: non-project Lean core twin of decl 7 (`k1n:lib_only_pair`, lean4 vs mathlib4 -> NOT project cross-repo!)
        (25, "Lean.Nat.lib_only_a", "thm", 1, 20, 30, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:lib_only", "k1a:lib_only"),
        (26, "Mathlib.Nat.lib_only_b", "thm", 1, 20, 32, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:lib_only", "k1a:lib_only"),
    ]
    con.executemany("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", decls)

    for row in decls:
        did, name, kind, _nc, tn, _vn, *_rest, sh, sha = row
        ckind = "thm" if kind == "thm" else "def"
        con.execute("INSERT INTO consts VALUES (?,?,?,?,?,?,?,?,?)", (did, name, did, ckind, 0, sh, sha, tn, 0))

    # Module provenance
    for row in decls:
        did, name = row[0], row[1]
        if did <= 7 or did in (25, 26):
            con.execute("INSERT INTO decl_module VALUES (?, NULL, 'unmatched:library_or_external', NULL)", (did,))
        else:
            mod = ".".join(name.split(".")[:-1]) or "Main"
            con.execute("INSERT INTO decl_module VALUES (?, ?, 'leanre_db:exact', ?)", (did, mod, did))

    # Edges (src > dst strictly):
    edges = [
        (2, 0, 2), (3, 0, 2), (4, 1, 2), (5, 1, 2), (6, 1, 2),
        # Mathlib 7: E_V = {0, 1, 2}
        (7, 0, 3), (7, 1, 2), (7, 2, 2),
        # Trivial shells
        (8, 0, 2), (9, 1, 2),
        # Clone pair 10, 11: both E_V = {0, 1, 2, 3}
        (10, 0, 2), (10, 1, 2), (10, 2, 3), (10, 3, 2),
        (11, 0, 2), (11, 1, 2), (11, 2, 3), (11, 3, 2),
        # Variant pair 12, 13: {0, 1, 2} vs {1, 2, 3, 4} -> J = 2/5 = 0.40
        (12, 0, 2), (12, 1, 2), (12, 2, 2),
        (13, 1, 2), (13, 2, 2), (13, 3, 2), (13, 4, 2),
        # Intra-project alien pair 14, 15: {0, 2, 3} vs {1, 5, 6} -> J = 0.0
        (14, 0, 2), (14, 2, 2), (14, 3, 3), (14, 4, 1),  # note (14,4,1) is type-only, NOT in E_V!
        (15, 1, 2), (15, 5, 2), (15, 6, 3), (15, 4, 1),
        # Cross-repo alien twin 16 vs 7: E_V(16) = {4, 5, 6} -> J(7, 16) = 0.0
        (16, 4, 2), (16, 5, 2), (16, 6, 2),
        # 2-hop relay 19 -> 18 -> 17
        (17, 0, 2), (17, 1, 2), (17, 2, 2), (17, 3, 2), (17, 4, 2),
        (18, 17, 2),
        (19, 18, 2), (19, 5, 2),
        # Synteny type edges
        (20, 2, 1), (21, 3, 1), (22, 4, 1),
        # Apex edges
        (23, 10, 2), (23, 11, 2), (23, 12, 2), (23, 13, 2),
        (23, 14, 3), (23, 15, 3), (23, 16, 2), (23, 19, 2),
        (23, 20, 1), (23, 21, 1), (23, 22, 1), (23, 7, 2),
        (23, 25, 2), (23, 26, 2),
        # Lib-only non-project alien pair 25 vs 26: {0,1,2} vs {3,4,5} -> J = 0.0 (lean4 vs mathlib4)
        (25, 0, 2), (25, 1, 2), (25, 2, 2),
        (26, 3, 2), (26, 4, 2), (26, 5, 2),
        # Dead edge from non-live decl 24
        (24, 0, 1),
    ]
    con.executemany("INSERT INTO edges VALUES (?,?,?)", edges)

    # Dominator tree 0 over live declarations 0..23,25,26 (root = 23 `allChi`, subtree_size = 26)
    con.execute("INSERT INTO dom VALUES (0, 23, NULL, 0, 26)")
    for did in list(range(23)) + [25, 26]:
        con.execute("INSERT INTO dom VALUES (0, ?, 23, 1, 1)", (did,))

    con.commit()
    con.close()


def _build_synthetic_tier2_db(path: str) -> None:
    con = sqlite3.connect(path)
    con.executescript(
        """
        CREATE TABLE kernel_matches(
            decl_id INTEGER NOT NULL,
            const_name TEXT NOT NULL,
            ckind TEXT NOT NULL,
            module TEXT,
            live_mask INTEGER NOT NULL,
            stmt_mask INTEGER NOT NULL,
            type_nodes INTEGER NOT NULL,
            sig_size INTEGER NOT NULL,
            is_aux INTEGER NOT NULL,
            variant TEXT NOT NULL,
            sighash TEXT NOT NULL,
            n_candidates INTEGER NOT NULL,
            lib_const_name TEXT NOT NULL,
            lib_ckind TEXT NOT NULL,
            lib_origin TEXT NOT NULL,
            lib_repo TEXT,
            lib_commit_sha TEXT,
            lib_license TEXT,
            same_short_name INTEGER NOT NULL,
            provenance TEXT NOT NULL,
            PRIMARY KEY (const_name, variant)
        );
        CREATE TABLE matches(
            proof_id INTEGER NOT NULL,
            variant TEXT NOT NULL,
            sighash TEXT NOT NULL,
            n_tokens INTEGER NOT NULL,
            grade TEXT NOT NULL,
            n_candidates INTEGER NOT NULL,
            corpus_id INTEGER NOT NULL,
            repo TEXT NOT NULL,
            commit_sha TEXT NOT NULL,
            license TEXT NOT NULL,
            corpus_name TEXT NOT NULL,
            same_short_name INTEGER NOT NULL,
            provenance TEXT NOT NULL,
            PRIMARY KEY (proof_id, variant)
        );
        """
    )
    rows = [
        (16, "Proj.Arith.isMaximal_prime_alt", "thm", "Proj.Arith", 1, 0, 32, 32, 0, "k1n", "k1n:cross_alien", 1, "Mathlib.Ring.isMaximal_prime", "thm", "library_corpus", "mathlib4", "0df4", "Apache-2.0", 0, "L"),
        (20, "Proj.Syn.s2", "thm", "Proj.Syn", 1, 0, 14, 14, 0, "k1a", "k1a:lib2", 1, "Algebra.lemA", "thm", "library_corpus", "mathlib4", "0df4", "Apache-2.0", 0, "L"),
        (21, "Proj.Syn.s3", "thm", "Proj.Syn", 1, 0, 15, 15, 0, "k1a", "k1a:lib3", 1, "Algebra.lemB", "thm", "library_corpus", "mathlib4", "0df4", "Apache-2.0", 0, "L"),
        (22, "Proj.Syn.s4", "thm", "Proj.Syn", 1, 0, 16, 16, 0, "k1a", "k1a:lib4", 1, "Algebra.lemC", "thm", "library_corpus", "mathlib4", "0df4", "Apache-2.0", 0, "L"),
    ]
    con.executemany("INSERT INTO kernel_matches VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", rows)
    con.execute(
        "INSERT INTO matches VALUES (1, 's1n', 's1n:x', 20, 'strong', 1, 1, 'FLT', 'abc', 'Apache-2.0', 'FLT.thm', 0, 'L')"
    )
    con.commit()
    con.close()


def _strip_timings(obj: object) -> object:
    if isinstance(obj, dict):
        return {
            k: _strip_timings(v)
            for k, v in obj.items()
            if k not in ("runtime_sec", "numpy_accelerated")
        }
    if isinstance(obj, list):
        return [_strip_timings(x) for x in obj]
    return obj


class TestAtlasSynthetic(unittest.TestCase):
    def setUp(self) -> None:
        self.tmpdir = tempfile.TemporaryDirectory()
        self.kdb_path = os.path.join(self.tmpdir.name, "kernel.db")
        self.t2_path = os.path.join(self.tmpdir.name, "tier2.db")
        _build_synthetic_kernel_db(self.kdb_path)
        _build_synthetic_tier2_db(self.t2_path)

    def tearDown(self) -> None:
        self.tmpdir.cleanup()

    def test_readonly_connection_blocks_writes(self) -> None:
        con = atlas.connect_ro(self.kdb_path)
        try:
            with self.assertRaises(sqlite3.OperationalError):
                con.execute("DELETE FROM decls WHERE id = 0")
        finally:
            con.close()

    def test_alien_twins_splitter_and_relay_filtering(self) -> None:
        res = atlas.compute_alien_twins(self.kdb_path, tier2_db_path=self.t2_path)
        counts = res["counts"]
        # 2 trivial shells (`type_nodes <= 3`) must be excluded
        self.assertEqual(counts["excluded_trivial_thms"], 2)
        # 6 non-trivial buckets: clone_sig, var_sig, intra_alien, cross_alien, relay_sig, lib_only
        self.assertEqual(counts["nontrivial_collision_buckets"], 6)
        # Only buckets involving >=1 project decl count as project cross-repo collisions (NOT lean4<->mathlib4!)
        self.assertEqual(counts["cross_repo_collision_buckets"], 1)
        # Direct 1-hop delegates in relay_sig: (17, 18) and (18, 19) -> 2 skipped!
        self.assertEqual(counts["direct_delegates_skipped"], 2)

        parts = res["partitions"]["all_sampled_pairs"]
        cross_parts = res["partitions"]["cross_repo_pairs"]
        # Evaluated non-direct pairs:
        #   clone_sig (10,11) -> clone (J=1.0)
        #   var_sig (12,13)   -> variant (J=0.4)
        #   intra_alien (14,15) -> alien_proof (J=0.0)
        #   cross_alien (7,16)  -> alien_proof (J=0.0, project vs mathlib4)
        #   lib_only (25,26)    -> alien_proof (J=0.0, lean4 vs mathlib4 -> excluded from cross_repo_pairs!)
        #   relay_sig (17,19)   -> alien_proof in raw J (0/7), BUT filtered out of top_alien_pairs by 2-hop DAG reach!
        self.assertEqual(parts["clone"], 1)
        self.assertEqual(parts["variant"], 1)
        self.assertEqual(parts["alien_proof"], 4)
        self.assertEqual(cross_parts["alien_proof"], 1)

        # Verify 2-hop relay (17, 19) is EXCLUDED from verified independent `top_alien_pairs`!
        top_sh = {p["sighash"] for p in res["top_alien_pairs"]}
        self.assertIn("k1n:intra_alien", top_sh)
        self.assertIn("k1n:cross_alien", top_sh)
        self.assertNotIn("k1n:relay_sig", top_sh)

        # Verify type-only edge (14 -> 4, kind=1) was NOT included in E_V(14)
        intra = res["top_alien_pairs_intra"][0]
        self.assertEqual(intra["jaccard"], 0.0)
        self.assertEqual(intra["thm_a"]["ev_size"], 3)
        self.assertEqual(intra["thm_b"]["ev_size"], 3)
        self.assertEqual(intra["band"], "alien")
        self.assertFalse(intra["is_cross_repo"])

        cross = res["top_alien_pairs_cross_repo"][0]
        self.assertEqual(cross["band"], "alien")
        self.assertTrue(cross["is_cross_repo"])

        # Verify histograms_by_scope (all, intra, cross_repo) and band counts
        hbs = res["histograms_by_scope"]
        self.assertEqual(hbs["all"]["bins_20"], res["jaccard_histogram_20bins"])
        self.assertEqual(hbs["all"]["counts"], {"alien": 4, "variant": 1, "clone": 1, "total": 6})
        # Intra excludes lib_only (25, 26) and cross_alien (7, 16)
        self.assertEqual(hbs["intra"]["counts"], {"alien": 2, "variant": 1, "clone": 1, "total": 4})
        self.assertEqual(sum(hbs["intra"]["bins_20"]), 4)
        self.assertEqual(hbs["cross_repo"]["counts"], {"alien": 1, "variant": 0, "clone": 0, "total": 1})
        self.assertEqual(sum(hbs["cross_repo"]["bins_20"]), 1)

        # Verify top_variant_pairs_* and top_clone_pairs_*
        self.assertEqual(len(res["top_variant_pairs_intra"]), 1)
        var_p = res["top_variant_pairs_intra"][0]
        self.assertEqual(var_p["sighash"], "k1n:var_sig")
        self.assertEqual(var_p["band"], "variant")
        self.assertFalse(var_p["is_cross_repo"])
        self.assertEqual(res["top_variant_pairs_cross_repo"], [])

        self.assertEqual(len(res["top_clone_pairs_intra"]), 1)
        cln_p = res["top_clone_pairs_intra"][0]
        self.assertEqual(cln_p["sighash"], "k1n:clone_sig")
        self.assertEqual(cln_p["band"], "clone")
        self.assertFalse(cln_p["is_cross_repo"])
        self.assertEqual(res["top_clone_pairs_cross_repo"], [])

    def test_alien_twins_cross_repo_bands_and_wrapper_tags(self) -> None:
        db_path = os.path.join(self.tmpdir.name, "bands.db")
        con = sqlite3.connect(db_path)
        con.executescript(
            """
            CREATE TABLE decls(
                id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
                n_consts INTEGER NOT NULL, type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL,
                fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL, fan_out_type INTEGER NOT NULL,
                fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL, live_mask INTEGER NOT NULL,
                stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
                sighash TEXT, sighash_anon TEXT
            );
            CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src, dst)) WITHOUT ROWID;
            CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
            """
        )
        decls = [
            (0, "inferInstance", "def", 1, 5, 5, 5, 0, 0, 0, 0, 1, 1, 1, 0, "k1n:inf", "k1a:inf"),
            (1, "Nat.b1", "def", 1, 5, 5, 5, 0, 0, 0, 0, 1, 1, 1, 0, "k1n:b1", "k1a:b1"),
            (2, "Nat.b2", "def", 1, 5, 5, 5, 0, 0, 0, 0, 1, 1, 1, 0, "k1n:b2", "k1a:b2"),
            (3, "Nat.b3", "def", 1, 5, 5, 5, 0, 0, 0, 0, 1, 1, 1, 0, "k1n:b3", "k1a:b3"),
            (4, "Nat.b4", "def", 1, 5, 5, 5, 0, 0, 0, 0, 1, 1, 1, 0, "k1n:b4", "k1a:b4"),
            # Cross-repo variant: J = 2/4 = 0.50 (lib vs proj)
            (5, "Mathlib.var_lib", "thm", 1, 30, 40, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:xvar", "k1a:xvar"),
            (6, "Proj.A.var_proj", "thm", 1, 30, 20, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:xvar", "k1a:xvar"),
            # Cross-repo clone: J = 3/3 = 1.0 (lib vs proj), with proj using inferInstance wrapper
            (7, "Mathlib.cln_lib", "thm", 1, 40, 50, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:xcln", "k1a:xcln"),
            (8, "Proj.B.cln_proj", "thm", 1, 40, 25, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:xcln", "k1a:xcln"),
            # Same-scope project pair (must be skipped in intra histogram & lists!)
            (9, "Proj.Same.s1", "thm", 1, 25, 25, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:same", "k1a:same"),
            (10, "Proj.Same.s2", "thm", 1, 25, 25, 1, 3, 0, 3, 0, 1, 0, 0, 0, "k1n:same", "k1a:same"),
        ]
        con.executemany("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", decls)
        for row in decls:
            did, name = row[0], row[1]
            if did in (0, 1, 2, 3, 4, 5, 7):
                con.execute("INSERT INTO decl_module VALUES (?, NULL, 'unmatched:library_or_external', NULL)", (did,))
            else:
                mod = ".".join(name.split(".")[:-1])
                con.execute("INSERT INTO decl_module VALUES (?, ?, 'leanre_db:exact', ?)", (did, mod, did))
        edges = [
            # xvar: {1, 2, 3} vs {2, 3, 4} -> J = 2/4 = 0.50; decl 6 has ev_size=3, vn=20 -> thin_wrapper
            (5, 1, 2), (5, 2, 2), (5, 3, 2),
            (6, 2, 2), (6, 3, 2), (6, 4, 2),
            # xcln: {0, 1, 2} vs {0, 1, 2} -> J = 1.0; both use inferInstance (id=0)
            (7, 0, 2), (7, 1, 2), (7, 2, 2),
            (8, 0, 2), (8, 1, 2), (8, 2, 2),
            # same-scope clone: {1, 2, 3} vs {1, 2, 3}
            (9, 1, 2), (9, 2, 2), (9, 3, 2),
            (10, 1, 2), (10, 2, 2), (10, 3, 2),
        ]
        con.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
        con.commit()
        con.close()

        res = atlas.compute_alien_twins(db_path)
        hbs = res["histograms_by_scope"]
        # `all` includes same-scope pair (total=3), while `intra` skips same-scope (total=0)
        self.assertEqual(hbs["all"]["counts"], {"alien": 0, "variant": 1, "clone": 2, "total": 3})
        self.assertEqual(hbs["intra"]["counts"], {"alien": 0, "variant": 0, "clone": 0, "total": 0})
        self.assertEqual(hbs["cross_repo"]["counts"], {"alien": 0, "variant": 1, "clone": 1, "total": 2})
        self.assertEqual(sum(hbs["cross_repo"]["bins_20"][4:14]), 1)
        self.assertEqual(sum(hbs["cross_repo"]["bins_20"][14:]), 1)

        self.assertEqual(len(res["top_variant_pairs_cross_repo"]), 1)
        xv = res["top_variant_pairs_cross_repo"][0]
        self.assertEqual(xv["band"], "variant")
        self.assertTrue(xv["is_cross_repo"])
        self.assertEqual(xv["thm_b"].get("wrapper_tag"), "thin_wrapper")
        self.assertIsNone(xv["thm_a"].get("wrapper_tag"))

        self.assertEqual(len(res["top_clone_pairs_cross_repo"]), 1)
        xc = res["top_clone_pairs_cross_repo"][0]
        self.assertEqual(xc["band"], "clone")
        self.assertTrue(xc["is_cross_repo"])
        self.assertEqual(xc["thm_a"].get("wrapper_tag"), "inferInstance")
        self.assertEqual(xc["thm_b"].get("wrapper_tag"), "inferInstance")

    def test_hic_matrix_and_png_encoding(self) -> None:
        out_json = os.path.join(self.tmpdir.name, "atlas.json")
        hic_png = os.path.join(self.tmpdir.name, "hic.png")
        syn_png = os.path.join(self.tmpdir.name, "syn.png")

        summary = atlas.run_atlas(
            kernel_db_path=self.kdb_path,
            tier2_db_path=self.t2_path,
            out_json_path=out_json,
            hic_png_path=hic_png,
            synteny_png_path=syn_png,
        )
        hc = summary["hic_matrix"]
        self.assertEqual(hc["n_live_decls"], 26)
        self.assertEqual(hc["total_decls_in_db"], 27)
        # 68 total edges: 67 live + 1 from dead decl 24
        self.assertEqual(hc["edge_totals"]["total_streamed"], 68)
        self.assertEqual(hc["edge_totals"]["live_binned"], 67)
        self.assertEqual(hc["edge_totals"]["unmapped_nonlive"], 1)

        # Coarse 32x32 sum equals live_binned
        c32 = hc["coarse_32"]
        tot_32 = (
            sum(sum(r) for r in c32["type_only"])
            + sum(sum(r) for r in c32["value_only"])
            + sum(sum(r) for r in c32["both"])
        )
        self.assertEqual(tot_32, 67)

        # Verify clickable bin_catalog (128 bins), cell_samples (32x32), and region_edge_samples
        self.assertEqual(len(hc["bin_catalog"]), 128)
        populated_bins = [b for b in hc["bin_catalog"] if b]
        self.assertGreater(len(populated_bins), 0)
        sample_decl = populated_bins[0][0]
        for key in ("name", "short", "kind", "dom", "mod", "line", "region"):
            self.assertIn(key, sample_decl)

        nz32_keys = {
            f"{r},{c}"
            for r in range(32)
            for c in range(32)
            if c32["type_only"][r][c] + c32["value_only"][r][c] + c32["both"][r][c] > 0
        }
        self.assertEqual(set(hc["cell_samples"].keys()), nz32_keys)
        for edges_list in hc["cell_samples"].values():
            self.assertGreaterEqual(len(edges_list), 1)
            self.assertLessEqual(len(edges_list), 3)
            for row in edges_list:
                self.assertEqual(len(row), 7)
                self.assertIn(row[2], ("type", "value", "both"))

        self.assertGreater(len(hc["region_edge_samples"]), 0)
        for edges_list in hc["region_edge_samples"].values():
            self.assertGreaterEqual(len(edges_list), 1)
            for row in edges_list:
                self.assertEqual(len(row), 7)

        # Verify valid 512x512 8-bit RGB PNG structure for both images
        for png_path in (hic_png, syn_png):
            with open(png_path, "rb") as f:
                data = f.read()
            self.assertEqual(data[:8], b"\x89PNG\r\n\x1a\n")
            ihdr_len, ihdr_tag = struct.unpack(">I4s", data[8:16])
            self.assertEqual(ihdr_tag, b"IHDR")
            self.assertEqual(ihdr_len, 13)
            w, h, bit_depth, color_type = struct.unpack(">IIBB", data[16:26])
            self.assertEqual((w, h, bit_depth, color_type), (512, 512, 8, 2))
            # Find IDAT and decompress
            pos = 8
            idat_chunks = []
            while pos < len(data):
                clen, ctag = struct.unpack(">I4s", data[pos : pos + 8])
                payload = data[pos + 8 : pos + 8 + clen]
                if ctag == b"IDAT":
                    idat_chunks.append(payload)
                elif ctag == b"IEND":
                    break
                pos += 12 + clen
            raw_pixels = zlib.decompress(b"".join(idat_chunks))
            self.assertEqual(len(raw_pixels), 512 * (1 + 512 * 3))

    def test_synteny_tier2_vs_kernel_fallback(self) -> None:
        s_t2 = atlas.run_atlas(kernel_db_path=self.kdb_path, tier2_db_path=self.t2_path)["synteny"]
        s_fb = atlas.run_atlas(kernel_db_path=self.kdb_path, tier2_db_path=None)["synteny"]

        self.assertEqual(s_t2["source"], "tier2_db")
        self.assertEqual(s_fb["source"], "kernel_db_fallback")
        self.assertEqual(s_t2["hit_totals"]["total_matches"], 4)
        self.assertEqual(s_fb["hit_totals"]["total_matches"], 4)
        self.assertEqual(s_t2["hit_totals"]["exact_k1n_matches"], 1)
        self.assertEqual(s_fb["terra_incognita_bands"]["eligible_project_bins_256"], 16)
        self.assertEqual(s_fb["terra_incognita_bands"]["zero_named_match_bins_256"], 12)

        # Verify clickable synteny lib_bins (128) and match_samples
        self.assertEqual(len(s_t2["lib_bins"]), 128)
        self.assertTrue(any(lbl for lbl in s_t2["lib_bins"]))
        self.assertGreater(len(s_t2["match_samples"]), 0)
        for samples in s_t2["match_samples"].values():
            self.assertGreaterEqual(len(samples), 1)
            for s_row in samples:
                self.assertEqual(len(s_row), 7)
                self.assertIn(s_row[6], ("k1n", "k1a"))

    def test_stdlib_fallback_matches_numpy_and_is_deterministic(self) -> None:
        res_np1 = atlas.run_atlas(kernel_db_path=self.kdb_path, tier2_db_path=self.t2_path)
        res_np2 = atlas.run_atlas(kernel_db_path=self.kdb_path, tier2_db_path=self.t2_path)
        with mock.patch.object(atlas, "np", None):
            res_py = atlas.run_atlas(kernel_db_path=self.kdb_path, tier2_db_path=self.t2_path)
            self.assertFalse(res_py["inputs"]["numpy_accelerated"])

        self.assertEqual(_strip_timings(res_np1), _strip_timings(res_np2))
        self.assertEqual(_strip_timings(res_np1), _strip_timings(res_py))

    def test_emitted_summary_hygiene_if_present(self) -> None:
        repo_summary = os.path.join(atlas._REPO_ROOT, "outputs", "atlas_summary.json")
        if not os.path.isfile(repo_summary):
            return
        sz = os.path.getsize(repo_summary)
        self.assertLessEqual(sz, 820 * 1024, f"atlas_summary.json ({sz} B) exceeds 820 KB cap")
        with open(repo_summary, "r", encoding="utf-8") as f:
            txt = f.read()
        self.assertNotIn("/usr/local/", txt)
        self.assertNotIn("/home/", txt)
        self.assertNotIn("/Users/", txt)
        parsed = json.loads(txt)
        self.assertEqual(parsed["schema"], atlas.SCHEMA_VERSION)
        at = parsed["alien_twins"]
        self.assertIn("histograms_by_scope", at)
        for scope in ("all", "intra", "cross_repo"):
            sc = at["histograms_by_scope"][scope]
            self.assertEqual(len(sc["bins_20"]), 20)
            self.assertEqual(sum(sc["bins_20"]), sc["counts"]["total"])
            self.assertEqual(sum(sc["bins_20"][:4]), sc["counts"]["alien"])
            self.assertEqual(sum(sc["bins_20"][4:14]), sc["counts"]["variant"])
            self.assertEqual(sum(sc["bins_20"][14:]), sc["counts"]["clone"])
        for key in (
            "top_alien_pairs_intra",
            "top_alien_pairs_cross_repo",
            "top_variant_pairs_intra",
            "top_variant_pairs_cross_repo",
            "top_clone_pairs_intra",
            "top_clone_pairs_cross_repo",
        ):
            self.assertIn(key, at)
            self.assertGreater(len(at[key]), 0)


if __name__ == "__main__":
    unittest.main()
