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

    def test_proof_diff_matching_roles_sort_and_truncation(self) -> None:
        db_path = os.path.join(self.tmpdir.name, "proof_diff.db")
        ldb_path = os.path.join(self.tmpdir.name, "leanre_diff.db")
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
        # Shared, moved_role, moved_helper (same_sig, same_sig_anon, same_short_name),
        # non-matching short (<4) and aux (_proof_1), plus type-only diffs.
        decls = [
            # 0: shared with same role (value=2) in both
            (0, "Mathlib.shared_val", "thm", 1, 10, 10, 50, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:sh0", "k1a:sh0"),
            # 1: moved_role (type=1 in A -> both=3 in B)
            (1, "Proj.Base.type_to_both", "def", 1, 10, 10, 4, 0, 0, 0, 0, 1, 1, 1, 0, "k1n:mr1", "k1a:mr1"),
            # 2: moved_role (value=2 in A -> both=3 in B) => counts toward moved_role_v!
            (2, "Proj.Base.val_to_both", "thm", 1, 10, 10, 3, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:mr2", "k1a:mr2"),
            # 3 & 4: same_sig match
            (3, "Proj.Old.helper_alpha", "thm", 1, 12, 12, 8, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:sig_pair", "k1a:sig_pair_a"),
            (4, "Proj.New.helper_beta", "thm", 1, 12, 12, 9, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:sig_pair", "k1a:sig_pair_b"),
            # 5 & 6: same_sig_anon match (distinct k1n, identical k1a)
            (5, "Proj.Old.anon_left", "thm", 1, 12, 12, 6, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:anon_a", "k1a:shared_anon"),
            (6, "Proj.New.anon_right", "thm", 1, 12, 12, 7, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:anon_b", "k1a:shared_anon"),
            # 7 & 8: same_short_name match (leaf len >= 4, non-aux)
            (7, "Proj.Old.localLemma", "thm", 1, 12, 12, 5, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:sn_a", "k1a:sn_a"),
            (8, "Mathlib.Extra.localLemma", "thm", 1, 12, 12, 11, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:sn_b", "k1a:sn_b"),
            # 9 & 10: must NOT match by short name (aux _proof_1)
            (9, "Proj.Old.foo._proof_1", "thm", 1, 10, 10, 2, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:aux_a", "k1a:aux_a"),
            (10, "Proj.New.bar._proof_1", "thm", 1, 10, 10, 2, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:aux_b", "k1a:aux_b"),
            # 11 & 12: must NOT match by short name (leaf length < 4)
            (11, "Proj.Old.aux", "thm", 1, 10, 10, 2, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:short_a", "k1a:short_a"),
            (12, "Proj.New.aux", "thm", 1, 10, 10, 2, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:short_b", "k1a:short_b"),
            # 13 & 14: pure removed/added to verify distinctive sort (project low fan_in before mathlib)
            (13, "Eq.trans", "thm", 1, 10, 10, 5000, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:eq", "k1a:eq"),
            (14, "Proj.A.concrete_lem", "thm", 1, 10, 10, 1, 0, 0, 0, 0, 1, 0, 0, 0, "k1n:conc", "k1a:conc"),
            # 15 & 16: type-only shared vs type-only diff
            (15, "Mathlib.TypeShared", "def", 1, 8, 8, 20, 0, 0, 0, 0, 1, 1, 1, 0, "k1n:ts", "k1a:ts"),
            (16, "Proj.TypeOnlyA", "def", 1, 8, 8, 3, 0, 0, 0, 0, 1, 1, 1, 0, "k1n:ta", "k1a:ta"),
            # 17, 18: theorem pair under test
            (17, "Proj.ModA.main_thm", "thm", 1, 40, 50, 1, 10, 2, 8, 0, 1, 0, 0, 0, "k1n:pair_sig", "k1a:pair_sig"),
            (18, "Proj.ModB.main_thm_alt", "thm", 1, 40, 55, 1, 9, 1, 8, 0, 1, 0, 0, 0, "k1n:pair_sig", "k1a:pair_sig"),
        ]
        con.executemany("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", decls)
        for row in decls:
            did, name = row[0], row[1]
            if name.startswith(("Mathlib.", "Eq.")):
                con.execute("INSERT INTO decl_module VALUES (?, NULL, 'unmatched:library_or_external', NULL)", (did,))
            else:
                mod = ".".join(name.split(".")[:-1])
                con.execute("INSERT INTO decl_module VALUES (?, ?, 'leanre_db:exact', ?)", (did, mod, did))

        edges = [
            # thm_a (17): type={1,15,16}, value={0,2,3,5,7,9,11,13,14}
            (17, 1, 1), (17, 15, 1), (17, 16, 1),
            (17, 0, 2), (17, 2, 2), (17, 3, 2), (17, 5, 2), (17, 7, 2),
            (17, 9, 2), (17, 11, 2), (17, 13, 2), (17, 14, 2),
            # thm_b (18): type={15}, value={0,4,6,8,10,12}, both={1,2}
            (18, 15, 1), (18, 1, 3), (18, 2, 3),
            (18, 0, 2), (18, 4, 2), (18, 6, 2), (18, 8, 2), (18, 10, 2), (18, 12, 2),
        ]
        con.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
        con.commit()
        con.close()

        # Minimal leanre.db to verify line enrichment on project dependencies
        lcon = sqlite3.connect(ldb_path)
        lcon.execute("CREATE TABLE declarations(id INTEGER PRIMARY KEY, name TEXT, kind TEXT, module TEXT, line_no INTEGER)")
        lcon.execute("INSERT INTO declarations VALUES (14, 'Proj.A.concrete_lem', 'thm', 'Proj.A', 123)")
        lcon.execute("INSERT INTO declarations VALUES (17, 'Proj.ModA.main_thm', 'thm', 'Proj.ModA', 10)")
        lcon.execute("INSERT INTO declarations VALUES (18, 'Proj.ModB.main_thm_alt', 'thm', 'Proj.ModB', 20)")
        lcon.commit()
        lcon.close()

        res = atlas.compute_alien_twins(db_path, leanre_db_path=ldb_path)
        pair = res["top_alien_pairs_intra"][0]
        pd = pair["proof_diff"]
        c = pd["counts"]

        # E_V(A) = 9, E_V(B) = 8; total edges A=12, B=9
        self.assertEqual(c["a_total"], 12)
        self.assertEqual(c["b_total"], 9)
        self.assertEqual(c["a_ev"], 9)
        self.assertEqual(c["b_ev"], 8)
        self.assertEqual(c["a_proof_only"], 9)
        self.assertEqual(c["b_proof_only"], 6)
        self.assertEqual(c["shared"], 1)         # decl 0
        self.assertEqual(c["moved_role"], 2)     # decl 1 (type->both), decl 2 (value->both)
        self.assertEqual(c["moved_role_v"], 1)   # only decl 2 is in E_V(A) & E_V(B)
        self.assertEqual(c["moved_helper"], 3)   # (3,4), (5,6), (7,8)
        self.assertEqual(c["removed"], 4)        # 9, 11, 13, 14
        self.assertEqual(c["added"], 3)          # 1 (type->both, newly in E_V(B)), 10, 12
        self.assertEqual(c["type_shared"], 1)    # decl 15
        self.assertEqual(c["type_a_only"], 2)    # decl 1, 16
        self.assertEqual(c["type_b_only"], 0)
        self.assertEqual(c["type_diff"], 2)

        # Partition arithmetic
        self.assertEqual(c["removed"] + c["moved_helper"] + c["moved_role_v"] + c["shared"], pair["thm_a"]["ev_size"])
        self.assertEqual(c["added"] + c["moved_helper"] + c["moved_role_v"] + c["shared"], pair["thm_b"]["ev_size"])

        # Moved helper reasons in priority order
        self.assertEqual([(m["a"]["decl_id"], m["b"]["decl_id"], m["reason"]) for m in pd["moved_helper"]], [
            (3, 4, "same_sig"),
            (5, 6, "same_sig_anon"),
            (7, 8, "same_short_name"),
        ])

        # Moved role entries
        self.assertEqual([(m["decl_id"], m["role_a"], m["role_b"]) for m in pd["moved_role"]], [
            (2, "value", "both"),
            (1, "type", "both"),
        ])

        # Distinctive sort order on removed: project ascending fan_in first (name tie-break), Eq.trans (fan_in=5000, mathlib4) last
        self.assertEqual([e["decl_id"] for e in pd["removed"]], [14, 11, 9, 13])
        self.assertEqual(pd["removed"][0]["line"], 123)
        self.assertEqual(pd["removed"][0]["mod"], "Proj.A")
        self.assertEqual(pd["removed"][-1]["origin"], "mathlib4")

        # Type-only diff summary
        self.assertEqual(pd["type_only"]["n_type_shared"], 1)
        self.assertEqual([e["decl_id"] for e in pd["type_only"]["a_only"]], [16, 1])
        self.assertEqual(pd["type_only"]["b_only"], [])

        # Verify truncation flags via _build_pair_proof_diff with tight caps
        dst_info = {
            i: {
                "name": f"Proj.L{i}",
                "kind": "thm",
                "fan_in": i,
                "sighash": None,
                "sighash_anon": None,
                "origin": "project",
                "mod": "Proj",
                "src_decl_id": None,
                "line": None,
            }
            for i in range(10)
        }
        pd_tr = atlas._build_pair_proof_diff(
            {0: 2, 1: 2, 2: 2, 3: 2, 4: 2},
            {0: 2, 5: 2, 6: 2, 7: 2},
            dst_info,
            max_diff=2,
            max_moved=1,
            max_shared=0,
        )
        self.assertEqual(pd_tr["truncated"]["removed"], 2)
        self.assertEqual(pd_tr["truncated"]["added"], 1)
        self.assertEqual(pd_tr["truncated"]["shared"], 1)
        self.assertEqual(len(pd_tr["removed"]), 2)
        self.assertEqual(len(pd_tr["added"]), 2)
        self.assertEqual(len(pd_tr["shared"]), 0)

    def test_emitted_summary_hygiene_if_present(self) -> None:
        repo_summary = os.path.join(atlas._REPO_ROOT, "outputs", "atlas_summary.json")
        if not os.path.isfile(repo_summary):
            return
        sz = os.path.getsize(repo_summary)
        self.assertLessEqual(sz, 2_200_000, f"atlas_summary.json ({sz} B) exceeds 2.2 MB cap")
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
            "top_alien_pairs",
            "top_alien_pairs_intra",
            "top_alien_pairs_cross_repo",
            "top_variant_pairs_intra",
            "top_variant_pairs_cross_repo",
            "top_clone_pairs_intra",
            "top_clone_pairs_cross_repo",
        ):
            self.assertIn(key, at)
            self.assertGreater(len(at[key]), 0)
            for p in at[key]:
                self.assertIn("proof_diff", p)
                c = p["proof_diff"]["counts"]
                self.assertEqual(c["removed"] + c["moved_helper"] + c["moved_role_v"] + c["shared"], p["thm_a"]["ev_size"])
                self.assertEqual(c["added"] + c["moved_helper"] + c["moved_role_v"] + c["shared"], p["thm_b"]["ev_size"])


if __name__ == "__main__":
    unittest.main()
