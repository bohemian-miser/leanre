#!/usr/bin/env python3
"""Unit and cross-engine equivalence test suite for leanre.xrefs (LXRF v1).

License: AGPL-3.0-or-later
"""
from __future__ import annotations

import gzip
import io
import json
import os
import sqlite3
import struct
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from typing import Dict, List, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import xrefs  # noqa: E402


def _build_synthetic_dbs(tmp_dir: str) -> Tuple[str, str]:
    """Build a synthetic kernel.db + leanre.db covering Unicode, non-BMP, hubs, isolated nodes."""
    kdb_path = os.path.join(tmp_dir, "kernel.db")
    ldb_path = os.path.join(tmp_dir, "leanre.db")

    # 12 declarations exercising all kinds, Unicode, non-BMP, high-BMP (>0xE000), apostrophes, isolated node
    decl_specs = [
        (0, "Eq", "inductive", 3, 10, 0, "Init.Core", 101, 12),
        (1, "Nat", "inductive", 3, 12, 0, "Init.Data.Nat", 102, 9),
        (2, "α_helper", "def", 1, 20, 40, "Math.Greek", 103, 4),
        (3, "Foo.bar₂", "thm", 1, 30, 60, "Math.Subscript", 104, 3),
        (4, "Foo.bar'", "thm", 1, 15, 25, "Math.Subscript", 105, 2),
        (5, "ℝ.norm", "def", 2, 18, 35, "Math.Real", 106, 5),
        (6, "AlgebraicGeometry.h𝒰S", "thm", 1, 40, 80, "Math.Geom", 107, 1),
        (7, "HighBMP.\uE001_pua", "opaque", 0, 5, 0, None, None, 0),
        (8, "Isolated.zero", "axiom", 0, 8, 0, None, None, 0),
        (9, "Quot.mk", "quot", 1, 11, 22, "Init.Core", 108, 2),
        (10, "allChi", "thm", 3, 50, 120, "UpperTheory.Main", 109, 10),
        (11, "Foo.bar₀", "thm", 1, 14, 28, "Math.Subscript", 110, 1),
    ]

    # Directed edges (src, dst, kind) with kinds 1=type, 2=value, 3=both
    # Make id=0 ("Eq") have fan_in=5 and id=1 ("Nat") have fan_in=3 (mega-hubs when hub_threshold=3!)
    # Keep id=8 ("Isolated.zero") completely isolated (deg_in=0, deg_out=0)
    edges = [
        (2, 0, 1),
        (2, 1, 2),
        (3, 0, 3),
        (3, 1, 1),
        (3, 2, 2),
        (4, 0, 2),
        (4, 3, 3),
        (5, 0, 1),
        (5, 1, 3),
        (6, 5, 2),
        (6, 9, 1),
        (7, 6, 3),
        (10, 0, 3),
        (10, 3, 2),
        (10, 4, 1),
        (10, 6, 2),
        (10, 11, 3),
        (11, 2, 1),
    ]

    # Compute exact degrees for decls table
    fan_in = [0] * len(decl_specs)
    fan_out = [0] * len(decl_specs)
    fan_out_t = [0] * len(decl_specs)
    fan_out_v = [0] * len(decl_specs)
    for s, d, k in edges:
        fan_out[s] += 1
        if k & 1:
            fan_out_t[s] += 1
        if k & 2:
            fan_out_v[s] += 1
        fan_in[d] += 1

    kconn = sqlite3.connect(kdb_path)
    kconn.executescript(
        """
        CREATE TABLE decls(
            id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
            n_consts INTEGER NOT NULL, type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL,
            fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
            fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL,
            flags INTEGER NOT NULL, live_mask INTEGER NOT NULL,
            stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL
        );
        CREATE TABLE edges(
            src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL,
            PRIMARY KEY(src, dst)
        ) WITHOUT ROWID;
        CREATE TABLE decl_module(
            decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER
        );
        CREATE TABLE dom(
            tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER,
            depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL,
            PRIMARY KEY(tree_id, decl_id)
        ) WITHOUT ROWID;
        """
    )
    for did, nm, kd, lmask, tnodes, vnodes, mod, sid, dsz in decl_specs:
        kconn.execute(
            "INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (did, nm, kd, 1, tnodes, vnodes, fan_in[did], fan_out[did], fan_out_t[did], fan_out_v[did], 0, lmask, 0, 0, 0),
        )
        if mod is not None:
            kconn.execute("INSERT INTO decl_module VALUES (?,?,?,?)", (did, mod, "exact", sid))
        if dsz > 0:
            kconn.execute("INSERT INTO dom VALUES (?,?,?,?,?)", (0, did, None, 0, dsz))
    kconn.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
    kconn.commit()
    kconn.close()

    lconn = sqlite3.connect(ldb_path)
    lconn.executescript(
        """
        CREATE TABLE modules(
            id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL, lines INTEGER NOT NULL,
            decl_count INTEGER NOT NULL, dom_subtree_size INTEGER NOT NULL
        );
        CREATE TABLE module_edges(src TEXT NOT NULL, dst TEXT NOT NULL, PRIMARY KEY(src, dst));
        CREATE TABLE declarations(
            id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
            module TEXT NOT NULL, line_no INTEGER NOT NULL
        );
        """
    )
    mods = sorted({sp[6] for sp in decl_specs if sp[6] is not None})
    for idx, m in enumerate(mods):
        lconn.execute("INSERT INTO modules VALUES (?,?,?,?,?)", (idx, m, 100 + idx * 10, 2, idx + 1))
    lconn.executemany(
        "INSERT INTO module_edges VALUES (?,?)",
        [
            ("UpperTheory.Main", "Math.Subscript"),
            ("UpperTheory.Main", "Math.Geom"),
            ("Math.Subscript", "Math.Greek"),
            ("Math.Geom", "Math.Real"),
            ("Math.Greek", "Init.Core"),
            ("Math.Greek", "Init.Data.Nat"),
        ],
    )
    for did, nm, kd, _, _, _, mod, sid, _ in decl_specs:
        if mod is not None and sid is not None:
            lconn.execute("INSERT INTO declarations VALUES (?,?,?,?,?)", (sid, nm, kd, mod, 10 + did * 7))
    lconn.commit()
    lconn.close()

    return kdb_path, ldb_path


class TestLxrfCodec(unittest.TestCase):
    def test_adj_roundtrip_edge_cases(self) -> None:
        # Test 0 edges, 1..7 edges (2-bit packing boundaries), large LEB128 gaps, HUB_SENTINEL
        adj_fwd = [
            [],
            [(0, 1)],
            [(0, 2), (1, 3)],
            [(5, 1), (133, 2), (100000, 3)],
            [(10, 1), (11, 2), (12, 3), (13, 1), (2000000, 2)],
        ]
        raw = xrefs.encode_adj_shard(xrefs.DIR_FWD, 100, adj_fwd)
        dec = xrefs.decode_adj_shard(xrefs.gzip_compress_bytes(raw))
        self.assertEqual(dec["dir"], xrefs.DIR_FWD)
        self.assertEqual(dec["start_id"], 100)
        self.assertEqual(dec["count"], 5)
        self.assertEqual(dec["adj"], adj_fwd)
        self.assertEqual(dec["total_edges"], 11)

        # Reverse shard with HUB_SENTINEL
        adj_rev = [None, [(3, 2), (10, 3)], None]
        raw_rev = xrefs.encode_adj_shard(xrefs.DIR_REV, 0, adj_rev)
        dec_rev = xrefs.decode_adj_shard(raw_rev)
        self.assertEqual(dec_rev["degrees"], [xrefs.HUB_SENTINEL, 2, xrefs.HUB_SENTINEL])
        self.assertEqual(dec_rev["adj"], adj_rev)

        # Rev hub shard
        hub_edges = [(0, 1), (1, 2), (2, 3), (999999, 1)]
        raw_hub = xrefs.encode_adj_shard(xrefs.DIR_REV_HUB, 42, [hub_edges])
        dec_hub = xrefs.decode_adj_shard(raw_hub)
        self.assertEqual(dec_hub["dir"], xrefs.DIR_REV_HUB)
        self.assertEqual(dec_hub["start_id"], 42)
        self.assertEqual(dec_hub["adj"], [hub_edges])

    def test_decoder_strict_invariants(self) -> None:
        valid = bytearray(xrefs.encode_adj_shard(xrefs.DIR_FWD, 0, [[(0, 1), (5, 3)]]))
        # Bad magic
        bad = bytearray(valid)
        bad[0] = ord("X")
        with self.assertRaises(ValueError):
            xrefs.decode_adj_shard(bytes(bad))
        # Trailing byte breaks exact end-of-buffer invariant
        with self.assertRaises(ValueError):
            xrefs.decode_adj_shard(bytes(valid) + b"\x00")
        # Truncated buffer
        with self.assertRaises(ValueError):
            xrefs.decode_adj_shard(bytes(valid[:-1]))
        # Non-zero padding bits in final kind byte
        bad_pad = bytearray(valid)
        bad_pad[-1] |= 0xF0
        with self.assertRaises(ValueError):
            xrefs.decode_adj_shard(bytes(bad_pad))
        # Invalid edge kind 0
        bad_kind = bytearray(valid)
        bad_kind[-1] &= ~0x03
        with self.assertRaises(ValueError):
            xrefs.decode_adj_shard(bytes(bad_kind))

    def test_utf16_ordering_matches_js(self) -> None:
        # In JS UTF-16 code units:
        #   'Foo.bar\'' (0x27) < 'Foo.bar₀' (0x2080) < 'Foo.bar₂' (0x2082)
        #   non-BMP '𝒰' (U+1D4B0 -> 0xD835 0xDCB0) < high-BMP '\uE001' (0xE001)!
        items = ["\uE001", "𝒰", "Foo.bar₂", "Foo.bar'", "Foo.bar₀", "Eq", "ℝ"]
        got = sorted(items, key=xrefs.utf16_key)
        expected = ["Eq", "Foo.bar'", "Foo.bar₀", "Foo.bar₂", "ℝ", "𝒰", "\uE001"]
        self.assertEqual(got, expected)


class TestKernelPythonAndCEquivalence(unittest.TestCase):
    def test_python_equals_c_bit_for_bit_payloads(self) -> None:
        fast_bin = xrefs.compile_fast_binary()
        self.assertIsNotNone(fast_bin, "xref_fast.c must compile cleanly with gcc")

        with tempfile.TemporaryDirectory() as tmp:
            kdb, ldb = _build_synthetic_dbs(tmp)
            out_py = os.path.join(tmp, "out_py")
            out_c = os.path.join(tmp, "out_c")

            mf_py = xrefs.export_kernel(
                kdb,
                out_py,
                leanre_db=ldb,
                shard_size=4,
                meta_shard_size=5,
                name_shards=4,
                hub_threshold=3,
                use_c=False,
            )
            mf_c = xrefs.export_kernel(
                kdb,
                out_c,
                leanre_db=ldb,
                shard_size=4,
                meta_shard_size=5,
                name_shards=4,
                hub_threshold=3,
                use_c=True,
                threads=2,
            )

            # Compare every semantic field of manifest.json
            for key in (
                "schema",
                "mode",
                "n_decls",
                "n_edges",
                "edge_kind_counts",
                "shard_size",
                "n_shards",
                "meta_shard_size",
                "n_meta_shards",
                "name_shards",
                "name_order",
                "name_ranges",
                "hub_threshold",
                "rev_hub_ids",
                "kind_labels",
                "modules_url",
                "n_modules",
                "paths",
                "pad",
                "meta_columns",
                "name_columns",
            ):
                self.assertEqual(mf_py[key], mf_c[key], f"manifest mismatch on key {key!r}")

            # Verify mega-hubs id=0 (fan_in=5) and id=1 (fan_in=3) were split
            self.assertEqual(mf_c["rev_hub_ids"], [0, 1])

            # Compare decompressed bytes of EVERY .lxrf shard between C and Python!
            def _collect_lxrf(root: str) -> Dict[str, bytes]:
                found: Dict[str, bytes] = {}
                for dp, _, fns in os.walk(root):
                    for fn in fns:
                        if fn.endswith(".lxrf"):
                            full = os.path.join(dp, fn)
                            rel = os.path.relpath(full, root)
                            with open(full, "rb") as f:
                                gz = f.read()
                            self.assertTrue(xrefs.is_gzip(gz), f"{rel} missing gzip magic")
                            found[rel] = gzip.decompress(gz)
                return found

            py_files = _collect_lxrf(out_py)
            c_files = _collect_lxrf(out_c)
            self.assertEqual(set(py_files.keys()), set(c_files.keys()))
            for rel in sorted(py_files):
                self.assertEqual(
                    py_files[rel],
                    c_files[rel],
                    f"Decompressed payload mismatch between Python and C on {rel}",
                )

            # Run full verifier on both outputs
            rep_py = xrefs.verify_xrefs(out_py, kernel_db=kdb, leanre_db=ldb, sample_decls=12, sample_names=12)
            rep_c = xrefs.verify_xrefs(out_c, kernel_db=kdb, leanre_db=ldb, sample_decls=12, sample_names=12)
            self.assertTrue(rep_py["ok"])
            self.assertTrue(rep_c["ok"])
            self.assertEqual(rep_c["checked_decls"], 12)
            self.assertEqual(rep_c["checked_names"], 12)

            # Verify exact binary search & prefix search on Unicode + non-BMP + high-BMP names
            store = xrefs.XrefStore(out_c)
            for name, exp_id in [
                ("Eq", 0),
                ("Foo.bar₂", 3),
                ("Foo.bar'", 4),
                ("Foo.bar₀", 11),
                ("ℝ.norm", 5),
                ("AlgebraicGeometry.h𝒰S", 6),
                ("HighBMP.\uE001_pua", 7),
                ("Isolated.zero", 8),
                ("allChi", 10),
            ]:
                hit = store.lookup_name(name)
                self.assertIsNotNone(hit, f"Missing lookup_name({name!r})")
                assert hit is not None
                self.assertEqual(hit["decl_id"], exp_id)
            self.assertIsNone(store.lookup_name("DoesNotExist.foo"))

            # Verify prefix search across shard boundary
            pref = [r["name"] for r in store.prefix_search("Foo.bar", limit=10)]
            self.assertEqual(pref, ["Foo.bar'", "Foo.bar₀", "Foo.bar₂"])

            # Verify isolated node & hub node queries
            self.assertEqual(store.get_fwd(8), [])
            self.assertEqual(store.get_rev(8), [])
            self.assertEqual(store.get_rev(0), [(2, 1), (3, 3), (4, 2), (5, 1), (10, 3)])
            self.assertEqual(store.get_meta(10)["line_no"], 10 + 10 * 7)
            self.assertEqual(store.get_meta(10)["dom_size"], 10)
            self.assertEqual(store.get_meta(8)["mod_idx"], -1)
            self.assertIsNone(store.get_meta(8)["module"])


class TestSourceModeAndCli(unittest.TestCase):
    def test_source_mode_from_leanre_db(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            _, ldb = _build_synthetic_dbs(tmp)
            out_src = os.path.join(tmp, "out_src")
            mf = xrefs.export_source(out_src, leanre_db=ldb, shard_size=8, meta_shard_size=8, name_shards=2)
            self.assertEqual(mf["mode"], "source")
            self.assertEqual(mf["schema"], xrefs.SCHEMA)
            self.assertIn("module", mf["kind_labels"])
            # 7 modules + 10 declarations = 17 nodes
            self.assertEqual(mf["n_decls"], 17)
            # 6 module import edges (type) + 10 decl->module edges (value) = 16 edges
            self.assertEqual(mf["n_edges"], 16)
            self.assertEqual(mf["edge_kind_counts"], {"type": 6, "value": 10, "both": 0})

            rep = xrefs.verify_xrefs(out_src)
            self.assertTrue(rep["ok"])

            store = xrefs.XrefStore(out_src)
            hit = store.lookup_name("UpperTheory.Main")
            self.assertIsNotNone(hit)
            assert hit is not None
            # UpperTheory.Main imports Math.Subscript and Math.Geom
            fwd_names = sorted(store.get_meta(t)["name"] for t, _ in store.get_fwd(hit["decl_id"]))
            self.assertEqual(fwd_names, ["Math.Geom", "Math.Subscript"])
            # allChi belongs to UpperTheory.Main
            rev_names = [store.get_meta(s)["name"] for s, _ in store.get_rev(hit["decl_id"])]
            self.assertIn("allChi", rev_names)

    def test_source_mode_from_tiny_demo_dir(self) -> None:
        demo_dir = os.path.join(_REPO_ROOT, "examples", "tiny_demo")
        if not os.path.isdir(demo_dir):
            self.skipTest("examples/tiny_demo not present")
        with tempfile.TemporaryDirectory() as tmp:
            out_dir = os.path.join(tmp, "tiny_xrefs")
            mf = xrefs.export_source(out_dir, src_dir=demo_dir)
            self.assertEqual(mf["mode"], "source")
            self.assertGreater(mf["n_decls"], 0)
            self.assertGreater(mf["n_edges"], 0)
            rep = xrefs.verify_xrefs(out_dir)
            self.assertTrue(rep["ok"])

    def test_cli_roundtrip(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            kdb, ldb = _build_synthetic_dbs(tmp)
            out_dir = os.path.join(tmp, "cli_out")
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = xrefs.main(["kernel", "--kernel-db", kdb, "--leanre-db", ldb, "--out-dir", out_dir])
            self.assertEqual(rc, 0)
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = xrefs.main(["verify", out_dir, "--kernel-db", kdb, "--leanre-db", ldb])
            self.assertEqual(rc, 0)
            rep = json.loads(buf.getvalue())
            self.assertTrue(rep["ok"])
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = xrefs.main(["query", out_dir, "--name", "Foo.bar₂"])
            self.assertEqual(rc, 0)
            q = json.loads(buf.getvalue())
            self.assertEqual(q["meta"]["decl_id"], 3)


if __name__ == "__main__":
    unittest.main()
