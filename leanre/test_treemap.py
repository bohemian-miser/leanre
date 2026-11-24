#!/usr/bin/env python3
"""Comprehensive unit tests for `leanre/treemap.py` (`leanre.treemap/1`)."""
from __future__ import annotations

import gzip
import json
import os
import sqlite3
import sys
import tempfile
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import treemap as tm  # noqa: E402


def _make_synthetic_kernel_db(db_path: str) -> None:
    """Create a multi-level synthetic `kernel.db` with pillars, small subtrees, and giant fan-out."""
    con = sqlite3.connect(db_path)
    con.executescript(
        """
        CREATE TABLE decls(
            id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
            value_nodes INTEGER NOT NULL, sighash TEXT
        );
        CREATE TABLE dom(
            tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER,
            depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL,
            PRIMARY KEY(tree_id, decl_id)
        );
        CREATE TABLE decl_module(
            decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER
        );
        """
    )
    # Build tree:
    # 1: allChi (idom=None, depth=0)
    #   2: UpperTheory.FinalTheorems.everyCharacter (idom=1)
    #     3: UpperTheory.Lit.every_character_of_theta_integrals_local_matching (Pillar A, idom=2)
    #        10..29: 20 children (each with 1 leaf 100..119) -> subtree_size=41
    #     4: UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter (Pillar B, idom=2)
    #        30..44: 15 direct leaves -> subtree_size=16
    #     50..69: 20 direct small leaves under everyCharacter (tests interior residual group!)
    # 90: Mathlib.Analysis.Helper (idom=None, external library root, subtree_size=1)
    nodes = []  # (id, idom, depth, name, kind, vn, sh, mod, method, src_id)
    nodes.append((1, None, 0, "allChi", "thm", 5, "k1n:0000000000000001", "Main", "leanre_db:exact", 1))
    nodes.append((2, 1, 1, "UpperTheory.FinalTheorems.everyCharacter", "thm", 12, "k1n:0000000000000002", "Core.Main", "leanre_db:exact", 2))
    nodes.append((3, 2, 2, "UpperTheory.Lit.every_character_of_theta_integrals_local_matching", "thm", 50, "k1n:0000000000000003", "PillarA.Top", "leanre_db:exact", 3))
    nodes.append((4, 2, 2, "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter", "thm", 40, "k1n:0000000000000004", "PillarB.Top", "leanre_db:exact", 4))

    for i in range(20):
        mid = 10 + i
        leaf = 100 + i
        nodes.append((mid, 3, 3, f"PillarA.Mid.step_{i}", "thm", 30 + i, f"k1n:{mid:016x}", "PillarA.Mid", "leanre_db:exact", 10 + i))
        nodes.append((leaf, mid, 4, f"PillarA.Leaf.lem_{i}", "def", 10, f"k1n:{leaf:016x}", "PillarA.Leaf", "leanre_db:exact", 100 + i))

    for i in range(15):
        bid = 30 + i
        nodes.append((bid, 4, 3, f"PillarB.Step.gal_{i}", "thm", 25, f"k1n:{bid:016x}", "PillarB.Step", "leanre_db:exact", 30 + i))

    for i in range(20):
        sid = 50 + i
        nodes.append((sid, 2, 2, f"Shared.Aux.helper_{i}", "thm", 8, f"k1n:{sid:016x}", "Shared.Aux", "leanre_db:exact", 50 + i))

    nodes.append((90, None, 0, "Mathlib.Analysis.Helper", "thm", 100, "k1n:0000000000000090", None, "unmatched:library_or_external", None))

    # Compute exact subtree sizes bottom-up
    ch_map = {}
    for row in nodes:
        ch_map.setdefault(row[1], []).append(row[0])

    sz_map = {}
    def _calc(u: int) -> int:
        s = 1 + sum(_calc(c) for c in ch_map.get(u, ()))
        sz_map[u] = s
        return s

    for root_id in ch_map.get(None, ()):
        _calc(root_id)

    for did, idom, depth, name, kind, vn, sh, mod, method, src_id in nodes:
        con.execute("INSERT INTO decls VALUES (?,?,?,?,?)", (did, name, kind, vn, sh))
        con.execute("INSERT INTO dom VALUES (0,?,?,?,?)", (did, idom, depth, sz_map[did]))
        con.execute("INSERT INTO decl_module VALUES (?,?,?,?)", (did, mod, method, src_id))

    con.commit()
    con.close()


def _make_synthetic_leanre_db(db_path: str) -> None:
    con = sqlite3.connect(db_path)
    con.executescript(
        """
        CREATE TABLE modules(
            id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL, file_path TEXT NOT NULL,
            lines INTEGER NOT NULL, decl_count INTEGER NOT NULL, bfs_depth INTEGER NOT NULL,
            zlib_ratio REAL NOT NULL
        );
        CREATE TABLE declarations(
            id INTEGER PRIMARY KEY, name TEXT NOT NULL, line_no INTEGER NOT NULL
        );
        CREATE TABLE forensic_hits(
            id INTEGER PRIMARY KEY, tag TEXT NOT NULL, module TEXT NOT NULL
        );
        """
    )
    mods = [
        (1, "Main", "Main.lean", 20, 1, 0, 0.4),
        (2, "Core.Main", "Core/Main.lean", 100, 1, 1, 0.3),
        (3, "PillarA.Top", "PillarA/Top.lean", 150, 1, 2, 0.25),
        (4, "PillarA.Mid", "PillarA/Mid.lean", 400, 20, 3, 0.2),
        (5, "PillarA.Leaf", "PillarA/Leaf.lean", 300, 20, 4, 0.22),
        (6, "PillarB.Top", "PillarB/Top.lean", 80, 1, 2, 0.35),
        (7, "PillarB.Step", "PillarB/Step.lean", 250, 15, 3, 0.21),
        (8, "Shared.Aux", "Shared/Aux.lean", 200, 20, 2, 0.19),
        (9, "Unused.Orphan", "Unused/Orphan.lean", 50, 2, -1, 0.5),
    ]
    con.executemany("INSERT INTO modules VALUES (?,?,?,?,?,?,?)", mods)
    con.executemany(
        "INSERT INTO declarations VALUES (?,?,?)",
        [(1, "allChi", 12), (2, "UpperTheory.FinalTheorems.everyCharacter", 44), (3, "UpperTheory.Lit.every_character_of_theta_integrals_local_matching", 9)],
    )
    con.commit()
    con.close()


def _make_synthetic_tier2_db(db_path: str) -> None:
    con = sqlite3.connect(db_path)
    con.execute("CREATE TABLE kernel_matches(decl_id INTEGER NOT NULL, variant TEXT NOT NULL)")
    # Mark 5 declarations as Mathlib-matched
    con.executemany("INSERT INTO kernel_matches VALUES (?, 'k1n')", [(10, ), (11, ), (12, ), (30, ), (50, )])
    con.commit()
    con.close()


def _make_synthetic_source_tree(src_dir: str) -> None:
    files = {
        "Main.lean": (
            "-- Entry module comment\n"
            "import Alpha.Core\n"
            "import Beta.ChallengeSpec\n"
            "theorem main_thm : True := by\n"
            "  trivial\n"
        ),
        "Alpha/Core.lean": (
            "/- Multi-line\n"
            "   block comment -/\n"
            "set_option maxHeartbeats 800000\n"
            "namespace Alpha\n"
            "theorem core_lemma_1 : True := by\n"
            "  sorry\n"
            "set_option maxHeartbeats 1600000\n"
            "def core_def_2 : Nat := 42\n"
            "end Alpha\n"
        ),
        "Beta/ChallengeSpec.lean": (
            "-- Challenge spec file with intentional sorry\n"
            "theorem challenge_goal : True := by\n"
            "  sorry\n"
        ),
        "Orphan/DeadFile.lean": (
            "theorem dead_lemma : True := by\n"
            "  trivial\n"
        ),
    }
    for rel, content in files.items():
        full = os.path.join(src_dir, rel)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w", encoding="utf-8") as f:
            f.write(content)


class TestTreemap(unittest.TestCase):
    def test_gzip_roundtrip_and_magic(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = os.path.join(td, "sample.lxrt")
            payload = {"schema": tm.TREE_SCHEMA, "rows": [[0, -1, "Main"]]}
            n_bytes = tm.write_lxrt(p, payload)
            self.assertGreater(n_bytes, 0)
            with open(p, "rb") as f:
                magic = f.read(2)
            self.assertEqual(magic, b"\x1f\x8b")
            # Raw gzip decompress matches read_lxrt
            with open(p, "rb") as f:
                raw = json.loads(gzip.decompress(f.read()).decode("utf-8"))
            self.assertEqual(raw, payload)
            self.assertEqual(tm.read_lxrt(p), payload)

    def test_kernel_dom_and_tiles_invariants(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            kdb = os.path.join(td, "kernel.db")
            ldb = os.path.join(td, "leanre.db")
            t2db = os.path.join(td, "tier2.db")
            out_dir = os.path.join(td, "out")
            _make_synthetic_kernel_db(kdb)
            _make_synthetic_leanre_db(ldb)
            _make_synthetic_tier2_db(t2db)

            res = tm.export_kernel_treemap(
                kdb,
                out_dir,
                slug="synth-rh",
                leanre_db=ldb,
                tier2_db=t2db,
                min_subtree=15,
                min_residual_group=10,
                max_tile_rows=100,
                workers=1,
            )
            self.assertEqual(res["manifest"]["schema"], tm.MANIFEST_SCHEMA)
            self.assertEqual(res["manifest"]["mode"], "kernel")
            self.assertEqual(len(res["manifest"]["views"]), 2)

            # Verify every file, gzip header, and parent >= sum(children) invariant across all tiles!
            vrep = tm.verify_treemap_dir(out_dir)
            self.assertTrue(vrep["ok"], f"verify failed: {vrep['errors']}")
            # Total live decls = 1 + 1 + 1 + 1 + 40 + 15 + 20 + 1 = 80
            self.assertEqual(vrep["views"]["dom"]["root_sz"], 80)
            self.assertEqual(vrep["views"]["dom"]["root_loc"], 1550)
            self.assertEqual(vrep["views"]["dom"]["root_mods"], 9)
            self.assertGreater(vrep["views"]["dom"]["verified_tiles"], 0)

            # Check pillar attribution and line join in dom.lxrt
            dom_tree = tm.read_lxrt(os.path.join(out_dir, "dom.lxrt"))
            cols = dom_tree["cols"]
            self.assertEqual(cols, tm.COLS)
            by_name = {r[cols.index("name")]: r for r in dom_tree["rows"]}
            pillars = dom_tree["tables"]["pillars"]
            self.assertEqual(pillars[by_name["allChi"][cols.index("pillar")]], "Spine")
            self.assertIn("Pillar A", pillars[by_name["UpperTheory.Lit.every_character_of_theta_integrals_local_matching"][cols.index("pillar")]])
            self.assertIn("Pillar B", pillars[by_name["UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter"][cols.index("pillar")]])
            self.assertEqual(by_name["allChi"][cols.index("line")], 12)
            self.assertEqual(by_name["allChi"][cols.index("hash")], "k1n:0000000000000001")
            # Interior residual group for everyCharacter's 20 small children must exist and have a tile!
            other_key = "UpperTheory.FinalTheorems.everyCharacter/[other]"
            self.assertIn(other_key, by_name)
            self.assertTrue(by_name[other_key][cols.index("tile")])

    def test_source_folder_exporter_metrics_and_no_proof_bodies(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            src_dir = os.path.join(td, "src")
            out_dir = os.path.join(td, "out")
            _make_synthetic_source_tree(src_dir)

            res = tm.export_source_treemap(
                src_dir,
                out_dir,
                slug="synth-src",
                inline_file_limit=100,
                workers=1,
            )
            self.assertEqual(res["manifest"]["mode"], "source")
            vrep = tm.verify_treemap_dir(out_dir)
            self.assertTrue(vrep["ok"], f"verify failed: {vrep['errors']}")

            tree = tm.read_lxrt(os.path.join(out_dir, "folder.lxrt"))
            cols = tree["cols"]
            root = tree["rows"][0]
            # 4 files total, 1 orphan (Orphan/DeadFile.lean)
            self.assertEqual(root[cols.index("mods")], 4)
            self.assertEqual(root[cols.index("hb_cnt")], 2)
            self.assertEqual(root[cols.index("hb_max")], 1600000)
            self.assertEqual(root[cols.index("sorry_p")], 1)
            self.assertEqual(root[cols.index("sorry_c")], 1)
            self.assertGreater(root[cols.index("comment_pct")], 0.0)
            self.assertAlmostEqual(root[cols.index("orphan_pct")], 0.25, places=4)

            # Verify zero verbatim .lean proof body tokens (`:= by`, `trivial`) in serialized JSON
            raw_text = json.dumps(tree)
            self.assertNotIn(":= by", raw_text)
            self.assertNotIn("trivial", raw_text)

    def test_source_folder_tiling_chunking(self) -> None:
        """Force lazy folder tiles + chunk splitting via tiny inline_file_limit & max_tile_rows."""
        with tempfile.TemporaryDirectory() as td:
            src_dir = os.path.join(td, "src")
            out_dir = os.path.join(td, "out")
            for i in range(12):
                p = os.path.join(src_dir, "BigDir", f"Mod{i:02d}.lean")
                os.makedirs(os.path.dirname(p), exist_ok=True)
                with open(p, "w", encoding="utf-8") as f:
                    f.write(f"theorem t_{i} : True := by\n  trivial\n")
            tm.export_source_treemap(
                src_dir,
                out_dir,
                slug="chunk-test",
                inline_file_limit=2,
                max_tile_rows=5,
                workers=1,
            )
            vrep = tm.verify_treemap_dir(out_dir)
            self.assertTrue(vrep["ok"], f"verify failed: {vrep['errors']}")
            self.assertGreaterEqual(vrep["views"]["folder"]["verified_tiles"], 2)
            self.assertEqual(vrep["views"]["folder"]["root_mods"], 12)

    def test_overlay_compiler_trust_separation_contested_and_dossiers(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            ann_dir = os.path.join(td, "annotations")
            contrib_dir = os.path.join(ann_dir, "contrib", "demo-proj")
            an_dir = os.path.join(td, "analysis")
            os.makedirs(contrib_dir, exist_ok=True)
            os.makedirs(an_dir, exist_ok=True)

            # Human verified pack
            with open(os.path.join(ann_dir, "human__facts.jsonl"), "w", encoding="utf-8") as f:
                f.write(json.dumps({"schema": "leanre.annot/1", "type": "pack"}) + "\n")
                f.write(json.dumps({
                    "type": "layer", "layer": "human/facts", "kind": "human",
                    "default_on": True, "title": "Human Facts",
                }) + "\n")
                f.write(json.dumps({
                    "type": "annot", "target": "decl", "name": "Foo.Bar",
                    "layer": "human/facts", "tag": "L", "author": "@alice",
                    "note": "Checked signature.", "source": "Main.lean#L1",
                    "created": "2026-01-01T00:00:00Z", "updated": "2026-01-01T00:00:00Z",
                }) + "\n")

            # Malicious/misconfigured AI draft pack trying to set default_on=True AND flagging Foo.Bar
            with open(os.path.join(contrib_dir, "ai__audit.jsonl"), "w", encoding="utf-8") as f:
                f.write(json.dumps({"schema": "leanre.annot/1", "type": "pack"}) + "\n")
                f.write(json.dumps({
                    "type": "layer", "layer": "ai/audit", "kind": "ai-draft",
                    "default_on": True, "title": "AI Audit",
                }) + "\n")
                f.write(json.dumps({
                    "type": "annot", "target": "decl", "name": "Foo.Bar",
                    "layer": "ai/audit", "tag": "M", "author": "ai:bot",
                    "draft": False, "status": "flagged",
                    "note": "Suspect lemma := by simp", "breaks": "heuristic",
                    "source": "bot", "created": "2026-01-01T00:00:00Z", "updated": "2026-01-01T00:00:00Z",
                }) + "\n")

            # Dossier referencing Foo.Bar
            with open(os.path.join(an_dir, "foo_audit.md"), "w", encoding="utf-8") as f:
                f.write("# Foo Audit Dossier\n\nDetailed review of `Foo.Bar`.\n\n```lean\ntheorem secret_proof := by sorry\n```\n")

            out_ov = os.path.join(td, "overlay.json")
            ov = tm.build_overlay_json(
                ann_dir,
                analysis_dir=an_dir,
                out_path=out_ov,
                project="demo-proj",
                known_names={"Foo.Bar"},
            )
            self.assertEqual(ov["schema"], tm.OVERLAY_SCHEMA)
            layers_by_id = {l["id"]: l for l in ov["layers"]}
            # Trust separation: AI layer MUST be forced default_on=False!
            self.assertTrue(layers_by_id["human/facts"]["default_on"])
            self.assertFalse(layers_by_id["ai/audit"]["default_on"])
            self.assertEqual(layers_by_id["ai/audit"]["kind"], "ai-draft")
            self.assertIn("dossiers/index", layers_by_id)

            # Contested detection: verified + flagged on Foo.Bar -> contested=True!
            foo_entries = ov["entries"]["Foo.Bar"]
            self.assertEqual(len(foo_entries), 3)
            self.assertTrue(all(e["contested"] for e in foo_entries))
            self.assertEqual(ov["stats"]["contested_targets"], 1)

            # AI record forced draft=True and `:= by` scrubbed; dossier code block stripped
            with open(out_ov, "r", encoding="utf-8") as f:
                raw_ov = f.read()
            self.assertNotIn(":= by", raw_ov)
            self.assertNotIn("secret_proof", raw_ov)
            ai_entry = [e for e in foo_entries if e["layer"] == "ai/audit"][0]
            self.assertTrue(ai_entry["draft"])

    def test_cli_source_and_verify_and_symlink_refusal(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            src_dir = os.path.join(td, "src")
            out_dir = os.path.join(td, "out")
            _make_synthetic_source_tree(src_dir)
            rc = tm.main(["source", "--src-dir", src_dir, "--slug", "cli-demo", "--out", out_dir, "--workers", "1"])
            self.assertEqual(rc, 0)
            rc_v = tm.main(["verify", out_dir])
            self.assertEqual(rc_v, 0)

            # Symlink output refusal
            real_target = os.path.join(td, "real.lxrt")
            link_path = os.path.join(td, "link.lxrt")
            os.symlink(real_target, link_path)
            with self.assertRaises(ValueError):
                tm.write_lxrt(link_path, {"ok": True})


if __name__ == "__main__":
    unittest.main()
