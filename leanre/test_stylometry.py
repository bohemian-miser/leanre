#!/usr/bin/env python3
"""Unit tests for `leanre.stylometry`."""
from __future__ import annotations

import io
import json
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import stylometry  # noqa: E402

TINY_DEMO_DIR = os.path.join(_REPO_ROOT, "examples", "tiny_demo")


class TestStylometry(unittest.TestCase):
    def test_comment_lines_and_max_heartbeats_counter(self) -> None:
        sample = (
            "-- header comment\n"
            "set_option maxHeartbeats 400000\n"
            "/- block start\n"
            "   /- nested comment set_option maxHeartbeats 999 -/\n"
            "   still inside block -/\n"
            'def msg : String := "-- not a comment and /- not block"\n'
            "theorem t : True := trivial -- inline comment\n"
            "set_option maxHeartbeats 0 -- another override\n"
        ).encode("utf-8")
        lines_wc, comment_lines, hb = stylometry.count_lean_comment_lines_and_heartbeats(sample)
        self.assertEqual(lines_wc, 8)
        # Lines 1, 3, 4, 5, 7, 8 contain comments; lines 2 and 6 do not
        self.assertEqual(comment_lines, 6)
        # Only lines 2 and 8 have real `set_option maxHeartbeats` (line 4 is commented out)
        self.assertEqual(hb, 2)

        # Commentless fast path
        fast = b"theorem a : True := trivial\nset_option maxHeartbeats 100000\n"
        l2, c2, h2 = stylometry.count_lean_comment_lines_and_heartbeats(fast)
        self.assertEqual((l2, c2, h2), (2, 0, 1))

    def test_name_compress_ratio_templated_vs_diverse(self) -> None:
        templated = [f"AutoGen.Block.lemma_step_{i:04d}_aux" for i in range(120)]
        diverse = [
            "RiemannZeta.analyticContinuation",
            "EulerProduct.convergesHalfPlane",
            "DirichletCharacter.orthogonality",
            "NavierStokes.vorticityStretchingBound",
            "Carleson.dyadicTreeSelection",
            "Viazovska.modularFormRadialLaplace",
            "Fermat.freyCurveSemistable",
            "Hironaka.principalizationIdealSheaf",
            "Kato.logarithmicCrystallineCohomology",
            "Siegel.thetaSeriesFunctionalEquation",
            "HarishChandra.orbitalIntegralAsymptotics",
            "Arakelov.hermitianLatticeSuccessiveMinima",
        ]
        r_tmpl = stylometry.compute_name_compress_ratio(templated)
        r_div = stylometry.compute_name_compress_ratio(diverse)
        self.assertGreater(r_tmpl, 0.0)
        self.assertLess(r_tmpl, r_div)
        self.assertEqual(stylometry.compute_name_compress_ratio([]), 0.0)

    def test_compute_project_stylometry_tiny_demo_and_cli(self) -> None:
        row = stylometry.compute_project_stylometry(
            src_dir=TINY_DEMO_DIR,
            slug="tiny-demo",
            title="Tiny Demo",
            path="p/tiny-demo",
            license_label="AGPL-3.0-or-later OR MIT-0",
            category="demo",
            has_kernel_export=True,
            has_embedding_2d=True,
            workers=1,
        )
        required_keys = [
            "slug", "title", "path", "files", "lines", "decls", "defs", "thms", "inds",
            "comment_lines", "comment_pct", "max_heartbeats_overrides", "name_compress_ratio",
            "avg_decl_lines", "median_file_lines", "reach_modules", "reach_pct",
            "orphan_modules", "orphan_pct", "exact_clone_clusters", "sig_clone_clusters",
            "misfile_count", "misfile_pct", "proof_sorry", "challenge_sorry", "axioms",
            "decide_kernel", "license", "has_kernel_export", "has_embedding_2d", "category",
        ]
        for k in required_keys:
            self.assertIn(k, row, f"Missing stylometry key {k}")
        self.assertEqual(row["files"], 5)
        self.assertEqual(row["reach_modules"], 4)
        self.assertEqual(row["orphan_modules"], 1)
        self.assertAlmostEqual(row["reach_pct"], 80.0)
        self.assertAlmostEqual(row["orphan_pct"], 20.0)
        self.assertGreater(row["comment_lines"], 0)
        self.assertGreater(row["name_compress_ratio"], 0.0)
        self.assertGreater(row["avg_decl_lines"], 0.0)
        self.assertGreater(row["median_file_lines"], 0.0)
        self.assertEqual(row["proof_sorry"], 0)
        self.assertEqual(row["challenge_sorry"], 0)

        # CLI test writing --out
        with tempfile.TemporaryDirectory() as td:
            out_json = os.path.join(td, "corpus_comparison.json")
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = stylometry.main([TINY_DEMO_DIR, "--out", out_json, "--workers", "1"])
            self.assertEqual(rc, 0)
            with open(out_json, "r", encoding="utf-8") as f:
                doc = json.load(f)
            self.assertEqual(doc["schema"], "leanre.corpus_comparison/1")
            self.assertEqual(doc["provenance"], "tool_generated")
            self.assertEqual(doc["count"], 1)
            self.assertEqual(doc["projects"][0]["files"], 5)

    def test_build_corpus_comparison_from_gallery_manifests(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p1 = os.path.join(td, "p", "alpha")
            os.makedirs(p1)
            with open(os.path.join(p1, "manifest.json"), "w", encoding="utf-8") as f:
                json.dump({
                    "schema": "leanre.site_manifest/1",
                    "slug": "alpha",
                    "title": "Alpha Proof",
                    "source_only": True,
                    "category": "human-baseline",
                    "license": "Apache-2.0",
                    "assets": {"embedding_2d": "data/embedding_2d.json"},
                    "stats": {
                        "total_files": 10,
                        "total_lines": 500,
                        "total_decls": 50,
                        "defs": 15,
                        "thms": 30,
                        "inds": 5,
                        "reach_count": 8,
                        "proof_sorry": 1,
                        "challenge_sorry": 2,
                        "axioms": 0,
                        "decide_kernel_count": 0,
                    },
                    "stylometry": {
                        "comment_lines": 100,
                        "comment_pct": 20.0,
                        "max_heartbeats_overrides": 3,
                        "name_compress_ratio": 0.421,
                        "avg_decl_lines": 10.0,
                        "median_file_lines": 48.5,
                        "exact_clone_clusters": 1,
                        "sig_clone_clusters": 2,
                        "misfile_count": 1,
                        "misfile_pct": 10.0,
                    },
                }, f)

            doc = stylometry.build_corpus_comparison(td)
            self.assertEqual(doc["schema"], "leanre.corpus_comparison/1")
            self.assertEqual(doc["count"], 1)
            out_file = os.path.join(td, "data", "corpus_comparison.json")
            self.assertTrue(os.path.isfile(out_file))
            row = doc["projects"][0]
            self.assertEqual(row["slug"], "alpha")
            self.assertEqual(row["orphan_modules"], 2)
            self.assertEqual(row["orphan_pct"], 20.0)
            self.assertEqual(row["comment_pct"], 20.0)
            self.assertEqual(row["max_heartbeats_overrides"], 3)
            self.assertEqual(row["name_compress_ratio"], 0.421)
            self.assertEqual(row["exact_clone_clusters"], 1)
            self.assertEqual(row["sig_clone_clusters"], 2)
            self.assertTrue(row["has_embedding_2d"])
            self.assertFalse(row["has_kernel_export"])

            # Symlink guard
            link_dir = os.path.join(td, "link_gal")
            os.symlink(td, link_dir)
            with self.assertRaises(ValueError):
                stylometry.build_corpus_comparison(link_dir)


if __name__ == "__main__":
    unittest.main()
