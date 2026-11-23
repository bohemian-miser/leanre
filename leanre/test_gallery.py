#!/usr/bin/env python3
"""Unit tests for `leanre.gallery`."""
from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest
import xml.etree.ElementTree as ET

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import gallery  # noqa: E402
import kernel  # noqa: E402

TINY_DEMO_DIR = os.path.join(_REPO_ROOT, "examples", "tiny_demo")


class TestGallery(unittest.TestCase):
    def test_source_only_export_tiny_demo(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            # Force pure source-only by passing ndjson_path=""? Wait: tiny_demo has leanre.toml
            # with export_path = "demo.ndjson", so test source-only on a copied source tree without ndjson.
            src_copy = os.path.join(td, "src_only")
            os.makedirs(src_copy)
            for fn in ("Main.lean", "Arithmetic.lean", "Wrappers.lean", "DeadCode.lean", "Bundles.lean", "lakefile.toml"):
                with open(os.path.join(TINY_DEMO_DIR, fn), "rb") as rf:
                    with open(os.path.join(src_copy, fn), "wb") as wf:
                        wf.write(rf.read())

            out_dir = os.path.join(td, "gallery")
            res = gallery.export_source_project(
                src_copy,
                out_dir,
                slug="tiny-source",
                title="Tiny Source Only",
                repo_url="https://github.com/example/tiny",
                pinned_commit="deadbeef12345678",
                src_prefix="src/",
                description="Source-only smoke test",
                license_label="MIT",
                workers=1,
            )
            self.assertTrue(res["source_only"])
            self.assertTrue(os.path.isfile(os.path.join(out_dir, ".nojekyll")))

            pdir = os.path.join(out_dir, "p", "tiny-source")
            man_path = os.path.join(pdir, "manifest.json")
            self.assertTrue(os.path.isfile(man_path))
            with open(man_path, "r", encoding="utf-8") as f:
                man = json.load(f)

            self.assertEqual(man["schema"], "leanre.site_manifest/1")
            self.assertTrue(man["source_only"])
            self.assertEqual(man["stats"]["total_files"], 5)
            self.assertEqual(man["stats"]["root_module"], "Main")
            self.assertEqual(man["stats"]["reach_count"], 4)
            self.assertGreater(man["stats"]["total_decls"], 0)
            self.assertGreater(len(man["overview_pillars"]), 0)
            self.assertGreater(len(man["top_modules"]), 0)

            # Macro circuit + valid dark/light SVG
            macro_path = os.path.join(pdir, man["circuits"]["macro"])
            with open(macro_path, "r", encoding="utf-8") as f:
                macro = json.load(f)
            self.assertEqual(macro["mode"], "macro")
            for key in ("svg_dark", "svg_light"):
                root = ET.fromstring(macro[key])
                self.assertTrue(root.tag.endswith("svg"))

            # Module matrix (32x32)
            mat_path = os.path.join(pdir, man["assets"]["module_matrix"])
            with open(mat_path, "r", encoding="utf-8") as f:
                mat = json.load(f)
            self.assertEqual(mat["schema"], "leanre.module_matrix/1")
            self.assertEqual(mat["grid_size"], 32)
            self.assertEqual(len(mat["grid"]), 32)
            self.assertEqual(len(mat["grid"][0]), 32)
            self.assertGreater(len(mat["cell_samples"]), 0)
            self.assertGreater(len(mat["top_declarations"]), 0)

            # Summary markdown
            sum_path = os.path.join(pdir, man["assets"]["summary"])
            with open(sum_path, "r", encoding="utf-8") as f:
                sum_md = f.read()
            self.assertIn("deadbeef1234", sum_md)
            self.assertIn("https://github.com/example/tiny/blob/deadbeef12345678/src/", sum_md)

            # Search shards <= 150 KB with mod/line/kind/fan_in
            search_meta = man["search"]
            self.assertEqual(search_meta["bucket_mode"], "leaf_prefix2")
            self.assertGreater(len(search_meta["shards"]), 0)
            found_main = False
            for sk in search_meta["shards"]:
                spath = os.path.join(pdir, "data", "search", f"{sk}.json")
                self.assertLessEqual(os.path.getsize(spath), 150 * 1024)
                with open(spath, "r", encoding="utf-8") as f:
                    sdata = json.load(f)
                rows = sdata["entries"] if isinstance(sdata, dict) else sdata
                for r in rows:
                    for req_k in ("name", "kind", "mod", "line", "fan_in"):
                        self.assertIn(req_k, r)
                    if r["name"] == "Main":
                        found_main = True
            self.assertTrue(found_main)

            # Zero .lean files anywhere in out_dir
            for r_dir, _, fns in os.walk(out_dir):
                for fn in fns:
                    self.assertFalse(fn.endswith(".lean"), f"Found .lean file {r_dir}/{fn}")

    def test_kernel_enriched_tiny_demo_and_registry(self) -> None:
        if not os.path.isfile(kernel.default_binary_path()):
            self.skipTest("leanre-kernel release binary not built")
        with tempfile.TemporaryDirectory() as td:
            out_dir = os.path.join(td, "gallery")
            res = gallery.export_source_project(
                TINY_DEMO_DIR,
                out_dir,
                slug="tiny-demo",
                title="Tiny Demo",
                repo_url="https://github.com/bohemian-miser/leanre",
                pinned_commit="abcdef0123456789",
                src_prefix="examples/tiny_demo/",
                license_label="AGPL-3.0-or-later OR MIT-0",
                ndjson_path=os.path.join(TINY_DEMO_DIR, "demo.ndjson"),
                workers=1,
            )
            self.assertFalse(res["source_only"])
            self.assertEqual(res["stats"]["kernel_total_decls"], 17)
            self.assertEqual(res["stats"]["kernel_live_decls"], 10)

            reg = gallery.build_projects_registry(out_dir)
            self.assertEqual(reg["schema"], "leanre.projects_registry/1")
            self.assertEqual(reg["count"], 1)
            entry = reg["projects"][0]
            self.assertEqual(entry["slug"], "tiny-demo")
            self.assertTrue(entry["has_kernel_export"])
            self.assertEqual(entry["category"], "demo")
            self.assertEqual(entry["files"], 5)
            self.assertEqual(entry["license"], "AGPL-3.0-or-later OR MIT-0")
            for k in ("files", "lines", "decls", "axioms", "sorry", "decide_kernel", "has_kernel_export", "category", "license", "repo_url", "pinned_commit", "tagline"):
                self.assertIn(k, entry)

    def test_smart_root_forensic_links_and_no_body_leak(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            src_dir = os.path.join(td, "repo", "lean")
            os.makedirs(os.path.join(src_dir, "Sub"))
            with open(os.path.join(src_dir, "lakefile.toml"), "w", encoding="utf-8") as f:
                f.write('name = "demo"\ndefaultTargets = ["Challenge", "Solution"]\n')
            with open(os.path.join(src_dir, "Challenge.lean"), "w", encoding="utf-8") as f:
                f.write("theorem goal_stmt : True := by\n  sorry\n")
            with open(os.path.join(src_dir, "Solution.lean"), "w", encoding="utf-8") as f:
                f.write("import Sub.Core\nimport Sub.Aux0\nimport Sub.Aux1\nimport Sub.Aux2\nimport Sub.Aux3\n"
                        "import Sub.Aux4\nimport Sub.Aux5\nimport Sub.Aux6\nimport Sub.Aux7\nimport Sub.Aux8\n"
                        "theorem solved : True := by\n  exact Sub.core_thm\n")
            secret_body = "UNIQUE_PROOF_BODY_TOKEN_DO_NOT_LEAK_12345"
            with open(os.path.join(src_dir, "Sub", "Core.lean"), "w", encoding="utf-8") as f:
                f.write(
                    "axiom custom_ax : Prop\n"
                    "theorem core_thm : True := by\n"
                    f"  have _unused := \"{secret_body}\"\n"
                    "  decide +kernel\n"
                )
            for idx in range(9):
                with open(os.path.join(src_dir, "Sub", f"Aux{idx}.lean"), "w", encoding="utf-8") as f:
                    f.write(f"import Sub.Core\ndef aux_{idx} : Nat := {idx}\n")

            out_dir = os.path.join(td, "gal")
            res = gallery.export_source_project(
                src_dir,
                out_dir,
                slug="synthetic",
                title="Synthetic",
                repo_url="https://github.com/org/synthetic",
                pinned_commit="1111222233334444",
                src_prefix="lean/",
                workers=1,
            )
            # Should escape 1-module Challenge leaf and select Solution
            self.assertEqual(res["stats"]["root_module"], "Solution")
            self.assertEqual(res["stats"]["reach_count"], 11)
            self.assertEqual(res["stats"]["sorry_count"], 1)
            self.assertEqual(res["stats"]["axioms"], 1)
            self.assertEqual(res["stats"]["decide_kernel_count"], 1)

            # Verify ZERO proof-body token leakage anywhere in exported files
            for r_dir, _, fns in os.walk(out_dir):
                for fn in fns:
                    full = os.path.join(r_dir, fn)
                    with open(full, "r", encoding="utf-8", errors="replace") as f:
                        txt = f.read()
                    self.assertNotIn(secret_body, txt, f"Proof body leaked in {full}")

            with open(os.path.join(out_dir, "p", "synthetic", "data", "summary.md"), "r", encoding="utf-8") as f:
                smd = f.read()
            self.assertIn("https://github.com/org/synthetic/blob/1111222233334444/lean/Challenge.lean#L2", smd)
            self.assertIn("https://github.com/org/synthetic/blob/1111222233334444/lean/Sub/Core.lean#L1", smd)

    def test_symlink_and_slug_validation(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            real_out = os.path.join(td, "real")
            os.makedirs(real_out)
            link_out = os.path.join(td, "link")
            os.symlink(real_out, link_out)
            with self.assertRaises(ValueError):
                gallery.export_source_project(
                    TINY_DEMO_DIR,
                    link_out,
                    slug="bad",
                    title="Bad",
                    repo_url="",
                    pinned_commit="",
                )
            with self.assertRaises(ValueError):
                gallery.export_source_project(
                    TINY_DEMO_DIR,
                    real_out,
                    slug="../evil",
                    title="Evil",
                    repo_url="",
                    pinned_commit="",
                )
            with self.assertRaises(ValueError):
                gallery.build_projects_registry(link_out)


if __name__ == "__main__":
    unittest.main()
