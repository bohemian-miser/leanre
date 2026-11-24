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
import treemap  # noqa: E402
import xrefs  # noqa: E402

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

            # Auto-generated source-level data/xrefs/
            self.assertTrue(res["has_xrefs"])
            self.assertEqual(man["assets"]["xrefs"], "data/xrefs/manifest.json")
            self.assertIn("data/xrefs/manifest.json", man["provenance"]["tool_generated"])
            self.assertEqual(man["xrefs_summary"]["mode"], "source")
            self.assertGreater(man["xrefs_summary"]["n_decls"], 0)
            self.assertGreater(man["xrefs_summary"]["n_edges"], 0)
            self.assertTrue(xrefs.verify_xrefs(os.path.join(pdir, "data", "xrefs"))["ok"])

            reg_src = gallery.build_projects_registry(out_dir)
            self.assertTrue(reg_src["projects"][0]["has_xrefs"])
            self.assertTrue(res["has_treemap"])
            self.assertEqual(man["assets"]["treemap"], "data/treemap/manifest.json")
            self.assertIn("data/treemap/manifest.json", man["provenance"]["tool_generated"])
            self.assertIn("data/treemap/**/*.lxrt", man["provenance"]["tool_generated"])
            self.assertEqual(man["provenance"]["treemap_overlay"]["provenance"], "mixed")
            self.assertEqual(man["treemap_summary"]["mode"], "source")
            self.assertGreater(man["treemap_summary"]["n_nodes"], 0)
            self.assertTrue(treemap.verify_treemap_dir(os.path.join(pdir, "data", "treemap"))["ok"])
            self.assertTrue(reg_src["projects"][0]["has_treemap"])

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
            self.assertEqual(res["stats"]["proof_sorry"], 0)
            self.assertEqual(res["stats"]["challenge_sorry"], 1)
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
            self.assertIn("Challenge-spec `sorry`", smd)
            self.assertNotIn("hit(s)", smd)
            self.assertNotIn("file(s)", smd)

    def test_multi_root_default_targets_and_rh_registry_helper(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            src_dir = os.path.join(td, "dual")
            os.makedirs(os.path.join(src_dir, "ComparatorChallenges"))
            with open(os.path.join(src_dir, "lakefile.toml"), "w", encoding="utf-8") as f:
                f.write('name = "dual"\ndefaultTargets = ["Alpha", "Beta", "ComparatorChallenges"]\n')
            with open(os.path.join(src_dir, "Alpha.lean"), "w", encoding="utf-8") as f:
                f.write("import AlphaSub\ntheorem alpha_main : True := trivial\n")
            with open(os.path.join(src_dir, "AlphaSub.lean"), "w", encoding="utf-8") as f:
                f.write("theorem alpha_sub : True := trivial\n")
            with open(os.path.join(src_dir, "Beta.lean"), "w", encoding="utf-8") as f:
                f.write("import BetaSub\ntheorem beta_main : True := trivial\n")
            with open(os.path.join(src_dir, "BetaSub.lean"), "w", encoding="utf-8") as f:
                f.write("theorem beta_sub : True := trivial\n")
            with open(os.path.join(src_dir, "ComparatorChallenges", "Stub.lean"), "w", encoding="utf-8") as f:
                f.write("theorem stub_goal : True := by sorry\n")

            out_dir = os.path.join(td, "gal")
            res = gallery.export_source_project(
                src_dir,
                out_dir,
                slug="dual-proj",
                title="Dual Proj",
                repo_url="https://github.com/org/dual",
                pinned_commit="abcdef0123456789",
                workers=1,
            )
            self.assertEqual(res["stats"]["reach_count"], 4)
            self.assertEqual(res["stats"]["proof_sorry"], 0)
            self.assertEqual(res["stats"]["challenge_sorry"], 1)

            reg = gallery.register_rh_root(out_dir)
            self.assertEqual(reg["count"], 2)
            slugs = [p["slug"] for p in reg["projects"]]
            self.assertEqual(slugs, ["riemann-hypothesis", "dual-proj"])
            self.assertEqual(reg["projects"][0]["path"], ".")
            self.assertEqual(reg["projects"][0]["license"], "None")
            self.assertEqual(reg["projects"][1]["proof_sorry"], 0)
            self.assertEqual(reg["projects"][1]["challenge_sorry"], 1)

            # Singularization check on 1 dominated module / 1 line
            pillars_1 = gallery._build_source_overview_pillars(
                [{
                    "name": "A", "dom_subtree_size": 1, "dom_parent": None, "bfs_depth": 0,
                    "lines_wc": 1, "decl_count": 1, "fan_in": 0, "rev_reach": 1,
                }],
                "A",
                1,
            )
            self.assertEqual(len(pillars_1), 1)
            self.assertEqual(pillars_1[0]["note"], "1 dominated module · 1 line · entry module")

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

    def test_notes_layer_separation_provenance_and_publish(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            # Build a repo WITHOUT notes -> notes_layer.enabled MUST be False
            out_clean = os.path.join(td, "site_clean")
            res_clean = gallery.export_source_project(
                TINY_DEMO_DIR,
                out_clean,
                slug="clean-demo",
                title="Clean Demo",
                repo_url="https://github.com/example/clean",
                pinned_commit="1234567890abcdef",
                workers=1,
            )
            self.assertFalse(res_clean["notes_enabled"])
            with open(os.path.join(out_clean, "p", "clean-demo", "manifest.json"), "r", encoding="utf-8") as f:
                m_clean = json.load(f)
            prov_c = m_clean["provenance"]
            self.assertIn("manifest.json", prov_c["tool_generated"])
            self.assertIn("data/module_matrix.json", prov_c["tool_generated"])
            self.assertIn("data/embedding_2d.json", prov_c["tool_generated"])
            self.assertEqual(m_clean["assets"]["embedding_2d"], "data/embedding_2d.json")
            self.assertTrue(res_clean["has_embedding_2d"])
            with open(os.path.join(out_clean, "p", "clean-demo", "data", "embedding_2d.json"), "r", encoding="utf-8") as f:
                emb_c = json.load(f)
            self.assertEqual(emb_c["schema"], "leanre.embedding_2d/1")
            self.assertEqual(emb_c["layers"]["modules"]["count"], 5)
            self.assertFalse(prov_c["notes_layer"]["enabled"])
            self.assertIsNone(prov_c["notes_layer"]["source_dir"])
            self.assertEqual(prov_c["notes_layer"]["findings_count"], 0)
            self.assertEqual(prov_c["notes_layer"]["dossiers_count"], 0)
            self.assertEqual(prov_c["notes_layer"]["annotations_count"], 0)
            self.assertEqual(m_clean["dossiers"], [])
            self.assertEqual(m_clean["findings"][0]["provenance"], "tool_generated")
            self.assertIn("stylometry", m_clean)

            # Build a repo WITH notes_dir (findings/, dossiers/, top-level .md, annotations/*.jsonl) + extra_dossier
            notes_dir = os.path.join(td, "notes", "noted-demo")
            os.makedirs(os.path.join(notes_dir, "findings"))
            os.makedirs(os.path.join(notes_dir, "dossiers"))
            os.makedirs(os.path.join(notes_dir, "annotations"))
            with open(os.path.join(notes_dir, "findings", "extra_finding.md"), "w", encoding="utf-8") as f:
                f.write("# Extra Finding\n\nAuthored note about $\\tfrac1{52}$ constant.\n")
            with open(os.path.join(notes_dir, "dossiers", "deep_dive.md"), "w", encoding="utf-8") as f:
                f.write("# Deep Dive Dossier\n\nSeparate authored review dossier.\n")
            with open(os.path.join(notes_dir, "top_level_note.md"), "w", encoding="utf-8") as f:
                f.write("# Top Level Note\n\nDirect markdown file in notes/<slug>/.\n")
            with open(os.path.join(notes_dir, "annotations", "review.jsonl"), "w", encoding="utf-8") as f:
                f.write(json.dumps({
                    "schema": "leanre.annot/1",
                    "id": "n1",
                    "target": "TinyDemo.main_theorem",
                    "author": "reviewer",
                    "kind": "note",
                    "text": "Checked statement.",
                }) + "\n")
            extra_cmp = os.path.join(td, "shared_cmp.md")
            with open(extra_cmp, "w", encoding="utf-8") as f:
                f.write("# Shared Comparison\n\nCross-repo review note.\n")

            # Also test `publish_gallery` with a TOML config including one missing corpus (must skip gracefully)
            cfg_toml = os.path.join(td, "gallery.toml")
            with open(cfg_toml, "w", encoding="utf-8") as f:
                f.write(
                    'schema_version = 1\n\n'
                    '[[projects]]\n'
                    'slug = "missing-repo"\n'
                    'title = "Missing Repo"\n'
                    'src_dir = "does_not_exist/src"\n\n'
                    '[[projects]]\n'
                    'slug = "noted-demo"\n'
                    'title = "Noted Demo"\n'
                    f'src_dir = {json.dumps(TINY_DEMO_DIR)}\n'
                    'repo_url = "https://github.com/example/noted"\n'
                    'pinned_commit = "abcdef1234567890"\n'
                    'license = "MIT"\n'
                    'category = "demo"\n'
                    'notes_dir = "notes/noted-demo"\n'
                    'extra_dossiers = ["shared_cmp.md"]\n'
                )

            pub_out = os.path.join(td, "published_site")
            pub_rep = gallery.publish_gallery(cfg_toml, pub_out, workers=1)
            self.assertEqual(pub_rep["built_count"], 1)
            self.assertEqual(pub_rep["skipped_count"], 1)
            self.assertEqual(pub_rep["skipped"][0]["slug"], "missing-repo")
            self.assertEqual(pub_rep["comparison"], "data/corpus_comparison.json")

            with open(os.path.join(pub_out, "projects.json"), "r", encoding="utf-8") as f:
                reg = json.load(f)
            self.assertEqual(reg["comparison"], "data/corpus_comparison.json")
            self.assertTrue(reg["projects"][0]["has_embedding_2d"])
            self.assertTrue(reg["projects"][0]["notes_enabled"])

            # Verify < 4 modules skips embedding_2d gracefully
            tiny2_src = os.path.join(td, "tiny2")
            os.makedirs(tiny2_src)
            with open(os.path.join(tiny2_src, "A.lean"), "w", encoding="utf-8") as f:
                f.write("theorem a : True := trivial\n")
            with open(os.path.join(tiny2_src, "B.lean"), "w", encoding="utf-8") as f:
                f.write("import A\ntheorem b : True := a\n")
            res_t2 = gallery.export_source_project(
                tiny2_src,
                os.path.join(td, "site_tiny2"),
                slug="tiny2",
                title="Tiny 2",
                repo_url="https://github.com/example/tiny2",
                pinned_commit="12345678",
                workers=1,
            )
            self.assertFalse(res_t2["has_embedding_2d"])
            reg_t2 = gallery.build_projects_registry(os.path.join(td, "site_tiny2"))
            self.assertFalse(reg_t2["projects"][0]["has_embedding_2d"])

            with open(os.path.join(pub_out, "data", "corpus_comparison.json"), "r", encoding="utf-8") as f:
                comp = json.load(f)
            self.assertEqual(comp["schema"], "leanre.corpus_comparison/1")
            self.assertEqual(comp["count"], 1)
            self.assertEqual(comp["projects"][0]["slug"], "noted-demo")
            self.assertGreater(comp["projects"][0]["name_compress_ratio"], 0.0)

            with open(os.path.join(pub_out, "p", "noted-demo", "manifest.json"), "r", encoding="utf-8") as f:
                m_noted = json.load(f)
            nl = m_noted["provenance"]["notes_layer"]
            self.assertTrue(nl["enabled"])
            self.assertEqual(nl["findings_count"], 1)
            self.assertEqual(nl["dossiers_count"], 3)
            self.assertEqual(nl["annotations_count"], 1)
            self.assertEqual(m_noted["assets"]["annotations"], ["data/notes/annotations/review.jsonl"])
            self.assertEqual(len(m_noted["findings"]), 2)
            self.assertIn("1/52", m_noted["findings"][1]["summary"])

    def test_xrefs_opt_out_rh_xrefs_dir_and_cross_corpus_notes(self) -> None:
        import io
        from contextlib import redirect_stdout

        with tempfile.TemporaryDirectory() as td:
            # 1) --no-xrefs opt-out in export_source_project
            out_no_x = os.path.join(td, "gal_no_xrefs")
            res_nx = gallery.export_source_project(
                TINY_DEMO_DIR,
                out_no_x,
                slug="no-xrefs-demo",
                title="No Xrefs Demo",
                repo_url="https://github.com/example/nx",
                pinned_commit="1234567890abcdef",
                run_xrefs=False,
                workers=1,
            )
            self.assertFalse(res_nx["has_xrefs"])
            self.assertFalse(os.path.exists(os.path.join(out_no_x, "p", "no-xrefs-demo", "data", "xrefs")))
            with open(os.path.join(out_no_x, "p", "no-xrefs-demo", "manifest.json"), "r", encoding="utf-8") as f:
                mnx = json.load(f)
            self.assertIsNone(mnx["assets"]["xrefs"])
            self.assertNotIn("xrefs_summary", mnx)
            reg_nx = gallery.build_projects_registry(out_no_x)
            self.assertFalse(reg_nx["projects"][0]["has_xrefs"])

            # 2) publish_main with --rh-xrefs-dir + notes/cross-corpus auto-discovery
            prebuilt_rh_x = os.path.join(td, "prebuilt_rh_xrefs")
            xmf = xrefs.export_source(prebuilt_rh_x, src_dir=TINY_DEMO_DIR)

            cross_dir = os.path.join(td, "notes", "cross-corpus")
            os.makedirs(cross_dir)
            with open(os.path.join(cross_dir, "human_vs_ai_structure.md"), "w", encoding="utf-8") as f:
                f.write("# Human vs. AI Structure\n\nCross-corpus structural synthesis.\n")

            cfg_toml = os.path.join(td, "gallery.toml")
            with open(cfg_toml, "w", encoding="utf-8") as f:
                f.write(
                    'schema_version = 1\n\n'
                    '[[projects]]\n'
                    'slug = "root-demo"\n'
                    'title = "Root Demo"\n'
                    'root = true\n'
                    'mode = "kernel_site"\n'
                    f'src_dir = {json.dumps(TINY_DEMO_DIR)}\n'
                    'extra_dossiers = ["does_not_exist.md"]\n\n'
                    '[[projects]]\n'
                    'slug = "sub-demo"\n'
                    'title = "Sub Demo"\n'
                    f'src_dir = {json.dumps(TINY_DEMO_DIR)}\n'
                    'repo_url = "https://github.com/example/sub"\n'
                    'pinned_commit = "abcdef0123456789"\n'
                )

            pub_out = os.path.join(td, "pub_site")
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = gallery.publish_main([
                    "--config", cfg_toml,
                    "--out-dir", pub_out,
                    "--workers", "1",
                    "--no-flirt",
                    "--no-embedding",
                    "--rh-xrefs-dir", prebuilt_rh_x,
                ])
            self.assertEqual(rc, 0)
            rep = json.loads(buf.getvalue())
            self.assertEqual(rep["built_count"], 2)
            self.assertTrue(all(b["has_xrefs"] for b in rep["built"]))

            # Root got prebuilt xrefs via hardlink + auto-discovered notes/cross-corpus/
            with open(os.path.join(pub_out, "manifest.json"), "r", encoding="utf-8") as f:
                root_man = json.load(f)
            self.assertEqual(root_man["assets"]["xrefs"], "data/xrefs/manifest.json")
            self.assertEqual(root_man["xrefs_summary"]["n_decls"], xmf["n_decls"])
            self.assertEqual(
                os.stat(os.path.join(prebuilt_rh_x, "modules.lxrf")).st_ino,
                os.stat(os.path.join(pub_out, "data", "xrefs", "modules.lxrf")).st_ino,
            )
            dossier_slugs = [d["slug"] for d in root_man["dossiers"]]
            self.assertIn("human_vs_ai_structure", dossier_slugs)
            self.assertTrue(root_man["provenance"]["notes_layer"]["enabled"])

            with open(os.path.join(pub_out, "projects.json"), "r", encoding="utf-8") as f:
                reg = json.load(f)
            self.assertTrue(all(p["has_xrefs"] for p in reg["projects"]))

            # 3) --no-xrefs on publish_main skips xrefs on both root and subprojects
            pub_no_x = os.path.join(td, "pub_no_x")
            buf2 = io.StringIO()
            with redirect_stdout(buf2):
                rc2 = gallery.publish_main([
                    "--config", cfg_toml,
                    "--out-dir", pub_no_x,
                    "--workers", "1",
                    "--no-flirt",
                    "--no-embedding",
                    "--no-xrefs",
                ])
            self.assertEqual(rc2, 0)
            rep2 = json.loads(buf2.getvalue())
            self.assertFalse(any(b["has_xrefs"] for b in rep2["built"]))
            self.assertFalse(os.path.exists(os.path.join(pub_no_x, "data", "xrefs")))
            self.assertFalse(os.path.exists(os.path.join(pub_no_x, "p", "sub-demo", "data", "xrefs")))

    def test_treemap_opt_out_rh_treemap_dir_refresh_overlay_and_contrib(self) -> None:
        import io
        from contextlib import redirect_stdout

        with tempfile.TemporaryDirectory() as td:
            # 1) run_treemap=False opt-out in export_source_project
            out_no_tm = os.path.join(td, "gal_no_tm")
            res_nt = gallery.export_source_project(
                TINY_DEMO_DIR,
                out_no_tm,
                slug="no-tm-demo",
                title="No Treemap Demo",
                repo_url="https://github.com/example/ntm",
                pinned_commit="1234567890abcdef",
                run_treemap=False,
                workers=1,
            )
            self.assertFalse(res_nt["has_treemap"])
            self.assertFalse(os.path.exists(os.path.join(out_no_tm, "p", "no-tm-demo", "data", "treemap")))
            with open(os.path.join(out_no_tm, "p", "no-tm-demo", "manifest.json"), "r", encoding="utf-8") as f:
                mnt = json.load(f)
            self.assertIsNone(mnt["assets"]["treemap"])
            self.assertNotIn("treemap_summary", mnt)
            reg_nt = gallery.build_projects_registry(out_no_tm)
            self.assertFalse(reg_nt["projects"][0]["has_treemap"])

            # 2) Auto-compiled overlay from annotations/contrib/<slug>/*.jsonl + notes/<slug>/ + extra_dossiers
            ann_root = os.path.join(td, "annotations")
            contrib_sub = os.path.join(ann_root, "contrib", "sub-demo")
            os.makedirs(contrib_sub, exist_ok=True)
            with open(os.path.join(contrib_sub, "bob__sub.jsonl"), "w", encoding="utf-8") as f:
                f.write(json.dumps({"schema": "leanre.annot/1", "type": "pack"}) + "\n")
                f.write(json.dumps({
                    "type": "layer", "layer": "human/bob-sub", "kind": "human-review",
                    "default_on": True, "title": "Bob Sub Notes",
                }) + "\n")
                f.write(json.dumps({
                    "type": "annot", "target": "decl", "name": "TinyDemo.main_theorem",
                    "layer": "human/bob-sub", "tag": "L", "author": "@bob",
                    "note": "Subproject contrib pack.", "source": "Main.lean#L11",
                    "created": "2026-01-01T00:00:00Z", "updated": "2026-01-01T00:00:00Z",
                }) + "\n")

            notes_sub = os.path.join(td, "notes", "sub-demo")
            os.makedirs(notes_sub, exist_ok=True)
            with open(os.path.join(notes_sub, "sub_audit.md"), "w", encoding="utf-8") as f:
                f.write("# Sub Audit\n\nNotes touching `TinyDemo.ProofBundle`.\n")

            extra_dos = os.path.join(td, "shared_extra.md")
            with open(extra_dos, "w", encoding="utf-8") as f:
                f.write("# Shared Extra\n\nExtra dossier mentioning `TinyDemo.main_theorem`.\n")

            # Prebuilt RH treemap dir + top-level RH annotation for --refresh-overlay check
            prebuilt_rh_tm = os.path.join(td, "prebuilt_rh_treemap")
            tm_res = treemap.export_source_treemap(
                TINY_DEMO_DIR, prebuilt_rh_tm, slug="root-demo", workers=1
            )
            tm_mf = tm_res["manifest"]
            with open(os.path.join(prebuilt_rh_tm, "overlay.json"), "r", encoding="utf-8") as f:
                orig_rh_ov = f.read()

            with open(os.path.join(ann_root, "human__root_fact.jsonl"), "w", encoding="utf-8") as f:
                f.write(json.dumps({"schema": "leanre.annot/1", "type": "pack"}) + "\n")
                f.write(json.dumps({
                    "type": "layer", "layer": "human/root-fact", "kind": "human-review",
                    "default_on": True, "title": "Root Fact",
                }) + "\n")
                f.write(json.dumps({
                    "type": "annot", "target": "decl", "name": "TinyDemo.main_theorem",
                    "layer": "human/root-fact", "tag": "L", "author": "@alice",
                    "note": "Refreshed RH overlay note.", "source": "Main.lean#L11",
                    "created": "2026-01-01T00:00:00Z", "updated": "2026-01-01T00:00:00Z",
                }) + "\n")

            cfg_toml = os.path.join(td, "gallery.toml")
            with open(cfg_toml, "w", encoding="utf-8") as f:
                f.write(
                    'schema_version = 1\n\n'
                    '[[projects]]\n'
                    'slug = "root-demo"\n'
                    'title = "Root Demo"\n'
                    'root = true\n'
                    'mode = "kernel_site"\n'
                    f'src_dir = {json.dumps(TINY_DEMO_DIR)}\n\n'
                    '[[projects]]\n'
                    'slug = "sub-demo"\n'
                    'title = "Sub Demo"\n'
                    f'src_dir = {json.dumps(TINY_DEMO_DIR)}\n'
                    'repo_url = "https://github.com/example/sub"\n'
                    'pinned_commit = "abcdef0123456789"\n'
                    'notes_dir = "notes/sub-demo"\n'
                    'extra_dossiers = ["shared_extra.md"]\n'
                )

            pub_out = os.path.join(td, "pub_site")
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = gallery.publish_main([
                    "--config", cfg_toml,
                    "--out-dir", pub_out,
                    "--workers", "1",
                    "--no-flirt",
                    "--no-embedding",
                    "--no-xrefs",
                    "--rh-treemap-dir", prebuilt_rh_tm,
                    "--refresh-overlay",
                ])
            self.assertEqual(rc, 0)
            rep = json.loads(buf.getvalue())
            self.assertEqual(rep["built_count"], 2)
            self.assertTrue(all(b["has_treemap"] for b in rep["built"]))

            # Root got prebuilt treemap via hardlink + refreshed overlay (without mutating prebuilt overlay.json)
            with open(os.path.join(pub_out, "manifest.json"), "r", encoding="utf-8") as f:
                root_man = json.load(f)
            self.assertEqual(root_man["assets"]["treemap"], "data/treemap/manifest.json")
            self.assertEqual(root_man["treemap_summary"]["n_nodes"], tm_mf["views"][0]["n_nodes"])
            self.assertEqual(
                os.stat(os.path.join(prebuilt_rh_tm, "folder.lxrt")).st_ino,
                os.stat(os.path.join(pub_out, "data", "treemap", "folder.lxrt")).st_ino,
            )
            with open(os.path.join(prebuilt_rh_tm, "overlay.json"), "r", encoding="utf-8") as f:
                self.assertEqual(f.read(), orig_rh_ov)
            with open(os.path.join(pub_out, "data", "treemap", "overlay.json"), "r", encoding="utf-8") as f:
                root_ov = json.load(f)
            self.assertIn("TinyDemo.main_theorem", root_ov["entries"])

            # Subproject compiled overlay from contrib/sub-demo + notes/sub-demo + extra_dossiers
            with open(os.path.join(pub_out, "p", "sub-demo", "data", "treemap", "overlay.json"), "r", encoding="utf-8") as f:
                sub_ov = json.load(f)
            sub_layers = {l["id"] for l in sub_ov["layers"]}
            self.assertIn("human/bob-sub", sub_layers)
            self.assertIn("dossiers/index", sub_layers)
            self.assertIn("TinyDemo.main_theorem", sub_ov["entries"])
            self.assertIn("TinyDemo.ProofBundle", sub_ov["entries"])

            with open(os.path.join(pub_out, "projects.json"), "r", encoding="utf-8") as f:
                reg = json.load(f)
            self.assertTrue(all(p["has_treemap"] for p in reg["projects"]))

            # 3) --no-treemap on publish_main skips treemap on both root and subprojects
            pub_no_tm = os.path.join(td, "pub_no_tm")
            buf2 = io.StringIO()
            with redirect_stdout(buf2):
                rc2 = gallery.publish_main([
                    "--config", cfg_toml,
                    "--out-dir", pub_no_tm,
                    "--workers", "1",
                    "--no-flirt",
                    "--no-embedding",
                    "--no-xrefs",
                    "--no-treemap",
                ])
            self.assertEqual(rc2, 0)
            rep2 = json.loads(buf2.getvalue())
            self.assertFalse(any(b["has_treemap"] for b in rep2["built"]))
            self.assertFalse(os.path.exists(os.path.join(pub_no_tm, "data", "treemap")))
            self.assertFalse(os.path.exists(os.path.join(pub_no_tm, "p", "sub-demo", "data", "treemap")))


if __name__ == "__main__":
    unittest.main()
