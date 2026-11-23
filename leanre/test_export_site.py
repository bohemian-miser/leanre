#!/usr/bin/env python3
"""Unit & integration tests for `examples/tiny_demo/` and `leanre.export_site`."""
from __future__ import annotations

import hashlib
import json
import os
import re
import sqlite3
import stat
import sys
import tempfile
import time
import unittest
import xml.etree.ElementTree as ET

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import bundles  # noqa: E402
import export_site  # noqa: E402
import kernel  # noqa: E402

TINY_DEMO_DIR = os.path.join(_REPO_ROOT, "examples", "tiny_demo")


def _extract_embedded_json(html_text: str) -> dict:
    m = re.search(
        r'<script id="leanre-data" type="application/json">(.*?)</script>',
        html_text,
        flags=re.DOTALL,
    )
    if not m:
        raise AssertionError("Missing <script id='leanre-data'> block")
    return json.loads(m.group(1))


class TestTinyDemoAndExportSite(unittest.TestCase):
    def test_tiny_demo_layout_license_and_size(self) -> None:
        expected_files = [
            "Main.lean",
            "Arithmetic.lean",
            "Wrappers.lean",
            "DeadCode.lean",
            "Bundles.lean",
            "lakefile.toml",
            "leanre.toml",
            "demo.ndjson",
        ]
        total_bytes = 0
        for fn in expected_files:
            p = os.path.join(TINY_DEMO_DIR, fn)
            self.assertTrue(os.path.isfile(p), f"Missing {p}")
            self.assertFalse(os.path.islink(p), f"Unexpected symlink {p}")
            total_bytes += os.path.getsize(p)
            if fn.endswith(".lean"):
                with open(p, "r", encoding="utf-8") as f:
                    head = f.read(300)
                self.assertIn("SPDX-License-Identifier: AGPL-3.0-or-later OR MIT-0", head)
        self.assertLess(total_bytes, 100 * 1024, f"tiny_demo too large: {total_bytes} bytes")

    def test_tiny_demo_kernel_bundles_and_static_site(self) -> None:
        bin_path = kernel.default_binary_path()
        if not os.path.exists(bin_path):
            self.skipTest("leanre-kernel release binary not built")

        ndjson_path = os.path.join(TINY_DEMO_DIR, "demo.ndjson")
        with tempfile.TemporaryDirectory() as td:
            out_dir = os.path.join(td, "kernel_out")
            t0 = time.monotonic()
            rep = kernel.run_pipeline(
                input_path=ndjson_path,
                out_dir=out_dir,
                src_dir=TINY_DEMO_DIR,
                roots=["TinyDemo.main_theorem:DEMO"],
                threads=2,
                workers=1,
                auto_build=False,
                verbose=False,
            )
            elapsed = time.monotonic() - t0
            self.assertLess(elapsed, 5.0)
            self.assertEqual(rep["k2_counts"]["measured_records"], 17)
            self.assertEqual(rep["k4_live_dead_and_axioms"]["union"]["live"], 10)
            self.assertEqual(rep["k4_live_dead_and_axioms"]["union"]["dead"], 7)
            self.assertEqual(rep["k5_dominators_and_taint"]["dominator_oracle_failures_total"], 0)

            kdb_path = os.path.join(out_dir, "kernel.db")
            conn = sqlite3.connect(f"file:{os.path.abspath(kdb_path)}?mode=ro", uri=True)
            try:
                vn1 = conn.execute(
                    "SELECT value_nodes, live_mask FROM decls WHERE name='TinyDemo.alias_bundle_weight'"
                ).fetchone()
                self.assertEqual(vn1, (1, 1))

                dead_names = {
                    r[0] for r in conn.execute("SELECT name FROM decls WHERE live_mask=0")
                }
                self.assertTrue({
                    "TinyDemo.deadHelper",
                    "TinyDemo.dead_branch_eq",
                    "TinyDemo.dead_unused_note_eq",
                    "TinyDemo.ProofBundle.unusedNote",
                }.issubset(dead_names))

                dom_rows = conn.execute(
                    "SELECT d.name, dp.name, dm.depth, dm.subtree_size "
                    "FROM dom dm "
                    "JOIN decls d ON d.id = dm.decl_id "
                    "LEFT JOIN decls dp ON dp.id = dm.idom "
                    "WHERE dm.tree_id = 0"
                ).fetchall()
                dom_by_name = {r[0]: (r[1], r[2], r[3]) for r in dom_rows}
                self.assertEqual(dom_by_name["TinyDemo.main_theorem"], (None, 0, 10))
                self.assertEqual(dom_by_name["TinyDemo.alias_bundle_weight"][0], "TinyDemo.main_theorem")
                self.assertEqual(dom_by_name["TinyDemo.bundle_weight_refl"][0], "TinyDemo.alias_bundle_weight")
            finally:
                conn.close()

            brep = bundles.run_bundles(kernel_db_path=kdb_path, src_root=TINY_DEMO_DIR, top=10)
            self.assertEqual(brep["summary"]["total_live_1ctor_project_inductives"], 1)
            self.assertEqual(len(brep["bundles"]), 1)
            b0 = brep["bundles"][0]
            self.assertEqual(b0["name"], "TinyDemo.ProofBundle")
            self.assertEqual(b0["total_fields"], 2)
            self.assertEqual(b0["projected_fields"], 1)
            self.assertEqual(b0["unread_fields"], 1)
            self.assertEqual(b0["projected_field_names"], ["coreWeight"])
            self.assertEqual(b0["unread_field_names"], ["unusedNote"])

            # Verify read-only chmod 0444/0555 kernel.db works for export_site
            ro_dir = os.path.join(td, "ro_kdb")
            os.makedirs(ro_dir, exist_ok=True)
            ro_db = os.path.join(ro_dir, "kernel.db")
            with open(kdb_path, "rb") as src_f, open(ro_db, "wb") as dst_f:
                dst_f.write(src_f.read())
            os.chmod(ro_db, stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)
            os.chmod(ro_dir, stat.S_IRUSR | stat.S_IXUSR)
            try:
                site_html = os.path.join(td, "tiny_site.html")
                meta = export_site.export_static_site(
                    decomp_dir=None,
                    out_html=site_html,
                    kernel_db=ro_db,
                    src_root=TINY_DEMO_DIR,
                    title="Tiny Demo Explorer",
                )
                self.assertTrue(meta["has_kernel"])
                self.assertTrue(meta["has_circuit"])
                with open(site_html, "r", encoding="utf-8") as f:
                    text = f.read()
                payload = _extract_embedded_json(text)
                self.assertEqual(payload["kernel"]["counts"]["live_decls"], 10)
                self.assertEqual(payload["kernel"]["counts"]["vn1_live_aliases"], 1)
                self.assertEqual(payload["kernel"]["bundles"]["bundles"][0]["name"], "TinyDemo.ProofBundle")
                cir = payload["circuit"]
                self.assertIsNotNone(cir)
                self.assertEqual(cir["schema"], "leanre.circuit/1")
                self.assertEqual(cir["mode"], "macro")
                self.assertEqual(cir["stats"]["live_decls"], 10)
                self.assertEqual(cir["stats"]["dead_decls"], 7)
                svg_root = ET.fromstring(cir["svg"])
                self.assertTrue(svg_root.tag.endswith("svg"))
                # Determinism check with embedded macro circuit
                site_html_2 = os.path.join(td, "tiny_site_2.html")
                export_site.export_static_site(
                    decomp_dir=None,
                    out_html=site_html_2,
                    kernel_db=ro_db,
                    src_root=TINY_DEMO_DIR,
                    title="Tiny Demo Explorer",
                )
                with open(site_html, "rb") as f1, open(site_html_2, "rb") as f2:
                    self.assertEqual(hashlib.sha256(f1.read()).hexdigest(), hashlib.sha256(f2.read()).hexdigest())
            finally:
                os.chmod(ro_dir, stat.S_IRWXU)
                os.chmod(ro_db, stat.S_IWUSR | stat.S_IRUSR)

    def test_xss_escaping_zero_cdn_and_determinism(self) -> None:
        xss_str = '</script><script>alert("xss")</script><img src=x onerror=alert(1)> & <!--'
        with tempfile.TemporaryDirectory() as td:
            decomp_dir = os.path.join(td, "decomp")
            os.makedirs(decomp_dir, exist_ok=True)

            bp = {
                "schema": "leanre.decomp/v1",
                "pillar": "spine",
                "pins": {"commit": "deadbeef"},
                "root": xss_str,
                "nodes": [
                    {
                        "id": xss_str,
                        "kind": "thm",
                        "module": "Demo.Main",
                        "anchor": "src/Main.lean:1",
                        "header": "theorem x : True",
                        "role": "theorem",
                        "status": "READ",
                        "verdict": "real",
                        "tag": "L",
                        "dom": {"depth": 0, "subtree": 2, "idom": None},
                        "summary": f"Testing {xss_str}",
                    },
                    {
                        "id": "Demo.Helper",
                        "kind": "def",
                        "module": "Demo.Aux",
                        "anchor": "src/Aux.lean:4",
                        "header": "def h : Nat",
                        "role": "bridge",
                        "status": "READ",
                        "verdict": "wrapper",
                        "tag": "S",
                        "dom": {"depth": 1, "subtree": 1, "idom": xss_str},
                        "summary": "Safe summary",
                    },
                ],
                "edges": [{"src": xss_str, "dst": "Demo.Helper", "rel": "value", "tag": "L"}],
                "horn": [],
                "claims": [{"tag": "L", "text": f"Claim {xss_str}"}],
                "opaque": [],
            }
            with open(os.path.join(decomp_dir, "bp.json"), "w", encoding="utf-8") as f:
                json.dump(bp, f)

            trim_doc = {
                "schema": "leanre.trim/1",
                "provenance": "[L] test",
                "epistemic_scope": {"Layer 1": "safe"},
                "pins": {"mirror_commit": "abc123"},
                "baseline": {"total_modules": 10, "total_lines_wc": 100, "kernel_live_records": 5},
                "c8_waterfall": {
                    "steps": [
                        {
                            "step_id": "step1",
                            "label": f"Step {xss_str}",
                            "precision": "[L]",
                            "before": {"modules": 10, "lines_wc": 100, "kernel_live_decls": 5},
                            "removed": {"modules": 2, "lines_wc": 20, "kernel_live_decls": 1},
                            "after": {"modules": 8, "lines_wc": 80, "kernel_live_decls": 4},
                        }
                    ],
                    "irreducible_core_estimate": {"modules": 8, "lines_wc": 80, "kernel_live_decls_total": 4},
                },
            }
            with open(os.path.join(decomp_dir, "trim_report.json"), "w", encoding="utf-8") as f:
                json.dump(trim_doc, f)

            clusters_doc = {
                "schema": "leanre.flirt_atlas/v1",
                "mirror_commit": "abc123",
                "totals": {"clusters_count": 1, "effective_core_decls": 4, "collapse_pct": 20.0},
                "clusters": [
                    {
                        "cluster_id": "BP001",
                        "kind": "residual_neighborhood",
                        "pillar": "spine",
                        "root_decl": xss_str,
                        "counts": {"live_decls": 5, "effective_core_decls": 4, "collapse_pct": 20.0},
                        "blinded_label": {"label": xss_str, "confidence": 0.9, "provenance": "M"},
                        "mismatch_audit": {"status": "aligned", "severity": "none", "reason": "ok"},
                        "top3_rep_decls": [
                            {"name": "Rep1", "subtree_size": 4, "github_url": "javascript:alert(1)"},
                            {"name": "Rep2", "subtree_size": 2, "github_url": "https://github.com/example/repo/blob/1/a.lean#L1"},
                        ],
                    }
                ],
            }
            with open(os.path.join(decomp_dir, "cluster_labels_141.json"), "w", encoding="utf-8") as f:
                json.dump(clusters_doc, f)

            out_a = os.path.join(td, "site_a.html")
            out_b = os.path.join(td, "site_b.html")
            export_site.export_static_site(decomp_dir, out_a, title=f"Title {xss_str}")
            export_site.export_static_site(decomp_dir, out_b, title=f"Title {xss_str}")

            with open(out_a, "rb") as fa, open(out_b, "rb") as fb:
                raw_a = fa.read()
                raw_b = fb.read()
            self.assertEqual(
                hashlib.sha256(raw_a).hexdigest(),
                hashlib.sha256(raw_b).hexdigest(),
                "HTML output must be deterministic",
            )

            html_text = raw_a.decode("utf-8")
            # Zero unescaped XSS strings in HTML
            self.assertNotIn('</script><script>alert("xss")', html_text)
            self.assertNotIn("<img src=x onerror=alert(1)>", html_text)
            self.assertNotIn("javascript:alert(1)", html_text)
            self.assertIn("\\u003c/script\\u003e\\u003cscript\\u003e", html_text)

            # Zero external CDN script/link/import tags
            self.assertIsNone(re.search(r"<script[^>]+src\s*=", html_text, re.I))
            self.assertIsNone(re.search(r"<link[^>]+href\s*=\s*['\"]?https?:", html_text, re.I))
            self.assertIsNone(re.search(r"@import\s+url\(", html_text, re.I))

            # Round-trip embedded JSON
            payload = _extract_embedded_json(html_text)
            self.assertEqual(payload["blueprints"][0]["root"], xss_str)
            self.assertIsNone(payload["cluster_atlas"]["clusters"][0]["top3_rep_decls"][0]["github_url"])
            self.assertEqual(
                payload["cluster_atlas"]["clusters"][0]["top3_rep_decls"][1]["github_url"],
                "https://github.com/example/repo/blob/1/a.lean#L1",
            )

    def test_symlink_refusal(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            real_target = os.path.join(td, "real.html")
            with open(real_target, "w", encoding="utf-8") as f:
                f.write("keep")
            sym_out = os.path.join(td, "sym.html")
            os.symlink(real_target, sym_out)

            with self.assertRaises(ValueError):
                export_site.export_static_site(None, sym_out)
            with open(real_target, "r", encoding="utf-8") as f:
                self.assertEqual(f.read(), "keep")

            # Also refuse symlinked trim_report input
            real_trim = os.path.join(td, "real_trim.json")
            with open(real_trim, "w", encoding="utf-8") as f:
                json.dump({"schema": "leanre.trim/1"}, f)
            sym_trim = os.path.join(td, "sym_trim.json")
            os.symlink(real_trim, sym_trim)
            with self.assertRaises(ValueError):
                export_site.export_static_site(None, os.path.join(td, "ok.html"), trim_report=sym_trim)

            # Also refuse symlinked portability input
            real_port = os.path.join(td, "real_port.json")
            with open(real_port, "w", encoding="utf-8") as f:
                json.dump({"schema": "leanre.portability/1", "targets": []}, f)
            sym_port = os.path.join(td, "sym_port.json")
            os.symlink(real_port, sym_port)
            with self.assertRaises(ValueError):
                export_site.export_static_site(None, os.path.join(td, "ok2.html"), portability=sym_port)

    def test_portability_embedding_islands_xss_and_demo_mode(self) -> None:
        xss_str = '</script><script>alert("port")</script>'
        with tempfile.TemporaryDirectory() as td:
            port_doc = {
                "schema": "leanre.portability/1",
                "pins": {"kernel_db": "outputs/kernel/kernel.db", "src_root": "src", "elapsed_seconds": 1.23},
                "targets": [
                    {
                        "name": "Demo.IslandA.lead",
                        "kind": "thm",
                        "module": "Demo.IslandA",
                        "sighash": "k1n:aaa",
                        "cone": {"total_decls": 100, "project_decls": 20, "external_decls": 80, "spec_cone_total_decls": 10, "spec_cone_project_decls": 2, "dom_subtree_size": 15, "dom_depth": 2, "module_count": 3, "vn1_forwarding_aliases": 0},
                        "boundary": {"direct_external_decls": 12, "direct_external_type_decls": 4, "direct_call_edges": 50, "distinct_prefixes_total": 3, "top_external_prefixes": [{"prefix": "AlgebraicGeometry", "distinct_decls": 7, "type_decls": 2, "call_edges": 30}]},
                        "contamination": {"tier": "standalone-ready", "reasons": [f"clean {xss_str}"], "axioms": ["propext"], "non_standard_axioms": [], "has_sorry": False, "mega_records": [], "significant_root_dirs": ["Demo"]},
                    },
                    {
                        "name": "Demo.IslandA.sub",
                        "kind": "thm",
                        "module": "Demo.IslandA",
                        "sighash": "k1n:bbb",
                        "cone": {"total_decls": 90, "project_decls": 15, "external_decls": 75, "spec_cone_total_decls": 8, "spec_cone_project_decls": 2, "dom_subtree_size": 10, "dom_depth": 3, "module_count": 2, "vn1_forwarding_aliases": 0},
                        "boundary": {"direct_external_decls": 10, "direct_external_type_decls": 3, "direct_call_edges": 40, "distinct_prefixes_total": 2, "top_external_prefixes": [{"prefix": "AlgebraicGeometry", "distinct_decls": 6, "type_decls": 2, "call_edges": 25}]},
                        "contamination": {"tier": "standalone-ready", "reasons": ["clean"], "axioms": ["propext"], "non_standard_axioms": [], "has_sorry": False, "mega_records": [], "significant_root_dirs": ["Demo"]},
                    },
                    {
                        "name": f"Demo.IslandB.{xss_str}",
                        "kind": "thm",
                        "module": "Demo.IslandB",
                        "sighash": "k1n:ccc",
                        "cone": {"total_decls": 60, "project_decls": 9, "external_decls": 51, "spec_cone_total_decls": 5, "spec_cone_project_decls": 1, "dom_subtree_size": 8, "dom_depth": 2, "module_count": 1, "vn1_forwarding_aliases": 0},
                        "boundary": {"direct_external_decls": 8, "direct_external_type_decls": 2, "direct_call_edges": 20, "distinct_prefixes_total": 2, "top_external_prefixes": [{"prefix": "CategoryTheory", "distinct_decls": 5, "type_decls": 2, "call_edges": 15}]},
                        "contamination": {"tier": "scoped", "reasons": ["scoped"], "axioms": ["propext"], "non_standard_axioms": [], "has_sorry": False, "mega_records": [], "significant_root_dirs": ["Demo"]},
                    },
                ],
                "overlap": {
                    "target_names": ["Demo.IslandA.lead", "Demo.IslandA.sub", f"Demo.IslandB.{xss_str}"],
                    "project_decls_matrix": [[20, 15, 0], [15, 15, 0], [0, 0, 9]],
                    "project_jaccard_matrix": [[1.0, 0.75, 0.0], [0.75, 1.0, 0.0], [0.0, 0.0, 1.0]],
                    "union_summary": {"union_total_decls": 140, "union_project_decls": 29, "union_external_decls": 111, "union_module_count": 4},
                },
            }
            port_path = os.path.join(td, "portability_gems.json")
            with open(port_path, "w", encoding="utf-8") as f:
                json.dump(port_doc, f)

            out_html = os.path.join(td, "port_site.html")
            meta = export_site.export_static_site(None, out_html, portability=port_path)
            self.assertTrue(meta["has_portability"])
            with open(out_html, "r", encoding="utf-8") as f:
                text = f.read()
            self.assertNotIn(xss_str, text)
            self.assertIsNone(re.search(r"<script[^>]+src\s*=", text, re.I))
            payload = _extract_embedded_json(text)
            pt = payload["portability"]
            self.assertEqual(pt["summary"]["islands_count"], 2)
            self.assertEqual(pt["summary"]["pairwise_disjoint_islands"], 2)
            self.assertEqual(pt["summary"]["standalone_ready_count"], 2)
            self.assertEqual(pt["summary"]["scoped_count"], 1)

            # Test --demo end-to-end when leanre-kernel binary is available
            if os.path.exists(kernel.default_binary_path()):
                demo_html = os.path.join(td, "demo_site.html")
                rc = export_site.main(["--demo", "--out", demo_html])
                self.assertEqual(rc, 0)
                self.assertTrue(os.path.isfile(demo_html))
                with open(demo_html, "r", encoding="utf-8") as f:
                    dtext = f.read()
                dpay = _extract_embedded_json(dtext)
                self.assertEqual(dpay["kernel"]["counts"]["live_decls"], 10)
                self.assertIsNotNone(dpay["portability"])
                self.assertGreaterEqual(dpay["portability"]["summary"]["targets_count"], 1)
                self.assertIsNotNone(dpay["circuit"])
                self.assertEqual(dpay["circuit"]["mode"], "macro")
                self.assertTrue(ET.fromstring(dpay["circuit"]["svg"]).tag.endswith("svg"))
                self.assertLess(len(dtext.encode("utf-8")), 250 * 1024, "demo site with circuit should stay compact (<250 KB)")
                self.assertNotIn("data:image/", dtext)

            # Also verify real outputs/portability_gems.json & outputs/kernel/kernel.db when present in repo
            real_gems = os.path.join(_REPO_ROOT, "outputs", "portability_gems.json")
            if os.path.isfile(real_gems) and not os.path.islink(real_gems):
                rh_html = os.path.join(td, "rh_port.html")
                rmeta = export_site.export_static_site(None, rh_html, portability=real_gems)
                self.assertTrue(rmeta["has_portability"])
                with open(rh_html, "r", encoding="utf-8") as f:
                    rpay = _extract_embedded_json(f.read())
                self.assertEqual(rpay["portability"]["summary"]["islands_count"], 4)
                self.assertEqual(rpay["portability"]["summary"]["pairwise_disjoint_islands"], 4)

            real_kdb = os.path.join(_REPO_ROOT, "outputs", "kernel", "kernel.db")
            if os.path.isfile(real_kdb) and not os.path.islink(real_kdb):
                rh_cir_html = os.path.join(td, "rh_circuit_site.html")
                rcmeta = export_site.export_static_site(
                    None,
                    rh_cir_html,
                    portability=real_gems if os.path.isfile(real_gems) else None,
                    kernel_db=real_kdb,
                    with_bundles=False,
                    title="RH Macro Circuit Test",
                )
                self.assertTrue(rcmeta["has_circuit"])
                self.assertLess(rcmeta["bytes"], 512 * 1024, "RH circuit static site should stay compact without bloat")
                with open(rh_cir_html, "r", encoding="utf-8") as f:
                    rcpay = _extract_embedded_json(f.read())
                self.assertIsNotNone(rcpay["circuit"])
                self.assertGreater(rcpay["circuit"]["stats"]["live_decls"], 1_000_000)
                self.assertTrue(ET.fromstring(rcpay["circuit"]["svg"]).tag.endswith("svg"))

    def test_split_dir_demo_and_safety(self) -> None:
        if not os.path.exists(kernel.default_binary_path()):
            self.skipTest("leanre-kernel release binary not built")
        import leanre as leanre_cli
        if not hasattr(leanre_cli, "main"):
            from leanre import leanre as leanre_cli  # type: ignore[no-redef]

        with tempfile.TemporaryDirectory() as td:
            out_dir = os.path.join(td, "site_demo")
            rc = leanre_cli.main(["export-site", "--demo", "--split-dir", out_dir])
            self.assertEqual(rc, 0)

            nojekyll = os.path.join(out_dir, ".nojekyll")
            self.assertTrue(os.path.isfile(nojekyll))
            self.assertEqual(os.path.getsize(nojekyll), 0)

            idx_path = os.path.join(out_dir, "index.html")
            self.assertTrue(os.path.isfile(idx_path))
            with open(idx_path, "r", encoding="utf-8") as f:
                idx_html = f.read()
            self.assertIsNone(re.search(r"<script[^>]+src\s*=\s*['\"]?https?:", idx_html, re.I))
            self.assertIsNone(re.search(r"<link[^>]+href\s*=\s*['\"]?https?:", idx_html, re.I))

            with open(os.path.join(out_dir, "manifest.json"), "r", encoding="utf-8") as f:
                m = json.load(f)
            self.assertEqual(m["schema"], "leanre.site_manifest/1")
            self.assertTrue(m["demo_mode"])
            self.assertEqual(m["repo_name"], "tiny_demo")
            for k in (
                "title", "repo_name", "repo_url", "pinned_commit", "src_prefix",
                "generated_at", "demo_mode", "stats", "overview_pillars",
                "findings", "dossiers", "research", "blueprints",
                "circuits", "assets", "search",
            ):
                self.assertIn(k, m)

            st = m["stats"]
            self.assertEqual(st["total_decls"], 17)
            self.assertEqual(st["live_decls"], 10)
            self.assertEqual(st["dead_decls"], 7)
            self.assertEqual(st["edges"], 39)
            self.assertEqual(st["total_files"], 5)
            self.assertEqual(st["total_lines"], 88)
            self.assertEqual(st["circuits_bundle_count"], 1)
            self.assertEqual(st["circuits_theorem_count"], 7)
            self.assertGreaterEqual(st["search_entries"], 10)
            self.assertGreater(len(m["overview_pillars"]), 0)
            self.assertEqual(m["findings"], [])
            self.assertEqual(m["dossiers"], [])
            self.assertEqual(m["blueprints"], [])
            self.assertIsNotNone(m["assets"]["portability"])
            self.assertIsNotNone(m["assets"]["outline"])
            self.assertEqual(m["assets"]["outline"], "data/outline.json")
            self.assertIsNone(m["assets"]["atlas"])
            self.assertIsNone(m["assets"]["embedding_2d"])
            self.assertIsNone(m["assets"]["experiments"])
            self.assertIsNone(m["assets"]["benchmark"])
            self.assertIsNone(m["assets"]["cluster_labels"])

            # Verify tiny_demo outline.json (< 5 KB)
            outline_path = os.path.join(out_dir, m["assets"]["outline"])
            self.assertTrue(os.path.isfile(outline_path))
            self.assertLess(os.path.getsize(outline_path), 5 * 1024)
            with open(outline_path, "r", encoding="utf-8") as f:
                outline = json.load(f)
            self.assertEqual(outline["schema"], "leanre.outline/1")
            self.assertGreater(len(outline["spine"]), 0)
            self.assertGreater(len(outline["folders"]), 0)
            self.assertEqual(outline["folder_stats"]["total_modules"], 5)
            self.assertIn("TinyDemo.main_theorem", outline["neighbors"])
            self.assertGreater(len(outline["neighbors"]["TinyDemo.main_theorem"]["depends_on"]), 0)

            # Verify macro + bundle + theorem circuit shards and dark/light SVG XML
            macro_path = os.path.join(out_dir, m["circuits"]["macro"])
            self.assertTrue(os.path.isfile(macro_path))
            with open(macro_path, "r", encoding="utf-8") as f:
                macro_doc = json.load(f)
            self.assertEqual(macro_doc["mode"], "macro")
            self.assertTrue(ET.fromstring(macro_doc["svg_dark"]).tag.endswith("svg"))
            self.assertTrue(ET.fromstring(macro_doc["svg_light"]).tag.endswith("svg"))

            for entry in m["circuits"]["bundles"] + m["circuits"]["theorems"]:
                cpath = os.path.join(out_dir, entry["path"])
                self.assertTrue(os.path.isfile(cpath), f"Missing circuit shard {cpath}")
                with open(cpath, "r", encoding="utf-8") as f:
                    cdoc = json.load(f)
                self.assertTrue(ET.fromstring(cdoc["svg_dark"]).tag.endswith("svg"))
                self.assertTrue(ET.fromstring(cdoc["svg_light"]).tag.endswith("svg"))
                # Zero raw .lean proof bodies in step tooltips/full_name
                for nd in (cdoc.get("payload") or {}).get("nodes") or []:
                    if str(nd.get("id") or "").startswith("step:"):
                        self.assertNotIn(":= by", str(nd.get("full_name") or ""))

            # Verify search shards
            search_meta = m["search"]
            self.assertEqual(search_meta["shard_prefix_len"], 2)
            self.assertIn("ma", search_meta["shards"])
            found_main = False
            for pfx in search_meta["shards"]:
                spath = os.path.join(out_dir, search_meta["shard_template"].replace("{prefix}", pfx))
                self.assertTrue(os.path.isfile(spath))
                self.assertLess(os.path.getsize(spath), 150 * 1024)
                with open(spath, "r", encoding="utf-8") as f:
                    sdata = json.load(f)
                rows = sdata if isinstance(sdata, list) else sdata.get("entries", [])
                for row in rows:
                    self.assertEqual(len(row), 8)
                    if row[0] == "TinyDemo.main_theorem":
                        found_main = True
                        self.assertEqual(row[1], "thm")
                        self.assertEqual(row[2], 10)
                        self.assertEqual(row[3], 1)
                        self.assertTrue(bool(row[6]))
            self.assertTrue(found_main)

            # Strict size, no-.lean, and no workstation path leakage checks
            total_bytes = 0
            for root, _dirs, files in os.walk(out_dir):
                for fn in files:
                    self.assertFalse(fn.endswith(".lean"))
                    fp = os.path.join(root, fn)
                    sz = os.path.getsize(fp)
                    self.assertLess(sz, 25 * 1024 * 1024)
                    total_bytes += sz
                    with open(fp, "r", encoding="utf-8", errors="replace") as f:
                        txt = f.read()
                    self.assertIsNone(export_site._FORBIDDEN_HOST_PATH_RE.search(txt))
            self.assertLess(total_bytes, 900 * 1024)

            # Verify CLI rejects missing --out and --split-dir with exit code 2
            import io
            from contextlib import redirect_stderr
            with redirect_stderr(io.StringIO()):
                rc_err = leanre_cli.main(["export-site", "--demo"])
            self.assertEqual(rc_err, 2)

    def test_split_dir_docs_blueprints_graceful_missing_and_fallback_html(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            # Symlinked split_dir must be refused
            real_d = os.path.join(td, "real_out")
            os.makedirs(real_d, exist_ok=True)
            sym_d = os.path.join(td, "sym_out")
            os.symlink(real_d, sym_d)
            with self.assertRaises(ValueError):
                export_site.export_split_site(sym_d)

            # Empty split_dir with missing site_assets -> crisp fallback HTML and empty lists
            empty_out = os.path.join(td, "empty_site")
            orig_assets = export_site.SITE_ASSETS_DIR
            try:
                export_site.SITE_ASSETS_DIR = os.path.join(td, "no_such_assets")
                res = export_site.export_split_site(empty_out, title="Graceful Empty")
            finally:
                export_site.SITE_ASSETS_DIR = orig_assets
            self.assertEqual(res["copied_site_assets"], [])
            with open(os.path.join(empty_out, "index.html"), "r", encoding="utf-8") as f:
                fb_html = f.read()
            self.assertIn("Graceful Empty", fb_html)
            self.assertIn("./manifest.json", fb_html)

            # Synthetic findings, analysis (with README categories), research (skip sources/), decomp
            fdir = os.path.join(td, "findings")
            adir = os.path.join(td, "analysis")
            rdir = os.path.join(td, "research")
            ddir = os.path.join(td, "decomp")
            for d in (fdir, adir, rdir, os.path.join(rdir, "sources"), ddir):
                os.makedirs(d, exist_ok=True)
            with open(os.path.join(fdir, "proof-map.md"), "w", encoding="utf-8") as f:
                f.write("# Proof Map Title\n\nSummary paragraph here.\n")
            with open(os.path.join(adir, "README.md"), "w", encoding="utf-8") as f:
                f.write("# Index\n\n## Core\n| [Spine](spine_map.md) | — | desc |\n")
            with open(os.path.join(adir, "spine_map.md"), "w", encoding="utf-8") as f:
                f.write("# Spine Dossier\n\nDossier text.\n")
            with open(os.path.join(rdir, "01_notes.md"), "w", encoding="utf-8") as f:
                f.write("# Research One\n\nResearch body.\n")
            with open(os.path.join(rdir, "sources", "raw_secret.md"), "w", encoding="utf-8") as f:
                f.write("# MUST NOT BE COPIED\n")
            with open(os.path.join(ddir, "spine_map.json"), "w", encoding="utf-8") as f:
                json.dump({
                    "schema": "leanre.decomp/v1",
                    "pillar": "spine",
                    "root": "Demo.Main",
                    "nodes": [{"id": "Demo.Main", "status": "READ"}, {"id": "Demo.Op", "status": "OPAQUE"}],
                    "edges": [],
                }, f)

            full_out = os.path.join(td, "full_site")
            meta = export_site.export_split_site(
                full_out,
                decomp_dir=ddir,
                findings_dir=fdir,
                analysis_dir=adir,
                research_dir=rdir,
                max_circuits=2,
                search_limit=50,
            )
            self.assertEqual(meta["stats"]["findings_count"], 1)
            self.assertEqual(meta["stats"]["dossiers_count"], 1)
            self.assertEqual(meta["stats"]["blueprints_count"], 1)
            self.assertFalse(os.path.exists(os.path.join(full_out, "data", "research", "raw_secret.md")))
            with open(os.path.join(full_out, "manifest.json"), "r", encoding="utf-8") as f:
                fm = json.load(f)
            self.assertEqual(fm["dossiers"][0]["category"], "Core")
            self.assertEqual(fm["blueprints"][0]["non_opaque_count"], 1)
            self.assertEqual(fm["blueprints"][0]["node_count"], 2)
            self.assertIsNone(fm["assets"]["atlas"])

    def test_split_dir_atlas_asset_path_stripping_and_cli_atlas_subcommand(self) -> None:
        import io
        from contextlib import redirect_stdout
        import leanre as leanre_cli
        if not hasattr(leanre_cli, "main"):
            from leanre import leanre as leanre_cli  # type: ignore[no-redef]

        with tempfile.TemporaryDirectory() as td:
            out_parent = os.path.join(td, "outputs")
            ddir = os.path.join(out_parent, "decomp")
            os.makedirs(ddir, exist_ok=True)
            with open(os.path.join(ddir, "spine_map.json"), "w", encoding="utf-8") as f:
                json.dump({"schema": "leanre.decomp/v1", "pillar": "spine", "root": "A", "nodes": [], "edges": []}, f)

            # Write sibling outputs/atlas_summary.json containing absolute & forbidden paths in inputs.*
            fake_home = "/" + "home" + "/alice/proj/sub/tier2.db"
            abs_kernel = os.path.join(td, "abs_dir", "kernel.db")
            atlas_src = os.path.join(out_parent, "atlas_summary.json")
            with open(atlas_src, "w", encoding="utf-8") as f:
                json.dump(
                    {
                        "schema": "leanre.atlas/1",
                        "inputs": {
                            "kernel_db": abs_kernel,
                            "tier2_db": fake_home,
                            "rel_note": "outputs/atlas_summary.json",
                            "numpy_accelerated": False,
                        },
                        "runtime_sec": 0.12,
                        "alien_twins": {"partitions": {}, "top_alien_pairs": []},
                        "hic_matrix": {"n_live_decls": 0, "grid_bins": 256},
                        "synteny": {"hit_totals": {"total_matches": 0}},
                    },
                    f,
                )

            # 1) Auto-discovered as sibling of decomp_dir
            site_sib = os.path.join(td, "site_sib")
            with redirect_stdout(io.StringIO()):
                rc = leanre_cli.main([
                    "export-site",
                    "--split-dir", site_sib,
                    "--decomp-dir", ddir,
                    "--max-circuits", "0",
                ])
            self.assertEqual(rc, 0)
            with open(os.path.join(site_sib, "manifest.json"), "r", encoding="utf-8") as f:
                ms = json.load(f)
            self.assertEqual(ms["assets"]["atlas"], "data/atlas_summary.json")
            copied_atlas = os.path.join(site_sib, "data", "atlas_summary.json")
            self.assertTrue(os.path.isfile(copied_atlas))
            with open(copied_atlas, "r", encoding="utf-8") as f:
                ad = json.load(f)
            self.assertEqual(ad["schema"], "leanre.atlas/1")
            self.assertEqual(ad["inputs"]["kernel_db"], "kernel.db")
            self.assertEqual(ad["inputs"]["tier2_db"], "tier2.db")
            self.assertEqual(ad["inputs"]["rel_note"], "outputs/atlas_summary.json")
            self.assertIsNone(export_site._FORBIDDEN_HOST_PATH_RE.search(json.dumps(ad)))

            # 2) Explicit --atlas-summary flag on export-site CLI
            site_exp = os.path.join(td, "site_exp")
            with redirect_stdout(io.StringIO()):
                rc2 = leanre_cli.main([
                    "export-site",
                    "--split-dir", site_exp,
                    "--atlas-summary", atlas_src,
                    "--max-circuits", "0",
                ])
            self.assertEqual(rc2, 0)
            with open(os.path.join(site_exp, "manifest.json"), "r", encoding="utf-8") as f:
                me = json.load(f)
            self.assertEqual(me["assets"]["atlas"], "data/atlas_summary.json")

            # 3) Symlinked atlas_summary must be refused
            sym_atlas = os.path.join(td, "sym_atlas.json")
            os.symlink(atlas_src, sym_atlas)
            with self.assertRaises(ValueError):
                export_site.export_split_site(os.path.join(td, "site_sym"), atlas_summary=sym_atlas)

            # 4) `leanre atlas --help` dispatches cleanly to leanre.atlas
            help_buf = io.StringIO()
            with redirect_stdout(help_buf):
                with self.assertRaises(SystemExit) as cm:
                    leanre_cli.main(["atlas", "--help"])
            self.assertEqual(cm.exception.code, 0)
            self.assertIn("--kernel-db", help_buf.getvalue())
            self.assertIn("--synteny-png", help_buf.getvalue())

    def test_embedding_experiments_outline_gallery_and_cli_subcommands(self) -> None:
        import io
        from contextlib import redirect_stdout
        import leanre as leanre_cli
        if not hasattr(leanre_cli, "main"):
            from leanre import leanre as leanre_cli  # type: ignore[no-redef]

        with tempfile.TemporaryDirectory() as td:
            out_parent = os.path.join(td, "outputs")
            ddir = os.path.join(out_parent, "decomp")
            fdir = os.path.join(out_parent, "flirt")
            os.makedirs(ddir, exist_ok=True)
            os.makedirs(fdir, exist_ok=True)
            with open(os.path.join(ddir, "spine_map.json"), "w", encoding="utf-8") as f:
                json.dump({"schema": "leanre.decomp/v1", "pillar": "spine", "root": "A", "nodes": [], "edges": []}, f)

            fake_home = "/" + "home" + "/alice/proj/kernel.db"
            emb_src = os.path.join(out_parent, "embedding_2d.json")
            with open(emb_src, "w", encoding="utf-8") as f:
                json.dump({
                    "schema": "leanre.embedding_2d/1",
                    "inputs": {"kernel_db": fake_home, "leanre_db": os.path.join(td, "leanre.db"), "numpy_version": "2.0.0"},
                    "layers": {"clusters_141": {"count": 1, "points": []}, "landmarks": {"count": 1, "points": []}},
                }, f)

            exp_src = os.path.join(out_parent, "brainstorm_experiment.json")
            with open(exp_src, "w", encoding="utf-8") as f:
                json.dump({
                    "schema": "leanre.brainstorm_experiment/1",
                    "title": "Blind Two-Arm Study",
                    "summary": {"total_raw_ideas": 142},
                }, f)

            with open(os.path.join(fdir, "cluster_labels_141.json"), "w", encoding="utf-8") as f:
                json.dump({
                    "schema": "leanre.flirt_atlas/v1",
                    "clusters": [
                        {
                            "cluster_id": "BP001",
                            "pillar": "pillar_a",
                            "root_decl": "Demo.Main",
                            "counts": {"live_decls": 12, "live_modules": 3},
                            "blinded_label": {"label": "Synthetic cluster", "primary_domain": "algebra"},
                            "mismatch_audit": {"status": "aligned", "severity": "none"},
                        }
                    ],
                }, f)

            # Synthetic leanre.db with modules for real folder_stats
            ldb = os.path.join(out_parent, "leanre.db")
            lcon = sqlite3.connect(ldb)
            lcon.executescript(
                "CREATE TABLE meta(key TEXT PRIMARY KEY, value_json TEXT NOT NULL);"
                "CREATE TABLE modules(id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL, file_path TEXT NOT NULL, "
                "lines_wc INTEGER NOT NULL, decl_count INTEGER NOT NULL, fan_in INTEGER NOT NULL);"
                "CREATE TABLE declarations(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, "
                "module TEXT NOT NULL, line_no INTEGER NOT NULL);"
                "INSERT INTO modules VALUES (1, 'Pkg.Alpha.One', 'Pkg/Alpha/One.lean', 40, 3, 2);"
                "INSERT INTO modules VALUES (2, 'Pkg.Alpha.Two', 'Pkg/Alpha/Two.lean', 60, 4, 1);"
                "INSERT INTO modules VALUES (3, 'Pkg.Beta.Three', 'Pkg/Beta/Three.lean', 30, 2, 0);"
            )
            lcon.commit()
            lcon.close()

            # 1) Sibling auto-discovery via --decomp-dir
            site_sib = os.path.join(td, "site_sib")
            with redirect_stdout(io.StringIO()):
                rc = leanre_cli.main([
                    "export-site",
                    "--split-dir", site_sib,
                    "--decomp-dir", ddir,
                    "--src-prefix", "src/",
                    "--max-circuits", "0",
                ])
            self.assertEqual(rc, 0)
            with open(os.path.join(site_sib, "manifest.json"), "r", encoding="utf-8") as f:
                ms = json.load(f)
            self.assertEqual(ms["assets"]["embedding_2d"], "data/embedding_2d.json")
            self.assertIsNone(ms["assets"]["experiments"])
            self.assertEqual(ms["assets"]["outline"], "data/outline.json")
            self.assertFalse(os.path.exists(os.path.join(site_sib, "data", "brainstorm_experiment.json")))

            with open(os.path.join(site_sib, "data", "embedding_2d.json"), "r", encoding="utf-8") as f:
                emb_out = json.load(f)
            self.assertEqual(emb_out["inputs"]["kernel_db"], "kernel.db")
            self.assertEqual(emb_out["inputs"]["leanre_db"], "leanre.db")
            self.assertIsNone(export_site._FORBIDDEN_HOST_PATH_RE.search(json.dumps(emb_out)))

            outline_file = os.path.join(site_sib, "data", "outline.json")
            self.assertLessEqual(os.path.getsize(outline_file), 250 * 1024)
            with open(outline_file, "r", encoding="utf-8") as f:
                ol = json.load(f)
            self.assertEqual(ol["schema"], "leanre.outline/1")
            self.assertEqual(ol["src_prefix"], "src/")
            self.assertEqual(ol["folder_stats"]["total_modules"], 3)
            self.assertEqual(ol["folders"][0]["path"], "Pkg/Alpha")
            self.assertEqual(ol["folders"][0]["files"], 2)
            self.assertEqual(ol["clusters"][0]["id"], "BP001")
            self.assertEqual(ol["clusters"][0]["count"], 12)

            # 2) Explicit --embedding-2d flag (brainstorm_experiment.json is never exported even if passed)
            site_exp = os.path.join(td, "site_exp")
            with redirect_stdout(io.StringIO()):
                rc2 = leanre_cli.main([
                    "export-site",
                    "--split-dir", site_exp,
                    "--embedding-2d", emb_src,
                    "--experiments", exp_src,
                    "--max-circuits", "0",
                ])
            self.assertEqual(rc2, 0)
            with open(os.path.join(site_exp, "manifest.json"), "r", encoding="utf-8") as f:
                me = json.load(f)
            self.assertEqual(me["assets"]["embedding_2d"], "data/embedding_2d.json")
            self.assertIsNone(me["assets"]["experiments"])
            self.assertFalse(os.path.exists(os.path.join(site_exp, "data", "brainstorm_experiment.json")))

            sym_emb = os.path.join(td, "sym_emb.json")
            os.symlink(emb_src, sym_emb)
            with self.assertRaises(ValueError):
                export_site.export_split_site(os.path.join(td, "site_sym1"), embedding_2d=sym_emb)

            # 3) --gallery-dir exports into <gallery>/p/<slug>/ alongside projects.json
            if os.path.exists(kernel.default_binary_path()):
                gal_dir = os.path.join(td, "gallery_out")
                with redirect_stdout(io.StringIO()):
                    rc_g = leanre_cli.main([
                        "export-site",
                        "--demo",
                        "--gallery-dir", gal_dir,
                    ])
                self.assertEqual(rc_g, 0)
                self.assertTrue(os.path.isfile(os.path.join(gal_dir, "index.html")))
                self.assertTrue(os.path.isfile(os.path.join(gal_dir, ".nojekyll")))
                self.assertTrue(os.path.isfile(os.path.join(gal_dir, "projects.json")))
                self.assertTrue(os.path.isfile(os.path.join(gal_dir, "p", "tiny-demo", "manifest.json")))
                self.assertTrue(os.path.isfile(os.path.join(gal_dir, "p", "tiny-demo", "index.html")))
                self.assertTrue(os.path.isfile(os.path.join(gal_dir, "p", "tiny-demo", "data", "outline.json")))
                with open(os.path.join(gal_dir, "projects.json"), "r", encoding="utf-8") as f:
                    reg = json.load(f)
                self.assertEqual(reg["schema"], "leanre.projects_registry/1")
                self.assertEqual(reg["count"], 1)
                self.assertEqual(reg["projects"][0]["slug"], "tiny-demo")
                self.assertTrue(reg["projects"][0]["has_kernel_export"])
                self.assertFalse(reg["projects"][0]["source_only"])

                sym_gal = os.path.join(td, "sym_gal")
                os.symlink(gal_dir, sym_gal)
                with self.assertRaises(ValueError):
                    export_site.export_gallery_project(sym_gal, demo_mode=True)

            # 4) `leanre embedding --help` and `leanre gallery --help` dispatch cleanly
            for subcmd, flag in (("embedding", "--knn-k"), ("gallery", "build-default")):
                buf = io.StringIO()
                with redirect_stdout(buf):
                    with self.assertRaises(SystemExit) as cm:
                        leanre_cli.main([subcmd, "--help"])
                self.assertEqual(cm.exception.code, 0)
                self.assertIn(flag, buf.getvalue())

    def test_plain_text_from_tex_decomp_titles_and_asset_cleaning(self) -> None:
        raw_sum = (
            r"Dirichlet $L$-functions do not vanish on $\operatorname{Re}(s) > 1/2$ "
            r"except at $\chi = 1, s = 1$; see $\mathrm{GL}_n$, $\mathrm{Ш}^1$, "
            r"$\frac{1}{2}$, $\tfrac{C_u}{2}$, $\Bigl(\log\Omega\Bigr)$."
        )
        cleaned = export_site.plain_text_from_tex(raw_sum)
        self.assertNotIn("$", cleaned)
        self.assertNotIn("\\", cleaned)
        self.assertIn("Re(s) > 1/2", cleaned)
        self.assertIn("χ = 1", cleaned)
        self.assertIn("GL_n", cleaned)
        self.assertIn("Ш¹", cleaned)
        self.assertIn("1/2", cleaned)
        self.assertIn("log Ω", cleaned)

        # Every outputs/decomp/*.json leanre.decomp/v1 stem has an explicit friendly title
        decomp_dir = os.path.join(_REPO_ROOT, "outputs", "decomp")
        if os.path.isdir(decomp_dir):
            for fn in os.listdir(decomp_dir):
                if not fn.endswith(".json"):
                    continue
                with open(os.path.join(decomp_dir, fn), "r", encoding="utf-8") as f:
                    doc = json.load(f)
                if doc.get("schema") == "leanre.decomp/v1":
                    stem = fn[:-5]
                    self.assertIn(stem, export_site._DECOMP_FRIENDLY_TITLES)

        cl = export_site._clean_cluster_labels({
            "clusters": [{
                "cluster_id": "BP001",
                "mismatch_audit": {
                    "reason": "[M] Blinded (algebra_rings_poly, high) and Tier1 (algebra_comm_ring) disagree",
                },
            }]
        })
        reason = cl["clusters"][0]["mismatch_audit"]["reason"]
        self.assertNotIn("[M]", reason)
        self.assertNotIn("Blinded", reason)
        self.assertNotIn("Tier1", reason)

        xb = export_site._clean_xrepo_benchmark({
            "repos": [{
                "repo": "PrimeNumberTheoremAnd",
                "decls_source": {"sorry_hits": 205, "sorry_hits_total_uncapped": 231},
            }],
            "xrepo_issue_verification": [{
                "id": "XREPO-01",
                "verified_685ebbb": "Verified at 685ebbb",
            }],
        })
        self.assertEqual(xb["repos"][0]["decls_source"]["sorry_hits"], 231)
        self.assertNotIn("XREPO-01", xb["xrepo_issue_verification"][0]["id"])
        self.assertNotIn("685ebbb", xb["xrepo_issue_verification"][0]["verified_685ebbb"])


if __name__ == "__main__":
    unittest.main()
