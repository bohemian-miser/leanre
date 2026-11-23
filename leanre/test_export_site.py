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
            self.assertIsNone(m["assets"]["benchmark"])
            self.assertIsNone(m["assets"]["cluster_labels"])

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
            self.assertLess(total_bytes, 600 * 1024)

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


if __name__ == "__main__":
    unittest.main()
