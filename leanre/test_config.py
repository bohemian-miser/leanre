#!/usr/bin/env python3
"""Unit & integration tests for leanre.config, pyproject.toml, leanre.toml, and RH decoupling."""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import compute_sweep
import config
import forensics
import kernel
import ndjson
import scanner


def _write_generic_ndjson(path: str) -> None:
    """Write a minimal non-RH Lean 4 NDJSON v3.1.0 export."""
    records = [
        {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"}, "format": {"version": "3.1.0"}}},
        {"in": 1, "str": {"pre": 0, "str": "MyLib"}},
        {"in": 2, "str": {"pre": 1, "str": "HelperDef"}},
        {"in": 3, "str": {"pre": 1, "str": "MainTheorem"}},
        {"in": 4, "str": {"pre": 0, "str": "sorryAx"}},
        {"ie": 0, "sort": 0},
        {"ie": 1, "const": {"name": 2, "us": []}},
        {"ie": 2, "const": {"name": 4, "us": []}},
        {"axiom": {"name": 4, "type": 0, "levelParams": [], "isUnsafe": False}},
        {"def": {"name": 2, "type": 0, "value": 0, "levelParams": [], "safety": "safe"}},
        {"thm": {"name": 3, "type": 1, "value": 2, "levelParams": []}},
    ]
    with open(path, "w", encoding="utf-8") as f:
        for rec in records:
            f.write(json.dumps(rec) + "\n")


class TestPackagingAndExampleProfile(unittest.TestCase):
    def test_pyproject_toml_pep621_metadata(self):
        pp_path = Path(_REPO_ROOT) / "pyproject.toml"
        self.assertTrue(pp_path.is_file(), "pyproject.toml missing")
        with pp_path.open("rb") as f:
            data = tomllib.load(f)
        proj = data["project"]
        self.assertEqual(proj["name"], "leanre")
        self.assertEqual(proj["requires-python"], ">=3.11")
        self.assertEqual(proj["dependencies"], [])
        lic = proj["license"]
        lic_text = lic["text"] if isinstance(lic, dict) else lic
        self.assertEqual(lic_text, "AGPL-3.0-or-later")
        self.assertEqual(proj["scripts"]["leanre"], "leanre.leanre:main")

    def test_ci_workflow_runs_python_and_rust_tests(self):
        ci_path = Path(_REPO_ROOT) / ".github" / "workflows" / "ci.yml"
        self.assertTrue(ci_path.is_file(), ".github/workflows/ci.yml missing")
        txt = ci_path.read_text(encoding="utf-8")
        self.assertIn("python3 -m unittest discover -s leanre -v", txt)
        self.assertIn("cargo test", txt)
        self.assertIn("leanre/kernel-rs", txt)

    def test_example_leanre_toml_profile(self):
        cfg_path = Path(_REPO_ROOT) / "leanre.toml"
        self.assertTrue(cfg_path.is_file(), "leanre.toml missing")
        cfg = config.load_config(cfg_path)
        self.assertEqual(cfg.project_name, "riemann-hypothesis")
        self.assertEqual(cfg.root_module, "Main")
        self.assertEqual(cfg.pinned_commit, "40e56bab026552e089d7afcfeff08d2defb9c005")
        self.assertIn("{commit}", cfg.upstream_url_template)
        self.assertEqual(len(cfg.headline_roots), 5)
        self.assertIn("riemannHypothesis", cfg.headline_roots)
        self.assertEqual(set(cfg.root_groups.keys()), {"RH", "GRH"})
        self.assertEqual(len(cfg.kernel_root_specs()), 5)
        self.assertTrue(cfg.rh_gates)
        self.assertEqual(len(cfg.timeout_modules), 5)
        self.assertEqual(len(cfg.slow_targets), 5)
        self.assertGreaterEqual(len(cfg.extra_regexes), 1)
        # Round-trip through render_toml -> tomllib
        rt = config.LeanreConfig.from_dict(tomllib.loads(config.render_toml(cfg)))
        self.assertEqual(rt.headline_roots, cfg.headline_roots)
        self.assertEqual(rt.timeout_modules, cfg.timeout_modules)
        self.assertEqual(rt.pinned_commit, cfg.pinned_commit)

        # Compatibility with compact examples/tiny_demo/leanre.toml if present
        demo_toml = Path(_REPO_ROOT) / "examples" / "tiny_demo" / "leanre.toml"
        if demo_toml.is_file():
            dcfg = config.load_config(demo_toml)
            self.assertEqual(dcfg.project_name, "tiny_demo")
            self.assertEqual(dcfg.root_module, "Main")
            self.assertIn("TinyDemo.main_theorem", dcfg.headline_roots)
            self.assertEqual(dcfg.kernel_root_specs(), ["TinyDemo.main_theorem:DEMO"])


class TestConfigDiscoveryAndInit(unittest.TestCase):
    def test_init_discovers_lakefile_toml_and_manifest(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "lakefile.toml").write_text(
                'name = "SamplePkg"\n'
                'defaultTargets = ["SamplePkg"]\n'
                '[[require]]\n'
                'name = "mathlib"\n'
                '[[lean_lib]]\n'
                'name = "SamplePkg"\n'
                'globs = ["SamplePkg", "SampleEntry"]\n',
                encoding="utf-8",
            )
            (root / "lake-manifest.json").write_text(
                json.dumps({"packages": [{"name": "batteries", "inherited": False}]}),
                encoding="utf-8",
            )
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n", encoding="utf-8")
            (root / "SamplePkg").mkdir()
            (root / "SamplePkg.lean").write_text(
                "import SamplePkg.Core\ntheorem sample_main : True := trivial\n",
                encoding="utf-8",
            )
            (root / "SampleEntry.lean").write_text(
                "import SamplePkg\ntheorem sample_entry : True := trivial\n",
                encoding="utf-8",
            )
            (root / "SamplePkg" / "Core.lean").write_text(
                "def helperVal : Nat := 1\n",
                encoding="utf-8",
            )

            out_toml = root / "leanre.toml"
            rc = config.cmd_init(
                argparse.Namespace(
                    repo_dir=str(root),
                    out=str(out_toml),
                    force=False,
                    dry_run=False,
                    json=False,
                )
            )
            self.assertEqual(rc, 0)
            self.assertTrue(out_toml.is_file())

            # Without --force, second init refuses to overwrite
            rc2 = config.cmd_init(
                argparse.Namespace(
                    repo_dir=str(root),
                    out=str(out_toml),
                    force=False,
                    dry_run=False,
                    json=False,
                )
            )
            self.assertEqual(rc2, 1)

            cfg = config.load_config(out_toml)
            self.assertEqual(cfg.project_name, "SamplePkg")
            self.assertEqual(cfg.src_dir, ".")
            self.assertEqual(cfg.root_module, "SamplePkg")
            self.assertEqual(cfg.source_roots, ["SamplePkg"])
            self.assertIn("mathlib", cfg.dependencies)
            self.assertIn("batteries", cfg.dependencies)
            self.assertIn("sample_main", cfg.headline_roots)
            self.assertIn("sample_entry", cfg.headline_roots)
            self.assertFalse(cfg.rh_gates)
            self.assertEqual(cfg.lean_toolchain, "leanprover/lean4:v4.35.0")

    def test_init_discovers_lakefile_lean_src_dir_layout(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "lakefile.lean").write_text(
                'import Lake\nopen Lake DSL\npackage «toy» where\n  srcDir := "src"\n'
                '@[default_target]\nlean_lib Toy where\nrequire mathlib from git "https://example.invalid"\n',
                encoding="utf-8",
            )
            (root / "src" / "Toy").mkdir(parents=True)
            (root / "src" / "Toy.lean").write_text(
                "import Toy.Sub\ntheorem toy_goal : True := trivial\n",
                encoding="utf-8",
            )
            (root / "src" / "Toy" / "Sub.lean").write_text("def subDef : Nat := 2\n", encoding="utf-8")

            cfg, meta = config.discover_project(root)
            self.assertEqual(cfg.project_name, "toy")
            self.assertEqual(cfg.src_dir, "src")
            self.assertEqual(cfg.root_module, "Toy")
            self.assertEqual(cfg.source_roots, ["src"])
            self.assertEqual(meta["lakefile"], "lakefile.lean")
            self.assertIn("toy_goal", cfg.headline_roots)


class TestGenericRepoDecoupling(unittest.TestCase):
    def test_scanner_and_forensics_decoupled_from_rh(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td) / "repo"
            (root / "MyPkg").mkdir(parents=True)
            (root / "MyPkg.lean").write_text(
                "import MyPkg.Alpha\nimport MyPkg.Beta\ntheorem my_root_thm : True := trivial\n",
                encoding="utf-8",
            )
            (root / "MyPkg" / "Alpha.lean").write_text(
                "def alphaDef : Nat := 7\n-- custom_marker_hit\ntheorem alpha_thm : True := by\n  have x := custom_marker_hit\n  trivial\n",
                encoding="utf-8",
            )
            (root / "MyPkg" / "Beta.lean").write_text(
                "import MyPkg.Alpha\ntheorem beta_thm : True := trivial\n",
                encoding="utf-8",
            )

            db_path = os.path.join(td, "generic.db")
            stats = scanner.run_scan(str(root), db_path, root_module="MyPkg", workers=1, verbose=False)
            self.assertEqual(stats["modules"], 3)
            self.assertEqual(stats["root_module"], "MyPkg")
            # No RH timeout/slow targets injected by default
            self.assertNotIn("lean4lean_timeout", stats["forensic_module_counts"])
            self.assertNotIn("slow_con_leche", stats["forensic_module_counts"])

            # Custom profile regex is picked up when supplied via config
            custom_cfg = config.LeanreConfig(
                project_name="MyPkg",
                root_module="MyPkg",
                src_dir=".",
                extra_regexes=[config.ForensicRegexSpec(tag="custom_tag", pattern=r"\bcustom_marker_hit\b")],
            )
            stats_custom = scanner.run_scan(
                str(root), db_path, root_module="auto", workers=1, verbose=False, config=custom_cfg
            )
            self.assertEqual(stats_custom["forensic_module_counts"].get("custom_tag"), 1)

            # Forensics on generic repo passes cleanly without RH gate exit 2
            rep_p = os.path.join(td, "rep.json")
            bun_p = os.path.join(td, "bun.json")
            dos_p = os.path.join(td, "dos.md")
            rc_generic = forensics.main(
                ["--db", db_path, "--out-report", rep_p, "--out-bundle", bun_p, "--out-dossier", dos_p, "--quiet"]
            )
            self.assertEqual(rc_generic, 0)
            rep = json.loads(Path(rep_p).read_text(encoding="utf-8"))
            self.assertFalse(rep["meta"]["acceptance_gates"]["rh_gates_enabled"])
            self.assertTrue(rep["meta"]["acceptance_gates"]["all_passed"])

            # Opt-in --rh-gates fails with exit 2 on non-RH corpus
            rc_rh = forensics.main(
                [
                    "--db", db_path,
                    "--out-report", rep_p,
                    "--out-bundle", bun_p,
                    "--out-dossier", dos_p,
                    "--rh-gates",
                    "--quiet",
                ]
            )
            self.assertEqual(rc_rh, 2)

    def test_ndjson_generic_roots_and_prefix_inference(self):
        self.assertEqual(
            ndjson.infer_module_prefix("_private.Carleson.Metric.0.aux_lemma", headline_roots={"Carleson.main"}),
            "Carleson.Metric",
        )
        self.assertEqual(
            ndjson.infer_module_prefix("MyLib.MainTheorem", headline_roots={"MyLib.MainTheorem"}),
            "Headline",
        )
        with tempfile.TemporaryDirectory() as td:
            nd_path = os.path.join(td, "gen.ndjson")
            db_path = os.path.join(td, "gen.db")
            _write_generic_ndjson(nd_path)

            rc = ndjson.main(
                ["--out-db", db_path, "--headline-roots", "MyLib.MainTheorem", "--quiet", nd_path]
            )
            self.assertEqual(rc, 0)
            res = ndjson.parse_ndjson_export(nd_path, verbose=False, headline_roots=["MyLib.MainTheorem"])
            st = res["stats"]
            self.assertEqual(st["decl_count"], 3)
            self.assertEqual(st["headline_roots"], ["MyLib.MainTheorem"])
            self.assertFalse(st["sorry_in_statement_closure"])
            self.assertEqual(st["reachable_from_headlines_type_only"], 2)

    def test_compute_sweep_verify_rh_is_opt_in(self):
        with tempfile.TemporaryDirectory() as td:
            atlas_path = Path(td) / "atlas.json"
            buckets = {
                b: {"modules": (2 if b == "import_shim_reexport" else 0), "lines_wc": (10 if b == "import_shim_reexport" else 0)}
                for b in compute_sweep.BUCKET_ORDER
            }
            spot_checks = {
                b: ([{"module": "A"}, {"module": "B"}] if b == "import_shim_reexport" else [])
                for b in compute_sweep.BUCKET_ORDER
            }
            payload = {
                "schema": "leanre.compute_atlas/1",
                "corpus_totals": {
                    "total_modules": 10,
                    "kernel_covered_modules": 8,
                    "zero_kernel_modules": 2,
                },
                "zero_kernel_classification": {
                    "bucket_sum_modules": 2,
                    "bucket_sum_lines_wc": 10,
                    "buckets": buckets,
                    "spot_checks_per_bucket": spot_checks,
                    "dyadic_prime_intervals_chain": {},
                },
                "computation_atlas": {"source_tactic_summaries": {"native_decide": {"total_hits": 0}}},
            }
            atlas_path.write_text(json.dumps(payload), encoding="utf-8")
            # Generic verify passes without 175,187 AssertionError
            compute_sweep.verify_atlas(atlas_path, verify_rh=False)
            # RH verify raises AssertionError on non-RH counts
            with self.assertRaises(AssertionError):
                compute_sweep.verify_atlas(atlas_path, verify_rh=True)

    def test_kernel_rs_no_default_roots_and_generic_root(self):
        bin_path = kernel.default_binary_path()
        if not os.path.exists(bin_path):
            self.skipTest("leanre-kernel release binary not built")
        with tempfile.TemporaryDirectory() as td:
            nd_path = os.path.join(td, "gen.ndjson")
            _write_generic_ndjson(nd_path)

            out_explicit = os.path.join(td, "out_explicit")
            p1 = subprocess.run(
                [bin_path, "extract", "--input", nd_path, "--out-dir", out_explicit, "--threads", "2", "--root", "MyLib.MainTheorem:MAIN"],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(p1.returncode, 0, p1.stderr)
            st1 = json.loads((Path(out_explicit) / "run_stats.json").read_text(encoding="utf-8"))
            self.assertEqual([r["name"] for r in st1["roots"]], ["MyLib.MainTheorem"])

            out_none = os.path.join(td, "out_none")
            p2 = subprocess.run(
                [bin_path, "extract", "--input", nd_path, "--out-dir", out_none, "--threads", "2", "--no-default-roots"],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(p2.returncode, 0, p2.stderr)
            st2 = json.loads((Path(out_none) / "run_stats.json").read_text(encoding="utf-8"))
            self.assertEqual(st2["roots"], [])


if __name__ == "__main__":
    unittest.main()
