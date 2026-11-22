#!/usr/bin/env python3
"""Unit & integration test suite for `leanre.trim` (`leanre trim`).

Covers:
  1. Worker cap enforcement (`<= 16`) & strict read-only (`mode=ro`) SQLite opens.
  2. Declaration parser & disjoint line-span accounting (`namespace A.B.C` / `end C`,
     `_root_.` escapes, `private`, `example`, duplicate `import Mathlib` & project imports).
  3. End-to-end synthetic corpus + `kernel.db` + `tier1.db` virtual proof stripping:
     verifies exact non-double-counted waterfall conservation across modules, lines,
     live kernel `decls`, and `value_nodes` (`unused` -> `dead_decls` -> `vn==1 aliases` ->
     `alpha clones + k1n dups` -> `dup imports`).
  4. CLI `register_cli(sub, dest="trim_func")` wiring contract (`--json`, `--out`, `--from-report`).
  5. Real-report schema, conservation, and pinned invariant checks on `outputs/decomp/trim_report.json`.
"""
from __future__ import annotations

import argparse
import io
import json
import os
import sqlite3
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import trim  # noqa: E402


def _build_synthetic_fixture(td: str) -> dict:
    """Create a mini Lean source tree + `kernel.db` + `tier1.db` exercising all 8 trim axes."""
    src = os.path.join(td, "src")
    os.makedirs(os.path.join(src, "Pkg"), exist_ok=True)

    files = {
        # 1. Live root module with 1 live theorem, 1 dead theorem, 1 example, and duplicate imports
        "Main.lean": (
            "import Mathlib\n"
            "import Mathlib\n"
            "import Pkg.RealCore\n"
            "import Pkg.RealCore\n"
            "import Pkg.AliasWrap\n"
            "\n"
            "theorem main_goal : True :=\n"
            "  Pkg.T.alias_thm\n"
            "\n"
            "theorem dead_in_main : True := by\n"
            "  trivial\n"
            "\n"
            "example : True := trivial\n"
        ),
        # 2. Live core module with 1 live real theorem + 1 inline 1-node alias + 1 k1n duplicate theorem
        "Pkg/RealCore.lean": (
            "import Mathlib\n"
            "\n"
            "namespace Pkg.Sub.Deep\n"
            "\n"
            "theorem real_thm : True := by\n"
            "  trivial\n"
            "\n"
            "end Deep\n"
            "\n"
            "theorem inline_alias : True := Pkg.Sub.Deep.real_thm\n"
            "\n"
            "theorem dup_k1n_thm : True := by\n"
            "  exact trivial\n"
            "\n"
            "end Pkg.Sub\n"
        ),
        # 3. Pure 1-node alias wrapper module (`GlobalTheory.T.*` style)
        "Pkg/AliasWrap.lean": (
            "import Mathlib\n"
            "import Pkg.RealCore\n"
            "\n"
            "theorem Pkg.T.alias_thm : True := Pkg.Sub.inline_alias\n"
        ),
        # 4. Surviving live alpha-clone pair (`CloneA.lean` and `CloneB.lean`)
        "Pkg/CloneA.lean": (
            "import Mathlib\n"
            "\n"
            "theorem Pkg.clone_a : True := by\n"
            "  trivial\n"
        ),
        "Pkg/CloneB.lean": (
            "import Mathlib\n"
            "\n"
            "theorem Pkg.clone_b : True := by\n"
            "  trivial\n"
        ),
        # 5. Completely unused theorem module (imported-but-unused)
        "Pkg/UnusedMod.lean": (
            "import Mathlib\n"
            "import Mathlib\n"
            "\n"
            "theorem Pkg.unused_thm : True := by\n"
            "  trivial\n"
        ),
        # 6. Pure import shim (0 kernel decls)
        "Pkg/ShimOnly.lean": (
            "import Mathlib\n"
            "import Pkg.RealCore\n"
        ),
        # 7. Private-only unused module (0 kernel decls)
        "Pkg/PrivUnused.lean": (
            "import Mathlib\n"
            "\n"
            "private theorem secret_unused : True := trivial\n"
        ),
        # 8. Meta-only module (0 kernel decls)
        "Pkg/MetaOnly.lean": (
            "import Lean\n"
            "\n"
            "elab \"my_tac\" : tactic => pure ()\n"
        ),
    }

    for rel, content in files.items():
        full = os.path.join(src, rel)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w", encoding="utf-8") as f:
            f.write(content)

    # Create synthetic `kernel.db`
    kdb = os.path.join(td, "kernel.db")
    ck = sqlite3.connect(kdb)
    ck.executescript(
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
        CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src, dst)) WITHOUT ROWID;
        CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
        CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
        CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id, decl_id)) WITHOUT ROWID;
        """
    )

    sh_true = "k1n:" + "a" * 32
    sh_other = "k1n:" + "b" * 32
    decls = [
        # (id, name, kind, tn, vn, fi, fo, fot, fov, live, sh, mod, meth)
        (0, "True", "inductive", 1, 2, 6, 0, 0, 0, 1, sh_other, None, "unmatched:challenge_library"),
        (1, "Pkg.Sub.Deep.real_thm", "thm", 2, 10, 2, 1, 1, 0, 1, sh_true, "Pkg.RealCore", "leanre_db:exact"),
        (2, "Pkg.Sub.inline_alias", "thm", 2, 1, 1, 2, 1, 1, 1, sh_true, "Pkg.RealCore", "leanre_db:exact"),
        (3, "Pkg.Sub.dup_k1n_thm", "thm", 2, 8, 1, 1, 1, 0, 1, sh_true, "Pkg.RealCore", "leanre_db:exact"),
        (4, "Pkg.T.alias_thm", "thm", 2, 1, 1, 2, 1, 1, 1, sh_true, "Pkg.AliasWrap", "leanre_db:exact"),
        (5, "Pkg.clone_a", "thm", 2, 6, 1, 1, 1, 0, 1, sh_other, "Pkg.CloneA", "leanre_db:exact"),
        (6, "Pkg.clone_b", "thm", 2, 6, 1, 1, 1, 0, 1, "k1n:" + "c" * 32, "Pkg.CloneB", "leanre_db:exact"),
        (7, "main_goal", "thm", 2, 15, 0, 4, 1, 3, 1, "k1n:" + "d" * 32, "Main", "leanre_db:exact"),
        (8, "Nat.lor", "def", 3, 3, 0, 0, 0, 0, 0, "k1n:" + "e" * 32, None, "unmatched:library_or_external"),
    ]
    for did, nm, knd, tn, vn, fi, fo, fot, fov, lm, sh, mod, meth in decls:
        ck.execute(
            "INSERT INTO decls VALUES (?,?,?,1,?,?,?,?,?,?,0,?,0,0,0,?,?)",
            (did, nm, knd, tn, vn, fi, fo, fot, fov, lm, sh, sh),
        )
        ck.execute(
            "INSERT INTO consts VALUES (?,?,?, ?,0,?,?,1,0)",
            (did, nm, did, "induct" if knd == "inductive" else knd, sh, sh),
        )
        ck.execute("INSERT INTO decl_module VALUES (?,?,?,NULL)", (did, mod, meth))

    # Edges: alias chain `Pkg.T.alias_thm (4) -> Pkg.Sub.inline_alias (2) -> Pkg.Sub.Deep.real_thm (1)`
    edges = [
        (2, 1, 2),
        (4, 2, 2),
        (7, 4, 2),
        (7, 3, 2),
        (7, 5, 2),
        (7, 6, 2),
        (7, 0, 1),
    ]
    ck.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
    ck.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '0', 8)")
    ck.execute("INSERT INTO dom VALUES (0, 7, NULL, 0, 8)")
    for cid in (0, 1, 2, 3, 4, 5, 6):
        ck.execute("INSERT INTO dom VALUES (0, ?, 7, 1, 1)", (cid,))
    ck.commit()
    ck.close()

    # Create synthetic `tier1.db` with `CloneA` and `CloneB` in an `alpha_body_clone` cluster
    tdb = os.path.join(td, "tier1.db")
    ct = sqlite3.connect(tdb)
    ct.executescript(
        """
        CREATE TABLE module_fingerprints(module TEXT PRIMARY KEY, is_statement_wrapper INTEGER NOT NULL);
        CREATE TABLE boilerplate_clusters(cluster_id TEXT PRIMARY KEY, kind TEXT NOT NULL);
        CREATE TABLE boilerplate_members(cluster_id TEXT NOT NULL, module TEXT NOT NULL, lines_wc INTEGER NOT NULL, PRIMARY KEY(cluster_id, module)) WITHOUT ROWID;
        """
    )
    ct.execute("INSERT INTO boilerplate_clusters VALUES ('AC001', 'alpha_body_clone')")
    ct.execute("INSERT INTO boilerplate_members VALUES ('AC001', 'Pkg.CloneA', 4)")
    ct.execute("INSERT INTO boilerplate_members VALUES ('AC001', 'Pkg.CloneB', 4)")
    ct.execute("INSERT INTO module_fingerprints VALUES ('Pkg.AliasWrap', 1)")
    ct.commit()
    ct.close()

    return {"src": src, "kernel_db": kdb, "tier1_db": tdb}


class TestTrimUnitAndSynthetic(unittest.TestCase):
    def test_worker_cap_and_readonly_connection(self):
        self.assertEqual(trim.clamp_workers(None), 16)
        self.assertEqual(trim.clamp_workers(64), 16)
        self.assertEqual(trim.clamp_workers(0), 1)
        self.assertEqual(trim.clamp_workers(4), 4)

        with tempfile.TemporaryDirectory() as td:
            dbp = os.path.join(td, "ro.db")
            c = sqlite3.connect(dbp)
            c.execute("CREATE TABLE t(x INT)")
            c.commit()
            c.close()

            ro = trim.connect_ro(dbp)
            try:
                with self.assertRaises(sqlite3.OperationalError):
                    ro.execute("INSERT INTO t VALUES (1)")
            finally:
                ro.close()

    def test_parser_multi_component_end_and_disjoint_spans(self):
        sample = (
            b"import Mathlib\n"
            b"import Mathlib\n"
            b"namespace A.B.C\n"
            b"theorem t1 : True := trivial\n"
            b"end C\n"
            b"theorem t2 : True := by\n"
            b"  trivial\n"
            b"\n"
            b"theorem _root_.Top.t3 : True := trivial\n"
            b"end A.B\n"
        )
        p = trim.parse_lean_file_for_trim(sample, "Mod", "Mod.lean")
        self.assertEqual(p["lines_wc"], 10)
        self.assertEqual(p["dup_mathlib_lines"], 1)
        fqns = [d["fqn"] for d in p["decls"]]
        self.assertEqual(fqns, ["A.B.C.t1", "A.B.t2", "Top.t3"])
        # t2 spans lines 6..7 trimmed (2 lines) and lines 6..8 block (3 lines incl blank line 8)
        self.assertEqual(p["decls"][1]["trimmed_lines"], 2)
        self.assertEqual(p["decls"][1]["block_lines"], 3)

    def test_synthetic_end_to_end_waterfall_conservation_and_cli(self):
        with tempfile.TemporaryDirectory() as td:
            fx = _build_synthetic_fixture(td)
            out_json = os.path.join(td, "trim_report.json")
            rep = trim.run_trim(
                src_dir=fx["src"],
                kernel_db_path=fx["kernel_db"],
                leanre_db_path=None,
                tier1_db_path=fx["tier1_db"],
                compute_atlas_path=None,
                out_path=out_json,
                workers=2,
            )
            self.assertEqual(rep["schema"], "leanre.trim/1")
            self.assertTrue(os.path.isfile(out_json))

            # Verify 4 unused zero-kernel modules peeled in Step 1 (1 unused, 1 shim, 1 priv, 1 meta)
            c1 = rep["c1_unused_modules"]
            self.assertEqual(c1["truly_unused_peeled"]["modules"], 4)
            self.assertEqual(c1["buckets"]["imported_but_unused_by_kernel"]["modules"], 1)
            self.assertEqual(c1["buckets"]["import_shim_reexport"]["modules"], 1)
            self.assertEqual(c1["buckets"]["unexported_private_or_inline"]["modules"], 1)
            self.assertEqual(c1["buckets"]["macro_tactic_elab_syntax_only"]["modules"], 1)

            # Verify Step 2 dead decls in Main.lean (`dead_in_main` + `example`)
            c2 = rep["c2_dead_decls_in_live_modules"]
            self.assertEqual(c2["dead_decls_in_all_live_modules"], 2)
            self.assertEqual(c2["dead_decls_by_kind"], {"example": 1, "theorem": 1})

            # Verify Step 3 2-hop alias chain (`Pkg.T.alias_thm -> Pkg.Sub.inline_alias -> Pkg.Sub.Deep.real_thm`)
            c3 = rep["c3_forwarding_aliases_vn1"]
            self.assertEqual(c3["project_thm_vn1_total"], 2)
            self.assertEqual(c3["chain_resolution"]["hop_length_histogram"], {"1": 1, "2": 1})
            self.assertEqual(c3["source_footprint_disjoint_after_step2"]["pure_alias_live_modules_removed"], 1)
            self.assertEqual(c3["source_footprint_disjoint_after_step2"]["inline_alias_spans_in_mixed_modules"], 1)

            # Verify Step 4a (`CloneB`) + Step 4b (`dup_k1n_thm`)
            c5 = rep["c5_clones_and_k1n_duplicates"]
            self.assertEqual(c5["alpha_body_clone"]["step4a_redundant_modules_removed"], 1)
            self.assertEqual(
                c5["kernel_k1n_type_duplicates"]["step4b_disjoint_after_step3_and_4a"]["redundant_user_thms"], 1
            )

            # Verify Step 5 duplicate imports ONLY counts surviving Main.lean (1 Mathlib + 1 Pkg.RealCore = 2),
            # NOT `Pkg/UnusedMod.lean`'s duplicate `import Mathlib` (already peeled in Step 1 -> zero double-counting!)
            c4 = rep["c4_duplicate_imports_and_shims"]
            self.assertEqual(c4["corpus_raw_totals"]["duplicate_mathlib_import_lines"], 2)
            self.assertEqual(c4["disjoint_residual_peeled_in_step5"]["dup_mathlib_lines_removed"], 1)
            self.assertEqual(c4["disjoint_residual_peeled_in_step5"]["dup_project_lines_removed"], 1)

            # Strict step-by-step waterfall conservation check
            steps = rep["c8_waterfall"]["steps"]
            self.assertEqual(len(steps), 5)
            for idx, st in enumerate(steps):
                for key in ("modules", "lines_wc", "kernel_live_decls", "kernel_live_value_nodes"):
                    self.assertEqual(
                        st["before"][key] - st["removed"][key],
                        st["after"][key],
                        f"conservation failed at {st['step_id']}.{key}",
                    )
                if idx > 0:
                    self.assertEqual(steps[idx - 1]["after"]["lines_wc"], st["before"]["lines_wc"])

            # Verify `register_cli(sub, dest="trim_func")` contract
            ap = argparse.ArgumentParser()
            sub = ap.add_subparsers(dest="cmd", required=True)
            trim.register_cli(sub, dest="trim_func")
            args = ap.parse_args(["trim", "--from-report", out_json])
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = args.trim_func(args)
            self.assertEqual(rc, 0)
            self.assertIn("Irreducible core estimate", buf.getvalue())


class TestRealTrimReport(unittest.TestCase):
    """Validate committed `outputs/decomp/trim_report.json` when present."""

    def test_real_trim_report_invariants(self):
        rep_path = os.path.join(_REPO_ROOT, "outputs", "decomp", "trim_report.json")
        if not os.path.isfile(rep_path):
            self.skipTest("outputs/decomp/trim_report.json not generated yet")
        with open(rep_path, "r", encoding="utf-8") as f:
            rep = json.load(f)

        self.assertEqual(rep["schema"], "leanre.trim/1")
        self.assertLessEqual(rep["pins"]["workers_used"], 16)
        b = rep["baseline"]
        self.assertEqual(b["total_modules"], 175187)
        self.assertEqual(b["total_lines_wc"], 17374215)
        self.assertEqual(b["kernel_live_records"], 1468414)
        self.assertEqual(b["live_modules_decl_module"], 146283)

        c1 = rep["c1_unused_modules"]
        self.assertEqual(c1["buckets"]["imported_but_unused_by_kernel"]["modules"], 28471)
        self.assertEqual(c1["buckets"]["unexported_private_or_inline"]["modules"], 239)
        self.assertEqual(c1["buckets"]["import_shim_reexport"]["modules"], 164)
        self.assertEqual(c1["buckets"]["macro_tactic_elab_syntax_only"]["modules"], 11)
        self.assertEqual(len(c1["meta_only_modules"]), 11)
        self.assertEqual(c1["truly_unused_peeled"]["modules"], 28885)

        c3 = rep["c3_forwarding_aliases_vn1"]
        self.assertEqual(c3["project_thm_vn1_global_theory_T"], 38194)
        self.assertGreater(c3["project_thm_vn1_other_namespaces"], 4000)

        c4 = rep["c4_duplicate_imports_and_shims"]["corpus_raw_totals"]
        self.assertEqual(c4["duplicate_mathlib_import_lines"], 19750)
        self.assertEqual(c4["duplicate_project_import_lines"], 308)
        self.assertEqual(c4["strict_import_only_shims"], 150)
        st_imp = rep["c4_duplicate_imports_and_shims"]["stage_accounting_for_all_duplicate_imports"]
        self.assertEqual(
            st_imp["dup_mathlib_peeled_in_step1_unused_files"]
            + st_imp["dup_mathlib_peeled_in_step3_pure_alias_files"]
            + st_imp["dup_mathlib_peeled_in_step4_clone_dup_files"]
            + st_imp["dup_mathlib_peeled_in_step5_surviving_core"],
            19750,
        )
        self.assertEqual(
            st_imp["dup_project_peeled_in_step1_unused_files"]
            + st_imp["dup_project_peeled_in_step3_pure_alias_files"]
            + st_imp["dup_project_peeled_in_step4_clone_dup_files"]
            + st_imp["dup_project_peeled_in_step5_surviving_core"],
            308,
        )
        self.assertEqual(
            len(rep["c7_macro_proof_term_blowup"]["copy_cases"]["lam_and_sigSpan_copy_callers_and_defs"]),
            5,
        )

        c5 = rep["c5_clones_and_k1n_duplicates"]
        self.assertEqual(c5["alpha_body_clone"]["raw_clusters"], 1192)
        self.assertEqual(c5["alpha_body_clone"]["raw_redundant_modules"], 3595)

        c6 = rep["c6_unread_phantom_struct_fields"]
        self.assertEqual(c6["LiteratureCMHypothesis"]["builder_subtree"]["dom_subtree_decls"], 907)
        self.assertEqual(c6["OpenLiteratureStatements"]["independent_of_O_theorems"], 182)
        self.assertEqual(c6["OpenLiteratureStatements"]["module_theorems_total"], 195)
        self.assertEqual(c6["LitLocAlt"]["unread_fields_count"], 7)
        self.assertEqual(c6["LiteratureAutomorphyHypothesis"]["unread_fields_count"], 5)

        steps = rep["c8_waterfall"]["steps"]
        self.assertEqual(len(steps), 5)
        self.assertEqual(steps[0]["before"]["lines_wc"], 17374215)
        for idx, st in enumerate(steps):
            for k in ("modules", "lines_wc", "kernel_live_decls", "kernel_live_value_nodes"):
                self.assertEqual(st["before"][k] - st["removed"][k], st["after"][k])
            if idx > 0:
                self.assertEqual(steps[idx - 1]["after"]["lines_wc"], st["before"]["lines_wc"])
        self.assertEqual(
            steps[-1]["after"]["lines_wc"],
            rep["c8_waterfall"]["irreducible_core_estimate"]["lines_wc"],
        )


if __name__ == "__main__":
    unittest.main()
