#!/usr/bin/env python3
"""Unit & integration test suite for `leanre.portability` (`leanre portability`).

Covers:
  1. Exact transitive `value`+`type` cone sizes, `spec_cone`, `dom` subtree, module count,
     `thm/def/inductive/axiom/opaque` split, `vn=1` forwarding aliases, and `value_nodes`.
  2. Direct external boundary inventory (including `_private.Mathlib.*`, `Lean.*`, and
     excluding transitive-only external declarations not directly called by project decls).
  3. Contamination & coupling tiers (`standalone-ready`, `scoped`, `coupled`):
     - clean standalone theorem (`standalone-ready`)
     - target-signature mega-record (`>= 40` fields) -> `scoped`
     - sparse ambient mega-record (`2/42` fields projected in cone) -> `coupled`
     - `decide_kernel` taint, non-standard axiom, `sorryAx`, `reduceBool`, project `opaque` -> `coupled`
  4. Pure-kernel (`--no-src`) and unenriched `kernel.db` (no `decl_module`/`taint_sources`/`dom_trees`)
     portability modes.
  5. Multi-target shared overlap matrices (`project`, `external`, `full`, Jaccard) & union conservation.
  6. `add_portability_parser(sub)` / `cmd_portability(args)` CLI wiring, read-only `chmod 0444/0555`
     safety, `--out` symlink refusal, and zero absolute host/home path leakage.
"""
from __future__ import annotations

import argparse
import io
import json
import os
import sqlite3
import stat
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import portability  # noqa: E402


def _build_synthetic_portability_fixture(td: str) -> dict:
    """Create a synthetic `kernel.db` + `.lean` tree exercising all portability paths."""
    src = os.path.join(td, "src")
    os.makedirs(os.path.join(src, "Geom"), exist_ok=True)
    os.makedirs(os.path.join(src, "Hodge"), exist_ok=True)
    os.makedirs(os.path.join(src, "Coupled"), exist_ok=True)

    pack_fields = "\n".join(f"  ch{i} : Nat = Nat" for i in range(1, 43))
    mega_fields = "\n".join(f"   slot{i} : Nat" for i in range(1, 45))

    files = {
        "Geom/Clean.lean": (
            "namespace Geom\n"
            "def IsCleanObj (n : Nat) : Prop := n = n\n"
            "theorem cleanGem (n : Nat) : IsCleanObj n := rfl\n"
            "end Geom\n"
        ),
        "Hodge/Scoped.lean": (
            "namespace Hodge\n"
            "structure Chapters42 : Prop where\n"
            f"{pack_fields}\n"
            "end Hodge\n"
        ),
        "Coupled/Ambient.lean": (
            "namespace Coupled\n"
            "structure MegaContext44 where\n"
            f"{mega_fields}\n"
            "end Coupled\n"
        ),
    }
    for rel, txt in files.items():
        full = os.path.join(src, rel)
        with open(full, "w", encoding="utf-8") as f:
            f.write(txt)

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
        CREATE TABLE edges(
            src INTEGER NOT NULL,
            dst INTEGER NOT NULL,
            kind INTEGER NOT NULL,
            PRIMARY KEY(src, dst)
        ) WITHOUT ROWID;
        CREATE TABLE decl_module(
            decl_id INTEGER PRIMARY KEY,
            module TEXT,
            method TEXT NOT NULL,
            src_decl_id INTEGER
        );
        CREATE TABLE dom_trees(
            id INTEGER PRIMARY KEY,
            label TEXT NOT NULL,
            view TEXT NOT NULL,
            root_ids TEXT NOT NULL,
            n_nodes INTEGER NOT NULL
        );
        CREATE TABLE dom(
            tree_id INTEGER NOT NULL,
            decl_id INTEGER NOT NULL,
            idom INTEGER,
            depth INTEGER NOT NULL,
            subtree_size INTEGER NOT NULL,
            PRIMARY KEY(tree_id, decl_id)
        ) WITHOUT ROWID;
        CREATE TABLE taint_sources(
            id INTEGER PRIMARY KEY,
            class TEXT NOT NULL,
            decl_id INTEGER NOT NULL,
            origin TEXT NOT NULL,
            module TEXT,
            line_no INTEGER,
            detail TEXT NOT NULL
        );
        CREATE UNIQUE INDEX decls_name ON decls(name);
        CREATE INDEX consts_decl ON consts(decl_id);
        """
    )

    def add_decl(
        did: int,
        name: str,
        kind: str,
        tn: int,
        vn: int,
        fo: int,
        fot: int,
        fov: int,
        flags: int,
        mod: str | None,
        meth: str,
        one_ctor: bool = False,
    ) -> None:
        ck.execute(
            "INSERT INTO decls VALUES (?,?,?,1,?,?,1,?,?,?,?,1,0,0,0,'k1n:00','k1a:00')",
            (did, name, kind, tn, vn, fo, fot, fov, flags),
        )
        ck.execute("INSERT INTO decl_module VALUES (?,?,?,NULL)", (did, mod, meth))
        if one_ctor:
            ck.execute("INSERT INTO consts VALUES (?,?,?,'induct',0,'','',1,0)", (did * 10, name, did))
            ck.execute("INSERT INTO consts VALUES (?,?,?,'ctor',1,'','',1,0)", (did * 10 + 1, name + ".mk", did))
        else:
            ck.execute("INSERT INTO consts VALUES (?,?,?, ?,0,'','',1,0)", (did * 10, name, did, kind))

    # Standard axioms & external library nodes
    add_decl(1, "propext", "axiom", 1, 0, 0, 0, 0, 0, None, "unmatched:challenge_library")
    add_decl(2, "Quot.sound", "axiom", 1, 0, 0, 0, 0, 0, None, "unmatched:challenge_library")
    add_decl(3, "Classical.choice", "axiom", 1, 0, 0, 0, 0, 0, None, "unmatched:challenge_library")
    add_decl(4, "AlgebraicGeometry.Scheme", "def", 10, 20, 1, 1, 1, 0, None, "unmatched:library_or_external")
    add_decl(5, "CategoryTheory.Functor", "def", 8, 12, 0, 0, 0, 0, None, "unmatched:library_or_external")
    add_decl(6, "_private.Mathlib.RingTheory.Ideal.0.helper", "thm", 4, 9, 0, 0, 0, 0, None, "unmatched:external_private")
    add_decl(7, "Lean.Omega.IntList", "def", 5, 8, 0, 0, 0, 0, None, "unmatched:challenge_library")
    # External node ONLY reached transitively from AlgebraicGeometry.Scheme (must NOT appear in direct boundary!)
    add_decl(8, "Mathlib.GroupTheory.deepHelper", "thm", 3, 6, 0, 0, 0, 0, None, "unmatched:library_or_external")

    # Target 1 (`Geom.cleanGem`): standalone-ready
    add_decl(10, "Geom.sharedBase", "thm", 4, 15, 2, 1, 1, 0, "Geom.Clean", "leanre_db:exact")
    add_decl(11, "Geom.IsCleanObj", "def", 3, 8, 1, 1, 1, 0, "Geom.Clean", "leanre_db:exact")
    add_decl(12, "Geom.aliasWrap", "thm", 2, 1, 1, 0, 1, 0, "Geom.Clean", "leanre_db:exact")  # vn=1 alias
    add_decl(13, "Geom.cleanGem", "thm", 5, 30, 5, 2, 4, 1, "Geom.Clean", "leanre_db:exact")  # benign flags=1

    # Target 2 (`Hodge.scopedGem`): scoped (returns 42-field `Hodge.Chapters42` in target signature)
    add_decl(20, "Hodge.Chapters42", "inductive", 80, 90, 1, 1, 1, 0, "Hodge.Scoped", "leanre_db:exact", one_ctor=True)
    for idx_f in range(1, 11):
        # 10 exported K_PROJ projections in DB, none inside scopedGem's own value cone
        add_decl(
            200 + idx_f,
            f"Hodge.Chapters42.ch{idx_f}",
            "thm",
            3,
            4,
            1,
            1,
            1,
            0,
            "Hodge.Scoped",
            "leanre_db:exact",
        )
    add_decl(21, "Hodge.scopedGem", "thm", 6, 50, 3, 1, 2, 0, "Hodge.Scoped", "leanre_db:exact")

    # Target 3 (`Coupled.ambientCoupled`): coupled (uses sparse 44-field `MegaContext44`: 2/44 projected in cone + decide_kernel taint)
    add_decl(30, "Coupled.MegaContext44", "inductive", 90, 100, 0, 0, 0, 0, "Coupled.Ambient", "leanre_db:exact", one_ctor=True)
    for idx_f in range(1, 43):
        add_decl(
            300 + idx_f,
            f"Coupled.MegaContext44.slot{idx_f}",
            "def",
            3,
            4,
            1,
            1,
            1,
            0,
            "Coupled.Ambient",
            "leanre_db:exact",
        )
    # Also add a namespace helper sharing prefix `MegaContext44.helperLemma` (fo != fot -> must NOT count as field in --no-src!)
    add_decl(390, "Coupled.MegaContext44.helperLemma", "thm", 10, 40, 3, 1, 3, 0, "Coupled.Ambient", "leanre_db:exact")
    add_decl(31, "Coupled.ambientStep", "thm", 6, 25, 3, 1, 2, 3, "Coupled.Ambient", "leanre_db:exact")
    add_decl(32, "Coupled.ambientCoupled", "thm", 4, 12, 2, 0, 2, 0, "Coupled.Ambient", "leanre_db:exact")

    # Target 4 (`Coupled.badAxiomThm`): coupled via custom axiom + sorryAx + reduceBool + project opaque
    add_decl(40, "CustomOracleAx", "axiom", 2, 0, 0, 0, 0, 0, "Coupled.Ambient", "leanre_db:exact")
    add_decl(41, "sorryAx", "axiom", 2, 0, 0, 0, 0, 16, None, "unmatched:challenge_library")
    add_decl(42, "Coupled.secretOpaque", "opaque", 3, 0, 0, 0, 0, 0, "Coupled.Ambient", "leanre_db:exact")
    add_decl(43, "Coupled.badAxiomThm", "thm", 4, 10, 3, 1, 2, 4 | 32, "Coupled.Ambient", "leanre_db:exact")

    edges = [
        # External transitive chain: Scheme -> TransitiveOnlyExt.deepHelper
        (4, 8, 2),
        # Shared project base: sharedBase -> CategoryTheory.Functor, propext, Classical.choice
        (10, 5, 2),
        (10, 1, 2),
        (10, 3, 2),
        # IsCleanObj -> AlgebraicGeometry.Scheme (in definition body -> part of spec_cone!)
        (11, 4, 3),
        # aliasWrap -> sharedBase
        (12, 10, 2),
        # cleanGem: type -> IsCleanObj; value -> aliasWrap, _private.Mathlib.RingTheory, Lean.Omega, Quot.sound
        (13, 11, 1),
        (13, 12, 2),
        (13, 6, 2),
        (13, 7, 2),
        (13, 2, 2),
        # Chapters42 projections -> Chapters42 (kind=3)
        *[(200 + i, 20, 3) for i in range(1, 11)],
        # scopedGem: type -> Chapters42 (target_signature!), value -> sharedBase + AlgebraicGeometry.Scheme
        (21, 20, 3),
        (21, 10, 2),
        (21, 4, 2),
        # MegaContext44 projections -> MegaContext44 (kind=3), helperLemma -> MegaContext44 + Scheme + Functor
        *[(300 + i, 30, 3) for i in range(1, 43)],
        (390, 30, 3),
        (390, 4, 2),
        (390, 5, 2),
        # ambientStep projects ONLY 2 fields (slot1, slot2) of MegaContext44; ambientCoupled calls ambientStep (NOT MegaContext44 in its own type!)
        (31, 30, 1),
        (31, 301, 2),
        (31, 302, 2),
        (32, 31, 2),
        (32, 10, 2),
        # badAxiomThm -> CustomOracleAx, sorryAx, secretOpaque
        (43, 40, 2),
        (43, 41, 2),
        (43, 42, 1),
    ]
    ck.executemany("INSERT INTO edges VALUES (?,?,?)", edges)

    ck.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '13,21,32', 20)")
    ck.executemany(
        "INSERT INTO dom VALUES (?,?,?,?,?)",
        [
            (0, 13, None, 0, 12),
            (0, 21, None, 0, 8),
            (0, 32, None, 0, 6),
        ],
    )
    ck.execute(
        "INSERT INTO taint_sources VALUES (1, 'decide_kernel', 31, 'source-hit:leanre.db', 'Coupled.Ambient', 10, 'decide +kernel')"
    )
    ck.execute(
        "INSERT INTO taint_sources VALUES (2, 'decide_kernel_pattern', 13, 'kernel-pattern:of_decide_eq_true_refl', 'Geom.Clean', 3, 'refl')"
    )
    ck.commit()
    ck.close()
    return {"src": src, "kernel_db": kdb}


class TestPortabilityAnalyzer(unittest.TestCase):
    def test_cones_boundaries_tiers_and_overlap(self):
        with tempfile.TemporaryDirectory() as td:
            fx = _build_synthetic_portability_fixture(td)
            rep = portability.analyze_portability(
                decls=["cleanGem", "Hodge.scopedGem", "Coupled.ambientCoupled", "Coupled.badAxiomThm"],
                kernel_db_path=fx["kernel_db"],
                src_root=fx["src"],
            )
            self.assertEqual(rep["schema"], "leanre.portability/1")
            self.assertFalse(os.path.isabs(rep["pins"]["kernel_db"]))
            self.assertFalse(os.path.isabs(rep["pins"]["src_root"]))

            by_name = {t["name"]: t for t in rep["targets"]}

            # 1. cleanGem: standalone-ready, suffix-resolved, exact cones & boundary
            clean = by_name["Geom.cleanGem"]
            self.assertEqual(clean["resolved_from"], "cleanGem")
            self.assertEqual(clean["contamination"]["tier"], "standalone-ready")
            # Project decls: cleanGem(13), IsCleanObj(11), aliasWrap(12), sharedBase(10) = 4
            # External decls: propext(1), Quot.sound(2), Classical.choice(3), Scheme(4), Functor(5),
            #   _private.Mathlib.RingTheory(6), Lean.Omega(7), TransitiveOnlyExt.deepHelper(8) = 8
            self.assertEqual(clean["cone"]["project_decls"], 4)
            self.assertEqual(clean["cone"]["external_decls"], 8)
            self.assertEqual(clean["cone"]["total_decls"], 12)
            self.assertEqual(clean["cone"]["dom_subtree_size"], 12)
            self.assertEqual(clean["cone"]["module_count"], 1)
            self.assertEqual(clean["cone"]["vn1_forwarding_aliases"], 1)
            # spec_cone of cleanGem unfolds IsCleanObj (1 proj other than cleanGem) -> Scheme -> deepHelper
            self.assertEqual(clean["cone"]["spec_cone_project_decls"], 1)
            # Direct boundary excludes TransitiveOnlyExt (8), includes AlgebraicGeometry, CategoryTheory, Mathlib.RingTheory, Lean.Omega
            b_pfxs = {p["prefix"]: p["distinct_decls"] for p in clean["boundary"]["top_external_prefixes"]}
            self.assertIn("AlgebraicGeometry", b_pfxs)
            self.assertIn("CategoryTheory", b_pfxs)
            self.assertIn("Mathlib.RingTheory", b_pfxs)
            self.assertIn("Lean.Omega", b_pfxs)
            self.assertNotIn("Mathlib.GroupTheory", b_pfxs)

            # 2. scopedGem: scoped due to 42-field target_signature Chapters42
            scoped = by_name["Hodge.scopedGem"]
            self.assertEqual(scoped["contamination"]["tier"], "scoped")
            self.assertEqual(len(scoped["contamination"]["mega_records"]), 1)
            m_ch = scoped["contamination"]["mega_records"][0]
            self.assertEqual(m_ch["name"], "Hodge.Chapters42")
            self.assertEqual(m_ch["total_fields"], 42)
            self.assertEqual(m_ch["projected_in_cone"], 0)
            self.assertEqual(m_ch["role"], "target_signature")

            # 3. ambientCoupled: coupled due to sparse ambient MegaContext44 (2/44) + decide_kernel taint
            amb = by_name["Coupled.ambientCoupled"]
            self.assertEqual(amb["contamination"]["tier"], "coupled")
            self.assertEqual(amb["contamination"]["taint_sources"]["project_by_class"].get("decide_kernel"), 1)
            m_amb = amb["contamination"]["mega_records"][0]
            self.assertEqual(m_amb["name"], "Coupled.MegaContext44")
            self.assertEqual(m_amb["total_fields"], 44)
            self.assertEqual(m_amb["projected_in_cone"], 2)
            self.assertEqual(m_amb["role"], "internal_or_context")

            # 4. badAxiomThm: coupled via non-standard axiom, sorryAx, reduceBool/trustCompiler, project opaque
            bad = by_name["Coupled.badAxiomThm"]
            self.assertEqual(bad["contamination"]["tier"], "coupled")
            self.assertEqual(bad["contamination"]["non_standard_axioms"], ["CustomOracleAx", "sorryAx"])
            self.assertTrue(bad["contamination"]["has_sorry"])
            self.assertEqual(bad["contamination"]["opaques"]["project_names"], ["Coupled.secretOpaque"])
            self.assertEqual(bad["contamination"]["kernel_flags"]["project"]["reduce_bool"], 1)
            self.assertEqual(bad["contamination"]["kernel_flags"]["project"]["trust_compiler"], 1)

            # 5. Shared overlap matrix: cleanGem, scopedGem, ambientCoupled all share `Geom.sharedBase` (1 project decl)
            pmat = rep["overlap"]["project_decls_matrix"]
            self.assertEqual(pmat[0][1], 1)
            self.assertEqual(pmat[0][2], 1)
            self.assertEqual(pmat[0][3], 0)

    def test_kernel_only_and_unenriched_db_modes(self):
        with tempfile.TemporaryDirectory() as td:
            fx = _build_synthetic_portability_fixture(td)
            # --no-src mode detects MegaContext44's 42 exported K_PROJ projections while excluding helperLemma!
            rep_nosrc = portability.analyze_portability(
                decls=["Coupled.ambientCoupled"],
                kernel_db_path=fx["kernel_db"],
                no_src=True,
            )
            self.assertEqual(rep_nosrc["pins"]["source_mode"], "kernel_only")
            t_amb = rep_nosrc["targets"][0]
            self.assertEqual(t_amb["contamination"]["tier"], "coupled")
            m0 = t_amb["contamination"]["mega_records"][0]
            self.assertEqual(m0["total_fields"], 42)
            self.assertEqual(m0["projected_in_cone"], 2)

            # Unenriched bare `kernel.db` (drop decl_module, dom_trees, dom, taint_sources)
            bare_db = os.path.join(td, "bare_kernel.db")
            with open(fx["kernel_db"], "rb") as sf, open(bare_db, "wb") as df:
                df.write(sf.read())
            c_bare = sqlite3.connect(bare_db)
            c_bare.executescript("DROP TABLE decl_module; DROP TABLE dom_trees; DROP TABLE dom; DROP TABLE taint_sources;")
            c_bare.commit()
            c_bare.close()

            rep_bare = portability.analyze_portability(
                decls=["Geom.cleanGem"],
                kernel_db_path=bare_db,
                no_src=True,
            )
            self.assertEqual(rep_bare["pins"]["classification_mode"], "namespace_heuristic")
            self.assertIsNone(rep_bare["targets"][0]["cone"]["dom_subtree_size"])
            self.assertEqual(rep_bare["targets"][0]["cone"]["project_decls"], 4)
            self.assertEqual(rep_bare["targets"][0]["contamination"]["tier"], "standalone-ready")

    def test_cli_parser_readonly_and_symlink_guardrails(self):
        with tempfile.TemporaryDirectory() as td:
            fx = _build_synthetic_portability_fixture(td)

            # Verify chmod 0444 DB inside chmod 0555 directory
            ro_dir = os.path.join(td, "ro_dir")
            os.makedirs(ro_dir, exist_ok=True)
            ro_db = os.path.join(ro_dir, "kernel.db")
            with open(fx["kernel_db"], "rb") as sf, open(ro_db, "wb") as df:
                df.write(sf.read())
            os.chmod(ro_db, stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)
            os.chmod(ro_dir, stat.S_IRUSR | stat.S_IXUSR)
            try:
                ap = argparse.ArgumentParser(prog="leanre")
                sub = ap.add_subparsers(dest="cmd", required=True)
                portability.add_portability_parser(sub)

                out_json = os.path.join(td, "out.json")
                buf = io.StringIO()
                with redirect_stdout(buf):
                    args = ap.parse_args([
                        "portability",
                        "Geom.cleanGem",
                        "Hodge.scopedGem",
                        "--kernel-db", ro_db,
                        "--src-root", fx["src"],
                        "--json",
                        "--compact",
                        "--out", out_json,
                    ])
                    rc = args.portability_func(args)
                self.assertEqual(rc, 0)
                data = json.loads(buf.getvalue())
                self.assertEqual(len(data["targets"]), 2)
                self.assertTrue(os.path.isfile(out_json))
            finally:
                os.chmod(ro_dir, stat.S_IRWXU)
                os.chmod(ro_db, stat.S_IRUSR | stat.S_IWUSR)

            # Refuse writing through symlink on --out
            real_target = os.path.join(td, "keep.txt")
            sym_path = os.path.join(td, "sym.json")
            with open(real_target, "w", encoding="utf-8") as f:
                f.write("SAFE")
            os.symlink(real_target, sym_path)
            err_buf = io.StringIO()
            with redirect_stderr(err_buf):
                rc_sym = portability.main([
                    "Geom.cleanGem",
                    "--kernel-db", fx["kernel_db"],
                    "--no-src",
                    "--out", sym_path,
                ])
            self.assertEqual(rc_sym, 1)
            with open(real_target, "r", encoding="utf-8") as f:
                self.assertEqual(f.read(), "SAFE")


class TestRealKernelPortabilitySmoke(unittest.TestCase):
    """Verify exact cone & disjointness invariants against real `outputs/kernel/kernel.db` when present."""

    def test_real_gems_disjoint_cones(self):
        kdb = os.path.join(_REPO_ROOT, "outputs", "kernel", "kernel.db")
        if not os.path.isfile(kdb):
            self.skipTest("real outputs/kernel/kernel.db not present")
        rep = portability.analyze_portability(
            decls=[
                "FunctorialResolution.EmbeddedResolution.strongResolutionOfSingularitiesCharZero",
                "GroundTheory.Arith.SchemeCoh.finiteH_of_isProper",
            ],
            kernel_db_path=kdb,
            src_root=os.path.join(_REPO_ROOT, "data", "rh_mirror", "src"),
        )
        t0, t1 = rep["targets"]
        self.assertEqual(t0["cone"]["project_decls"], 10113)
        self.assertEqual(t0["cone"]["total_decls"], 67704)
        self.assertEqual(t0["contamination"]["tier"], "standalone-ready")
        self.assertEqual(t1["cone"]["project_decls"], 2302)
        self.assertEqual(t1["cone"]["total_decls"], 56244)
        self.assertEqual(t1["contamination"]["tier"], "standalone-ready")
        # Hironaka resolution and Grothendieck proper finiteness share 0 project declarations
        self.assertEqual(rep["overlap"]["project_decls_matrix"][0][1], 0)


if __name__ == "__main__":
    unittest.main()
