#!/usr/bin/env python3
"""Unit & integration test suite for `leanre.kdiff` (`leanre kdiff`).

Covers:
  1. Strict `mode=ro` + `PRAGMA query_only=1` SQLite handling and never joining on numeric `decl_id`.
  2. All alignment tiers: `unchanged`, `proof_changed`, `type_changed`, 1:1 `renamed_k1n`,
     `N:M` `ambiguous_k1n`, 1:1 `alpha_k1a`, `N:M` `ambiguous_k1a`, `added`, `removed`,
     plus exact partition conservation.
  3. Security/TCB regressions (`F_SORRY`, `F_REDUCE_BOOL`, `F_REDUCE_NAT`, `F_TRUST_COMPILER`,
     custom `axiom`, newly live `F_OF_DECIDE` vs dead `F_OF_DECIDE`) and `--fail-on-regression` exit 2.
  4. Root cone swings (`roots` + `dom` `tree_id=0` `subtree_size` delta) and top `dom`/`value_nodes`/`type_nodes` movers.
  5. Optional read-only `--annot-dir` reanchor impact preview (`exact`, `moved_renamed`, `needs_review`, `orphaned`).
  6. `--format (text|markdown|json)`, `--out` symlink refusal, `--top`, `--filter`, `add_kdiff_parser`/`cmd_kdiff`.
  7. Optional live self-diff check against `outputs/kernel/kernel.db` (< 30s).
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
from contextlib import redirect_stdout
from typing import Any, Dict, List, Optional, Sequence, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import annot  # noqa: E402
import kdiff  # noqa: E402


def _create_kernel_db(
    path: str,
    decls: Sequence[Dict[str, Any]],
    roots: Sequence[Tuple[int, str, str, str]] = (),
    dom0: Optional[Dict[str, int]] = None,
) -> None:
    """Create a synthetic `kernel.db` with arbitrary caller-supplied `id`s (to test ID independence)."""
    if os.path.exists(path):
        os.unlink(path)
    conn = sqlite3.connect(path)
    conn.executescript(
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
        CREATE TABLE roots(
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            decl_id INTEGER NOT NULL,
            grp TEXT NOT NULL
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
        CREATE UNIQUE INDEX decls_name ON decls(name);
        CREATE UNIQUE INDEX consts_name ON consts(name);
        CREATE INDEX consts_sighash ON consts(sighash);
        CREATE INDEX consts_sighash_anon ON consts(sighash_anon);
        """
    )
    name_to_id: Dict[str, int] = {}
    for cid, d in enumerate(decls):
        did = int(d["id"])
        name = d["name"]
        name_to_id[name] = did
        sh = d.get("k1n")
        sha = d.get("k1a")
        conn.execute(
            "INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (
                did,
                name,
                d.get("kind", "thm"),
                1,
                d.get("tn", 10),
                d.get("vn", 20),
                d.get("fan_in", 1),
                d.get("fan_out", 1),
                1,
                1,
                d.get("flags", 0),
                d.get("live_mask", 1),
                d.get("stmt_mask", 1),
                0,
                d.get("attrs", 0),
                sh,
                sha,
            ),
        )
        conn.execute(
            "INSERT INTO consts VALUES (?,?,?,?,?,?,?,?,?)",
            (cid, name, did, d.get("kind", "thm"), 0, sh, sha, d.get("tn", 10), 0),
        )

    for rid, rname, decl_name, grp in roots:
        conn.execute(
            "INSERT INTO roots VALUES (?,?,?,?)",
            (rid, rname, name_to_id[decl_name], grp),
        )

    if dom0 is not None:
        conn.execute(
            "INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '0', ?)",
            (len(dom0),),
        )
        for dname, sz in dom0.items():
            conn.execute(
                "INSERT INTO dom VALUES (0, ?, NULL, 0, ?)",
                (name_to_id[dname], sz),
            )
    conn.commit()
    conn.close()


def _h(tag: str, prefix: str = "k1n") -> str:
    import hashlib
    return f"{prefix}:{hashlib.sha256(tag.encode()).hexdigest()[:32]}"


class TestKdiffCore(unittest.TestCase):
    def test_all_alignment_tiers_and_id_independence(self) -> None:
        """Verify every alignment tier, N:M ambiguity, partition conservation, and numeric decl_id independence."""
        with tempfile.TemporaryDirectory() as td:
            a_path = os.path.join(td, "a.db")
            b_path = os.path.join(td, "b.db")

            # Deliberately scramble numeric `id`s between A and B!
            decls_a = [
                {"id": 100, "name": "Pkg.root", "kind": "thm", "tn": 10, "vn": 20, "k1n": _h("root"), "k1a": _h("root", "k1a")},
                {"id": 101, "name": "Pkg.unchanged", "kind": "thm", "tn": 15, "vn": 30, "k1n": _h("unch"), "k1a": _h("unch", "k1a")},
                {"id": 102, "name": "Pkg.proof_mod", "kind": "thm", "tn": 12, "vn": 40, "k1n": _h("pmod"), "k1a": _h("pmod", "k1a")},
                {"id": 103, "name": "Pkg.kind_mod", "kind": "def", "tn": 12, "vn": 40, "k1n": _h("kmod"), "k1a": _h("kmod", "k1a")},
                {"id": 104, "name": "Pkg.type_mod", "kind": "thm", "tn": 14, "vn": 25, "k1n": _h("tmod_a"), "k1a": _h("tmod_a", "k1a")},
                {"id": 105, "name": "Pkg.old_name", "kind": "thm", "tn": 18, "vn": 50, "k1n": _h("ren1"), "k1a": _h("ren1", "k1a")},
                {"id": 106, "name": "Pkg.alpha_old", "kind": "thm", "tn": 22, "vn": 60, "k1n": _h("alpha_n_a"), "k1a": _h("alpha_shared", "k1a")},
                {"id": 107, "name": "Pkg.twin_a1", "kind": "thm", "tn": 8, "vn": 10, "k1n": _h("twin_k1n"), "k1a": _h("twin_k1a", "k1a")},
                {"id": 108, "name": "Pkg.twin_a2", "kind": "thm", "tn": 8, "vn": 10, "k1n": _h("twin_k1n"), "k1a": _h("twin_k1a", "k1a")},
                {"id": 109, "name": "Pkg.alpha_twin_a1", "kind": "thm", "tn": 9, "vn": 11, "k1n": _h("at_n1"), "k1a": _h("at_shared", "k1a")},
                {"id": 110, "name": "Pkg.alpha_twin_a2", "kind": "thm", "tn": 9, "vn": 11, "k1n": _h("at_n2"), "k1a": _h("at_shared", "k1a")},
                {"id": 111, "name": "Pkg.deleted", "kind": "thm", "tn": 5, "vn": 7, "k1n": _h("del"), "k1a": _h("del", "k1a")},
            ]
            # Notice IDs in B reuse 100..111 for COMPLETELY DIFFERENT declarations,
            # and root bit is 2 (live_mask=4, stmt_mask=4) instead of bit 0!
            decls_b = [
                {"id": 101, "name": "Pkg.root", "kind": "thm", "tn": 10, "vn": 20, "k1n": _h("root"), "k1a": _h("root", "k1a"), "live_mask": 4, "stmt_mask": 4},
                {"id": 111, "name": "Pkg.unchanged", "kind": "thm", "tn": 15, "vn": 30, "k1n": _h("unch"), "k1a": _h("unch", "k1a"), "live_mask": 4, "stmt_mask": 4},
                {"id": 110, "name": "Pkg.proof_mod", "kind": "thm", "tn": 12, "vn": 95, "k1n": _h("pmod"), "k1a": _h("pmod", "k1a"), "live_mask": 4, "stmt_mask": 4},
                {"id": 109, "name": "Pkg.kind_mod", "kind": "thm", "tn": 12, "vn": 40, "k1n": _h("kmod"), "k1a": _h("kmod", "k1a"), "live_mask": 4, "stmt_mask": 4},
                {"id": 108, "name": "Pkg.type_mod", "kind": "thm", "tn": 24, "vn": 25, "k1n": _h("tmod_b"), "k1a": _h("tmod_b", "k1a"), "live_mask": 4, "stmt_mask": 4},
                {"id": 107, "name": "Pkg.new_name", "kind": "thm", "tn": 18, "vn": 120, "k1n": _h("ren1"), "k1a": _h("ren1", "k1a"), "live_mask": 4, "stmt_mask": 4},
                {"id": 106, "name": "Pkg.alpha_new", "kind": "thm", "tn": 22, "vn": 60, "k1n": _h("alpha_n_b"), "k1a": _h("alpha_shared", "k1a"), "live_mask": 4, "stmt_mask": 4},
                {"id": 105, "name": "Pkg.twin_b1", "kind": "thm", "tn": 8, "vn": 10, "k1n": _h("twin_k1n"), "k1a": _h("twin_k1a", "k1a"), "live_mask": 4, "stmt_mask": 4},
                {"id": 104, "name": "Pkg.twin_b2", "kind": "thm", "tn": 8, "vn": 10, "k1n": _h("twin_k1n"), "k1a": _h("twin_k1a", "k1a"), "live_mask": 4, "stmt_mask": 4},
                {"id": 103, "name": "Pkg.alpha_twin_b1", "kind": "thm", "tn": 9, "vn": 11, "k1n": _h("at_n3"), "k1a": _h("at_shared", "k1a"), "live_mask": 4, "stmt_mask": 4},
                {"id": 102, "name": "Pkg.added_1", "kind": "thm", "tn": 33, "vn": 77, "k1n": _h("add1"), "k1a": _h("add1", "k1a"), "live_mask": 4, "stmt_mask": 4},
            ]

            dom_a = {"Pkg.root": 500, "Pkg.unchanged": 100, "Pkg.proof_mod": 10}
            dom_b = {"Pkg.root": 650, "Pkg.unchanged": 100, "Pkg.proof_mod": 45}

            _create_kernel_db(a_path, decls_a, roots=[(0, "Pkg.root", "Pkg.root", "MAIN")], dom0=dom_a)
            _create_kernel_db(b_path, decls_b, roots=[(2, "Pkg.root", "Pkg.root", "MAIN")], dom0=dom_b)

            # Test strict read-only on chmod 0444 DB files
            os.chmod(a_path, 0o444)
            os.chmod(b_path, 0o444)
            try:
                rep = kdiff.run_kdiff(a_path, b_path, top=10)
            finally:
                os.chmod(a_path, 0o644)
                os.chmod(b_path, 0o644)

            s = rep["summary"]
            self.assertEqual(s["decls_a"], 12)
            self.assertEqual(s["decls_b"], 11)
            self.assertEqual(s["unchanged"], 2)  # Pkg.root, Pkg.unchanged
            self.assertEqual(s["proof_changed"], 2)  # Pkg.proof_mod (vn), Pkg.kind_mod (kind)
            self.assertEqual(s["type_changed"], 1)  # Pkg.type_mod
            self.assertEqual(s["renamed_k1n"], 1)  # Pkg.old_name -> Pkg.new_name
            self.assertEqual(s["alpha_k1a"], 1)  # Pkg.alpha_old -> Pkg.alpha_new
            self.assertEqual(s["ambiguous_k1n_groups"], 1)  # 2:2 twin_k1n
            self.assertEqual(s["ambiguous_k1n_a_decls"], 2)
            self.assertEqual(s["ambiguous_k1n_b_decls"], 2)
            self.assertEqual(s["ambiguous_k1a_groups"], 1)  # 2:1 at_shared
            self.assertEqual(s["ambiguous_k1a_a_decls"], 2)
            self.assertEqual(s["ambiguous_k1a_b_decls"], 1)
            self.assertEqual(s["added"], 1)  # Pkg.added_1
            self.assertEqual(s["removed"], 1)  # Pkg.deleted
            self.assertFalse(s["has_regression"])

            # Partition conservation check
            self.assertEqual(
                s["decls_a"],
                s["unchanged"]
                + s["proof_changed"]
                + s["type_changed"]
                + s["renamed_k1n"]
                + s["alpha_k1a"]
                + s["ambiguous_k1n_a_decls"]
                + s["ambiguous_k1a_a_decls"]
                + s["removed"],
            )
            self.assertEqual(
                s["decls_b"],
                s["unchanged"]
                + s["proof_changed"]
                + s["type_changed"]
                + s["renamed_k1n"]
                + s["alpha_k1a"]
                + s["ambiguous_k1n_b_decls"]
                + s["ambiguous_k1a_b_decls"]
                + s["added"],
            )

            # Check specific entries
            self.assertEqual(rep["tiers"]["renamed_k1n"][0]["a_name"], "Pkg.old_name")
            self.assertEqual(rep["tiers"]["renamed_k1n"][0]["name"], "Pkg.new_name")
            self.assertEqual(rep["tiers"]["alpha_k1a"][0]["a_name"], "Pkg.alpha_old")
            self.assertEqual(rep["tiers"]["alpha_k1a"][0]["name"], "Pkg.alpha_new")
            self.assertEqual(rep["tiers"]["ambiguous_k1n"][0]["multiplicity"], "2:2")
            self.assertEqual(rep["tiers"]["ambiguous_k1a"][0]["multiplicity"], "2:1")

            # Root cones & movers
            self.assertEqual(len(rep["root_cones"]), 1)
            rc = rep["root_cones"][0]
            self.assertEqual(rc["name"], "Pkg.root")
            self.assertEqual(rc["live_a"], 12)
            self.assertEqual(rc["live_b"], 11)
            self.assertEqual(rc["live_delta"], -1)
            self.assertEqual(rc["dom_subtree_a"], 500)
            self.assertEqual(rc["dom_subtree_b"], 650)
            self.assertEqual(rc["dom_subtree_delta"], 150)

            self.assertEqual(rep["top_dom_movers"][0]["name"], "Pkg.root")
            self.assertEqual(rep["top_dom_movers"][0]["delta"], 150)
            self.assertEqual(rep["top_value_movers"][0]["name"], "Pkg.new_name")
            self.assertEqual(rep["top_value_movers"][0]["delta"], 70)
            self.assertEqual(rep["top_type_movers"][0]["name"], "Pkg.type_mod")
            self.assertEqual(rep["top_type_movers"][0]["delta"], 10)

    def test_tcb_regressions_and_fail_on_regression(self) -> None:
        """Verify all 6 TCB regression types, dead decide_kernel non-regression, and exit code 2."""
        with tempfile.TemporaryDirectory() as td:
            a_path = os.path.join(td, "a.db")
            b_path = os.path.join(td, "b.db")

            decls_a = [
                {"id": 1, "name": "propext", "kind": "axiom", "k1n": _h("propext"), "k1a": _h("propext", "k1a")},
                {"id": 2, "name": "T.clean_to_sorry", "k1n": _h("c2s"), "k1a": _h("c2s", "k1a"), "flags": 0},
                {"id": 3, "name": "T.dead_decide", "k1n": _h("dd"), "k1a": _h("dd", "k1a"), "flags": kdiff.F_OF_DECIDE, "live_mask": 0},
                {"id": 4, "name": "T.already_sorry", "k1n": _h("as"), "k1a": _h("as", "k1a"), "flags": kdiff.F_SORRY},
            ]
            decls_b = [
                {"id": 10, "name": "propext", "kind": "axiom", "k1n": _h("propext"), "k1a": _h("propext", "k1a")},
                {"id": 11, "name": "T.clean_to_sorry", "k1n": _h("c2s"), "k1a": _h("c2s", "k1a"), "flags": kdiff.F_SORRY, "vn": 25},
                {"id": 12, "name": "T.dead_decide", "k1n": _h("dd"), "k1a": _h("dd", "k1a"), "flags": kdiff.F_OF_DECIDE, "live_mask": 1},
                {"id": 13, "name": "T.already_sorry", "k1n": _h("as"), "k1a": _h("as", "k1a"), "flags": kdiff.F_SORRY},
                {"id": 14, "name": "T.added_native", "k1n": _h("nat"), "k1a": _h("nat", "k1a"), "flags": kdiff.F_REDUCE_BOOL},
                {"id": 15, "name": "T.added_rnat", "k1n": _h("rnat"), "k1a": _h("rnat", "k1a"), "flags": kdiff.F_REDUCE_NAT},
                {"id": 16, "name": "T.added_tc", "k1n": _h("tc"), "k1a": _h("tc", "k1a"), "flags": kdiff.F_TRUST_COMPILER},
                {"id": 17, "name": "T.custom_ax", "kind": "axiom", "k1n": _h("cax"), "k1a": _h("cax", "k1a")},
                {"id": 18, "name": "T.new_dead_decide", "k1n": _h("ndd"), "k1a": _h("ndd", "k1a"), "flags": kdiff.F_OF_DECIDE, "live_mask": 0},
            ]
            _create_kernel_db(a_path, decls_a)
            _create_kernel_db(b_path, decls_b)

            rep = kdiff.run_kdiff(a_path, b_path)
            rc = rep["regressions"]["counts"]
            self.assertEqual(rc["new_sorry"], 1)
            self.assertEqual(rc["new_reduce_bool"], 1)
            self.assertEqual(rc["new_reduce_nat"], 1)
            self.assertEqual(rc["new_trust_compiler"], 1)
            self.assertEqual(rc["new_custom_axiom"], 1)
            self.assertEqual(rc["newly_live_decide_kernel"], 1)
            self.assertEqual(rep["regressions"]["total"], 6)
            self.assertEqual(rep["regressions"]["informational"]["new_decide_kernel_dead"], 1)

            # CLI exit codes: 0 without --fail-on-regression, 2 with --fail-on-regression
            buf = io.StringIO()
            with redirect_stdout(buf):
                code0 = kdiff.main([a_path, b_path, "--format", "json"])
            self.assertEqual(code0, 0)

            buf2 = io.StringIO()
            with redirect_stdout(buf2):
                code2 = kdiff.main([a_path, b_path, "--fail-on-regression"])
            self.assertEqual(code2, 2)
            self.assertIn("SECURITY / TCB REGRESSIONS DETECTED: 6", buf2.getvalue())

            # Self-diff with --fail-on-regression must exit 0
            buf3 = io.StringIO()
            with redirect_stdout(buf3):
                code_ok = kdiff.main([a_path, a_path, "--fail-on-regression"])
            self.assertEqual(code_ok, 0)

    def test_annot_dir_reanchor_preview(self) -> None:
        """Verify read-only --annot-dir preview classifies exact, moved/renamed, needs-review, orphaned."""
        with tempfile.TemporaryDirectory() as td:
            a_path = os.path.join(td, "a.db")
            b_path = os.path.join(td, "b.db")
            ann_dir = os.path.join(td, "annots")
            os.makedirs(ann_dir, exist_ok=True)

            k_exact = _h("exact")
            k_moved = _h("moved")
            k_chg_a = _h("chg_a")
            k_chg_b = _h("chg_b")
            k_orphan = _h("orphan")

            _create_kernel_db(
                a_path,
                [
                    {"id": 1, "name": "A.exact", "k1n": k_exact, "k1a": _h("exact", "k1a")},
                    {"id": 2, "name": "A.old_moved", "k1n": k_moved, "k1a": _h("moved", "k1a")},
                    {"id": 3, "name": "A.sig_chg", "k1n": k_chg_a, "k1a": _h("chg_a", "k1a")},
                    {"id": 4, "name": "A.deleted", "k1n": k_orphan, "k1a": _h("orphan", "k1a")},
                ],
            )
            _create_kernel_db(
                b_path,
                [
                    {"id": 10, "name": "A.exact", "k1n": k_exact, "k1a": _h("exact", "k1a")},
                    {"id": 11, "name": "A.new_moved", "k1n": k_moved, "k1a": _h("moved", "k1a")},
                    {"id": 12, "name": "A.sig_chg", "k1n": k_chg_b, "k1a": _h("chg_b", "k1a")},
                ],
            )

            pack = annot.Pack()
            pack.add_layer("human/notes", "human", "Notes")
            now = "2026-11-22T00:00:00Z"
            for nm, sh in (
                ("A.exact", k_exact),
                ("A.old_moved", k_moved),
                ("A.sig_chg", k_chg_a),
                ("A.deleted", k_orphan),
            ):
                pack.put(
                    annot.make_annotation(
                        name=nm,
                        layer="human/notes",
                        tag="L",
                        source="synthetic fixture",
                        author="tester",
                        now=now,
                        sighash=sh,
                        note=f"note for {nm}",
                    )
                )
            annot.PackStore(ann_dir).save(pack)

            rep = kdiff.run_kdiff(a_path, b_path, annot_dir=ann_dir)
            ap = rep["annot_preview"]
            self.assertIsNotNone(ap)
            self.assertEqual(ap["counts"]["exact"], 1)
            self.assertEqual(ap["counts"]["moved_renamed"], 1)
            self.assertEqual(ap["counts"]["needs_review"], 1)
            self.assertEqual(ap["counts"]["orphaned"], 1)
            self.assertEqual(ap["samples"]["moved_renamed"][0]["resolved_name"], "A.new_moved")

    def test_formats_out_symlink_refusal_filter_and_parser_wiring(self) -> None:
        """Verify text/markdown/json formats, symlink refusal on --out, --filter, and add_kdiff_parser."""
        with tempfile.TemporaryDirectory() as td:
            a_path = os.path.join(td, "a.db")
            b_path = os.path.join(td, "b.db")
            _create_kernel_db(
                a_path,
                [
                    {"id": 1, "name": "Alpha.x", "vn": 10, "k1n": _h("ax"), "k1a": _h("ax", "k1a")},
                    {"id": 2, "name": "Beta.y", "vn": 10, "k1n": _h("by"), "k1a": _h("by", "k1a")},
                ],
            )
            _create_kernel_db(
                b_path,
                [
                    {"id": 1, "name": "Alpha.x", "vn": 50, "k1n": _h("ax"), "k1a": _h("ax", "k1a")},
                    {"id": 2, "name": "Beta.y", "vn": 60, "k1n": _h("by"), "k1a": _h("by", "k1a")},
                ],
            )

            # Markdown --out
            md_out = os.path.join(td, "diff.md")
            rc = kdiff.main([a_path, b_path, "--format", "markdown", "--out", md_out, "--filter", "Alpha"])
            self.assertEqual(rc, 0)
            with open(md_out, "r", encoding="utf-8") as f:
                md_text = f.read()
            self.assertIn("# Kernel BinDiff", md_text)
            self.assertIn("`Alpha.x`", md_text)
            self.assertNotIn("`Beta.y`", md_text)

            # JSON --out
            json_out = os.path.join(td, "diff.json")
            rc_j = kdiff.main([a_path, b_path, "--format", "json", "--out", json_out, "--top", "1"])
            self.assertEqual(rc_j, 0)
            with open(json_out, "r", encoding="utf-8") as f:
                payload = json.load(f)
            self.assertEqual(payload["schema_version"], "leanre.kdiff/1")
            self.assertEqual(len(payload["top_value_movers"]), 1)

            # Symlink refusal on --out
            target = os.path.join(td, "real_target.txt")
            with open(target, "w", encoding="utf-8") as f:
                f.write("keep")
            sym_out = os.path.join(td, "sym.md")
            os.symlink(target, sym_out)
            rc_sym = kdiff.main([a_path, b_path, "--format", "markdown", "--out", sym_out])
            self.assertEqual(rc_sym, 1)
            with open(target, "r", encoding="utf-8") as f:
                self.assertEqual(f.read(), "keep")

            # add_kdiff_parser + cmd_kdiff wiring test (mimicking leanre/leanre.py)
            ap = argparse.ArgumentParser(prog="leanre")
            sub = ap.add_subparsers(dest="cmd", required=True)
            kdiff.add_kdiff_parser(sub)
            parsed = ap.parse_args(["kdiff", a_path, b_path, "--format", "json"])
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc_w = parsed.kdiff_func(parsed)
            self.assertEqual(rc_w, 0)
            self.assertEqual(json.loads(buf.getvalue())["summary"]["proof_changed"], 2)


class TestKdiffLiveSelfDiff(unittest.TestCase):
    def test_live_kernel_db_self_diff_under_30s(self) -> None:
        live_db = os.path.join(_REPO_ROOT, "outputs", "kernel", "kernel.db")
        if not os.path.isfile(live_db):
            self.skipTest("outputs/kernel/kernel.db not present")
        rep = kdiff.run_kdiff(live_db, live_db, top=10)
        s = rep["summary"]
        self.assertLess(rep["timing_s"], 30.0)
        self.assertEqual(s["decls_a"], s["decls_b"])
        self.assertEqual(s["unchanged"], s["decls_a"])
        self.assertEqual(s["proof_changed"], 0)
        self.assertEqual(s["type_changed"], 0)
        self.assertEqual(s["renamed_k1n"], 0)
        self.assertEqual(s["alpha_k1a"], 0)
        self.assertEqual(s["added"], 0)
        self.assertEqual(s["removed"], 0)
        self.assertFalse(s["has_regression"])


if __name__ == "__main__":
    unittest.main()
