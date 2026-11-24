#!/usr/bin/env python3
"""Unit & integration tests for ``leanre.circuit`` (3-level Proof-Circuit engine)."""
from __future__ import annotations

import io
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
from contextlib import redirect_stdout

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import circuit  # noqa: E402
import kernel  # noqa: E402
import leanre as leanre_cli  # noqa: E402
if not hasattr(leanre_cli, "main"):
    from leanre import leanre as leanre_cli  # type: ignore[no-redef]

TINY_DEMO_DIR = os.path.join(_REPO_ROOT, "examples", "tiny_demo")
REAL_KDB = os.path.join(_REPO_ROOT, "outputs", "kernel", "kernel.db")
REAL_SRC = os.path.join(_REPO_ROOT, "data", "rh_mirror", "src")
SVG_NS = "{http://www.w3.org/2000/svg}"


def _assert_valid_svg(test: unittest.TestCase, svg_text: str) -> ET.Element:
    root = ET.fromstring(svg_text)
    test.assertTrue(root.tag.endswith("svg"))
    w = float(root.attrib["width"])
    h = float(root.attrib["height"])
    test.assertGreater(w, 200.0)
    test.assertGreater(h, 150.0)

    node_rects = []
    for r in root.findall(f".//{SVG_NS}rect"):
        rx = float(r.attrib.get("x", 0.0))
        ry = float(r.attrib.get("y", 0.0))
        rw = float(r.attrib.get("width", 0.0))
        rh = float(r.attrib.get("height", 0.0))
        test.assertGreaterEqual(rx, 0.0)
        test.assertGreaterEqual(ry, 0.0)
        test.assertLessEqual(rx + rw, w + 1.0)
        test.assertLessEqual(ry + rh, h + 1.0)

    for g in root.findall(f'.//{SVG_NS}g[@class="circuit-node"]'):
        r = g.find(f"{SVG_NS}rect")
        if r is not None:
            rx = float(r.attrib["x"])
            ry = float(r.attrib["y"])
            rw = float(r.attrib["width"])
            rh = float(r.attrib["height"])
            node_rects.append((g.attrib.get("data-node-id", ""), rx, ry, rx + rw, ry + rh))
            for t in g.findall(f"{SVG_NS}text"):
                fs = float(t.attrib.get("font-size", 11.0))
                txt = t.text or ""
                test.assertLessEqual(len(txt) * fs * 0.60, rw + 6.0, f"Text clipped in {g.attrib}: {txt!r}")

    for i in range(len(node_rects)):
        id1, x1a, y1a, x1b, y1b = node_rects[i]
        for j in range(i + 1, len(node_rects)):
            id2, x2a, y2a, x2b, y2b = node_rects[j]
            ov_x = min(x1b, x2b) - max(x1a, x2a)
            ov_y = min(y1b, y2b) - max(y1a, y2a)
            test.assertFalse(ov_x > 1.5 and ov_y > 1.5, f"Overlapping node rects {id1} vs {id2}")
    return root


def _build_synthetic_circuit_db(td: str, *, include_xss: bool = False) -> tuple[str, str]:
    """Create a synthetic Lean project + SQLite kernel.db exercising all 3 circuit zoom levels."""
    src_dir = os.path.join(td, "src")
    os.makedirs(src_dir, exist_ok=True)
    xss_tail = '<script>alert(1)</script>'
    thm_name = f'SynProj.thm_{xss_tail}' if include_xss else "SynProj.mainThm"
    bundle_name = "SynProj.SpecRec"

    lean_lines = [
        "namespace SynProj",
        "structure SpecRec where",
        "  coreOk : Nat",
        "  unreadField : Nat",
        "  condField : Nat → True",
        "  stubField : True",
        "",
        "def mkSpec (n : Nat) : SpecRec :=",
        "  { coreOk := n, unreadField := 0, condField := fun _ => trivial, stubField := trivial }",
        "",
        "def readCore (s : SpecRec) : Nat := s.coreOk",
        "",
        "def helperZero (n : Nat) : Nat :=",
        "  if h : 0 < n then n else 0",
        "",
        "theorem repeatShapeA (n : Nat) : Eq n n := Eq.refl n",
        "theorem repeatShapeB (m : Nat) : Eq m m := Eq.refl m",
        "theorem repeatShapeC (k : Nat) : Eq k k := Eq.refl k",
        "theorem repeatShapeD (p : Nat) : Eq p p := Eq.refl p",
        "theorem repeatShapeE (q : Nat) : Eq q q := Eq.refl q",
        "",
        "theorem dropConsumer (s : SpecRec) : True := trivial",
        "",
        "theorem useConsumer (s : SpecRec) : Eq s.coreOk s.coreOk := Eq.refl s.coreOk",
        "",
        "theorem stepProof (n : Nat) (hUnused : Nat) : Eq (readCore (mkSpec n)) (readCore (mkSpec n)) := by",
        "  have s1 := mkSpec n",
        "  have s2 := readCore s1",
        "  have _h := repeatShapeA s2",
        "  exact Eq.refl s2",
        "",
        "theorem deadIsland (x : Nat) : Eq x x := Eq.refl x",
        "end SynProj",
    ]
    lean_path = os.path.join(src_dir, "SynProj.lean")
    with open(lean_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lean_lines) + "\n")

    kdb_path = os.path.join(td, "kernel.db")
    conn = sqlite3.connect(kdb_path)
    conn.executescript(
        """
        CREATE TABLE meta(key TEXT PRIMARY KEY, value_json TEXT NOT NULL);
        CREATE TABLE decls(
            id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
            n_consts INTEGER NOT NULL, type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL,
            fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
            fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL,
            flags INTEGER NOT NULL, live_mask INTEGER NOT NULL,
            stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL,
            attrs INTEGER NOT NULL, sighash TEXT, sighash_anon TEXT
        );
        CREATE TABLE consts(
            id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL,
            ckind TEXT NOT NULL, ord INTEGER NOT NULL,
            sighash TEXT, sighash_anon TEXT, sig_size INTEGER, n_local INTEGER
        );
        CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src, dst)) WITHOUT ROWID;
        CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
        CREATE TABLE reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, depth INTEGER NOT NULL, parent INTEGER, PRIMARY KEY(root_id, decl_id)) WITHOUT ROWID;
        CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
        CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id, decl_id)) WITHOUT ROWID;
        CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT NOT NULL, src_decl_id INTEGER);
        CREATE UNIQUE INDEX decls_name ON decls(name);
        CREATE INDEX consts_sighash ON consts(sighash);
        CREATE INDEX consts_sighash_anon ON consts(sighash_anon);
        CREATE INDEX edges_dst ON edges(dst, src);
        CREATE INDEX dom_top ON dom(tree_id, subtree_size DESC, decl_id);
        CREATE INDEX dom_idom ON dom(tree_id, idom, subtree_size DESC, decl_id);
        """
    )

    decls = [
        (1, bundle_name, "inductive", 1, 10, 0, 5, 0, 0, 0, 0, 1, 1, 0, 0, "k1n:spec", "k1a:spec"),
        (2, f"{bundle_name}.coreOk", "def", 1, 4, 2, 2, 1, 1, 1, 0, 1, 0, 0, 0, "k1n:proj", "k1a:proj"),
        (3, "SynProj.mkSpec", "def", 1, 6, 8, 2, 1, 1, 1, 0, 1, 0, 0, 0, "k1n:mk", "k1a:mk"),
        (4, "SynProj.readCore", "def", 1, 4, 4, 2, 2, 1, 1, 0, 1, 0, 0, 0, "k1n:read", "k1a:read"),
        (5, "SynProj.helperZero", "def", 1, 4, 6, 1, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:hz", "k1a:hz"),
        (6, "SynProj.repeatShapeA", "thm", 1, 4, 3, 2, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:rep5", "k1a:rep5"),
        (7, "SynProj.repeatShapeB", "thm", 1, 4, 3, 1, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:rep5", "k1a:rep5"),
        (8, "SynProj.repeatShapeC", "thm", 1, 4, 3, 1, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:rep5", "k1a:rep5"),
        (9, "SynProj.repeatShapeD", "thm", 1, 4, 3, 1, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:rep5", "k1a:rep5"),
        (10, "SynProj.repeatShapeE", "thm", 1, 4, 3, 1, 1, 0, 1, 0, 1, 0, 0, 0, "k1n:rep5", "k1a:rep5"),
        (11, "SynProj.dropConsumer", "thm", 1, 4, 2, 1, 1, 1, 0, 0, 1, 0, 0, 0, "k1n:dropc", "k1a:dropc"),
        (12, "SynProj.useConsumer", "thm", 1, 4, 5, 1, 2, 1, 1, 0, 1, 0, 0, 0, "k1n:usec", "k1a:usec"),
        (13, "SynProj.stepProof", "thm", 1, 8, 12, 1, 5, 1, 4, 0, 1, 1, 0, 0, "k1n:step", "k1a:step"),
        (14, thm_name, "thm", 1, 6, 10, 0, 3, 1, 2, 0, 1, 1, 0, 0, "k1n:root", "k1a:root"),
        (15, "SynProj.deadIsland", "thm", 1, 4, 3, 0, 1, 0, 1, 0, 0, 0, 0, 0, "k1n:dead", "k1a:dead"),
        (16, "SynProj.propShellA", "def", 1, 1, 5, 1, 0, 0, 0, 0, 1, 0, 0, 0, circuit._PROP_SIGHASH, "k1a:64ae2cd10a490abdd34316b6e3b02ee1"),
        (17, "SynProj.propShellB", "def", 1, 1, 5, 1, 0, 0, 0, 0, 1, 0, 0, 0, circuit._PROP_SIGHASH, "k1a:64ae2cd10a490abdd34316b6e3b02ee1"),
        (18, "SynProj.propShellC", "def", 1, 1, 5, 1, 0, 0, 0, 0, 1, 0, 0, 0, circuit._PROP_SIGHASH, "k1a:64ae2cd10a490abdd34316b6e3b02ee1"),
    ]
    conn.executemany("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", decls)
    conn.executemany(
        "INSERT INTO consts VALUES (?,?,?,?,?,?,?,?,?)",
        [(i, nm, i, "thm" if knd == "thm" else "def", 0, sh, sha, 1 if i >= 16 else 4, 0) for i, nm, knd, *_rest, sh, sha in decls]
        + [(100, f"{bundle_name}.mk", 1, "ctor", 0, "k1n:ctor", "k1a:ctor", 2, 0)],
    )
    conn.executemany(
        "INSERT INTO decl_module VALUES (?,?,?,?)",
        [(i, "SynProj", "exact", i) for i in range(1, 19)],
    )
    edges = [
        (2, 1, 1), (3, 1, 3), (4, 1, 1), (4, 2, 2),
        (11, 1, 1), (12, 1, 1), (12, 2, 2),
        (13, 3, 2), (13, 4, 2), (13, 6, 2), (13, 16, 2), (13, 1, 1), (13, 5, 2),
        (14, 13, 2), (14, 11, 2), (14, 12, 2),
    ]
    conn.executemany("INSERT INTO edges VALUES (?,?,?)", edges)
    conn.execute("INSERT INTO roots VALUES (0, ?, 14, 'SYN')", (thm_name,))
    conn.executemany("INSERT INTO reach VALUES (0, ?, ?, NULL)", [(i, 1 if i != 14 else 0) for i in range(1, 15)])
    conn.execute("INSERT INTO dom_trees VALUES (0, 'ALL', 'proof', '0', 14)")
    dom_rows = [
        (0, 14, None, 0, 14),
        (0, 13, 14, 1, 7),
        (0, 11, 14, 1, 2),
        (0, 12, 14, 1, 2),
        (0, 1, 14, 1, 3),
        (0, 3, 13, 2, 1),
        (0, 4, 13, 2, 1),
        (0, 6, 13, 2, 1),
        (0, 5, 13, 2, 1),
    ]
    conn.executemany("INSERT INTO dom VALUES (?,?,?,?,?)", dom_rows)
    conn.commit()
    conn.close()
    return kdb_path, src_dir


class TestCircuitSynthetic(unittest.TestCase):
    def test_three_levels_synthetic_svg_html_and_xss(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            kdb_path, src_dir = _build_synthetic_circuit_db(td, include_xss=True)

            # Zoom 0: Macro
            macro_p = circuit.build_macro_circuit(kdb_path, src_root=src_dir)
            self.assertEqual(macro_p["schema"], circuit.SCHEMA_VERSION)
            self.assertEqual(macro_p["mode"], "macro")
            self.assertEqual(macro_p["stats"]["total_decls"], 18)
            self.assertEqual(macro_p["stats"]["live_decls"], 17)
            self.assertEqual(macro_p["stats"]["dead_decls"], 1)
            self.assertGreaterEqual(macro_p["stats"]["motif_clusters_count"], 1)
            self.assertEqual(macro_p["stats"]["excluded_prop_shells"], 3)
            self.assertGreaterEqual(macro_p["stats"]["excluded_trivial_shells"], 3)
            motif_hashes = {mt["sighash"] for mt in macro_p["meta"]["motifs"]}
            self.assertNotIn(circuit._PROP_SIGHASH, motif_hashes)
            self.assertIn("k1n:rep5", motif_hashes)
            for theme in ("dark", "light"):
                svg_m = circuit.render_circuit_svg(macro_p, theme=theme)
                self.assertNotIn("<script>alert", svg_m)
                self.assertNotIn("mode=MACRO", svg_m)
                self.assertIn("ENTRY THEOREMS &amp; UNREACHED DECLARATIONS", svg_m)
                self.assertIn("REPEATED STATEMENT PATTERNS", svg_m)
                self.assertIn("AST nodes)", svg_m)
                self.assertNotIn("k1n ×", svg_m)
                _assert_valid_svg(self, svg_m)
            src_macro = dict(macro_p, source_only=True)
            svg_src = circuit.render_circuit_svg(src_macro, theme="dark")
            self.assertIn("Module import overview · source scan", svg_src)
            self.assertIn("MOST-IMPORTED MODULES (BY DIRECT IMPORTERS)", svg_src)
            self.assertIn("INCOMPLETE / AXIOMATIC HOTSPOTS", svg_src)
            self.assertIn("import edges:", svg_src)
            self.assertNotIn("cross-pillar edges:", svg_src)
            html_m = circuit.render_circuit_html(macro_p)
            self.assertNotIn("<script>alert", html_m)
            self.assertEqual(
                set(re.findall(r"https?://[^\s\"'<>\\]+", html_m)),
                {"http://www.w3.org/2000/svg"},
            )
            self.assertIn("LEANRE_CIRCUIT_ON_NODE_CLICK", html_m)
            self.assertIn("leanre:circuit-zoom", html_m)

            # Zoom 1: Bundle (SpecRec with projected, unread, conditional, literal_true, dropped consumer)
            bun_p = circuit.build_bundle_circuit(kdb_path, "SpecRec", src_root=src_dir)
            self.assertEqual(bun_p["mode"], "bundle")
            self.assertIn("Structure Field Usage —", bun_p["title"])
            self.assertNotIn("Bundle Pin-Board", bun_p["title"])
            self.assertEqual(bun_p["stats"]["total_fields"], 4)
            self.assertEqual(bun_p["stats"]["projected_fields"], 1)
            self.assertEqual(bun_p["stats"]["unread_fields"], 1)
            self.assertEqual(bun_p["stats"]["conditional_prop_fields"], 1)
            self.assertEqual(bun_p["stats"]["literal_true_fields"], 1)
            self.assertEqual(bun_p["stats"]["consumers_dropped_input"], 1)
            b_labels = [b["label"] for b in bun_p["badges"]]
            self.assertIn("builders: 1 root", b_labels)
            self.assertIn("fields: 1 read · 1 unread", b_labels)
            self.assertFalse(any("root:0" in lbl or "local:0" in lbl for lbl in b_labels))
            for theme in ("dark", "light"):
                svg_b = circuit.render_circuit_svg(bun_p, theme=theme)
                self.assertIn("Structure Field Usage —", svg_b)
                self.assertNotIn("Bundle Pin-Board", svg_b)
                _assert_valid_svg(self, svg_b)
            html_b = circuit.render_circuit_html(bun_p)
            self.assertEqual(
                set(re.findall(r"https?://[^\s\"'<>\\]+", html_b)),
                {"http://www.w3.org/2000/svg"},
            )

            # Zoom 2: Theorem (stepProof with Tromp binder bar, dropped hUnused, obtain/have chain, ×5+ pattern, muted Prop shell callee)
            thm_p = circuit.build_theorem_circuit(kdb_path, "SynProj.stepProof", src_root=src_dir)
            self.assertEqual(thm_p["mode"], "theorem")
            self.assertEqual(thm_p["stats"]["binders_used"], 1)
            self.assertEqual(thm_p["stats"]["binders_dropped"], 1)
            self.assertGreaterEqual(thm_p["stats"]["steps_count"], 3)
            self.assertGreaterEqual(thm_p["stats"]["wire_count"], 3)
            prop_callees = [nd for nd in thm_p["nodes"] if nd["kind"] == "callee" and nd["full_name"] == "SynProj.propShellA"]
            self.assertEqual(len(prop_callees), 1)
            self.assertEqual(prop_callees[0]["status"], "trivial_shell")
            self.assertEqual(prop_callees[0]["color_key"], "slate")
            self.assertEqual(prop_callees[0]["badge"], "Prop")
            rep_callees = [nd for nd in thm_p["nodes"] if nd["kind"] == "callee" and nd["full_name"] == "SynProj.repeatShapeA"]
            self.assertEqual(len(rep_callees), 1)
            self.assertEqual(rep_callees[0]["color_key"], "violet")
            self.assertEqual(rep_callees[0]["badge"], "×5")
            for theme in ("dark", "light"):
                svg_t = circuit.render_circuit_svg(thm_p, theme=theme)
                self.assertIn("×2–4 Repeated pattern", svg_t)
                self.assertIn("Default-0 / refl / True pin", svg_t)
                self.assertNotIn("k1n ×", svg_t)
                _assert_valid_svg(self, svg_t)
            _ = circuit.render_circuit_html(thm_p)

            # Zoom 2 semantic pin on helperZero (`else 0` -> rendered as `Default-0`)
            hz_p = circuit.build_theorem_circuit(kdb_path, "SynProj.helperZero", src_root=src_dir)
            self.assertTrue(any(b["label"] == "else 0" for b in hz_p["badges"]))
            svg_hz = circuit.render_circuit_svg(hz_p, theme="dark")
            self.assertIn("Default-0", svg_hz)
            _assert_valid_svg(self, svg_hz)

            # Read-only chmod 0444/0555 + kernel-only mode (no src_root, no portability_gems.json)
            ro_dir = os.path.join(td, "ro_db")
            os.makedirs(ro_dir, exist_ok=True)
            ro_db = os.path.join(ro_dir, "kernel.db")
            with open(kdb_path, "rb") as src_f, open(ro_db, "wb") as dst_f:
                dst_f.write(src_f.read())
            os.chmod(ro_db, stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)
            os.chmod(ro_dir, stat.S_IRUSR | stat.S_IXUSR)
            try:
                ro_macro = circuit.build_macro_circuit(ro_db)
                self.assertEqual(ro_macro["pins"]["source_mode"], "kernel_only")
                ro_thm = circuit.build_theorem_circuit(ro_db, "SynProj.stepProof")
                self.assertEqual(ro_thm["pins"]["source_mode"], "kernel_only")
                _assert_valid_svg(self, circuit.render_circuit_svg(ro_thm))
            finally:
                os.chmod(ro_dir, stat.S_IRWXU)
                os.chmod(ro_db, stat.S_IRUSR | stat.S_IWUSR)

    def test_cli_flags_mode_alias_and_symlink_refusal(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            kdb_path, src_dir = _build_synthetic_circuit_db(td, include_xss=False)
            svg_out = os.path.join(td, "out.svg")
            html_out = os.path.join(td, "out.html")

            with redirect_stdout(io.StringIO()):
                rc1 = leanre_cli.main([
                    "circuit", "macro",
                    "--kernel-db", kdb_path,
                    "--src-root", src_dir,
                    "--svg", svg_out,
                    "--html", html_out,
                    "--theme", "light",
                    "--title", "Custom Macro",
                ])
            self.assertEqual(rc1, 0)
            with open(svg_out, encoding="utf-8") as f_svg:
                _assert_valid_svg(self, f_svg.read())
            with open(html_out, encoding="utf-8") as f_html:
                self.assertIn("Custom Macro", f_html.read())

            # --mode alias + --json + --exact-case + --max-nodes
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc2 = leanre_cli.main([
                    "circuit", "--mode", "bundle", "SpecRec",
                    "--kernel-db", kdb_path,
                    "--src-root", src_dir,
                    "--max-nodes", "2",
                    "--exact-case",
                    "--json",
                ])
            self.assertEqual(rc2, 0)
            parsed = json.loads(buf.getvalue())
            self.assertEqual(parsed["mode"], "bundle")

            # Symlink target refusal
            sym_target = os.path.join(td, "real.svg")
            sym_link = os.path.join(td, "link.svg")
            os.symlink(sym_target, sym_link)
            with self.assertRaises(ValueError):
                circuit._safe_write_text(sym_link, "<svg/>")


class TestCircuitTinyDemo(unittest.TestCase):
    def test_tiny_demo_all_three_levels(self) -> None:
        bin_path = kernel.default_binary_path()
        if not os.path.exists(bin_path):
            self.skipTest("leanre-kernel release binary not built")
        ndjson_path = os.path.join(TINY_DEMO_DIR, "demo.ndjson")
        with tempfile.TemporaryDirectory() as td:
            out_dir = os.path.join(td, "kernel_out")
            kernel.run_pipeline(
                input_path=ndjson_path,
                out_dir=out_dir,
                src_dir=TINY_DEMO_DIR,
                roots=["TinyDemo.main_theorem:DEMO"],
                threads=2,
                workers=1,
                auto_build=False,
                verbose=False,
            )
            kdb_path = os.path.join(out_dir, "kernel.db")

            m = circuit.build_macro_circuit(kdb_path, src_root=TINY_DEMO_DIR)
            self.assertEqual(m["stats"]["total_decls"], 17)
            self.assertEqual(m["stats"]["live_decls"], 10)
            self.assertEqual(m["stats"]["dead_decls"], 7)
            _assert_valid_svg(self, circuit.render_circuit_svg(m, theme="dark"))

            b = circuit.build_bundle_circuit(kdb_path, "ProofBundle", src_root=TINY_DEMO_DIR)
            self.assertEqual(b["stats"]["projected_fields"], 1)
            self.assertEqual(b["stats"]["unread_fields"], 1)
            _assert_valid_svg(self, circuit.render_circuit_svg(b, theme="light"))

            t = circuit.build_theorem_circuit(kdb_path, "TinyDemo.main_theorem", src_root=TINY_DEMO_DIR)
            self.assertEqual(t["stats"]["binders_used"], 1)
            self.assertEqual(t["stats"]["binders_dropped"], 0)
            _assert_valid_svg(self, circuit.render_circuit_svg(t, theme="dark"))


class TestCircuitRealKernelDB(unittest.TestCase):
    def test_real_kernel_db_macro_bundle_theorem(self) -> None:
        if not (os.path.isfile(REAL_KDB) and os.path.isdir(REAL_SRC)):
            self.skipTest("real outputs/kernel/kernel.db or mirror not present")

        # 1. Macro under 5s budget (target < 3s)
        t0 = time.monotonic()
        m = circuit.build_macro_circuit(REAL_KDB, src_root=REAL_SRC)
        elapsed_m = time.monotonic() - t0
        self.assertLess(elapsed_m, 5.0, f"Macro took too long: {elapsed_m:.2f}s")
        self.assertGreater(m["stats"]["total_decls"], 1_000_000)
        self.assertEqual(m["stats"]["motif_clusters_count"], 10)
        self.assertEqual(m["stats"]["excluded_prop_shells"], 22984)
        self.assertGreaterEqual(m["stats"]["excluded_trivial_shells"], 22984)
        for mt in m["meta"]["motifs"]:
            self.assertNotIn(mt["sighash"], circuit._TRIVIAL_SIGHASH_LABELS)
            self.assertGreaterEqual(mt["min_type_nodes"], 4)
        self.assertGreaterEqual(m["stats"]["islands_count"], 2)
        self.assertGreater(m["stats"]["shared_diamond_decls"], 0)
        _assert_valid_svg(self, circuit.render_circuit_svg(m, theme="dark"))

        # 2. Bundle pin-boards
        b_open = circuit.build_bundle_circuit(REAL_KDB, "OpenLiteratureStatements", src_root=REAL_SRC, exact_case=True)
        self.assertEqual(b_open["stats"]["consumers_audited"], 195)
        self.assertEqual(b_open["stats"]["consumers_dropped_input"], 152)
        _assert_valid_svg(self, circuit.render_circuit_svg(b_open, theme="dark"))

        b_real = circuit.build_bundle_circuit(REAL_KDB, "RealInAlt", src_root=REAL_SRC, exact_case=True)
        self.assertEqual(b_real["stats"]["conditional_prop_fields"], 3)
        _assert_valid_svg(self, circuit.render_circuit_svg(b_real, theme="light"))

        b_hyps = circuit.build_bundle_circuit(REAL_KDB, "HypsAlt", src_root=REAL_SRC, exact_case=True)
        self.assertEqual(b_hyps["stats"]["total_fields"], 46)
        _assert_valid_svg(self, circuit.render_circuit_svg(b_hyps, theme="dark"))

        # 3. Theorems
        t_link = circuit.build_theorem_circuit(REAL_KDB, "linkGLOBAL7_items", src_root=REAL_SRC, exact_case=True)
        self.assertEqual(t_link["stats"]["binders_dropped"], 0)
        self.assertGreaterEqual(t_link["stats"]["steps_count"], 10)
        _assert_valid_svg(self, circuit.render_circuit_svg(t_link, theme="dark"))

        t_ll = circuit.build_theorem_circuit(REAL_KDB, "llOf_alt", src_root=REAL_SRC, exact_case=True)
        self.assertEqual(t_ll["stats"]["binders_used"], 1)
        self.assertEqual(t_ll["stats"]["binders_dropped"], 11)
        ll_callees = [nd for nd in t_ll["nodes"] if nd["kind"] == "callee"]
        self.assertGreaterEqual(len(ll_callees), 10)
        for cn in ll_callees:
            self.assertEqual(cn["status"], "trivial_shell")
            self.assertEqual(cn["color_key"], "slate")
            self.assertEqual(cn["badge"], "Prop")
            self.assertNotIn("22,984", cn["badge"])
        _assert_valid_svg(self, circuit.render_circuit_svg(t_ll, theme="dark"))

        t_ch = circuit.build_theorem_circuit(REAL_KDB, "ch_balance", src_root=REAL_SRC, exact_case=True)
        self.assertEqual(t_ch["stats"]["binders_dropped"], 0)
        self.assertGreaterEqual(t_ch["stats"]["steps_count"], 8)
        _assert_valid_svg(self, circuit.render_circuit_svg(t_ch, theme="dark"))


if __name__ == "__main__":
    unittest.main()
