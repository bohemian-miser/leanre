#!/usr/bin/env python3
"""Unit tests for `leanre.embedding` (synthetic DB, determinism, bounds, PNG & OPSEC)."""
from __future__ import annotations

import json
import os
import sqlite3
import struct
import tempfile
import unittest
import zlib

import numpy as np  # type: ignore[import-not-found]

try:
    from leanre import embedding
except ImportError:  # pragma: no cover
    import embedding  # type: ignore[no-redef]


def _build_synthetic_embedding_db(kdb_path: str, ldb_path: str) -> None:
    """Create a realistic multi-directory synthetic `kernel.db` + `leanre.db`."""
    con = sqlite3.connect(kdb_path)
    con.executescript(
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
        CREATE TABLE edges(
            src INTEGER NOT NULL,
            dst INTEGER NOT NULL,
            kind INTEGER NOT NULL,
            PRIMARY KEY(src, dst)
        ) WITHOUT ROWID;
        CREATE TABLE dom(
            tree_id INTEGER NOT NULL,
            decl_id INTEGER NOT NULL,
            idom INTEGER,
            depth INTEGER NOT NULL,
            subtree_size INTEGER NOT NULL,
            PRIMARY KEY(tree_id, decl_id)
        ) WITHOUT ROWID;
        CREATE TABLE decl_module(
            decl_id INTEGER PRIMARY KEY,
            module TEXT,
            method TEXT NOT NULL,
            src_decl_id INTEGER
        );
        """
    )

    # 12 external library symbols across 3 mathematical domains:
    # 0..3: NumberTheory/Padic, 4..7: MeasureTheory/Analysis, 8..11: AlgebraicGeometry/Cohomology
    ext_names = [
        ("NumberField.RingOfIntegers", "def"),
        ("HeightOneSpectrum.adicCompletion", "def"),
        ("PadicInt.norm_le_one", "thm"),
        ("DirichletCharacter.conductor", "def"),
        ("MeasureTheory.integral_mono", "thm"),
        ("MeasureTheory.Measure.haar", "def"),
        ("Complex.abs_exp", "thm"),
        ("FourierTransform.integral_fourier", "thm"),
        ("AlgebraicGeometry.Scheme.Spec", "def"),
        ("CategoryTheory.Abelian.exact", "thm"),
        ("Polynomial.roots_card", "thm"),
        ("Cohomology.sheaf_iso", "thm"),
    ]
    decls = []
    mod_rows = []
    for idx, (nm, kd) in enumerate(ext_names):
        decls.append((idx, nm, kd, 1, 15 + idx, 10, 20, 0, 0, 0, 0, 1, 1, 1, 0, f"k1n:ext{idx}", f"k1a:ext{idx}"))
        mod_rows.append((idx, None, "unmatched:library_or_external", None))

    # 24 project declarations across two directories (`Alpha.Mod` and `Beta.Mod`)
    # Some in `Beta.Mod` share identical external math deps with `Alpha.Mod` to produce measurable drift!
    proj_specs = [
        # Group A (NumberTheory): ids 12..19
        (12, "Alpha.NT.local_padic_unit", "thm", "Alpha.NT.Local", [0, 1, 2, 3], 1, 2),
        (13, "Alpha.NT.ideal_norm_bound", "thm", "Alpha.NT.Local", [0, 1, 2], 1, 3),
        (14, "Alpha.NT.char_cond_factor", "def", "Alpha.NT.Global", [0, 2, 3], 2, 1),
        (15, "Beta.NT.twin_padic_unit", "thm", "Beta.NT.Hidden", [0, 1, 2, 3], 1, 2),
        (16, "Alpha.NT.SpecRing", "inductive", "Alpha.NT.Struct", [0, 1], 3, 1),
        (17, "Alpha.NT.conductor_split", "thm", "Alpha.NT.Global", [1, 2, 3], 1, 2),
        (18, "Beta.NT.completion_norm", "thm", "Beta.NT.Hidden", [0, 1, 2], 1, 3),
        (19, "Alpha.NT.adic_residue", "thm", "Alpha.NT.Local", [0, 1, 3], 1, 2),
        # Group B (MeasureTheory/Analysis): ids 20..27
        (20, "Alpha.An.haar_fourier", "thm", "Alpha.An.Harmonic", [4, 5, 6, 7], 1, 3),
        (21, "Alpha.An.exp_integral", "thm", "Alpha.An.Harmonic", [4, 6, 7], 1, 2),
        (22, "Beta.An.twin_haar", "thm", "Beta.An.Mirror", [4, 5, 6, 7], 1, 3),
        (23, "Alpha.An.L2Measure", "inductive", "Alpha.An.Struct", [4, 5], 3, 1),
        (24, "Alpha.An.plancherel_step", "thm", "Alpha.An.Harmonic", [5, 6, 7], 1, 4),
        (25, "Beta.An.fourier_decay", "thm", "Beta.An.Mirror", [4, 5, 7], 1, 2),
        (26, "Alpha.An.mellin_bound", "thm", "Alpha.An.Mellin", [4, 6, 7], 2, 2),
        (27, "Alpha.An.theta_kernel", "def", "Alpha.An.Mellin", [4, 5, 6], 2, 1),
        # Group C (AlgebraicGeometry): ids 28..35
        (28, "Beta.AG.spec_exact", "thm", "Beta.AG.Schemes", [8, 9, 10, 11], 1, 2),
        (29, "Beta.AG.sheaf_cohom", "thm", "Beta.AG.Schemes", [8, 9, 11], 1, 3),
        (30, "Alpha.AG.twin_scheme", "thm", "Alpha.AG.Bridge", [8, 9, 10, 11], 1, 2),
        (31, "Beta.AG.CohesiveSite", "inductive", "Beta.AG.Struct", [8, 9], 3, 1),
        (32, "Beta.AG.poly_roots_etale", "thm", "Beta.AG.Schemes", [8, 10, 11], 1, 2),
        (33, "Beta.AG.abelian_iso", "thm", "Beta.AG.Cohom", [9, 10, 11], 1, 3),
        (34, "Alpha.AG.etale_descent", "thm", "Alpha.AG.Bridge", [8, 9, 11], 1, 2),
        (35, "Beta.AG.sheaf_kernel", "def", "Beta.AG.Cohom", [8, 10, 11], 2, 1),
    ]

    edges = []
    for did, nm, kd, mod, ext_deps, fot, fov in proj_specs:
        decls.append((
            did, nm, kd, 1, 20 + did, 30 + did, 4, len(ext_deps), fot, fov,
            0, 1, 0, 0, 0, f"k1n:p{did}", f"k1a:p{did}",
        ))
        mod_rows.append((did, mod, "leanre_db:exact", did))
        for dst in ext_deps:
            edges.append((did, dst, 2))

    # Apex hub id=36 connecting groups via project edges (so 2-hop works too!)
    decls.append((36, "Alpha.Main.apex_theorem", "thm", 1, 50, 100, 0, 3, 1, 2, 0, 1, 1, 0, 0, "k1n:apex", "k1a:apex"))
    mod_rows.append((36, "Alpha.Main.Root", "leanre_db:exact", 36))
    edges.extend([(36, 12, 2), (36, 20, 2), (36, 28, 1)])

    con.executemany("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", decls)
    con.executemany("INSERT INTO decl_module VALUES (?,?,?,?)", mod_rows)
    con.executemany("INSERT INTO edges VALUES (?,?,?)", edges)

    # Dominator tree 0 with root=36 (subtree_size=37; give 12, 20, 28 >= 1000? Test synthetic dom>=1000 too!)
    con.execute("INSERT INTO dom VALUES (0, 36, NULL, 0, 1500)")
    for d in range(36):
        sz = 1100 if d in (12, 20, 28) else 1
        con.execute("INSERT INTO dom VALUES (0, ?, 36, 1, ?)", (d, sz))
    con.commit()
    con.close()

    # Companion leanre.db with line numbers and structure kind
    lcon = sqlite3.connect(ldb_path)
    lcon.executescript(
        """
        CREATE TABLE declarations(
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            kind TEXT NOT NULL,
            module TEXT NOT NULL,
            line_no INTEGER NOT NULL
        );
        """
    )
    for did, nm, kd, mod, *_ in proj_specs:
        lk = "structure" if kd == "inductive" else kd
        lcon.execute("INSERT INTO declarations VALUES (?,?,?,?,?)", (did, nm, lk, mod, 10 + did))
    lcon.execute("INSERT INTO declarations VALUES (36, 'Alpha.Main.apex_theorem', 'theorem', 'Alpha.Main.Root', 99)")
    lcon.commit()
    lcon.close()


class TestEmbeddingSynthetic(unittest.TestCase):
    def setUp(self) -> None:
        self.tmpdir = tempfile.TemporaryDirectory()
        self.kdb_path = os.path.join(self.tmpdir.name, "kernel.db")
        self.ldb_path = os.path.join(self.tmpdir.name, "leanre.db")
        _build_synthetic_embedding_db(self.kdb_path, self.ldb_path)

    def tearDown(self) -> None:
        self.tmpdir.cleanup()

    def test_synthetic_embedding_schema_metrics_and_png(self) -> None:
        out_json = os.path.join(self.tmpdir.name, "embedding_2d.json")
        out_png = os.path.join(self.tmpdir.name, "embedding_2d.png")
        doc = embedding.run_embedding(
            kernel_db_path=self.kdb_path,
            leanre_db_path=self.ldb_path,
            out_json_path=out_json,
            png_path=out_png,
            max_landmarks=100,
            svd_dim=24,
            knn_k=15,
            knn_steps=180,
            seed=42,
        )
        self.assertEqual(doc["schema"], embedding.SCHEMA_VERSION)
        self.assertNotIn("/tmp", doc["inputs"]["kernel_db"] or "")

        lm = doc["layers"]["landmarks"]
        cl = doc["layers"]["clusters_141"]
        self.assertGreaterEqual(lm["count"], 25)
        self.assertGreaterEqual(cl["count"], 2)
        self.assertGreater(lm["svd_explained_variance_sum"], 0.5)
        self.assertGreater(lm["metrics"]["knn2"]["knn_preservation"], 0.3)
        self.assertGreater(lm["metrics"]["knn2"]["trustworthiness"], 0.5)

        pts = embedding.decode_layer_points(lm)
        self.assertEqual(len(pts), lm["count"])

        by_name = {p["name"]: p for p in pts}
        # Verify structure kind & line resolution from leanre.db
        self.assertEqual(by_name["Alpha.NT.SpecRing"]["kind"], "structure")
        self.assertEqual(by_name["Alpha.NT.SpecRing"]["line"], 26)
        self.assertEqual(by_name["Alpha.Main.apex_theorem"]["dom"], 1500)

        # Verify coordinates lie in [-1, 1] and nn_idx are valid non-self indices
        for idx, p in enumerate(pts):
            self.assertGreaterEqual(p["px"], -1.0)
            self.assertLessEqual(p["px"], 1.0)
            self.assertGreaterEqual(p["py"], -1.0)
            self.assertLessEqual(p["py"], 1.0)
            self.assertGreaterEqual(p["ux"], -1.0)
            self.assertLessEqual(p["ux"], 1.0)
            self.assertGreaterEqual(p["uy"], -1.0)
            self.assertLessEqual(p["uy"], 1.0)
            self.assertEqual(len(p["nn_idx"]), 5)
            self.assertNotIn(idx, p["nn_idx"])
            self.assertTrue(0.0 <= p["drift"] <= 1.0)
            self.assertTrue(0.0 <= p["type_ratio"] <= 1.0)

        # Verify cross-folder twins are nearest mathematical neighbors and exhibit positive drift!
        beta_nt_idx = next(i for i, p in enumerate(pts) if p["name"] == "Beta.NT.twin_padic_unit")
        alpha_nt_idx = next(i for i, p in enumerate(pts) if p["name"] == "Alpha.NT.local_padic_unit")
        self.assertIn(alpha_nt_idx, pts[beta_nt_idx]["nn_idx"][:2])
        self.assertGreater(pts[beta_nt_idx]["drift"], 0.0)
        self.assertGreater(lm["metrics"]["drift"]["dom1k_nn1_diff_folder_pct"], 0.0)

        # Verify PNG is valid 512x512 RGB
        with open(out_png, "rb") as f:
            png = f.read()
        self.assertEqual(png[:8], b"\x89PNG\r\n\x1a\n")
        w, h, bd, ct = struct.unpack(">IIBB", png[16:26])
        self.assertEqual((w, h, bd, ct), (512, 512, 8, 2))
        pos = 8
        idats = []
        while pos < len(png):
            clen, ctag = struct.unpack(">I4s", png[pos : pos + 8])
            if ctag == b"IDAT":
                idats.append(png[pos + 8 : pos + 8 + clen])
            elif ctag == b"IEND":
                break
            pos += 12 + clen
        raw = zlib.decompress(b"".join(idats))
        self.assertEqual(len(raw), 512 * (1 + 512 * 3))

    def test_determinism_and_small_no_dom_fallback(self) -> None:
        d1 = embedding.run_embedding(self.kdb_path, leanre_db_path=None, seed=42)
        d2 = embedding.run_embedding(self.kdb_path, leanre_db_path=None, seed=42)
        d1.pop("runtime_sec", None)
        d2.pop("runtime_sec", None)
        self.assertEqual(d1, d2)

        # Strip `dom` table to verify graceful fallback
        nodom_db = os.path.join(self.tmpdir.name, "nodom.db")
        with open(self.kdb_path, "rb") as src_f, open(nodom_db, "wb") as dst_f:
            dst_f.write(src_f.read())
        con = sqlite3.connect(nodom_db)
        con.execute("DROP TABLE dom")
        con.commit()
        con.close()
        d_nd = embedding.run_embedding(nodom_db, seed=42)
        self.assertGreater(d_nd["layers"]["landmarks"]["count"], 0)
        self.assertGreater(d_nd["layers"]["clusters_141"]["count"], 0)

    def test_math_primitives_edge_cases(self) -> None:
        X = np.eye(6, dtype=np.float64)
        U, S, Vt = embedding.randomized_svd(X, k=24, seed=42)
        self.assertEqual(U.shape, (6, 6))
        self.assertEqual(S.shape, (6,))
        self.assertEqual(Vt.shape, (6, 6))
        empty_u, empty_s, _ = embedding.randomized_svd(np.zeros((0, 4)), k=24)
        self.assertEqual(empty_u.shape, (0, 0))
        self.assertEqual(empty_s.shape, (0,))

    def test_emitted_embedding_hygiene_if_present(self) -> None:
        repo_emb = os.path.join(embedding._REPO_ROOT, "outputs", "embedding_2d.json")
        if not os.path.isfile(repo_emb):
            return
        sz = os.path.getsize(repo_emb)
        self.assertLessEqual(sz, 650 * 1024, f"embedding_2d.json ({sz} B) exceeds 650 KB cap")
        with open(repo_emb, "r", encoding="utf-8") as f:
            txt = f.read()
        self.assertNotIn("/usr/local/", txt)
        self.assertNotIn("/home/", txt)
        self.assertNotIn("/Users/", txt)
        parsed = json.loads(txt)
        self.assertEqual(parsed["schema"], embedding.SCHEMA_VERSION)
        self.assertIn("clusters_141", parsed["layers"])
        self.assertIn("landmarks", parsed["layers"])


if __name__ == "__main__":
    unittest.main()
