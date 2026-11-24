#!/usr/bin/env python3
"""Tests for leanre/annot.py -- gates A1 (anchoring), A2 (canonical round trip + schema), A3 (layers,
drafts, conflicts).  Run:  python3 -m unittest discover -s leanre -p 'test_annot.py' -v

All graphs in this file are tiny SYNTHETIC fixtures (hand-written names and type strings), not
telemetry extracted from the proof.  ``_sig`` is a stand-in signature hash used only where the test
is about annot.py's own logic; ``RealSighashTests`` exercises the real leanre/sighash.py."""
from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
import random
import shutil
import sys
import tempfile
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import annot  # noqa: E402

T0 = "2026-11-22T03:00:00Z"
T1 = "2026-11-22T04:00:00Z"
T2 = "2026-11-22T05:00:00Z"
REPO_ANNOTATIONS = os.path.join(os.path.dirname(_HERE), "annotations")


def _sig(type_text: str, scheme: str = "t1n") -> str:
    """Stand-in signature hash: depends on the TYPE text only (never on name or proof body)."""
    return scheme + ":" + hashlib.sha256(" ".join(type_text.split()).encode()).hexdigest()[:32]


def _pack() -> annot.Pack:
    p = annot.Pack()
    p.add_layer("human/notes", "human", "Human notes")
    p.add_layer("ai/flirt-tier3", "ai-draft", "FLIRT Tier 3 drafts")
    return p


def _human(name: str, **kw) -> dict:
    base = dict(name=name, layer="human/notes", tag="L", source="synthetic fixture", author="tester", now=T0,
                note="note on " + name)
    base.update(kw)
    return annot.make_annotation(**base)


def _draft(name: str, **kw) -> dict:
    base = dict(name=name, layer="ai/flirt-tier3", tag="M", source="tier3 pilot (synthetic fixture)",
                author="ai:test-model", now=T0, rename="guessed_" + name.replace(".", "_"),
                breaks="label guessed from types only", draft=True)
    base.update(kw)
    return annot.make_annotation(**base)


def _codes(issues) -> set:
    return {i["code"] for i in issues}


def _lines(*objs) -> str:
    return "".join(annot.canonical_json(o) + "\n" for o in objs)


HDR = {"type": "pack", "schema": annot.SCHEMA}
LAYER_H = {"type": "layer", "layer": "human/notes", "kind": "human", "default_on": True, "title": "Human notes"}
LAYER_AI = {"type": "layer", "layer": "ai/drafts", "kind": "ai-draft", "default_on": False, "title": "Drafts"}
REC = {"type": "annot", "target": "decl", "name": "Foo.bar", "layer": "human/notes", "tag": "L",
       "source": "synthetic fixture", "author": "tester", "created": T0, "updated": T0, "note": "n"}


# ================================================================================================
# A1 -- key = declaration name + normalized signature hash
# ================================================================================================

class AnchoringTests(unittest.TestCase):
    """Synthetic graph v1 -> v2.  A graph is {decl name: (type text, proof text)}."""

    V1 = {
        "Proj.keep": ("∀ n : Nat, n + 0 = n", "by simp"),
        "Proj.old_name": ("∀ a b : Nat, a + b = b + a", "by omega"),
        "Proj.restated": ("∀ n : Nat, 0 ≤ n", "by simp"),
        "Proj.deleted": ("∀ n : Nat, n * 1 = n", "by simp"),
        "Proj.twin": ("True ∧ True", "⟨trivial, trivial⟩"),
    }
    V2 = {
        "Proj.keep": ("∀ n : Nat, n + 0 = n", "by induction n <;> simp_all"),   # proof body changed
        "Proj.new_name": ("∀ a b : Nat, a + b = b + a", "by omega"),            # renamed, same signature
        "Proj.restated": ("∀ n : Nat, 0 ≤ n + 1", "by simp"),                   # signature changed
        "Proj.twin_a": ("True ∧ True", "⟨trivial, trivial⟩"),                   # renamed, but ...
        "Proj.twin_b": ("True ∧ True", "⟨trivial, trivial⟩"),                   # ... hash is not unique
    }

    @staticmethod
    def graph(g) -> annot.GraphIndex:
        return annot.GraphIndex({n: _sig(t) for n, (t, _proof) in g.items()}, label="synthetic")

    def pack_on_v1(self) -> annot.Pack:
        p = _pack()
        for name, (t, _proof) in self.V1.items():
            p.put(_human(name, sighash=_sig(t), rename="nice_" + name.split(".")[-1]))
        return p

    def by_name(self, rep) -> dict:
        return {e["name"]: e for e in rep["entries"]}

    def test_all_exact_on_the_graph_it_was_written_against(self):
        rep = annot.reanchor(self.pack_on_v1(), self.graph(self.V1))
        self.assertEqual(rep["counts"], {"exact": 5, "name_only": 0, "hash_only": 0, "orphan": 0, "unchecked": 0})

    def test_survives_proof_body_change(self):
        self.assertNotEqual(self.V1["Proj.keep"][1], self.V2["Proj.keep"][1])
        e = self.by_name(annot.reanchor(self.pack_on_v1(), self.graph(self.V2)))["Proj.keep"]
        self.assertEqual(e["status"], "exact")

    def test_rename_with_unchanged_signature_re_resolves(self):
        p = self.pack_on_v1()
        rep = annot.reanchor(p, self.graph(self.V2))
        e = self.by_name(rep)["Proj.old_name"]
        self.assertEqual((e["status"], e["unique"], e["resolved_name"]), ("hash_only", True, "Proj.new_name"))
        rb = annot.rebind(p, rep, now=T1)
        moved = {m["name"] for m in rb["moved"]}
        self.assertEqual(moved, {"Proj.new_name"})
        new = [r for r in rb["pack"].annots.values() if r["name"] == "Proj.new_name"]
        self.assertEqual(len(new), 1)
        self.assertEqual(new[0]["was"], ["Proj.old_name"])
        self.assertEqual(new[0]["note"], "note on Proj.old_name")          # payload carried over intact
        self.assertEqual(new[0]["rename"], "nice_old_name")
        self.assertEqual(new[0]["sighash"], _sig(self.V1["Proj.old_name"][0]))
        self.assertEqual((new[0]["created"], new[0]["updated"]), (T0, T1))
        # after rebinding it is an exact hit, and the overlay shows it under the new name
        again = self.by_name(annot.reanchor(rb["pack"], self.graph(self.V2)))
        self.assertEqual(again["Proj.new_name"]["status"], "exact")
        self.assertIn("decl:Proj.new_name", annot.view(rb["pack"])["targets"])
        self.assertEqual(p, self.pack_on_v1())                               # input pack untouched

    def test_full_report_classes(self):
        rep = annot.reanchor(self.pack_on_v1(), self.graph(self.V2))
        e = self.by_name(rep)
        self.assertEqual(rep["counts"], {"exact": 1, "name_only": 1, "hash_only": 2, "orphan": 1, "unchecked": 0})
        self.assertEqual((e["Proj.restated"]["status"], e["Proj.restated"]["reason"]), ("name_only", "signature_changed"))
        self.assertEqual(e["Proj.deleted"]["status"], "orphan")
        twin = e["Proj.twin"]
        self.assertEqual((twin["status"], twin["unique"], twin["candidates"]),
                         ("hash_only", False, ["Proj.twin_a", "Proj.twin_b"]))
        self.assertNotIn("resolved_name", twin)

    def test_rebind_never_guesses(self):
        p = self.pack_on_v1()
        rep = annot.reanchor(p, self.graph(self.V2))
        rb = annot.rebind(p, rep, now=T1)
        skipped = {(s["status"], s["reason"]) for s in rb["skipped"]}
        self.assertEqual(skipped, {("name_only", "signature_changed"), ("hash_only", "ambiguous"),
                                   ("orphan", "name_and_hash_not_found")})
        names = {r["name"] for r in rb["pack"].annots.values()}
        self.assertEqual(names, {"Proj.keep", "Proj.new_name", "Proj.restated", "Proj.deleted", "Proj.twin"})
        # a changed statement is only re-keyed on explicit request
        rb2 = annot.rebind(p, rep, now=T1, accept_signature_change=True)
        r = [x for x in rb2["pack"].annots.values() if x["name"] == "Proj.restated"][0]
        self.assertEqual(r["sighash"], _sig(self.V2["Proj.restated"][0]))

    def test_rebind_key_collision_is_reported_not_overwritten(self):
        p = self.pack_on_v1()
        p.put(_human("Proj.new_name", sighash=_sig(self.V1["Proj.old_name"][0]), note="already here"))
        rb = annot.rebind(p, annot.reanchor(p, self.graph(self.V2)), now=T1)
        self.assertEqual([c["kind"] for c in rb["conflicts"]], ["key_collision"])
        kept = [r for r in rb["pack"].annots.values() if r["name"] == "Proj.new_name"]
        self.assertEqual([r["note"] for r in kept], ["already here"])
        self.assertTrue(any(r["name"] == "Proj.old_name" for r in rb["pack"].annots.values()))

    def test_unhashed_annotation_is_name_only_and_can_be_filled(self):
        p = _pack()
        p.put(_human("Proj.keep"))
        g = annot.GraphIndex([("Proj.keep", ("k1n:" + "1" * 32, "k1a:" + "2" * 32))])
        rep = annot.reanchor(p, g)
        self.assertEqual((rep["entries"][0]["status"], rep["entries"][0]["reason"]), ("name_only", "unhashed_annotation"))
        rb = annot.rebind(p, rep, now=T1)
        r = list(rb["pack"].annots.values())[0]
        self.assertEqual((r["sighash"], r["alt_sighash"]), ("k1n:" + "1" * 32, ["k1a:" + "2" * 32]))
        self.assertEqual(annot.reanchor(rb["pack"], g)["counts"]["exact"], 1)

    def test_schemes_are_never_compared_across(self):
        k, s = "k1n:" + "a" * 32, "s1n:" + "a" * 32          # same hex, different scheme
        p = _pack()
        p.put(_human("X.y", sighash=k))
        e = annot.reanchor(p, annot.GraphIndex({"X.y": s}))["entries"][0]
        self.assertEqual((e["status"], e["reason"]), ("name_only", "no_common_scheme"))
        e = annot.reanchor(p, annot.GraphIndex({"Z.w": s}))["entries"][0]
        self.assertEqual(e["status"], "orphan")
        # alt hash of the graph's scheme confirms the anchor when the primary's scheme is absent
        q = _pack()
        q.put(_human("X.y", sighash=k, alt_sighash=[s]))
        e = annot.reanchor(q, annot.GraphIndex({"X.y": s}))["entries"][0]
        self.assertEqual((e["status"], e["via_primary"]), ("exact", False))

    def test_alt_hash_rename_needs_opt_in(self):
        k, a = "k1n:" + "a" * 32, "k1a:" + "b" * 32
        p = _pack()
        p.put(_human("Old.n", sighash=k, alt_sighash=[a]))
        rep = annot.reanchor(p, annot.GraphIndex([("New.n", ("k1n:" + "c" * 32, a))]))
        e = rep["entries"][0]
        self.assertEqual((e["status"], e["via"], e["via_primary"]), ("hash_only", a, False))
        self.assertEqual(annot.rebind(p, rep, now=T1)["moved"], [])
        self.assertEqual(len(annot.rebind(p, rep, now=T1, accept_alt_hash=True)["moved"]), 1)

    def test_non_decl_targets(self):
        p = _pack()
        p.put(_human("Main", target="module"))
        p.put(_human("Gone.Mod", target="module"))
        p.put(_human("Some.Ns", target="namespace"))
        rep = annot.reanchor(p, annot.GraphIndex({}, names={"module": ["Main"]}))
        st = {e["name"]: (e["status"], e["reason"]) for e in rep["entries"]}
        self.assertEqual(st, {"Main": ("name_only", "non_decl_target"), "Gone.Mod": ("orphan", "name_not_found"),
                              "Some.Ns": ("unchecked", "no_namespace_table")})
        with self.assertRaises(annot.PackError):
            p.put(_human("Main", target="module", sighash="k1n:" + "a" * 32, slot="x"))

    def test_restricted_index_gives_same_report(self):
        p = self.pack_on_v1()
        rows = [(n, _sig(t)) for n, (t, _) in self.V2.items()] + [(f"Noise.n{i}", _sig(f"T{i}")) for i in range(500)]
        full = annot.reanchor(p, annot.GraphIndex(rows))
        lean = annot.GraphIndex(iter(rows), restrict_to=p)
        self.assertLess(len(lean.hashes_of), 10)
        self.assertEqual(annot.reanchor(p, lean)["entries"], full["entries"])

    def test_sqlite_and_tsv_sources(self):
        import sqlite3
        d = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, d)
        db = os.path.join(d, "kernel.db")
        conn = sqlite3.connect(db)
        conn.execute("CREATE TABLE consts(name PRIMARY KEY, decl_id, ckind, sighash, sighash_anon)")
        for n, (t, _) in self.V2.items():
            conn.execute("INSERT INTO consts VALUES (?,?,?,?,?)", (n, 0, "thm", _sig(t), _sig(t, "t1a")))
        conn.commit()
        conn.close()
        p = self.pack_on_v1()
        want = annot.reanchor(p, self.graph(self.V2))["counts"]
        self.assertEqual(annot.reanchor(p, annot.GraphIndex.from_kernel_db(db, restrict_to=p))["counts"], want)
        with self.assertRaises(ValueError):
            annot.GraphIndex.from_sqlite(db, "DELETE FROM consts")
        with self.assertRaises(ValueError):
            annot.GraphIndex.from_sqlite(db, "SELECT name, sighash FROM consts; DROP TABLE consts")
        tsv = os.path.join(d, "g.tsv")
        with open(tsv, "w", encoding="utf-8") as f:
            f.write("# name\thash\n" + "".join(f"{n}\t{_sig(t)}\n" for n, (t, _) in self.V2.items()))
        self.assertEqual(annot.reanchor(p, annot.GraphIndex.from_tsv(tsv))["counts"], want)


class RealSighashTests(unittest.TestCase):
    """A1 against the real spec (leanre/sighash.py, docs/SIGHASH.md), source form `s1n`.

    The declarations are hand-written toy Lean headers (SYNTHETIC, not from the proof archive)."""

    V1 = [
        "theorem Toy.add_zero' (n : Nat) : n + 0 = n := by simp",
        "theorem Toy.comm_old {a b : Nat} : a + b = b + a := by omega",
        "theorem Toy.restated (n : Nat) : 0 ≤ n := by simp",
    ]
    V2 = [
        # proof body replaced AND binder alpha-renamed + reformatted: same normalized signature
        "theorem Toy.add_zero' (m : Nat) :\n    m + 0 = m := by\n  induction m with\n  | zero => rfl\n  | succ k ih => simp",
        "theorem Toy.comm_new {a b : Nat} : a + b = b + a := by omega",      # renamed only
        "theorem Toy.restated (n : Nat) : 0 ≤ n + 1 := by simp",             # statement changed
    ]

    def setUp(self):
        try:
            import sighash
        except ImportError:
            self.skipTest("leanre/sighash.py not present")
        self.sighash = sighash

    def graph(self, headers) -> dict:
        out = {}
        for h in headers:
            r = self.sighash.source_hash_header(h)
            self.assertIsNotNone(r, h)
            self.assertRegex(r["s1n"], annot.SIGHASH_RE)
            out[r["name"]] = (r["s1n"], r["s1a"])
        return out

    def test_real_hash_strings_are_accepted_as_keys(self):
        for name, (s1n, s1a) in self.graph(self.V1).items():
            p = _pack()
            rec = p.put(_human(name, sighash=s1n, alt_sighash=[s1a]))
            self.assertEqual(annot.loads(annot.dumps(p)).annots[annot.record_key(rec)], rec)

    def test_annotations_survive_proof_change_and_rename_under_real_sighash(self):
        g1, g2 = self.graph(self.V1), self.graph(self.V2)
        self.assertEqual(sorted(g1), ["Toy.add_zero'", "Toy.comm_old", "Toy.restated"])
        p = _pack()
        for name, (s1n, _s1a) in g1.items():
            p.put(_human(name, sighash=s1n))
        self.assertEqual(annot.reanchor(p, annot.GraphIndex(g1))["counts"]["exact"], 3)
        rep = annot.reanchor(p, annot.GraphIndex(g2))
        st = {e["name"]: e for e in rep["entries"]}
        self.assertEqual(st["Toy.add_zero'"]["status"], "exact")                       # proof body changed
        self.assertEqual((st["Toy.comm_old"]["status"], st["Toy.comm_old"].get("resolved_name")),
                         ("hash_only", "Toy.comm_new"))                                # rename re-resolves
        self.assertEqual((st["Toy.restated"]["status"], st["Toy.restated"]["reason"]),
                         ("name_only", "signature_changed"))                           # and only then
        rb = annot.rebind(p, rep, now=T1)
        self.assertEqual([(m["name"], m["status"]) for m in rb["moved"]], [("Toy.comm_new", "hash_only")])
        self.assertEqual(annot.reanchor(rb["pack"], annot.GraphIndex(g2))["counts"],
                         {"exact": 2, "name_only": 1, "hash_only": 0, "orphan": 0, "unchecked": 0})


class RealKernelGraphTests(unittest.TestCase):
    """A1 on real data: kernel hashes (`k1n`) of the pinned challenge export, [L]
    data/challenge.ndjson.zst SHA-256 c24ef99d...8ac6.  Skipped when the export or sighash is absent.
    Opt-in (the hashing pass takes ~35 s):  LEANRE_ANNOT_REAL=1 python3 -m unittest ..."""

    NAMES = ("riemannHypothesis", "riemannZeta_eq_zero_re", "sorryAx")
    _rows = None

    @classmethod
    def rows(cls):
        if cls._rows is None:
            import sighash
            path = os.path.join(os.path.dirname(_HERE), "data", "challenge.ndjson.zst")
            cls._rows = [(r["name"], "k1n:" + r["k1n"].hex(), "k1a:" + r["k1a"].hex())
                         for r in sighash.kernel_sighashes(path)]
        return cls._rows

    def setUp(self):
        path = os.path.join(os.path.dirname(_HERE), "data", "challenge.ndjson.zst")
        if not os.environ.get("LEANRE_ANNOT_REAL"):
            self.skipTest("opt-in real-data test: set LEANRE_ANNOT_REAL=1")
        if not os.path.exists(path):
            self.skipTest("data/challenge.ndjson.zst not available")
        try:
            import sighash  # noqa: F401
        except ImportError:
            self.skipTest("leanre/sighash.py not present")

    def test_seed_pack_binds_and_reanchors_on_the_real_kernel_graph(self):
        rows = self.rows()
        pack, issues = annot.PackStore(REPO_ANNOTATIONS).load()
        self.assertEqual(issues, [])
        pack = pack.subset([l for l in pack.layers if pack.layers[l]["kind"] == "human"])
        g = annot.GraphIndex(rows, restrict_to=pack, label="challenge.ndjson.zst")
        rep = annot.reanchor(pack, g)
        st = {e["name"]: e["status"] for e in rep["entries"] if e["target"] == "decl"}
        for n in self.NAMES:
            self.assertEqual(st[n], "exact", n)                  # seed decls carry frozen k1n hashes
        by_name = {r["name"]: r for r in pack.annots.values() if r["target"] == "decl"}
        for n in self.NAMES:
            self.assertRegex(by_name[n]["sighash"], r"^k1n:[0-9a-f]{32}$")
        # Rename experiment on the real hashes: rename one constant in the graph, keep its signature.
        renamed = [("Renamed.rh" if n == "riemannHypothesis" else n, a, b) for n, a, b in rows]
        g2 = annot.GraphIndex(renamed, restrict_to=pack)
        e = [x for x in annot.reanchor(pack, g2)["entries"] if x["name"] == "riemannHypothesis"][0]
        self.assertEqual(e["status"], "hash_only")
        self.assertIn("Renamed.rh", e["candidates"])
        self.assertEqual(e["candidate_count"], sum(1 for _n, a, _b in rows if a == by_name["riemannHypothesis"]["sighash"]))


class RealKernelDbTests(unittest.TestCase):
    """A1 on real Phase 3 DBs: challenge-derived seed k1n hashes re-anchored against the full
    solution export in outputs/kernel/kernel.db (+ outputs/leanre.db).  Skipped if DBs are absent."""

    def setUp(self):
        repo = os.path.dirname(_HERE)
        self.kdb = os.path.join(repo, "outputs", "kernel", "kernel.db")
        self.ldb = os.path.join(repo, "outputs", "leanre.db")
        if not os.path.exists(self.kdb):
            self.skipTest("outputs/kernel/kernel.db not present")

    def test_challenge_seed_reanchors_on_full_solution_kernel_db(self):
        pack, issues = annot.PackStore(REPO_ANNOTATIONS).load()
        self.assertEqual(issues, [])
        ldb = self.ldb if os.path.exists(self.ldb) else None
        g = annot.GraphIndex.from_kernel_db(self.kdb, restrict_to=pack, leanre_db=ldb)
        rep = annot.reanchor(pack, g)
        seed = {e["name"]: e for e in rep["entries"] if e["layer"] == "human/canonical-facts"}
        # Proof bodies changed from sorryAx stubs (challenge) to full proofs (solution): exact hits.
        self.assertEqual(seed["riemannHypothesis"]["status"], "exact")
        self.assertEqual(seed["riemannZeta_eq_zero_re"]["status"], "exact")
        # sorryAx is absent from solution.ndjson.zst: reported as orphan, never silently dropped.
        self.assertEqual(seed["sorryAx"]["status"], "orphan")
        if ldb:
            self.assertEqual(seed["Main"]["status"], "name_only")
            self.assertEqual(seed["Development.AbelianVarietyTheory"]["status"], "name_only")
            self.assertEqual(rep["counts"]["unchecked"], 0)
        # Every AI-draft Phase 4 decompilation landmark (when present) must anchor 100% exact.
        p4 = [e for e in rep["entries"] if e["layer"] == "ai/decomp-phase4"]
        if p4:
            self.assertTrue(all(e["status"] == "exact" for e in p4),
                            [e for e in p4 if e["status"] != "exact"][:5])

    def test_rename_re_resolves_against_real_solution_kernel_db(self):
        # Challenge k1n hashes under simulated old names, re-anchored against full solution kernel.db:
        # - riemannZeta_eq_zero_re has a unique k1n across all 1.48M consts -> auto-rebinds cleanly.
        # - riemannHypothesis shares its k1n with rhOfAll -> reported ambiguous, never guessed.
        p = _pack()
        p.put(_human("Simulated.old_zeta_re", sighash="k1n:407e56a49b1c5d53ff3748d49d502ad6", rename="Zeta RH (2)"))
        p.put(_human("Simulated.old_rh_name", sighash="k1n:e67d3cf7e6fa39c3480c359052fb059f", rename="Zeta RH (1)"))
        g = annot.GraphIndex.from_kernel_db(self.kdb, restrict_to=p)
        rep = annot.reanchor(p, g)
        by_name = {e["name"]: e for e in rep["entries"]}
        z = by_name["Simulated.old_zeta_re"]
        self.assertEqual((z["status"], z["unique"], z["resolved_name"]), ("hash_only", True, "riemannZeta_eq_zero_re"))
        r = by_name["Simulated.old_rh_name"]
        self.assertEqual((r["status"], r["unique"], r["candidates"]), ("hash_only", False, ["rhOfAll", "riemannHypothesis"]))
        rb = annot.rebind(p, rep, now=T1)
        self.assertEqual([m["name"] for m in rb["moved"]], ["riemannZeta_eq_zero_re"])
        self.assertEqual([(s["status"], s["reason"]) for s in rb["skipped"]], [("hash_only", "ambiguous")])
        g2 = annot.GraphIndex.from_kernel_db(self.kdb, restrict_to=rb["pack"])
        self.assertEqual(annot.reanchor(rb["pack"], g2)["counts"],
                         {"exact": 1, "name_only": 0, "hash_only": 1, "orphan": 0, "unchecked": 0})


# ================================================================================================
# A2 -- canonical bytes, round trip, schema validation
# ================================================================================================

def _random_pack(rng: random.Random, n: int = 60) -> annot.Pack:
    p = _pack()
    p.add_layer("human/zeta", "human", "Zêta ζ notes", description="second human layer", default_on=False)
    alphabet = ["Foo", "bar", "ζ", "Baz'", "x₁", "«odd name»", "q\"uote", "back\\slash", "ℕ", "a.b"]
    for i in range(n):
        name = ".".join(rng.choice(alphabet) for _ in range(rng.randint(1, 4)))
        if rng.random() < 0.3:
            rec = _draft(name, sighash=_sig(name) if rng.random() < 0.7 else None,
                         extra={"confidence": rng.random(), "cluster": i, "blinded": True, "nested": {"z": [1, 2.5, None]}})
        else:
            tag = rng.choice(annot.TAGS)
            rec = _human(name, layer=rng.choice(["human/notes", "human/zeta"]), tag=tag,
                         breaks="breaks here" if tag == "M" else None,
                         sighash=_sig(name) if rng.random() < 0.7 else None,
                         alt_sighash=[_sig(name, "t1a")] if rng.random() < 0.3 else None,
                         slot=rng.choice([None, "math", "re"]),
                         rename=rng.choice([None, "renamed " + name]),
                         aliases=rng.choice([None, ["b", "a", "a"]]),
                         note=rng.choice(["line1\nline2 — tab\there", "ünïcödé ∀ε>0 \U0001d53d", "plain"]))
            if "sighash" not in rec:
                rec.pop("alt_sighash", None)
        try:
            p.put(rec)
        except annot.ConflictError:
            pass
    return p


class RoundTripTests(unittest.TestCase):
    def test_export_import_export_is_byte_identical(self):
        for seed in range(25):
            p = _random_pack(random.Random(seed))
            text1 = annot.dumps(p)
            q = annot.loads(text1)
            text2 = annot.dumps(q)
            self.assertEqual(text1.encode("utf-8"), text2.encode("utf-8"))
            self.assertEqual(p, q)
            self.assertEqual(annot.validate_text(text1), [])

    def test_file_round_trip_is_byte_identical(self):
        d = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, d)
        p = _random_pack(random.Random(99))
        a, b = os.path.join(d, "a.jsonl"), os.path.join(d, "b.jsonl")
        annot.dump(p, a)
        annot.dump(annot.load(a), b)
        with open(a, "rb") as fa, open(b, "rb") as fb:
            raw = fa.read()
            self.assertEqual(raw, fb.read())
        self.assertTrue(raw.endswith(b"\n") and b"\r" not in raw and not raw.startswith(b"\xef\xbb\xbf"))

    def test_export_is_independent_of_insertion_order(self):
        p = _random_pack(random.Random(7))
        q = annot.Pack()
        for lid in sorted(p.layers, reverse=True):
            q.layers[lid] = dict(reversed(list(p.layers[lid].items())))
        keys = list(p.annots)
        random.Random(1).shuffle(keys)
        for k in keys:
            q.annots[k] = dict(reversed(list(p.annots[k].items())))
        self.assertEqual(annot.dumps(p), annot.dumps(q))

    def test_shape_one_sorted_object_per_line(self):
        text = annot.dumps(_random_pack(random.Random(3)))
        lines = text.split("\n")
        self.assertEqual(lines[-1], "")
        lines = lines[:-1]
        objs = [json.loads(l) for l in lines]
        self.assertTrue(all(isinstance(o, dict) for o in objs))
        self.assertEqual(objs[0], {"type": "pack", "schema": "leanre.annot/1"})
        kinds = [o["type"] for o in objs]
        n_layers = kinds.count("layer")
        self.assertEqual(kinds, ["pack"] + ["layer"] * n_layers + ["annot"] * (len(objs) - 1 - n_layers))
        layer_ids = [o["layer"] for o in objs if o["type"] == "layer"]
        self.assertEqual(layer_ids, sorted(layer_ids))
        keys = [(o["target"], o["name"], o.get("sighash", ""), o["layer"], o.get("slot", "")) for o in objs[1 + n_layers:]]
        self.assertEqual(keys, sorted(keys))
        self.assertEqual(len(keys), len(set(keys)))
        for l, o in zip(lines, objs):   # each line is the canonical encoding of its object
            self.assertEqual(l, json.dumps(o, sort_keys=True, ensure_ascii=False, separators=(",", ":")))
        for o in objs[1 + n_layers:]:   # mandatory provenance + author + layer on every record
            self.assertIn(o["tag"], ("L", "A", "C", "S", "M"))
            self.assertTrue(o["source"] and o["author"] and o["layer"] and o["created"] and o["updated"])

    def test_hand_formatted_pack_imports_and_normalizes(self):
        p = _random_pack(random.Random(5), n=20)
        canon = annot.dumps(p)
        lines = canon.rstrip("\n").split("\n")
        body = lines[1:]
        random.Random(2).shuffle(body)
        messy = "\n".join([lines[0]] + [json.dumps(json.loads(l), indent=None, ensure_ascii=True) for l in body]) + "\n"
        self.assertNotEqual(messy, canon)
        self.assertEqual(annot.validate_text(messy, canonical=False), [])              # schema-valid
        self.assertEqual(_codes(annot.validate_text(messy)), {"noncanonical"})         # but not canonical bytes
        self.assertEqual(annot.dumps(annot.loads(messy)), canon)

    def test_empty_optionals_have_one_representation(self):
        a = dict(REC, aliases=[], rename="", slot=None, extra={}, draft=False)
        self.assertEqual(annot.dumps(annot.loads(_lines(HDR, LAYER_H, a))), _lines(HDR, LAYER_H, REC))


class ValidationTests(unittest.TestCase):
    def check(self, *objs, text=None) -> set:
        return _codes(annot.validate_text(_lines(*objs) if text is None else text))

    def test_minimal_valid(self):
        self.assertEqual(self.check(HDR, LAYER_H, REC), set())

    def test_mandatory_fields(self):
        for f in ("tag", "source", "author", "layer", "name", "created", "updated"):
            rec = {k: v for k, v in REC.items() if k != f}
            self.assertIn("missing_" + f, self.check(HDR, LAYER_H, rec), f)
            with self.assertRaises(annot.PackError):
                annot.loads(_lines(HDR, LAYER_H, rec))
        self.assertIn("bad_source", self.check(HDR, LAYER_H, dict(REC, source="")))
        self.assertIn("bad_author", self.check(HDR, LAYER_H, dict(REC, author="  ")))

    def test_provenance_tag_rules(self):
        for bad in ("X", "[L]", "l", "", None, 1):
            self.assertIn("bad_tag", self.check(HDR, LAYER_H, dict(REC, tag=bad)), repr(bad))
        for tag in ("L", "A", "C", "S"):
            self.assertEqual(self.check(HDR, LAYER_H, dict(REC, tag=tag)), set())
            self.assertIn("unexpected_breaks", self.check(HDR, LAYER_H, dict(REC, tag=tag, breaks="x")))
        self.assertIn("missing_breaks", self.check(HDR, LAYER_H, dict(REC, tag="M")))
        self.assertEqual(self.check(HDR, LAYER_H, dict(REC, tag="M", breaks="no Frobenius over Q")), set())

    def test_record_shape_errors(self):
        cases = {
            "unknown_field": dict(REC, colour="red"),
            "bad_target": dict(REC, target="file"),
            "bad_sighash": dict(REC, sighash="deadbeef"),
            "bad_alt_sighash": dict(REC, alt_sighash=["k1a:" + "a" * 32]),
            "bad_slot": dict(REC, slot="Bad Slot"),
            "bad_created": dict(REC, created="2026-11-22 03:00:00"),
            "bad_updated": dict(REC, updated="2026-11-21T03:00:00Z"),
            "empty_annotation": {k: v for k, v in REC.items() if k != "note"},
            "too_long": dict(REC, note="x" * (annot.MAX_NOTE + 1)),
            "bad_chars": dict(REC, name="Foo\nbar"),
            "bad_aliases": dict(REC, aliases="a"),
            "bad_extra": dict(REC, extra=[1]),
            "undeclared_layer": dict(REC, layer="human/other"),
            "bad_layer": dict(REC, layer="../etc"),
        }
        for code, rec in cases.items():
            self.assertIn(code, self.check(HDR, LAYER_H, rec), code)

    def test_file_shape_errors(self):
        good = _lines(HDR, LAYER_H, REC)
        self.assertIn("missing_header", self.check(LAYER_H, REC))
        self.assertIn("bad_schema", self.check({"type": "pack", "schema": "leanre.annot/2"}, LAYER_H, REC))
        self.assertIn("header_not_first", self.check(LAYER_H, HDR, REC))
        self.assertIn("bad_type", self.check(HDR, LAYER_H, {"type": "comment"}))
        self.assertIn("bad_json", self.check(text=good + "{not json}\n"))
        self.assertIn("bad_json", self.check(text=good + "[1,2]\n"))
        self.assertIn("bad_json", self.check(text=good.replace('"note":"n"', '"note":"n","note":"m"')))
        self.assertIn("bad_json", self.check(text=_lines(HDR, LAYER_H).rstrip("\n") + "\n"
                                             + annot.canonical_json(REC)[:-1] + ',"extra":{"x":NaN}}\n'))
        self.assertIn("blank_line", self.check(text=good + "\n"))
        self.assertIn("carriage_return", self.check(text=good.replace("\n", "\r\n")))
        self.assertIn("bom", self.check(text="\ufeff" + good))
        self.assertIn("noncanonical", self.check(text=good.rstrip("\n")))
        self.assertIn("duplicate_key", self.check(HDR, LAYER_H, REC, REC))
        self.assertIn("conflict", self.check(HDR, LAYER_H, REC, dict(REC, note="other")))
        self.assertIn("layer_conflict", self.check(HDR, LAYER_H, dict(LAYER_H, title="Other"), REC))
        self.assertIn("bad_utf8", _codes(annot.validate_text(b"\xff\xfe")))

    def test_git_conflict_markers_are_reported(self):
        a, b = annot.canonical_json(REC), annot.canonical_json(dict(REC, note="theirs"))
        text = _lines(HDR, LAYER_H) + f"<<<<<<< HEAD\n{a}\n=======\n{b}\n>>>>>>> their-branch\n"
        issues = annot.validate_text(text)
        self.assertEqual(sum(i["code"] == "git_conflict_marker" for i in issues), 3)
        self.assertIn("conflict", _codes(issues))
        with self.assertRaises(annot.PackError):
            annot.loads(text)

    def test_issues_carry_line_numbers(self):
        issues = annot.validate_text(_lines(HDR, LAYER_H, REC, dict(REC, name="Zed", tag="Q")))
        self.assertEqual([(i["line"], i["code"]) for i in issues], [(4, "bad_tag")])


class SeedPackTests(unittest.TestCase):
    """The committed packs under annotations/ must be canonical, valid and guardrail-clean."""

    def test_committed_packs(self):
        store = annot.PackStore(REPO_ANNOTATIONS)
        files = store.files()
        self.assertTrue(files, "annotations/ has no packs")
        for path in files:
            with open(path, "rb") as f:
                raw = f.read()
            self.assertEqual(annot.validate_text(raw), [], path)
            self.assertEqual(annot.dumps(annot.loads(raw)).encode("utf-8"), raw, path)
        pack, issues = store.load()
        self.assertEqual(issues, [])
        self.assertGreater(len(pack), 0)
        for lid, layer in pack.layers.items():
            self.assertEqual(os.path.exists(os.path.join(REPO_ANNOTATIONS, annot.layer_filename(lid))), True)
        for rec in pack.annots.values():
            kind = pack.layers[rec["layer"]]["kind"]
            self.assertEqual(rec.get("draft", False), kind == "ai-draft")
            self.assertNotIn("automorphy lifting", json.dumps(rec).lower())   # HANDOFF §3 canonical fact

    def test_documented_example_is_a_valid_canonical_pack(self):
        doc = os.path.join(os.path.dirname(_HERE), "docs", "ANNOTATION_PACKS.md")
        with open(doc, encoding="utf-8") as f:
            text = f.read()
        block = text.split("```json\n", 1)[1].split("```", 1)[0]
        self.assertEqual(annot.validate_text(block), [])
        pack = annot.loads(block)
        self.assertEqual((len(pack.layers), len(pack), annot.default_layers(pack)), (2, 2, ["human/example"]))

    def test_ai_draft_layers_committed_are_off(self):
        pack, _ = annot.PackStore(REPO_ANNOTATIONS).load()
        on = annot.default_layers(pack)
        self.assertTrue(all(pack.layers[l]["kind"] == "human" for l in on))


# ================================================================================================
# A3 -- layers, drafts, conflicts
# ================================================================================================

class LayerTests(unittest.TestCase):
    def pack(self) -> annot.Pack:
        p = _pack()
        p.add_layer("human/second", "human", "Second human layer")
        p.put(_human("A.x", rename="alpha"))
        p.put(_human("B.y", layer="human/second", rename="beta"))
        p.put(_draft("A.x", rename="ai_alpha"))
        p.put(_draft("C.z", rename="ai_gamma"))
        return p

    def test_ai_draft_layers_are_off_by_default(self):
        p = self.pack()
        self.assertEqual(annot.default_layers(p), ["human/notes", "human/second"])
        v = annot.view(p)
        self.assertEqual(sorted(v["targets"]), ["decl:A.x", "decl:B.y"])
        self.assertFalse(any(a["draft"] for t in v["targets"].values() for a in t["annotations"]))
        self.assertEqual(v["targets"]["decl:A.x"]["rename"], "alpha")
        row = {r["layer"]: r for r in v["layers"]}["ai/flirt-tier3"]
        self.assertEqual((row["enabled"], row["draft"], row["default_on"], row["count"]), (False, True, False, 2))

    def test_ai_draft_layer_can_never_be_default_on(self):
        with self.assertRaises(annot.PackError):
            annot.Pack().add_layer("ai/x", "ai-draft", "x", default_on=True)
        bad = dict(LAYER_AI, default_on=True)
        self.assertIn("ai_draft_default_on", _codes(annot.validate_text(_lines(HDR, bad))))
        no_flag = {k: v for k, v in LAYER_AI.items() if k != "default_on"}
        self.assertEqual(annot.loads(_lines(HDR, no_flag)).layers["ai/drafts"]["default_on"], False)

    def test_layers_toggle_independently(self):
        p = self.pack()
        all_layers = sorted(p.layers)
        seen = {}
        for mask in range(1 << len(all_layers)):
            on = [l for i, l in enumerate(all_layers) if mask >> i & 1]
            v = annot.view(p, on)
            got = sorted((a["layer"], a["name"]) for t in v["targets"].values() for a in t["annotations"])
            want = sorted((r["layer"], r["name"]) for r in p.annots.values() if r["layer"] in on)
            self.assertEqual(got, want, on)
            self.assertEqual([r["layer"] for r in v["layers"] if r["enabled"]], on)
            seen[tuple(on)] = got
        self.assertEqual(len(seen), 8)
        self.assertEqual(annot.dumps(p), annot.dumps(self.pack()))      # toggling is a pure view

    def test_drafts_are_visibly_distinct_and_never_outrank_humans(self):
        p = self.pack()
        v = annot.view(p, ["ai/flirt-tier3", "human/notes"])           # even when listed first
        ax = v["targets"]["decl:A.x"]
        self.assertEqual((ax["rename"], ax["rename_draft"], ax["rename_layer"]), ("alpha", False, "human/notes"))
        self.assertEqual([a["draft"] for a in ax["annotations"]], [False, True])
        cz = v["targets"]["decl:C.z"]
        self.assertEqual((cz["rename"], cz["rename_draft"]), ("ai_gamma", True))
        for t in v["targets"].values():
            for a in t["annotations"]:
                self.assertEqual(a["draft"], a["layer"].startswith("ai/"))
                self.assertEqual(a["display_tag"], "[" + a["tag"] + "]")
                if a["draft"]:   # the mark is in the stored record too, not only in the view
                    self.assertTrue(p.get(a["id"])["draft"] is True and a["author"].startswith("ai:") and a["tag"] == "M")

    def test_ai_records_cannot_enter_human_layers_or_claim_facts(self):
        p = _pack()
        for bad, code in [
            (_human("A.x", author="ai:model"), "ai_author_in_human_layer"),
            (_human("A.x", draft=True), "draft_in_human_layer"),
            (_draft("A.x", draft=False), "draft_unmarked"),
            (_draft("A.x", author="some human"), "draft_author"),
            (_draft("A.x", tag="L", breaks=None), "draft_tag"),
            (_draft("A.x", tag="S", breaks=None), "draft_tag"),
            (_draft("A.x", breaks=None), "missing_breaks"),
        ]:
            with self.assertRaises(annot.PackError) as cm:
                p.put(bad)
            self.assertIn(code, _codes(cm.exception.issues), code)
        self.assertEqual(len(p), 0)
        draft_line = dict(REC, layer="ai/drafts", author="ai:m", tag="L", draft=True)
        self.assertIn("draft_tag", _codes(annot.validate_text(_lines(HDR, LAYER_AI, draft_line))))

    def test_rename_disagreement_between_enabled_layers_is_reported(self):
        p = self.pack()
        p.put(_human("A.x", layer="human/second", rename="aleph"))
        v = annot.view(p)
        ax = v["targets"]["decl:A.x"]
        self.assertTrue(ax["rename_conflict"])
        self.assertEqual(ax["rename"], "alpha")
        self.assertEqual([c["kind"] for c in v["conflicts"]], ["rename"])
        self.assertEqual(sorted(c["rename"] for c in v["conflicts"][0]["candidates"]), ["aleph", "alpha"])
        self.assertEqual(annot.view(p, ["human/second", "human/notes"])["targets"]["decl:A.x"]["rename"], "aleph")
        self.assertEqual(annot.view(p, ["human/notes"])["conflicts"], [])

    def test_unknown_layer_in_view(self):
        with self.assertRaises(annot.PackError):
            annot.view(self.pack(), ["nope"])

    def test_promote_copies_draft_into_human_layer(self):
        p = self.pack()
        rid = annot.record_id(_draft("C.z"))
        new = annot.promote(p, rid, "human/notes", author="reviewer", tag="C", source="reviewed by hand", now=T1)
        self.assertEqual((new["layer"], new["author"], new["tag"], new["rename"]), ("human/notes", "reviewer", "C", "ai_gamma"))
        self.assertNotIn("draft", new)
        self.assertEqual(new["extra"]["promoted_from"]["layer"], "ai/flirt-tier3")
        self.assertIsNotNone(p.get(rid))                                   # draft still there
        with self.assertRaises(annot.PackError):                           # an AI cannot promote itself
            annot.promote(p, annot.record_id(_draft("A.x")), "human/second", author="ai:m", tag="L", source="s", now=T1)


class MergeTests(unittest.TestCase):
    def two(self):
        ours, theirs = _pack(), _pack()
        ours.put(_human("Same.a"))
        theirs.put(_human("Same.a"))
        ours.put(_human("Clash.b", note="our reading"))
        theirs.put(_human("Clash.b", note="their reading", now=T1, created=T0))
        ours.put(_human("Time.c"))
        theirs.put(_human("Time.c", now=T1, created=T0))
        ours.put(_human("Only.ours"))
        theirs.put(_human("Only.theirs"))
        theirs.add_layer("human/extra", "human", "Extra")
        theirs.put(_human("Extra.e", layer="human/extra"))
        return ours, theirs

    def test_conflicts_are_reported_and_ours_is_kept(self):
        ours, theirs = self.two()
        before = annot.dumps(ours)
        m = annot.merge(ours, theirs)
        self.assertFalse(m["ok"])
        kinds = {c["key"][2]: (c["kind"], c["fields"]) for c in m["conflicts"]}
        self.assertEqual(kinds, {"Clash.b": ("content", ["note", "updated"]), "Time.c": ("timestamp_only", ["updated"])})
        c = [c for c in m["conflicts"] if c["key"][2] == "Clash.b"][0]
        self.assertEqual((c["ours"]["note"], c["theirs"]["note"]), ("our reading", "their reading"))
        merged = m["pack"]
        self.assertEqual(merged.annots[annot.record_key(_human("Clash.b"))]["note"], "our reading")
        self.assertEqual(len(m["added"]), 2)
        self.assertEqual(len(m["identical"]), 1)
        self.assertEqual(m["layers_added"], ["human/extra"])
        self.assertEqual(len(merged), 6)
        self.assertEqual(annot.dumps(ours), before)                         # inputs untouched

    def test_explicit_resolution(self):
        ours, theirs = self.two()
        ids = {c["key"][2]: c["id"] for c in annot.merge(ours, theirs)["conflicts"]}
        m = annot.merge(ours, theirs, {ids["Clash.b"]: "theirs", ids["Time.c"]: "ours"})
        self.assertTrue(m["ok"])
        self.assertEqual(m["pack"].annots[annot.record_key(_human("Clash.b"))]["note"], "their reading")
        self.assertEqual(m["pack"].annots[annot.record_key(_human("Time.c"))]["updated"], T0)
        self.assertEqual(sorted(r["choice"] for r in m["resolved"]), ["ours", "theirs"])
        with self.assertRaises(ValueError):
            annot.merge(ours, theirs, {ids["Clash.b"]: "newest"})

    def test_merge_is_idempotent_and_commutative_without_conflicts(self):
        a, b = _pack(), _pack()
        a.put(_human("A.a"))
        b.put(_human("B.b"))
        b.put(_draft("B.b"))
        ab, ba = annot.merge(a, b), annot.merge(b, a)
        self.assertTrue(ab["ok"] and ba["ok"])
        self.assertEqual(annot.dumps(ab["pack"]), annot.dumps(ba["pack"]))
        again = annot.merge(ab["pack"], b)
        self.assertEqual((again["added"], again["conflicts"]), ([], []))
        self.assertEqual(annot.dumps(again["pack"]), annot.dumps(ab["pack"]))

    def test_layer_kind_cannot_be_flipped_by_a_merge(self):
        ours = _pack()
        theirs = annot.Pack()
        theirs.add_layer("ai/flirt-tier3", "human", "pretend human")       # same id, tries to be human
        theirs.put(_human("Sneak.x", layer="ai/flirt-tier3", author="ai-in-disguise"))
        m = annot.merge(ours, theirs, {"layer:ai/flirt-tier3": "theirs"})
        self.assertFalse(m["ok"])
        self.assertEqual({c["kind"] for c in m["conflicts"]}, {"layer", "invalid_here"})
        self.assertEqual(m["pack"].layers["ai/flirt-tier3"]["kind"], "ai-draft")
        self.assertEqual(len(m["pack"]), 0)

    def test_diff(self):
        ours, theirs = self.two()
        d = annot.diff(ours, theirs)
        self.assertEqual([x["key"][2] for x in d["added"]], ["Extra.e", "Only.theirs"])
        self.assertEqual([x["key"][2] for x in d["removed"]], ["Only.ours"])
        self.assertEqual({x["key"][2]: x["fields"] for x in d["changed"]},
                         {"Clash.b": ["note", "updated"], "Time.c": ["updated"]})
        self.assertEqual((d["layers_added"], d["same"]), (["human/extra"], False))
        self.assertTrue(annot.diff(ours, ours.copy())["same"])


class StoreTests(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.dir)
        self.store = annot.PackStore(os.path.join(self.dir, "annotations"))

    def snapshot(self) -> dict:
        out = {}
        for path in self.store.files():
            with open(path, "rb") as f:
                out[os.path.basename(path)] = f.read()
        return out

    def seed(self) -> annot.Pack:
        p = _pack()
        p.put(_human("Clash.b", note="our reading"))
        p.put(_draft("D.d"))
        self.store.save(p)
        return p

    def test_one_canonical_file_per_layer(self):
        p = self.seed()
        snap = self.snapshot()
        self.assertEqual(sorted(snap), ["ai__flirt-tier3.jsonl", "human__notes.jsonl"])
        for raw in snap.values():
            self.assertEqual(annot.validate_text(raw), [])
        loaded, issues = self.store.load()
        self.assertEqual((issues, loaded), ([], p))
        self.assertEqual(self.store.export_text(), annot.dumps(p))
        only = annot.loads(self.store.export_text(["human/notes"]))
        self.assertEqual((sorted(only.layers), len(only)), (["human/notes"], 1))

    def test_conflicting_import_writes_nothing(self):
        self.seed()
        before = self.snapshot()
        theirs = _pack()
        theirs.put(_human("Clash.b", note="their reading"))
        theirs.put(_human("New.n"))
        rep = self.store.import_text(annot.dumps(theirs))
        self.assertEqual((rep["ok"], rep["applied"], rep["written"]), (False, False, []))
        self.assertEqual(len(rep["conflicts"]), 1)
        self.assertEqual(rep["conflicts"][0]["ours"]["note"], "our reading")
        self.assertEqual(self.snapshot(), before)                           # byte-for-byte unchanged
        json.dumps(rep)                                                     # report is JSON-ready
        # dry run with a resolution: still nothing written
        rid = rep["conflicts"][0]["id"]
        rep2 = self.store.import_text(annot.dumps(theirs), resolve={rid: "ours"}, dry_run=True)
        self.assertEqual((rep2["ok"], rep2["applied"]), (True, False))
        self.assertEqual(self.snapshot(), before)
        # explicit resolution applies, and only the touched layer file is rewritten
        rep3 = self.store.import_text(annot.dumps(theirs), resolve={rid: "theirs"})
        self.assertEqual((rep3["ok"], rep3["applied"], rep3["written"]), (True, True, ["human__notes.jsonl"]))
        after = self.snapshot()
        self.assertEqual(after["ai__flirt-tier3.jsonl"], before["ai__flirt-tier3.jsonl"])
        pack, _ = self.store.load()
        self.assertEqual(pack.annots[annot.record_key(_human("Clash.b"))]["note"], "their reading")

    def test_invalid_import_is_rejected_whole(self):
        self.seed()
        before = self.snapshot()
        with self.assertRaises(annot.PackError):
            self.store.import_text(_lines(HDR, LAYER_H, REC, dict(REC, name="Bad", tag="Z")))
        self.assertEqual(self.snapshot(), before)

    def test_upsert_create_edit_and_optimistic_locking(self):
        self.store.ensure_layer("human/notes", "human", "Human notes")
        fields = dict(name="U.x", layer="human/notes", tag="[S]", source="textbook, 1900", author="tester", note="v1")
        r1 = self.store.upsert(fields, now=T0)
        self.assertEqual((r1["tag"], r1["created"], r1["updated"], r1["id"]), ("S", T0, T0, annot.record_id(r1)))
        with self.assertRaises(annot.ConflictError):                        # blind re-create = overwrite attempt
            self.store.upsert(dict(fields, note="v2"), now=T1)
        with self.assertRaises(annot.ConflictError):                        # stale editor
            self.store.upsert(dict(fields, note="v2"), now=T1, expect_updated="2026-01-01T00:00:00Z")
        self.assertEqual(self.store.load()[0].get(r1["id"])["note"], "v1")
        r2 = self.store.upsert(dict(fields, note="v2"), now=T1, expect_updated=T0)
        self.assertEqual((r2["note"], r2["created"], r2["updated"]), ("v2", T0, T1))
        with self.assertRaises(annot.PackError):                            # validation applies to edits
            self.store.upsert(dict(fields, tag="M"), now=T2, expect_updated=T1)
        with self.assertRaises(annot.PackError):
            self.store.upsert(dict(fields, layer="human/undeclared"), now=T2)
        with self.assertRaises(annot.ConflictError):
            self.store.delete(r1["id"], expect_updated=T0)
        self.store.delete(r1["id"], expect_updated=T1)
        self.assertEqual(len(self.store.load()[0]), 0)
        self.assertEqual(annot.validate_text(self.snapshot()["human__notes.jsonl"]), [])

    def test_layer_ids_cannot_escape_the_directory(self):
        for bad in ("../x", "/abs", "a/../b", "A/Upper", "a//b", "a b", "x.jsonl/../../y", ""):
            with self.assertRaises(annot.PackError, msg=bad):
                annot.layer_filename(bad)
            with self.assertRaises(annot.PackError, msg=bad):
                self.store.ensure_layer(bad, "human", "t")
        self.assertEqual(annot.layer_filename("ai/flirt-tier3"), "ai__flirt-tier3.jsonl")
        self.assertEqual(os.listdir(self.dir), [])

    def test_cross_file_disagreement_is_reported(self):
        self.seed()
        rogue = _pack()
        rogue.put(_human("Clash.b", note="hand-edited copy"))
        annot.dump(rogue, os.path.join(self.store.root, "zz-rogue.jsonl"), layers=["human/notes"])
        pack, issues = self.store.load()
        self.assertEqual([(i["code"], i["file"]) for i in issues], [("conflict", "zz-rogue.jsonl")])
        self.assertEqual(pack.annots[annot.record_key(_human("Clash.b"))]["note"], "our reading")
        with self.assertRaises(annot.PackError):
            self.store.upsert(dict(name="N.n", layer="human/notes", tag="L", source="s", author="a", note="n"))


class CliTests(unittest.TestCase):
    def run_cli(self, *argv):
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
            code = annot.main(list(argv))
        return code, out.getvalue()

    def test_cli_end_to_end(self):
        d = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, d)
        ours, theirs = MergeTests().two()
        a, b, store = os.path.join(d, "a.jsonl"), os.path.join(d, "b.jsonl"), os.path.join(d, "annotations")
        annot.dump(ours, a)
        annot.dump(theirs, b)
        self.assertEqual(self.run_cli("validate", a, b)[0], 0)
        self.assertEqual(self.run_cli("annot", "validate", a)[0], 0)        # with or without the prefix
        with open(os.path.join(d, "bad.jsonl"), "w") as f:
            f.write(_lines(HDR, LAYER_H, dict(REC, tag="Q")))
        code, out = self.run_cli("validate", os.path.join(d, "bad.jsonl"))
        self.assertEqual(code, 1)
        self.assertIn("bad_tag", out)
        code, out = self.run_cli("export", a)
        self.assertEqual((code, out), (0, annot.dumps(ours)))
        self.assertEqual(self.run_cli("diff", a, a)[0], 0)
        self.assertEqual(self.run_cli("diff", a, b)[0], 1)
        merged = os.path.join(d, "m.jsonl")
        code, out = self.run_cli("merge", a, b, "-o", merged)
        self.assertEqual(code, 2)
        self.assertFalse(os.path.exists(merged))
        self.assertEqual(len(json.loads(out)["conflicts"]), 2)
        self.assertEqual(self.run_cli("import", a, "--into", store)[0], 0)
        code, out = self.run_cli("import", b, "--into", store)
        self.assertEqual((code, json.loads(out)["applied"]), (2, False))
        self.assertEqual(annot.PackStore(store).export_text(), annot.dumps(ours))
        self.assertEqual(self.run_cli("validate", store)[0], 0)
        code, out = self.run_cli("layers", store)
        self.assertEqual(code, 0)
        draft_row = [l for l in out.splitlines() if "ai/flirt-tier3" in l][0]
        self.assertTrue(draft_row.startswith("off") and "DRAFT" in draft_row)
        tsv = os.path.join(d, "g.tsv")
        with open(tsv, "w") as f:
            f.write("Same.a\t\n")
        code, out = self.run_cli("reanchor", a, "--graph-tsv", tsv, "--summary")
        self.assertEqual(json.loads(out)["counts"], {"exact": 0, "name_only": 1, "hash_only": 0, "orphan": 3, "unchecked": 0})

    def test_register_cli_on_a_host_parser(self):
        import argparse
        ap = argparse.ArgumentParser()
        sub = ap.add_subparsers(dest="cmd")
        annot.register_cli(sub)
        args = ap.parse_args(["annot", "validate", REPO_ANNOTATIONS])
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(args.annot_func(args), 0)


# ================================================================================================
# Contributor PR validation (`check-pr`), Treemap `overlay`, and `template`
# ================================================================================================

RH_SHA = "40e56bab026552e089d7afcfeff08d2defb9c005"
RH_PINNED_URL = f"https://github.com/leanprover-community/riemann-hypothesis/blob/{RH_SHA}/src/Main.lean#L4"


class ContribPrTests(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.dir)
        self.contrib = os.path.join(self.dir, "annotations", "contrib")
        os.makedirs(os.path.join(self.contrib, "riemann-hypothesis"), exist_ok=True)
        # Copy repo leanre_gallery.toml so strict project + pinned SHA rules run identically in temp dir
        repo_gallery = os.path.join(os.path.dirname(_HERE), "leanre_gallery.toml")
        if os.path.isfile(repo_gallery):
            shutil.copyfile(repo_gallery, os.path.join(self.dir, "leanre_gallery.toml"))

    def _write_raw_pack(self, rel_under_contrib: str, *objs: dict) -> str:
        path = os.path.join(self.contrib, rel_under_contrib)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            f.write(_lines(*objs))
        return path

    def _run_cli(self, *argv):
        out = io.StringIO()
        err = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = annot.main(list(argv))
        return code, out.getvalue(), err.getvalue()

    def test_valid_human_ai_and_bot_contrib_packs_and_markdown_report(self):
        h_layer = {
            "type": "layer", "layer": "human/alice-main", "kind": "human-review",
            "default_on": True, "title": "Alice check on Main",
        }
        h_rec = {
            "type": "annot", "target": "decl", "name": "riemannHypothesis",
            "sighash": "k1n:e67d3cf7e6fa39c3480c359052fb059f",
            "layer": "human/alice-main", "tag": "L", "status": "verified",
            "source": RH_PINNED_URL, "author": "@alice",
            "note": "Checked statement export in Main.lean against Mathlib RiemannHypothesis.",
            "extra": {"dom_subtree": 12},
            "created": T0, "updated": T0,
        }
        ai_layer = {
            "type": "layer", "layer": "ai/model-scan", "kind": "ai-draft",
            "default_on": False, "title": "Model structural summary",
        }
        ai_rec = {
            "type": "annot", "target": "decl", "name": "Claim.zeta",
            "sighash": "k1n:c5d0be07def54e1e2aba0fe15641c349",
            "layer": "ai/model-scan", "tag": "M", "status": "summary", "draft": True,
            "breaks": "Header-only pass; inner tactic proof unread.",
            "source": RH_PINNED_URL, "author": "ai:model-v1",
            "note": "Maps HalfPlane hypothesis to Zeta via Claim.strip.",
            "extra": {"dom_subtree": 50},
            "created": T0, "updated": T0,
        }
        bot_layer = {
            "type": "layer", "layer": "bot/checker-scan", "kind": "bot-check",
            "default_on": False, "title": "Automated axiom scan",
        }
        bot_rec = {
            "type": "annot", "target": "decl", "name": "Claim.strip",
            "sighash": "k1n:5a042d182e75334fac8c995e2581a923",
            "layer": "bot/checker-scan", "tag": "C", "status": "read", "draft": True,
            "source": RH_PINNED_URL, "author": "bot:checker",
            "note": "Axiom cone restricted to propext, Classical.choice, and Quot.sound.",
            "created": T0, "updated": T0,
        }
        self._write_raw_pack("riemann-hypothesis/alice__main.jsonl", HDR, h_layer, h_rec)
        self._write_raw_pack("riemann-hypothesis/ai-model-v1__scan.jsonl", HDR, ai_layer, ai_rec)
        self._write_raw_pack("riemann-hypothesis/bot-checker__scan.jsonl", HDR, bot_layer, bot_rec)

        md_out = os.path.join(self.dir, "summary.md")
        code, stdout, _ = self._run_cli(
            "check-pr", "--all-contrib", "--contrib-root", self.contrib,
            "--strict", "--json", "--markdown-report", md_out,
        )
        self.assertEqual(code, 0, stdout)
        rep = json.loads(stdout)
        self.assertTrue(rep["ok"])
        self.assertEqual(rep["files_checked"], 3)
        self.assertEqual(rep["totals"]["entries"], 3)
        with open(md_out, encoding="utf-8") as f:
            md = f.read()
        self.assertIn("**Result:** **PASS**", md)
        self.assertIn("`human-review`", md)
        self.assertIn("`ai-draft`", md)
        self.assertIn("+12", md)
        self.assertIn("+50", md)

    def test_a_ai_and_bot_packs_cannot_set_default_on_or_omit_draft(self):
        # 1. AI layer trying to set default_on: true
        bad_layer = {
            "type": "layer", "layer": "ai/sneaky", "kind": "ai-draft",
            "default_on": True, "title": "Sneaky AI",
        }
        rec_ok = {
            "type": "annot", "target": "decl", "name": "Foo.bar",
            "sighash": "k1n:" + "a" * 32, "layer": "ai/sneaky", "tag": "M",
            "breaks": "none", "draft": True, "source": RH_PINNED_URL,
            "author": "ai:sneaky", "note": "Draft note.", "created": T0, "updated": T0,
        }
        p1 = self._write_raw_pack("riemann-hypothesis/ai-sneaky__on.jsonl", HDR, bad_layer, rec_ok)
        r1 = annot.check_pr([p1], contrib_root=self.contrib, strict=True)
        self.assertFalse(r1["ok"])
        self.assertIn("ai_draft_default_on", _codes(r1["issues"]))

        # 2. AI record trying to set draft: false (or omit draft)
        ok_layer = dict(bad_layer, default_on=False)
        bad_rec = dict(rec_ok, draft=False)
        p2 = self._write_raw_pack("riemann-hypothesis/ai-sneaky__nodraft.jsonl", HDR, ok_layer, bad_rec)
        r2 = annot.check_pr([p2], contrib_root=self.contrib, strict=True)
        self.assertFalse(r2["ok"])
        self.assertIn("draft_unmarked", _codes(r2["issues"]))

        # 3. Bot pack trying to use human-review kind or status=verified on ai-draft
        forged_layer = {
            "type": "layer", "layer": "human/ai-forged", "kind": "human-review",
            "default_on": True, "title": "Forged",
        }
        forged_rec = {
            "type": "annot", "target": "decl", "name": "Foo.bar",
            "sighash": "k1n:" + "a" * 32, "layer": "human/ai-forged", "tag": "L",
            "source": RH_PINNED_URL, "author": "ai:forged", "note": "Forged human note.",
            "created": T0, "updated": T0,
        }
        p3 = self._write_raw_pack("riemann-hypothesis/ai-forged__bad.jsonl", HDR, forged_layer, forged_rec)
        r3 = annot.check_pr([p3], contrib_root=self.contrib, strict=True)
        self.assertFalse(r3["ok"])
        self.assertTrue(_codes(r3["issues"]) & {"ai_in_human_layer", "ai_author_in_human_layer"})
        self.assertIn("draft_unmarked", _codes(r3["issues"]))

        ver_rec = dict(rec_ok, status="verified")
        p4 = self._write_raw_pack("riemann-hypothesis/ai-sneaky__ver.jsonl", HDR, ok_layer, ver_rec)
        r4 = annot.check_pr([p4], contrib_root=self.contrib, strict=True)
        self.assertFalse(r4["ok"])
        self.assertIn("ai_verified_claim", _codes(r4["issues"]))

    def test_b_rejects_overclaim_phrases(self):
        layer = {
            "type": "layer", "layer": "human/alice-oc", "kind": "human-review",
            "default_on": True, "title": "Notes",
        }
        phrases = [
            "Therefore RH is proved unconditionally.",
            "This theorem proves RH directly.",
            "Here Alpoge proved the Riemann Hypothesis.",
            "The proof of the Riemann Hypothesis is complete.",
        ]
        for idx, bad_note in enumerate(phrases):
            rec = {
                "type": "annot", "target": "decl", "name": "riemannHypothesis",
                "sighash": "k1n:e67d3cf7e6fa39c3480c359052fb059f",
                "layer": "human/alice-oc", "tag": "L", "source": RH_PINNED_URL,
                "author": "@alice", "note": bad_note, "created": T0, "updated": T0,
            }
            path = self._write_raw_pack(f"riemann-hypothesis/alice__oc{idx}.jsonl", HDR, layer, rec)
            rep = annot.check_pr([path], contrib_root=self.contrib, strict=True)
            self.assertFalse(rep["ok"], bad_note)
            self.assertIn("overclaim", _codes(rep["issues"]), bad_note)

    def test_c_rejects_floating_blob_main_url_and_wrong_commit_sha(self):
        layer = {
            "type": "layer", "layer": "human/alice-url", "kind": "human-review",
            "default_on": True, "title": "URL check",
        }
        floating = "https://github.com/leanprover-community/riemann-hypothesis/blob/main/src/Main.lean#L4"
        rec1 = {
            "type": "annot", "target": "decl", "name": "riemannHypothesis",
            "sighash": "k1n:e67d3cf7e6fa39c3480c359052fb059f",
            "layer": "human/alice-url", "tag": "L", "source": floating,
            "author": "@alice", "note": "Exports RH statement.", "created": T0, "updated": T0,
        }
        p1 = self._write_raw_pack("riemann-hypothesis/alice__float.jsonl", HDR, layer, rec1)
        r1 = annot.check_pr([p1], contrib_root=self.contrib, strict=True)
        self.assertFalse(r1["ok"])
        self.assertIn("unpinned_url", _codes(r1["issues"]))

        wrong_sha = "https://github.com/leanprover-community/riemann-hypothesis/blob/" + ("b" * 40) + "/src/Main.lean#L4"
        rec2 = dict(rec1, source=wrong_sha)
        p2 = self._write_raw_pack("riemann-hypothesis/alice__wrongsha.jsonl", HDR, layer, rec2)
        r2 = annot.check_pr([p2], contrib_root=self.contrib, strict=True)
        self.assertFalse(r2["ok"])
        self.assertIn("wrong_pinned_sha", _codes(r2["issues"]))

    def test_d_rejects_pasted_lean_proof_body(self):
        layer = {
            "type": "layer", "layer": "human/alice-paste", "kind": "human-review",
            "default_on": True, "title": "Paste check",
        }
        for idx, snippet in enumerate([
            "Copied from file:\ntheorem foo (n : Nat) : n = n := by\n  rfl",
            "import Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nnamespace Foo\ntheorem bar : True := trivial",
            "Here is the code:\n```lean\nhave h1 : x = y := rfl\n```",
        ]):
            rec = {
                "type": "annot", "target": "decl", "name": "Foo.bar",
                "sighash": "k1n:" + "c" * 32, "layer": "human/alice-paste", "tag": "L",
                "source": RH_PINNED_URL, "author": "@alice", "note": snippet,
                "created": T0, "updated": T0,
            }
            p = self._write_raw_pack(f"riemann-hypothesis/alice__paste{idx}.jsonl", HDR, layer, rec)
            rep = annot.check_pr([p], contrib_root=self.contrib, strict=True)
            self.assertFalse(rep["ok"], snippet)
            self.assertIn("lean_proof_paste", _codes(rep["issues"]), snippet)

    def test_e_rejects_path_traversal_foreign_author_and_oversized_pack(self):
        # Path traversal
        trav = os.path.join(self.contrib, "riemann-hypothesis", "..", "..", "evil.jsonl")
        r_trav = annot.check_pr([trav], contrib_root=self.contrib, strict=True)
        self.assertFalse(r_trav["ok"])
        self.assertIn("path_traversal", _codes(r_trav["issues"]))

        # Foreign author editing alice's pack
        layer = {
            "type": "layer", "layer": "human/bob-hijack", "kind": "human-review",
            "default_on": True, "title": "Hijack",
        }
        rec = {
            "type": "annot", "target": "decl", "name": "Foo.bar",
            "sighash": "k1n:" + "d" * 32, "layer": "human/bob-hijack", "tag": "L",
            "source": RH_PINNED_URL, "author": "@bob", "note": "Bob writing in Alice's file.",
            "created": T0, "updated": T0,
        }
        p_foreign = self._write_raw_pack("riemann-hypothesis/alice__notes.jsonl", HDR, layer, rec)
        r_foreign = annot.check_pr([p_foreign], contrib_root=self.contrib, strict=True)
        self.assertFalse(r_foreign["ok"])
        self.assertIn("foreign_author", _codes(r_foreign["issues"]))
        # Allowed explicitly with allow_shared=True
        r_shared = annot.check_pr([p_foreign], contrib_root=self.contrib, allow_shared=True)
        self.assertTrue(r_shared["ok"], r_shared["issues"])

        # Oversized (> 2 MiB)
        big_path = os.path.join(self.contrib, "riemann-hypothesis", "alice__huge.jsonl")
        with open(big_path, "wb") as f:
            f.write((annot.canonical_json(HDR) + "\n").encode("utf-8"))
            f.write(b" " * (annot.MAX_PR_PACK_BYTES + 64))
        r_big = annot.check_pr([big_path], contrib_root=self.contrib)
        self.assertFalse(r_big["ok"])
        self.assertIn("pack_too_large", _codes(r_big["issues"]))

    def test_optional_anchors_json_and_committed_contrib_packs(self):
        anchors_file = os.path.join(self.dir, "annot_anchors.json")
        with open(anchors_file, "w", encoding="utf-8") as f:
            json.dump({
                "decls": {
                    "Good.decl": {"sighash": "k1n:" + "1" * 32, "dom_subtree": 250},
                    "Changed.decl": {"sighash": "k1n:" + "2" * 32, "dom_subtree": 40},
                }
            }, f)
        layer = {
            "type": "layer", "layer": "human/alice-anc", "kind": "human-review",
            "default_on": True, "title": "Anchor test",
        }
        good = {
            "type": "annot", "target": "decl", "name": "Good.decl",
            "sighash": "k1n:" + "1" * 32, "layer": "human/alice-anc", "tag": "L",
            "source": RH_PINNED_URL, "author": "@alice", "note": "Matches anchor map.",
            "created": T0, "updated": T0,
        }
        p_ok = self._write_raw_pack("riemann-hypothesis/alice__ancok.jsonl", HDR, layer, good)
        rep_ok = annot.check_pr([p_ok], contrib_root=self.contrib, anchors_path=anchors_file, strict=True)
        self.assertTrue(rep_ok["ok"], rep_ok["issues"])
        self.assertEqual(rep_ok["files"][0]["subtree_coverage_delta"], 250)

        bad_hash = dict(good, name="Changed.decl", sighash="k1n:" + "9" * 32)
        orphan = dict(good, name="Missing.decl", sighash="k1n:" + "8" * 32)
        layer2 = dict(layer, layer="human/alice-anc2")
        p_bad = self._write_raw_pack(
            "riemann-hypothesis/alice__ancbad.jsonl",
            HDR, layer2, dict(bad_hash, layer="human/alice-anc2"), dict(orphan, layer="human/alice-anc2"),
        )
        rep_bad = annot.check_pr([p_bad], contrib_root=self.contrib, anchors_path=anchors_file, strict=True)
        self.assertFalse(rep_bad["ok"])
        self.assertIn("anchor_hash_mismatch", _codes(rep_bad["issues"]))
        self.assertIn("anchor_orphan", _codes(rep_bad["issues"]))

        # Real committed contrib directory passes strict check
        real_contrib = os.path.join(REPO_ANNOTATIONS, "contrib")
        rep_real = annot.check_pr(all_contrib=True, contrib_root=real_contrib, strict=True)
        self.assertTrue(rep_real["ok"], rep_real["issues"])

    def test_same_author_multi_chunk_packs_merge_while_cross_author_hijack_fails(self):
        # Matches treemap.js buildDraftJsonl where one contributor exports multiple chunk files under one layer id
        shared_layer = {
            "type": "layer", "layer": "human/contrib-riemann-hypothesis-alice",
            "kind": "human", "default_on": True,
            "title": "Community review by @alice (riemann-hypothesis)",
        }
        r1 = {
            "type": "annot", "target": "decl", "name": "Chunk.one",
            "sighash": "k1n:" + "1" * 32, "layer": shared_layer["layer"], "tag": "L",
            "source": RH_PINNED_URL, "author": "@alice", "note": "Chunk 1 note.",
            "extra": {"project": "riemann-hypothesis", "review_kind": "human-review", "status": "verified"},
            "created": T0, "updated": T0,
        }
        r2 = dict(r1, name="Chunk.two", sighash="k1n:" + "2" * 32, note="Chunk 2 note.")
        p1 = self._write_raw_pack("riemann-hypothesis/alice__chunk-one.jsonl", HDR, shared_layer, r1)
        p2 = self._write_raw_pack("riemann-hypothesis/alice__chunk-two.jsonl", HDR, shared_layer, r2)
        rep = annot.check_pr([p1, p2], contrib_root=self.contrib, strict=True)
        self.assertTrue(rep["ok"], rep["issues"])

        # Another author trying to reuse Alice's layer id in Bob's file is blocked
        r_bob = dict(r1, name="Chunk.three", sighash="k1n:" + "3" * 32, author="@bob")
        p3 = self._write_raw_pack("riemann-hypothesis/bob__hijack.jsonl", HDR, shared_layer, r_bob)
        rep2 = annot.check_pr([p1, p3], contrib_root=self.contrib, strict=True)
        self.assertFalse(rep2["ok"])
        self.assertIn("duplicate_contrib_layer", _codes(rep2["issues"]))


class OverlayAndTemplateTests(unittest.TestCase):
    def test_f_contested_status_detection_in_overlay(self):
        d = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, d)
        annot_dir = os.path.join(d, "annotations")
        contrib_rh = os.path.join(annot_dir, "contrib", "riemann-hypothesis")
        os.makedirs(contrib_rh, exist_ok=True)

        p1 = annot.Pack()
        p1.add_layer("human/reviewer-a", "human-review", "Reviewer A")
        r_ver = annot.make_annotation(
            name="Target.contested", sighash="k1n:" + "1" * 32,
            layer="human/reviewer-a", tag="L", source=RH_PINNED_URL,
            author="@alice", now=T0, note="Verified step by step.",
        )
        r_ver["status"] = "verified"
        p1.put(r_ver)
        r_agree = annot.make_annotation(
            name="Target.uncontested", sighash="k1n:" + "2" * 32,
            layer="human/reviewer-a", tag="L", source=RH_PINNED_URL,
            author="@alice", now=T0, note="Clean helper lemma.",
        )
        r_agree["status"] = "verified"
        p1.put(r_agree)
        annot.dump(p1, os.path.join(contrib_rh, "alice__part1.jsonl"))

        p2 = annot.Pack()
        p2.add_layer("ai/auditor-bot", "ai-draft", "Auditor bot")
        r_flag = annot.make_annotation(
            name="Target.contested", sighash="k1n:" + "1" * 32,
            layer="ai/auditor-bot", tag="M", source=RH_PINNED_URL,
            author="ai:auditor", now=T1, draft=True,
            breaks="Heuristic structural flag.",
            note="Suspect unused hypothesis in bundle projection.",
        )
        r_flag["status"] = "flagged"
        r_flag["verdict"] = "suspect"
        p2.put(r_flag)
        r_agree2 = annot.make_annotation(
            name="Target.uncontested", sighash="k1n:" + "2" * 32,
            layer="ai/auditor-bot", tag="M", source=RH_PINNED_URL,
            author="ai:auditor", now=T1, draft=True,
            breaks="Header summary only.",
            note="Matches standard helper signature.",
        )
        r_agree2["status"] = "read"
        p2.put(r_agree2)
        annot.dump(p2, os.path.join(contrib_rh, "ai-auditor__part2.jsonl"))

        ov = annot.build_overlay(annot_dir, project="riemann-hypothesis", now=T2)
        self.assertEqual(ov["schema"], "leanre.treemap.overlay/1")
        self.assertEqual(ov["stats"], {
            "total_layers": 2,
            "total_records": 4,
            "unique_targets": 2,
            "contested_targets": 1,
        })
        self.assertTrue(all(e["contested"] for e in ov["entries"]["Target.contested"]))
        self.assertFalse(any(e["contested"] for e in ov["entries"]["Target.uncontested"]))
        # Human entry sorted ahead of AI draft entry
        self.assertEqual([e["draft"] for e in ov["entries"]["Target.contested"]], [False, True])

    def test_g_real_repo_annotations_compile_into_valid_overlay(self):
        ov = annot.build_overlay(REPO_ANNOTATIONS, project="riemann-hypothesis", now=T0)
        self.assertEqual(ov["schema"], "leanre.treemap.overlay/1")
        self.assertEqual(ov["project"], "riemann-hypothesis")
        self.assertGreaterEqual(ov["stats"]["total_layers"], 3)
        self.assertGreaterEqual(ov["stats"]["total_records"], 370)
        self.assertGreaterEqual(ov["stats"]["unique_targets"], 365)
        self.assertEqual(ov["stats"]["contested_targets"], 0)
        by_id = {l["id"]: l for l in ov["layers"]}
        self.assertIn("human/canonical-facts", by_id)
        self.assertIn("ai/decomp-phase4", by_id)
        self.assertIn("ai/decomp-phase6", by_id)
        self.assertEqual(by_id["human/canonical-facts"]["kind"], "human-review")
        self.assertTrue(by_id["human/canonical-facts"]["default_on"])
        self.assertFalse(by_id["ai/decomp-phase4"]["default_on"])
        self.assertFalse(by_id["ai/decomp-phase6"]["default_on"])
        for entries in ov["entries"].values():
            for e in entries:
                self.assertIn(e["status"], ("verified", "read", "summary", "flagged"))
                if e["layer"].startswith("ai/"):
                    self.assertTrue(e["draft"])

    def test_template_cli_generates_valid_packs_for_human_and_ai(self):
        d = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, d)
        contrib = os.path.join(d, "annotations", "contrib")
        repo_gallery = os.path.join(os.path.dirname(_HERE), "leanre_gallery.toml")
        shutil.copyfile(repo_gallery, os.path.join(d, "leanre_gallery.toml"))

        h_out = os.path.join(contrib, "riemann-hypothesis", "alice__everycharacter.jsonl")
        ai_out = os.path.join(contrib, "tiny-demo", "ai-helper__main-theorem.jsonl")
        with contextlib.redirect_stdout(io.StringIO()):
            c1 = annot.main([
                "template", "--project", "riemann-hypothesis",
                "--name", "UpperTheory.FinalTheorems.everyCharacter",
                "--sighash", "k1n:" + "a" * 32,
                "--author", "@alice", "--kind", "human-review",
                "--gallery-config", os.path.join(d, "leanre_gallery.toml"),
                "--out", h_out, "--now", T0,
            ])
            c2 = annot.main([
                "template", "--project", "tiny-demo",
                "--name", "TinyDemo.main_theorem",
                "--author", "ai:helper", "--kind", "ai-draft",
                "--gallery-config", os.path.join(d, "leanre_gallery.toml"),
                "--out", ai_out, "--now", T0,
            ])
        self.assertEqual((c1, c2), (0, 0))
        self.assertEqual(annot.validate_file(h_out), [])
        self.assertEqual(annot.validate_file(ai_out), [])
        # TinyDemo.main_theorem sighash auto-populated from examples/tiny_demo/demo.ndjson
        ai_pack = annot.load(ai_out)
        ai_rec = list(ai_pack.annots.values())[0]
        self.assertEqual(ai_rec["sighash"], "k1n:d881d9bce631f1d640f5c9be764f5014")
        self.assertTrue(ai_rec["draft"])
        self.assertFalse(list(ai_pack.layers.values())[0]["default_on"])
        rep = annot.check_pr(all_contrib=True, contrib_root=contrib, strict=True)
        self.assertTrue(rep["ok"], rep["issues"])


if __name__ == "__main__":
    unittest.main()
