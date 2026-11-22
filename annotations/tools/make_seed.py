#!/usr/bin/env python3
"""Regenerate annotations/human__canonical-facts.jsonl (the seed pack).

Every note below is a transcription of an already-audited canonical fact from HANDOFF.md §3 item 4.
No new mathematical or structural claim is introduced here.  Uses the real current UTC time
by default (pass ``--now YYYY-MM-DDTHH:MM:SSZ`` to reproduce a specific timestamp)."""
import argparse
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(REPO, "leanre"))
import annot  # noqa: E402

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument("--now", default=None, help="UTC ISO-8601 timestamp (default: current UTC time)")
NOW = ap.parse_args().now or annot.utc_now()
LAYER = "human/canonical-facts"
AUTHOR = "leanre-phase3/annot (transcribed from HANDOFF.md §3)"
MIRROR = "Deicyde/riemann-hypothesis@40e56bab026552e089d7afcfeff08d2defb9c005"
CHALLENGE = "challenge.ndjson.zst SHA-256 c24ef99dab3556a52c7fb886e03cf22a242f3b96f82ae4cc40539e5d2f678ac6"
AUDIT = "audited: HANDOFF.md §3 item 4"
# Frozen SIGHASH v1 (docs/SIGHASH.md) k1n digests extracted from data/challenge.ndjson.zst
# (TSV SHA-256 1c0b8c380ae14e89398f4837fdcd77df1716b1ee1fb2d54d68197848e1e1767e, no lexicon).
K1N = {
    "riemannHypothesis": "k1n:e67d3cf7e6fa39c3480c359052fb059f",
    "riemannZeta_eq_zero_re": "k1n:407e56a49b1c5d53ff3748d49d502ad6",
    "sorryAx": "k1n:d385ff723887407cf6e6654f6ff0457e",
}

p = annot.Pack()
p.add_layer(LAYER, "human", "Canonical verified facts (HANDOFF.md §3)",
            description="Seed/example pack. Each note transcribes a canonical fact already audited against the "
                        "primary files in Phases 1-2 (HANDOFF.md §3 item 4); no new claims. Transcribed by the "
                        "Phase 3 annotation worker, not hand-written by a person: review before relying on it. "
                        "These facts describe the artifact (Layer 1/2 telemetry); they say nothing about whether "
                        "the mathematics is correct.")


def add(**kw):
    p.put(annot.make_annotation(layer=LAYER, tag="L", author=AUTHOR, now=NOW, **kw))


add(target="module", name="Main",
    note="Exports 2 zeta RH theorems (riemannHypothesis + riemannZeta_eq_zero_re) and 3 Dirichlet-only GRH "
         "theorems. Extended RH is not claimed.",
    source=f"Main.lean, {MIRROR}; {AUDIT}")
add(name="riemannHypothesis", sighash=K1N["riemannHypothesis"],
    aliases=["zeta RH theorem (1 of 2 exported by Main.lean)"],
    note="One of the 2 zeta RH theorems exported by Main.lean; the other is riemannZeta_eq_zero_re.",
    source=f"Main.lean, {MIRROR}; k1n from {CHALLENGE}; {AUDIT}")
add(name="riemannZeta_eq_zero_re", sighash=K1N["riemannZeta_eq_zero_re"],
    aliases=["zeta RH theorem (2 of 2 exported by Main.lean)"],
    note="One of the 2 zeta RH theorems exported by Main.lean; the other is riemannHypothesis.",
    source=f"Main.lean, {MIRROR}; k1n from {CHALLENGE}; {AUDIT}")
add(name="sorryAx", sighash=K1N["sorryAx"],
    note="Fan-in is 5 in challenge.ndjson.zst, isolated strictly to Challenge.lean value stubs.",
    source=f"{CHALLENGE}; {AUDIT}")
add(target="folder", name="Development.AbelianVarietyTheory",
    note="99,187 files (56.6%). Actually declares _root_.GlobalTheory (39,212), IndefiniteRowSideFullHecke "
         "(14,165), GlobalTheory.Mem (11,592).",
    source=f"source scan of {MIRROR}; {AUDIT}")

out = os.path.join(REPO, "annotations", annot.layer_filename(LAYER))
annot.dump(p, out)
print(out, len(p), "records")
