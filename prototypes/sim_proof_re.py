#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
sim_proof_re.py -- "Ghidra for a 17.4M-line Lean proof": a reverse-engineering test session.

WHAT THIS IS
    A standard-library-only (Python >= 3.9) workbench that treats a huge machine-generated
    Lean 4 proof as a stripped binary: nodes = declarations, edges = "uses", and the questions
    are the ones a reverse engineer asks of a call graph.

    It has three input modes that all feed the SAME analysis passes:

      (default)        SIMULATE a declaration-level dependency DAG modeled on the Alpoge+Claude
                       RH/GRH release (Nov 20 2026) and analyse it.
      --from-jsonl F   analyse a REAL declaration graph (one JSON object per line, schema below),
                       e.g. produced from Sutherland's `solution.ndjson` or from `.olean` files.
      --lean-dir D     analyse a REAL source tree at module granularity (parses `import` lines;
                       no Lean toolchain needed) + clone/entropy/red-flag passes on the text.

WHAT IS REAL AND WHAT IS INVENTED IN THE SIMULATION   (read this before quoting any number)
    REAL (taken from primary sources collected in research/01_landscape_and_artifacts.md):
      * global scale: 175,187 files, 17,374,215 lines, 1,060,822 keyword declarations,
        thm/def ratio, bytes per line; the statement closure size (51,692 declarations in
        the Comparator `challenge` export); "every file is in the import closure of Main".
      * the five headline theorems and four `Statements.lean` definitions (verbatim names).
      * the ~30 named nodes of the top spine and how they are wired (from the community
        blueprint `spine.mmd` / PROOF-MAP, which were read off the Lean source by others).
    INVENTED (priors, NOT measurements -- nobody has published the declaration-level graph):
      * everything below the named spine: cluster sizes, depths, fan-out, which cluster uses
        which, how often encapsulation is violated ("leaks"), dead-code rate, clone rate.
      * all names starting with `Sim.` and `Mathlib.cone_/thm_/def_`.
    So: structural *phenomena* and *orders of magnitude* are the output; specific percentages
    are properties of the generator until the passes are re-run on real data.

PASSES
    1  reachability / dead code from Main.riemannHypothesis (decl level vs import level)
    2  axiom footprint (`#print axioms` as graph reachability) vs lexical grep
    3  statement closure = the semantic TCB ("what must be read to know WHAT was proved")
    4  dominator tree (Cooper-Harvey-Kennedy) + retained mass + chapter frontier
    5  articulation points & bridges (iterative Tarjan), with/without library sinks
    6  path-flow centrality (source->sink betweenness) : hubs vs chokepoints
    7  export tables (entry points per cluster) + min vertex cut below the nearest
       common dominator (unit-capacity max-flow)
    8  clone clustering (normalise -> shingle -> min-hash bands -> Jaccard verify) + entropy
    9  hierarchical "decompilation budget" (tokens / dollars / calls / wall-clock)
    10 sensitivity sweep: how do passes 4 and 7 degrade as encapsulation leaks grow?
    H  (--lean-dir only) Horn skeleton: implications between NAMED propositions read off theorem
       signatures. The constant-reference graph cannot see hypotheses that are passed in as
       arguments ("dependency injection": `foo_of_bar (h : Bar) : Foo`); this pass can.
    A brute-force self-test of passes 4, 5, 7, H and of both ingest modes runs first.

KNOWN LIMITS
    * Edges are "constant X is mentioned by constant Y". A proof that takes its key input as a
      hypothesis and is discharged elsewhere shows up as two SIBLING subtrees, not parent/child.
    * articulation() assumes no antiparallel edge pairs (true for DAGs; mutual blocks need SCC
      condensation first).
    * --lean-dir sees files, not declarations: it over-approximates dependence (see pass 1).

JSONL SCHEMA for --from-jsonl (one declaration per line):
    {"name": str, "kind": "thm"|"def"|"inst"|"aux"|"axiom", "module": str, "lines": int,
     # "lines" may be omitted or 0 everywhere: mass then falls back to 1 per declaration
     "ext": bool,            # true = library (Mathlib/core), treated as trusted sink
     "deps": [str, ...],     # every constant referenced in type OR value
     "sig":  [str, ...]}     # constants referenced in the TYPE (statement) only

USAGE
    python3 sim_proof_re.py                       # self-test + simulation at 5% scale (~10 s)
    python3 sim_proof_re.py --scale 1.0           # full 1.06M-declaration simulation (~35 s, ~2.3 GB RSS)
    python3 sim_proof_re.py --json out.json       # also dump metrics + spine tree for visualisation
    python3 sim_proof_re.py --lean-dir path/to/lean/src --root Main
    python3 sim_proof_re.py --from-jsonl decls.jsonl --root riemannHypothesis
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import heapq
import itertools
import json
import math
import os
import random
import re
import sys
import tempfile
import time
import zlib

# --------------------------------------------------------------------------------------
# Real, sourced calibration constants (see research/01_landscape_and_artifacts.md)
# --------------------------------------------------------------------------------------
REAL = {
    "files": 175_187,                 # .lean files                         (Deicyde NOTES.md)
    "lines": 17_374_215,              # physical lines, wc -l               (Deicyde NOTES.md)
    "bytes": 1_030_531_854,           # source bytes                        (Deicyde NOTES.md)
    "decls_kw": 1_060_822,            # keyword declarations                (Deicyde NOTES.md)
    "thm_kw": 818_755,                # theorem/lemma
    "def_kw": 242_067,                # def/abbrev/structure/class/instance/inductive
    "import_edges": 753_261,          # project->project imports            (drew2apps summary.json)
    "export_decls": 1_468_418,        # decls in lean4export closure        (con-leche log, Sutherland)
    "challenge_decls": 51_692,        # decls needed to STATE the 5 thms    (con-leche --compare)
    "env_constants": 2_701_132,       # constants in full environment       (Sutherland audit.log)
    "src_trace_keep": (0.55, 0.80),   # share of decls kept by two source-level traces (keithadler)
}
SEED = 20261120

# --------------------------------------------------------------------------------------
# Budget-model assumptions (all overridable in one place; printed in the report)
# --------------------------------------------------------------------------------------
BYTES_PER_TOKEN = 3.3     # ASSUMPTION: Lean with Unicode math + long identifiers; plausible 2.8-4.0
TOK_PER_LINE = REAL["bytes"] / REAL["lines"] / BYTES_PER_TOKEN   # ~18 tokens / line
PROMPT_TOK = 400          # instructions per call
DEP_STMT_TOK = 60         # one dependency's statement/summary pulled into context
CARD_OUT = 120            # output tokens per declaration "card"
MOD_OUT = 250             # output tokens per module summary
DIR_FAN = 40              # summaries folded per roll-up call
DIR_OUT = 500
SPINE_OUT = 600           # output tokens per spine explanation
SIG_LINES = 3.0           # ASSUMPTION: average statement (signature) length in lines; a decl averages 16.4
DIFF_FRAC = 0.20          # reading a clone as a diff against its exemplar costs 20% of full
QA_SAMPLE = 0.05          # share of bulk calls independently re-done by a verifier
CTX_WINDOW = 200_000
CALL_SECONDS = 45
PARALLEL = 64
PRICES = {                # ASSUMPTION: illustrative $ per million tokens (input, output). Plug in your own.
    "economy": (0.25, 1.25),
    "mid": (3.0, 15.0),
    "frontier": (15.0, 75.0),
}


# ======================================================================================
# Graph container
# ======================================================================================
class PG:
    """Proof graph. Node attributes are parallel lists indexed by int id."""

    def __init__(self):
        self.name, self.kind, self.grp, self.lines = [], [], [], []
        self.ext = bytearray()
        self.deps, self.sig = [], []
        self.mod = []
        self.grp_names, self.mod_names = [], []
        # simulation-only ground truth
        self.level, self.role, self.tmpl = [], [], []
        self.tmpl_len = {}
        self.extra_imports = []      # (importer module, imported module)
        self.meta = {}

    @property
    def n(self):
        return len(self.name)

    def add(self, name, kind, grp, lines=0, ext=False, level=-1, role="", tmpl=-1):
        self.name.append(name); self.kind.append(kind); self.grp.append(grp)
        self.lines.append(lines); self.ext.append(1 if ext else 0)
        self.deps.append([]); self.sig.append([]); self.mod.append(-1)
        self.level.append(level); self.role.append(role); self.tmpl.append(tmpl)
        return len(self.name) - 1


# ======================================================================================
# Simulation generator
# ======================================================================================
Stage = collections.namedtuple("Stage", "key title share iface depth dead clone xrate uses skew")

# Cluster entry points carry the names reported by the community blueprint (jae-63 spine.mmd,
# keithadler PROOF-MAP). Shares / depths / dead / clone / uses are INVENTED priors.
STAGES = [
    Stage("Spine", "Main.lean + thin connective spine (hand-wired from spine.mmd)", 0, [], 0, 0, 0, 0, [], 1.0),
    Stage("Landau", "Landau: one-sided growth bound => zero-free region", 0.02,
          ["Landau.zero_free_of_Chebyshev_growth"], 4, 0.15, 0.05, 0.5, [10], 1.3),
    Stage("Window", "Gm(x) <= x^(1/2+O(eps)) on windows (the crux inequality)", 0.10,
          ["Comparison₂.level_gm_le_on_family_scales"], 6, 0.25, 0.15, 0.8, [5, 7, 10], 1.6),
    Stage("Hosts", "character averaging / auxiliary hosts", 0.04,
          ["Top.supplyChi", "Top.imprimitive"], 5, 0.20, 0.10, 0.6, [10], 1.5),
    Stage("TopG", "TopG: families are connected", 0.08,
          ["Top.shape_closed_link_n_of_green", "Top.forall_goal_of_shape_of_hyps"], 6, 0.25, 0.15, 0.8, [5, 6, 10], 1.7),
    Stage("Hyps", "HypsAlt family package: Siegel-Weil, Howe duality, theta integrals", 0.16,
          ["Lit.nonempty_hyps_definite_side_of_closed_bound"], 7, 0.30, 0.30, 0.8, [8, 9, 10], 2.0),
    Stage("Green", "Green: cuspidal characters of GL_d(F_q)", 0.03,
          ["GreenBridge.green_of_regular"], 5, 0.20, 0.10, 0.5, [10], 1.5),
    Stage("VWin", "VWin: Sha-length window, Iwasawa towers", 0.10,
          ["One.Join.automorphic_window_of_inputs"], 6, 0.25, 0.15, 0.8, [8, 10], 1.7),
    Stage("Row", "Row0b: Galois reps via global theta lift + geometric realisation", 0.22,
          ["TP.K.tLiftK", "Geo.geoOne_holds"], 7, 0.30, 0.35, 0.7, [9, 10], 2.2),
    Stage("LLC", "local Langlands for GL_n", 0.10,
          ["Zero.LLC.recTExists"], 6, 0.25, 0.25, 0.6, [10], 2.1),
    Stage("Ground", "shared in-repo infrastructure (fields, cohomology, analysis)", 0.15,
          None, 5, 0.30, 0.20, 0.0, [], 1.8),
]
GROUND = 10
GROW = 2.6           # geometric growth of lemma count per level
CHUNK_FIT = 1.23     # fitted so that simulated files/decl matches the real 175,187 files
DEF_FRAC = REAL["def_kw"] / REAL["decls_kw"]
ROOT = "riemannHypothesis"
HEADLINES = ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
             "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"]

# (name, kind, [deps], [sig])  -- wiring per blueprint/spine.mmd; "@X" = entry point of cluster X
SPINE = [
    ("RiemannZetaZerosOnLine", "def", ["riemannZeta", "Complex.re"], None),
    ("DirichletLNonvanishingRightOfHalf", "def", ["DirichletCharacter.LFunction", "DirichletCharacter", "Complex.re"], None),
    ("DirichletLZerosOnLine", "def", ["DirichletCharacter.LFunction", "DirichletCharacter", "Complex.re"], None),
    ("PrimitiveDirichletLZerosOnLine", "def",
     ["DirichletCharacter.LFunction", "DirichletCharacter.IsPrimitive", "Complex.re"], None),
    ("UpperTheory.EveryCharacter", "def", ["DirichletCharacter.LFunction", "DirichletCharacter", "Complex.re"], None),
    ("riemannHypothesis", "thm", ["rhOfAll"], ["RiemannHypothesis"]),
    ("riemannZeta_eq_zero_re", "thm", ["rhOfAll"], ["RiemannZetaZerosOnLine"]),
    ("LFunction_ne_zero_of_half_lt_re", "thm", ["allChi"], ["DirichletLNonvanishingRightOfHalf"]),
    ("LFunction_eq_zero_re", "thm", ["claimAll"], ["DirichletLZerosOnLine"]),
    ("LFunction_eq_zero_re_of_isPrimitive", "thm", ["critAll"], ["PrimitiveDirichletLZerosOnLine"]),
    ("rhOfAll", "thm", ["Formalism.VW.rh_of_every", "allChi"], ["RiemannHypothesis"]),
    ("critAll", "thm", ["Formalism.VW.critLine", "allChi"], ["PrimitiveDirichletLZerosOnLine"]),
    ("claimAll", "thm", ["Claim.strip", "allChi"], ["DirichletLZerosOnLine"]),
    ("Formalism.VW.rh_of_every", "thm", ["Formalism.VW.rh_of_right"], ["UpperTheory.EveryCharacter", "RiemannHypothesis"]),
    ("Formalism.VW.rh_of_right", "thm", [], ["RiemannHypothesis"]),
    ("Formalism.VW.critLine", "thm", [], ["UpperTheory.EveryCharacter"]),
    ("Claim.strip", "thm", [], ["UpperTheory.EveryCharacter"]),
    ("allChi", "thm", ["UpperTheory.FinalTheorems.everyCharacter"], ["UpperTheory.EveryCharacter"]),
    ("UpperTheory.FinalTheorems.everyCharacter", "thm",
     ["UpperTheory.FinalTheorems.everyCharacter_of_row", "Gal.Int.galoisLocalGlobalStrong_recParameter"],
     ["UpperTheory.EveryCharacter"]),
    ("UpperTheory.FinalTheorems.everyCharacter_of_row", "thm",
     ["LiteratureTheorems.every_character_of_literature_of_vWin", "@LLC:0", "One.vwin_of_row"],
     ["UpperTheory.EveryCharacter"]),
    ("One.vwin_of_row", "thm", ["@VWin:0"], []),
    ("Gal.Int.galoisLocalGlobalStrong_recParameter", "thm", ["galoisRepresentations_of_thetaLift"], []),
    ("galoisRepresentations_of_thetaLift", "thm", ["@Row:0", "@Row:1"], []),
    ("LiteratureTheorems.every_character_of_literature_of_vWin", "thm",
     ["Lit.every_character_of_theta_integrals_local_matching"], ["UpperTheory.EveryCharacter"]),
    ("Lit.every_character_of_theta_integrals_local_matching", "thm",
     ["@Green:0", "@Hyps:0", "Top.every_character_of_green_v_win"], ["UpperTheory.EveryCharacter"]),
    ("Top.every_character_of_green_v_win", "thm", ["@Hosts:1", "Top.zero_free_all_of_green_v_win"],
     ["UpperTheory.EveryCharacter"]),
    ("Top.zero_free_all_of_green_v_win", "thm", ["@TopG:0", "@TopG:1", "@Hosts:0", "Top.zeroFreeAll_of_topG"], []),
    ("Top.zeroFreeAll_of_topG", "thm", ["HC.zeroFreeOn_of_tiedWin_cyc"], []),
    ("HC.zeroFreeOn_of_tiedWin_cyc", "thm", ["@Window:0", "@Landau:0"], []),
]
SPINE_MODULE = {"riemannHypothesis": "Main", "riemannZeta_eq_zero_re": "Main",
                "LFunction_ne_zero_of_half_lt_re": "Main", "LFunction_eq_zero_re": "Main",
                "LFunction_eq_zero_re_of_isPrimitive": "Main",
                "RiemannZetaZerosOnLine": "Statements", "DirichletLNonvanishingRightOfHalf": "Statements",
                "DirichletLZerosOnLine": "Statements", "PrimitiveDirichletLZerosOnLine": "Statements",
                "rhOfAll": "Supplements.Kernels.MainTheoremsAll", "critAll": "Supplements.Kernels.MainTheoremsAll",
                "claimAll": "Supplements.Kernels.MainTheoremsAll", "allChi": "Supplements.Kernels.MainTheoremsAll"}
ML_NAMED = [("Complex", []), ("Complex.re", ["Complex"]), ("riemannZeta", ["Complex"]),
            ("RiemannHypothesis", ["riemannZeta", "Complex.re", "Complex"]),
            ("DirichletCharacter", []), ("DirichletCharacter.LFunction", ["DirichletCharacter", "Complex"]),
            ("DirichletCharacter.IsPrimitive", ["DirichletCharacter"])]

_LINES = {  # role -> (median, sigma) of a log-normal, before global normalisation
    "spine": (3, 0.5), "stmt": (3, 0.2), "iface": (120, 0.6), "major": (70, 0.7), "tech": (28, 0.8),
    "leaf": (11, 0.7), "def": (8, 0.6), "inst": (5, 0.4), "dead_branch": (22, 0.9), "dead_orphan": (10, 0.7),
}


def generate(scale=0.05, seed=SEED, p_leak=0.01, p_chain=0.25, plant_live_axiom=False):
    """Build a synthetic declaration DAG. Deterministic for a given (scale, seed, p_leak, p_chain)."""
    rnd = random.Random(seed)
    g = PG()
    g.grp_names = [s.key for s in STAGES] + ["Mathlib"]
    MATH = len(STAGES)
    n_decl = max(1500, round(REAL["decls_kw"] * scale))
    by_name = {}

    def ext(name, kind):
        v = g.add(name, kind, MATH, ext=True, role="mathlib")
        by_name[name] = v
        return v

    # ---- library layer ------------------------------------------------------------
    AX = {nm: ext(nm, "axiom") for nm in ("propext", "Classical.choice", "Quot.sound", "sorryAx", "Lean.ofReduceBool")}
    std_ax = [AX["propext"], AX["Classical.choice"], AX["Quot.sound"]]
    for nm, _ in ML_NAMED:
        ext(nm, "def")
    for nm, ds in ML_NAMED:
        g.deps[by_name[nm]] = [by_name[d] for d in ds]
    # statement closure, calibrated to the REAL 51,692-declaration challenge export
    n_cone = max(60, round(REAL["challenge_decls"] * scale) - len(ML_NAMED) - 3)
    cone = []
    for i in range(n_cone):
        v = ext("Mathlib.cone_%d" % i, "def" if rnd.random() < 0.45 else "thm")
        if g.kind[v] == "thm":
            g.deps[v].extend(a for a in std_ax if rnd.random() < 0.8)
        cone.append(v)
    tops = [by_name["riemannZeta"], by_name["DirichletCharacter.LFunction"], by_name["DirichletCharacter"],
            by_name["Complex"], by_name["DirichletCharacter.IsPrimitive"]]
    for i, v in enumerate(cone):          # every cone node gets a user above it => reachable from the statements
        if i >= n_cone - 3 * len(tops) or rnd.random() < 0.01:
            g.deps[rnd.choice(tops)].append(v)
        else:
            g.deps[cone[rnd.randrange(i + 1, n_cone)]].append(v)
        if rnd.random() < 0.6 and i + 1 < n_cone:
            g.deps[cone[rnd.randrange(i + 1, n_cone)]].append(v)
    ml_thms = [v for v in cone if g.kind[v] == "thm"]
    ml_defs = [v for v in cone if g.kind[v] == "def"]
    for i in range(max(300, round(150_000 * scale))):   # INVENTED size: library lemmas the proofs touch
        if i % 10 < 3:
            ml_defs.append(ext("Mathlib.def_%d" % i, "def"))
        else:
            v = ext("Mathlib.thm_%d" % i, "thm")
            g.deps[v].extend(a for a in std_ax if rnd.random() < 0.8)
            ml_thms.append(v)
    rnd.shuffle(ml_thms); rnd.shuffle(ml_defs)

    def cumw(k, a=0.9):
        out, s = [], 0.0
        for i in range(k):
            s += 1.0 / (i + 1) ** a
            out.append(s)
        return out
    cw_thm, cw_def = cumw(len(ml_thms)), cumw(len(ml_defs))
    pick_ml_thm = lambda: rnd.choices(ml_thms, cum_weights=cw_thm)[0]
    pick_ml_def = lambda: rnd.choices(ml_defs, cum_weights=cw_def)[0]

    def draw_lines(role):
        med, sg = _LINES[role]
        return max(1, int(rnd.lognormvariate(math.log(med), sg)))

    # ---- clusters, generated bottom-up so that users can reference finished clusters ------
    S = len(STAGES)
    iface = [[] for _ in range(S)]
    levels = [None] * S
    defs = [[] for _ in range(S)]
    order = [[] for _ in range(S)]        # creation order with segment keys, for module chunking
    iface_used = set()
    api = [[] for _ in range(S)]          # designed public surface: entry points + major lemmas
    api_truth = set()
    fam_id = 0
    dead_tops = [[] for _ in range(S)]
    first_dead = {}

    for s in range(S - 1, 0, -1):
        st = STAGES[s]
        key = st.key
        n_s = max(60, int(n_decl * st.share))
        n_dead = int(n_s * st.dead)
        n_live = n_s - n_dead
        n_def = max(4, int(n_live * DEF_FRAC))
        lower_defs = [d for t in st.uses for d in defs[t]]
        # definitions: a small DAG, never depending on theorems
        for i in range(n_def):
            kind = "inst" if rnd.random() < 0.2 else "def"
            v = g.add("Sim.%s.Defs.%s_%d" % (key, kind, i), kind, s, draw_lines(kind), role="def")
            d = set()
            if defs[s]:
                for _ in range(rnd.choice((0, 1, 1, 2))):
                    d.add(defs[s][int(len(defs[s]) * rnd.random() ** 2)])
            if lower_defs and rnd.random() < 0.3:
                d.add(rnd.choice(lower_defs))
            for _ in range(rnd.choice((1, 1, 2))):
                d.add(pick_ml_def())
            g.deps[v] = sorted(d); g.sig[v] = list(g.deps[v])
            defs[s].append(v); order[s].append((("def",), v))
        # theorems: entry points (level 0) then geometric levels with a spanning skeleton
        n_thm = n_live - n_def
        lv = [[] for _ in range(st.depth + 1)]
        names = st.iface if st.iface is not None else ["Sim.%s.api_%d" % (key, i) for i in range(max(8, int(n_thm * 0.04)))]
        for nm in names:
            v = g.add(nm, "thm", s, draw_lines("iface"), level=0, role="iface")
            by_name[nm] = v
            lv[0].append(v); order[s].append((("thm", 0), v))
        rem = max(st.depth, n_thm - len(names))
        w = [GROW ** l for l in range(1, st.depth + 1)]
        tot = sum(w)
        for l in range(1, st.depth + 1):
            role = "major" if l == 1 else ("leaf" if l == st.depth else "tech")
            for i in range(max(1, int(rem * w[l - 1] / tot))):
                v = g.add("Sim.%s.L%d.lem_%d" % (key, l, i), "thm", s, draw_lines(role), level=l, role=role)
                lv[l].append(v); order[s].append((("thm", l), v))
                g.deps[rnd.choice(lv[l - 1])].append(v)          # skeleton edge: guarantees a user
        levels[s] = lv
        iface[s] = lv[0]
        api[s] = lv[0] + lv[1] + (lv[2][:max(1, len(lv[2]) // 4)] if st.depth >= 3 else [])
        api_truth.update(api[s])
        # clone families among the two deepest levels (AI boilerplate: same proof shape, new names)
        for l in (st.depth - 1, st.depth):
            L, i = lv[l], 0
            while i < len(L):
                m = rnd.randint(4, 40)
                if rnd.random() < st.clone:
                    base = max(3, min(60, g.lines[L[i]]))
                    g.tmpl_len[fam_id] = base
                    for v in L[i:i + m]:
                        g.tmpl[v] = fam_id
                        g.lines[v] = max(1, int(base * rnd.uniform(0.9, 1.1)))
                    fam_id += 1
                i += m
        internals_top = [v for l in range(1, min(4, st.depth + 1)) for v in lv[l]]
        internals_all = [v for l in range(1, st.depth + 1) for v in lv[l]]
        levels[s].append(internals_top); levels[s].append(internals_all)   # stash at [-2], [-1]
        # remaining edges
        for l in range(0, st.depth + 1):
            L = lv[l]
            for i, v in enumerate(L):
                d = g.deps[v]
                if l < st.depth:
                    for _ in range(rnd.choice((0, 0, 0, 1, 1, 2, 3))):
                        l2 = l + 1 if (rnd.random() < 0.7 or l + 1 == st.depth) else rnd.randint(l + 1, st.depth)
                        L2 = lv[l2]
                        d.append(L2[int(len(L2) * rnd.random() ** 3)] if rnd.random() < 0.35 else L2[rnd.randrange(len(L2))])
                if l >= 1 and i >= 3 and rnd.random() < p_chain:    # sequential "lemma N uses lemma N-1" chains
                    d.append(L[i - rnd.randint(1, 3)])
                if st.uses:
                    r = rnd.random()
                    k = 2 if r < st.xrate * 0.10 else (1 if r < st.xrate * 0.45 else 0)
                    for _ in range(k):
                        t = rnd.choice(st.uses)
                        if rnd.random() < p_leak:                   # encapsulation leak: reach past the API
                            pool = levels[t][-2] if rnd.random() < 0.5 else levels[t][-1]
                            d.append(rnd.choice(pool))
                        else:                                       # well-behaved: go through the public API
                            F = api[t]
                            tgt = F[int(len(F) * rnd.random() ** 2.5)]
                            d.append(tgt); iface_used.add(tgt)
                sg = set()
                for _ in range(rnd.choice((1, 1, 2, 3))):
                    sg.add(defs[s][int(len(defs[s]) * rnd.random() ** 2)])
                if lower_defs and rnd.random() < 0.25:
                    sg.add(rnd.choice(lower_defs))
                sg.add(pick_ml_def())
                for _ in range(1 + int(rnd.expovariate(0.6))):
                    d.append(pick_ml_thm())
                g.sig[v] = sorted(sg)
                g.deps[v] = sorted(set(d) | sg)
        # dead code: abandoned attempts (connected sub-DAGs nobody uses) and orphan helpers
        pool = [v for l in range(2, st.depth + 1) for v in lv[l]] or internals_all
        lower_if = [v for t in st.uses for v in iface[t]]
        made, j, nb = 0, 0, int(n_dead * 0.6)
        while made < nb:
            size = min(nb - made, max(2, int(rnd.lognormvariate(3.0, 1.2))))
            br = []
            for i in range(size):
                kind = "def" if rnd.random() < DEF_FRAC else "thm"
                v = g.add("Sim.%s.Attempt%d.lem_%d" % (key, j, i), kind, s, draw_lines("dead_branch"), role="dead_branch")
                if br:
                    g.deps[br[int(len(br) * rnd.random())]].append(v)
                br.append(v); order[s].append((("dead", j), v))
            for v in br:
                d = g.deps[v]
                for _ in range(rnd.choice((0, 1, 1, 2))):
                    d.append(rnd.choice(pool))
                if lower_if and rnd.random() < 0.3:
                    d.append(rnd.choice(lower_if))
                d.append(pick_ml_thm())
                sgd = [defs[s][int(len(defs[s]) * rnd.random() ** 2)]]
                g.sig[v] = sgd
                g.deps[v] = sorted(set(d) | set(sgd))
            dead_tops[s].append(br[0])
            first_dead.setdefault(s, br)
            made += size; j += 1
        for i in range(n_dead - nb):
            v = g.add("Sim.%s.Scratch.unused_%d" % (key, i), "def" if rnd.random() < DEF_FRAC else "thm", s,
                      draw_lines("dead_orphan"), role="dead_orphan")
            d = {rnd.choice(pool), pick_ml_thm()}
            if rnd.random() < 0.5:
                d.add(rnd.choice(pool))
            g.deps[v] = sorted(d)
            g.sig[v] = [defs[s][int(len(defs[s]) * rnd.random() ** 2)]]
            g.deps[v] = sorted(set(g.deps[v]) | set(g.sig[v]))
            dead_tops[s].append(v)
            order[s].append((("orph", i // 6), v))

    # ---- the named spine (stage 0) ---------------------------------------------------
    for nm, kind, _, _ in SPINE:
        role = "stmt" if kind == "def" else "spine"
        by_name[nm] = g.add(nm, kind, 0, draw_lines(role), level=0, role=role)

    def resolve(tok):
        if tok.startswith("@"):
            k, i = tok[1:].split(":")
            s = [x.key for x in STAGES].index(k)
            iface_used.add(iface[s][int(i)])
            return iface[s][int(i)]
        return by_name[tok]
    for nm, kind, ds, sg in SPINE:
        v = by_name[nm]
        d = [resolve(t) for t in ds]
        if kind == "def":
            g.sig[v] = list(d)
        else:
            g.sig[v] = [resolve(t) for t in (sg or [])]
            d.append(pick_ml_thm())
        g.deps[v] = sorted(set(d) | set(g.sig[v]))
    # any entry point nobody picked gets one user in a cluster that is allowed to use it
    for t in range(1, S):
        users = [u for u in range(1, S) if t in STAGES[u].uses]
        for v in iface[t]:
            if v not in iface_used and users:
                u = rnd.choice(users)
                p = rnd.choice(levels[u][1])
                g.deps[p] = sorted(set(g.deps[p]) | {v})

    # ---- planted audit traps (all in DEAD code unless --plant-live-axiom) ---------------
    hy = [x.key for x in STAGES].index("Hyps")
    llc = [x.key for x in STAGES].index("LLC")
    trap_ax = g.add("Sim.LLC.Attempt0.assumed_local_bound", "axiom", llc, 1, role="dead_branch")
    order[llc].append((("dead", 0), trap_ax))
    b1, b2 = first_dead[hy], first_dead[llc]
    g.deps[b1[-1]] = sorted(set(g.deps[b1[-1]]) | {AX["sorryAx"]})
    g.deps[b2[-1]] = sorted(set(g.deps[b2[-1]]) | {trap_ax})
    g.deps[b2[0]] = sorted(set(g.deps[b2[0]]) | {AX["Lean.ofReduceBool"]})
    g.meta["planted_axioms"] = ["sorryAx", "Lean.ofReduceBool", "Sim.LLC.Attempt0.assumed_local_bound"]
    if plant_live_axiom:
        victim = levels[llc][STAGES[llc].depth][0]
        g.deps[victim] = sorted(set(g.deps[victim]) | {trap_ax})
        g.role[trap_ax] = "trap_live"

    # ---- compiler-generated auxiliaries (`_proof_1`, `match_1`): nodes without source lines ----
    n_before = g.n
    for v in range(n_before):
        if g.ext[v] or g.kind[v] != "thm" or g.grp[v] == 0 or rnd.random() >= 0.30:
            continue
        for j in range(rnd.choice((1, 1, 2))):
            a = g.add(g.name[v] + "._proof_%d" % (j + 1), "aux", g.grp[v], 0, level=g.level[v], role="aux")
            cand = [w for w in g.deps[v] if g.kind[w] != "aux"]
            g.deps[a] = sorted(set(rnd.sample(cand, min(len(cand), rnd.choice((1, 2))))))
            g.deps[v].append(a)
            g.mod[a] = -2 - v           # resolved to the parent's module below

    # ---- normalise source lines to the real total --------------------------------------
    target = REAL["lines"] * (n_decl / REAL["decls_kw"])
    cur = sum(g.lines[v] for v in range(g.n) if not g.ext[v])
    f = target / cur
    for v in range(g.n):
        if not g.ext[v] and g.lines[v]:
            g.lines[v] = max(1, int(round(g.lines[v] * f)))
    for k in list(g.tmpl_len):
        g.tmpl_len[k] = max(3, int(round(g.tmpl_len[k] * f)))

    # ---- modules (files) ------------------------------------------------------------
    dpf = REAL["decls_kw"] / REAL["files"]
    mod_id = {}

    def module(name):
        if name not in mod_id:
            mod_id[name] = len(g.mod_names); g.mod_names.append(name)
        return mod_id[name]
    for nm, _, _, _ in SPINE:
        g.mod[by_name[nm]] = module(SPINE_MODULE.get(nm, "Sim.Spine." + nm.replace(".", "_")))
    top_mods = [[] for _ in range(S)]
    for s in range(1, S):
        key, cnt, prev, cur_m, left = STAGES[s].key, 0, None, -1, 0
        for seg, v in order[s]:
            if seg != prev or left <= 0:
                sub = {"def": "Defs", "thm": "Lemmas", "dead": "Attempt", "orph": "Scratch"}[seg[0]]
                cur_m = module("Sim.%s.%s.P%03d.F%06d" % (key, sub, cnt // 200, cnt))
                cnt += 1
                left = 1 + int(rnd.expovariate(1.0 / max(0.5, dpf * CHUNK_FIT - 1)))
                prev = seg
                if seg[0] == "thm" and seg[1] <= 1:
                    top_mods[s].append(cur_m)
            g.mod[v] = cur_m; left -= 1
    for v in range(g.n):
        if g.mod[v] <= -2:
            g.mod[v] = g.mod[-2 - g.mod[v]]
    # leftover imports: the real tree has EVERY file in Main's import closure, dead or not
    for s in range(1, S):
        for v in dead_tops[s]:
            g.extra_imports.append((rnd.choice(top_mods[s]), g.mod[v]))
    g.meta.update(scale=scale, seed=seed, p_leak=p_leak, p_chain=p_chain, n_decl_target=n_decl, api=api_truth,
                  truth_dead=sum(1 for v in range(g.n) if g.role[v].startswith("dead")))
    g.by_name = by_name
    return g


# ======================================================================================
# Graph algorithms (all iterative: no recursion limits, usable at 10^6 nodes)
# ======================================================================================
def reach(starts, adj, n, blocked=None):
    """Forward reachability. Returns a bytearray mask."""
    seen = bytearray(n)
    stack = []
    for s in starts:
        if not seen[s] and not (blocked is not None and blocked[s]):
            seen[s] = 1; stack.append(s)
    while stack:
        for w in adj[stack.pop()]:
            if not seen[w] and not (blocked is not None and blocked[w]):
                seen[w] = 1; stack.append(w)
    return seen


def subgraph(g, live, include_ext=False, drop=None):
    """Adjacency of the live graph. By default library nodes are stripped ("strip libc first");
    `drop` is an optional mask of further nodes to remove (e.g. definitions)."""
    n, ext = g.n, g.ext
    adj = [()] * n
    radj = [[] for _ in range(n)]
    for v in range(n):
        if live[v] and (include_ext or not ext[v]) and not (drop is not None and drop[v]):
            lst = [w for w in g.deps[v] if (include_ext or not ext[w]) and not (drop is not None and drop[w])]
            adj[v] = lst
            for w in lst:
                radj[w].append(v)
    return adj, radj


def rpo_from(root, adj, n):
    """Reverse post-order of the DFS from root (a topological order when the graph is a DAG)."""
    seen = bytearray(n); seen[root] = 1
    post, stack, its = [], [root], [iter(adj[root])]
    while stack:
        for w in its[-1]:
            if not seen[w]:
                seen[w] = 1; stack.append(w); its.append(iter(adj[w]))
                break
        else:
            post.append(stack.pop()); its.pop()
    post.reverse()
    return post


def dominators(root, adj, radj, n):
    """Cooper-Harvey-Kennedy iterative dominators. idom[root] = root; -1 = unreachable.
    Works on cyclic graphs too (iterates to a fixpoint); on a DAG one pass is already exact."""
    rpo = rpo_from(root, adj, n)
    num = [-1] * n
    for i, v in enumerate(rpo):
        num[v] = i
    idom = [-1] * n
    idom[root] = root
    passes, changed = 0, True
    while changed:
        changed = False; passes += 1
        for v in rpo:
            if v == root:
                continue
            new = -1
            for p in radj[v]:
                if idom[p] == -1:
                    continue
                if new == -1:
                    new = p
                else:
                    a, b = p, new
                    while a != b:
                        while num[a] > num[b]:
                            a = idom[a]
                        while num[b] > num[a]:
                            b = idom[b]
                    new = a
            if idom[v] != new:
                idom[v] = new; changed = True
    return idom, rpo, num, passes


def dom_tree(g, idom, rpo, root):
    """Retained mass (lines / count dominated) and child lists of the dominator tree."""
    n = g.n
    rl, rc = [0] * n, [0] * n
    for v in rpo:
        rl[v] = g.lines[v]; rc[v] = 1
    kids = {}
    for v in reversed(rpo):          # a dominator always precedes what it dominates in RPO
        if v == root:
            continue
        p = idom[v]
        rl[p] += rl[v]; rc[p] += rc[v]
        kids.setdefault(p, []).append(v)
    return rl, rc, kids


def nearest_common_dominator(nodes, idom, num):
    it = iter(nodes)
    a = next(it)
    for b in it:
        while a != b:
            while num[a] > num[b]:
                a = idom[a]
            while num[b] > num[a]:
                b = idom[b]
    return a


def articulation(root, adj, radj, lines, n):
    """Iterative Tarjan on the UNDIRECTED view. Returns {ap: lines cut off from root},
    {ap: nodes cut off}, bridges[(parent, child)]. Assumes no antiparallel edge pairs (true for DAGs)."""
    disc, low, par = [0] * n, [0] * n, [-1] * n
    mass, cnt = [0] * n, [0] * n
    ap_mass, ap_cnt, bridges = {}, {}, []
    t = 1
    disc[root] = low[root] = 1; mass[root] = lines[root]; cnt[root] = 1
    stack, its = [root], [itertools.chain(adj[root], radj[root])]
    while stack:
        v = stack[-1]
        pushed = False
        for w in its[-1]:
            if disc[w] == 0:
                t += 1
                disc[w] = low[w] = t; par[w] = v; mass[w] = lines[w]; cnt[w] = 1
                stack.append(w); its.append(itertools.chain(adj[w], radj[w]))
                pushed = True
                break
            elif w != par[v] and disc[w] < low[v]:
                low[v] = disc[w]
        if pushed:
            continue
        stack.pop(); its.pop()
        if stack:
            p = stack[-1]
            mass[p] += mass[v]; cnt[p] += cnt[v]
            if low[v] < low[p]:
                low[p] = low[v]
            if low[v] >= disc[p] and p != root:
                ap_mass[p] = ap_mass.get(p, 0) + mass[v]
                ap_cnt[p] = ap_cnt.get(p, 0) + cnt[v]
            if low[v] > disc[p]:
                bridges.append((p, v))
    return ap_mass, ap_cnt, bridges


def path_flow(root, adj, rpo, n):
    """pf[v] = #paths root->v ; pt[v] = #paths v->(any sink). pf*pt/pt[root] = share of all
    root-to-sink dependency paths through v (exact source->sink betweenness on a DAG)."""
    pf, pt = [0] * n, [0] * n
    pf[root] = 1
    for v in rpo:
        x = pf[v]
        for w in adj[v]:
            pf[w] += x
    for v in reversed(rpo):
        a = adj[v]
        pt[v] = sum(pt[w] for w in a) if a else 1
    return pf, pt


def min_vertex_cut(src, targets, adj, n, region=None, kmax=64, radj=None):
    """Smallest set of vertices (!= src; targets allowed) whose removal disconnects src from
    every target. Unit vertex capacities, augmenting paths on the implicit split graph
    (state 2v = v_in, 2v+1 = v_out). Returns (k, cut_nearest_src, cut_nearest_targets).
    Minimum cuts are not unique: the first is the one closest to src, the second (needs radj)
    the one closest to the targets. (None, None, None) if k > kmax."""
    is_t = bytearray(n)
    for t in targets:
        is_t[t] = 1
    if is_t[src]:
        return 0, [], []
    touched = set()
    prv = [-1] * n            # prv[v] = u  <=>  one unit of flow on edge u->v (so v is saturated)
    sunk = bytearray(n)       # flow v->sink
    flow = 0
    while True:
        s0 = src * 2 + 1
        par = {s0: -1}
        stack, hit = [s0], -1
        while stack:
            s = stack.pop(); v = s >> 1
            if s & 1:                                   # at v_out
                if is_t[v] and not sunk[v]:
                    hit = s; break
                for w in adj[v]:
                    # edges have infinite capacity (only vertices are capacitated), so an edge that
                    # already carries flow stays traversable: w_in is then marked reachable, which is
                    # what makes the final cut read-out (v_in reached, v_out not) correct.
                    if w == src or (region is not None and not region[w]):
                        continue
                    ws = w * 2
                    if ws not in par:
                        par[ws] = s; stack.append(ws)
                if v != src and prv[v] != -1 and (s - 1) not in par:   # undo v's internal unit
                    par[s - 1] = s; stack.append(s - 1)
            else:                                       # at v_in
                nxt = s + 1 if prv[v] == -1 else prv[v] * 2 + 1       # free: go through; used: cancel inflow
                if nxt not in par:
                    par[nxt] = s; stack.append(nxt)
        if hit < 0:
            cut = [s >> 1 for s in par if not (s & 1) and (s + 1) not in par]
            near = None
            if radj is not None:              # states that can still reach the sink in the residual graph
                nxts = {}
                for v in touched:
                    if prv[v] != -1:
                        nxts.setdefault(prv[v], []).append(v)
                B, st = set(), []
                for t in targets:
                    if t * 2 + 1 not in B:
                        B.add(t * 2 + 1); st.append(t * 2 + 1)
                while st:
                    s = st.pop(); v = s >> 1
                    if s & 1:                               # predecessors of v_out
                        preds = [w * 2 for w in nxts.get(v, ())]
                        if v != src and prv[v] == -1:
                            preds.append(s - 1)
                    else:                                   # predecessors of v_in
                        preds = [u * 2 + 1 for u in radj[v]]
                        if prv[v] != -1:
                            preds.append(s + 1)
                    for p_ in preds:
                        if p_ not in B:
                            B.add(p_); st.append(p_)
                near = [s >> 1 for s in B if (s & 1) and (s - 1) not in B and (s >> 1) != src]
            return flow, cut, near
        path, s = [], hit
        while s != -1:
            path.append(s); s = par[s]
        path.reverse()
        cancels, adds = [], []
        for a, b in zip(path, path[1:]):
            va, vb = a >> 1, b >> 1
            if va == vb:
                continue                                # internal edge (use or undo): implied by prv
            if a & 1:
                adds.append((va, vb))                   # forward edge u_out -> w_in
            else:
                cancels.append((vb, va))                # v_in -> u_out cancels flow u->v
        for u, v in cancels:
            if prv[v] == u:
                prv[v] = -1
        for u, v in adds:
            prv[v] = u; touched.add(v)
        sunk[hit >> 1] = 1
        flow += 1
        if flow > kmax:
            return None, None, None


def chapter_curve(cands, idom, root, rl, ks):
    """Greedy maximum-mass antichain in the dominator tree: walk candidates by decreasing retained
    mass and take each one that is not already inside a taken chapter. (An ancestor can never come
    later: it retains strictly more.) Returns {k: (covered_lines, chapters, opened_ancestors)}."""
    picked, cov, out, ks = set(), 0, {}, set(ks)
    opened = set()
    order = []
    for v in cands:
        x, nested = idom[v], False
        while True:
            if x in picked:
                nested = True; break
            if x == root:
                break
            x = idom[x]
        if nested:
            continue
        picked.add(v); order.append(v); cov += rl[v]
        x = idom[v]
        while x not in opened:
            opened.add(x)
            if x == root:
                break
            x = idom[x]
        if len(picked) in ks:
            out[len(picked)] = (cov, list(order), set(opened))
            if len(picked) == max(ks):
                break
    return out


# ======================================================================================
# Text lab: synthetic tactic scripts, clone clustering, entropy, lexical red flags
# ======================================================================================
TAC = [
    "simp only [{L}, {M}] at {h} ⊢", "exact {L} {x} {h}", "rw [{L}] at {h}", "intro {x} {h}",
    "have {h} : {x} ≤ {n} * {y} := by", "  nlinarith [{L} {x}, {M} {y}]", "refine ⟨{x}, ?_, ?_⟩",
    "obtain ⟨{x}, {h}⟩ := {L} {y}", "apply {L}", "· exact {L}.trans ({M} {x})", "norm_num [{L}]",
    "linarith [{h}, {L} {x}]", "rcases {h} with ⟨{x}, {y}⟩ | {h}", "field_simp", "ring_nf", "positivity",
    "gcongr", "omega", "constructor", "ext {x}", "push_cast", "simp", "exact_mod_cast {h}",
    "by_cases {h} : {x} = {y}", "calc {x} = {y} := by ring", "  _ ≤ {n} := by norm_num", "funext {x}",
    "congr 1", "unfold {L}", "show {x} = {y}", "filter_upwards [{L}] with {x} {h}", "specialize {h} {x} {n}",
    "induction {x} with", "| zero => simp", "| succ {x} ih => simpa using ih", "apply le_trans ({L} {x})",
    "rw [← {L}, {M}]", "exact ⟨{h}, {L} {y}⟩", "simpa [{L}] using {h}", "refine le_of_lt ?_",
    "apply mul_pos {h} ({L} {x})", "rw [div_le_iff ({L} {x})]", "exact absurd {h} ({L} {y})",
    "have := {L} {x} {y} {h}", "subst {h}", "cases {x} with", "apply Finset.sum_le_sum", "intro {x} _",
    "rw [Finset.sum_comm]", "exact Nat.le_of_lt_succ {h}", "apply ContinuousOn.mono ({L} {x})",
    "exact (measure_mono {h}).trans ({L} {y})", "rw [integral_congr_ae {h}]", "aesop", "tauto", "decide",
]
KW = set("""simp only at exact rw intro have by nlinarith refine obtain apply norm_num linarith rcases with
field_simp ring_nf positivity gcongr omega constructor ext push_cast exact_mod_cast by_cases calc ring funext congr
unfold show filter_upwards specialize induction zero succ simpa using ih le_trans le_of_lt mul_pos div_le_iff absurd
this subst cases intros theorem lemma def instance structure fun trans aesop tauto decide import open namespace end
variable section noncomputable private protected abbrev class where match if then else do let in""".split())
_TOK = re.compile(r"[A-Za-z_][\w.'!?]*|\d+|\S")


def synth_doc(g, v, skew):
    """Deterministic fake tactic script for node v. Clone-family members share a shape."""
    t = g.tmpl[v]
    if t >= 0:
        L, rs = g.tmpl_len[t], random.Random(0x9E3779B1 * (t + 1))
    else:
        L, rs = max(2, min(120, g.lines[v])), random.Random(0x85EBCA6B * (v + 1) + 7)
    idx = [int(len(TAC) * rs.random() ** skew) for _ in range(L)]
    ri = random.Random(v * 7919 + 13)
    if t >= 0:
        for k in range(L):
            if ri.random() < 0.05:
                idx[k] = ri.randrange(len(TAC))
    ns = g.grp_names[g.grp[v]]
    out = ["theorem %s : stmt_%d := by" % (g.name[v], ri.randrange(10 ** 6))]
    for i in idx:
        out.append("  " + TAC[i].format(
            h="h%d" % ri.randrange(40), x="x%d" % ri.randrange(30), y="y%d" % ri.randrange(30),
            n=ri.randrange(2, 99), L="%s.lem_%d" % (ns, ri.randrange(9999)), M="aux_%d" % ri.randrange(9999)))
    return out


def normalize_line(line):
    """Alpha-rename: keep tactic keywords and punctuation, erase identifiers and literals."""
    out = []
    for t in _TOK.findall(line):
        c = t[0]
        if c.isdigit():
            out.append("0")
        elif c.isalpha() or c == "_":
            out.append(t if t in KW else "x")
        else:
            out.append(t)
    return " ".join(out)


_P = 4294967311
_COEF = [(2654435761, 1013904223), (40503, 12345), (2246822519, 3266489917),
         (374761393, 668265263), (1103515245, 2531011), (22695477, 1)]


def clone_clusters(norm_docs, thresh=0.4):
    """Type-2 clones (identical after renaming) + Type-3 near clones (min-hash bands, verified
    by exact Jaccard on 2-line shingles). Returns a cluster id per document."""
    n = len(norm_docs)
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x

    exact, shs = {}, []
    for i, doc in enumerate(norm_docs):
        key = hashlib.blake2b("\n".join(doc).encode("utf-8"), digest_size=8).digest()
        if key in exact:
            parent[find(i)] = find(exact[key])
        else:
            exact[key] = i
        if len(doc) >= 2:
            shs.append({zlib.crc32((doc[j] + "\n" + doc[j + 1]).encode("utf-8")) for j in range(len(doc) - 1)})
        else:
            shs.append({zlib.crc32(doc[0].encode("utf-8"))} if doc else set())
    buckets = {}
    for i, sh in enumerate(shs):
        if len(sh) < 4:
            continue
        for b, (a, c) in enumerate(_COEF):
            m = heapq.nsmallest(2, ((a * x + c) % _P for x in sh))
            buckets.setdefault((b, m[0], m[1]), []).append(i)
    for lst in buckets.values():
        if len(lst) < 2:
            continue
        reps = [lst[0]]
        for j in lst[1:]:
            ok = False
            for r in reps:
                if find(j) == find(r):
                    ok = True; break
                inter = len(shs[j] & shs[r])
                if inter / (len(shs[j]) + len(shs[r]) - inter) >= thresh:
                    parent[find(j)] = find(r); ok = True; break
            if not ok and len(reps) < 8:
                reps.append(j)
    return [find(i) for i in range(n)]


def clone_savings(cl, sizes):
    """Lines that are redundant given one exemplar per cluster."""
    by = collections.defaultdict(list)
    for i, c in enumerate(cl):
        by[c].append(sizes[i])
    dup = sum(sum(v) - max(v) for v in by.values() if len(v) > 1)
    multi = sum(len(v) for v in by.values() if len(v) > 1)
    return dup, multi, sum(1 for v in by.values() if len(v) > 1)


def pair_pr(pred, truth):
    """Pairwise precision / recall of a clustering against ground-truth classes."""
    c2 = lambda k: k * (k - 1) // 2
    cp, ct, cell = collections.Counter(pred), collections.Counter(truth), collections.Counter(zip(pred, truth))
    tp = sum(c2(k) for k in cell.values())
    pp, tt = sum(c2(k) for k in cp.values()), sum(c2(k) for k in ct.values())
    return (tp / pp if pp else 1.0), (tp / tt if tt else 1.0)


def line_entropy(norm_lines):
    c = collections.Counter(norm_lines)
    tot = sum(c.values())
    return -sum(k / tot * math.log2(k / tot) for k in c.values()) if tot else 0.0


RED_FLAGS = [   # lexical "YARA rules" for Lean. A hit is a lead, never a verdict.
    ("sorry/admit", r"\b(sorry|admit)\b"), ("axiom decl", r"^\s*(private\s+|protected\s+)?axiom\b"),
    ("native_decide", r"\bnative_decide\b|ofReduceBool|decide\s*\+native"),
    ("implemented_by/extern", r"implemented_by|@\[extern|\bcsimp\b"),
    ("unsafe/opaque/partial", r"^\s*(unsafe|opaque|partial)\b|\bunsafe\b"),
    ("kernel-bypass opts", r"skipKernelTC|debug\.|bootstrap\."), ("set_option", r"^\s*set_option\b"),
    ("meta: elab/macro/syntax", r"^\s*(scoped\s+|local\s+)?(elab|macro|syntax|macro_rules|elab_rules)\b"),
    ("meta: run_cmd/run_tac/#eval", r"\b(run_cmd|run_tac|run_elab)\b|^\s*#eval\b"),
    ("meta: addDecl/Environment", r"\baddDecl\b|addAndCompile|modifyEnv|setEnv"),
    ("notation (any)", r"^\s*(local\s+|scoped\s+)?(notation|infix[lr]?|prefix|postfix)\b"),
    ("local/scoped instance", r"^\s*(local|scoped)\s+instance\b|attribute\s*\[\s*-?\s*instance"),
    ("attribute [-...]", r"attribute\s*\[\s*-"), ("decide +kernel", r"decide\s*\+kernel|Nat\.decEq|by decide"),
    ("IO / process", r"\bIO\.(FS|Process|getEnv)\b"),
]
_RF = [(nm, re.compile(rx, re.M)) for nm, rx in RED_FLAGS]


# ======================================================================================
# Reporting helpers
# ======================================================================================
def hdr(title):
    print("\n" + "=" * 100 + "\n" + title + "\n" + "=" * 100)


def table(rows, head, align=None):
    cols = list(zip(*([head] + [[str(c) for c in r] for r in rows]))) if rows else [[h] for h in head]
    wd = [max(len(str(c)) for c in col) for col in cols]
    align = align or ["l"] + ["r"] * (len(head) - 1)
    fmt = lambda r: "  " + "  ".join(str(c).ljust(w) if a == "l" else str(c).rjust(w) for c, w, a in zip(r, wd, align))
    print(fmt(head)); print("  " + "  ".join("-" * w for w in wd))
    for r in rows:
        print(fmt(r))


def pct(a, b):
    return "%.1f%%" % (100.0 * a / b) if b else "n/a"


def short(name, k=62):
    return name if len(name) <= k else name[:k - 1] + "…"


# ======================================================================================
# The analysis session (shared by simulation and real-graph modes)
# ======================================================================================
def analyze(g, root_name, headline_names=None, truth=False, verbose=True, text_sample=12000, budget_scale=None):
    """Run passes 1-9. Returns a metrics dict. `truth` = graph carries simulation ground truth."""
    M = {}
    n = g.n
    idx = getattr(g, "by_name", None) or {nm: i for i, nm in enumerate(g.name)}
    if root_name not in idx:
        raise SystemExit("root %r not found" % root_name)
    root = idx[root_name]
    heads = [idx[h] for h in (headline_names or [root_name]) if h in idx]
    P = print if verbose else (lambda *a, **k: None)
    T = table if verbose else (lambda *a, **k: None)
    H = hdr if verbose else (lambda *a, **k: None)
    proj = [v for v in range(n) if not g.ext[v]]
    src = [v for v in proj if g.kind[v] != "aux"]
    tot_lines = sum(g.lines[v] for v in proj)
    n_groups = len(g.grp_names)

    # ---------------------------------------------------------------- pass 1
    H("PASS 1  Reachability / dead-code stripping  (root = %s)" % root_name)
    t0 = time.time()
    live = reach([root], g.deps, n)
    live_any = reach(heads, g.deps, n)
    live_src = [v for v in src if live[v]]
    live_lines = sum(g.lines[v] for v in live_src)
    dead_any = [v for v in src if not live_any[v]]
    M.update(nodes=n, project_constants=len(proj), source_decls=len(src), total_lines=tot_lines,
             live_decls=len(live_src), live_lines=live_lines, live_frac_decls=len(live_src) / max(1, len(src)),
             live_frac_lines=live_lines / max(1, tot_lines),
             only_other_headlines=sum(1 for v in src if live_any[v] and not live[v]))
    P("  constants in graph                 %10d   (project %d, of which compiler-generated aux %d; library %d)"
      % (n, len(proj), len(proj) - len(src), n - len(proj)))
    P("  source declarations                %10d   %12d lines" % (len(src), tot_lines))
    P("  live from %-24s %10d   %12d lines   (%s of decls, %s of lines)"
      % (root_name, len(live_src), live_lines, pct(len(live_src), len(src)), pct(live_lines, tot_lines)))
    P("  needed only by the other headlines %10d   (binary-diff of two entry points)" % M["only_other_headlines"])
    P("  dead w.r.t. ALL headline theorems  %10d   %12d lines   (%s of decls)"
      % (len(dead_any), sum(g.lines[v] for v in dead_any), pct(len(dead_any), len(src))))
    if truth:
        planted = set(v for v in src if g.role[v].startswith("dead"))
        got = set(dead_any)
        M["dead_recall"] = len(planted & got) / max(1, len(planted))
        P("  ground truth: planted dead recovered %d/%d ; plus %d accidentally-unused definitions the generator did not plan"
          % (len(planted & got), len(planted), len(got - planted)))
        assert planted <= got, "a planted dead declaration was reported live"
    rows = []
    for gi in range(n_groups):
        mem = [v for v in src if g.grp[v] == gi]
        if not mem:
            continue
        lv = [v for v in mem if live_any[v]]
        rows.append((g.grp_names[gi], len(mem), sum(g.lines[v] for v in mem), pct(len(lv), len(mem)),
                     pct(sum(g.lines[v] for v in lv), max(1, sum(g.lines[v] for v in mem)))))
    T(rows, ["cluster", "decls", "lines", "live decls", "live lines"])
    # module level: what an import-graph tool would conclude
    if g.mod_names:
        nm_ = len(g.mod_names)
        madj = [set() for _ in range(nm_)]
        for v in proj:
            mv = g.mod[v]
            for w in g.deps[v]:
                if not g.ext[w] and g.mod[w] != mv:
                    madj[mv].add(g.mod[w])
        used_edges = sum(len(s) for s in madj)
        for a, b in g.extra_imports:
            madj[a].add(b)
        mreach = reach([g.mod[root]], madj, nm_)
        mod_live = bytearray(nm_)
        for v in src:
            if live_any[v]:
                mod_live[g.mod[v]] = 1
        M.update(modules=nm_, modules_import_reachable=sum(mreach), modules_with_live_decl=sum(mod_live),
                 module_edges=sum(len(s) for s in madj))
        P("\n  FILE-LEVEL VIEW (what `import` lines alone can tell you)")
        P("    files                                   %8d" % nm_)
        P("    in the import closure of the root file  %8d  (%s)   <- an import-graph tool calls all of these live"
          % (sum(mreach), pct(sum(mreach), nm_)))
        P("    files holding >= 1 live declaration     %8d  (%s)   <- declaration-level truth"
          % (sum(mod_live), pct(sum(mod_live), nm_)))
        P("    => import reachability over-states the live file set by %.2fx" % (sum(mreach) / max(1, sum(mod_live))))
    P("  [%.2fs]" % (time.time() - t0))

    # ---------------------------------------------------------------- pass 2
    H("PASS 2  Axiom footprint: reachability, not grep")
    ax_all = [v for v in range(n) if g.kind[v] == "axiom"]
    used_anywhere = set()
    for v in range(n):
        for w in g.deps[v]:
            if g.kind[w] == "axiom":
                used_anywhere.add(w)
    fp = sorted(g.name[v] for v in ax_all if live[v])
    fp_any = sorted(g.name[v] for v in ax_all if live_any[v])
    M.update(axioms_in_env=len(ax_all), axiom_footprint=fp, axiom_footprint_all_headlines=fp_any)
    P("  axioms present in the environment      : %d  %s" % (len(ax_all), sorted(g.name[v] for v in ax_all)))
    P("  axioms referenced by SOME declaration  : %d  %s" % (len(used_anywhere), sorted(g.name[v] for v in used_anywhere)))
    P("  axioms reachable from %-17s: %d  %s" % (root_name, len(fp), fp))
    P("  axioms reachable from all headlines    : %d  %s" % (len(fp_any), fp_any))
    if truth:
        std = ["Classical.choice", "Quot.sound", "propext"]
        ok = (fp_any == std) or bool(g.meta.get("plant_live"))
        P("  ground truth: %d traps planted in dead code %s -> footprint %s"
          % (len(g.meta["planted_axioms"]), g.meta["planted_axioms"], "CLEAN (standard three only)" if fp_any == std else "CONTAMINATED"))
        assert ok, "axiom footprint should be exactly the standard three"

    # ---------------------------------------------------------------- pass 3
    H("PASS 3  Statement closure = semantic TCB  (what must be trusted to know WHAT was proved)")
    cone = reach(list(g.sig[root]), g.deps, n)
    cone_all = reach([w for h in heads for w in g.sig[h]], g.deps, n)
    c_all = [v for v in range(n) if cone_all[v]]
    c_proj = [v for v in c_all if not g.ext[v]]
    c_defs = [v for v in c_all if g.kind[v] in ("def", "inst")]
    M.update(cone_root=sum(cone), cone_all=len(c_all), cone_project=len(c_proj), cone_defs=len(c_defs))
    P("  closure of the statement of %-22s: %7d declarations (%d project-defined)"
      % (root_name, sum(cone), sum(1 for v in range(n) if cone[v] and not g.ext[v])))
    P("  closure of all %d headline statements           : %7d declarations (%d project-defined: %s)"
      % (len(heads), len(c_all), len(c_proj), [g.name[v] for v in c_proj][:6]))
    P("     of which definitions/instances (carry meaning): %6d ; theorems inside definitions (kernel-checked): %d"
      % (len(c_defs), len(c_all) - len(c_defs)))
    P("  proof closure (everything live incl. library)    : %7d declarations" % sum(live_any))
    P("  => WHAT-was-proved surface is %s of the WHY-it-is-true surface" % pct(len(c_all), sum(live_any)))

    # ---------------------------------------------------------------- pass 4
    H("PASS 4  Dominator tree: mandatory chokepoints and retained proof mass")
    t0 = time.time()
    adj, radj = subgraph(g, live)
    idom, rpo, num, passes = dominators(root, adj, radj, n)
    rl, rc, kids = dom_tree(g, idom, rpo, root)
    nontriv = [v for v in rpo if v in kids]
    edges = sum(len(adj[v]) for v in rpo)
    M.update(live_project_nodes=len(rpo), live_project_edges=edges, dominators_nontrivial=len(nontriv))
    P("  live project subgraph: %d nodes, %d edges (library stripped); CHK converged in %d passes  [%.2fs]"
      % (len(rpo), edges, passes, time.time() - t0))
    P("  declarations that dominate at least one other declaration: %d (%s)" % (len(nontriv), pct(len(nontriv), len(rpo))))
    sizes = collections.Counter()
    for c in kids.get(root, []):
        pass
    # trunk: follow the unique heavy child while it retains > 90% of its parent
    trunk_chain, v = [root], root
    while True:
        ks = kids.get(v, [])
        if not ks:
            break
        h = max(ks, key=lambda c: rl[c])
        if rl[h] < 0.9 * (rl[v] - g.lines[v]):
            break
        trunk_chain.append(h); v = h
    M["trunk_chain"] = [g.name[x] for x in trunk_chain]
    P("\n  TRUNK (each retains >90% of its parent's mass -- the proof's `main()` call chain):")
    for x in trunk_chain:
        P("    %-66s retains %s of live lines" % (short(g.name[x]), pct(rl[x], live_lines)))
    fork = trunk_chain[-1]
    # distribution of top-level components under the fork, as drew2apps did at file level
    comp = sorted(((rc[c], rl[c], c) for c in kids.get(fork, [])), reverse=True)
    buckets = [("1000+", 1000, 10 ** 12), ("100-999", 100, 1000), ("10-99", 10, 100), ("2-9", 2, 10), ("1 (shared)", 1, 2)]
    rows = []
    for nm, lo, hi in buckets:
        sel = [(a, b) for a, b, _ in comp if lo <= a < hi]
        rows.append((nm, len(sel), sum(a for a, _ in sel), pct(sum(a for a, _ in sel), len(rpo)),
                     pct(sum(b for _, b in sel), live_lines)))
    M["fork"] = g.name[fork]
    M["fork_components"] = {r[0]: {"components": r[1], "decls": r[2]} for r in rows}
    P("\n  SINGLE-ENTRY COMPONENTS directly under the fork `%s`:" % short(g.name[fork], 50))
    T(rows, ["component size (decls)", "components", "decls", "share of decls", "share of lines"])
    top = sorted((v for v in nontriv if v not in set(trunk_chain)), key=lambda v: -rl[v])[:18]
    P("\n  TOP DOMINATORS by retained lines (understand the STATEMENT, black-box everything it retains):")
    T([(short(g.name[v]), g.grp_names[g.grp[v]], rc[v], rl[v], pct(rl[v], live_lines), len(radj[v]),
        short(g.name[idom[v]], 34)) for v in top],
      ["declaration", "cluster", "dominates", "retained lines", "of live", "fan-in", "immediate dominator"],
      ["l", "l", "r", "r", "r", "r", "l"])
    rows, M["frontier"] = [], {}
    cap = 0.25 * live_lines
    cands = sorted((v for v in nontriv if rl[v] <= cap), key=lambda v: (-rl[v], num[v]))
    KS = (10, 30, 100, 300, 1000, 3000)
    curve = chapter_curve(cands, idom, root, rl, KS)
    spine_trunk, spine_front = [root], []
    for k in KS:
        if k not in curve:
            continue
        cov, ch, op = curve[k]
        own = sum(g.lines[v] for v in op)
        rows.append((k, pct(cov, live_lines), pct(rl[ch[-1]], live_lines), len(op), own, pct(live_lines - cov - own, live_lines)))
        M["frontier"][k] = dict(coverage=cov / max(1, live_lines), opened=len(op), opened_lines=own,
                                smallest=rl[ch[-1]] / max(1, live_lines))
        if k == 100:
            spine_trunk, spine_front = sorted(op), ch
    P("\n  CHAPTER CURVE: the k heaviest disjoint single-entry sub-proofs (each capped at 25% of the proof).")
    P("  'If I read k statements and trust the kernel for what is behind them, how much proof disappears?'")
    T(rows, ["k statements", "lines black-boxed", "smallest chapter", "ancestors to read in full", "their lines",
             "residue: shared / multi-entry"])
    P("  reading: 'residue' is code reached along several independent paths -- no single statement owns it.")
    P("  It is what dominators alone cannot package; pass 7 packages it with entry SETS (multi-entry modules).")

    # ---------------------------------------------------------------- pass 5
    H("PASS 5  Articulation points & bridges (undirected view)")
    t0 = time.time()
    ap_mass, ap_cnt, bridges = articulation(root, adj, radj, g.lines, n)
    aps_ok = all(v in kids for v in ap_mass)        # theorem: root-separating APs are dominators
    P("  library stripped : %d articulation points, %d bridge edges  [%.2fs]" % (len(ap_mass), len(bridges), time.time() - t0))
    P("  check: every root-separating articulation point is a non-trivial dominator -> %s" % aps_ok)
    assert aps_ok
    big_ap = sum(1 for v in ap_mass if ap_cnt[v] >= 10)
    big_dom = sum(1 for v in nontriv if rc[v] - 1 >= 10)
    M.update(aps=len(ap_mass), bridges=len(bridges), aps_ge10=big_ap, doms_ge10=big_dom)
    rows = [("library stripped (default view)", len(ap_mass), big_ap)]
    if True:
        fadj, fradj = subgraph(g, live, include_ext=True)
        ap2, apc2, _ = articulation(root, fadj, fradj, g.lines, n)
        big2 = sum(1 for v in ap2 if apc2[v] >= 10 and not g.ext[v])
        rows.insert(0, ("library included", len(ap2), big2))
        M.update(aps_with_lib=len(ap2), aps_ge10_with_lib=big2)
        del fadj, fradj
        drop = bytearray(n)
        for v in range(n):
            if g.kind[v] in ("def", "inst"):
                drop[v] = 1
        tadj, tradj = subgraph(g, live, drop=drop)
        ap3, apc3, _ = articulation(root, tadj, tradj, g.lines, n)
        big3 = sum(1 for v in ap3 if apc3[v] >= 10)
        rows.append(("library + definitions stripped (theorem->theorem only)", len(ap3), big3))
        M.update(aps_thm_only=len(ap3), aps_ge10_thm_only=big3)
        del tadj, tradj
    T(rows, ["undirected view", "articulation points", "guarding >= 10 decls"])
    P("  directed dominators guarding >= 10 declarations: %d" % big_dom)
    P("  => shared vocabulary (library lemmas, then in-repo definitions) welds the undirected graph into one")
    P("     biconnected blob; chokepoints only exist once edge DIRECTION is respected. Use dominators.")

    # ---------------------------------------------------------------- pass 6
    H("PASS 6  Path-flow centrality: utility hubs vs structural chokepoints")
    pf, pt = path_flow(root, adj, rpo, n)
    total = pt[root]
    flow = {v: pf[v] * pt[v] for v in rpo}
    cand = sorted((v for v in rpo if v != root), key=lambda v: -flow[v])[:400]
    M["root_to_sink_paths_log10"] = math.log10(total) if total else 0
    P("  distinct root->leaf dependency paths: about 10^%.1f" % M["root_to_sink_paths_log10"])
    choke = [v for v in cand if rl[v] > 0.005 * live_lines]
    hubs = [v for v in cand if rl[v] <= 0.005 * live_lines][:10]
    P("  of the 400 highest path-flow declarations, %d also retain > 0.5%% of the proof (true chokepoints)." % len(choke))
    P("  the rest are utility hubs -- on everybody's path, owning nothing:")
    T([(short(g.name[v]), g.grp_names[g.grp[v]], "%.4f" % (flow[v] / total), len(radj[v]), pct(rl[v], live_lines)) for v in hubs],
      ["highest path-flow declarations that are NOT chokepoints", "cluster", "share of all paths", "fan-in", "retained"],
      ["l", "l", "r", "r", "r"])
    fan = sorted((v for v in rpo), key=lambda v: -len(radj[v]))[:5]
    P("  highest fan-in (the `memcpy`s of the proof): " + ", ".join("%s(%d)" % (short(g.name[v], 28), len(radj[v])) for v in fan))
    n_hub = sum(1 for v in cand[:200] if rl[v] <= 0.005 * live_lines)
    M["top200_pathflow_that_are_hubs"] = n_hub
    P("  of the 200 highest path-flow declarations, %d retain < 0.5%% of the proof: centrality finds plumbing, retained mass finds ideas." % n_hub)

    # ---------------------------------------------------------------- pass 7
    H("PASS 7  Export tables & min vertex cuts: how encapsulated is each cluster?")
    t0 = time.time()
    is_entry = bytearray(n)
    for v in rpo:
        gv = g.grp[v]
        for w in adj[v]:
            if g.grp[w] != gv:
                is_entry[w] = 1
    rows, M["clusters"] = [], {}
    for gi in range(n_groups):
        mem = [v for v in rpo if g.grp[v] == gi]
        ent = [v for v in mem if is_entry[v]]
        if not mem or not ent or g.grp[root] == gi:
            continue
        blocked = bytearray(n)
        for v in ent:
            blocked[v] = 1
        r = reach([root], adj, n, blocked)
        excl = live_lines - sum(g.lines[v] for v in rpo if r[v])
        ncd = nearest_common_dominator(ent, idom, num)
        if is_entry[ncd] and g.grp[ncd] == gi:
            k, cut_desc, own_waist = 1, "1 = single entry", True
        else:
            region = reach(ent, radj, n)
            k, _, cut = min_vertex_cut(ncd, ent, adj, n, region=region, kmax=64, radj=radj)
            if k is None:
                cut_desc, own_waist = "> 64", False
            else:
                by = collections.Counter(g.grp_names[g.grp[v]] for v in cut)
                own_waist = by.get(g.grp_names[gi], 0) == k
                cut_desc = "%d = %s%s" % (k, "+".join("%d %s" % (c, nm) for nm, c in by.most_common(3)),
                                          "" if own_waist else "  (upstream: cluster itself has no narrow waist)")
        declared = sum(1 for v in mem if v in g.meta["api"]) if truth else "-"
        heavy = sum(1 for v in ent if rl[v] >= 0.002 * live_lines)
        e_thm = sum(1 for v in ent if g.kind[v] not in ("def", "inst"))
        rows.append((g.grp_names[gi], len(mem), e_thm, len(ent) - e_thm, declared, heavy, pct(len(ent), len(mem)),
                     short(g.name[ncd], 36), cut_desc))
        M["clusters"][g.grp_names[gi]] = dict(live=len(mem), entries=len(ent), thm_entries=e_thm, exclusive_frac=excl / max(1, live_lines),
                                             waist=k, own_waist=own_waist, ncd=g.name[ncd])
    T(rows, ["cluster", "live decls", "thm entries", "def entries", "designed thm API", "heavy entries",
             "interface width", "nearest common dominator", "min vertex cut below it (target-side)"],
      ["l", "r", "r", "r", "r", "r", "r", "l", "l"])
    n_ent = sum(c["entries"] for c in M["clusters"].values())
    n_live_c = sum(c["live"] for c in M["clusters"].values())
    M["interface_width"] = n_ent / max(1, n_live_c)
    M["entries_total"] = n_ent
    P("  entries = declarations referenced from outside their cluster: the export table actually in use.")
    P("  'designed thm API' = what the generator intended to be public; thm entries beyond it are leaks.")
    P("  'interface width' = entries / live declarations: the share of a cluster's statements you must read")
    P("  to treat the whole cluster as a black box (an entry SET is a multi-node dominator of the cluster).")
    P("  overall: reading %d entry statements (%s of live declarations) black-boxes every cluster below the spine;"
      % (n_ent, pct(n_ent, n_live_c)))
    P("  the best 100 SINGLE dominators black-box only %s. Multi-entry modules need entry sets, not dominators."
      % pct(M["frontier"].get(100, {}).get("coverage", 0), 1))
    P("  'heavy entries' = entries that themselves retain >= 0.2%% of the proof (API you must read; the rest are leaks).  [%.2fs]"
      % (time.time() - t0))

    # ---------------------------------------------------------------- pass 8
    f_clone = 0.0
    if truth:
        H("PASS 8  Clone clustering & entropy  (SYNTHETIC text: proves the pipeline, says nothing about the real corpus)")
        t0 = time.time()
        rs = random.Random(SEED + 8)
        thm_live = [v for v in rpo if g.kind[v] == "thm" and g.grp[v] != 0]
        sample = []
        if len(thm_live) <= text_sample:
            sample = thm_live[:]
        else:
            thm_live.sort()
            while len(sample) < text_sample:           # contiguous windows keep clone families intact
                s = rs.randrange(len(thm_live) - 400)
                sample.extend(thm_live[s:s + 400])
            sample = sorted(set(sample))
        raw = {v: synth_doc(g, v, STAGES[g.grp[v]].skew) for v in sample}
        norm = [[normalize_line(x) for x in raw[v][1:]] for v in sample]
        cl = clone_clusters(norm)
        sizes_ = [len(raw[v]) - 1 for v in sample]
        dup, multi, ncl = clone_savings(cl, sizes_)
        truth_lbl = [g.tmpl[v] if g.tmpl[v] >= 0 else -1 - v for v in sample]
        prec, rec = pair_pr(cl, truth_lbl)
        f_clone = dup / max(1, sum(sizes_))
        M.update(clone_precision=prec, clone_recall=rec, clone_frac_lines=f_clone, clone_clusters=ncl)
        P("  sample: %d live theorems, %d script lines" % (len(sample), sum(sizes_)))
        P("  clusters with >= 2 members: %d covering %d theorems; redundant lines given one exemplar each: %s"
          % (ncl, multi, pct(dup, sum(sizes_))))
        P("  against planted families: pairwise precision %.3f, recall %.3f  (true redundant share: %s)"
          % (prec, rec, pct(sum(s for s, t in zip(sizes_, truth_lbl) if t >= 0) -
                            sum(max(s for s, t2 in zip(sizes_, truth_lbl) if t2 == t) for t in set(t for t in truth_lbl if t >= 0)),
                            sum(sizes_))))
        rows = []
        for gi in range(1, len(STAGES)):
            vs = [v for v in sample if g.grp[v] == gi]
            if not vs:
                continue
            blob = "\n".join("\n".join(raw[v]) for v in vs).encode("utf-8")
            nl = [x for v in vs for x in (normalize_line(y) for y in raw[v][1:])]
            nb = "\n".join(nl).encode("utf-8")
            rows.append((g.grp_names[gi], len(vs), "%.3f" % (len(zlib.compress(blob, 6)) / len(blob)),
                         "%.3f" % (len(zlib.compress(nb, 6)) / len(nb)), "%.2f" % line_entropy(nl), "%.2f" % STAGES[gi].skew))
        T(rows, ["cluster", "sampled thms", "zlib ratio raw", "zlib ratio renamed", "tactic-line entropy (bits)", "planted skew"])
        P("  lower ratio / entropy = more boilerplate = cheaper to summarise by exemplar.  [%.2fs]" % (time.time() - t0))

    # ---------------------------------------------------------------- pass 9
    H("PASS 9  Decompilation budget (projected to the REAL corpus size)")
    lf_lines = live_lines / max(1, tot_lines)
    sp = set(spine_trunk) | set(spine_front)
    for gi in range(n_groups):
        ent = sorted((v for v in rpo if is_entry[v] and g.grp[v] == gi and not g.ext[v]),
                     key=lambda v: -sum(1 for u in radj[v] if g.grp[u] != gi))[:10]
        sp.update(ent)
    sp_lines = sum(g.lines[v] for v in sp)
    sp_deps = sum(len(g.deps[v]) for v in sp)
    R_lines = REAL["lines"] if budget_scale else tot_lines
    R_files = REAL["files"] if budget_scale else max(1, len(g.mod_names) or len(src) // 6)
    R_decls = REAL["decls_kw"] if budget_scale else len(src)
    live_file_frac = (M.get("modules_with_live_decl", 0) / M["modules"]) if M.get("modules") else lf_lines
    avg_deps = sum(len(g.deps[v]) for v in src) / max(1, len(src))
    cone_defs_real = REAL["challenge_decls"] * (len(c_defs) / max(1, len(c_all))) if budget_scale else len(c_defs)

    def bulk(lines, files, decls):
        calls = files
        tin = lines * TOK_PER_LINE + decls * avg_deps * DEP_STMT_TOK * 0.5 + files * PROMPT_TOK
        tout = decls * CARD_OUT + files * MOD_OUT
        lvl = files
        while lvl > 1:                                   # roll-up pyramid
            lvl = math.ceil(lvl / DIR_FAN)
            calls += lvl; tin += lvl * (DIR_FAN * MOD_OUT + PROMPT_TOK); tout += lvl * DIR_OUT
        qa = QA_SAMPLE * files
        calls += qa; tin += QA_SAMPLE * (lines * TOK_PER_LINE + files * PROMPT_TOK) * 2; tout += qa * MOD_OUT
        return calls, tin, tout
    strat = []
    strat.append(("S0 read everything, bottom-up", "economy") + bulk(R_lines, R_files, R_decls))
    strat.append(("S1 dead-stripped (live cone only)", "economy")
                 + bulk(R_lines * lf_lines, R_files * live_file_frac, R_decls * M["live_frac_decls"]))
    strat.append(("S2 S1 + clones read as diffs", "economy")
                 + bulk(R_lines * lf_lines * (1 - f_clone * (1 - DIFF_FRAC)), R_files * live_file_frac,
                        R_decls * M["live_frac_decls"]))
    live_decls_real = R_decls * M["live_frac_decls"]
    sig_in = live_decls_real * SIG_LINES * TOK_PER_LINE
    sig_calls = math.ceil(sig_in / (CTX_WINDOW * 0.5))
    strat.append(("S2b signatures only: every live statement, no proofs", "mid", sig_calls,
                  sig_in + sig_calls * PROMPT_TOK, live_decls_real * 40))
    sp_in = sp_lines * TOK_PER_LINE + sp_deps * DEP_STMT_TOK + len(sp) * PROMPT_TOK
    strat.append(("S3 spine-first (%d decls) + 3 adversarial verifiers" % len(sp), "frontier",
                  len(sp) * 4, sp_in * 4, len(sp) * SPINE_OUT * 4))
    if 1000 in curve:
        sp2 = set(curve[1000][1]) | curve[1000][2] | sp
        sp2_in = sum(g.lines[v] for v in sp2) * TOK_PER_LINE + sum(len(g.deps[v]) for v in sp2) * DEP_STMT_TOK + len(sp2) * PROMPT_TOK
        strat.append(("S3b second layer (%d decls) + 3 verifiers" % len(sp2), "frontier", len(sp2) * 4, sp2_in * 4,
                      len(sp2) * SPINE_OUT * 4))
    cone_in = cone_defs_real * 15 * TOK_PER_LINE
    strat.append(("S4 statement-closure audit (~%d defs*) x 3 auditors" % round(cone_defs_real), "frontier",
                  3 * math.ceil(cone_in / (CTX_WINDOW * 0.5)), cone_in * 3, 3 * 0.05 * cone_in))
    rows = []
    M["budget"] = {}
    for name, tier, calls, tin, tout in strat:
        cost = {k: (tin * p[0] + tout * p[1]) / 1e6 for k, p in PRICES.items()}
        rows.append((name, "%d" % calls, "%.1f" % (tin / 1e6), "%.1f" % (tout / 1e6),
                     "$%s" % format(round(cost["economy"]), ","), "$%s" % format(round(cost["mid"]), ","),
                     "$%s" % format(round(cost["frontier"]), ","), tier,
                     "%.1f" % (calls * CALL_SECONDS / PARALLEL / 3600), "%.0f" % (tin / CTX_WINDOW)))
        M["budget"][name] = dict(calls=calls, in_tok=tin, out_tok=tout, cost=cost, tier=tier)
    P("  assumptions: %.1f tokens/line (%.1f bytes/line real, %.1f bytes/token ASSUMED); context %dk; %d parallel calls of %ds;"
      % (TOK_PER_LINE, REAL["bytes"] / REAL["lines"], BYTES_PER_TOKEN, CTX_WINDOW // 1000, PARALLEL, CALL_SECONDS))
    P("  prices are ILLUSTRATIVE $/Mtok (in,out): %s. Live/clone/spine fractions come from THIS graph." % PRICES)
    T(rows, ["strategy", "calls", "in Mtok", "out Mtok", "economy", "mid", "frontier", "sensible tier", "wall h", "200k windows"])
    P("  * definition share of the 51,692-declaration statement closure is ASSUMED (45%); measure it from challenge.ndjson.")
    P("  human baseline: %s lines at 150 lines/hour of careful reading = %.0f person-years; the spine alone = %.0f hours."
      % (format(R_lines, ","), R_lines / 150 / 2000, sp_lines / 150))
    M.update(spine_decls=len(sp), spine_lines=sp_lines)

    # spine tree for visualisation
    keep = set(trunk_chain) | set(spine_trunk) | set(sorted(spine_front, key=lambda v: -rl[v])[:120])
    M["spine_tree"] = [dict(name=g.name[v], parent=(g.name[idom[v]] if v != root else None), cluster=g.grp_names[g.grp[v]],
                            retained_frac=round(rl[v] / max(1, live_lines), 5), dominates=rc[v], fan_in=len(radj[v]),
                            lines=g.lines[v]) for v in sorted(keep, key=lambda v: num[v])]
    return M


# ======================================================================================
# Real-data ingest
# ======================================================================================
def dump_jsonl(g, path):
    with open(path, "w", encoding="utf-8") as f:
        for v in range(g.n):
            f.write(json.dumps({"name": g.name[v], "kind": g.kind[v], "ext": bool(g.ext[v]), "lines": g.lines[v],
                                "module": g.mod_names[g.mod[v]] if g.mod[v] >= 0 else g.grp_names[g.grp[v]],
                                "deps": [g.name[w] for w in g.deps[v]], "sig": [g.name[w] for w in g.sig[v]]},
                               ensure_ascii=False) + "\n")


def load_jsonl(path, group_depth=1):
    g = PG()
    recs = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            if line.strip():
                recs.append(json.loads(line))
    idx, gid, mid = {}, {}, {}
    for r in recs:
        mod = r.get("module", "")
        grp = "Mathlib" if r.get("ext") else ".".join(mod.split(".")[:group_depth]) or "?"
        if grp not in gid:
            gid[grp] = len(g.grp_names); g.grp_names.append(grp)
        v = g.add(r["name"], r.get("kind", "thm"), gid[grp], int(r.get("lines", 0)), ext=bool(r.get("ext")))
        if mod not in mid:
            mid[mod] = len(g.mod_names); g.mod_names.append(mod)
        g.mod[v] = mid[mod]
        idx[r["name"]] = v
    for v, r in enumerate(recs):
        g.deps[v] = sorted({idx[d] for d in r.get("deps", []) if d in idx and idx[d] != v})
        g.sig[v] = sorted({idx[d] for d in r.get("sig", []) if d in idx and idx[d] != v})
    if not any(g.lines):                 # no source-line info (e.g. dumped from an Environment):
        for v in range(g.n):             # fall back to "1 per declaration" so retained mass = count
            if not g.ext[v] and g.kind[v] != "aux":
                g.lines[v] = 1
    g.by_name = idx
    return g


_IMPORT = re.compile(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\s]+)")
_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
                   r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\b", re.M)


_OPEN, _CLOSE = "([{⦃⟨", ")]}⦄⟩"
_REL = re.compile(r"[=<>≤≥≠∧∨→↔∀∃¬∈∣]")
_HEAD = re.compile(r"[A-Za-z_][\w.'₀-₉]*")


def _named_prop(ty):
    """Head constant if `ty` looks like an application of a NAMED proposition (no top-level
    relation/connective), else None. `Nonempty (X ..)` is unwrapped to X."""
    ty = ty.strip()
    m = _HEAD.match(ty)
    if not m:
        return None
    head, rest = m.group(0), ty[m.end():]
    if head == "Nonempty":
        return _named_prop(rest.strip().lstrip("(")) or None
    flat, depth = [], 0
    for ch in rest.replace("=>", "  "):
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif depth == 0:
            flat.append(ch)
    if _REL.search("".join(flat)) or not head[0].isupper() or not head.split(".")[-1][:1].isupper():
        return None
    return head


def horn_skeleton(text):
    """Heuristic, TEXT-LEVEL extraction of `theorem T (h : A) (h' : B) : C` as the Horn clause
    A & B => C over named propositions. (The exact version walks binder types in the kernel term.)
    Returns [(theorem, [named hypotheses], n_unnamed_hypotheses, named conclusion or None)]."""
    out = []
    for m in re.finditer(r"^(?:theorem|lemma)\s+(\S+)", text, re.M):
        i, depth, binders, cur, concl = m.end(), 0, [], [], None
        n = len(text)
        while i < n:                                   # binders, up to the top-level ':'
            ch = text[i]
            if ch in _OPEN:
                depth += 1
            if depth > 0:
                cur.append(ch)
            if ch in _CLOSE:
                depth -= 1
                if depth == 0:
                    binders.append("".join(cur)); cur = []
            elif depth == 0 and ch == ":":
                break
            i += 1
        j, depth = i + 1, 0
        while j < n:                                   # conclusion, up to the top-level ':='
            ch = text[j]
            if ch in _OPEN:
                depth += 1
            elif ch in _CLOSE:
                depth -= 1
            elif depth == 0 and text.startswith(":=", j):
                break
            j += 1
        concl = _named_prop(text[i + 1:j])
        hyps, unnamed = [], 0
        for b in binders:
            if b[0] != "(" or ":" not in b:
                continue
            names, ty = b[1:-1].split(":", 1)
            if not all(x.startswith("h") for x in names.split()):
                continue                               # Lean convention: hypotheses are named h*
            a = _named_prop(ty)
            if a:
                hyps.append(a)
            else:
                unnamed += 1
        out.append((m.group(1), hyps, unnamed, concl))
    return out


def load_lean_dir(root_dir, group_depth=1):
    """Module-level graph from a real Lean source tree. Nodes = files, edges = imports."""
    g = PG()
    files = []
    for dp, dn, fn in os.walk(root_dir):
        dn[:] = sorted(d for d in dn if d not in (".lake", ".git", "build"))
        for f in sorted(fn):
            if f.endswith(".lean"):
                files.append(os.path.join(dp, f))
    idx, texts, imports, gid = {}, {}, {}, {}
    for p in files:
        mod = os.path.relpath(p, root_dir)[:-5].replace(os.sep, ".")
        with open(p, encoding="utf-8", errors="replace") as f:
            txt = f.read()
        grp = ".".join(mod.split(".")[:group_depth])
        if grp not in gid:
            gid[grp] = len(g.grp_names); g.grp_names.append(grp)
        v = g.add(mod, "module", gid[grp], txt.count("\n") + (0 if txt.endswith("\n") or not txt else 1))
        g.mod_names.append(mod); g.mod[v] = v
        idx[mod] = v; texts[v] = txt
        imports[v] = [m.group(1) for m in (_IMPORT.match(l) for l in txt.split("\n")) if m]
    lib = len(g.grp_names); g.grp_names.append("(external)")
    dup = 0
    for v, imps in imports.items():
        dup += len(imps) - len(set(imps))
        ds = set()
        for m in imps:
            if m not in idx:
                idx[m] = g.add(m, "module", lib, 0, ext=True)
            ds.add(idx[m])
        g.deps[v] = sorted(ds)
    g.by_name = idx
    g.meta["duplicate_imports"] = dup
    return g, texts


def analyze_lean_dir(path, root_name, group_depth, verbose=True):
    """File-granularity session on a real tree: reachability, dominators, clones, entropy, red flags."""
    P = print if verbose else (lambda *a, **k: None)
    g, texts = load_lean_dir(path, group_depth)
    n = g.n
    proj = [v for v in range(n) if not g.ext[v]]
    if root_name not in g.by_name:
        raise SystemExit("root module %r not found under %s" % (root_name, path))
    root = g.by_name[root_name]
    live = reach([root], g.deps, n)
    adj, radj = subgraph(g, live)
    idom, rpo, num, _ = dominators(root, adj, radj, n)
    rl, rc, kids = dom_tree(g, idom, rpo, root)
    tot = sum(g.lines[v] for v in proj)
    M = dict(modules=len(proj), lines=tot, import_edges=sum(1 for v in proj for w in g.deps[v] if not g.ext[w]),
             reachable=len(rpo), duplicate_imports=g.meta["duplicate_imports"],
             import_only=sum(1 for v in proj if not _DECL.search(texts[v]) and g.deps[v]),
             decls=sum(len(_DECL.findall(texts[v])) for v in proj))
    if verbose:
        hdr("REAL SOURCE TREE (module granularity): %s" % path)
    P("  modules %d | lines %d | project import edges %d | keyword decls %d" % (M["modules"], tot, M["import_edges"], M["decls"]))
    P("  reachable from %s: %d (%s) | import-only shims %d | duplicate import lines %d"
      % (root_name, len(rpo), pct(len(rpo), len(proj)), M["import_only"], M["duplicate_imports"]))
    hub = root
    while len(kids.get(hub, [])) == 1:
        hub = kids[hub][0]
    comp = [rc[c] for c in kids.get(hub, [])]
    M.update(hub=g.name[hub], hub_dominates=rc[hub] - 1, top_level_components=len(comp),
             singleton_components=sum(1 for c in comp if c == 1))
    P("  hub %s dominates %d modules; %d top-level single-entry components, %d of them singletons (shared)"
      % (g.name[hub], rc[hub] - 1, len(comp), M["singleton_components"]))
    if verbose:
        top = sorted((v for v in rpo if v in kids and v != root), key=lambda v: -rl[v])[:12]
        table([(short(g.name[v], 70), rc[v], rl[v], pct(rl[v], max(1, tot))) for v in top],
              ["dominator module", "modules retained", "lines retained", "of all"])
    # text passes
    docs, keep = [], []
    for v in proj:
        body = [l for l in texts[v].split("\n") if l.strip() and not _IMPORT.match(l)]
        if body:
            docs.append([normalize_line(l) for l in body]); keep.append(v)
    cl = clone_clusters(docs)
    dup, multi, ncl = clone_savings(cl, [len(d) for d in docs])
    M.update(clone_clusters=ncl, clone_files=multi, clone_redundant_lines=dup)
    P("  clone clusters (files identical/near-identical after renaming): %d clusters, %d files, %d redundant lines (%s)"
      % (ncl, multi, dup, pct(dup, max(1, sum(len(d) for d in docs)))))
    by = collections.defaultdict(list)
    for v in proj:
        by[g.grp[v]].append(v)
    rows = []
    for gi, vs in sorted(by.items(), key=lambda kv: -sum(g.lines[v] for v in kv[1])):
        blob = "\n".join(texts[v] for v in vs).encode("utf-8")
        nl = [normalize_line(l) for v in vs for l in texts[v].split("\n") if l.strip()]
        rows.append((g.grp_names[gi], len(vs), sum(g.lines[v] for v in vs),
                     "%.3f" % (len(zlib.compress(blob, 6)) / max(1, len(blob))), "%.2f" % line_entropy(nl)))
    if verbose:
        table(rows[:25], ["folder", "files", "lines", "zlib ratio", "line entropy (bits)"])
    hits = []
    for nm, rx in _RF:
        fs = [v for v in proj if rx.search(texts[v])]
        if fs:
            hits.append((nm, len(fs), sum(len(rx.findall(texts[v])) for v in fs), short(g.name[fs[0]], 60)))
    M["red_flags"] = {h[0]: h[1] for h in hits}
    if verbose:
        print("  lexical red flags (leads for a human, NOT findings):")
        table(hits or [("none", 0, 0, "")], ["pattern", "files", "hits", "first file"], ["l", "r", "r", "l"])
    # Horn skeleton over named propositions
    clauses = [c for v in proj for c in horn_skeleton(texts[v])]
    impl = [c for c in clauses if c[3] and c[1]]
    facts = [c for c in clauses if c[3] and not c[1] and not c[2]]
    edge = collections.Counter((a, c[3]) for c in impl for a in c[1] if a != c[3])
    M.update(horn_theorems=len(clauses), horn_implications=len(impl), horn_facts=len(facts),
             horn_edges=sorted("%s => %s" % e for e in edge))
    if verbose:
        print("\n  PASS H  Horn skeleton: implications between NAMED propositions, read off theorem signatures (text heuristic)")
        print("    %d theorem headers parsed; %d are conditional on a named proposition; %d prove a named proposition outright"
              % (len(clauses), len(impl), len(facts)))
        rows = [(short(c[0], 52), " & ".join(short(a, 34) for a in c[1]) + (" (+%d unnamed)" % c[2] if c[2] else ""),
                 short(c[3], 40)) for c in impl[:40]]
        table(rows or [("none", "", "")], ["conditional theorem", "named hypotheses", "=> conclusion"], ["l", "l", "l"])
        if facts:
            print("    discharged outright: " + "; ".join("%s : %s" % (short(c[0], 44), short(c[3], 34)) for c in facts[:12]))
        if len(edge) > len(impl[:40]):
            print("    (%d distinct proposition->proposition edges in total)" % len(edge))
    return M


def emit_lean_tree(g, out_dir, skew=1.6):
    """Write the simulated graph as a fake Lean source tree (round-trip test for --lean-dir)."""
    by = collections.defaultdict(list)
    for v in range(g.n):
        if not g.ext[v] and g.kind[v] != "aux":
            by[g.mod[v]].append(v)
    imports = collections.defaultdict(set)
    for m, vs in by.items():
        for v in vs:
            for w in g.deps[v]:
                if not g.ext[w] and g.mod[w] != m:
                    imports[m].add(g.mod[w])
    for a, b in g.extra_imports:
        imports[a].add(b)
    for m, vs in by.items():
        p = os.path.join(out_dir, *g.mod_names[m].split(".")) + ".lean"
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w", encoding="utf-8") as f:
            f.write("import Mathlib\n")
            for b in sorted(imports[m]):
                f.write("import %s\n" % g.mod_names[b])
            for v in vs:
                f.write("\n" + "\n".join(synth_doc(g, v, skew)) + "\n")
    return len(by), sum(len(s) for s in imports.values())


# ======================================================================================
# Self-test: brute-force cross-validation on small random graphs + ingest round trips
# ======================================================================================
def _brute_reach(nn, adj, src, removed):
    if src in removed:
        return set()
    seen, st = {src}, [src]
    while st:
        for w in adj[st.pop()]:
            if w not in seen and w not in removed:
                seen.add(w); st.append(w)
    return seen


def selftest(trials=250, verbose=True):
    rnd = random.Random(7)
    checked = collections.Counter()
    for trial in range(trials):
        nn = rnd.randint(4, 10)
        dag = trial % 3 != 0
        adj = [[] for _ in range(nn)]
        for a in range(nn):
            for b in range(nn):
                if a != b and rnd.random() < 0.28 and (b > a or not dag):
                    if not dag and a in adj[b]:
                        continue                         # articulation() assumes no antiparallel pairs
                    adj[a].append(b)
        radj = [[] for _ in range(nn)]
        for a in range(nn):
            for b in adj[a]:
                radj[b].append(a)
        full = _brute_reach(nn, adj, 0, set())
        # live-restricted reverse adjacency, as the real pipeline uses
        radj_l = [[u for u in radj[v] if u in full] if v in full else [] for v in range(nn)]
        adj_l = [adj[v] if v in full else [] for v in range(nn)]
        # --- dominators vs removal definition
        idom, rpo, num, _ = dominators(0, adj_l, radj_l, nn)
        for v in full:
            if v == 0:
                continue
            brute = {d for d in full if d != v and v not in _brute_reach(nn, adj, 0, {d})}
            chain, x = set(), v
            while x != 0:
                x = idom[x]; chain.add(x)
            assert chain == brute, ("dominators", trial, v, chain, brute)
            checked["dominator sets"] += 1
        # --- articulation points / bridges vs removal definition (undirected view)
        und = [sorted(set(adj_l[v]) | set(radj_l[v])) for v in range(nn)]
        apm, apc, br = articulation(0, adj_l, radj_l, [1] * nn, nn)
        ufull = _brute_reach(nn, und, 0, set())
        for v in ufull:
            if v == 0:
                continue
            lost = len(ufull) - 1 - len(_brute_reach(nn, und, 0, {v}))
            assert (lost > 0) == (v in apm) and apm.get(v, 0) == lost, ("articulation", trial, v, lost, apm.get(v))
            checked["articulation points"] += 1
        bset = {frozenset(e) for e in br}
        for a in ufull:
            for b in und[a]:
                if a < b:
                    und2 = [[w for w in und[x] if {x, w} != {a, b}] for x in range(nn)]
                    is_b = len(_brute_reach(nn, und2, 0, set())) < len(ufull)
                    assert is_b == (frozenset((a, b)) in bset), ("bridge", trial, a, b)
                    checked["bridges"] += 1
        # --- min vertex cut vs exhaustive search
        others = [v for v in full if v != 0]
        if others:
            targets = rnd.sample(others, rnd.randint(1, min(3, len(others))))
            k, cut, near = min_vertex_cut(0, targets, adj_l, nn, radj=radj_l)
            best = None
            for size in range(0, len(others) + 1):
                for S in itertools.combinations(others, size):
                    r = _brute_reach(nn, adj, 0, set(S))
                    if not any(t in r for t in targets):
                        best = size; break
                if best is not None:
                    break
            assert k == best and len(cut) == k and len(near) == k, ("mincut", trial, k, best, cut, near)
            for c in (cut, near):
                r = _brute_reach(nn, adj, 0, set(c))
                assert not any(t in r for t in targets), ("cut does not separate", trial, c)
            checked["min vertex cuts"] += 1
    # --- generator invariants + ingest round trips on a tiny simulated project
    g = generate(scale=0.004, seed=11)
    order_ok = True
    state = bytearray(g.n)                                # iterative cycle check
    for s in range(g.n):
        if state[s]:
            continue
        st = [(s, iter(g.deps[s]))]; state[s] = 1
        while st:
            v, it = st[-1]
            for w in it:
                if state[w] == 1:
                    order_ok = False
                if state[w] == 0:
                    state[w] = 1; st.append((w, iter(g.deps[w]))); break
            else:
                state[v] = 2; st.pop()
    assert order_ok, "generator produced a cycle"
    checked["generator is acyclic"] += 1
    m1 = analyze(g, ROOT, HEADLINES, truth=True, verbose=False, text_sample=3000)
    assert m1["clone_precision"] > 0.9 and m1["clone_recall"] > 0.6, (m1["clone_precision"], m1["clone_recall"])
    checked["clone detector vs planted families"] += 1
    g2 = generate(scale=0.004, seed=11, plant_live_axiom=True)
    g2.meta["plant_live"] = True
    m2 = analyze(g2, ROOT, HEADLINES, truth=True, verbose=False, text_sample=500)
    assert "Sim.LLC.Attempt0.assumed_local_bound" in m2["axiom_footprint"], "planted LIVE axiom was not detected"
    checked["planted live axiom detected"] += 1
    with tempfile.TemporaryDirectory() as td:
        p = os.path.join(td, "g.jsonl")
        dump_jsonl(g, p)
        gj = load_jsonl(p)
        m3 = analyze(gj, ROOT, HEADLINES, truth=False, verbose=False)
        for k in ("live_decls", "live_lines", "dominators_nontrivial", "aps", "bridges", "cone_all", "trunk_chain"):
            assert m1[k] == m3[k], ("jsonl round trip", k, m1[k], m3[k])
        checked["jsonl round trip (7 metrics identical)"] += 1
        nmods, nedges = emit_lean_tree(g, os.path.join(td, "src"))
        ml = analyze_lean_dir(os.path.join(td, "src"), "Main", 2, verbose=False)
        assert ml["modules"] == nmods and ml["import_edges"] == nedges, (ml["modules"], nmods, ml["import_edges"], nedges)
        assert ml["reachable"] == m1["modules_import_reachable"], (ml["reachable"], m1["modules_import_reachable"])
        assert ml["clone_clusters"] > 0
        checked["lean-dir round trip (modules, edges, reachability)"] += 1
    sample = ("theorem A.b_of_c (hG : Ns.Green) (hV : Ns.Top.VWin)\n    (h : Nonempty (Hyps (fun x => Closed x) DRS)) : Ns.EveryCharacter :=\n  foo\n"
              "theorem t2 (N : ℕ) [NeZero N] (χ : D ℂ N) (hχ : χ.IsPrimitive) (h0 : 0 < s.re) : s.re = 1 / 2 := by\n  simp\n"
              "theorem t3 (h : Ns.Row0b fun h rc => Ns.IsRecT h rc) : Ns.EveryCharacter :=\n  bar\n"
              "theorem t4 : RiemannHypothesis := baz t3\n")
    hs = horn_skeleton(sample)
    assert hs[0] == ("A.b_of_c", ["Ns.Green", "Ns.Top.VWin", "Hyps"], 0, "Ns.EveryCharacter"), hs[0]
    assert hs[1] == ("t2", [], 2, None), hs[1]
    assert hs[2] == ("t3", ["Ns.Row0b"], 0, "Ns.EveryCharacter"), hs[2]
    assert hs[3] == ("t4", [], 0, "RiemannHypothesis"), hs[3]
    checked["Horn-skeleton signature parser"] += 4
    if verbose:
        hdr("SELF-TEST  brute-force cross-validation (%d random graphs, DAG and cyclic) + ingest round trips" % trials)
        for k, v in checked.items():
            print("  PASS  %-52s %6d checks" % (k, v))
    return dict(checked)


# ======================================================================================
# Sensitivity sweep
# ======================================================================================
def sweep(scale, leaks=(0.0, 0.002, 0.01, 0.05, 0.2)):
    hdr("PASS 10  Sensitivity: what happens to the RE passes as encapsulation leaks grow?  (scale %.3f)" % scale)
    rows, out = [], []
    for p in leaks:
        g = generate(scale=scale, seed=SEED, p_leak=p)
        m = analyze(g, ROOT, HEADLINES, truth=True, verbose=False, text_sample=1)
        cl = m["clusters"]
        ent = sum(c["thm_entries"] for c in cl.values())
        api = sum(1 for _ in g.meta["api"])
        own = sum(1 for c in cl.values() if c["own_waist"])
        f30, f300 = m["frontier"].get(30, {}), m["frontier"].get(300, {})
        rows.append(("%.3f" % p, ent, api, "%d / %d" % (own, len(cl)), m["doms_ge10"], pct(f30.get("coverage", 0), 1),
                     pct(f300.get("coverage", 0), 1), pct(m["interface_width"], 1)))
        out.append(dict(p_leak=p, thm_entries=ent, designed_api=api, clusters_with_own_waist=own, doms_ge10=m["doms_ge10"],
                        blackboxed_k30=f30.get("coverage"), blackboxed_k300=f300.get("coverage"),
                        interface_width=m["interface_width"]))
    table(rows, ["P(cross-cluster call bypasses API)", "thm entry points", "designed API", "clusters cut at own API",
                 "dominators >=10", "black-boxed k=30", "k=300", "interface width"])
    print("  reading: leaks multiply entry points (the export table grows past the designed API) while the")
    print("  mass-weighted decompositions move slowly: dominators and entry sets are robust to sloppy encapsulation.")
    return out


# ======================================================================================
def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0], formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--scale", type=float, default=0.05, help="fraction of the real 1.06M declarations to simulate")
    ap.add_argument("--seed", type=int, default=SEED)
    ap.add_argument("--p-leak", type=float, default=0.01, help="P(a cross-cluster reference bypasses the cluster API)")
    ap.add_argument("--plant-live-axiom", action="store_true", help="plant a custom axiom in LIVE code (pass 2 must flag it)")
    ap.add_argument("--no-selftest", action="store_true")
    ap.add_argument("--no-sweep", action="store_true")
    ap.add_argument("--sweep-scale", type=float, default=0.02)
    ap.add_argument("--json", help="write metrics + spine tree to this file")
    ap.add_argument("--dump-jsonl", help="write the simulated declaration graph in the documented JSONL schema")
    ap.add_argument("--from-jsonl", help="analyse a real declaration graph instead of simulating")
    ap.add_argument("--lean-dir", help="analyse a real Lean source tree at module granularity")
    ap.add_argument("--root", default=None, help="root declaration (or root module with --lean-dir)")
    ap.add_argument("--group-depth", type=int, default=1, help="namespace/folder depth used as 'cluster'")
    a = ap.parse_args(argv)
    t_all = time.time()
    out = {}
    if not a.no_selftest:
        out["selftest"] = selftest()
    if a.lean_dir:
        out["lean_dir"] = analyze_lean_dir(a.lean_dir, a.root or "Main", a.group_depth)
    elif a.from_jsonl:
        g = load_jsonl(a.from_jsonl, a.group_depth)
        hdr("REAL DECLARATION GRAPH: %s (%d declarations)" % (a.from_jsonl, g.n))
        out["graph"] = analyze(g, a.root or ROOT, [h for h in HEADLINES if h in g.by_name] or None, truth=False)
    else:
        hdr("SIMULATION  scale=%.3f  seed=%d  p_leak=%.3f   -- names starting `Sim.`/`Mathlib.cone_` are SYNTHETIC"
            % (a.scale, a.seed, a.p_leak))
        t0 = time.time()
        g = generate(a.scale, a.seed, a.p_leak, plant_live_axiom=a.plant_live_axiom)
        g.meta["plant_live"] = a.plant_live_axiom
        src = [v for v in range(g.n) if not g.ext[v] and g.kind[v] != "aux"]
        nthm = sum(1 for v in src if g.kind[v] == "thm")
        print("  generated %d constants, %d edges, %d files in %.1fs" % (g.n, sum(len(d) for d in g.deps), len(g.mod_names), time.time() - t0))
        print("\n  CALIBRATION against the real release (sim value is rescaled by 1/scale where it is a count):")
        k = 1.0 / a.scale
        table([
            ("source declarations", format(REAL["decls_kw"], ","), format(round(len(src) * k), ","), "fitted"),
            ("files", format(REAL["files"], ","), format(round(len(g.mod_names) * k), ","), "fitted (decls/file)"),
            ("lines", format(REAL["lines"], ","), format(round(sum(g.lines[v] for v in src) * k), ","), "fitted"),
            ("theorem share of decls", pct(REAL["thm_kw"], REAL["decls_kw"]), pct(nthm, len(src)), "fitted"),
            ("statement closure (decls)", format(REAL["challenge_decls"], ","), "see pass 3", "fitted"),
            ("files in import closure of Main", "100%", "see pass 1", "fitted (leftover imports)"),
            ("decls kept by source-level traces", "55% .. 80%", "see pass 1", "NOT fitted: prior, real value unpublished"),
            ("cluster wiring / leak rate / clone rate", "unknown", "invented", "NOT fitted"),
        ], ["quantity", "real", "simulated", "status"], ["l", "r", "r", "l"])
        if a.dump_jsonl:
            dump_jsonl(g, a.dump_jsonl)
            print("  wrote %s" % a.dump_jsonl)
        out["params"] = dict(scale=a.scale, seed=a.seed, p_leak=a.p_leak)
        out["sim"] = analyze(g, ROOT, HEADLINES, truth=True, budget_scale=True)
        del g
        if not a.no_sweep:
            out["sweep"] = sweep(a.sweep_scale)
    if not (a.lean_dir or a.from_jsonl):
        print("\nREMINDER: every percentage above describes the GENERATOR (invented wiring below a real top spine).")
        print("They show which questions are answerable and how the passes behave, not what the real proof looks like.")
    print("\n[total %.1fs]" % (time.time() - t_all))
    if a.json:
        with open(a.json, "w", encoding="utf-8") as f:
            json.dump(out, f, indent=1, ensure_ascii=False, default=str)
        print("wrote %s" % a.json)
    return 0


if __name__ == "__main__":
    sys.exit(main())
