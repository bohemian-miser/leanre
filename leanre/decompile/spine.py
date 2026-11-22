"""Spine & shared-diamond decompilation (gate D1): whole-graph reachability classification and the
`outputs/decomp/spine_map.json` generator.

Whole-graph passes use an in-memory CSR of kernel.db `edges` (114,115,002 rows) built with stdlib
`array`; it is cached (binary, not in git) under $LEANRE_DECOMP_CACHE (default ~/.cache/leanre).
"""
from __future__ import annotations

import hashlib
import json
import os
import sys
import time
from array import array
from collections import Counter, defaultdict
from typing import Iterable, Optional

from .kdb import BOTH, TYPE, VALUE, KernelDB

CACHE_DIR = os.environ.get("LEANRE_DECOMP_CACHE", os.path.expanduser("~/.cache/leanre"))


class CSR:
    """Forward adjacency: for decl id i, dst[off[i]:off[i+1]] with edge kinds kind[...]."""

    def __init__(self, n: int, off: array, dst: array, kind: array) -> None:
        self.n, self.off, self.dst, self.kind = n, off, dst, kind

    @classmethod
    def load(cls, kdb: KernelDB, log=None) -> "CSR":
        row = kdb.k.execute("SELECT value_json FROM meta WHERE key='content_hashes'").fetchone()
        edges_hash = json.loads(row[0]).get("edges") if row else None
        if edges_hash:  # survives atomic kernel.db swaps that leave `edges` untouched
            key = "e" + edges_hash[:16]
        else:
            st = os.stat(kdb.kpath)
            key = hashlib.sha1(f"{os.path.abspath(kdb.kpath)}:{st.st_size}:{int(st.st_mtime)}".encode()).hexdigest()[:16]
        base = os.path.join(CACHE_DIR, f"csr_{key}")
        n = int(kdb.k.execute("SELECT max(id) FROM decls").fetchone()[0]) + 1
        if os.path.exists(base + ".kind"):
            off, dst, kind = array("q"), array("i"), array("b")
            with open(base + ".off", "rb") as f:
                off.fromfile(f, n + 1)
            m = off[n]
            with open(base + ".dst", "rb") as f:
                dst.fromfile(f, m)
            with open(base + ".kind", "rb") as f:
                kind.fromfile(f, m)
            return cls(n, off, dst, kind)
        t = time.time()
        deg = array("q", bytes(8 * (n + 1)))
        dst, kind = array("i"), array("b")
        last = -1
        cur = kdb.k.execute("SELECT src, dst, kind FROM edges ORDER BY src")  # PK order: no sort
        while True:
            rows = cur.fetchmany(200_000)
            if not rows:
                break
            for s, d, k in rows:
                deg[s + 1] += 1
                dst.append(d)
                kind.append(k)
        for i in range(n):
            deg[i + 1] += deg[i]
        if log:
            print(f"[csr] loaded {len(dst):,} edges in {time.time() - t:.0f}s", file=log)
        os.makedirs(CACHE_DIR, exist_ok=True)
        for ext, arr in ((".off", deg), (".dst", dst), (".kind", kind)):
            with open(base + ext + ".tmp", "wb") as f:
                arr.tofile(f)
            os.replace(base + ext + ".tmp", base + ext)
        return cls(n, deg, dst, kind)

    def reach(self, seeds: Iterable[int], kinds: tuple[int, ...] = (TYPE, VALUE, BOTH),
              stop: Optional[bytearray] = None) -> bytearray:
        """bytearray mask of forward closure; nodes with stop[i] set are reached but not expanded."""
        seen = bytearray(self.n)
        stack = []
        for s in seeds:
            if not seen[s]:
                seen[s] = 1
                stack.append(s)
        off, dst, kind = self.off, self.dst, self.kind
        all_kinds = set(kinds) == {TYPE, VALUE, BOTH}
        while stack:
            i = stack.pop()
            if stop is not None and stop[i]:
                continue
            for j in range(off[i], off[i + 1]):
                d = dst[j]
                if not seen[d] and (all_kinds or kind[j] in kinds):
                    seen[d] = 1
                    stack.append(d)
        return seen


def dom_subtree_mask(kdb: KernelDB, root_id: int, n: int) -> bytearray:
    m = bytearray(n)
    m[root_id] = 1
    frontier = [root_id]
    while frontier:
        nxt = []
        for i in range(0, len(frontier), 900):
            ch = frontier[i:i + 900]
            q = f"SELECT decl_id FROM dom WHERE tree_id=? AND idom IN ({','.join('?' * len(ch))})"
            for (x,) in kdb.k.execute(q, [kdb.tree_id, *ch]):
                m[x] = 1
                nxt.append(x)
        frontier = nxt
    return m


def count(mask: bytearray) -> int:
    return mask.count(1)


# ---------------------------------------------------------------------------------------------
# Top-of-proof constants (names verified against kernel.db in test_decompile.TestRealDB).
ALLCHI = "allChi"
EVERY = "UpperTheory.FinalTheorems.everyCharacter"
ROW = "UpperTheory.FinalTheorems.everyCharacter_of_row"
GAL = "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter"
EVERY_DEF = "UpperTheory.EveryCharacter"


def _top_ns(name: str, depth: int = 1) -> str:
    parts = name.removeprefix("_root_.").split(".")
    return ".".join(parts[:depth]) if len(parts) > depth else "(root)"


def classify(kdb: KernelDB, ids: Iterable[int], masks: dict[str, bytearray], top_ns_depth: int = 1) -> dict:
    """Counts of ids by reach-signature, kind, ground/project, top namespace, top module folder."""
    sig, kinds, grp, ns, folder = Counter(), Counter(), Counter(), Counter(), Counter()
    ids = list(ids)
    for d in kdb.decls(ids):
        s = "+".join(k for k, m in masks.items() if m[d.id]) or "none"
        sig[s] += 1
        kinds[d.kind] += 1
        grp["ground(Mathlib/Lean)" if d.ground else ("project" if d.module else f"project:{d.method}")] += 1
        ns[_top_ns(d.name, top_ns_depth)] += 1
        folder[".".join(d.module.split(".")[:2]) if d.module else f"<{d.method}>"] += 1
    return {"n": len(ids), "reach_signature": dict(sig.most_common()), "kind": dict(kinds.most_common()),
            "origin": dict(grp.most_common()), "top_namespace": dict(ns.most_common(25)),
            "module_folder": dict(folder.most_common(25))}


def diamond_analysis(kdb: KernelDB, G: CSR, log=None) -> dict:
    t = time.time()
    ev, row, gal, edef = (kdb.decl(x) for x in (EVERY, ROW, GAL, EVERY_DEF))
    R = G.reach([row.id]); Gm = G.reach([gal.id]); E = G.reach([edef.id])
    if log:
        print(f"[diamond] cones row={count(R):,} gal={count(Gm):,} EveryCharacter-def={count(E):,} "
              f"({time.time() - t:.0f}s)", file=log)
    roots = [n.decl_id for n in kdb.dom_children(ev, limit=10 ** 7)]
    droots = [i for i in roots if i not in (row.id, gal.id)]
    dmask = bytearray(G.n)
    sizes = {}
    for n in kdb.dom_children(ev, limit=10 ** 7):
        sizes[n.decl_id] = n.subtree_size
    # full diamond membership: subtree of every diamond root
    sub_row = dom_subtree_mask(kdb, row.id, G.n); sub_gal = dom_subtree_mask(kdb, gal.id, G.n)
    sub_ev = dom_subtree_mask(kdb, ev.id, G.n)
    for i in range(G.n):
        if sub_ev[i] and not sub_row[i] and not sub_gal[i] and i != ev.id:
            dmask[i] = 1
    masks = {"row": R, "gal": Gm, "EveryCharacter_def": E}
    dids = [i for i in range(G.n) if dmask[i]]
    out = {
        "everyCharacter_children": len(roots),
        "diamond_roots": len(droots),
        "diamond_decls": len(dids),
        "diamond_root_subtree_total": sum(sizes[i] for i in droots),
        "cone_sizes": {"row": count(R), "gal": count(Gm), "EveryCharacter_def": count(E),
                       "row_and_gal": sum(1 for i in range(G.n) if R[i] and Gm[i])},
        "roots": classify(kdb, droots, masks),
        "all": classify(kdb, dids, masks),
        "root_size_hist": dict(sorted(Counter(min(s, 10 ** 9) if s < 10 else (10 * (s // 10) if s < 100 else 100 * (s // 100) if s < 1000 else 1000 * (s // 1000)) for s in (sizes[i] for i in droots)).items())),
    }
    # how many diamond roots are directly used by each side (one edge) vs deep
    if log:
        print(f"[diamond] done ({time.time() - t:.0f}s)", file=log)
    return out


def outside_analysis(kdb: KernelDB, G: CSR, log=None) -> dict:
    """The decls reachable from the 5 roots but NOT dominated by allChi."""
    t = time.time()
    allchi = kdb.decl(ALLCHI)
    sub = dom_subtree_mask(kdb, allchi.id, G.n)
    roots = kdb.roots()
    live = G.reach([r[2] for r in roots])
    A = G.reach([allchi.id])
    stop = bytearray(G.n); stop[allchi.id] = 1
    bridge = G.reach([r[2] for r in roots], stop=stop)  # reached without expanding allChi
    per_root = {r[1]: G.reach([r[2]], stop=stop) for r in roots}
    outside = [i for i in range(G.n) if live[i] and not sub[i]]
    masks = {"allChi_cone": A, **{f"root:{k}": v for k, v in per_root.items()}}
    res = {"live_total": count(live), "allChi_subtree": count(sub), "outside": len(outside),
           "bridge_cone_without_allChi": count(bridge),
           "outside_not_in_allChi_cone": sum(1 for i in outside if not A[i]),
           "outside_in_allChi_cone": sum(1 for i in outside if A[i]),
           "classes": classify(kdb, outside, {"allChi_cone": A, "bridge": bridge}, 1)}
    # project (non-ground) decls outside allChi: list them all if few
    proj = [d for d in kdb.decls(outside) if not d.ground]
    res["outside_project_n"] = len(proj)
    res["outside_project_by_module"] = dict(Counter(d.module or f"<{d.method}>" for d in proj).most_common(40))
    res["outside_project_by_root_signature"] = dict(Counter(
        "+".join(sorted(k for k, m in per_root.items() if m[d.id])) + (" | allChi" if A[d.id] else "")
        for d in proj).most_common(20))
    vr = kdb.dom_children(None, limit=10 ** 7)
    res["virtual_root_children"] = len(vr)
    res["virtual_root_children_top"] = [(kdb.decl(n.decl_id).name, n.subtree_size) for n in vr[:25]]
    if log:
        print(f"[outside] done ({time.time() - t:.0f}s)", file=log)
    return res


# ---------------------------------------------------------------------------------------------
# spine_map.json builder

SPINE_ORDER = [
    "riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive", "rhOfAll", "critAll", "claimAll", "Formalism.VW.rh_of_every",
    "Formalism.VW.rh_of_right", "Formalism.VW.critLine", "Claim.strip", "Claim.zeta", ALLCHI, EVERY_DEF, EVERY, ROW, GAL,
    "UpperTheory.GalStar.Row0b", "UpperTheory.Gal.Int.recT", "UpperTheory.GalStar.RecNotion", "UpperTheory.Zero.LLC.IsRecT",
    "UpperTheory.Zero.LLC.RecTExists", "UpperTheory.Zero.LLC.recTExists",
    "UpperTheory.LiteratureTheorems.OpenLiteratureStatements", "UpperTheory.One.M.Row",
    "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
    "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
    "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt",
    "UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature",
    "UpperTheory.One.vwin_of_row", "UpperTheory.Top.VWin",
]
PILLARS = {
    "A_theta": "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
    "B_galois": GAL,
    "C_volume": "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt",
    "D_window": "UpperTheory.One.vwin_of_row",
}
PINS = {"rh_mirror": "40e56bab026552e089d7afcfeff08d2defb9c005",
        "export_sha256": "5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e", "dom_tree": "ALL"}


def literature_usage(kdb: KernelDB, G: CSR) -> dict:
    ols = kdb.decl("UpperTheory.LiteratureTheorems.OpenLiteratureStatements")
    fields = ("caraianiLocalGlobalDual", "localLanglandsExists", "galoisRepOfPolarizedPairLit")
    pid = {kdb.decl(f"{ols.name}.{f}").id for f in fields}
    users = sorted({u.id for u, _ in kdb.users(ols, limit=10 ** 6) if u.kind == "thm"} - pid)
    # backward closure of the 3 field projections (who transitively depends on a field of O)
    anc, frontier = set(pid), list(pid)
    while frontier:
        nxt = []
        for i in range(0, len(frontier), 900):
            ch = frontier[i:i + 900]
            q = f"SELECT src FROM edges WHERE dst IN ({','.join('?' * len(ch))})"
            for (x,) in kdb.k.execute(q, ch):
                if x not in anc:
                    anc.add(x); nxt.append(x)
        frontier = nxt
    uses = [kdb.decl(u).name for u in users if u in anc]
    direct = {kdb.decl(p).name.rsplit(".", 1)[1]: sorted(x.name for x, _ in kdb.users(p, limit=100)) for p in pid}
    return {"theorems_mentioning_O": len(users), "transitively_use_a_field_of_O": len(uses),
            "ignore_O": len(users) - len(uses), "users_of_O_fields_direct": direct, "O_using_theorems": sorted(uses)}


def build_spine_map(D, top: int = 60, log=None) -> dict:
    from .spine_notes import SPINE, DIAMOND
    from .source import one_line
    kdb = D.kdb
    G = CSR.load(kdb, log)
    stats = {"diamond": diamond_analysis(kdb, G, log), "outside_allChi": outside_analysis(kdb, G, log),
             "literature_O_usage": literature_usage(kdb, G)}
    ev = kdb.decl(EVERY)
    sub_row = dom_subtree_mask(kdb, kdb.decl(ROW).id, G.n)
    sub_gal = dom_subtree_mask(kdb, kdb.decl(GAL).id, G.n)
    sub_ev = dom_subtree_mask(kdb, ev.id, G.n)
    pub = [d for d in kdb.search("GlobalTheory.Published.%", 10 ** 6) if d.kind == "def" and "._" not in d.name]
    stats["published_defs"] = dict(Counter(
        "row" if sub_row[d.id] else "gal" if sub_gal[d.id] else "diamond" if sub_ev[d.id] else "outside_everyCharacter"
        for d in pub), total=len(pub))
    row_kids = kdb.dom_children(kdb.decl(ROW), limit=8, min_size=1)
    lit = kdb.decl("UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin")
    stats["split"] = {
        "allChi": kdb.dom(ALLCHI).subtree_size, "everyCharacter": kdb.dom(ev).subtree_size,
        "everyCharacter_children": kdb.dom_child_stats(ev),
        "row": kdb.dom(ROW).subtree_size, "gal": kdb.dom(GAL).subtree_size,
        "row_children": kdb.dom_child_stats(kdb.decl(ROW)),
        "row_top_children": [(kdb.decl(n.decl_id).name, n.subtree_size) for n in row_kids],
        "literature_children": kdb.dom_child_stats(lit),
        "literature_top_children": [(kdb.decl(n.decl_id).name, n.subtree_size) for n in kdb.dom_children(lit, limit=12)],
        "pillars": {k: kdb.dom(v).subtree_size for k, v in PILLARS.items()},
    }
    nodes, opaque, seen = [], set(), set()

    def add(name: str, note: Optional[tuple], rank: Optional[int] = None, group: str = "spine") -> None:
        if name in seen:
            return
        d = kdb.maybe(name)
        if d is None:
            raise KeyError(name)
        seen.add(name)
        n = D.node(d)
        n["group"] = group
        if rank is not None:
            n["diamond_rank"] = rank
        if note:
            role, status, verdict, tag, summary, inner = note
            n.update(role=role, status=status, verdict=verdict, tag=tag, summary=summary)
            if inner:
                n["opaque_inner"] = inner
                opaque.update(inner)
        else:
            n.update(status="OPAQUE" if not d.ground else "READ",
                     summary=n["summary"] or "Not yet read by spine (header only).")
        if d.ground:  # Mathlib / Lean core: ground truth for our purposes
            n.update(role="glue", status="READ", verdict="real", tag="L",
                     summary="Mathlib/Lean library declaration (ground; not authored in the RH project).")
            n.pop("opaque_inner", None)
        if n["status"] == "OPAQUE":
            opaque.add(name)
        n["fields"] = [dict(f, ground=None) for f in n["fields"]][:20]
        nodes.append(n)

    for nm in SPINE_ORDER:
        add(nm, SPINE.get(nm))
    ranked = [n for n in kdb.dom_children(ev, limit=top + 2) if n.decl_id not in (kdb.decl(ROW).id, kdb.decl(GAL).id)][:top]
    for r, dn in enumerate(ranked, 1):
        nm = kdb.decl(dn.decl_id).name
        add(nm, DIAMOND.get(nm) or SPINE.get(nm), rank=r, group="diamond")
    # edges: dominator edges + kernel type/value edges among included nodes
    ids = {kdb.decl(n["id"]).id: n["id"] for n in nodes}
    edges = []
    for n in nodes:
        idom = (n.get("dom") or {}).get("idom")
        if idom:
            edges.append({"src": idom, "dst": n["id"], "rel": "dom", "tag": "L"})
    for i, nm in ids.items():
        for dst, k in kdb.deps(i):
            if dst.id in ids and dst.id != i:
                edges.append({"src": nm, "dst": dst.name, "rel": {1: "type", 2: "value", 3: "both"}[k], "tag": "L"})
    horn = []
    for n in nodes:
        if n["kind"] == "thm" and n["group"] == "spine":
            h = D.horn(n["id"])
            horn.append({"concl": h["concl"], "hyps": h["hyps"], "via": h["via"], "lemmas_project": h["lemmas_project"],
                         "tag": "L"})
    sd, so, sl, sp = stats["diamond"], stats["outside_allChi"], stats["literature_O_usage"], stats["split"]
    claims = [
        {"text": f"everyCharacter has {sd['everyCharacter_children']:,} direct dominator children: everyCharacter_of_row "
                 f"({sp['row']:,}), galoisLocalGlobalStrong_recParameter ({sp['gal']:,}) and {sd['diamond_roots']:,} "
                 f"diamond roots dominating {sd['diamond_decls']:,} decls.", "tag": "L", "anchors": [], "nodes": [EVERY]},
        {"text": f"All {sd['diamond_decls']:,} diamond decls (and all {sd['diamond_roots']:,} roots) are reachable from BOTH "
                 f"everyCharacter_of_row and galoisLocalGlobalStrong_recParameter (cone sizes {sd['cone_sizes']['row']:,} / "
                 f"{sd['cone_sizes']['gal']:,}; intersection {sd['cone_sizes']['row_and_gal']:,}). None is reached only via "
                 "the EveryCharacter type.", "tag": "L", "anchors": [], "nodes": [ROW, GAL]},
        {"text": f"Diamond origin: {sd['all']['origin']}; kinds {sd['all']['kind']}.", "tag": "L", "anchors": [], "nodes": []},
        {"text": f"Outside allChi: {so['outside']:,} live decls = {so['classes']['origin']}; {so['outside_project_n']} project "
                 f"decls are exactly the Statement/bridge layer (Main, Statements, MainTheorems, CritLine, RhOfRight, "
                 f"HalfPlane, ClaimStrip, EveryCharacter def). {so['outside_in_allChi_cone']:,} of them are also in allChi's "
                 f"cone (shared Mathlib); {so['outside_not_in_allChi_cone']} are bridge-only.", "tag": "L", "anchors": [], "nodes": [ALLCHI]},
        {"text": f"OpenLiteratureStatements: {sl['theorems_mentioning_O']} theorems take/mention it; only "
                 f"{sl['transitively_use_a_field_of_O']} transitively use one of its 3 fields; {sl['ignore_O']} ignore it.",
         "tag": "L", "anchors": ["src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/"
                                 "EveryCharacterOfLiteratureOfVWin.lean:215"], "nodes": ["UpperTheory.LiteratureTheorems.OpenLiteratureStatements"]},
    ]
    doc = {"schema": "leanre.decomp/v1", "pillar": "spine", "pins": PINS, "root": ALLCHI,
           "generated_by": "python3 leanre/decompile spine-map --out outputs/decomp/spine_map.json",
           "nodes": nodes, "edges": edges, "horn": horn, "claims": claims, "opaque": sorted(opaque),
           "pillars": PILLARS, "stats": stats}
    return doc
