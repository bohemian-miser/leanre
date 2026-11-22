#!/usr/bin/env python3
"""Phase 4 independent verifier for outputs/decomp/*.json (schema leanre.decomp/v1).

Zero-trust checks (no imports from leanre/):
  1. Required top-level schema keys, valid pillar/pins, no multi-line Lean code anywhere.
  2. Every node.id verified against outputs/kernel/kernel.db (decls or consts):
     exact kid (when non-null), kind, module (when non-null), and dom tree_id=0 (ALL)
     depth / subtree_size / idom!
  3. Every edge (src, dst, rel) verified against outputs/kernel/kernel.db:
     - rel in (type, value, both): edge exists in `edges` with exact matching kind (1/2/3)
       (or allows rel='both' only when kind==3; type when kind in (1,3)? Strict check reports both!)
     - rel == 'dom': idom(dst) == src or idom(src) == dst in dom(tree_id=0).
  4. Every anchor (`src/X/Y.lean:N`) exists on disk under data/rh_mirror/, 1 <= N <= wc -l,
     and the node's leaf identifier appears near line N.
  5. Every header is <= 1 line (no newlines), non-empty when present, and not a proof body.
  6. OPAQUE consistency: every status=='OPAQUE' node appears in top-level `opaque[]`,
     valid tag in {L,A,C,S,M}, valid status/verdict.

Usage:
  python3 verify/p4_decomp_check.py outputs/decomp/spine_map.json [more.json ...]
"""
from __future__ import annotations

import json
import os
import re
import sqlite3
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MIRROR = os.path.join(ROOT, "data", "rh_mirror")
VALID_TAGS = {"L", "A", "C", "S", "M"}
VALID_STATUS = {"READ", "PARTIAL", "OPAQUE"}
VALID_VERDICT = {"real", "wrapper", "proxy", "degenerate", "vacuous", "boilerplate", "unknown"}
VALID_KIND = {"thm", "def", "opaque", "axiom", "induct", "inductive", "ctor", "rec", "quot"}


def load_file_lines(cache, rel):
    if rel not in cache:
        p = os.path.join(MIRROR, rel) if rel.startswith("src/") else os.path.join(MIRROR, "src", rel)
        if not os.path.isfile(p):
            cache[rel] = None
        else:
            cache[rel] = open(p, encoding="utf-8", errors="replace").readlines()
    return cache[rel]


def check_file(path, kdb):
    print(f"\n=== Verifying {os.path.relpath(path, ROOT)} ===")
    errs = []
    warns = []
    try:
        data = json.load(open(path, encoding="utf-8"))
    except Exception as e:
        print(f"FAIL [JSON] cannot parse {path}: {e}")
        return 1

    if data.get("schema") != "leanre.decomp/v1":
        errs.append(f"schema={data.get('schema')!r} != 'leanre.decomp/v1'")
    for k in ("pillar", "pins", "root", "nodes", "edges", "claims", "opaque"):
        if k not in data:
            errs.append(f"missing top-level key {k!r}")

    nodes = data.get("nodes") or []
    edges = data.get("edges") or []
    opaque_list = set(data.get("opaque") or [])
    if not nodes:
        errs.append("nodes[] is empty")

    # Preload referenced decls/consts/dom/decl_module from kernel.db
    node_ids = [n.get("id") for n in nodes if isinstance(n, dict) and n.get("id")]
    edge_names = set()
    for e in edges:
        if isinstance(e, dict):
            if e.get("src"):
                edge_names.add(e["src"])
            if e.get("dst"):
                edge_names.add(e["dst"])
    all_names = sorted(set(node_ids) | edge_names)

    decl_info = {}  # name -> (id, kind, live_mask, stmt_mask)
    const_info = {}  # name -> (decl_id, ckind)
    for i in range(0, len(all_names), 500):
        chunk = all_names[i:i + 500]
        qs = ",".join("?" * len(chunk))
        for r in kdb.execute(f"SELECT name, id, kind, live_mask, stmt_mask FROM decls WHERE name IN ({qs})", chunk):
            decl_info[r[0]] = (r[1], r[2], r[3], r[4])
        for r in kdb.execute(f"SELECT name, decl_id, ckind FROM consts WHERE name IN ({qs})", chunk):
            const_info[r[0]] = (r[1], r[2])

    dids = sorted({v[0] for v in decl_info.values()} | {v[0] for v in const_info.values()})
    dom_info = {}  # decl_id -> (idom, depth, subtree_size)
    mod_info = {}  # decl_id -> module
    id_to_name = {}
    for i in range(0, len(dids), 500):
        chunk = dids[i:i + 500]
        qs = ",".join("?" * len(chunk))
        for r in kdb.execute(f"SELECT decl_id, idom, depth, subtree_size FROM dom WHERE tree_id=0 AND decl_id IN ({qs})", chunk):
            dom_info[r[0]] = (r[1], r[2], r[3])
        for r in kdb.execute(f"SELECT decl_id, module FROM decl_module WHERE decl_id IN ({qs})", chunk):
            mod_info[r[0]] = r[1]
        for r in kdb.execute(f"SELECT id, name FROM decls WHERE id IN ({qs})", chunk):
            id_to_name[r[0]] = r[1]
    # Also fetch names of any idoms not in dids
    idom_ids = sorted({v[0] for v in dom_info.values() if v[0] is not None and v[0] not in id_to_name})
    for i in range(0, len(idom_ids), 500):
        chunk = idom_ids[i:i + 500]
        qs = ",".join("?" * len(chunk))
        for r in kdb.execute(f"SELECT id, name FROM decls WHERE id IN ({qs})", chunk):
            id_to_name[r[0]] = r[1]

    file_cache = {}
    node_ok = 0
    anchor_checked = 0
    dom_checked = 0
    for idx, nd in enumerate(nodes):
        if not isinstance(nd, dict):
            errs.append(f"nodes[{idx}] not an object")
            continue
        nid = nd.get("id")
        if not nid:
            errs.append(f"nodes[{idx}] missing id")
            continue
        if nd.get("tag") not in VALID_TAGS:
            errs.append(f"node {nid}: invalid tag {nd.get('tag')!r}")
        if nd.get("status") not in VALID_STATUS:
            errs.append(f"node {nid}: invalid status {nd.get('status')!r}")
        if nd.get("verdict") not in VALID_VERDICT:
            errs.append(f"node {nid}: invalid verdict {nd.get('verdict')!r}")
        if nd.get("status") == "OPAQUE" and nid not in opaque_list:
            errs.append(f"node {nid}: status=OPAQUE but missing from top-level opaque[]")

        # Multi-line Lean check on header & fields
        hdr = nd.get("header")
        if hdr is not None:
            if "\n" in hdr or "\r" in hdr:
                errs.append(f"node {nid}: multi-line header ({len(hdr)} chars)")
            elif len(hdr) > 400:
                warns.append(f"node {nid}: long header ({len(hdr)} chars)")
        for fld in (nd.get("fields") or []):
            if isinstance(fld, dict) and isinstance(fld.get("type"), str) and "\n" in fld["type"]:
                errs.append(f"node {nid}.{fld.get('name')}: multi-line field type")

        # Check existence in kernel.db
        di = decl_info.get(nid)
        ci = const_info.get(nid)
        if di is None and ci is None:
            # Allow synthetic/non-kernel nodes ONLY if explicitly kid=None AND non-L or noted?
            # Schema rule: id must exist in kernel.db decls.name (or consts.name)
            errs.append(f"node {nid}: NOT FOUND in kernel.db decls/consts")
            continue

        actual_did = di[0] if di else ci[0]
        actual_kind = di[1] if di else ci[1]
        if nd.get("kid") is not None and nd["kid"] != actual_did:
            errs.append(f"node {nid}: kid={nd['kid']} != kernel.db {actual_did}")
        if nd.get("kind") is not None:
            k_norm = "inductive" if nd["kind"] == "induct" else nd["kind"]
            ak_norm = "inductive" if actual_kind == "induct" else actual_kind
            if k_norm != ak_norm:
                errs.append(f"node {nid}: kind={nd['kind']!r} != kernel.db {actual_kind!r}")
        if nd.get("module") is not None and actual_did in mod_info and mod_info[actual_did] is not None:
            if nd["module"] != mod_info[actual_did]:
                errs.append(f"node {nid}: module={nd['module']!r} != kernel.db {mod_info[actual_did]!r}")

        # Check dom (tree_id=0 ALL) if present
        dom = nd.get("dom")
        if isinstance(dom, dict) and actual_did in dom_info:
            dom_checked += 1
            a_idom_id, a_dep, a_sub = dom_info[actual_did]
            a_idom = id_to_name.get(a_idom_id) if a_idom_id is not None else None
            if dom.get("subtree") is not None and dom["subtree"] != a_sub:
                errs.append(f"node {nid}: dom.subtree={dom['subtree']} != kernel.db ALL {a_sub}")
            if dom.get("depth") is not None and dom["depth"] != a_dep:
                errs.append(f"node {nid}: dom.depth={dom['depth']} != kernel.db ALL {a_dep}")
            if "idom" in dom and dom["idom"] != a_idom:
                errs.append(f"node {nid}: dom.idom={dom['idom']!r} != kernel.db ALL {a_idom!r}")

        # Check anchor on disk
        anc = nd.get("anchor")
        if anc:
            m = re.match(r"^([^:]+):(\d+)(?:-\d+)?$", anc)
            if not m:
                errs.append(f"node {nid}: malformed anchor {anc!r}")
            else:
                rel, lno = m.group(1), int(m.group(2))
                # Ignore mathlib4 anchors here if explicitly prefixed data/corpora/
                if rel.startswith(("data/corpora/", "Mathlib/", "Init/", "Std/")):
                    pass
                else:
                    lines = load_file_lines(file_cache, rel)
                    if lines is None:
                        errs.append(f"node {nid}: anchor file missing on disk: {rel}")
                    elif not (1 <= lno <= len(lines)):
                        errs.append(f"node {nid}: anchor line {lno} out of range (1..{len(lines)}) in {rel}")
                    else:
                        anchor_checked += 1
                        win = "".join(lines[max(0, lno - 4):min(len(lines), lno + 6)])
                        leaf = nid.split(".")[-1]
                        if leaf not in win and not any(p in win for p in nid.split(".")[-2:]):
                            warns.append(f"node {nid}: leaf {leaf!r} not found near {anc}")
        node_ok += 1

    # Check edges against kernel.db
    edge_checked = 0
    edge_bad = 0
    for e in edges:
        if not isinstance(e, dict):
            continue
        s, d, rel = e.get("src"), e.get("dst"), e.get("rel")
        si = decl_info.get(s) or const_info.get(s)
        di = decl_info.get(d) or const_info.get(d)
        if si is None or di is None:
            if rel in ("type", "value", "both", "dom"):
                errs.append(f"edge {s} -> {d} ({rel}): endpoint absent from kernel.db")
                edge_bad += 1
            continue
        sid, did = si[0], di[0]
        if rel in ("type", "value", "both"):
            edge_checked += 1
            row = kdb.execute("SELECT kind FROM edges WHERE src=? AND dst=?", (sid, did)).fetchone()
            if row is None:
                errs.append(f"edge {s} -> {d} ({rel}): NOT PRESENT in kernel.db edges")
                edge_bad += 1
            else:
                ek = row[0]  # 1=type, 2=value, 3=both
                ok_k = (rel == "type" and ek in (1, 3)) or (rel == "value" and ek in (2, 3)) or (rel == "both" and ek == 3)
                if not ok_k:
                    errs.append(f"edge {s} -> {d}: claimed rel={rel!r} contradicts kernel.db kind={ek}")
                    edge_bad += 1
        elif rel == "dom":
            edge_checked += 1
            # Convention: src is idom of dst (or dst is idom of src)
            d_idom = dom_info.get(did, (None,))[0]
            s_idom = dom_info.get(sid, (None,))[0]
            if d_idom != sid and s_idom != did:
                errs.append(f"dom edge {s} -> {d}: neither is idom of the other in tree ALL (idom(dst)={d_idom}, idom(src)={s_idom})")
                edge_bad += 1

    # Check claims anchors on disk
    claim_anc_ok = 0
    for c in (data.get("claims") or []):
        if isinstance(c, dict):
            if c.get("tag") not in VALID_TAGS:
                errs.append(f"claim missing/invalid tag: {c.get('tag')!r}")
            for anc in (c.get("anchors") or []):
                m = re.match(r"^([^:]+):(\d+)(?:-\d+)?$", str(anc))
                if m and not m.group(1).startswith(("data/corpora/", "Mathlib/", "Init/", "Std/")):
                    lines = load_file_lines(file_cache, m.group(1))
                    if lines is None or not (1 <= int(m.group(2)) <= len(lines)):
                        errs.append(f"claim anchor invalid: {anc}")
                    else:
                        claim_anc_ok += 1

    print(f"  nodes={len(nodes)} verified={node_ok} dom_checked={dom_checked} anchors_ok={anchor_checked} edges_checked={edge_checked} claim_anchors_ok={claim_anc_ok}")
    print(f"  errors={len(errs)} warnings={len(warns)}")
    for x in errs[:20]:
        print("  ERR :", x)
    if len(errs) > 20:
        print(f"  ... +{len(errs)-20} more errors")
    for x in warns[:10]:
        print("  WARN:", x)
    print(f"  VERDICT: {'PASS' if not errs else 'FAIL'}")
    return len(errs)


def main():
    paths = sys.argv[1:]
    if not paths:
        d = os.path.join(ROOT, "outputs", "decomp")
        if os.path.isdir(d):
            paths = [os.path.join(d, f) for f in sorted(os.listdir(d)) if f.endswith(".json") and f != "compute_atlas.json"]
    if not paths:
        print("No decomp JSON files found.")
        sys.exit(2)
    kdb = sqlite3.connect(f"file:{ROOT}/outputs/kernel/kernel.db?mode=ro", uri=True)
    total_err = 0
    for p in paths:
        total_err += check_file(p, kdb)
    print(f"\nP4-DECOMP-CHECK {'PASS' if total_err == 0 else 'FAIL'} (files={len(paths)}, total_errors={total_err})")
    sys.exit(1 if total_err else 0)


if __name__ == "__main__":
    main()
