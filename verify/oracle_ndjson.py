#!/usr/bin/env python3
"""Verifier-owned independent parser for lean4export NDJSON (format 3.1.0).

Independent of leanre/ndjson.py and of leanre/kernel-rs: imports nothing from leanre/.
Purpose: an oracle for K2/K3 (and, on a sample or in full, K4) — record/constant counts
with an explicit counting rule, type-vs-value dependency edges, cones.

Counting rules reported (never tuned):
  records    = one per top-level declaration record (thm/def/opaque/quot/axiom/inductive);
               an `inductive` record bundles its types + ctors + recursors.
  constants  = thm + def + opaque + quot + axiom + sum(types) + sum(ctors) + sum(recs).

Unknown top-level keys / unknown expression kinds are COUNTED AND REPORTED, never dropped
silently (a parser that treats an unknown expr as a leaf loses edges).

Usage:
  python3 verify/oracle_ndjson.py data/challenge.ndjson.zst --out verify/out/challenge_oracle.pkl
"""
from __future__ import annotations

import argparse
import array
import collections
import json
import pickle
import subprocess
import sys
import time

DECL_KEYS = ("thm", "def", "opaque", "quot", "axiom", "inductive")
BIN_KEYS = {"app": ("fn", "arg"), "lam": ("type", "body"), "forallE": ("type", "body")}
LEAF_KEYS = ("sort", "bvar", "natVal", "strVal", "lit", "fvar", "mvar")

K_LEAF, K_CONST, K_BIN, K_LET, K_PROJ, K_MDATA = 0, 1, 2, 3, 4, 5


def stream_lines(path):
    if path.endswith(".zst"):
        p = subprocess.Popen(["zstd", "-d", "-c", "--long=31", path], stdout=subprocess.PIPE, bufsize=1 << 22)
        return p.stdout, p
    return open(path, "rb"), None


def parse(path, progress=True):
    t0 = time.time()
    names = {0: ""}
    kind = bytearray()
    A = array.array("I")
    B = array.array("I")
    C = array.array("I")
    zeros = None

    def grow(eid):
        need = eid + 1 - len(kind)
        if need > 0:
            need = max(need, 1 << 16)
            kind.extend(bytes(need))
            z = array.array("I", bytes(4 * need))
            A.extend(z)
            B.extend(z)
            C.extend(z)

    recs = []  # (record_kind, primary_name_id, [all name ids], [type roots], [value roots])
    top_keys = collections.Counter()
    expr_kinds = collections.Counter()
    unknown_expr = collections.Counter()
    unknown_top = collections.Counter()
    meta = None
    nlines = 0
    max_eid = -1
    f, proc = stream_lines(path)
    loads = json.loads
    for line in f:
        nlines += 1
        o = loads(line)
        if "ie" in o:
            eid = o["ie"]
            if eid > max_eid:
                max_eid = eid
            if eid >= len(kind):
                grow(eid)
            if "app" in o:
                d = o["app"]; kind[eid] = K_BIN; A[eid] = d["fn"]; B[eid] = d["arg"]
            elif "const" in o:
                kind[eid] = K_CONST; A[eid] = o["const"]["name"]
            elif "lam" in o:
                d = o["lam"]; kind[eid] = K_BIN; A[eid] = d["type"]; B[eid] = d["body"]
            elif "forallE" in o:
                d = o["forallE"]; kind[eid] = K_BIN; A[eid] = d["type"]; B[eid] = d["body"]
            elif "letE" in o:
                d = o["letE"]; kind[eid] = K_LET; A[eid] = d["type"]; B[eid] = d["value"]; C[eid] = d["body"]
            elif "proj" in o:
                d = o["proj"]; kind[eid] = K_PROJ; A[eid] = d["struct"]; B[eid] = d["typeName"]
            elif "mdata" in o:
                d = o["mdata"]; kind[eid] = K_MDATA; A[eid] = d["expr"]
            else:
                ks = [k for k in o if k != "ie"]
                k0 = ks[0] if ks else "?"
                if k0 not in LEAF_KEYS:
                    unknown_expr[k0] += 1
                kind[eid] = K_LEAF
                expr_kinds[k0] += 1
                continue
            continue
        if "in" in o:
            nid = o["in"]
            if "str" in o:
                s = o["str"]; pre = names[s["pre"]]
                names[nid] = pre + "." + s["str"] if pre else s["str"]
            elif "num" in o:
                s = o["num"]; pre = names[s["pre"]]
                names[nid] = pre + "." + str(s["i"]) if pre else str(s["i"])
            else:
                unknown_top["in:" + ",".join(sorted(o))] += 1
            continue
        if "il" in o:
            top_keys["il"] += 1
            continue
        hit = False
        for k in DECL_KEYS:
            if k in o:
                hit = True
                top_keys[k] += 1
                d = o[k]
                if k == "inductive":
                    types = d.get("types", []); ctors = d.get("ctors", []); rs = d.get("recs", [])
                    allids = [t["name"] for t in types] + [c["name"] for c in ctors] + [r["name"] for r in rs]
                    troots = [t["type"] for t in types] + [c["type"] for c in ctors] + [r["type"] for r in rs]
                    vroots = [rule["rhs"] for r in rs for rule in r.get("rules", [])]
                    recs.append((k, types[0]["name"], allids, troots, vroots, (len(types), len(ctors), len(rs))))
                else:
                    vroots = [d["value"]] if "value" in d else []
                    recs.append((k, d["name"], [d["name"]], [d["type"]], vroots, None))
                break
        if not hit:
            if "meta" in o:
                meta = o["meta"]
            else:
                unknown_top[",".join(sorted(o))] += 1
        if progress and nlines % 20_000_000 == 0:
            print(f"  .. {nlines:,} lines, {len(recs):,} records, {time.time()-t0:.0f}s", file=sys.stderr, flush=True)
    f.close()
    if proc is not None:
        rc = proc.wait()
        if rc != 0:
            raise RuntimeError(f"zstd exit {rc}")
    return dict(names=names, kind=kind, A=A, B=B, C=C, recs=recs, top_keys=top_keys, expr_leaf_kinds=expr_kinds,
                unknown_expr=unknown_expr, unknown_top=unknown_top, meta=meta, nlines=nlines, n_expr=max_eid + 1,
                parse_s=time.time() - t0)


def const_refs(P, roots):
    """Set of const-name-ids (incl. proj typeName) referenced under the given expr roots."""
    kind, A, B, C = P["kind"], P["A"], P["B"], P["C"]
    seen = set()
    out = set()
    st = [r for r in roots]
    while st:
        e = st.pop()
        if e in seen:
            continue
        seen.add(e)
        k = kind[e]
        if k == K_BIN:
            st.append(A[e]); st.append(B[e])
        elif k == K_CONST:
            out.add(A[e])
        elif k == K_LET:
            st.append(A[e]); st.append(B[e]); st.append(C[e])
        elif k == K_PROJ:
            out.add(B[e]); st.append(A[e])
        elif k == K_MDATA:
            st.append(A[e])
    return out


def build_graph(P, progress=True):
    """Record-level graph. Returns dict with names (primary name per record), kinds,
    tdeps[i], vdeps[i] (sets of record indices, self removed), plus diagnostics."""
    recs = P["recs"]
    names = P["names"]
    owner = {}
    dup_const = 0
    for i, r in enumerate(recs):
        for nid in r[2]:
            if nid in owner:
                dup_const += 1
            owner[nid] = i
    tdeps, vdeps = [], []
    dangling = collections.Counter()
    t0 = time.time()
    for i, r in enumerate(recs):
        tr = const_refs(P, r[3])
        vr = const_refs(P, r[4]) if r[4] else set()
        ts, vs = set(), set()
        for nid in tr:
            j = owner.get(nid)
            if j is None:
                dangling[names.get(nid, f"#{nid}")] += 1
            elif j != i:
                ts.add(j)
        for nid in vr:
            j = owner.get(nid)
            if j is None:
                dangling[names.get(nid, f"#{nid}")] += 1
            elif j != i:
                vs.add(j)
        tdeps.append(ts)
        vdeps.append(vs)
        if progress and i and i % 200_000 == 0:
            print(f"  .. walked {i:,}/{len(recs):,} records, {time.time()-t0:.0f}s", file=sys.stderr, flush=True)
    rec_names = [names[r[1]] for r in recs]
    const_names = {names[nid]: i for nid, i in owner.items()}
    n_const = sum(len(r[2]) for r in recs)
    return dict(rec_names=rec_names, rec_kinds=[r[0] for r in recs], tdeps=tdeps, vdeps=vdeps,
                const_to_rec=const_names, n_records=len(recs), n_constants=n_const,
                dup_const_ids=dup_const, dup_rec_names=len(rec_names) - len(set(rec_names)),
                dup_const_names=n_const - len(const_names),
                dangling=dict(dangling), ind_shape=[r[5] for r in recs])


def summarize(P, G):
    n_edges = sum(len(t | v) for t, v in zip(G["tdeps"], G["vdeps"]))
    ek = collections.Counter()
    for t, v in zip(G["tdeps"], G["vdeps"]):
        ek["both"] += len(t & v); ek["type"] += len(t - v); ek["value"] += len(v - t)
    ind = [s for s in G["ind_shape"] if s]
    return {
        "meta": P["meta"], "ndjson_lines": P["nlines"], "n_expr": P["n_expr"],
        "records": G["n_records"], "constants": G["n_constants"],
        "record_kinds": dict(P["top_keys"]),
        "inductive_types": sum(s[0] for s in ind), "inductive_ctors": sum(s[1] for s in ind),
        "inductive_recs": sum(s[2] for s in ind),
        "edges_union": n_edges, "edges_by_kind": dict(ek),
        "expr_leaf_kinds": dict(P["expr_leaf_kinds"]),
        "UNKNOWN_expr_kinds": dict(P["unknown_expr"]), "UNKNOWN_top_keys": dict(P["unknown_top"]),
        "dangling_const_refs": len(G["dangling"]), "dup_const_ids": G["dup_const_ids"],
        "dup_record_names": G["dup_rec_names"], "dup_const_names": G["dup_const_names"],
        "parse_s": round(P["parse_s"], 1),
    }


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--out")
    a = ap.parse_args()
    P = parse(a.path)
    G = build_graph(P)
    S = summarize(P, G)
    print(json.dumps(S, indent=1, sort_keys=True, ensure_ascii=False))
    if a.out:
        with open(a.out, "wb") as fh:
            pickle.dump({"G": G, "S": S}, fh, protocol=4)
        print("wrote", a.out)
