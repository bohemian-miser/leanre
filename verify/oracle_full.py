#!/usr/bin/env python3
"""Run the verifier's own NDJSON parser (oracle_ndjson.py) over an export and dump a
compact record-level graph for the kernel.db cross-checks.

Output <out>.npz : src,dst (int32 record indices, export order, 0-based), kind (int8:
1=type-only 2=value-only 3=both), rec_kind (int8 index into KINDS), n_consts (int32)
Output <out>.names.json : record primary names (list), const name -> record index
Output <out>.summary.json : counts with counting rules (see oracle_ndjson.summarize)

  python3 verify/oracle_full.py data/solution.ndjson.zst verify/out/solution_oracle
"""
from __future__ import annotations

import json
import os
import resource
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle_ndjson as O  # noqa: E402

KINDS = ["thm", "def", "opaque", "axiom", "quot", "inductive"]


def main():
    path, out = sys.argv[1], sys.argv[2]
    t0 = time.time()
    P = O.parse(path)
    print(f"parsed {P['nlines']:,} lines, {len(P['recs']):,} records, {P['n_expr']:,} exprs in {time.time()-t0:.0f}s", flush=True)
    G = O.build_graph(P)
    S = O.summarize(P, G)
    n = G["n_records"]
    m = S["edges_union"]
    src = np.empty(m, np.int32); dst = np.empty(m, np.int32); kind = np.empty(m, np.int8)
    k = 0
    for i in range(n):
        t, v = G["tdeps"][i], G["vdeps"][i]
        for j in sorted(t | v):
            src[k] = i; dst[k] = j; kind[k] = (1 if j in t else 0) | (2 if j in v else 0); k += 1
        G["tdeps"][i] = G["vdeps"][i] = None
    assert k == m
    np.savez(out + ".npz", src=src, dst=dst, kind=kind,
             rec_kind=np.array([KINDS.index(x) for x in G["rec_kinds"]], np.int8),
             n_consts=np.array([len(r[2]) for r in P["recs"]], np.int32))
    with open(out + ".names.json", "w") as f:
        json.dump({"rec_names": G["rec_names"], "const_to_rec": G["const_to_rec"]}, f, ensure_ascii=False)
    S["forward_refs"] = int((dst >= src).sum())  # deps should precede dependents in export order
    S["wall_s"] = round(time.time() - t0, 1)
    S["peak_rss_kib"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    S["dangling_examples"] = dict(list(G["dangling"].items())[:20])
    with open(out + ".summary.json", "w") as f:
        json.dump(S, f, indent=1, sort_keys=True, ensure_ascii=False)
    print(json.dumps(S, indent=1, sort_keys=True, ensure_ascii=False))


if __name__ == "__main__":
    main()
