#!/usr/bin/env python3
"""F1 oracle (verifier-owned): scan data/rh_mirror directly (no leanre imports, no leanre.db)
for what `Development/AbelianVarietyTheory/**` files actually declare.

Emits several candidate counting rules side by side so the Tier-1 numbers can be matched to
an explicit rule rather than tuned:
  first_ns      : first `namespace X` line in the file (full dotted X)
  first_ns_top  : its first component
  any_ns        : files containing at least one `namespace X` with that exact X
  root_decl     : files with a declaration header naming `_root_.<Top>...`
"""
from __future__ import annotations

import collections
import json
import os
import re
import sys
from multiprocessing import Pool

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "data", "rh_mirror", "src")
NS = re.compile(r"^\s*namespace\s+(\S+)", re.M)
ROOTDECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+_root_\.([A-Za-z0-9_'.]+)", re.M)


def scan(path):
    with open(path, encoding="utf-8", errors="replace") as f:
        t = f.read()
    ns = NS.findall(t)
    rd = ROOTDECL.findall(t)
    return os.path.relpath(path, SRC), ns, rd


def main():
    sub = sys.argv[1] if len(sys.argv) > 1 else "Development/AbelianVarietyTheory"
    files = []
    for dp, dn, fn in os.walk(os.path.join(SRC, sub)):
        files += [os.path.join(dp, x) for x in fn if x.endswith(".lean")]
    with Pool(16) as p:
        res = p.map(scan, files, chunksize=500)
    first = collections.Counter(); first_top = collections.Counter(); anyns = collections.Counter()
    rootd = collections.Counter(); none = 0
    for rel, ns, rd in res:
        if ns:
            first[ns[0]] += 1; first_top[ns[0].split(".")[0]] += 1
        else:
            none += 1
        for x in set(ns):
            anyns[x] += 1
        for x in {r.split(".")[0] for r in rd}:
            rootd[x] += 1
    out = dict(subtree=sub, files=len(files), files_without_namespace=none,
               first_ns=first.most_common(8), first_ns_top=first_top.most_common(8),
               any_ns=anyns.most_common(8), root_decl_top=rootd.most_common(5))
    print(json.dumps(out, indent=1, ensure_ascii=False))
    # known misfile
    tgt = "GlobalTheory.PrimeRecip"
    hits = [rel for rel, ns, rd in res if any(x == tgt or x.endswith("PrimeRecip") for x in ns)]
    print("files declaring a *PrimeRecip namespace:", len(hits), hits[:5])


if __name__ == "__main__":
    main()
