#!/usr/bin/env python3
"""Independent implementation of docs/SIGHASH.md §2 (K1-K4) from the prose spec alone.
Zero imports from leanre/. Used to verify that the written spec in docs/SIGHASH.md is
unambiguous and matches the published test vectors and TSV SHA-256 on challenge.ndjson.zst.
"""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys


def H(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()[:16]


def n1(name: str) -> str:
    parts = name.split(".")
    if parts and parts[0] == "_private":
        try:
            i = parts.index("0", 1)
            if i + 1 < len(parts):
                return ".".join(parts[i + 1:])
        except ValueError:
            pass
    return name


def load_lexicon(path: str | None) -> set[str]:
    if not path:
        return set()
    return {line.rstrip("\n") for line in open(path, encoding="utf-8") if line.strip()}


def is_local(nm: str, lex: set[str]) -> bool:
    if not lex:
        return False
    s = n1(nm)
    if s in lex:
        return True
    i = s.rfind(".")
    while i > 0:
        if s[:i] in lex:
            return True
        i = s.rfind(".", 0, i)
    return False


def run(ndjson_path: str, lexicon_path: str | None = None):
    lex = load_lexicon(lexicon_path)
    names = {0: ""}
    levels = {0: ("zero",)}
    exprs = {}
    records = []

    p = subprocess.Popen(["zstd", "-d", "-c", "--long=31", ndjson_path], stdout=subprocess.PIPE, bufsize=1 << 22)
    for line in p.stdout:
        o = json.loads(line)
        if "in" in o:
            nid = o["in"]
            if "str" in o:
                pre = names[o["str"]["pre"]]
                names[nid] = f"{pre}.{o['str']['str']}" if pre else o["str"]["str"]
            else:
                pre = names[o["num"]["pre"]]
                names[nid] = f"{pre}.{o['num']['i']}" if pre else str(o["num"]["i"])
        elif "il" in o:
            lid = o["il"]
            if "succ" in o:
                levels[lid] = ("succ", o["succ"])
            elif "max" in o:
                levels[lid] = ("max", o["max"][0], o["max"][1])
            elif "imax" in o:
                levels[lid] = ("imax", o["imax"][0], o["imax"][1])
            elif "param" in o:
                levels[lid] = ("param", o["param"])
        elif "ie" in o:
            eid = o["ie"]
            if "bvar" in o:
                exprs[eid] = ("bvar", o["bvar"])
            elif "sort" in o:
                exprs[eid] = ("sort", o["sort"])
            elif "const" in o:
                exprs[eid] = ("const", o["const"]["name"], tuple(o["const"].get("us", ())))
            elif "app" in o:
                exprs[eid] = ("app", o["app"]["fn"], o["app"]["arg"])
            elif "lam" in o:
                exprs[eid] = ("lam", o["lam"]["type"], o["lam"]["body"])
            elif "forallE" in o:
                exprs[eid] = ("forallE", o["forallE"]["type"], o["forallE"]["body"])
            elif "letE" in o:
                exprs[eid] = ("letE", o["letE"]["type"], o["letE"]["value"], o["letE"]["body"])
            elif "proj" in o:
                exprs[eid] = ("proj", o["proj"]["typeName"], o["proj"]["idx"], o["proj"]["struct"])
            elif "natVal" in o:
                exprs[eid] = ("natVal", str(o["natVal"]))
            elif "strVal" in o:
                exprs[eid] = ("strVal", o["strVal"])
            elif "mdata" in o:
                exprs[eid] = ("mdata", o["mdata"]["expr"])
            else:
                raise ValueError(f"unexpected expr: {o}")
        else:
            for k in ("thm", "def", "opaque", "axiom", "quot", "inductive"):
                if k in o:
                    records.append((k, o[k]))
                    break
    p.stdout.close()
    assert p.wait() == 0

    def hash_roots(roots, self_map, abstract):
        lparam = {}
        local_idx = {}
        vis_e = set()
        vis_l = set()

        def walk_l(lid):
            if lid in vis_l:
                return
            vis_l.add(lid)
            lv = levels[lid]
            if lv[0] == "succ":
                walk_l(lv[1])
            elif lv[0] in ("max", "imax"):
                walk_l(lv[1]); walk_l(lv[2])
            elif lv[0] == "param":
                if lv[1] not in lparam:
                    lparam[lv[1]] = len(lparam)

        def note_name(nid):
            if nid in self_map:
                return
            if abstract and is_local(names[nid], lex):
                nm = n1(names[nid])
                if nm not in local_idx:
                    local_idx[nm] = len(local_idx)

        def walk_e(eid):
            if eid in vis_e:
                return
            vis_e.add(eid)
            e = exprs[eid]
            k = e[0]
            if k == "sort":
                walk_l(e[1])
            elif k == "const":
                note_name(e[1])
                for u in e[2]:
                    walk_l(u)
            elif k in ("app", "lam", "forallE"):
                walk_e(e[1]); walk_e(e[2])
            elif k == "letE":
                walk_e(e[1]); walk_e(e[2]); walk_e(e[3])
            elif k == "proj":
                note_name(e[1]); walk_e(e[3])
            elif k == "mdata":
                walk_e(e[1])

        for r in roots:
            walk_e(r)

        lmemo = {}
        def hl(lid):
            if lid in lmemo:
                return lmemo[lid]
            lv = levels[lid]
            if lv[0] == "zero":
                res = H(b"z")
            elif lv[0] == "succ":
                res = H(b"s" + hl(lv[1]))
            elif lv[0] == "max":
                res = H(b"m" + hl(lv[1]) + hl(lv[2]))
            elif lv[0] == "imax":
                res = H(b"i" + hl(lv[1]) + hl(lv[2]))
            elif lv[0] == "param":
                res = H(b"p" + str(lparam[lv[1]]).encode())
            lmemo[lid] = res
            return res

        def nref(nid):
            if nid in self_map:
                return H(b"r" + str(self_map[nid]).encode())
            nm = n1(names[nid])
            if abstract and nm in local_idx:
                return H(b"l" + str(local_idx[nm]).encode())
            return H(b"n" + nm.encode("utf-8"))

        ememo = {}
        smemo = {}
        def he(eid):
            if eid in ememo:
                return ememo[eid], smemo[eid]
            e = exprs[eid]
            k = e[0]
            if k == "bvar":
                res, sz = H(b"v" + str(e[1]).encode()), 1
            elif k == "sort":
                res, sz = H(b"S" + hl(e[1])), 1
            elif k == "const":
                uh = H(b"u" + b"".join(hl(u) for u in e[2]))
                res, sz = H(b"C" + nref(e[1]) + uh), 1
            elif k == "app":
                h1, s1 = he(e[1]); h2, s2 = he(e[2])
                res, sz = H(b"A" + h1 + h2), 1 + s1 + s2
            elif k == "lam":
                h1, s1 = he(e[1]); h2, s2 = he(e[2])
                res, sz = H(b"F" + h1 + h2), 1 + s1 + s2
            elif k == "forallE":
                h1, s1 = he(e[1]); h2, s2 = he(e[2])
                res, sz = H(b"P" + h1 + h2), 1 + s1 + s2
            elif k == "letE":
                h1, s1 = he(e[1]); h2, s2 = he(e[2]); h3, s3 = he(e[3])
                res, sz = H(b"T" + h1 + h2 + h3), 1 + s1 + s2 + s3
            elif k == "proj":
                h1, s1 = he(e[3])
                res, sz = H(b"J" + nref(e[1]) + h1 + str(e[2]).encode()), 1 + s1
            elif k == "natVal":
                res, sz = H(b"N" + e[1].encode()), 1
            elif k == "strVal":
                res, sz = H(b"X" + e[1].encode("utf-8")), 1
            elif k == "mdata":
                res, sz = he(e[1])
            sz = min(sz, 4294967295)
            ememo[eid] = res; smemo[eid] = sz
            return res, sz

        hs = [he(r) for r in roots]
        return hs, len(local_idx)

    tsv_hash = hashlib.sha256()
    n_consts = 0
    for rk, d in records:
        if rk == "inductive":
            types = d.get("types", [])
            ctors = d.get("ctors", [])
            recs = d.get("recs", [])
            self_map = {t["name"]: j for j, t in enumerate(types)}
            ctors_by_ind = {}
            for c in ctors:
                ctors_by_ind.setdefault(c["induct"], []).append(c)
            for t in types:
                cs = sorted(ctors_by_ind.get(t["name"], []), key=lambda x: x["cidx"])
                roots = [t["type"]] + [c["type"] for c in cs]
                hs_n, _ = hash_roots(roots, self_map, False)
                hs_a, nloc = hash_roots(roots, self_map, True)
                dn = H(b"I" + hs_n[0][0] + H(b"c" + b"".join(x[0] for x in hs_n[1:])))
                da = H(b"I" + hs_a[0][0] + H(b"c" + b"".join(x[0] for x in hs_a[1:])))
                sz = min(sum(x[1] for x in hs_n), 4294967295)
                line = f"{names[t['name']]}\tind\t{dn.hex()}\t{da.hex()}\t{sz}\t{nloc}\n"
                tsv_hash.update(line.encode("utf-8")); n_consts += 1
            for c in ctors:
                hs_n, _ = hash_roots([c["type"]], self_map, False)
                hs_a, nloc = hash_roots([c["type"]], self_map, True)
                line = f"{names[c['name']]}\tctor\t{hs_n[0][0].hex()}\t{hs_a[0][0].hex()}\t{hs_n[0][1]}\t{nloc}\n"
                tsv_hash.update(line.encode("utf-8")); n_consts += 1
            for r in recs:
                hs_n, _ = hash_roots([r["type"]], self_map, False)
                hs_a, nloc = hash_roots([r["type"]], self_map, True)
                line = f"{names[r['name']]}\trec\t{hs_n[0][0].hex()}\t{hs_a[0][0].hex()}\t{hs_n[0][1]}\t{nloc}\n"
                tsv_hash.update(line.encode("utf-8")); n_consts += 1
        else:
            hs_n, _ = hash_roots([d["type"]], {}, False)
            hs_a, nloc = hash_roots([d["type"]], {}, True)
            line = f"{names[d['name']]}\t{rk}\t{hs_n[0][0].hex()}\t{hs_a[0][0].hex()}\t{hs_n[0][1]}\t{nloc}\n"
            tsv_hash.update(line.encode("utf-8")); n_consts += 1

    print(f"constants={n_consts} tsv_sha256={tsv_hash.hexdigest()}")


if __name__ == "__main__":
    run(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else None)
