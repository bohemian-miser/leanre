#!/usr/bin/env python3
"""A1–A3 black-box checks (verifier-owned). Uses leanre/annot.py + leanre/sighash.py only
through their public API / CLI, with inputs written here; does not reuse leanre/test_annot.py.
All writes happen in a temp dir; the repo's annotations/ is only read.
"""
from __future__ import annotations

import hashlib
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "leanre"))
import annot  # noqa: E402
import sighash  # noqa: E402

R = []
NOW = "2026-11-22T02:50:00Z"


def ck(gate, ok, msg):
    R.append((gate, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'} [{gate}] {msg}")


def raises(fn, exc=Exception):
    try:
        fn()
    except exc as e:  # noqa: BLE001
        return type(e).__name__
    return None


def h(header):
    r = sighash.source_hash_header(header)
    # accept dict or tuple return; find the s1n string
    if isinstance(r, dict):
        for k in ("s1n", "exact", "sighash"):
            if k in r:
                return r[k]
    for x in (r if isinstance(r, (tuple, list)) else [r]):
        if isinstance(x, str) and x.startswith("s1n:"):
            return x
    raise SystemExit(f"cannot find s1n in {r!r}")


# ---------------------------------------------------------------- A1
H0 = "theorem foo_bound {n : ℕ} (hn : 2 ≤ n) (x : ℝ) : x ^ n ≤ Real.exp (n * x)"
variants = {
    "body_change": H0,                                                                  # same header, other proof
    "alpha_ws": "theorem foo_bound {m : ℕ}   (hm : 2 ≤ m)\n    (y : ℝ) :\n  y ^ m ≤ Real.exp (m * y)",  # binder rename + whitespace
    "renamed": "theorem totally_new_name {n : ℕ} (hn : 2 ≤ n) (x : ℝ) : x ^ n ≤ Real.exp (n * x)",
    "sig_changed": "theorem foo_bound {n : ℕ} (hn : 3 ≤ n) (x : ℝ) : x ^ n ≤ Real.exp (n * x)",
    "other": "theorem unrelated (a b : ℕ) : a + b = b + a",
}
h0 = h(H0)
hv = {k: h(v) for k, v in variants.items()}
ck("A1", hv["body_change"] == h0 and hv["alpha_ws"] == h0 and hv["renamed"] == h0,
   f"sighash s1n stable under body change / binder alpha-rename+whitespace / decl rename: {h0}")
ck("A1", hv["sig_changed"] != h0 and hv["other"] != h0 and hv["other"] != hv["sig_changed"], "sighash changes when the statement changes (2 ≤ n → 3 ≤ n) and differs for an unrelated statement")
ck("A1", bool(annot.SIGHASH_RE.match(h0)), f"sighash string accepted by annot.SIGHASH_RE")

p = annot.Pack()
p.add_layer("human/verifier-test", "human", "t", "d")
rec = annot.make_annotation(name="foo_bound", sighash=h0, layer="human/verifier-test", tag="L", source="verify/a_check.py synthetic header",
                            author="verifier", now=NOW, note="a note", rename="FooBound")
p.put(rec)
key = annot.record_key(rec)
ck("A1", key[2] == "foo_bound" and key[3] == h0, f"record key carries (name, sighash): {key}")


def status(graph_rows):
    rep = annot.reanchor(p, annot.GraphIndex(graph_rows, label="t"))
    return rep["entries"][0], rep


e, _ = status([("foo_bound", h0), ("unrelated", hv["other"])])
ck("A1", e["status"] == "exact", f"proof-body change (same name, same signature hash) -> {e['status']}")
e, rep = status([("totally_new_name", hv["renamed"]), ("unrelated", hv["other"])])
ck("A1", e["status"] == "hash_only" and e.get("resolved_name") == "totally_new_name" and e.get("unique") is True, f"rename with unchanged signature -> {e['status']} resolved={e.get('resolved_name')}")
rb = annot.rebind(p, rep, now=NOW)
moved = list(rb["pack"].annots.values())
ck("A1", len(moved) == 1 and moved[0]["name"] == "totally_new_name" and moved[0].get("note") == "a note" and moved[0].get("rename") == "FooBound"
   and "foo_bound" in (moved[0].get("was") or []) and moved[0]["sighash"] == h0,
   f"rebind: annotation follows the rename with payload intact, old name recorded in was={moved[0].get('was')}")
e, rep = status([("foo_bound", hv["sig_changed"])])
rb = annot.rebind(p, rep, now=NOW)
ck("A1", e["status"] == "name_only" and e.get("reason") == "signature_changed" and list(rb["pack"].annots) == list(p.annots),
   f"signature change -> {e['status']}/{e.get('reason')}; NOT silently re-keyed")
e, rep = status([("a1", h0), ("a2", h0)])
rb = annot.rebind(p, rep, now=NOW)
ck("A1", e["status"] == "hash_only" and not e.get("unique") and "resolved_name" not in e and list(rb["pack"].annots) == list(p.annots),
   f"ambiguous hash (2 candidates) -> not auto-resolved (candidates={e.get('candidates')})")
e, _ = status([("zzz", hv["other"])])
ck("A1", e["status"] == "orphan", f"neither name nor hash -> {e['status']}")

# ---------------------------------------------------------------- A2
seed_dir = os.path.join(ROOT, "annotations")
for fn in sorted(x for x in os.listdir(seed_dir) if x.endswith(".jsonl")):
    b = open(os.path.join(seed_dir, fn), "rb").read()
    out = annot.dumps(annot.loads(b.decode("utf-8"))).encode("utf-8")
    out2 = annot.dumps(annot.loads(out.decode("utf-8"))).encode("utf-8")
    ck("A2", out == b and out2 == out, f"{fn}: export(import(file)) byte-identical to file and stable (sha256 {hashlib.sha256(b).hexdigest()[:16]}, {len(b)} B)")
    lines = b.decode().split("\n")
    objs = [json.loads(x) for x in lines if x]
    ck("A2", b.endswith(b"\n") and b"\r" not in b and all(json.dumps(o, sort_keys=True, ensure_ascii=False, separators=(",", ":")) == l for o, l in zip(objs, lines)),
       f"{fn}: LF-terminated, one canonical JSON object per line ({len(objs)} lines)")
    an = [o for o in objs if o.get("type") == "annot"]
    ck("A2", all(o.get("tag") in "LACSM" and len(o.get("tag", "")) == 1 and o.get("author") and o.get("layer") and o.get("source") for o in an),
       f"{fn}: all {len(an)} annotations carry tag/author/layer/source; tags={sorted({o['tag'] for o in an})}")
    import datetime as _dt
    REAL_NOW = _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    future = [o["created"] for o in an if o["created"] > REAL_NOW or o["updated"] > REAL_NOW]
    ck("A2", not future, f"{fn}: timestamps are not in the future relative to wall clock ({REAL_NOW}); offending={future[:2]} (file mtime-based authorship should not post-date its commit)")

rnd = random.Random(99)
alpha = "abcXYZ ℕℝχζ«»→∀λ'_.0123456789\"\\/\t"
ok_rt = True
ok_order = True
for trial in range(40):
    P = annot.Pack()
    layers = ["human/a", "human/b.c", "ai/draft-x"]
    P.add_layer("human/a", "human", "A", "da"); P.add_layer("human/b.c", "human", "B", "db"); P.add_layer("ai/draft-x", "ai-draft", "X", "dx")
    recs = []
    for i in range(rnd.randint(1, 25)):
        lay = rnd.choice(layers)
        ai = lay.startswith("ai/")
        nm = "N." + "".join(rnd.choice("abcdeζ_'") for _ in range(rnd.randint(1, 12))) + str(i)
        kw = dict(name=nm, layer=lay, tag="M" if ai else rnd.choice("LACS"), source="src " + str(i), author=("ai:model-x" if ai else "human-" + str(i)), now=NOW,
                  note=("".join(rnd.choice(alpha) for _ in range(rnd.randint(0, 60))).strip() or "n"), draft=ai,
                  sighash=("s1n:" + "%032x" % rnd.getrandbits(128)) if rnd.random() < 0.6 else None)
        if ai:
            kw["breaks"] = "where it breaks"
        recs.append(annot.make_annotation(**kw))
    for r_ in recs:
        P.put(r_)
    t1 = annot.dumps(P)
    t2 = annot.dumps(annot.loads(t1))
    ok_rt &= (t1.encode() == t2.encode())
    Q = annot.Pack()
    for lay in reversed(layers):
        Q.add_layer(lay, P.layers[lay]["kind"], P.layers[lay]["title"], P.layers[lay]["description"])
    for r_ in rnd.sample(recs, len(recs)):
        Q.put(r_)
    ok_order &= (annot.dumps(Q) == t1)
    body = [json.loads(x) for x in t1.split("\n")[1:] if x]
ck("A2", ok_rt, "40 random packs (unicode, quotes, backslashes, tabs): export→import→export byte-identical")
ck("A2", ok_order, "export independent of insertion order (sorted output)")

good = annot.dumps(p)
ann_line = [l for l in good.split("\n") if '"type":"annot"' in l][0]
base = json.loads(ann_line)


def mutated(**chg):
    o = dict(base)
    for k, v in chg.items():
        if v is None:
            o.pop(k, None)
        else:
            o[k] = v
    return good.replace(ann_line, json.dumps(o, sort_keys=True, ensure_ascii=False, separators=(",", ":")))


rej = {}
for label, txt in {
    "missing tag": mutated(tag=None), "bad tag X": mutated(tag="X"), "tag '[L]' literal": mutated(tag="[L]"), "missing author": mutated(author=None),
    "empty author": mutated(author=""), "missing layer": mutated(layer=None), "undeclared layer": mutated(layer="human/nope"),
    "missing source": mutated(source=None), "unknown field": mutated(bogus=1), "bad sighash": mutated(sighash="deadbeef"),
    "M without breaks": mutated(tag="M"), "ai author in human layer": mutated(author="ai:gpt"), "unsorted keys": good.replace(ann_line, json.dumps(base, sort_keys=False, separators=(",", ":"), ensure_ascii=False)[::1].replace('{"', '{"zz":1,"', 1)),
    "duplicate record": good + ann_line + "\n", "CRLF": good.replace("\n", "\r\n"), "no header": "\n".join(good.split("\n")[1:]),
    "trailing garbage": good + "not json\n", "NaN": mutated(extra={"x": float("nan")}),
}.items():
    errs = annot.errors_of(annot.validate_text(txt))
    rej[label] = len(errs)
ck("A2", all(v > 0 for v in rej.values()), f"schema validation rejects each malformed pack: {rej}")
ck("A2", not annot.errors_of(annot.validate_text(good)), "…and accepts the well-formed one")
ai_bad = raises(lambda: annot.Pack().add_layer("ai/x", "ai-draft", "t", "d", default_on=True))
ck("A3", ai_bad is not None, f"ai-draft layer with default_on=true rejected ({ai_bad})")

# ---------------------------------------------------------------- A3 (store + layers + conflicts) in a temp copy
tmp = tempfile.mkdtemp(prefix="leanre_verify_annot_")
try:
    st_dir = os.path.join(tmp, "annotations")
    shutil.copytree(seed_dir, st_dir)
    st = annot.PackStore(st_dir)
    st.ensure_layer("ai/flirt-draft", "ai-draft", "AI drafts", "verifier test")
    st.upsert(dict(target="decl", name="riemannHypothesis", layer="ai/flirt-draft", tag="M", source="verifier synthetic", author="ai:test-model",
                   draft=True, rename="AI_GUESS_NAME", note="draft label", breaks="heuristic only"), now=NOW)
    pack, issues = st.load()
    ck("A3", not annot.errors_of(issues), "store with human + ai-draft layers loads clean")
    dl = annot.default_layers(pack)
    ck("A3", "ai/flirt-draft" not in dl and len(dl) >= 1, f"default layers = {dl} (AI draft off by default)")
    v0 = annot.view(pack)
    v1 = annot.view(pack, enabled=["ai/flirt-draft"])
    v2 = annot.view(pack, enabled=dl + ["ai/flirt-draft"])
    v3 = annot.view(pack, enabled=[])
    t = "decl:riemannHypothesis"

    def anns(v):
        return [(a_["layer"], bool(a_.get("draft"))) for a_ in v["targets"].get(t, {}).get("annotations", [])]
    ck("A3", all(l != "ai/flirt-draft" for l, _ in anns(v0)) and anns(v1) == [("ai/flirt-draft", True)] and len(anns(v2)) == len(anns(v0)) + 1 and anns(v3) == [],
       f"layers independently toggleable: default={anns(v0)} ai-only={anns(v1)} both={anns(v2)} none={anns(v3)}")
    ck("A3", v0["targets"].get(t, {}).get("rename") != "AI_GUESS_NAME", "AI draft rename invisible when its layer is off")
    ck("A3", all(x["draft"] for x in annot.layer_table(pack) if x["kind"] == "ai-draft") and not any(x["draft"] for x in annot.layer_table(pack) if x["kind"] == "human"),
       "layer_table marks ai-draft layers draft=true (the hook for visual distinction)")
    raw = open(os.path.join(st_dir, annot.layer_filename("ai/flirt-draft"))).read()
    ck("A3", '"draft":true' in raw and '"author":"ai:' in raw, "AI-draft records are marked in the file itself (draft:true, ai: author)")
    not_draft = raises(lambda: st.upsert(dict(target="decl", name="x", layer="ai/flirt-draft", tag="L", source="s", author="ai:m", note="n"), now=NOW))
    ck("A3", not_draft is not None, f"AI-draft layer refuses a record posing as an [L] fact / non-draft ({not_draft})")
    # conflicting import
    before = {f: open(os.path.join(st_dir, f), "rb").read() for f in os.listdir(st_dir) if f.endswith(".jsonl")}
    theirs = annot.loads(st.export_text())
    k0 = sorted(k for k in theirs.annots if theirs.layers[k[0]]["kind"] == "human")[0]
    r2 = dict(theirs.annots[k0]); r2["note"] = "CONFLICTING NOTE FROM IMPORT"; r2["updated"] = "2026-11-22T09:55:00Z"
    theirs.put(r2, replace=True)
    rep = st.import_text(annot.dumps(theirs))
    after = {f: open(os.path.join(st_dir, f), "rb").read() for f in os.listdir(st_dir) if f.endswith(".jsonl")}
    ck("A3", rep.get("ok") is False and rep.get("applied") is False and len(rep.get("conflicts", [])) == 1 and before == after,
       f"conflicting import: reported (conflicts={len(rep.get('conflicts', []))}, applied={rep.get('applied')}), files byte-identical afterwards")
    stale = raises(lambda: st.upsert(dict(pack.annots[k0], note="stale edit"), now=NOW, expect_updated="2020-01-01T00:00:00Z"), annot.ConflictError)
    clobber = raises(lambda: st.upsert(dict(pack.annots[k0], note="clobber"), now=NOW), annot.ConflictError)
    ck("A3", stale and clobber, f"stale edit and blind overwrite both raise ConflictError ({stale}, {clobber})")
    # non-conflicting import applies and is idempotent
    theirs2 = annot.loads(st.export_text())
    theirs2.put(annot.make_annotation(name="LFunction_eq_zero_re", layer=k0[0], tag="C", source="verifier synthetic", author="verifier", now=NOW, note="new", slot="v"))
    rep2 = st.import_text(annot.dumps(theirs2)); rep3 = st.import_text(annot.dumps(theirs2))
    ck("A3", rep2.get("applied") and rep2.get("ok") and rep3.get("ok") and not rep3.get("written"), f"clean import applies ({rep2.get('written')}) and re-import is a no-op")
    # path safety of the store
    esc = raises(lambda: st.ensure_layer("../../evil", "human", "t", "d"))
    ck("A3", esc is not None and not os.path.exists(os.path.join(tmp, "evil.jsonl")) and sorted(os.listdir(tmp)) == ["annotations"], f"layer id '../../evil' rejected ({esc}); nothing written outside the store")
    # CLI
    c1 = subprocess.run([sys.executable, os.path.join(ROOT, "leanre", "annot.py"), "validate", seed_dir], capture_output=True, text=True)
    c2 = subprocess.run([sys.executable, os.path.join(ROOT, "leanre", "annot.py"), "export", seed_dir], capture_output=True)
    allb = b"".join(open(os.path.join(seed_dir, f), "rb").read() for f in sorted(os.listdir(seed_dir)) if f.endswith(".jsonl"))
    ck("A2", c1.returncode == 0 and c2.returncode == 0 and (c2.stdout == allb or len([f for f in os.listdir(seed_dir) if f.endswith('.jsonl')]) != 1),
       f"CLI validate rc={c1.returncode}; CLI export == seed file bytes: {c2.stdout == allb}")
finally:
    shutil.rmtree(tmp, ignore_errors=True)
gs = subprocess.run(["git", "-C", ROOT, "status", "--porcelain", "annotations"], capture_output=True, text=True).stdout
ck("A3", gs.strip() == "", f"repo annotations/ untouched by this check (git status: {gs.strip()!r})")

fails = [g for g, ok in R if not ok]
print(f"\nA-CHECK {'PASS' if not fails else 'FAIL'} ({len(R)-len(fails)}/{len(R)}) fails={fails}")
sys.exit(1 if fails else 0)
