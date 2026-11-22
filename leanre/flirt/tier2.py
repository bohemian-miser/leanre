#!/usr/bin/env python3
"""FLIRT Tier 2 -- cross-repo signature DB, matching and honest measurement.

    python3 leanre/flirt/tier2.py all --threads 24      # build + match + controls + summary
    python3 leanre/flirt/tier2.py kernel                # add kernel-exact matches (needs kernel.db)
    python3 leanre/flirt/tier2.py summary               # rewrite outputs/flirt/tier2_summary.json

Outputs: outputs/flirt/tier2.db (gitignored) and outputs/flirt/tier2_summary.json (small,
committed). Schema: docs/FLIRT_TIER2.md (linked from docs/FLIRT.md).

WHAT A MATCH MEANS. A row in `matches` says: the normalized *statement shape* of a proof
declaration (binder telescope + result type, own name / binder names / binder kinds /
whitespace / proof body removed) is identical to that of a declaration in a pinned public
repo. It does NOT say the same mathematics is proved: source hashes have no elaboration and
no name resolution, and identical text can elaborate differently under different `open`s,
instances or local definitions. All numbers here are [L] (extracted by us from pinned
inputs); none is an [S] claim about published mathematics.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import multiprocessing
import os
import random
import re
import sqlite3
import sys
import time
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
LEANRE = os.path.dirname(HERE)
REPO = os.path.dirname(LEANRE)
for _p in (LEANRE, HERE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import tier2_corpora  # noqa: E402
import tier2_sig  # noqa: E402
from tier2_extract import RE_IDENT, discover, extract_decls, parse_binder  # noqa: E402

try:
    import sighash as _sighash  # noqa: E402
except Exception:  # pragma: no cover
    _sighash = None

OUT_DIR = os.path.join(REPO, "outputs", "flirt")
DB_PATH = os.path.join(OUT_DIR, "tier2.db")
SUMMARY_PATH = os.path.join(OUT_DIR, "tier2_summary.json")
MIRROR_SRC = os.path.join(REPO, "data", "rh_mirror", "src")
KERNEL_DB = os.path.join(REPO, "outputs", "kernel", "kernel.db")
PROOF_LEXICON_PATH = os.path.join(OUT_DIR, "cache", "lexicon_rh.txt")
LIBRARY_REPOS = frozenset({"mathlib4", "lean4", "batteries"})
VARIANTS = ("s1n", "s1t", "s1a")
MAX_THREADS = 24
THRESHOLD_GRID = (1, 4, 6, 8, 10, 12, 16, 20, 24, 32)
# Rule for the "strong" grade (theorem/lemma only, per variant): the smallest grid threshold T
# at which the ESTIMATED FALSE-DISCOVERY RATE is <= FDR_TARGET, where
#   FDR_est(variant, T) = max over the two negative controls of
#                         (control hits with n_tokens >= T, rescaled to the real query count)
#                         / (real theorem matches with n_tokens >= T).
# History, disclosed: the first run used "control FPR <= 0.1%". That was the wrong metric --
# real matches are so rare (base rate ~4e-4) that a 0.03% FPR still meant most matches were
# chance. The rule was replaced ONCE by this FDR rule; the threshold is whatever the rule
# returns and is never tuned to a desired total.
FDR_TARGET = 0.05
THEOREM_KINDS = ("theorem", "lemma")
SIG_TEXT_MAX = 400
# Inherited copy-on-write by forked workers (set right before Pool creation).
_WORKER_LEXICONS: Dict[str, Any] = {}

SCHEMA = """
CREATE TABLE meta (key TEXT PRIMARY KEY, value_json TEXT NOT NULL);
CREATE TABLE corpora (
    repo TEXT PRIMARY KEY, url TEXT NOT NULL, commit_sha TEXT NOT NULL, license TEXT NOT NULL,
    lean_toolchain TEXT, mathlib_rev TEXT, lexicon_id TEXT,
    lean_files INTEGER NOT NULL, decls INTEGER NOT NULL);
CREATE TABLE corpus_sigs (
    id INTEGER PRIMARY KEY, repo TEXT NOT NULL, module TEXT NOT NULL, line_no INTEGER NOT NULL,
    kind TEXT NOT NULL, name TEXT NOT NULL, is_private INTEGER NOT NULL,
    s1n TEXT NOT NULL, s1t TEXT NOT NULL, s1a TEXT NOT NULL,
    n_tokens INTEGER NOT NULL, n_local INTEGER NOT NULL,
    sig_text TEXT NOT NULL);           -- normalized header of the PUBLIC corpus decl (Apache-2.0)
CREATE TABLE proof_sigs (
    id INTEGER PRIMARY KEY, module TEXT NOT NULL, line_no INTEGER NOT NULL, kind TEXT NOT NULL,
    name TEXT NOT NULL, s1n TEXT NOT NULL, s1t TEXT NOT NULL, s1a TEXT NOT NULL,
    n_tokens INTEGER NOT NULL, n_local INTEGER NOT NULL);
                                       -- hashes only: no proof text is stored
CREATE TABLE matches (
    proof_id INTEGER NOT NULL, variant TEXT NOT NULL,   -- s1n (exact) | s1t (tail) | s1a (name-indep)
    sighash TEXT NOT NULL, n_tokens INTEGER NOT NULL,
    grade TEXT NOT NULL,   -- strong | weak (theorem/lemma) ; defsig (def/structure/...: type shape only)
    n_candidates INTEGER NOT NULL, corpus_id INTEGER NOT NULL,   -- best candidate (evidence)
    repo TEXT NOT NULL, commit_sha TEXT NOT NULL, license TEXT NOT NULL,
    corpus_name TEXT NOT NULL,
    same_short_name INTEGER NOT NULL,
    provenance TEXT NOT NULL,           -- always 'L'
    PRIMARY KEY (proof_id, variant));
CREATE TABLE match_candidates (proof_id INTEGER NOT NULL, variant TEXT NOT NULL,
    corpus_id INTEGER NOT NULL, PRIMARY KEY (proof_id, variant, corpus_id)) WITHOUT ROWID;
CREATE TABLE module_summary (
    module TEXT PRIMARY KEY, n_decls INTEGER NOT NULL, n_thm INTEGER NOT NULL,
    n_match_s1n INTEGER NOT NULL, n_match_s1t INTEGER NOT NULL, n_match_s1a INTEGER NOT NULL,
    n_strong INTEGER NOT NULL, n_thm_strong INTEGER NOT NULL, n_strong_s1a INTEGER NOT NULL);
CREATE TABLE control_sigs (            -- negative controls (hashes only)
    control TEXT NOT NULL, proof_id INTEGER NOT NULL,
    s1n TEXT NOT NULL, s1t TEXT NOT NULL, s1a TEXT NOT NULL, n_tokens INTEGER NOT NULL,
    hit_s1n INTEGER NOT NULL DEFAULT 0, hit_s1t INTEGER NOT NULL DEFAULT 0,
    hit_s1a INTEGER NOT NULL DEFAULT 0);
CREATE TABLE control_restate (         -- synthetic held-out restatement control
    corpus_id INTEGER PRIMARY KEY, n_tokens INTEGER NOT NULL, extracted INTEGER NOT NULL,
    outcome_s1n TEXT NOT NULL, outcome_s1t TEXT NOT NULL, outcome_s1a TEXT NOT NULL);
CREATE TABLE controls (
    control TEXT NOT NULL, variant TEXT NOT NULL, min_tokens INTEGER NOT NULL,
    n INTEGER NOT NULL, tp INTEGER, fp INTEGER, fn INTEGER,
    precision REAL, recall REAL, fpr REAL, note TEXT,
    PRIMARY KEY (control, variant, min_tokens));
CREATE VIEW matches_view AS
    SELECT m.proof_id, p.module AS proof_module, p.line_no AS proof_line, p.kind AS proof_kind,
           p.name AS proof_name, p.n_local AS proof_n_local,
           m.variant, m.sighash, m.n_tokens, m.grade, m.n_candidates,
           m.corpus_id, m.repo, m.commit_sha, m.license, m.corpus_name,
           s.module AS corpus_module, s.line_no AS corpus_line, s.kind AS corpus_kind,
           s.n_local AS corpus_n_local, s.sig_text AS corpus_sig_text,
           m.same_short_name, m.provenance
    FROM matches m
    JOIN proof_sigs p ON p.id = m.proof_id
    JOIN corpus_sigs s ON s.id = m.corpus_id;
"""
INDEXES = """
CREATE INDEX corpus_s1n ON corpus_sigs(s1n);
CREATE INDEX corpus_s1t ON corpus_sigs(s1t);
CREATE INDEX corpus_s1a ON corpus_sigs(s1a);
CREATE INDEX corpus_name ON corpus_sigs(name);
CREATE INDEX proof_module ON proof_sigs(module);
CREATE INDEX proof_name ON proof_sigs(name);
CREATE INDEX proof_s1n ON proof_sigs(s1n);
CREATE INDEX proof_s1a ON proof_sigs(s1a);
CREATE INDEX matches_grade ON matches(grade, variant);
CREATE INDEX matches_corpus ON matches(corpus_id);
"""


# --------------------------------------------------------------------------- workers
def _sig_text(d: Dict[str, Any]) -> str:
    s = " ".join(d["var_binders"] + d["own_binders"])
    s = (s + " : " + d["type"]) if d["type"] else s
    s = " ".join(s.split())
    return s if len(s) <= SIG_TEXT_MAX else s[:SIG_TEXT_MAX - 1] + "…"


def _make_resolver(lex: Any, ns: str, opens: Sequence[str]):
    if lex is None:
        return None
    return lambda tok: lex.resolve_source(tok, ns, opens)


def _corpus_batch(args: Tuple[str, List[Tuple[str, str]]]) -> List[Tuple]:
    repo, items = args
    lex = _WORKER_LEXICONS.get(repo)
    rows: List[Tuple] = []
    for mod, path in items:
        with open(path, encoding="utf-8", errors="replace") as f:
            text = f.read()
        for d in extract_decls(text):
            binders = d["var_binders"] + d["own_binders"]
            if not d["type"] and (not binders or d["kind"] in THEOREM_KINDS):
                continue  # nothing to hash / statement could not be cut (documented limit)
            res = _make_resolver(lex, d["namespace"], d["opens"])
            h = tier2_sig.sig_hashes(binders, d["type"], resolve=res)
            rows.append((repo, mod, d["line"], d["kind"], d["name"], d["private"],
                         h.s1n, h.s1t, h.s1a, h.n_tokens, h.n_local, _sig_text(d)))
    return rows


_PERM_KEEP = {
    "fun", "Type", "Sort", "Prop", "in", "if", "then", "else", "let", "have", "show", "from",
    "at", "by", "do", "match", "with", "λ", "_",
}


def _perm_sub(text: str, mapping: Dict[str, str]) -> str:
    return RE_IDENT.sub(lambda m: mapping.get(m.group(0), m.group(0)), text)


def _proof_batch(args: Tuple[int, List[Tuple[str, str]]]) -> Tuple[List[Tuple], List[Tuple]]:
    """Returns (proof rows, control rows). Control rows reference the row index in the batch.

    Negative controls, built from the real proof signatures of this batch:
      swap  -- binders of declaration i with the result type of another declaration j
               (random derangement within the batch): well-formed-looking, wrong statement.
      perm  -- every identifier of the signature pushed through one random permutation of
               the batch's identifier vocabulary: same shape, shuffled constants.
    A control signature identical to its original (e.g. pure-notation statements that the
    permutation cannot change) is dropped, not counted.
    """
    seed, items = args
    rng = random.Random(seed)
    lex = _WORKER_LEXICONS.get("__proof__")
    rows: List[Tuple] = []
    sigs: List[Tuple[List[str], str, str, Tuple[str, ...]]] = []
    for mod, path in items:
        with open(path, encoding="utf-8", errors="replace") as f:
            text = f.read()
        for d in extract_decls(text):
            binders = d["var_binders"] + d["own_binders"]
            if not d["type"] and (not binders or d["kind"] in THEOREM_KINDS):
                continue  # nothing to hash / statement could not be cut (documented limit)
            res = _make_resolver(lex, d["namespace"], d["opens"])
            h = tier2_sig.sig_hashes(binders, d["type"], resolve=res)
            rows.append((mod, d["line"], d["kind"], d["name"],
                         h.s1n, h.s1t, h.s1a, h.n_tokens, h.n_local))
            sigs.append((binders, d["type"], d["namespace"], d["opens"]))
    ctl: List[Tuple] = []
    thm_idx = [i for i, r in enumerate(rows) if r[2] in THEOREM_KINDS and sigs[i][1]]
    if len(thm_idx) >= 2:
        shuffled = thm_idx[:]
        rng.shuffle(shuffled)
        partner = {a: b for a, b in zip(shuffled, shuffled[1:] + shuffled[:1])}
        vocab = sorted({m.group(0) for i in thm_idx
                        for m in RE_IDENT.finditer(" ".join(sigs[i][0]) + " " + sigs[i][1])}
                       - _PERM_KEEP)
        perm = vocab[:]
        rng.shuffle(perm)
        mapping = dict(zip(vocab, perm))
        for i in thm_idx:
            binders, ty, ns, opens = sigs[i]
            res = _make_resolver(lex, ns, opens)
            j = partner[i]
            if sigs[j][1] != ty:
                h = tier2_sig.sig_hashes(binders, sigs[j][1], resolve=res)
                if h.s1n != rows[i][4]:
                    ctl.append(("swap", i, h.s1n, h.s1t, h.s1a, h.n_tokens))
            pb = [_perm_sub(b, mapping) for b in binders]
            pt = _perm_sub(ty, mapping)
            h = tier2_sig.sig_hashes(pb, pt, resolve=res)
            if h.s1n != rows[i][4]:
                ctl.append(("perm", i, h.s1n, h.s1t, h.s1a, h.n_tokens))
    return rows, ctl


# ------------------------------------------------- synthetic restatement control
_FLIP = {"{": ("(", ")"), "(": ("{", "}"), "⦃": ("(", ")"), "[": ("[", "]")}


def _rename_idents(text: str, ren: Dict[str, str]) -> str:
    def sub(m: "re.Match[str]") -> str:
        t = m.group(0)
        if t in ren:
            return ren[t]
        head, dot, rest = t.partition(".")
        if dot and head in ren:
            return ren[head] + "." + rest
        return t
    return RE_IDENT.sub(sub, text)


def restate(d: Dict[str, Any], idx: int, rng: random.Random) -> Optional[str]:
    """Render declaration record `d` as a cosmetically different, standalone source text:
    new declaration name + namespace, alpha-renamed binders, flipped binder kinds, renamed
    universes, some leading binders moved into a `variable` line, reflowed whitespace, and
    an unrelated proof body. The statement itself is unchanged."""
    groups = d["var_binders"] + d["own_binders"]
    ty = d["type"]
    if not ty:
        return None
    parsed = [parse_binder(g) for g in groups]
    names: List[str] = []
    for _k, nms, _t in parsed:
        names.extend(n for n in nms if n != "_")
    ren = {n: "zq%d_%d" % (idx, i) for i, n in enumerate(dict.fromkeys(names))}
    alltext = " ".join(groups) + " " + ty
    for m in re.finditer(r"\b(?:Type|Sort)\s+([^\W\d][\w']*)", alltext):
        u = m.group(1)
        if u not in ren:
            ren[u] = "uq%d_%d" % (idx, len(ren))
    out_groups: List[str] = []
    for kind, nms, t in parsed:
        o, c = _FLIP[kind]
        t2 = _rename_idents(t, ren)
        if kind == "[":
            pre = (" ".join(ren.get(n, n) for n in nms) + " : ") if nms else ""
            out_groups.append("[" + pre + t2 + "]")
        else:
            nm2 = " ".join(ren.get(n, n) for n in nms)
            out_groups.append(o + nm2 + ((" : " + t2) if t2 else "") + c)
    ty2 = _rename_idents(ty, ren)
    # move a leading run of binders into `variable` when Lean would re-include them
    rest_text = lambda k: " ".join(out_groups[k + 1:]) + " " + ty2  # noqa: E731
    n_var = 0
    moved: set = set()
    if rng.random() < 0.5:
        for k, (kind, nms, _t) in enumerate(parsed):
            later = {m.group(0).split(".")[0] for m in RE_IDENT.finditer(rest_text(k))}
            new_nms = [ren.get(n, n) for n in nms]
            if kind == "[":
                deps = {m.group(0).split(".")[0] for m in RE_IDENT.finditer(out_groups[k])}
                if nms or not (deps & moved) or not (deps & set(ren.values()) <= moved):
                    break
            elif not new_nms or not all(n in later for n in new_nms) or "_" in nms:
                break
            moved.update(new_nms)
            n_var = k + 1
    sep = rng.choice([" ", "\n    ", "  ", "\n      "])
    kw = rng.choice(THEOREM_KINDS)
    lines = []
    univs = sorted(v for v in ren.values() if v.startswith("uq"))
    if univs:
        lines.append("universe " + " ".join(univs))
    lines.append("namespace Ctl%d" % idx)
    if n_var:
        lines.append("variable " + sep.join(out_groups[:n_var]))
    hdr = "%s restated_%d %s :%s%s := by" % (
        kw, idx, sep.join(out_groups[n_var:]), sep, ty2)
    lines.append(hdr)
    lines.append("  simp [foo_%d] at this ⊢" % rng.randrange(10 ** 6))
    lines.append("  exact fun h => (h : True := trivial)")
    lines.append("end Ctl%d" % idx)
    return "\n".join(lines) + "\n"


def _restate_batch(args: Tuple[int, List[Tuple[str, str, str, List[Tuple[int, int]]]]]) -> List[Tuple]:
    """For held-out corpus files: re-extract, restate each theorem, push the restated text
    through the full extract+hash path. Returns (corpus_id, n_tokens, extracted, s1n, s1t, s1a)."""
    seed, items = args
    rng = random.Random(seed)
    out: List[Tuple] = []
    for repo, _mod, path, want in items:
        lex = _WORKER_LEXICONS.get(repo)
        by_line = dict(want)
        with open(path, encoding="utf-8", errors="replace") as f:
            text = f.read()
        for d in extract_decls(text):
            cid = by_line.get(d["line"])
            if cid is None or d["kind"] not in THEOREM_KINDS:
                continue
            synth = restate(d, cid, rng)
            if synth is None:
                continue
            got = [x for x in extract_decls(synth) if x["short"] == "restated_%d" % cid]
            if len(got) != 1:
                out.append((cid, 0, 0, "", "", ""))
                continue
            g = got[0]
            # Preserve the original lookup scope for lexicon resolution (as an `open` would)
            res = _make_resolver(lex, d["namespace"], d["opens"])
            h = tier2_sig.sig_hashes(g["var_binders"] + g["own_binders"], g["type"], resolve=res)
            out.append((cid, h.n_tokens, 1, h.s1n, h.s1t, h.s1a))
    return out


def _held_out(module: str) -> bool:
    """Deterministic 1/8 sample of corpus modules for the restatement control."""
    return hashlib.sha256(module.encode("utf-8")).digest()[0] < 32


# --------------------------------------------------------------------------- build
def _batches(items: Sequence, size: int) -> List[List]:
    return [list(items[i:i + size]) for i in range(0, len(items), size)]


def _pool(threads: int) -> "multiprocessing.pool.Pool":
    return multiprocessing.get_context("fork").Pool(processes=max(1, min(threads, MAX_THREADS)))


def _build_repo_lexicon(files: Sequence[Tuple[str, str]]) -> Any:
    if _sighash is None:
        return None
    names = set()
    for _mod, path in files:
        with open(path, encoding="utf-8", errors="replace") as f:
            text = f.read()
        for d in extract_decls(text):
            names.add(d["name"])
    return _sighash.Lexicon(names)


def _load_proof_lexicon(mirror_src: str, threads: int, verbose: bool) -> Any:
    if _sighash is None:
        return None
    if os.path.abspath(mirror_src) == os.path.abspath(MIRROR_SRC) and os.path.exists(PROOF_LEXICON_PATH):
        lex = _sighash.Lexicon.load(PROOF_LEXICON_PATH)
        if verbose:
            print(f"[tier2] loaded proof lexicon {lex.id} ({len(lex):,} names)", flush=True)
        return lex
    lex, _nf = _sighash.build_lexicon(mirror_src, workers=min(threads, 16))
    return lex


def build(db_path: str = DB_PATH, threads: int = MAX_THREADS, mirror_src: str = MIRROR_SRC,
          corpora: Optional[List[Dict[str, Any]]] = None, verbose: bool = True) -> None:
    """Extract + hash every corpus and the proof mirror into a fresh tier2.db."""
    global _WORKER_LEXICONS
    t0 = time.time()
    threads = max(1, min(threads, MAX_THREADS))
    if corpora is None:
        corpora = tier2_corpora.build_manifest(fetch=False, write=False)["corpora"]
        for c in corpora:
            c["root"] = os.path.join(tier2_corpora.CORPORA_DIR, c["name"])
    os.makedirs(os.path.dirname(db_path), exist_ok=True)
    final_path = db_path
    # Built aside as *_building.db (matches .gitignore outputs/**/*.db), renamed atomically at end.
    db_path = (final_path[:-3] + "_building.db") if final_path.endswith(".db") else (final_path + ".building")
    for suffix in ("", "-wal", "-shm", "-journal"):
        if os.path.exists(db_path + suffix):
            os.remove(db_path + suffix)
    conn = sqlite3.connect(db_path)
    conn.executescript("PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF;" + SCHEMA)

    def meta(k: str, v: Any) -> None:
        conn.execute("INSERT OR REPLACE INTO meta VALUES (?,?)", (k, json.dumps(v, sort_keys=True)))

    tier2_sig.sig_hashes([], "True")  # bind implementation before forking

    # Prepare lexicons before forking so workers inherit them copy-on-write:
    # - library repos (mathlib4/lean4/batteries) -> None (library names are never abstracted, §4)
    # - non-library external corpora -> per-repo Lexicon of that repo's declared names
    # - proof mirror -> pinned lexicon_rh.txt (or built in-memory for test fixtures)
    lexicons: Dict[str, Any] = {}
    corpus_files: Dict[str, List[Tuple[str, str]]] = {}
    for c in corpora:
        files = discover(c["root"], c["subdirs"])
        corpus_files[c["name"]] = files
        is_lib = c.get("is_library", c["name"] in LIBRARY_REPOS)
        lexicons[c["name"]] = None if is_lib else _build_repo_lexicon(files)
    proof_lex = _load_proof_lexicon(mirror_src, threads, verbose)
    lexicons["__proof__"] = proof_lex
    _WORKER_LEXICONS = lexicons

    meta("schema", "leanre.flirt.tier2/2")
    meta("sighash_impl", tier2_sig.IMPL_NAME)
    meta("threads", threads)
    if proof_lex is not None:
        meta("proof_lexicon_id", proof_lex.id)
        meta("proof_lexicon_names", len(proof_lex))

    with _pool(threads) as pool:
        # corpora
        for c in corpora:
            files = corpus_files[c["name"]]
            jobs = [(c["name"], b) for b in _batches(files, 40)]
            n = 0
            for rows in pool.imap(_corpus_batch, jobs, chunksize=1):
                conn.executemany(
                    "INSERT INTO corpus_sigs(repo,module,line_no,kind,name,is_private,"
                    "s1n,s1t,s1a,n_tokens,n_local,sig_text) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)", rows)
                n += len(rows)
            clex = lexicons[c["name"]]
            conn.execute("INSERT INTO corpora VALUES (?,?,?,?,?,?,?,?,?)", (
                c["name"], c["url"], c["commit"], c["license"], c.get("lean_toolchain"),
                c.get("mathlib_rev"), clex.id if clex is not None else None, len(files), n))
            if verbose:
                lx = f" lex={clex.id}" if clex is not None else " (library)"
                print(f"[tier2] {c['name']:24s} {len(files):6,d} files {n:8,d} signatures{lx} "
                      f"({time.time() - t0:.1f}s)", flush=True)
        # proof mirror
        files = discover(mirror_src)
        meta("proof_files", len(files))
        jobs = [(i, b) for i, b in enumerate(_batches(files, 300))]
        n = 0
        n_ctl = 0
        for rows, ctl in pool.imap(_proof_batch, jobs, chunksize=1):
            base = n + 1
            conn.executemany(
                "INSERT INTO proof_sigs(id,module,line_no,kind,name,s1n,s1t,s1a,n_tokens,n_local) "
                "VALUES (?,?,?,?,?,?,?,?,?,?)",
                [(base + i,) + r for i, r in enumerate(rows)])
            conn.executemany(
                "INSERT INTO control_sigs(control,proof_id,s1n,s1t,s1a,n_tokens) VALUES (?,?,?,?,?,?)",
                [(c, base + i, a, b, sa, k) for c, i, a, b, sa, k in ctl])
            n += len(rows)
            n_ctl += len(ctl)
        if verbose:
            print(f"[tier2] proof mirror            {len(files):6,d} files {n:8,d} signatures, "
                  f"{n_ctl:,} negative-control signatures ({time.time() - t0:.1f}s)", flush=True)
        conn.commit()

        # synthetic restatement control over held-out corpus modules
        roots = {c["name"]: c["root"] for c in corpora}
        want: Dict[Tuple[str, str], List[Tuple[int, int]]] = collections.defaultdict(list)
        for cid, repo, mod, line in conn.execute(
                "SELECT id, repo, module, line_no FROM corpus_sigs WHERE kind IN ('theorem','lemma')"):
            if _held_out(mod):
                want[(repo, mod)].append((line, cid))
        items = []
        for (repo, mod), lst in sorted(want.items()):
            sub = mod.replace(".", os.sep) + ".lean"
            items.append((repo, mod, os.path.join(roots[repo], sub), lst))
        jobs2 = [(i, b) for i, b in enumerate(_batches(items, 20))]
        restated: List[Tuple] = []
        for rows in pool.imap(_restate_batch, jobs2, chunksize=1):
            restated.extend(rows)
    _WORKER_LEXICONS = {}
    meta("restate_modules", len(items))
    conn.executescript(INDEXES)
    conn.commit()
    _finish(conn, restated, verbose=verbose)
    meta("build_seconds", round(time.time() - t0, 1))
    conn.commit()
    conn.close()
    os.replace(db_path, final_path)


def _rate(a: int, b: int) -> Optional[float]:
    return (a / b) if b else None


def _finish(conn: sqlite3.Connection, restated: List[Tuple], verbose: bool = True) -> None:
    """Match, score the controls, pick the pre-registered per-variant thresholds, fill summary."""
    idx: Dict[str, Dict[str, List[int]]] = {v: collections.defaultdict(list) for v in VARIANTS}
    cinfo: Dict[int, Tuple[str, str]] = {}
    for cid, repo, name, s1n, s1t, s1a in conn.execute(
            "SELECT id, repo, name, s1n, s1t, s1a FROM corpus_sigs ORDER BY id"):
        idx["s1n"][s1n].append(cid)
        idx["s1t"][s1t].append(cid)
        idx["s1a"][s1a].append(cid)
        cinfo[cid] = (repo, name)
    commit = dict(conn.execute("SELECT repo, commit_sha FROM corpora"))
    lic_map = dict(conn.execute("SELECT repo, license FROM corpora"))

    # ---- negative controls & per-variant FDR thresholds
    conn.execute(
        "UPDATE control_sigs SET "
        "hit_s1n = s1n IN (SELECT s1n FROM corpus_sigs), "
        "hit_s1t = s1t IN (SELECT s1t FROM corpus_sigs), "
        "hit_s1a = s1a IN (SELECT s1a FROM corpus_sigs)")
    ctl_rows: List[Tuple] = []
    fdr_by_var: Dict[str, Dict[int, float]] = {v: {} for v in VARIANTS}
    for T in THRESHOLD_GRID:
        for variant in VARIANTS:
            nq, real_hits = conn.execute(
                f"SELECT COUNT(*), COALESCE(SUM({variant} IN (SELECT {variant} FROM corpus_sigs)),0) "
                "FROM proof_sigs WHERE kind IN ('theorem','lemma') AND n_tokens>=?", (T,)).fetchone()
            exp_false = 0.0
            for control in ("swap", "perm"):
                n, fp = conn.execute(
                    f"SELECT COUNT(*), COALESCE(SUM(hit_{variant}),0) FROM control_sigs "
                    "WHERE control=? AND n_tokens>=?", (control, T)).fetchone()
                fpr = _rate(fp, n)
                ctl_rows.append(("neg_" + control, variant, T, n, None, fp, None, None, None, fpr,
                                 "false positives among shuffled proof theorem signatures"))
                if fpr is not None:
                    exp_false = max(exp_false, fpr * nq)
            fdr = min(1.0, exp_false / real_hits) if real_hits else 1.0
            ctl_rows.append(("fdr_estimate", variant, T, nq, real_hits, round(exp_false, 3), None,
                             1.0 - fdr, None, fdr,
                             "tp column = real theorem matches; fp = expected chance matches; "
                             "fpr column = estimated false-discovery rate"))
            fdr_by_var[variant][T] = fdr

    strong_T_by_var: Dict[str, int] = {}
    strong_ok_by_var: Dict[str, bool] = {}
    for v in VARIANTS:
        t_v = next((T for T in THRESHOLD_GRID if fdr_by_var[v][T] <= FDR_TARGET), THRESHOLD_GRID[-1])
        strong_T_by_var[v] = t_v
        strong_ok_by_var[v] = fdr_by_var[v][t_v] <= FDR_TARGET
    # Headline threshold (s1n/s1t): max of the two named/tail thresholds for backward compatibility
    strong_T = max(strong_T_by_var["s1n"], strong_T_by_var["s1t"])

    # ---- restatement control
    rrows = []
    for cid, ntok, extracted, s1n, s1t, s1a in restated:
        outc = []
        for variant, h in (("s1n", s1n), ("s1t", s1t), ("s1a", s1a)):
            cands = idx[variant].get(h) if extracted else None
            outc.append("fn" if not cands else ("tp" if cid in cands else "fp"))
        rrows.append((cid, ntok, extracted, outc[0], outc[1], outc[2]))
    conn.executemany("INSERT OR REPLACE INTO control_restate VALUES (?,?,?,?,?,?)", rrows)
    orig_tok = dict(conn.execute(
        "SELECT id, n_tokens FROM corpus_sigs WHERE id IN (SELECT corpus_id FROM control_restate)"))
    for T in THRESHOLD_GRID:
        for vi, variant in ((3, "s1n"), (4, "s1t"), (5, "s1a")):
            sel = [r for r in rrows if orig_tok[r[0]] >= T]
            tp = sum(1 for r in sel if r[vi] == "tp")
            fp = sum(1 for r in sel if r[vi] == "fp")
            fn = sum(1 for r in sel if r[vi] == "fn")
            ctl_rows.append(("restate_selfmatch", variant, T, len(sel), tp, fp, fn,
                             _rate(tp, tp + fp), _rate(tp, len(sel)), None,
                             "synthetic: held-out corpus theorems restated cosmetically"))
    conn.executemany("INSERT OR REPLACE INTO controls VALUES (?,?,?,?,?,?,?,?,?,?,?)", ctl_rows)

    # ---- real matches
    mrows: List[Tuple] = []
    crows: List[Tuple] = []
    for pid, name, kind, s1n, s1t, s1a, ntok in conn.execute(
            "SELECT id, name, kind, s1n, s1t, s1a, n_tokens FROM proof_sigs"):
        short = name.rsplit(".", 1)[-1]
        for variant, h in (("s1n", s1n), ("s1t", s1t), ("s1a", s1a)):
            cands = idx[variant].get(h)
            if not cands:
                continue
            if kind in THEOREM_KINDS:
                grade = "strong" if (ntok >= strong_T_by_var[variant] and strong_ok_by_var[variant]) else "weak"
            else:
                grade = "defsig"
            best = min(cands, key=lambda c: (
                cinfo[c][1].rsplit(".", 1)[-1] != short, cinfo[c][0] != "mathlib4", c))
            repo, cname = cinfo[best]
            mrows.append((pid, variant, h, ntok, grade,
                          len(cands), best, repo, commit[repo], lic_map[repo], cname,
                          int(cname.rsplit(".", 1)[-1] == short), "L"))
            for c in sorted(cands, key=lambda c: (
                    cinfo[c][1].rsplit(".", 1)[-1] != short, cinfo[c][0] != "mathlib4", c))[:5]:
                crows.append((pid, variant, c))
    conn.executemany("INSERT INTO matches VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)", mrows)
    conn.executemany("INSERT INTO match_candidates VALUES (?,?,?)", crows)
    conn.execute("""
        INSERT INTO module_summary
        SELECT p.module, COUNT(*), SUM(p.kind IN ('theorem','lemma')),
               SUM(m1.proof_id IS NOT NULL), SUM(m2.proof_id IS NOT NULL),
               SUM(m3.proof_id IS NOT NULL),
               SUM(COALESCE(m1.grade,'')='strong' OR COALESCE(m2.grade,'')='strong'),
               SUM((COALESCE(m1.grade,'')='strong' OR COALESCE(m2.grade,'')='strong')
                   AND p.kind IN ('theorem','lemma')),
               SUM(COALESCE(m3.grade,'')='strong')
        FROM proof_sigs p
        LEFT JOIN matches m1 ON m1.proof_id=p.id AND m1.variant='s1n'
        LEFT JOIN matches m2 ON m2.proof_id=p.id AND m2.variant='s1t'
        LEFT JOIN matches m3 ON m3.proof_id=p.id AND m3.variant='s1a'
        GROUP BY p.module""")
    conn.execute("INSERT OR REPLACE INTO meta VALUES ('strong_min_tokens', ?)", (json.dumps(strong_T),))
    conn.execute("INSERT OR REPLACE INTO meta VALUES ('strong_min_tokens_by_variant', ?)",
                 (json.dumps(strong_T_by_var, sort_keys=True),))
    conn.execute("INSERT OR REPLACE INTO meta VALUES ('strong_ok_by_variant', ?)",
                 (json.dumps(strong_ok_by_var, sort_keys=True),))
    conn.execute("INSERT OR REPLACE INTO meta VALUES ('fdr_target', ?)", (json.dumps(FDR_TARGET),))
    conn.execute("INSERT OR REPLACE INTO meta VALUES ('fdr_at_threshold', ?)",
                 (json.dumps({str(T): round(max(fdr_by_var["s1n"][T], fdr_by_var["s1t"][T]), 6)
                              for T in THRESHOLD_GRID}, sort_keys=True),))
    conn.execute("INSERT OR REPLACE INTO meta VALUES ('fdr_by_variant', ?)",
                 (json.dumps({v: {str(T): round(fdr_by_var[v][T], 6) for T in THRESHOLD_GRID}
                              for v in VARIANTS}, sort_keys=True),))
    conn.commit()
    if verbose:
        parts = [f"{v}:>={strong_T_by_var[v]}(fdr={fdr_by_var[v][strong_T_by_var[v]]:.4f},"
                 f"ok={strong_ok_by_var[v]})" for v in VARIANTS]
        print(f"[tier2] matches: {len(mrows):,} rows; strong thresholds: " + ", ".join(parts),
              flush=True)


# --------------------------------------------------------------------------- summary
def summary(db_path: str = DB_PATH, out_path: Optional[str] = SUMMARY_PATH) -> Dict[str, Any]:
    conn = sqlite3.connect("file:%s?mode=ro" % db_path, uri=True)
    q = lambda sql, *a: conn.execute(sql, a).fetchall()  # noqa: E731
    one = lambda sql, *a: conn.execute(sql, a).fetchone()[0]  # noqa: E731
    meta = {k: json.loads(v) for k, v in q("SELECT key, value_json FROM meta")}
    T = meta["strong_min_tokens"]
    T_by_v = meta.get("strong_min_tokens_by_variant", {"s1n": T, "s1t": T, "s1a": T})
    ok_by_v = meta.get("strong_ok_by_variant", {"s1n": True, "s1t": True, "s1a": True})
    n_proof = one("SELECT COUNT(*) FROM proof_sigs")
    n_thm = one("SELECT COUNT(*) FROM proof_sigs WHERE kind IN ('theorem','lemma')")
    out: Dict[str, Any] = {
        "schema": "leanre.flirt.tier2_summary/2",
        "provenance": "[L] extracted by us from the pinned proof mirror and pinned public repos",
        "meaning_of_a_match": (
            "Same normalized statement shape (source text, no elaboration, no name resolution). "
            "NOT evidence that the same mathematics is proved; unmatched is NOT evidence of "
            "novelty (source-level recall is limited, see controls and limits)."),
        "sighash_impl": meta.get("sighash_impl"),
        "proof_lexicon_id": meta.get("proof_lexicon_id"),
        "proof_lexicon_names": meta.get("proof_lexicon_names"),
        "strong_rule": (
            f"strong (per variant) = theorem/lemma match with n_tokens >= T_variant, where "
            f"T_variant is the smallest grid threshold with estimated FDR <= {meta['fdr_target']} "
            f"(negative-control hits rescaled / real matches); if no grid threshold reaches "
            f"<= {meta['fdr_target']}, strong_ok=false and all matches for that variant stay 'weak'. "
            f"Non-theorem kinds are graded 'defsig' (type shape only) and never 'strong'."),
        "strong_min_tokens": T,
        "strong_min_tokens_by_variant": T_by_v,
        "strong_ok_by_variant": ok_by_v,
        "estimated_fdr_by_min_tokens": meta.get("fdr_at_threshold"),
        "estimated_fdr_by_variant": meta.get("fdr_by_variant"),
        "corpora": [dict(zip(("repo", "commit", "license", "lean_toolchain", "lexicon_id",
                              "files", "signatures"), r))
                    for r in q("SELECT repo, commit_sha, license, lean_toolchain, lexicon_id, "
                               "lean_files, decls FROM corpora ORDER BY decls DESC")],
        "proof": {
            "files": meta.get("proof_files"),
            "signatures": n_proof,
            "theorem_signatures": n_thm,
            "distinct_s1n": one("SELECT COUNT(DISTINCT s1n) FROM proof_sigs"),
            "distinct_s1t": one("SELECT COUNT(DISTINCT s1t) FROM proof_sigs"),
            "distinct_s1a": one("SELECT COUNT(DISTINCT s1a) FROM proof_sigs"),
            "with_local_refs": one("SELECT COUNT(*) FROM proof_sigs WHERE n_local>0"),
            "by_kind": dict(q("SELECT kind, COUNT(*) FROM proof_sigs GROUP BY 1 ORDER BY 2 DESC")),
        },
        "matches": {},
        "controls": [dict(zip(("control", "variant", "min_tokens", "n", "tp", "fp", "fn",
                               "precision", "recall", "fpr"), r))
                     for r in q("SELECT control, variant, min_tokens, n, tp, fp, fn, precision, "
                                "recall, fpr FROM controls ORDER BY control, variant, min_tokens")],
    }
    for variant in VARIANTS:
        for grade in ("strong", "weak", "defsig"):
            rows = q("SELECT COUNT(*), COUNT(DISTINCT sighash), SUM(same_short_name), "
                     "SUM(n_candidates>1) FROM matches WHERE variant=? AND grade=?", variant, grade)[0]
            entry = {
                "proof_decls": rows[0], "distinct_signatures": rows[1],
                "same_short_name": rows[2] or 0, "ambiguous_multi_candidate": rows[3] or 0,
                "share_of_proof_signatures": round(rows[0] / n_proof, 6) if n_proof else None,
                "by_repo": dict(q("SELECT repo, COUNT(*) FROM matches WHERE variant=? AND grade=? "
                                  "GROUP BY 1 ORDER BY 2 DESC", variant, grade)),
                "by_kind": dict(q("SELECT p.kind, COUNT(*) FROM matches m JOIN proof_sigs p ON "
                                  "p.id=m.proof_id WHERE m.variant=? AND m.grade=? GROUP BY 1 "
                                  "ORDER BY 2 DESC", variant, grade)),
            }
            if variant == "s1a":
                entry["extra_over_s1t_with_local_abstraction"] = one(
                    "SELECT COUNT(*) FROM matches m JOIN proof_sigs p ON p.id=m.proof_id "
                    "JOIN corpus_sigs s ON s.id=m.corpus_id "
                    "WHERE m.variant='s1a' AND m.grade=? AND (p.n_local>0 OR s.n_local>0)", grade)
            out["matches"][f"{variant}_{grade}"] = entry
    out["modules"] = {
        "with_signatures": one("SELECT COUNT(*) FROM module_summary"),
        "with_any_strong_match": one("SELECT COUNT(*) FROM module_summary WHERE n_strong>0"),
        "with_any_strong_s1a_match": one("SELECT COUNT(*) FROM module_summary WHERE n_strong_s1a>0"),
        "all_theorems_strong_matched": one(
            "SELECT COUNT(*) FROM module_summary WHERE n_thm>0 AND n_thm_strong=n_thm"),
        "no_match_at_all": one("SELECT COUNT(*) FROM module_summary WHERE n_match_s1t=0 AND n_match_s1a=0"),
    }
    out["by_top_namespace"] = [
        dict(zip(("namespace", "modules", "signatures", "strong_matches", "modules_with_strong"), r))
        for r in q("""SELECT CASE WHEN instr(module,'.')>0 THEN substr(module,1,instr(module,'.')-1)
                             ELSE module END AS ns, COUNT(*), SUM(n_decls), SUM(n_strong),
                             SUM(n_strong>0) FROM module_summary GROUP BY ns ORDER BY 3 DESC""")]
    out["top_matched_corpus_decls"] = [
        dict(zip(("repo", "name", "proof_decls"), r))
        for r in q("SELECT repo, corpus_name, COUNT(*) FROM matches WHERE variant='s1t' AND "
                   "grade='strong' GROUP BY corpus_id ORDER BY 3 DESC, 2 LIMIT 25")]
    # Candidate multiplicity on synthetic restatement TPs (unique-match rate + mean candidates)
    restate_mult: Dict[str, Any] = {}
    for v in VARIANTS:
        row = q(f"""
            WITH counts AS (SELECT {v} AS h, COUNT(*) AS cnt FROM corpus_sigs GROUP BY {v})
            SELECT COUNT(*), COALESCE(SUM(counts.cnt=1),0), AVG(counts.cnt), MAX(counts.cnt)
            FROM control_restate r
            JOIN corpus_sigs s ON s.id = r.corpus_id
            JOIN counts ON counts.h = s.{v}
            WHERE r.outcome_{v} = 'tp'""")[0]
        tp_n = row[0]
        restate_mult[v] = {
            "tp": tp_n,
            "unique_match": row[1],
            "unique_match_rate": round(row[1] / tp_n, 6) if tp_n else None,
            "mean_candidates": round(row[2], 4) if row[2] is not None else None,
            "max_candidates": row[3],
        }
    out["restate_multiplicity"] = restate_mult
    for k in ("kernel", ):
        if k in meta:
            out[k] = meta[k]
    conn.close()
    if out_path:
        with open(out_path, "w", encoding="utf-8") as f:
            json.dump(out, f, indent=1, sort_keys=True, ensure_ascii=False)
            f.write("\n")
    return out


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("cmd", choices=["all", "build", "summary", "kernel"])
    ap.add_argument("--threads", type=int, default=MAX_THREADS)
    ap.add_argument("--db", default=DB_PATH)
    a = ap.parse_args(argv)
    if a.cmd in ("all", "build"):
        build(a.db, threads=a.threads)
    if a.cmd == "kernel":
        import tier2_kernel
        tier2_kernel.run(a.db)
    if a.cmd in ("all", "summary", "kernel"):
        s = summary(a.db)
        print(json.dumps({k: s[k] for k in ("strong_min_tokens", "matches", "modules")}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
