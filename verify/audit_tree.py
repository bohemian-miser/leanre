#!/usr/bin/env python3
"""R2 tree audit (verifier-owned). Checks every path in `git ls-files` PLUS untracked,
non-ignored files (`git ls-files -o --exclude-standard`), since those are what a careless
`git add` would publish.

Checks:
  a. no *.lean, nothing under data/ or research/sources/, no *.ndjson(.zst), no *.olean
  b. no file > 5 MB
  c. secrets: private keys, common token shapes, password assignments
  d. internal hostnames / corp identifiers that should not be published
  e. absolute home paths (informational; leaks LDAP + host layout)
  f. verbatim proof-source leakage: any line of >= MINLEN chars from data/rh_mirror that
     appears verbatim in a tracked text file and is not a 1-line declaration header /
     import / namespace line (run with --leak; needs the mirror)
Exit 1 on any a/b/c/d/f finding. (e is reported, judged by the verifier.)
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)


def git(*a):
    return subprocess.run(["git", *a], capture_output=True, text=True, check=True).stdout


SECRET_RES = [
    ("private-key", re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----")),
    ("github-token", re.compile(r"\b(ghp|gho|ghu|ghs|ghr)_[A-Za-z0-9]{30,}\b|\bgithub_pat_[A-Za-z0-9_]{40,}\b")),
    ("google-api-key", re.compile(r"\bAIza[0-9A-Za-z_\-]{35}\b")),
    ("aws-key", re.compile(r"\bAKIA[0-9A-Z]{16}\b")),
    ("slack-token", re.compile(r"\bxox[baprs]-[A-Za-z0-9-]{10,}\b")),
    ("oauth-token", re.compile(r"\bya29\.[A-Za-z0-9_\-]{20,}\b")),
    ("anthropic/openai-key", re.compile(r"\bsk-[A-Za-z0-9_\-]{24,}\b")),
    ("bearer", re.compile(r"(?i)authorization:\s*bearer\s+[A-Za-z0-9._\-]{16,}")),
    ("password-assign", re.compile(r"(?i)\b(password|passwd|secret|api[_-]?key|token)\b\s*[:=]\s*['\"][^'\"\s]{8,}['\"]")),
]
INTERNAL_RES = [
    ("corp-host", re.compile(r"(?i)\b[\w.-]+\.(corp|prod|internal)\.[a-z0-9-]+\.(com|net|org)\b|\b[\w.-]+\.(internal|corp\.local)\b")),
    ("home-path", re.compile(r"/usr/local/[^/\s]+/home/")),
    ("scratch-dir", re.compile(r"\.[a-z0-9_-]+/brain/[0-9a-f-]{20,}", re.I)),
]
HOME_RE = re.compile(r"/Users/[A-Za-z0-9_.-]+|/home/[A-Za-z0-9_.-]+|/usr/local/[^/\s]+/home/[A-Za-z0-9_.-]+")


def is_text(path):
    try:
        with open(path, "rb") as f:
            return b"\0" not in f.read(8192)
    except OSError:
        return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--leak", action="store_true", help="also scan for verbatim mirror lines (slow, ~1 GB read)")
    ap.add_argument("--minlen", type=int, default=60)
    ap.add_argument("--max-show", type=int, default=40)
    a = ap.parse_args()

    tracked = [p for p in git("ls-files", "-z").split("\0") if p]
    untracked = [p for p in git("ls-files", "-o", "--exclude-standard", "-z").split("\0") if p]
    files = [(p, "T") for p in tracked] + [(p, "U") for p in untracked]
    print(f"tracked={len(tracked)} untracked-not-ignored={len(untracked)} HEAD={git('rev-parse','--short','HEAD').strip()}")
    hard = 0
    findings = {"path": [], "size": [], "secret": [], "internal": [], "home": []}
    for p, st in files:
        if not os.path.lexists(p):
            continue
        is_tiny_demo = (
            p.startswith("examples/tiny_demo/")
            and not os.path.islink(p)
            and os.path.isfile(p)
            and os.path.getsize(p) <= 128 * 1024
        )
        if (re.search(r"\.(lean|olean|ndjson)$|\.ndjson\.zst$", p) and not is_tiny_demo) or p.startswith(("data/", "research/sources/")) or p == "data":
            findings["path"].append(f"[{st}] {p}")
        if os.path.islink(p):
            findings["path"].append(f"[{st}] {p} is a symlink -> {os.readlink(p)}")
            continue
        sz = os.path.getsize(p)
        if sz > 5 * 1024 * 1024:
            findings["size"].append(f"[{st}] {p} {sz:,} B")
        if not is_text(p):
            continue
        with open(p, "r", encoding="utf-8", errors="replace") as f:
            for ln, line in enumerate(f, 1):
                for tag, rx in SECRET_RES:
                    m = rx.search(line)
                    if m:
                        findings["secret"].append(f"[{st}] {p}:{ln} {tag}: {m.group(0)[:60]}")
                for tag, rx in INTERNAL_RES:
                    m = rx.search(line)
                    if m:
                        findings["internal"].append(f"[{st}] {p}:{ln} {tag}: {m.group(0)[:80]}")
                m = HOME_RE.search(line)
                if m:
                    findings["home"].append(f"[{st}] {p}:{ln} {m.group(0)}")
    for k in ("path", "size", "secret", "internal", "home"):
        v = findings[k]
        print(f"\n== {k}: {len(v)} finding(s)")
        for x in v[: a.max_show]:
            print("  ", x)
        if len(v) > a.max_show:
            print(f"   ... +{len(v)-a.max_show} more")
        if k != "home":
            hard += len(v)

    if a.leak:
        hard += leak_scan(files, a.minlen, a.max_show)
    print(f"\nR2-AUDIT hard_findings={hard}")
    sys.exit(1 if hard else 0)


HEADER_RE = re.compile(r"^\s*(@\[[^\]]*\]\s*)*(private |protected |noncomputable |nonrec |unsafe |partial )*"
                       r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque|example|import|namespace|open|end|section|universe|variable|set_option|macro|syntax|elab)\b")
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.\u2080-\u2089]*$")


def leak_scan(files, minlen, max_show):
    """Verbatim-line containment: tracked lines (stripped, >= minlen) that equal a stripped
    line of the mirror. Bare single-token qualified Lean identifiers and 1-line declaration
    headers/imports are reported separately (allowed by R2) from proof-body lines (not allowed)."""
    cand = {}
    for p, st in files:
        if os.path.islink(p) or not os.path.exists(p) or not is_text(p) or p.startswith("verify/out/"):
            continue
        with open(p, "r", encoding="utf-8", errors="replace") as f:
            for ln, line in enumerate(f, 1):
                s = line.strip()
                if len(s) >= minlen:
                    cand.setdefault(s, []).append(f"{p}:{ln}")
                # JSON-escaped / embedded snippets: also test long quoted substrings
                for m in re.finditer(r'"((?:[^"\\]|\\.){%d,})"' % minlen, line):
                    try:
                        u = bytes(m.group(1), "utf-8").decode("unicode_escape").encode("latin-1", "ignore").decode("utf-8", "ignore").strip()
                    except Exception:
                        u = m.group(1).strip()
                    for part in u.split("\n"):
                        part = part.strip()
                        if len(part) >= minlen:
                            cand.setdefault(part, []).append(f"{p}:{ln}(str)")
    print(f"\n== leak scan: {len(cand):,} candidate lines/strings of >= {minlen} chars; streaming mirror ...")
    hits = {}
    n = 0
    src = os.path.join(ROOT, "data", "rh_mirror")
    for dp, dn, fn in os.walk(src, followlinks=True):
        if ".git" in dn:
            dn.remove(".git")
        for x in fn:
            if not x.endswith(".lean"):
                continue
            n += 1
            with open(os.path.join(dp, x), "r", encoding="utf-8", errors="replace") as f:
                for line in f:
                    s = line.strip()
                    if len(s) >= minlen and s in cand and s not in hits:
                        hits[s] = os.path.relpath(os.path.join(dp, x), src)
    ident = {s: w for s, w in hits.items() if IDENT_RE.match(s)}
    hdr = {s: w for s, w in hits.items() if not IDENT_RE.match(s) and HEADER_RE.match(s)}
    body = {s: w for s, w in hits.items() if not IDENT_RE.match(s) and not HEADER_RE.match(s)}
    print(f"   mirror files scanned: {n:,}; verbatim hits: {len(hits)} (bare idents: {len(ident)}, 1-line headers/imports: {len(hdr)}, BODY lines: {len(body)})")
    # multi-line check: same tracked file quoting >= 3 DISTINCT non-ident mirror lines from the same mirror file
    per = {}
    for s, w in hits.items():
        if s in ident:
            continue
        for loc in cand[s]:
            per.setdefault((loc.split(":")[0], w), set()).add(s)
    multi = {k: sorted(v) for k, v in per.items() if len(v) >= 3}
    for s, w in list(body.items())[:max_show]:
        print(f"   BODY  {cand[s][0]}  <- {w}: {s[:110]}")
    for s, w in list(hdr.items())[:10]:
        print(f"   hdr   {cand[s][0]}  <- {w}: {s[:110]}")
    for s, w in list(ident.items())[:10]:
        print(f"   ident {cand[s][0]}  <- {w}: {s[:110]}")
    print(f"   (tracked file, mirror file) pairs sharing >= 3 distinct non-ident mirror lines: {len(multi)}")
    for (p, w), v in list(multi.items())[:max_show]:
        print(f"   MULTI {p} <- {w}: {len(v)} distinct lines")
    return len(body) + len(multi)


if __name__ == "__main__":
    main()
