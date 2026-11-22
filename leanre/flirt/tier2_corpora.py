#!/usr/bin/env python3
"""FLIRT Tier 2 -- pinned public corpora (clone + manifest).

Clones each corpus into data/corpora/<name> at an exact commit (shallow, detached) and
writes outputs/flirt/tier2_corpora.json with URL, commit SHA, license and file counts.
Corpora are NEVER committed (data/ is gitignored); only the manifest is.

Mathlib's pin is not chosen by us: it is read from the proof mirror's lake-manifest.json,
so the DB is built from exactly the Mathlib the proof compiles against. The other corpora
are pinned to the HEAD we observed on the build date (they track newer toolchains; the
manifest records each one's own lean-toolchain and Mathlib rev so the skew is explicit).
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from typing import Any, Dict, List, Optional

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
CORPORA_DIR = os.path.join(REPO, "data", "corpora")
MIRROR = os.path.join(REPO, "data", "rh_mirror")
MANIFEST = os.path.join(REPO, "outputs", "flirt", "tier2_corpora.json")

# name -> (url, pinned commit or None = "take from the proof's lake-manifest", source subdirs)
PINS: Dict[str, Dict[str, Any]] = {
    "mathlib4": {
        "url": "https://github.com/leanprover-community/mathlib4",
        "commit": None, "manifest_name": "mathlib",
        "subdirs": ["Mathlib"],
        "role": "the exact Mathlib revision the proof pins (lake-manifest.json)",
    },
    "batteries": {
        "url": "https://github.com/leanprover-community/batteries",
        "commit": None, "manifest_name": "batteries",
        "subdirs": ["Batteries"],
        "role": "Batteries at the revision the proof pins (Mathlib dependency)",
    },
    "lean4": {
        "url": "https://github.com/leanprover/lean4",
        "commit": "819816b2e0a3bf405af45ae5c7af2491d8f5bee6",
        "subdirs": ["src/Init", "src/Std"],
        "role": "Lean core library (Init, Std) at the release tag in the proof's lean-toolchain",
    },
    "PrimeNumberTheoremAnd": {
        "url": "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd",
        "commit": "a4fb6989b07e9c76b511807ae93e33e25b820e9b",
        "subdirs": ["PrimeNumberTheoremAnd"],
        "role": "analytic number theory (PNT+), HEAD observed 2026-11-22",
    },
    "FLT": {
        "url": "https://github.com/ImperialCollegeLondon/FLT",
        "commit": "019805815d7da565ed1e9f427b6fbd0cbc9d00d3",
        "subdirs": ["FLT"],
        "role": "Imperial FLT project, HEAD observed 2026-11-22",
    },
    "carleson": {
        "url": "https://github.com/fpvandoorn/carleson",
        "commit": "f7487cc9da4d1e73f009dc0280cd5b958f3e2c78",
        "subdirs": ["Carleson"],
        "role": "Carleson project, HEAD observed 2026-11-22",
    },
    "SpherePacking": {
        "url": "https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean",
        "commit": "e07215872319dcadd7ced28670ae4daa13b74b8d",
        "subdirs": ["SpherePacking"],
        "role": "Sphere packing project, HEAD observed 2026-11-22",
    },
}


def _git(cwd: str, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True,
                          text=True).stdout.strip()


def proof_pins(mirror: str = MIRROR) -> Dict[str, str]:
    with open(os.path.join(mirror, "lake-manifest.json"), encoding="utf-8") as f:
        man = json.load(f)
    return {p["name"]: p["rev"] for p in man["packages"]}


def resolved_pins(mirror: str = MIRROR) -> Dict[str, Dict[str, Any]]:
    pp = proof_pins(mirror)
    out: Dict[str, Dict[str, Any]] = {}
    for name, spec in PINS.items():
        s = dict(spec)
        if s["commit"] is None:
            s["commit"] = pp[s["manifest_name"]]
            s["pin_source"] = "data/rh_mirror/lake-manifest.json"
        else:
            s["pin_source"] = "leanre/flirt/tier2_corpora.py PINS"
        out[name] = s
    return out


def _license_id(text: str) -> str:
    head = " ".join(text.split())[:400]
    if "Apache License" in head and "Version 2.0" in head:
        return "Apache-2.0"
    if "MIT License" in head:
        return "MIT"
    return "UNKNOWN"


def ensure(name: str, spec: Dict[str, Any], fetch: bool = True) -> Dict[str, Any]:
    d = os.path.join(CORPORA_DIR, name)
    if not os.path.isdir(os.path.join(d, ".git")):
        if not fetch:
            raise FileNotFoundError(d)
        os.makedirs(d, exist_ok=True)
        _git(d, "init", "-q")
        _git(d, "remote", "add", "origin", spec["url"])
    head: Optional[str]
    try:
        head = _git(d, "rev-parse", "HEAD")
    except subprocess.CalledProcessError:
        head = None
    if head != spec["commit"]:
        if not fetch:
            raise RuntimeError(f"{name}: HEAD {head} != pin {spec['commit']}")
        _git(d, "fetch", "-q", "--depth", "1", "origin", spec["commit"])
        _git(d, "checkout", "-q", "--detach", "FETCH_HEAD")
        head = _git(d, "rev-parse", "HEAD")
    assert head == spec["commit"], (name, head, spec["commit"])
    dirty = _git(d, "status", "--porcelain")
    lic_file = next((f for f in sorted(os.listdir(d))
                     if f.upper().startswith(("LICENSE", "COPYING"))), None)
    lic_text = open(os.path.join(d, lic_file), "rb").read() if lic_file else b""
    n_lean = 0
    n_bytes = 0
    for sub in spec["subdirs"]:
        for dp, dns, fns in os.walk(os.path.join(d, sub)):
            dns[:] = [x for x in dns if x not in (".lake", ".git")]
            for fn in fns:
                if fn.endswith(".lean"):
                    n_lean += 1
                    n_bytes += os.path.getsize(os.path.join(dp, fn))
    toolchain = None
    tc = os.path.join(d, "lean-toolchain")
    if os.path.exists(tc):
        toolchain = open(tc).read().strip()
    mathlib_rev = None
    lm = os.path.join(d, "lake-manifest.json")
    if os.path.exists(lm) and name != "mathlib4":
        for p in json.load(open(lm)).get("packages", []):
            if p.get("name") == "mathlib":
                mathlib_rev = p.get("rev")
    return {
        "name": name,
        "url": spec["url"],
        "commit": head,
        "pin_source": spec["pin_source"],
        "role": spec["role"],
        "commit_date": _git(d, "log", "-1", "--format=%cI"),
        "worktree_clean": dirty == "",
        "license": _license_id(lic_text.decode("utf-8", "replace")),
        "license_file": lic_file,
        "license_sha256": hashlib.sha256(lic_text).hexdigest() if lic_file else None,
        "lean_toolchain": toolchain,
        "mathlib_rev": mathlib_rev,
        "subdirs": spec["subdirs"],
        "lean_files": n_lean,
        "lean_bytes": n_bytes,
    }


def build_manifest(fetch: bool = True, write: bool = True) -> Dict[str, Any]:
    pins = resolved_pins()
    rows: List[Dict[str, Any]] = [ensure(n, s, fetch=fetch) for n, s in pins.items()]
    mirror_tc = open(os.path.join(MIRROR, "lean-toolchain")).read().strip()
    out = {
        "schema": "leanre.flirt.tier2_corpora/1",
        "provenance": "[L] extracted by us: git rev-parse HEAD + LICENSE file of each pinned clone",
        "proof_mirror": {
            "lean_toolchain": mirror_tc,
            "mirror_commit": _git(MIRROR, "rev-parse", "HEAD"),
            "mathlib_rev": proof_pins()["mathlib"],
        },
        "corpora": rows,
        "note": ("Corpora live under data/corpora/ (gitignored) and are never committed or "
                 "redistributed by this repo. Non-Mathlib corpora track newer toolchains than "
                 "the proof (see lean_toolchain / mathlib_rev per row)."),
    }
    if write:
        os.makedirs(os.path.dirname(MANIFEST), exist_ok=True)
        with open(MANIFEST, "w", encoding="utf-8") as f:
            json.dump(out, f, indent=1, sort_keys=True)
            f.write("\n")
    return out


if __name__ == "__main__":
    m = build_manifest(fetch="--no-fetch" not in sys.argv)
    for r in m["corpora"]:
        print(f"{r['name']:24s} {r['commit']} {r['license']:10s} {r['lean_files']:6d} files "
              f"{r['lean_toolchain']}")
    print("wrote", os.path.relpath(MANIFEST, REPO))
