#!/usr/bin/env python3
"""leanre.community — Curated & PR-extensible registry of independent analyses (`leanre.community/1`).

Loads canonical community entries from `notes/community/sources.json` (plus any
conflict-free drop-in PR files under `notes/community/contrib/*.json`), strictly
validates provenance, URLs, licensing tags, XSS/control-char safety, and
anti-overclaim/no-verbatim-Lean guardrails, then filters per project for
inclusion in exported static sites (`data/community.json`).

License: AGPL-3.0-or-later.
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
import re
from typing import Any, Dict, List, Optional, Sequence, Tuple

COMMUNITY_SCHEMA = "leanre.community/1"

VALID_CATEGORIES = frozenset({
    "official-statement",
    "kernel-check",
    "blueprint",
    "visualizer",
    "build-log",
    "math-review",
    "source-mirror",
    "commentary",
})

_ID_RE = re.compile(r"^[a-z0-9][a-z0-9._-]{1,79}$")
_DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
_HTTPS_URL_RE = re.compile(r"^https://[^\s<>\"]+$")
_CTRL_RE = re.compile(r"[\x00-\x08\x0b-\x1f\x7f\u2028\u2029]")
_XSS_RE = re.compile(r"<\s*(?:script|iframe|object|embed)\b|javascript\s*:|\bon(?:error|load|click)\s*=", re.I)
_HOST_PATH_RE = re.compile(r"(?:/usr/local/google|/google/src|/home/[A-Za-z0-9_.-]+|/Users/[A-Za-z0-9_.-]+|corp\.google\.com)")
_CONTRIB_NAME_RE = re.compile(r"^[a-z0-9][a-z0-9_-]*__[a-z0-9][a-z0-9_-]*\.json$")


def validate_entry(rec: Any, *, source_file: str = "<entry>") -> List[str]:
    """Validate one community-analysis entry and return a list of error strings."""
    errs: List[str] = []
    if not isinstance(rec, dict):
        return [f"{source_file}: entry must be a JSON object"]
    eid = rec.get("id")
    if not isinstance(eid, str) or not _ID_RE.match(eid):
        errs.append(f"{source_file}: invalid or missing id ({eid!r})")
    for field in ("project", "title", "author", "category", "url", "scope_summary", "caveat"):
        val = rec.get(field)
        if not isinstance(val, str) or not val.strip():
            errs.append(f"{source_file}[{eid}]: missing non-empty string field '{field}'")
            continue
        if _CTRL_RE.search(val) or _XSS_RE.search(val):
            errs.append(f"{source_file}[{eid}]: disallowed control/markup character in '{field}'")
        if _HOST_PATH_RE.search(val):
            errs.append(f"{source_file}[{eid}]: workstation path leaked in '{field}'")
    cat = rec.get("category")
    if isinstance(cat, str) and cat not in VALID_CATEGORIES:
        errs.append(f"{source_file}[{eid}]: unsupported category {cat!r}")
    url = rec.get("url")
    if isinstance(url, str) and not _HTTPS_URL_RE.match(url.strip()):
        errs.append(f"{source_file}[{eid}]: url must be a clean https:// URL")
    repo_url = rec.get("repo_url")
    if repo_url is not None and repo_url != "":
        if not isinstance(repo_url, str) or not _HTTPS_URL_RE.match(repo_url.strip()):
            errs.append(f"{source_file}[{eid}]: repo_url must be https://")
    dt = rec.get("updated")
    if not isinstance(dt, str) or not _DATE_RE.match(dt):
        errs.append(f"{source_file}[{eid}]: updated must be YYYY-MM-DD (got {dt!r})")
    if isinstance(rec.get("scope_summary"), str) and len(rec["scope_summary"]) > 600:
        errs.append(f"{source_file}[{eid}]: scope_summary exceeds 600 chars")
    if isinstance(rec.get("caveat"), str) and len(rec["caveat"]) > 400:
        errs.append(f"{source_file}[{eid}]: caveat exceeds 400 chars")
    lic = rec.get("license")
    if lic is not None and not isinstance(lic, str):
        errs.append(f"{source_file}[{eid}]: license must be a string")
    nums = rec.get("key_numbers")
    if nums is not None:
        if not isinstance(nums, list) or len(nums) > 12 or any(not isinstance(x, str) for x in nums):
            errs.append(f"{source_file}[{eid}]: key_numbers must be a list of <= 12 strings")
    anchors = rec.get("anchors")
    if anchors is not None:
        if not isinstance(anchors, list) or len(anchors) > 8:
            errs.append(f"{source_file}[{eid}]: anchors must be a list of <= 8 objects")
        else:
            for a in anchors:
                if not isinstance(a, dict) or not isinstance(a.get("label"), str) or not isinstance(a.get("route"), str):
                    errs.append(f"{source_file}[{eid}]: invalid anchor object {a!r}")
                elif not str(a.get("route", "")).startswith("#"):
                    errs.append(f"{source_file}[{eid}]: anchor route must start with '#' ({a.get('route')!r})")
    return errs


def load_community_dir(community_dir: str) -> Tuple[Dict[str, Any], List[str]]:
    """Load `sources.json` and `contrib/*.json` from `community_dir`, validating everything."""
    errs: List[str] = []
    entries: List[Dict[str, Any]] = []
    seen_ids: Dict[str, str] = {}
    as_of = ""
    disclaimer = (
        "Independent external links compiled for navigation and credit. Each entry reflects "
        "its own author and scope; a kernel check or link listing is not mathematical peer review. "
        "No external code or unlicensed prose is copied."
    )

    base = os.path.join(community_dir, "sources.json")
    if os.path.islink(base):
        errs.append(f"Refusing symlink: {base}")
    elif os.path.isfile(base):
        try:
            with open(base, "r", encoding="utf-8") as fh:
                doc = json.load(fh)
        except (OSError, json.JSONDecodeError) as exc:
            errs.append(f"sources.json: {exc}")
            doc = {}
        if isinstance(doc, dict):
            if doc.get("schema") not in (None, COMMUNITY_SCHEMA):
                errs.append(f"sources.json: unexpected schema {doc.get('schema')!r}")
            if isinstance(doc.get("as_of"), str) and _DATE_RE.match(doc["as_of"]):
                as_of = doc["as_of"]
            if isinstance(doc.get("disclaimer"), str) and doc["disclaimer"].strip():
                disclaimer = doc["disclaimer"].strip()
            raw_list = doc.get("entries", [])
            if not isinstance(raw_list, list):
                errs.append("sources.json: 'entries' must be a list")
            else:
                for rec in raw_list:
                    errs.extend(validate_entry(rec, source_file="sources.json"))
                    if isinstance(rec, dict) and isinstance(rec.get("id"), str):
                        if rec["id"] in seen_ids:
                            errs.append(f"duplicate id {rec['id']!r} (first in {seen_ids[rec['id']]})")
                        else:
                            seen_ids[rec["id"]] = "sources.json"
                            item = dict(rec)
                            item.setdefault("source_kind", "curated")
                            entries.append(item)

    contrib_dir = os.path.join(community_dir, "contrib")
    if os.path.isdir(contrib_dir) and not os.path.islink(contrib_dir):
        for fn in sorted(os.listdir(contrib_dir)):
            if not fn.endswith(".json"):
                continue
            fp = os.path.join(contrib_dir, fn)
            if os.path.islink(fp):
                errs.append(f"contrib/{fn}: refusing symlink")
                continue
            if not _CONTRIB_NAME_RE.match(fn):
                errs.append(f"contrib/{fn}: filename must match <author>__<slug>.json")
            try:
                with open(fp, "r", encoding="utf-8") as fh:
                    doc = json.load(fh)
            except (OSError, json.JSONDecodeError) as exc:
                errs.append(f"contrib/{fn}: {exc}")
                continue
            recs = doc.get("entries", [doc]) if isinstance(doc, dict) and "entries" in doc else (doc if isinstance(doc, list) else [doc])
            for rec in recs:
                errs.extend(validate_entry(rec, source_file=f"contrib/{fn}"))
                if isinstance(rec, dict) and isinstance(rec.get("id"), str):
                    if rec["id"] in seen_ids:
                        errs.append(f"contrib/{fn}: duplicate id {rec['id']!r}")
                    else:
                        seen_ids[rec["id"]] = f"contrib/{fn}"
                        item = dict(rec)
                        item["source_kind"] = "contrib"
                        item["contrib_file"] = f"notes/community/contrib/{fn}"
                        entries.append(item)

    if not as_of:
        dates = [str(e.get("updated", "")) for e in entries if _DATE_RE.match(str(e.get("updated", "")))]
        as_of = max(dates) if dates else datetime.date.today().isoformat()

    # Deterministic newest-first ordering inside priority buckets
    entries.sort(key=lambda e: (str(e.get("updated", "")), str(e.get("id", ""))), reverse=True)
    return {
        "schema": COMMUNITY_SCHEMA,
        "as_of": as_of,
        "disclaimer": disclaimer,
        "contrib_template_path": "notes/community/contrib/<author>__<slug>.json",
        "tool_repo_url": "https://github.com/bohemian-miser/leanre",
        "entries": entries,
    }, errs


def filter_for_project(bundle: Dict[str, Any], slug: str) -> Dict[str, Any]:
    """Return a bundle carrying all entries while recording direct-match count for `slug`."""
    all_entries = list(bundle.get("entries") or [])
    direct = [e for e in all_entries if e.get("project") == slug]
    out = dict(bundle)
    out["project"] = slug
    out["project_count"] = len(direct)
    out["total_count"] = len(all_entries)
    out["entries"] = all_entries
    return out


def _main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="Validate leanre community analysis registry.")
    ap.add_argument("--dir", default="notes/community", help="Path to community directory")
    args = ap.parse_args(list(argv) if argv is not None else None)
    bundle, errs = load_community_dir(args.dir)
    if errs:
        for e in errs:
            print(f"ERROR: {e}")
        return 1
    print(f"OK: {len(bundle['entries'])} valid community entries (as of {bundle['as_of']})")
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
