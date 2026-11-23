"""`leanre.decomp/v1` — shared JSON schema for outputs/decomp/{pillar_*,spine_map,tcb_audit}.json.

Posted on the swarm board (#61).  `validate()` is dependency-free; pass a KernelDB to also check
that every node id exists in kernel.db.
"""
from __future__ import annotations

import json
import re
from typing import Any, Optional

SCHEMA_ID = "leanre.decomp/v1"
PILLARS = {"theta", "galois", "volume", "volume_lit", "window", "tcb", "spine", "compute", "arch"}
KINDS = {"thm", "def", "opaque", "axiom", "induct", "inductive", "ctor", "rec", "quot"}
ROLES = {"theorem", "contract", "structure", "bridge", "lit_wrapper", "compute", "boilerplate", "glue"}
STATUS = {"READ", "PARTIAL", "OPAQUE"}
VERDICTS = {"real", "wrapper", "proxy", "degenerate", "vacuous", "boilerplate", "unknown"}
TAGS = {"L", "A", "C", "S", "M"}
RELS = {"dom", "type", "value", "both", "horn"}
_ANCHOR_RE = re.compile(r"^(?!/)[^\s:]+\.lean:\d+$")
MAX_TEXT_LINE = 600  # fair-use: single-line strings only

TEMPLATE: dict[str, Any] = {
    "schema": SCHEMA_ID,
    "pillar": "spine",
    "pins": {"rh_mirror": "40e56bab", "export_sha256": "5ea74b91…244e", "dom_tree": "ALL"},
    "root": "",
    "nodes": [],
    "edges": [],
    "horn": [],
    "claims": [],
    "opaque": [],
}


def _err(errs: list[str], path: str, msg: str) -> None:
    errs.append(f"{path}: {msg}")


def _check_text(errs: list[str], path: str, v: Any, max_len: int = MAX_TEXT_LINE) -> None:
    if v is None:
        return
    if not isinstance(v, str):
        _err(errs, path, "must be a string or null"); return
    if "\n" in v:
        _err(errs, path, "multi-line text is forbidden (license guardrail)")
    if len(v) > max_len and not path.endswith(".summary") and not path.endswith(".text"):
        _err(errs, path, f"longer than {max_len} chars")


def validate(doc: dict, kdb: Optional[Any] = None) -> list[str]:
    errs: list[str] = []
    if doc.get("schema") != SCHEMA_ID:
        _err(errs, "schema", f"must be {SCHEMA_ID!r}")
    if doc.get("pillar") not in PILLARS:
        _err(errs, "pillar", f"must be one of {sorted(PILLARS)}")
    if not isinstance(doc.get("pins"), dict):
        _err(errs, "pins", "missing")
    for key in ("nodes", "edges", "horn", "claims", "opaque"):
        if not isinstance(doc.get(key), list):
            _err(errs, key, "must be a list")
    if errs:
        return errs
    ids: set[str] = set()
    opaque_nodes: set[str] = set()
    for i, n in enumerate(doc["nodes"]):
        p = f"nodes[{i}]"
        if not isinstance(n, dict) or not isinstance(n.get("id"), str) or not n["id"]:
            _err(errs, p, "id required"); continue
        p = f"nodes[{n['id']}]"
        if n["id"] in ids:
            _err(errs, p, "duplicate id")
        ids.add(n["id"])
        if n.get("kind") is not None and n["kind"] not in KINDS:
            _err(errs, p + ".kind", f"bad kind {n['kind']!r}")
        if n.get("role") not in ROLES:
            _err(errs, p + ".role", f"bad role {n.get('role')!r}")
        if n.get("status") not in STATUS:
            _err(errs, p + ".status", f"bad status {n.get('status')!r}")
        if n.get("verdict") not in VERDICTS:
            _err(errs, p + ".verdict", f"bad verdict {n.get('verdict')!r}")
        if n.get("tag") not in TAGS:
            _err(errs, p + ".tag", f"bad tag {n.get('tag')!r}")
        a = n.get("anchor")
        if a is not None and not (isinstance(a, str) and _ANCHOR_RE.match(a)):
            _err(errs, p + ".anchor", "must look like src/<path>.lean:<line>")
        _check_text(errs, p + ".header", n.get("header"))
        _check_text(errs, p + ".summary", n.get("summary"), 4000)
        if n.get("status") == "OPAQUE":
            opaque_nodes.add(n["id"])
        dom = n.get("dom")
        if dom is not None and not (isinstance(dom, dict) and {"depth", "subtree"} <= set(dom)):
            _err(errs, p + ".dom", "must have depth & subtree")
        for j, f in enumerate(n.get("fields") or []):
            if not isinstance(f, dict) or "name" not in f:
                _err(errs, f"{p}.fields[{j}]", "needs name"); continue
            _check_text(errs, f"{p}.fields[{j}].type", f.get("type"))
    for i, e in enumerate(doc["edges"]):
        p = f"edges[{i}]"
        if not isinstance(e, dict) or not {"src", "dst", "rel"} <= set(e):
            _err(errs, p, "needs src,dst,rel"); continue
        if e["rel"] not in RELS:
            _err(errs, p + ".rel", f"bad rel {e['rel']!r}")
        if e.get("tag", "L") not in TAGS:
            _err(errs, p + ".tag", "bad tag")
    for i, h in enumerate(doc["horn"]):
        p = f"horn[{i}]"
        if not isinstance(h, dict) or not isinstance(h.get("hyps"), list) or "concl" not in h:
            _err(errs, p, "needs concl + hyps list"); continue
        if h.get("tag", "L") not in TAGS:
            _err(errs, p + ".tag", "bad tag")
    for i, c in enumerate(doc["claims"]):
        p = f"claims[{i}]"
        if not isinstance(c, dict) or not isinstance(c.get("text"), str):
            _err(errs, p, "needs text"); continue
        if c.get("tag") not in TAGS:
            _err(errs, p + ".tag", "bad tag")
        _check_text(errs, p + ".text", c["text"], 4000)
    missing = opaque_nodes - set(doc["opaque"])
    if missing:
        _err(errs, "opaque", f"OPAQUE nodes missing from opaque list: {sorted(missing)[:10]}")
    if kdb is not None:
        for nid in sorted(ids):
            if kdb.maybe(nid) is None:
                _err(errs, f"nodes[{nid}]", "id not found in kernel.db decls/consts")
    return errs


def validate_file(path: str, kdb: Optional[Any] = None) -> list[str]:
    with open(path, encoding="utf-8") as f:
        return validate(json.load(f), kdb)
