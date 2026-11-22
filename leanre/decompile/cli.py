"""`leanre decompile` CLI.  Wire into leanre/leanre.py with:

    import decompile.cli as decompile_cli      # (leanre/ is on sys.path there)
    decompile_cli.register_cli(sub)
    ...
    if args.cmd == "decompile": return int(args.decompile_func(args))

or run standalone:  python3 -m decompile <cmd> ...   (from inside leanre/)
                    python3 leanre/decompile <cmd> ...
"""
from __future__ import annotations

import argparse
import json
import sys
from typing import Any, Optional

from .graph import Decompiler
from .kdb import DEFAULT_KERNEL_DB, DEFAULT_LEANRE_DB, DEFAULT_SRC, KernelDB
from .schema import validate_file


def _dec(a: argparse.Namespace) -> Decompiler:
    return Decompiler(KernelDB(a.kernel_db, a.leanre_db, a.tree), a.src)


def _dump(obj: Any) -> None:
    print(json.dumps(obj, ensure_ascii=False, indent=1))


def _cmd_contract(a) -> int:
    D = _dec(a)
    d = D.kdb.decl(a.name)
    c = D.contract(d)
    if a.json:
        _dump({"decl": {"id": d.id, "name": d.name, "kind": d.kind, "module": d.module, "method": d.method},
               "contract": c.to_json(a.max_len, with_body=a.body and d.kind != "thm") if c else None})
        return 0
    print(f"{d.name}  [{d.kind}] id={d.id} module={d.module} ({d.method})")
    if c is None:
        print("  (no source contract: ground Mathlib/Lean decl)" if d.ground else "  OPAQUE: source not located")
        return 0
    print(f"  anchor   : {c.anchor}")
    if c.namespace:
        print(f"  namespace: {c.namespace}")
    for v in c.variables:
        print(f"  variable : {v}")
    print(f"  header   : {c.header}")
    if c.extends:
        print(f"  extends  : {', '.join(c.extends)}")
    for f in c.fields:
        print(f"    .{f.name} : {' '.join(f.type.split())}")
    if a.body and c.body is not None and d.kind != "thm":
        print(f"  := {c.body[:a.max_len]}")
    return 0


def _print_unfold(u: dict, ind: int = 0) -> None:
    pad = "  " * ind
    tag = "GROUND" if u.get("ground") else ("REF" if u.get("ref") else ("…" if u.get("unexpanded") else u.get("kind", "")))
    print(f"{pad}- {u['id']} [{tag}]{' via ' + u['edge'] if u.get('edge') else ''}  {u.get('anchor') or ''}")
    if u.get("header"):
        print(f"{pad}    {u['header']}")
    for f in u.get("fields", []):
        print(f"{pad}    .{f['name']} : {f['type']}")
    if u.get("body"):
        print(f"{pad}    := {u['body']}")
    if u.get("opaque"):
        print(f"{pad}    OPAQUE ({u['opaque']})")
    if u.get("ground_deps"):
        print(f"{pad}    ground: {', '.join(u['ground_deps'])}")
    for k in u.get("deps", []):
        _print_unfold(k, ind + 1)


def _cmd_unfold(a) -> int:
    u = _dec(a).unfold(a.name, a.depth, with_body=not a.no_body)
    _dump(u) if a.json else _print_unfold(u)
    return 0


def _cmd_horn(a) -> int:
    D = _dec(a)
    if a.graph:
        _dump(D.horn_graph(a.name, a.max))
    else:
        _dump(D.horn(a.name))
    return 0


def _cmd_dom(a) -> int:
    D = _dec(a)
    if a.name in ("ROOT", "-"):
        kids = D.kdb.dom_children(None, a.limit, a.min_size)
        _dump([{"id": D.kdb.decl(k.decl_id).name, "subtree": k.subtree_size} for k in kids])
        return 0
    _dump(D.dom_spine(a.name, a.depth, a.min_size, a.limit))
    return 0


def _cmd_path(a) -> int:
    D = _dec(a)
    chain = D.kdb.dom_path(a.name)
    _dump([{"id": D.kdb.decl(n.decl_id).name, "depth": n.depth, "subtree": n.subtree_size} for n in chain])
    return 0


def _cmd_node(a) -> int:
    _dump(_dec(a).node(a.name, with_body=False))
    return 0


def _cmd_search(a) -> int:
    D = _dec(a)
    for d in D.kdb.search(a.pattern, a.limit):
        dn = D.kdb.dom(d)
        print(f"{d.id}\t{d.kind}\t{dn.subtree_size if dn else '-'}\t{d.name}\t{d.module or d.method}")
    return 0


def _cmd_validate(a) -> int:
    kdb = None if a.no_db else KernelDB(a.kernel_db, None, a.tree)
    bad = 0
    for p in a.files:
        errs = validate_file(p, kdb)
        print(f"{p}: {'OK' if not errs else f'{len(errs)} error(s)'}")
        for e in errs[:50]:
            print(f"  - {e}")
        bad += bool(errs)
    return 1 if bad else 0


def _cmd_spine_map(a) -> int:
    from .spine import build_spine_map
    doc = build_spine_map(_dec(a), top=a.top, log=sys.stderr)
    with open(a.out, "w", encoding="utf-8") as f:
        json.dump(doc, f, ensure_ascii=False, indent=1)
        f.write("\n")
    print(f"wrote {a.out}: {len(doc['nodes'])} nodes, {len(doc['edges'])} edges", file=sys.stderr)
    return 0


def _common(p: argparse.ArgumentParser) -> None:
    p.add_argument("--kernel-db", default=DEFAULT_KERNEL_DB)
    p.add_argument("--leanre-db", default=DEFAULT_LEANRE_DB)
    p.add_argument("--src", default=DEFAULT_SRC, help="data/rh_mirror/src")
    p.add_argument("--tree", default="ALL", help="dom_trees.label (ALL, ROOT:<name>, STMT_ALL)")


def build_parser(p: argparse.ArgumentParser, dest: str = "decompile_func") -> argparse.ArgumentParser:
    sp = p.add_subparsers(dest="decompile_cmd", required=True)

    def add(name: str, fn, help_: str) -> argparse.ArgumentParser:
        q = sp.add_parser(name, help=help_)
        _common(q)
        q.set_defaults(**{dest: fn})
        return q

    q = add("contract", _cmd_contract, "Exact header / fields / (def-only) body of one declaration")
    q.add_argument("name"); q.add_argument("--body", action="store_true"); q.add_argument("--json", action="store_true")
    q.add_argument("--max-len", type=int, default=2000)
    q = add("unfold", _cmd_unfold, "Recursive contract unfolding to Mathlib/Lean ground types")
    q.add_argument("name"); q.add_argument("--depth", type=int, default=2)
    q.add_argument("--json", action="store_true"); q.add_argument("--no-body", action="store_true")
    q = add("horn", _cmd_horn, "Declaration-level Horn clause (hyps ∧ lemmas → concl) or BFS Horn graph")
    q.add_argument("name"); q.add_argument("--graph", action="store_true"); q.add_argument("--max", type=int, default=100)
    q = add("dom", _cmd_dom, "Dominator spine below a decl (name or ROOT)")
    q.add_argument("name"); q.add_argument("--depth", type=int, default=1)
    q.add_argument("--min-size", type=int, default=500); q.add_argument("--limit", type=int, default=60)
    q = add("path", _cmd_path, "idom chain from a decl up to the virtual root")
    q.add_argument("name")
    q = add("node", _cmd_node, "leanre.decomp/v1 node skeleton for a decl")
    q.add_argument("name")
    q = add("search", _cmd_search, "LIKE search over kernel decl names")
    q.add_argument("pattern"); q.add_argument("--limit", type=int, default=50)
    q = add("validate", _cmd_validate, "Validate outputs/decomp/*.json against leanre.decomp/v1")
    q.add_argument("files", nargs="+"); q.add_argument("--no-db", action="store_true")
    q = add("spine-map", _cmd_spine_map, "Regenerate outputs/decomp/spine_map.json")
    q.add_argument("--out", default="outputs/decomp/spine_map.json"); q.add_argument("--top", type=int, default=60)
    return p


def register_cli(sub: Any, dest: str = "decompile_func") -> argparse.ArgumentParser:
    """Attach `decompile` to a leanre argparse subparsers object."""
    p = sub.add_parser("decompile", help="Proof decompiler: contracts, unfolding, Horn graph, dominator spine")
    return build_parser(p, dest)


def main(argv: Optional[list[str]] = None) -> int:
    ap = argparse.ArgumentParser(prog="leanre decompile")
    build_parser(ap)
    a = ap.parse_args(argv)
    return int(a.decompile_func(a))
