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
import os
import sys
from typing import Any, Optional

from .graph import Decompiler
from .kdb import (
    DEFAULT_KERNEL_DB,
    DEFAULT_SRC,
    Decl,
    KernelDB,
    ResolveError,
    resolve_leanre_db_path,
)
from .schema import validate_file
from .source import Contract, find_dead_in_src, one_line, preserve_truncate, read_contract

_FLAG_NAMES = (
    (1, "refl_true"),
    (2, "of_decide"),
    (4, "reduce_bool"),
    (8, "reduce_nat"),
    (16, "sorry"),
    (32, "trust_compiler"),
)


def _kdb(a: argparse.Namespace) -> KernelDB:
    ldb = resolve_leanre_db_path(a.kernel_db, a.leanre_db)
    return KernelDB(a.kernel_db, ldb, a.tree)


def _dec(a: argparse.Namespace) -> Decompiler:
    return Decompiler(_kdb(a), a.src_root)


def _dump(obj: Any) -> None:
    print(json.dumps(obj, ensure_ascii=False, indent=1))


def _print_resolve_err(err: ResolveError) -> None:
    print(f"error: {err}", file=sys.stderr)
    if err.hits:
        label = "Matching candidates:" if err.ambiguous else "Top candidate matches (sorted by ALL dom subtree size):"
        print(label, file=sys.stderr)
        for h in err.hits:
            print(
                f"  {h.decl.id}\t{h.decl.kind}\t{h.all_dom}\t{h.decl.name}\t{h.decl.module or h.decl.method}",
                file=sys.stderr,
            )
    elif not err.ambiguous:
        print("  (no fuzzy/suffix candidate matches found)", file=sys.stderr)


def _err_entry(err: ResolveError) -> dict:
    return {
        "query": err.query,
        "error": str(err),
        "ambiguous": err.ambiguous,
        "candidates": [
            {
                "id": h.decl.id,
                "name": h.decl.name,
                "kind": h.decl.kind,
                "dom_subtree": h.all_dom,
                "module": h.decl.module,
                "method": h.decl.method,
                "match": h.match,
            }
            for h in err.hits
        ],
    }


def _resolve_or_die(kdb: KernelDB, name: str, limit: int = 10) -> Optional[tuple[Decl, Optional[str]]]:
    try:
        return kdb.resolve_unique(name, limit=limit)
    except ResolveError as err:
        _print_resolve_err(err)
        return None


def _load_manifest_info(src_root: str) -> Optional[dict]:
    abs_src = os.path.abspath(src_root)
    for cand_dir in (abs_src, os.path.dirname(abs_src)):
        mf = os.path.join(cand_dir, "lake-manifest.json")
        if os.path.exists(mf):
            try:
                with open(mf, encoding="utf-8") as f:
                    data = json.load(f)
            except (OSError, json.JSONDecodeError):
                return None
            tc_path = os.path.join(cand_dir, "lean-toolchain")
            toolchain = None
            if os.path.exists(tc_path):
                try:
                    with open(tc_path, encoding="utf-8") as tf:
                        toolchain = tf.read().strip()
                except OSError:
                    pass
            return {"manifest_path": mf, "packages": data.get("packages") or [], "toolchain": toolchain}
    return None


def _match_package(decl_name: str, manifest: Optional[dict]) -> Optional[dict]:
    if not manifest:
        return None
    ns = decl_name.split(".", 1)[0]
    if ns in ("Lean", "Init", "Std") and manifest.get("toolchain"):
        return {"name": "lean4-core", "rev": manifest["toolchain"], "url": "https://github.com/leanprover/lean4"}
    pkgs = manifest.get("packages") or []
    for pkg in pkgs:
        pname = str(pkg.get("name") or "")
        if pname.lower() == ns.lower():
            return {"name": pname, "rev": pkg.get("rev"), "url": pkg.get("url")}
    for pkg in pkgs:
        if str(pkg.get("name") or "").lower() == "mathlib":
            return {"name": pkg["name"], "rev": pkg.get("rev"), "url": pkg.get("url"), "inferred": True}
    return None


def _decode_flags(flags: int) -> list[str]:
    return [label for bit, label in _FLAG_NAMES if flags & bit]


def _cmd_resolve(a) -> int:
    kdb = _kdb(a)
    results = []
    any_miss = False
    for query in a.queries:
        hits = kdb.resolve(query, limit=a.limit)
        cands = [
            {
                "id": h.decl.id,
                "name": h.decl.name,
                "kind": h.decl.kind,
                "dom_subtree": h.all_dom,
                "module": h.decl.module,
                "method": h.decl.method,
                "match": h.match,
            }
            for h in hits
        ]
        has_strong = any(h.match in ("exact", "suffix") for h in hits)
        if not has_strong:
            src_hits = kdb.find_source_decls(query, limit=a.limit)
            if not src_hits and kdb.l is None and not hits:
                dead_cs = find_dead_in_src(a.src_root, query, limit=a.limit)
                src_hits = [
                    {
                        "name": c.name,
                        "kind": c.keyword,
                        "module": c.file[:-5].replace("/", ".") if c.file.endswith(".lean") else None,
                        "line": c.line,
                        "snippet": c.header,
                        "file": c.file,
                    }
                    for c in dead_cs
                ]
            if src_hits:
                dead_cands = [
                    {
                        "id": None,
                        "name": s["name"],
                        "kind": s["kind"],
                        "dom_subtree": 0,
                        "module": s["module"],
                        "method": "dead_source_only",
                        "status": "dead_source_only",
                        "file": s["file"],
                        "line": s["line"],
                        "anchor": f"src/{s['file']}:{s['line']}",
                        "match": "dead_source_only",
                    }
                    for s in src_hits
                ]
                cands = (dead_cands + cands)[: a.limit]
        if not cands:
            any_miss = True
        results.append({
            "query": query,
            "exact": bool(hits and hits[0].match == "exact"),
            "candidates": cands,
        })

    if a.json:
        _dump(results[0] if len(results) == 1 else results)
    else:
        for idx, res in enumerate(results):
            if len(results) > 1:
                if idx > 0:
                    print()
                print(f"== {res['query']} ==")
            if not res["candidates"]:
                print(f"no matches for {res['query']!r}", file=sys.stderr)
            for c in res["candidates"]:
                cid = c["id"] if c["id"] is not None else "-"
                loc = c.get("anchor") or c["module"] or c["method"]
                print(f"{cid}\t{c['kind']}\t{c['dom_subtree']}\t{c['name']}\t{loc}\t[{c['match']}]")
    return 0 if (not any_miss or getattr(a, "continue_on_error", False)) else 1


def _print_contract_body(body: str, max_len: int, preserve_lines: bool) -> None:
    if not preserve_lines:
        print(f"  := {one_line(body, max_len)}")
        return
    txt = preserve_truncate(body, max_len) or ""
    lines = txt.split("\n")
    if len(lines) <= 1:
        print(f"  := {txt}")
        return
    print(f"  := {lines[0]}")
    for ln in lines[1:]:
        print(f"    {ln}" if ln else "")


def _find_dead_contracts(
    kdb: KernelDB,
    src_root: str,
    query: str,
    *,
    include_thm: bool,
    preserve_lines: bool,
) -> list[tuple[Contract, str, Optional[str]]]:
    """Fallback lookup for dead declarations absent from `kernel.db`."""
    rows = kdb.find_source_decls(query)
    if rows:
        out: list[tuple[Contract, str, Optional[str]]] = []
        for r in rows:
            c = read_contract(
                src_root,
                r["file"],
                r["name"],
                hint=r["line"],
                include_thm=include_thm,
                preserve_lines=preserve_lines,
            )
            if c is None:
                c = Contract(
                    name=r["name"],
                    keyword=r["kind"],
                    file=r["file"],
                    line=r["line"],
                    header=r["snippet"] or r["name"],
                )
            out.append((c, r["kind"], r["module"]))
        return out
    if kdb.l is None:
        cs = find_dead_in_src(src_root, query, include_thm=include_thm, preserve_lines=preserve_lines)
        return [
            (
                c,
                c.keyword,
                c.file[:-5].replace("/", ".") if c.file.endswith(".lean") else None,
            )
            for c in cs
        ]
    return []


def _print_missing_summary(missing: list[str], errors: list[dict]) -> None:
    if not errors:
        return
    print()
    print(f"missing ({len(missing)}): {', '.join(missing)}")
    for e in errors:
        print(f"  error [{e['query']}]: {e['error']}")


def _cmd_contract(a) -> int:
    D = _dec(a)
    entries: list[tuple[str, Any]] = []  # ("live", (Decl, resolved_from)) | ("dead", (query, matches))
    missing: list[str] = []
    errors: list[dict] = []

    for nm in a.names:
        try:
            d, resolved_from = D.kdb.resolve_unique(nm)
            entries.append(("live", (d, resolved_from)))
        except ResolveError as err:
            dead_matches = [] if err.ambiguous else _find_dead_contracts(
                D.kdb,
                a.src_root,
                nm,
                include_thm=a.include_thm,
                preserve_lines=a.preserve_lines,
            )
            if dead_matches:
                entries.append(("dead", (nm, dead_matches)))
                continue
            if not a.continue_on_error:
                _print_resolve_err(err)
                return 1
            _print_resolve_err(err)
            missing.append(nm)
            errors.append(_err_entry(err))

    manifest: Optional[dict] = None
    manifest_loaded = False

    def get_manifest() -> Optional[dict]:
        nonlocal manifest, manifest_loaded
        if not manifest_loaded:
            manifest = _load_manifest_info(a.src_root)
            manifest_loaded = True
        return manifest

    if a.table:
        rows = []
        for kind_tag, payload in entries:
            if kind_tag == "live":
                d, resolved_from = payload
                c = D.contract(d, include_thm=a.include_thm, preserve_lines=a.preserve_lines)
                st = D.kdb.decl_stats(d)
                row = {
                    "id": d.id,
                    "name": d.name,
                    "kind": d.kind,
                    "dom_subtree": st["all_dom_subtree"],
                    "fan_in": st["fan_in"],
                    "module": d.module,
                    "method": d.method,
                    "anchor": c.anchor if c else None,
                    "header": one_line(c.header, a.max_len) if c else None,
                }
                if resolved_from is not None:
                    row["resolved_from"] = resolved_from
                rows.append(row)
            else:
                _nm, matches = payload
                c, dkind, dmod = matches[0]
                rows.append({
                    "id": None,
                    "name": c.name,
                    "kind": dkind,
                    "status": "dead_source_only",
                    "dom_subtree": None,
                    "fan_in": None,
                    "module": dmod,
                    "method": "dead_source_only",
                    "file": c.file,
                    "line": c.line,
                    "anchor": c.anchor,
                    "header": one_line(c.header, a.max_len),
                })
        if a.json:
            _dump({"results": rows, "missing": missing, "errors": errors} if errors else rows)
        else:
            print("id\tkind\tdom\tfan_in\tmodule\tanchor\theader")
            for r in rows:
                rid = r["id"] if r["id"] is not None else "-"
                dom_s = r["dom_subtree"] if r["dom_subtree"] is not None else "-"
                fi_s = r["fan_in"] if r["fan_in"] is not None else "-"
                hdr = r["header"] or "-"
                if r.get("status") == "dead_source_only":
                    hdr = f"[dead_source_only] {hdr}"
                print(
                    f"{rid}\t{r['kind']}\t{dom_s}\t{fi_s}\t"
                    f"{r['module'] or r['method']}\t{r['anchor'] or '-'}\t{hdr}"
                )
            _print_missing_summary(missing, errors)
        return 0

    json_items = []
    for idx, (kind_tag, payload) in enumerate(entries):
        if kind_tag == "dead":
            nm, matches = payload
            c, dkind, dmod = matches[0]
            others = matches[1:]
            with_body = a.body and (a.include_thm or dkind not in ("thm", "theorem", "lemma"))
            if a.json:
                item: dict[str, Any] = {
                    "status": "dead_source_only",
                    "query": nm,
                    "decl": {
                        "id": None,
                        "name": c.name,
                        "kind": dkind,
                        "module": dmod,
                        "method": "dead_source_only",
                    },
                    "file": c.file,
                    "line": c.line,
                    "anchor": c.anchor,
                    "header": one_line(c.header, a.max_len),
                    "contract": c.to_json(a.max_len, with_body=with_body, preserve_lines=a.preserve_lines),
                }
                if others:
                    item["other_matches"] = [
                        {
                            "name": oc.name,
                            "kind": okind,
                            "module": omod,
                            "file": oc.file,
                            "line": oc.line,
                            "anchor": oc.anchor,
                            "header": one_line(oc.header, a.max_len),
                        }
                        for oc, okind, omod in others
                    ]
                json_items.append(item)
                continue

            if idx > 0:
                print()
            print(f"{c.name}  [{dkind}] status=dead_source_only module={dmod} (absent from kernel.db)")
            print(f"  anchor   : {c.anchor}")
            print(f"  file     : {c.file}")
            print(f"  line     : {c.line}")
            if c.namespace:
                print(f"  namespace: {c.namespace}")
            for v in c.variables:
                print(f"  variable : {v}")
            print(f"  header   : {one_line(c.header, a.max_len)}")
            if c.extends:
                print(f"  extends  : {', '.join(c.extends)}")
            for f in c.fields:
                print(f"    .{f.name} : {' '.join(f.type.split())}")
            if with_body and c.body is not None:
                _print_contract_body(c.body, a.max_len, a.preserve_lines)
            for oc, okind, _omod in others:
                print(f"  other    : {oc.name} [{okind}] ({oc.anchor})")
            continue

        d, resolved_from = payload
        c = D.contract(d, include_thm=a.include_thm, preserve_lines=a.preserve_lines)
        with_body = a.body and (a.include_thm or d.kind != "thm")
        need_stats = c is None or d.ground
        st = D.kdb.decl_stats(d) if need_stats else None
        pkg = _match_package(d.name, get_manifest()) if d.ground else None

        if a.json:
            item = {
                "decl": {"id": d.id, "name": d.name, "kind": d.kind, "module": d.module, "method": d.method},
                "contract": c.to_json(a.max_len, with_body=with_body, preserve_lines=a.preserve_lines) if c else None,
            }
            if resolved_from is not None:
                item["resolved_from"] = resolved_from
            if st is not None:
                item["kernel"] = {
                    "kind": st["kind"],
                    "live_mask": st["live_mask"],
                    "fan_in": st["fan_in"],
                    "fan_out": st["fan_out"],
                    "type_nodes": st["type_nodes"],
                    "value_nodes": st["value_nodes"],
                    "flags": st["flags"],
                    "flag_names": _decode_flags(st["flags"]),
                    "method": st["method"],
                    "all_dom_subtree": st["all_dom_subtree"],
                }
            if pkg is not None:
                item["package"] = pkg
            json_items.append(item)
            continue

        if idx > 0:
            print()
        print(f"{d.name}  [{d.kind}] id={d.id} module={d.module} ({d.method})")
        if c is None:
            print("  (no source contract: ground Mathlib/Lean decl)" if d.ground else "  OPAQUE: source not located")
            if st is not None:
                flag_str = f"{st['flags']}"
                fnames = _decode_flags(st["flags"])
                if fnames:
                    flag_str += f" ({','.join(fnames)})"
                print(
                    f"  kernel   : kind={st['kind']} live_mask={st['live_mask']} "
                    f"fan_in={st['fan_in']} fan_out={st['fan_out']} "
                    f"type_nodes={st['type_nodes']} value_nodes={st['value_nodes']} "
                    f"flags={flag_str} method={st['method']}"
                )
            if pkg is not None:
                rev = pkg.get("rev") or "-"
                url = pkg.get("url") or ""
                extra = f" ({url})" if url else ""
                print(f"  package  : {pkg['name']} rev={rev}{extra}")
            continue
        print(f"  anchor   : {c.anchor}")
        if c.namespace:
            print(f"  namespace: {c.namespace}")
        for v in c.variables:
            print(f"  variable : {v}")
        print(f"  header   : {one_line(c.header, a.max_len)}")
        if c.extends:
            print(f"  extends  : {', '.join(c.extends)}")
        for f in c.fields:
            print(f"    .{f.name} : {' '.join(f.type.split())}")
        if with_body and c.body is not None:
            _print_contract_body(c.body, a.max_len, a.preserve_lines)

    if a.json:
        if errors:
            _dump({"results": json_items, "missing": missing, "errors": errors})
        else:
            _dump(json_items[0] if len(json_items) == 1 else json_items)
    else:
        _print_missing_summary(missing, errors)
    return 0


def _print_unfold(u: dict, ind: int = 0) -> None:
    pad = "  " * ind
    tag = "GROUND" if u.get("ground") else ("REF" if u.get("ref") else ("…" if u.get("unexpanded") else u.get("kind", "")))
    stop_tag = " [STOPPED]" if u.get("stopped") else ""
    print(f"{pad}- {u['id']} [{tag}]{stop_tag}{' via ' + u['edge'] if u.get('edge') else ''}  {u.get('anchor') or ''}")
    if u.get("header"):
        print(f"{pad}    {u['header']}")
    for f in u.get("fields", []):
        print(f"{pad}    .{f['name']} : {f['type']}")
    if u.get("fields_truncated"):
        print(f"{pad}    ... (+{u['fields_truncated']} more fields)")
    elif u.get("stopped") and u.get("fields_count"):
        print(f"{pad}    ... ({u['fields_count']} fields omitted at stop boundary)")
    if u.get("body"):
        print(f"{pad}    := {u['body']}")
    if u.get("opaque"):
        print(f"{pad}    OPAQUE ({u['opaque']})")
    if u.get("ground_deps"):
        print(f"{pad}    ground: {', '.join(u['ground_deps'])}")
    for k in u.get("deps", []):
        _print_unfold(k, ind + 1)


def _resolve_single_cmd(D: Decompiler, name: str, continue_on_error: bool) -> tuple[Optional[Decl], Optional[str], Optional[ResolveError]]:
    try:
        d, resolved_from = D.kdb.resolve_unique(name)
        return d, resolved_from, None
    except ResolveError as err:
        _print_resolve_err(err)
        if not continue_on_error:
            return None, None, err
        return None, None, err


def _cmd_unfold(a) -> int:
    D = _dec(a)
    d, resolved_from, err = _resolve_single_cmd(D, a.name, a.continue_on_error)
    if d is None:
        assert err is not None
        if not a.continue_on_error:
            return 1
        if a.json:
            _dump({"results": [], "missing": [a.name], "errors": [_err_entry(err)]})
        else:
            _print_missing_summary([a.name], [_err_entry(err)])
        return 0
    u = D.unfold(
        d,
        a.depth,
        with_body=not a.no_body,
        max_len=a.max_len,
        full_fields=a.full_fields,
        stop_at=a.stop_at,
        max_fields=a.max_fields,
    )
    if resolved_from is not None:
        u["resolved_from"] = resolved_from
    _dump(u) if a.json else _print_unfold(u)
    return 0


def _cmd_horn(a) -> int:
    D = _dec(a)
    d, resolved_from, err = _resolve_single_cmd(D, a.name, a.continue_on_error)
    if d is None:
        assert err is not None
        if not a.continue_on_error:
            return 1
        _dump({"results": [], "missing": [a.name], "errors": [_err_entry(err)]})
        return 0
    if a.graph:
        _dump(D.horn_graph(d, a.max))
    else:
        h = D.horn(d)
        if resolved_from is not None:
            h["resolved_from"] = resolved_from
        _dump(h)
    return 0


def _cmd_dom(a) -> int:
    D = _dec(a)
    if len(a.names) == 1 and a.names[0] in ("ROOT", "-"):
        kids = D.kdb.dom_children(None, a.limit, a.min_size)
        _dump([{"id": D.kdb.decl(k.decl_id).name, "subtree": k.subtree_size} for k in kids])
        return 0
    results = []
    missing: list[str] = []
    errors: list[dict] = []
    for nm in a.names:
        if nm in ("ROOT", "-"):
            kids = D.kdb.dom_children(None, a.limit, a.min_size)
            results.append({"id": "ROOT", "children": [{"id": D.kdb.decl(k.decl_id).name, "subtree": k.subtree_size} for k in kids]})
            continue
        try:
            d, resolved_from = D.kdb.resolve_unique(nm)
        except ResolveError as err:
            _print_resolve_err(err)
            if not a.continue_on_error:
                return 1
            missing.append(nm)
            errors.append(_err_entry(err))
            continue
        sp = D.dom_spine(d, a.depth, a.min_size, a.limit, with_cone=a.with_cone)
        if resolved_from is not None:
            sp["resolved_from"] = resolved_from
        results.append(sp)
    if errors:
        _dump({"results": results, "missing": missing, "errors": errors})
    else:
        _dump(results[0] if len(results) == 1 else results)
    return 0


def _cmd_path(a) -> int:
    D = _dec(a)
    s, s_from, s_err = _resolve_single_cmd(D, a.src, a.continue_on_error)
    t, t_from, t_err = (None, None, None)
    if a.dst is not None and (s is not None or a.continue_on_error):
        t, t_from, t_err = _resolve_single_cmd(D, a.dst, a.continue_on_error)
    if s is None or (a.dst is not None and t is None):
        if not a.continue_on_error:
            return 1
        missing: list[str] = []
        errors: list[dict] = []
        if s_err is not None:
            missing.append(a.src)
            errors.append(_err_entry(s_err))
        if t_err is not None:
            missing.append(a.dst)
            errors.append(_err_entry(t_err))
        _dump({
            "from": s.name if s is not None else a.src,
            "to": (t.name if t is not None else a.dst),
            "kind": a.kind,
            "project_only": a.project_only,
            "found": False,
            "length": None,
            "path": [],
            "missing": missing,
            "errors": errors,
        })
        return 0
    assert s is not None
    if a.dst is None:
        chain = D.kdb.dom_path(s)
        _dump([{"id": D.kdb.decl(n.decl_id).name, "depth": n.depth, "subtree": n.subtree_size} for n in chain])
        return 0
    assert t is not None
    p = D.shortest_path(s, t, project_only=a.project_only, kind=a.kind)
    out = {
        "from": s.name,
        "to": t.name,
        "kind": a.kind,
        "project_only": a.project_only,
        "found": p is not None,
        "length": (len(p) - 1) if p is not None else None,
        "path": p or [],
    }
    if s_from is not None or t_from is not None:
        rf = {}
        if s_from is not None:
            rf["from"] = s_from
        if t_from is not None:
            rf["to"] = t_from
        out["resolved_from"] = rf
    _dump(out)
    return 0


def _cmd_node(a) -> int:
    D = _dec(a)
    d, resolved_from, err = _resolve_single_cmd(D, a.name, a.continue_on_error)
    if d is None:
        assert err is not None
        if not a.continue_on_error:
            return 1
        _dump({"results": [], "missing": [a.name], "errors": [_err_entry(err)]})
        return 0
    nd = D.node(d, with_body=False)
    if resolved_from is not None:
        nd["resolved_from"] = resolved_from
    _dump(nd)
    return 0


def _cmd_search(a) -> int:
    D = _dec(a)
    try:
        rows = D.kdb.search_rows(
            a.pattern,
            a.limit,
            project_only=a.project_only,
            no_aux=a.no_aux,
            case_sensitive=a.case_sensitive,
            kind=a.kind,
            module_regex=a.module,
            sort_by=a.sort_by,
            regex=a.regex,
            search_module=a.search_module,
        )
    except ValueError as err:
        print(f"error: {err}", file=sys.stderr)
        return 2
    if a.json:
        _dump([
            {
                "id": d.id,
                "kind": d.kind,
                "dom_subtree": dom_sz,
                "fan_in": fi,
                "value_nodes": vn,
                "name": d.name,
                "module": d.module,
                "method": d.method,
            }
            for d, dom_sz, fi, vn in rows
        ])
        return 0
    for d, dom_sz, fi, vn in rows:
        extra = ""
        if a.sort_by == "fan_in":
            extra = f"\tfan_in={fi}"
        elif a.sort_by == "vn":
            extra = f"\tvn={vn}"
        print(f"{d.id}\t{d.kind}\t{dom_sz if dom_sz is not None else '-'}\t{d.name}\t{d.module or d.method}{extra}")
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
    p.add_argument(
        "--leanre-db",
        "--source-db",
        dest="leanre_db",
        default=None,
        help="Path to outputs/leanre.db (auto-detected beside --kernel-db if omitted)",
    )
    p.add_argument("--src", "--src-root", dest="src_root", default=DEFAULT_SRC, help="data/rh_mirror/src")
    p.add_argument("--tree", default="ALL", help="dom_trees.label (ALL, ROOT:<name>, STMT_ALL)")


def build_parser(p: argparse.ArgumentParser, dest: str = "decompile_func") -> argparse.ArgumentParser:
    sp = p.add_subparsers(dest="decompile_cmd", required=True)

    def add(name: str, fn, help_: str) -> argparse.ArgumentParser:
        q = sp.add_parser(name, help=help_)
        _common(q)
        q.set_defaults(**{dest: fn})
        return q

    q = add("resolve", _cmd_resolve, "Resolve exact, module-qualified, suffix, or fuzzy decl names")
    q.add_argument("queries", nargs="+", metavar="query")
    q.add_argument("--limit", type=int, default=10)
    q.add_argument("--json", action="store_true")
    q.add_argument("--continue-on-error", action="store_true")

    q = add("contract", _cmd_contract, "Exact header / fields / body of one or more declarations")
    q.add_argument("names", nargs="+", metavar="decl")
    q.add_argument("--body", action="store_true")
    q.add_argument("--include-thm", action="store_true")
    q.add_argument("--preserve-lines", action="store_true", help="Keep newlines/indentation in --body output")
    q.add_argument("--continue-on-error", action="store_true", help="Report missing/ambiguous decls without aborting batch")
    q.add_argument("--table", action="store_true")
    q.add_argument("--json", action="store_true")
    q.add_argument("--max-len", type=int, default=2000)

    q = add("unfold", _cmd_unfold, "Recursive contract unfolding to Mathlib/Lean ground types")
    q.add_argument("name")
    q.add_argument("--depth", type=int, default=2)
    q.add_argument("--json", action="store_true")
    q.add_argument("--no-body", action="store_true")
    q.add_argument("--max-len", type=int, default=400)
    q.add_argument("--full-fields", action="store_true")
    q.add_argument("--stop-at", action="append", default=[])
    q.add_argument("--max-fields", type=int, default=None)
    q.add_argument("--continue-on-error", action="store_true")

    q = add("horn", _cmd_horn, "Declaration-level Horn clause (hyps ∧ lemmas → concl) or BFS Horn graph")
    q.add_argument("name")
    q.add_argument("--graph", action="store_true")
    q.add_argument("--max", type=int, default=100)
    q.add_argument("--continue-on-error", action="store_true")

    q = add("dom", _cmd_dom, "Dominator spine below one or more decls (name or ROOT)")
    q.add_argument("names", nargs="+", metavar="decl")
    q.add_argument("--depth", type=int, default=1)
    q.add_argument("--min-size", "--min-subtree", type=int, default=500, dest="min_size")
    q.add_argument("--limit", type=int, default=60)
    q.add_argument("--with-cone", action="store_true")
    q.add_argument("--continue-on-error", action="store_true")

    q = add("path", _cmd_path, "idom chain to root (1 arg) or shortest directed edge BFS path (2 args)")
    q.add_argument("src", metavar="from_decl")
    q.add_argument("dst", nargs="?", default=None, metavar="to_decl")
    q.add_argument("--project-only", action="store_true")
    q.add_argument("--kind", choices=("type", "value", "both"), default="both")
    q.add_argument("--continue-on-error", action="store_true")

    q = add("node", _cmd_node, "leanre.decomp/v1 node skeleton for a decl")
    q.add_argument("name")
    q.add_argument("--continue-on-error", action="store_true")

    q = add("search", _cmd_search, "Search kernel decl names with project/kind/aux/module filters")
    q.add_argument("pattern")
    q.add_argument("--limit", type=int, default=50)
    q.add_argument("--project-only", action="store_true")
    q.add_argument("--no-aux", action="store_true", help="Exclude compiler/tactic auxiliary decls")
    q.add_argument("--include-aux", action="store_false", dest="no_aux", default=argparse.SUPPRESS,
                   help="Include auxiliary decls (overrides --no-aux)")
    q.add_argument("--case-sensitive", action="store_true")
    q.add_argument("--kind", default=None)
    q.add_argument("--module", default=None, help="Regex filter on decl_module.module")
    q.add_argument("--regex", action="store_true", help="Treat pattern as Python regex (supports | alternation)")
    q.add_argument("--search-module", action="store_true", help="Match pattern across both module and decl.name")
    q.add_argument("--sort-by", choices=("name", "dom", "fan_in", "vn"), default="name")
    q.add_argument("--json", action="store_true")
    q.set_defaults(no_aux=False)

    q = add("validate", _cmd_validate, "Validate outputs/decomp/*.json against leanre.decomp/v1")
    q.add_argument("files", nargs="+")
    q.add_argument("--no-db", action="store_true")
    q = add("spine-map", _cmd_spine_map, "Regenerate outputs/decomp/spine_map.json")
    q.add_argument("--out", default="outputs/decomp/spine_map.json")
    q.add_argument("--top", type=int, default=60)
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
