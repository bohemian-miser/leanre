"""Reverse-lookup of structure field readers and `∧`-conjunct readers (`leanre decompile readers`).

Uses `kernel.db` incoming edges (`edges_dst`) to restrict candidate declarations to the exact
set of project declarations referencing `<Target>` (or its field projection / wrapper `∧`-defs)
before inspecting `.lean` contracts, achieving `< 1s` latency on `1.47M`-decl graphs.
"""
from __future__ import annotations

import re
from typing import Any, Optional, Sequence

from .kdb import BOTH, TYPE, VALUE, Decl
from .source import (
    Contract,
    Field,
    _IDENT_RE,
    _LEAN_STOPWORDS,
    _OPEN,
    _CLOSE,
    _arrow_split_depth0,
    _depth0_find,
    _depth0_find_assign,
    _depth0_split,
    _group_tactic_blocks,
    _head_ident,
    _matches_target_ident,
    _parse_binder_names,
    _split_top_binop,
    _strip_outer_parens,
    classify_codomain_producer,
    identifiers,
    one_line,
)

_PROJ_CHAIN_RE = re.compile(
    r"(?:\)|[A-Za-z_\u0370-\u03ff\u1d00-\u1dbf\u2100-\u214f𝒜-𝔷][\w'.!?\u0370-\u03ff₀-₉ᵢ-ᵪ\u2100-\u214f𝒜-𝔷]*)"
    r"((?:\.(?:1|2|left|right|fst|snd))+)\b"
)
_DESTRUCT_STMT_RE = re.compile(
    r"^(?:obtain|rcases|have|let)\s+(⟨.+⟩)\s*(?::=|with)\s*(.+)$"
)
_HAVE_ASSIGN_RE = re.compile(r"^(?:have|let)\s+([A-Za-z_][\w']*)\s*(?::\s*([^:=]+?))?\s*:=\s*(.+)$")


def _count_exists_binders(blob: str) -> int:
    """Count existential witness variables in `∃ x y : T, ...` or `∃ (x y : T) (z : U), ...`."""
    s = blob.strip()
    if not s:
        return 0
    j0 = _depth0_find(s, ":")
    if j0 >= 0 and not s.startswith(("(", "{", "[", "⦃")):
        names = [t for t in s[:j0].split() if t]
        return max(1, len(names))
    if not any(ch in s for ch in "([{⦃"):
        names = [t for t in s.split() if t]
        return max(1, len(names))
    total = 0
    depth = 0
    start: Optional[int] = None
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c in "([{⦃":
            if depth == 0:
                start = i
            depth += 1
        elif c in ")]}⦄":
            depth = max(0, depth - 1)
            if depth == 0 and start is not None:
                br_open = s[start]
                inner = s[start + 1:i].strip()
                if br_open == "(":
                    k = _depth0_find(inner, ":")
                    lhs = inner[:k].strip() if k >= 0 else inner
                    cnt = len([t for t in lhs.split() if t])
                    total += max(1, cnt)
                start = None
        elif depth == 0 and not c.isspace():
            m = _IDENT_RE.match(s[i:])
            if m:
                total += 1
                i += len(m.group(0))
                continue
        i += 1
    return max(1, total)


def split_target_conjuncts(c: Contract) -> tuple[list[str], int]:
    """Extract top-level `∧` / `×` conjuncts and leading `∃` witness count from `c`."""
    raw: Optional[str]
    is_def = c.keyword in ("def", "abbrev")
    if is_def and c.body:
        raw = c.body
    else:
        raw = c.type
    if not raw:
        return [], 0

    s = _strip_outer_parens(" ".join(raw.split()))
    n_exists = 0

    # Strip leading `fun x y =>` on lambda-style Prop defs (`def P := fun h rc => ...`)
    m_fun = re.match(r"^(?:fun|λ)\b([^=]+?)=>\s*(.+)$", s)
    if m_fun:
        s = _strip_outer_parens(m_fun.group(2))

    # Strip universal binders, outer `→` premises (`→` has lower precedence than `∧` in Lean 4),
    # and leading existential binders before splitting top-level `∧` / `×`.
    changed = True
    while changed:
        changed = False
        if s.startswith("∀") or re.match(r"^forall\b", s):
            comma = _depth0_find(s, ",")
            if comma >= 0:
                s = _strip_outer_parens(s[comma + 1:])
                changed = True
                continue
        segs = _arrow_split_depth0(s)
        if len(segs) > 1:
            s = _strip_outer_parens(segs[-1])
            changed = True
            continue
        if s.startswith(("∃", "Σ")):
            comma = _depth0_find(s, ",")
            if comma >= 0:
                n_exists += _count_exists_binders(s[1:comma])
                s = _strip_outer_parens(s[comma + 1:])
                changed = True
                continue

    parts = _split_top_binop(s, ("∧", "×"))
    return parts, n_exists


def _parse_proj_steps(dot_chain: str) -> list[int]:
    out: list[int] = []
    for seg in dot_chain.lstrip(".").split("."):
        if seg in ("1", "left", "fst"):
            out.append(1)
        elif seg in ("2", "right", "snd"):
            out.append(2)
    return out


def eval_conjunct_steps(
    steps: Sequence[int],
    total_conjuncts: int,
    start_idx: int = 1,
) -> tuple[str, int, list[int]]:
    """Evaluate `.1`/`.2` steps on a right-associated `total_conjuncts`-way `∧` starting at 1-based `start_idx`.

    Returns `(kind, index_1based, remaining_steps_inside_selected_conjunct)` where
    `kind` is `'conjunct'` (landed on a single conjunct) or `'slice'` (landed on tail `index..total`).
    """
    if total_conjuncts <= 1:
        return "conjunct", 1, list(steps)
    cur = start_idx
    for i, st in enumerate(steps):
        if cur >= total_conjuncts:
            return "conjunct", total_conjuncts, list(steps[i:])
        if st == 1:
            return "conjunct", cur, list(steps[i + 1:])
        cur += 1
    if cur >= total_conjuncts:
        return "conjunct", total_conjuncts, []
    return "slice", cur, []


def _extract_receiver_and_chains(line_txt: str) -> list[tuple[str, str]]:
    """Extract `(receiver_expr, '.2.1...')` pairs from a line of Lean code."""
    results: list[tuple[str, str]] = []
    i, n = 0, len(line_txt)
    while i < n:
        m = re.search(r"\.(?:1|2|left|right|fst|snd)\b", line_txt[i:])
        if not m:
            break
        dot_pos = i + m.start()
        # Make sure this isn't a numeric literal like `0.1` or `1.2`
        if dot_pos > 0 and line_txt[dot_pos - 1].isdigit():
            # Could be either `3.1` (float) or `.1.2` (chained). Since we consume full chains below,
            # hitting a digit immediately before the FIRST dot means numeric literal (`2.1`) unless preceded by `.`!
            if dot_pos < 2 or line_txt[dot_pos - 2] != ".":
                i = dot_pos + m.end() - m.start()
                continue
        # Consume full chain `.1.2.1...`
        chain_end = dot_pos
        while True:
            mc = re.match(r"\.(?:1|2|left|right|fst|snd)\b", line_txt[chain_end:])
            if not mc:
                break
            chain_end += mc.end()
        chain = line_txt[dot_pos:chain_end]

        # Walk backward from `dot_pos` to extract receiver (`ident` or `(...)`)
        recv = ""
        if dot_pos > 0 and line_txt[dot_pos - 1] in _CLOSE:
            close_ch = line_txt[dot_pos - 1]
            open_ch = _OPEN[_CLOSE.index(close_ch)]
            depth = 0
            k = dot_pos - 1
            while k >= 0:
                if line_txt[k] == close_ch:
                    depth += 1
                elif line_txt[k] == open_ch:
                    depth -= 1
                    if depth == 0:
                        recv = line_txt[k:dot_pos].strip()
                        break
                k -= 1
        elif dot_pos > 0:
            k = dot_pos - 1
            while k >= 0 and (line_txt[k].isalnum() or line_txt[k] in "_'.₀₁₂₃₄₅₆₇₈₉"):
                k -= 1
            recv = line_txt[k + 1:dot_pos].strip()
        results.append((recv, chain))
        i = chain_end
    return results


def _split_tuple_pattern(pat: str) -> Optional[list[str]]:
    s = pat.strip()
    if not (s.startswith("⟨") and s.endswith("⟩")):
        return None
    inner = s[1:-1].strip()
    if not inner:
        return []
    return [p.strip() for p in _depth0_split(inner, ",")]


def _pattern_vars(slot: str) -> list[str]:
    return [
        v for v in _IDENT_RE.findall(slot)
        if v not in ("_", "-") and v not in _LEAN_STOPWORDS
    ]


def _is_discard_slot(slot: str) -> bool:
    s = slot.strip()
    if s in ("-", "_"):
        return True
    if s.startswith("⟨") and s.endswith("⟩"):
        sub = _split_tuple_pattern(s)
        return bool(sub is not None and all(_is_discard_slot(x) for x in sub))
    return False


def _find_var_use_line(
    var_name: str,
    body_lines: Sequence[tuple[int, str]],
    after_line: int,
) -> Optional[tuple[int, str]]:
    rx = re.compile(rf"(?<![\w'.]){re.escape(var_name)}(?![\w'])")
    for fl, txt in body_lines:
        if fl > after_line and rx.search(txt):
            return fl, txt.strip()
    return None


# ---------------------------------------------------------------------------
# Structure / Class Field Readers
# ---------------------------------------------------------------------------

def _scan_struct_field_sites_in_contract(
    uc: Contract,
    struct_name: str,
    field_obj: Field,
    field_idx_1based: int,
    total_fields: int,
    has_direct_proj_edge: bool,
) -> list[dict[str, Any]]:
    """Locate exact lines inside `uc` where `struct_name.<field>` is projected or destructured."""
    fname = field_obj.name
    sites: list[dict[str, Any]] = []
    dot_rx = re.compile(rf"(?:\.|^|\s){re.escape(fname)}(?![\w'])")
    strict_dot_rx = re.compile(rf"\.{re.escape(fname)}(?![\w'])")

    # 1. Check signature / header
    if strict_dot_rx.search(uc.header):
        sites.append({
            "line": uc.line,
            "site_kind": "signature",
            "snippet": one_line(uc.header, 200),
        })

    # 2. Check structure/def fields if `uc` is a structure/instance
    for uf in uc.fields:
        if strict_dot_rx.search(uf.type):
            sites.append({
                "line": uf.line or uc.line,
                "site_kind": "field_type",
                "snippet": one_line(f".{uf.name} : {uf.type}", 200),
            })

    # 3. Check body lines for `.fname` dot projection
    for fl, txt in uc.body_lines:
        if strict_dot_rx.search(txt) or (has_direct_proj_edge and dot_rx.search(txt) and fname != uc.name.rsplit(".", 1)[-1]):
            if strict_dot_rx.search(txt) or f"{struct_name.rsplit('.', 1)[-1]}.{fname}" in txt or re.search(rf"\b{re.escape(fname)}\b", txt):
                if strict_dot_rx.search(txt) or has_direct_proj_edge:
                    sites.append({
                        "line": fl,
                        "site_kind": "dot_proj",
                        "snippet": one_line(txt, 200),
                    })

    # 4. Check anonymous destructuring `obtain ⟨f1, f2, ...⟩ := x` on `struct_name`-typed binders
    if not sites and total_fields >= 1 and uc.body_lines:
        struct_vars = {
            b["name"]
            for b in _parse_binder_names(uc.binders)
            if _matches_target_ident(_head_ident(b["type"]), struct_name)
        }
        for ln, stmt in _group_tactic_blocks(uc.body_lines):
            m = _DESTRUCT_STMT_RE.match(stmt)
            if not m:
                continue
            slots = _split_tuple_pattern(m.group(1))
            rhs = m.group(2).strip()
            rhs_base = rhs.split()[0].split(".")[0] if rhs else ""
            if slots and len(slots) == total_fields and (rhs_base in struct_vars or not sites):
                if rhs_base in struct_vars or total_fields >= 4:
                    slot = slots[field_idx_1based - 1]
                    if not _is_discard_slot(slot):
                        pvars = _pattern_vars(slot)
                        use_hit = _find_var_use_line(pvars[0], uc.body_lines, ln) if pvars else None
                        if use_hit is not None or not pvars:
                            sites.append({
                                "line": use_hit[0] if use_hit else ln,
                                "obtain_line": ln,
                                "bound_var": pvars[0] if pvars else None,
                                "site_kind": "destructure",
                                "snippet": one_line(use_hit[1] if use_hit else stmt, 200),
                            })

    # 5. Kernel-verified edge fallback (e.g. implicit coercion `toParent`, `simp`, or `rw` inside macro)
    if not sites and has_direct_proj_edge:
        sites.append({
            "line": uc.line,
            "site_kind": "kernel_edge",
            "snippet": one_line(uc.header, 200),
        })
    return sites


def analyze_structure_readers(
    decompiler: Any,
    struct_decl: Decl,
    struct_contract: Contract,
    *,
    field_name: Optional[str] = None,
    live_only: bool = False,
    limit: int = 50,
    max_len: int = 220,
) -> dict[str, Any]:
    """Find readers of `struct_decl` (either a specific `--field` or per-field census)."""
    kdb = decompiler.kdb
    fields = struct_contract.fields
    if not fields:
        raise ValueError(f"{struct_decl.name} [{struct_contract.keyword}] has 0 parsed fields")

    # Summary census mode when `--field` is omitted
    if field_name is None:
        proj_map: dict[str, Optional[Decl]] = {}
        proj_id_to_fname: dict[int, str] = {}
        for f in fields:
            pd = kdb.maybe(f"{struct_decl.name}.{f.name}")
            if pd is not None and pd.id != struct_decl.id:
                proj_map[f.name] = pd
                proj_id_to_fname[pd.id] = f.name
            else:
                proj_map[f.name] = None

        counts_by_field: dict[str, list[tuple[Decl, bool, int]]] = {f.name: [] for f in fields}
        if proj_id_to_fname:
            pids = list(proj_id_to_fname.keys())
            q = (
                "SELECT e.dst, e.src, d2.live_mask, COALESCE(dom.subtree_size, 0) AS dom_sz "
                "FROM edges e "
                "JOIN decls d2 ON d2.id = e.src "
                "LEFT JOIN dom ON dom.tree_id = ? AND dom.decl_id = d2.id "
                f"WHERE e.dst IN ({','.join('?' * len(pids))})"
            )
            raw = kdb.k.execute(q, [kdb._all_tree_id, *pids]).fetchall()
            all_u_ids = list({int(r[1]) for r in raw})
            u_map = {u.id: u for u in kdb.decls(all_u_ids)}
            struct_prefix = struct_decl.name + "."
            for dst_id, src_id, lmask, dom_sz in raw:
                u = u_map.get(int(src_id))
                if u is None or u.ground or u.is_aux or u.id == struct_decl.id:
                    continue
                if u.name.startswith(struct_prefix) and u.name[len(struct_prefix):] in proj_map:
                    continue
                is_live = int(lmask) != 0
                if live_only and not is_live:
                    continue
                fn = proj_id_to_fname[int(dst_id)]
                counts_by_field[fn].append((u, is_live, int(dom_sz)))

        field_rows: list[dict[str, Any]] = []
        for idx, f in enumerate(fields, 1):
            entries = counts_by_field[f.name]
            entries.sort(key=lambda t: (0 if t[1] else 1, -t[2], t[0].name))
            live_c = sum(1 for _, lv, _ in entries if lv)
            field_rows.append({
                "index": idx,
                "field": f.name,
                "line": f.line,
                "anchor": f"{struct_contract.anchor.rsplit(':', 1)[0]}:{f.line}" if f.line else struct_contract.anchor,
                "type": one_line(f.type, max_len),
                "proj_decl": proj_map[f.name].name if proj_map[f.name] else None,
                "live_readers": live_c,
                "total_readers": len(entries),
                "sample_readers": [u.name for u, _, _ in entries[:5]],
            })
        return {
            "mode": "field_census",
            "target": {
                "id": struct_decl.id,
                "name": struct_decl.name,
                "kind": struct_decl.kind,
                "keyword": struct_contract.keyword,
                "anchor": struct_contract.anchor,
                "fields_count": len(fields),
            },
            "fields": field_rows,
        }

    # Specific `--field NAME` lookup
    fld_idx = next((i for i, f in enumerate(fields, 1) if f.name == field_name), None)
    if fld_idx is None:
        avail = ", ".join(f.name for f in fields[:20])
        more = f" (+{len(fields) - 20} more)" if len(fields) > 20 else ""
        raise ValueError(
            f"field {field_name!r} not found on {struct_decl.name} ({len(fields)} fields: {avail}{more})"
        )
    fld = fields[fld_idx - 1]
    proj_decl = kdb.maybe(f"{struct_decl.name}.{field_name}")
    if proj_decl is not None and proj_decl.id == struct_decl.id:
        proj_decl = None

    # Gather kernel candidate users: `edges_dst(proj_decl)` + (when small or for destructuring) `edges_dst(struct_decl)`
    direct_proj_user_ids: set[int] = set()
    meta_by_id: dict[int, tuple[int, int, int]] = {}

    def _collect_users(dst_id: int, cap: int = 5000, mark_direct: bool = False) -> None:
        q = (
            "SELECT e.src, d2.live_mask, COALESCE(dom.subtree_size, 0) AS dom_sz, d2.fan_in "
            "FROM edges e "
            "JOIN decls d2 ON d2.id = e.src "
            "LEFT JOIN dom ON dom.tree_id = ? AND dom.decl_id = d2.id "
            "WHERE e.dst = ? "
            "ORDER BY (d2.live_mask != 0) DESC, dom_sz DESC LIMIT ?"
        )
        for src_id, lmask, dom_sz, fan_in in kdb.k.execute(q, (kdb._all_tree_id, dst_id, cap)):
            sid = int(src_id)
            if sid == struct_decl.id or (proj_decl and sid == proj_decl.id):
                continue
            meta_by_id.setdefault(sid, (int(lmask), int(dom_sz), int(fan_in)))
            if mark_direct:
                direct_proj_user_ids.add(sid)

    if proj_decl is not None:
        _collect_users(proj_decl.id, cap=5000, mark_direct=True)
    # Also scan direct `struct_decl` users for `obtain ⟨...⟩` destructuring when fan-in is moderate
    struct_fan_in = kdb.k.execute("SELECT fan_in FROM decls WHERE id=?", (struct_decl.id,)).fetchone()
    if proj_decl is None or (struct_fan_in and int(struct_fan_in[0]) <= 600):
        _collect_users(struct_decl.id, cap=600, mark_direct=False)

    struct_prefix = struct_decl.name + "."
    field_names_set = {f.name for f in fields}
    cand_decls = [
        u for u in kdb.decls(meta_by_id.keys())
        if not u.ground
        and not u.is_aux
        and not (u.name.startswith(struct_prefix) and u.name[len(struct_prefix):] in field_names_set)
        and (not live_only or meta_by_id[u.id][0] != 0)
    ]
    kdb.preload_src_rows(cand_decls)

    readers: list[dict[str, Any]] = []
    for u in cand_decls:
        lmask, dom_sz, fan_in = meta_by_id[u.id]
        has_direct = u.id in direct_proj_user_ids
        uc = decompiler.contract(u, include_thm=True, preserve_lines=True)
        if uc is None:
            if has_direct:
                readers.append({
                    "id": u.id,
                    "name": u.name,
                    "kind": u.kind,
                    "live": lmask != 0,
                    "dom_subtree": dom_sz,
                    "fan_in": fan_in,
                    "module": u.module,
                    "line": None,
                    "anchor": u.module,
                    "site_kind": "kernel_edge",
                    "snippet": None,
                    "sites_count": 1,
                })
            continue
        sites = _scan_struct_field_sites_in_contract(
            uc, struct_decl.name, fld, fld_idx, len(fields), has_direct
        )
        if not sites:
            continue
        s0 = sites[0]
        base_file = uc.anchor.rsplit(":", 1)[0]
        site_anchor = f"{base_file}:{s0['line']}" if s0.get("line") else uc.anchor
        readers.append({
            "id": u.id,
            "name": u.name,
            "kind": u.kind,
            "keyword": uc.keyword,
            "live": lmask != 0,
            "dom_subtree": dom_sz,
            "fan_in": fan_in,
            "module": u.module,
            "decl_anchor": uc.anchor,
            "line": s0["line"],
            "anchor": site_anchor,
            "site_kind": s0["site_kind"],
            "snippet": one_line(s0["snippet"], max_len),
            "sites_count": len(sites),
            "sites": sites[:5],
        })

    readers.sort(key=lambda r: (
        0 if r["live"] else 1,
        1 if r["site_kind"] == "kernel_edge" else 0,
        -r["dom_subtree"],
        -r["fan_in"],
        r["name"],
    ))
    live_count = sum(1 for r in readers if r["live"])
    fld_anchor = f"{struct_contract.anchor.rsplit(':', 1)[0]}:{fld.line}" if fld.line else struct_contract.anchor
    return {
        "mode": "field",
        "target": {
            "id": struct_decl.id,
            "name": struct_decl.name,
            "kind": struct_decl.kind,
            "keyword": struct_contract.keyword,
            "anchor": struct_contract.anchor,
            "field": fld.name,
            "field_index": fld_idx,
            "fields_total": len(fields),
            "field_line": fld.line,
            "field_anchor": fld_anchor,
            "field_type": one_line(fld.type, max_len),
            "proj_decl": proj_decl.name if proj_decl else None,
        },
        "live_count": live_count,
        "total_count": len(readers),
        "readers": readers[:limit] if limit > 0 else readers,
    }


# ---------------------------------------------------------------------------
# `∧`-Conjunct Readers (`decompile readers <Def> [--conjunct N]`)
# ---------------------------------------------------------------------------

def _scan_conjunct_reads_in_contract(
    uc: Contract,
    target_name: str,
    total_conjuncts: int,
    n_target_exists: int,
    wrappers: dict[str, tuple[int, int, int]],  # wrapper_fqn -> (w_idx_1based, w_total, w_exists)
    producer_stems: dict[str, tuple[str, int]],  # stem -> (target_or_wrapper_fqn, n_exists_in_producer)
) -> dict[int, list[dict[str, Any]]]:
    """Scan `uc` once and return `{conjunct_1based: [site_dict, ...]}` for all read conjuncts `1..K`."""
    hits: dict[int, list[dict[str, Any]]] = {}

    # Reject pure codomain producers of `target_name` unless `target_name` is ALSO in hypotheses!
    is_codomain_prod = classify_codomain_producer(uc.type, target_name) is not None
    binder_list = _parse_binder_names(uc.binders)
    arrow_segs = _arrow_split_depth0(uc.type or "")
    premises = arrow_segs[:-1] if len(arrow_segs) > 1 else []

    # Tracked local variables:
    #   target_vars[var] = (start_conjunct_1based, n_leading_exists_remaining)
    #   wrapper_vars[var] = (w_idx_1based, w_total, w_exists_remaining)
    target_vars: dict[str, tuple[int, int]] = {}
    wrapper_vars: dict[str, tuple[int, int, int]] = {}

    def _classify_type_expr(texpr: Optional[str]) -> Optional[tuple[str, Any]]:
        if not texpr:
            return None
        s = _strip_outer_parens(texpr)
        ex_cnt = 0
        while True:
            if s.startswith("∀") or re.match(r"^forall\b", s):
                c_pos = _depth0_find(s, ",")
                if c_pos >= 0:
                    s = _strip_outer_parens(s[c_pos + 1:])
                    continue
            segs = _arrow_split_depth0(s)
            if len(segs) > 1:
                s = _strip_outer_parens(segs[-1])
                continue
            if s.startswith(("∃", "Σ")):
                c_pos = _depth0_find(s, ",")
                if c_pos >= 0:
                    ex_cnt += _count_exists_binders(s[1:c_pos])
                    s = _strip_outer_parens(s[c_pos + 1:])
                    continue
            break
        hd = _head_ident(s)
        if _matches_target_ident(hd, target_name):
            return ("target", (1, n_target_exists + ex_cnt))
        for w_fqn, (w_idx, w_tot, w_ex) in wrappers.items():
            if _matches_target_ident(hd, w_fqn):
                return ("wrapper", (w_idx, w_tot, w_ex + ex_cnt))
        return None

    has_hyp_target = False
    for b in binder_list:
        cl = _classify_type_expr(b["type"])
        if cl is not None:
            has_hyp_target = True
            if cl[0] == "target":
                target_vars[b["name"]] = cl[1]
            else:
                wrapper_vars[b["name"]] = cl[1]

    premise_classes = [_classify_type_expr(p) for p in premises]
    if any(pc is not None for pc in premise_classes):
        has_hyp_target = True

    if is_codomain_prod and not has_hyp_target:
        return {}

    def _add_hit(c_idx: int, site: dict[str, Any]) -> None:
        if 1 <= c_idx <= total_conjuncts:
            lst = hits.setdefault(c_idx, [])
            if not any(x["line"] == site["line"] and x["site_kind"] == site["site_kind"] for x in lst):
                lst.append(site)

    def _rhs_origin(rhs: str) -> Optional[tuple[str, Any]]:
        s = _strip_outer_parens(rhs.strip())
        if not s:
            return None
        # Direct tracked var or application `(hW x y ...)`
        hd = _head_ident(s)
        if hd:
            base = hd.split(".", 1)[0]
            if base in target_vars and "." not in hd:
                return ("target", target_vars[base])
            if base in wrapper_vars and "." not in hd:
                return ("wrapper", wrapper_vars[base])
            last = hd.rsplit(".", 1)[-1]
            if last in producer_stems:
                fqn, p_ex = producer_stems[last]
                if fqn == target_name:
                    return ("target", (1, n_target_exists + p_ex))
                if fqn in wrappers:
                    w_idx, w_tot, w_ex = wrappers[fqn]
                    return ("wrapper", (w_idx, w_tot, w_ex + p_ex))
        return None

    # Pass 1: walk grouped tactic statements to propagate `intro`, `obtain`, and `have`/`let` aliases/slices
    premise_cursor = 0
    for ln, stmt in _group_tactic_blocks(uc.body_lines):
        m_in = re.match(r"^(?:intro|rintro)\s+(.+)$", stmt)
        if m_in:
            raw_arg = m_in.group(1).strip()
            if raw_arg.startswith("⟨"):
                # `rintro ⟨a1, a2, ...⟩` destructuring the next premise directly!
                slots = _split_tuple_pattern(raw_arg)
                pcl = premise_classes[premise_cursor] if premise_cursor < len(premise_classes) else None
                premise_cursor += 1
                if slots and pcl and pcl[0] == "target":
                    st_idx, ex_rem = pcl[1]
                    c_slots = slots[ex_rem:]
                    for i, sl in enumerate(c_slots):
                        is_last = i == len(c_slots) - 1
                        c_num = st_idx + i
                        if is_last and c_num < total_conjuncts:
                            for pv in _pattern_vars(sl):
                                target_vars[pv] = (c_num, 0)
                        elif not _is_discard_slot(sl):
                            pvars = _pattern_vars(sl)
                            use_hit = _find_var_use_line(pvars[0], uc.body_lines, ln) if pvars else None
                            if use_hit is not None or not pvars:
                                _add_hit(c_num, {
                                    "line": use_hit[0] if use_hit else ln,
                                    "obtain_line": ln,
                                    "bound_var": pvars[0] if pvars else None,
                                    "site_kind": "destructure",
                                    "snippet": one_line(use_hit[1] if use_hit else stmt, 200),
                                })
                continue
            for tok in re.findall(r"⟨[^⟩]*⟩|[A-Za-z_][\w']*|-", raw_arg):
                pcl = premise_classes[premise_cursor] if premise_cursor < len(premise_classes) else None
                premise_cursor += 1
                if pcl is not None and tok not in ("_", "-") and not tok.startswith("⟨"):
                    if pcl[0] == "target":
                        target_vars[tok] = pcl[1]
                    else:
                        wrapper_vars[tok] = pcl[1]
            continue

        m_ds = _DESTRUCT_STMT_RE.match(stmt)
        if m_ds:
            pat_str, rhs_str = m_ds.group(1), m_ds.group(2).strip()
            slots = _split_tuple_pattern(pat_str)
            orig = _rhs_origin(rhs_str)
            if slots and orig is not None:
                if orig[0] == "wrapper":
                    w_idx, w_tot, w_ex = orig[1]
                    if len(slots) <= w_ex and slots:
                        # Only existential witnesses unpacked; last slot holds the wrapper body!
                        rem_ex = w_ex - (len(slots) - 1)
                        for pv in _pattern_vars(slots[-1]):
                            wrapper_vars[pv] = (w_idx, w_tot, max(0, rem_ex))
                    else:
                        c_slots = slots[w_ex:]
                        if len(c_slots) >= w_idx:
                            target_slot = c_slots[w_idx - 1]
                            is_tail = (w_idx == len(c_slots)) and (len(c_slots) < w_tot)
                            if not is_tail and not _is_discard_slot(target_slot):
                                if target_slot.startswith("⟨"):
                                    sub_slots = _split_tuple_pattern(target_slot) or []
                                    sub_c = sub_slots[n_target_exists:]
                                    for j, ssl in enumerate(sub_c):
                                        c_num = 1 + j
                                        is_sub_last = j == len(sub_c) - 1
                                        if is_sub_last and c_num < total_conjuncts:
                                            for pv in _pattern_vars(ssl):
                                                target_vars[pv] = (c_num, 0)
                                        elif not _is_discard_slot(ssl):
                                            pvars = _pattern_vars(ssl)
                                            use_hit = _find_var_use_line(pvars[0], uc.body_lines, ln) if pvars else None
                                            if use_hit is not None:
                                                _add_hit(c_num, {
                                                    "line": use_hit[0],
                                                    "obtain_line": ln,
                                                    "bound_var": pvars[0],
                                                    "site_kind": "destructure",
                                                    "snippet": one_line(use_hit[1], 200),
                                                })
                                else:
                                    for pv in _pattern_vars(target_slot):
                                        target_vars[pv] = (1, n_target_exists)
                elif orig[0] == "target":
                    st_idx, ex_rem = orig[1]
                    if len(slots) <= ex_rem and slots:
                        # Unpacked existential witnesses only (e.g. `obtain ⟨eK, xW, heK, hW⟩ := hWin ...`)!
                        # The final slot now holds `∀ ..., Target`!
                        rem_ex = ex_rem - (len(slots) - 1)
                        for pv in _pattern_vars(slots[-1]):
                            target_vars[pv] = (st_idx, max(0, rem_ex))
                    else:
                        c_slots = slots[ex_rem:]
                        for i, sl in enumerate(c_slots):
                            c_num = st_idx + i
                            is_last = i == len(c_slots) - 1
                            if is_last and c_num < total_conjuncts:
                                for pv in _pattern_vars(sl):
                                    target_vars[pv] = (c_num, 0)
                            elif not _is_discard_slot(sl):
                                pvars = _pattern_vars(sl)
                                use_hit = _find_var_use_line(pvars[0], uc.body_lines, ln) if pvars else None
                                if use_hit is not None or not pvars:
                                    _add_hit(c_num, {
                                        "line": use_hit[0] if use_hit else ln,
                                        "obtain_line": ln,
                                        "bound_var": pvars[0] if pvars else None,
                                        "site_kind": "destructure",
                                        "snippet": one_line(use_hit[1] if use_hit else stmt, 200),
                                    })
            continue

        if stmt.startswith(("have ", "let ")):
            rest_hv = stmt.split(None, 1)[1].strip()
            eq_hv = _depth0_find_assign(rest_hv)
            if eq_hv > 0:
                lhs_hv = rest_hv[:eq_hv].strip()
                rhs_str = rest_hv[eq_hv + 2:].strip()
                col_hv = _depth0_find(lhs_hv, ":")
                if col_hv >= 0:
                    lhs_var_cand = lhs_hv[:col_hv].strip()
                    lhs_typ: Optional[str] = lhs_hv[col_hv + 1:].strip()
                else:
                    lhs_var_cand = lhs_hv
                    lhs_typ = None
                if _IDENT_RE.fullmatch(lhs_var_cand):
                    lhs_var = lhs_var_cand
                    if lhs_typ:
                        tcl = _classify_type_expr(lhs_typ)
                        if tcl is not None:
                            if tcl[0] == "target":
                                target_vars[lhs_var] = tcl[1]
                            else:
                                wrapper_vars[lhs_var] = tcl[1]
                            continue
                    rc_pairs = _extract_receiver_and_chains(rhs_str)
                    if len(rc_pairs) == 1 and rhs_str.endswith(rc_pairs[0][1]):
                        recv, ch = rc_pairs[0]
                        steps = _parse_proj_steps(ch)
                        orig = _rhs_origin(recv)
                        if orig and orig[0] == "wrapper":
                            w_idx, w_tot, _ = orig[1]
                            wk, wsel, rem_st = eval_conjunct_steps(steps, w_tot, 1)
                            if wk == "conjunct" and wsel == w_idx:
                                if not rem_st:
                                    target_vars[lhs_var] = (1, n_target_exists)
                                else:
                                    tk, tsel, _ = eval_conjunct_steps(rem_st, total_conjuncts, 1)
                                    if tk == "slice":
                                        target_vars[lhs_var] = (tsel, 0)
                        elif orig and orig[0] == "target":
                            st_idx, _ = orig[1]
                            tk, tsel, _ = eval_conjunct_steps(steps, total_conjuncts, st_idx)
                            if tk == "slice":
                                target_vars[lhs_var] = (tsel, 0)
                        continue

                    orig = _rhs_origin(rhs_str)
                    if orig is not None:
                        if orig[0] == "target":
                            target_vars[lhs_var] = orig[1]
                        else:
                            wrapper_vars[lhs_var] = orig[1]

    # Pass 2: line-by-line `.1`/`.2` projection chain scan across `uc.body_lines`
    t_stem = target_name.rsplit(".", 1)[-1]
    unfold_rx = re.compile(rf"\b(?:unfold|dsimp|simp)\b[^\n]*\b{re.escape(t_stem)}\b")
    for fl, txt in uc.body_lines:
        for recv, ch in _extract_receiver_and_chains(txt):
            steps = _parse_proj_steps(ch)
            if not steps:
                continue
            orig = _rhs_origin(recv)
            if orig is not None:
                if orig[0] == "target":
                    st_idx, ex_rem = orig[1]
                    eff_steps = steps[ex_rem:]
                    if eff_steps:
                        tk, tsel, _ = eval_conjunct_steps(eff_steps, total_conjuncts, st_idx)
                        if tk == "conjunct":
                            _add_hit(tsel, {
                                "line": fl,
                                "site_kind": "dot_proj",
                                "proj_chain": ch,
                                "snippet": one_line(txt, 200),
                            })
                elif orig[0] == "wrapper":
                    w_idx, w_tot, w_ex = orig[1]
                    eff_steps = steps[w_ex:]
                    if eff_steps:
                        wk, wsel, rem_st = eval_conjunct_steps(eff_steps, w_tot, 1)
                        if wk == "conjunct" and wsel == w_idx and rem_st:
                            tk, tsel, _ = eval_conjunct_steps(rem_st, total_conjuncts, 1)
                            if tk == "conjunct":
                                _add_hit(tsel, {
                                    "line": fl,
                                    "site_kind": "wrapper_proj",
                                    "proj_chain": ch,
                                    "snippet": one_line(txt, 200),
                                })
            elif wrappers:
                # Fallback for indirect wrapper field calls like `(Fm.sizes x hx i).2.2.2.1.<subchain>`
                # on pure `∧`-bundle wrappers (`w_ex == 0 and w_tot >= 3`) when `u` has a kernel edge to `target_name`.
                for _w_fqn, (w_idx, w_tot, w_ex) in wrappers.items():
                    if w_ex != 0 or w_tot < 3:
                        continue
                    wk, wsel, rem_st = eval_conjunct_steps(steps, w_tot, 1)
                    if wk == "conjunct" and wsel == w_idx and rem_st:
                        tk, tsel, _ = eval_conjunct_steps(rem_st, total_conjuncts, 1)
                        if tk == "conjunct":
                            _add_hit(tsel, {
                                "line": fl,
                                "site_kind": "wrapper_proj",
                                "proj_chain": ch,
                                "snippet": one_line(txt, 200),
                            })
                            break

    # Fallback: if `uc` took `Target` as a hypothesis and unfolded it (`unfold Target; linarith`) with 0 projections
    if not hits and has_hyp_target:
        for fl, txt in uc.body_lines:
            if unfold_rx.search(txt):
                for c_i in range(1, total_conjuncts + 1):
                    _add_hit(c_i, {
                        "line": fl,
                        "site_kind": "unfold",
                        "snippet": one_line(txt, 200),
                    })
                break

    return hits


def analyze_conjunct_readers(
    decompiler: Any,
    target_decl: Decl,
    target_contract: Contract,
    *,
    conjunct_idx: Optional[int] = None,
    live_only: bool = False,
    limit: int = 50,
    max_len: int = 220,
) -> dict[str, Any]:
    """Find project declarations that read/project `N`-th `∧`-conjunct of `target_decl` (or all conjuncts census)."""
    kdb = decompiler.kdb
    conjuncts, n_target_exists = split_target_conjuncts(target_contract)
    total_c = len(conjuncts)
    if total_c == 0:
        raise ValueError(f"{target_decl.name} [{target_contract.keyword}] has no extractable statement/body")
    if conjunct_idx is not None and (conjunct_idx < 1 or conjunct_idx > total_c):
        preview = "; ".join(f"#{i}: {one_line(c, 70)}" for i, c in enumerate(conjuncts[:8], 1))
        raise ValueError(
            f"--conjunct {conjunct_idx} out of range for {target_decl.name} "
            f"(has {total_c} conjunct(s): {preview})"
        )

    # 1. Query kernel incoming edges (`edges_dst`) on `target_decl`
    q_users = (
        "SELECT e.src, e.kind, d2.live_mask, COALESCE(dom.subtree_size, 0) AS dom_sz, d2.fan_in "
        "FROM edges e "
        "JOIN decls d2 ON d2.id = e.src "
        "LEFT JOIN dom ON dom.tree_id = ? AND dom.decl_id = d2.id "
        "WHERE e.dst = ? "
        "ORDER BY (d2.live_mask != 0) DESC, dom_sz DESC LIMIT 5000"
    )
    raw_rows = kdb.k.execute(q_users, (kdb._all_tree_id, target_decl.id)).fetchall()
    meta_by_id: dict[int, tuple[int, int, int, int]] = {
        int(r[0]): (int(r[1]), int(r[2]), int(r[3]), int(r[4]))
        for r in raw_rows
        if int(r[0]) != target_decl.id
    }
    base_decls = [
        u for u in kdb.decls(meta_by_id.keys())
        if not u.ground and not u.is_aux
    ]
    kdb.preload_src_rows(base_decls)

    # 2. Identify 1-hop `∧`-wrapper `def`s (like `SizesAt` wrapping `SizeKRel` at conjunct #4)
    #    and direct producers (like `winM` / `hWin` producing `Win_at`, `Fm.sizes` producing `SizesAt`)
    wrappers: dict[str, tuple[int, int, int]] = {}  # wrapper_fqn -> (w_idx, w_total, w_exists)
    producer_stems: dict[str, tuple[str, int]] = {
        target_decl.name.rsplit(".", 1)[-1]: (target_decl.name, 0)
    }

    for u in base_decls:
        ek = meta_by_id[u.id][0]
        if u.kind == "def" and ek in (VALUE, BOTH):
            wc = decompiler.contract(u)
            if wc and wc.keyword in ("def", "abbrev") and wc.body:
                w_conjs, w_ex = split_target_conjuncts(wc)
                if len(w_conjs) >= 2:
                    for idx1, part in enumerate(w_conjs, 1):
                        if (
                            _matches_target_ident(_head_ident(part), target_decl.name)
                            or classify_codomain_producer(part, target_decl.name) == "direct"
                        ):
                            wrappers[u.name] = (idx1, len(w_conjs), w_ex)
                            producer_stems[u.name.rsplit(".", 1)[-1]] = (u.name, 0)
                            break
                elif len(w_conjs) == 1 and classify_codomain_producer(wc.body, target_decl.name) in ("direct", "exists"):
                    wrappers[u.name] = (1, 1, w_ex)
                    producer_stems[u.name.rsplit(".", 1)[-1]] = (u.name, 0)
        elif ek in (TYPE, BOTH):
            uc = decompiler.contract(u)
            if uc and classify_codomain_producer(uc.type, target_decl.name) is not None:
                _, u_ex = split_target_conjuncts(uc)
                producer_stems[u.name.rsplit(".", 1)[-1]] = (target_decl.name, u_ex)

    # Also include users of wrapper defs (and register wrapper-producing lemmas even if already in `meta_by_id`)
    for w_fqn in list(wrappers.keys())[:4]:
        wd = kdb.maybe(w_fqn)
        if wd is None:
            continue
        for src_id, ek, lmask, dom_sz, fan_in in kdb.k.execute(q_users, (kdb._all_tree_id, wd.id)):
            sid = int(src_id)
            if sid == target_decl.id or sid == wd.id:
                continue
            meta_by_id.setdefault(sid, (int(ek), int(lmask), int(dom_sz), int(fan_in)))
            if int(ek) in (TYPE, BOTH):
                wu = kdb.maybe(sid)
                if wu and not wu.ground and not wu.is_aux:
                    wuc = decompiler.contract(wu)
                    if wuc and classify_codomain_producer(wuc.type, w_fqn) is not None:
                        _, wu_ex = split_target_conjuncts(wuc)
                        producer_stems[wu.name.rsplit(".", 1)[-1]] = (w_fqn, wu_ex)

    cand_decls = [
        u for u in kdb.decls(meta_by_id.keys())
        if not u.ground
        and not u.is_aux
        and u.name not in wrappers
        and (not live_only or meta_by_id[u.id][1] != 0)
    ]
    kdb.preload_src_rows(cand_decls)

    by_conj: dict[int, list[dict[str, Any]]] = {i: [] for i in range(1, total_c + 1)}
    for u in cand_decls:
        _ek, lmask, dom_sz, fan_in = meta_by_id[u.id]
        uc = decompiler.contract(u, include_thm=True, preserve_lines=True)
        if uc is None or not uc.body_lines:
            continue
        c_hits = _scan_conjunct_reads_in_contract(
            uc,
            target_decl.name,
            total_c,
            n_target_exists,
            wrappers,
            producer_stems,
        )
        if not c_hits:
            continue
        base_file = uc.anchor.rsplit(":", 1)[0]
        for c_i, sites in c_hits.items():
            if conjunct_idx is not None and c_i != conjunct_idx:
                continue
            s0 = sites[0]
            site_anchor = f"{base_file}:{s0['line']}" if s0.get("line") else uc.anchor
            by_conj[c_i].append({
                "id": u.id,
                "name": u.name,
                "kind": u.kind,
                "keyword": uc.keyword,
                "live": lmask != 0,
                "dom_subtree": dom_sz,
                "fan_in": fan_in,
                "module": u.module,
                "decl_anchor": uc.anchor,
                "line": s0["line"],
                "anchor": site_anchor,
                "site_kind": s0["site_kind"],
                "snippet": one_line(s0["snippet"], max_len),
                "sites_count": len(sites),
                "sites": sites[:5],
            })

    for c_i in by_conj:
        by_conj[c_i].sort(key=lambda r: (0 if r["live"] else 1, -r["dom_subtree"], -r["fan_in"], r["name"]))

    wrapper_list = [
        {"name": wn, "conjunct_index": wi, "conjuncts_total": wt}
        for wn, (wi, wt, _) in sorted(wrappers.items())
    ]

    if conjunct_idx is None:
        rows = []
        for i, c_txt in enumerate(conjuncts, 1):
            rlist = by_conj[i]
            rows.append({
                "conjunct": i,
                "formula": one_line(c_txt, max_len),
                "live_readers": sum(1 for r in rlist if r["live"]),
                "total_readers": len(rlist),
                "sample_readers": [f"{r['name']} ({r['anchor']})" for r in rlist[:4]],
            })
        return {
            "mode": "conjunct_census",
            "target": {
                "id": target_decl.id,
                "name": target_decl.name,
                "kind": target_decl.kind,
                "keyword": target_contract.keyword,
                "anchor": target_contract.anchor,
                "conjuncts_total": total_c,
                "exists_binders": n_target_exists,
            },
            "wrappers": wrapper_list,
            "conjuncts": rows,
        }

    rlist = by_conj[conjunct_idx]
    return {
        "mode": "conjunct",
        "target": {
            "id": target_decl.id,
            "name": target_decl.name,
            "kind": target_decl.kind,
            "keyword": target_contract.keyword,
            "anchor": target_contract.anchor,
            "conjunct": conjunct_idx,
            "conjuncts_total": total_c,
            "exists_binders": n_target_exists,
            "formula": one_line(conjuncts[conjunct_idx - 1], max_len),
        },
        "wrappers": wrapper_list,
        "live_count": sum(1 for r in rlist if r["live"]),
        "total_count": len(rlist),
        "readers": rlist[:limit] if limit > 0 else rlist,
    }
