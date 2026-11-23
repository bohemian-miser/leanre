"""Read-only access to the kernel-exact graph (`outputs/kernel/kernel.db`, schema in docs/KERNEL.md)
and the Phase 2 source index (`outputs/leanre.db`).

Every connection is opened with `mode=ro` (Phase 4 CPU/RAM hygiene rule). stdlib only.
"""
from __future__ import annotations

import difflib
import os
import re
import sqlite3
from dataclasses import dataclass
from typing import Iterable, Iterator, Optional

from .source import read_contract

_HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(_HERE))
DEFAULT_KERNEL_DB = os.path.join(REPO, "outputs", "kernel", "kernel.db")
DEFAULT_LEANRE_DB = os.path.join(REPO, "outputs", "leanre.db")
DEFAULT_SRC = os.path.join(REPO, "data", "rh_mirror", "src")

# edges.kind
TYPE, VALUE, BOTH = 1, 2, 3
EDGE_REL = {TYPE: "type", VALUE: "value", BOTH: "both"}

# decl_module.method values that mean "not part of the target project" (Mathlib / Lean core / Batteries).
GROUND_METHODS = (
    "unmatched:challenge_library",
    "unmatched:library_or_external",
    "unmatched:external_private",
)

_AUX_LAST_PREFIXES = ("_", "match_", "proof_")
_AUTO_INST_RE = re.compile(r"^(?:inst[A-Z0-9_]|_inst_)")


def is_aux_name(name: str) -> bool:
    """True for compiler/tactic auxiliary declarations (._proof_*, ._simp_*, _rarg, etc.)."""
    last = name.rsplit(".", 1)[-1]
    return (
        last.startswith(_AUX_LAST_PREFIXES)
        or "._" in name
        or last.endswith("_rarg")
    )


def is_auto_instance_name(name: str) -> bool:
    """True for Lean 4 elaborated instance names (`instFoo...`, `Ns.instBar...`, `_inst_...`)."""
    if is_aux_name(name):
        return False
    last = name.rsplit(".", 1)[-1]
    if last.endswith((".eq_1", ".eq_2", ".eq_def")):
        return False
    return bool(_AUTO_INST_RE.match(last))


def _escape_like(s: str) -> str:
    return s.replace("!", "!!").replace("%", "!%").replace("_", "!_")


def _common_prefix_len(a: list[str], b: list[str]) -> int:
    n = 0
    for x, y in zip(a, b):
        if x == y:
            n += 1
        else:
            break
    return n


def open_ro(path: str) -> sqlite3.Connection:
    if not os.path.exists(path):
        raise FileNotFoundError(path)
    con = sqlite3.connect(f"file:{os.path.abspath(path)}?mode=ro", uri=True, check_same_thread=False)
    con.execute("PRAGMA query_only=1")
    return con


@dataclass(frozen=True)
class Decl:
    id: int
    name: str
    kind: str
    module: Optional[str]
    method: str
    src_decl_id: Optional[int]

    @property
    def ground(self) -> bool:
        """True for Mathlib/Lean/external decls (not authored in the target project)."""
        return self.method in GROUND_METHODS

    @property
    def is_aux(self) -> bool:
        return is_aux_name(self.name)


@dataclass(frozen=True)
class DomNode:
    decl_id: int
    idom: Optional[int]
    depth: int
    subtree_size: int


@dataclass(frozen=True)
class ResolveHit:
    decl: Decl
    all_dom: int
    match: str


class ResolveError(LookupError):
    """Raised by `KernelDB.resolve_unique` when a query is missing or ambiguous."""

    def __init__(
        self,
        message: str,
        query: str,
        hits: Optional[list[ResolveHit]] = None,
        ambiguous: bool = False,
    ) -> None:
        super().__init__(message)
        self.query = query
        self.hits = hits or []
        self.ambiguous = ambiguous


class KernelDB:
    """Thin read-only facade over kernel.db (+ optional leanre.db for file:line anchors)."""

    def __init__(self, kernel_db: str = DEFAULT_KERNEL_DB, leanre_db: Optional[str] = DEFAULT_LEANRE_DB,
                 tree: str = "ALL") -> None:
        self.kpath = kernel_db
        self.k = open_ro(kernel_db)
        self.l = open_ro(leanre_db) if leanre_db and os.path.exists(leanre_db) else None
        row = self.k.execute("SELECT id FROM dom_trees WHERE label=?", (tree,)).fetchone()
        if row is None:
            raise KeyError(f"dom tree {tree!r} not found")
        self.tree_id = int(row[0])
        self.tree_label = tree
        if tree == "ALL":
            self._all_tree_id = self.tree_id
        else:
            arow = self.k.execute("SELECT id FROM dom_trees WHERE label='ALL'").fetchone()
            self._all_tree_id = int(arow[0]) if arow else self.tree_id
        self._decl_cache: dict[int, Decl] = {}
        self._inst_src_ids: Optional[set[int]] = None
        self._src_kw_cache: dict[tuple[str, int], Optional[str]] = {}
        self._near_cache: dict[str, tuple[list[str], list[str], set[int]]] = {}
        self._suffix_scans = 0
        self._stem_index: Optional[dict[str, list[tuple[int, str]]]] = None

    def close(self) -> None:
        if getattr(self, "k", None) is not None:
            self.k.close()
        if getattr(self, "l", None) is not None:
            self.l.close()

    def __enter__(self) -> "KernelDB":
        return self

    def __exit__(self, *_exc) -> None:
        self.close()

    # ---- declarations -------------------------------------------------
    _DECL_SQL = ("SELECT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id "
                 "FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id ")

    def _mk(self, r) -> Decl:
        d = Decl(int(r[0]), r[1], r[2], r[3], r[4], r[5])
        self._decl_cache[d.id] = d
        return d

    def decl(self, key: int | str) -> Decl:
        if isinstance(key, int):
            if key in self._decl_cache:
                return self._decl_cache[key]
            r = self.k.execute(self._DECL_SQL + "WHERE d.id=?", (key,)).fetchone()
        else:
            r = self.k.execute(self._DECL_SQL + "WHERE d.name=?", (key,)).fetchone()
            if r is None:  # constants (ctors/recs/projections) belong to a parent decl record
                c = self.k.execute("SELECT decl_id FROM consts WHERE name=?", (key,)).fetchone()
                if c is not None:
                    r = self.k.execute(self._DECL_SQL + "WHERE d.id=?", (int(c[0]),)).fetchone()
        if r is None:
            raise KeyError(f"declaration not in kernel.db: {key!r}")
        return self._mk(r)

    def maybe(self, key: int | str) -> Optional[Decl]:
        try:
            return self.decl(key)
        except KeyError:
            return None

    def decls(self, ids: Iterable[int]) -> list[Decl]:
        ids = list(ids)
        out: dict[int, Decl] = {i: self._decl_cache[i] for i in ids if i in self._decl_cache}
        miss = [i for i in ids if i not in out]
        for chunk in _chunks(miss, 900):
            q = self._DECL_SQL + f"WHERE d.id IN ({','.join('?' * len(chunk))})"
            for r in self.k.execute(q, chunk):
                out[int(r[0])] = self._mk(r)
        return [out[i] for i in ids if i in out]

    def all_dom_map(self, ids: Iterable[int]) -> dict[int, int]:
        id_list = list(dict.fromkeys(ids))
        out: dict[int, int] = {i: 0 for i in id_list}
        for chunk in _chunks(id_list, 900):
            q = f"SELECT decl_id, subtree_size FROM dom WHERE tree_id=? AND decl_id IN ({','.join('?' * len(chunk))})"
            for did, sz in self.k.execute(q, [self._all_tree_id, *chunk]):
                out[int(did)] = int(sz)
        return out

    # ---- instance detection (`search --kind instance` & `contract`) ---
    def _instance_src_ids(self) -> set[int]:
        if self._inst_src_ids is None:
            if self.l is None:
                self._inst_src_ids = set()
            else:
                self._inst_src_ids = {
                    int(r[0])
                    for r in self.l.execute("SELECT id FROM declarations WHERE kind='instance'")
                }
        return self._inst_src_ids

    def is_instance(self, d: Decl, src_root: Optional[str] = None) -> bool:
        if d.is_aux or d.kind not in ("def", "thm"):
            return False
        if d.method == "unmatched:project_auto_instance":
            return True
        if d.src_decl_id is not None and d.src_decl_id in self._instance_src_ids():
            return True
        if is_auto_instance_name(d.name):
            return True
        if self.l is None and not d.ground and src_root and d.module:
            key = (os.path.abspath(src_root), d.id)
            if key not in self._src_kw_cache:
                rel = self.module_file(d.module)
                c = read_contract(src_root, rel, d.name) if rel else None
                self._src_kw_cache[key] = c.keyword if c is not None else None
            return self._src_kw_cache[key] == "instance"
        return False

    # ---- search -------------------------------------------------------
    def search(
        self,
        pattern: str,
        limit: int = 50,
        *,
        project_only: bool = False,
        no_aux: bool = False,
        case_sensitive: bool = False,
        kind: Optional[str] = None,
        module_regex: Optional[str] = None,
        sort_by: str = "name",
        regex: bool = False,
        search_module: bool = False,
        src_root: Optional[str] = None,
    ) -> list[Decl]:
        return [
            r[0]
            for r in self.search_rows(
                pattern,
                limit,
                project_only=project_only,
                no_aux=no_aux,
                case_sensitive=case_sensitive,
                kind=kind,
                module_regex=module_regex,
                sort_by=sort_by,
                regex=regex,
                search_module=search_module,
                src_root=src_root,
            )
        ]

    def search_rows(
        self,
        pattern: str,
        limit: int = 50,
        *,
        project_only: bool = False,
        no_aux: bool = False,
        case_sensitive: bool = False,
        kind: Optional[str] = None,
        module_regex: Optional[str] = None,
        sort_by: str = "name",
        regex: bool = False,
        search_module: bool = False,
        src_root: Optional[str] = None,
    ) -> list[tuple[Decl, Optional[int], int, int]]:
        """Search decls returning `(Decl, dom_subtree, fan_in, value_nodes)`."""
        if sort_by not in ("name", "dom", "fan_in", "vn"):
            raise ValueError(f"invalid sort_by {sort_by!r} (expected name|dom|fan_in|vn)")
        mod_rx: Optional[re.Pattern[str]] = None
        if module_regex:
            try:
                mod_rx = re.compile(module_regex)
            except re.error as e:
                raise ValueError(f"invalid --module regex {module_regex!r}: {e}") from e
        pat_rx: Optional[re.Pattern[str]] = None
        if regex:
            rx_flags = 0 if case_sensitive else re.IGNORECASE
            try:
                pat_rx = re.compile(pattern, rx_flags)
            except re.error as e:
                raise ValueError(f"invalid --regex pattern {pattern!r}: {e}") from e

        raw_kinds = [k.strip() for k in (kind or "").split(",") if k.strip()]
        want_instance = "instance" in raw_kinds
        db_kinds = [k for k in raw_kinds if k != "instance"]

        # Fast covering-index pre-scan for regex queries (avoids 1.47M-row JOIN + ORDER BY before regex filter)
        if pat_rx is not None and not search_module:
            matched_ids: list[int] = []
            for did, dname in self.k.execute("SELECT id, name FROM decls"):
                if pat_rx.search(dname):
                    matched_ids.append(int(did))
                    if len(matched_ids) > 5000:
                        break
            if not matched_ids:
                return []
            if len(matched_ids) <= 5000:
                rows_cand: list[tuple[Decl, Optional[int], int, int]] = []
                for chunk in _chunks(matched_ids, 900):
                    iq = (
                        "SELECT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id, "
                        "dom.subtree_size, d.fan_in, d.value_nodes "
                        "FROM decls d "
                        "LEFT JOIN decl_module m ON m.decl_id = d.id "
                        "LEFT JOIN dom ON dom.tree_id = ? AND dom.decl_id = d.id "
                        f"WHERE d.id IN ({','.join('?' * len(chunk))})"
                    )
                    for r in self.k.execute(iq, [self._all_tree_id, *chunk]):
                        d = self._mk(r[:6])
                        if project_only and d.ground:
                            continue
                        if no_aux and d.is_aux:
                            continue
                        if raw_kinds:
                            ok_kind = (d.kind in db_kinds) or (want_instance and self.is_instance(d, src_root=src_root))
                            if not ok_kind:
                                continue
                        if mod_rx is not None and not mod_rx.search(d.module or ""):
                            continue
                        dom_sz = int(r[6]) if r[6] is not None else None
                        rows_cand.append((d, dom_sz, int(r[7]), int(r[8])))
                py_order = {
                    "name": lambda t: (len(t[0].name), t[0].name),
                    "dom": lambda t: (-(t[1] or 0), len(t[0].name), t[0].name),
                    "fan_in": lambda t: (-t[2], len(t[0].name), t[0].name),
                    "vn": lambda t: (-t[3], len(t[0].name), t[0].name),
                }
                rows_cand.sort(key=py_order[sort_by])
                return rows_cand[:limit] if limit > 0 else rows_cand

        has_wild = (not regex) and ("%" in pattern)
        where: list[str] = []
        params: list = [self._all_tree_id]
        if not regex:
            like_pat = pattern if has_wild else f"%{_escape_like(pattern)}%"
            if search_module:
                if has_wild:
                    where.append("(d.name LIKE ? OR COALESCE(m.module, '') LIKE ?)")
                else:
                    where.append("(d.name LIKE ? ESCAPE '!' OR COALESCE(m.module, '') LIKE ? ESCAPE '!')")
                params.extend([like_pat, like_pat])
            else:
                where.append("d.name LIKE ? ESCAPE '!'" if not has_wild else "d.name LIKE ?")
                params.append(like_pat)
        if project_only:
            ph = ",".join("?" * len(GROUND_METHODS))
            where.append(f"COALESCE(m.method, 'unmatched:none') NOT IN ({ph})")
            params.extend(GROUND_METHODS)
        if raw_kinds:
            sql_kinds = sorted(set(db_kinds) | ({"def", "thm"} if want_instance else set()))
            ph = ",".join("?" * len(sql_kinds))
            where.append(f"d.kind IN ({ph})")
            params.extend(sql_kinds)
            if want_instance and not db_kinds:
                where.append("d.name NOT LIKE '%.!_%' ESCAPE '!' AND d.name NOT LIKE '%!_rarg' ESCAPE '!'")
                if self.l is not None:
                    where.append(
                        "(m.src_decl_id IS NOT NULL OR m.method = 'unmatched:project_auto_instance' "
                        "OR d.name LIKE 'inst%' OR d.name LIKE '%.inst%' OR d.name LIKE '%!_inst!_%' ESCAPE '!')"
                    )
        if no_aux:
            where.append("d.name NOT LIKE '%.!_%' ESCAPE '!' AND d.name NOT LIKE '%!_rarg' ESCAPE '!'")
        order_map = {
            "name": "length(d.name) ASC, d.name ASC",
            "dom": "COALESCE(dom.subtree_size, 0) DESC, length(d.name) ASC, d.name ASC",
            "fan_in": "d.fan_in DESC, length(d.name) ASC, d.name ASC",
            "vn": "d.value_nodes DESC, length(d.name) ASC, d.name ASC",
        }
        needs_py_filter = bool(regex or case_sensitive or module_regex or no_aux or want_instance)
        sql_limit = "" if (limit <= 0 or needs_py_filter) else f" LIMIT {int(limit)}"
        where_sql = f"WHERE {' AND '.join(where)} " if where else ""
        q = (
            "SELECT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id, "
            "dom.subtree_size, d.fan_in, d.value_nodes "
            "FROM decls d "
            "LEFT JOIN decl_module m ON m.decl_id = d.id "
            "LEFT JOIN dom ON dom.tree_id = ? AND dom.decl_id = d.id "
            f"{where_sql}"
            f"ORDER BY {order_map[sort_by]}{sql_limit}"
        )
        if not regex and case_sensitive and has_wild:
            rx_parts = [re.escape(p) for p in pattern.split("%")]
            name_rx: Optional[re.Pattern[str]] = re.compile("^" + ".*".join(rx_parts) + "$")
        else:
            name_rx = None

        out: list[tuple[Decl, Optional[int], int, int]] = []
        for r in self.k.execute(q, params):
            d = self._mk(r[:6])
            if no_aux and d.is_aux:
                continue
            if want_instance:
                ok_kind = (d.kind in db_kinds) or self.is_instance(d, src_root=src_root)
                if not ok_kind:
                    continue
            if pat_rx is not None:
                if search_module:
                    mod_str = d.module or ""
                    if not (
                        pat_rx.search(d.name)
                        or (mod_str and (pat_rx.search(mod_str) or pat_rx.search(f"{mod_str} {d.name}")))
                    ):
                        continue
                elif not pat_rx.search(d.name):
                    continue
            elif case_sensitive:
                if name_rx is not None:
                    mod_str = d.module or ""
                    if search_module:
                        if not (name_rx.match(d.name) or (mod_str and name_rx.match(mod_str))):
                            continue
                    elif not name_rx.match(d.name):
                        continue
                else:
                    if search_module:
                        if pattern not in d.name and pattern not in (d.module or ""):
                            continue
                    elif pattern not in d.name:
                        continue
            if mod_rx is not None and not mod_rx.search(d.module or ""):
                continue
            dom_sz = int(r[6]) if r[6] is not None else None
            out.append((d, dom_sz, int(r[7]), int(r[8])))
            if limit > 0 and len(out) >= limit:
                break
        return out

    def all_dom_subtree(self, decl_id: int) -> int:
        r = self.k.execute(
            "SELECT subtree_size FROM dom WHERE tree_id=? AND decl_id=?",
            (self._all_tree_id, decl_id),
        ).fetchone()
        return int(r[0]) if r else 0

    def decl_stats(self, d: int | str | Decl) -> dict:
        decl_obj = d if isinstance(d, Decl) else self.decl(d)
        r = self.k.execute(
            "SELECT kind, n_consts, type_nodes, value_nodes, fan_in, fan_out, "
            "fan_out_type, fan_out_value, flags, live_mask, stmt_mask, defcone_mask, attrs "
            "FROM decls WHERE id=?",
            (decl_obj.id,),
        ).fetchone()
        if r is None:
            raise KeyError(f"declaration not in kernel.db: {decl_obj.id}")
        return {
            "id": decl_obj.id,
            "name": decl_obj.name,
            "kind": r[0],
            "n_consts": int(r[1]),
            "type_nodes": int(r[2]),
            "value_nodes": int(r[3]),
            "fan_in": int(r[4]),
            "fan_out": int(r[5]),
            "fan_out_type": int(r[6]),
            "fan_out_value": int(r[7]),
            "flags": int(r[8]),
            "live_mask": int(r[9]),
            "stmt_mask": int(r[10]),
            "defcone_mask": int(r[11]),
            "attrs": int(r[12]),
            "module": decl_obj.module,
            "method": decl_obj.method,
            "all_dom_subtree": self.all_dom_subtree(decl_obj.id),
        }

    # ---- exact-case-first resolution & `--near` disambiguation --------
    def _ensure_stem_index(self) -> Optional[dict[str, list[tuple[int, str]]]]:
        """Lazily build an in-memory lowercased last-segment index when batching >= 3 suffix lookups."""
        self._suffix_scans += 1
        if self._stem_index is not None:
            return self._stem_index
        if self._suffix_scans < 3:
            return None
        idx: dict[str, list[tuple[int, str]]] = {}
        for did, name in self.k.execute("SELECT id, name FROM decls"):
            stem_lo = name.rsplit(".", 1)[-1].lower()
            idx.setdefault(stem_lo, []).append((int(did), name))
        self._stem_index = idx
        return idx

    def _matching_stem_decls(self, stem: str) -> list[Decl]:
        """Return all `Decl`s whose last dot-segment equals `stem` (case-insensitive), without truncation."""
        idx = self._ensure_stem_index()
        if idx is not None:
            pairs = idx.get(stem.lower(), ())
            return self.decls([did for did, _ in pairs])
        rows = self.k.execute(
            "SELECT id FROM decls WHERE name LIKE ? ESCAPE '!' OR LOWER(name) = LOWER(?)",
            (f"%.{_escape_like(stem)}", stem),
        ).fetchall()
        return self.decls([int(r[0]) for r in rows])

    def _near_context(self, near: Optional[str]) -> Optional[tuple[list[str], list[str], set[int]]]:
        if not near or not near.strip():
            return None
        key = near.strip()
        if key in self._near_cache:
            return self._near_cache[key]
        nd: Optional[Decl] = None
        try:
            nd, _ = self.resolve_unique(key, near=None)
        except ResolveError:
            nd = None
        if nd is not None:
            ns_parts = nd.name.split(".") if nd.kind == "inductive" else nd.name.split(".")[:-1]
            mod_parts = nd.module.split(".") if nd.module else []
            cone: set[int] = {nd.id}
            frontier = [nd.id]
            for _hop in range(2):
                if not frontier or len(cone) >= 2000:
                    break
                nxt: list[int] = []
                for _s, dst, _ek in self.iter_out_batch(frontier):
                    did = int(dst)
                    if did not in cone:
                        cone.add(did)
                        nxt.append(did)
                        if len(cone) >= 2000:
                            break
                frontier = nxt
        else:
            clean = key.removeprefix("_root_.")
            ns_parts = [p for p in clean.split(".") if p]
            mod_parts = list(ns_parts)
            cone = set()
        ctx = (ns_parts, mod_parts, cone)
        self._near_cache[key] = ctx
        return ctx

    def _near_score(self, d: Decl, ctx: Optional[tuple[list[str], list[str], set[int]]]) -> tuple[int, int, int]:
        if ctx is None:
            return (0, 0, 0)
        ns_parts, mod_parts, cone = ctx
        d_ns = d.name.split(".")[:-1]
        ns_pref = _common_prefix_len(d_ns, ns_parts)
        in_cone = 1 if d.id in cone else 0
        mod_pref = _common_prefix_len((d.module or "").split("."), mod_parts) if (d.module and mod_parts) else 0
        return (ns_pref, in_cone, mod_pref)

    def _pick_near_unique(self, cands: list[Decl], near: Optional[str]) -> Optional[Decl]:
        ctx = self._near_context(near)
        if ctx is None or len(cands) < 2:
            return None
        scored = [(self._near_score(c, ctx), c) for c in cands]
        scored.sort(key=lambda t: t[0], reverse=True)
        top_score, top_decl = scored[0]
        if top_score > (0, 0, 0) and top_score > scored[1][0]:
            return top_decl
        return None

    def resolve(self, query: str, limit: int = 10, *, near: Optional[str] = None) -> list[ResolveHit]:
        """Resolve an exact name, exact-case `.suffix`, exact-case unqualified stem, case-insensitive
        fallback, substring, or near-miss fuzzy stem.

        Order:
          0. exact FQN (exact case) -> `exact`
          1. exact-case `.suffix` -> `suffix`
          2. exact-case unqualified (`d.name == stem` when query had module/namespace prefix) -> `unqualified`
          3. case-insensitive FQN / `.suffix` / unqualified -> `case_fold`
          4. substring (only when 0..3 found no hits) -> `substring`
          5. fuzzy (only when 0..4 found no hits) -> `fuzzy`
        """
        q = query.strip()
        if not q:
            return []
        q_clean = q[7:] if q.startswith("_root_.") else q
        exact = self.maybe(q) or (self.maybe(q_clean) if q != q_clean else None)
        if exact is not None and near is None:
            return [ResolveHit(exact, self.all_dom_subtree(exact.id), "exact")]

        near_ctx = self._near_context(near)
        parts = [p for p in q_clean.split(".") if p]
        stem = parts[-1] if parts else q_clean
        tier_rank = {"exact": 0, "suffix": 1, "unqualified": 2, "case_fold": 3, "substring": 4, "fuzzy": 5}
        seen: dict[int, tuple[Decl, str]] = {}

        def add_cand(d: Decl, tag: str) -> None:
            prev = seen.get(d.id)
            if prev is None or tier_rank[tag] < tier_rank[prev[1]]:
                seen[d.id] = (d, tag)

        if exact is not None:
            add_cand(exact, "exact")

        # 1. Dot-stripping exact lookups
        for i in range(1, len(parts)):
            sub = ".".join(parts[i:])
            d = self.maybe(sub)
            if d is not None:
                tag = "unqualified" if ("." not in sub and len(parts) > 1) else "suffix"
                add_cand(d, tag)

        # 2. All stem matches (exact-case and case-insensitive, zero LIMIT truncation)
        for d in self._matching_stem_decls(stem):
            if d.name == q_clean:
                add_cand(d, "exact")
            elif d.name.endswith("." + q_clean) or d.name.endswith("." + stem):
                add_cand(d, "suffix")
            elif d.name == stem:
                add_cand(d, "unqualified" if "." in q_clean else "exact")
            elif (
                d.name.lower() == q_clean.lower()
                or d.name.lower().endswith("." + q_clean.lower())
                or d.name.lower().endswith("." + stem.lower())
                or d.name.lower() == stem.lower()
            ):
                add_cand(d, "case_fold")

        # 3. Substring LIKE matches ONLY when no exact/suffix/case_fold candidate exists
        sql_cap = max(limit * 10, 200)
        if not seen and len(stem) >= 3:
            q_sub = (
                "SELECT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id "
                "FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id "
                "WHERE d.name LIKE ? ESCAPE '!' "
                "ORDER BY length(d.name) ASC LIMIT ?"
            )
            for r in self.k.execute(q_sub, (f"%{_escape_like(stem)}%", sql_cap)):
                add_cand(self._mk(r), "substring")

        # 4. Fuzzy fallback (typos / near-miss stems) if still empty
        if not seen and len(stem) >= 4:
            mid = len(stem) // 2
            chunks = [stem[:mid], stem[mid:]]
            like_clauses = ["d.name LIKE ? ESCAPE '!'"] * len(chunks)
            params_fz: list = [self._all_tree_id] + [f"%{_escape_like(c)}%" for c in chunks]
            if len(parts) > 1:
                like_clauses.append("d.name LIKE ? ESCAPE '!'")
                params_fz.append(f"{_escape_like(parts[0])}.%")
            params_fz.append(500)
            q_fz = (
                "SELECT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id, "
                "COALESCE(dom.subtree_size, 0) AS sz "
                "FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id "
                "LEFT JOIN dom ON dom.tree_id = ? AND dom.decl_id = d.id "
                f"WHERE {' OR '.join(like_clauses)} "
                "ORDER BY sz DESC, length(d.name) ASC LIMIT ?"
            )
            stem_lo = stem.lower()
            for r in self.k.execute(q_fz, params_fz):
                d = self._mk(r[:6])
                d_stem = d.name.rsplit(".", 1)[-1].lower()
                if difflib.SequenceMatcher(None, stem_lo, d_stem).ratio() >= 0.55:
                    add_cand(d, "fuzzy")

        dom_map = self.all_dom_map(seen.keys())
        q_lo = q_clean.lower()
        stem_lo = stem.lower()

        def sort_key(item: tuple[Decl, str]) -> tuple:
            d, tag = item
            tier = tier_rank[tag]
            sz = dom_map.get(d.id, 0)
            n_ns, n_cone, n_mod = self._near_score(d, near_ctx)
            exact_query_suf = d.name == q_clean or d.name.endswith("." + q_clean)
            d_stem_lo = d.name.rsplit(".", 1)[-1].lower()
            sim = difflib.SequenceMatcher(None, stem_lo, d_stem_lo).ratio() if tier == 5 else 0.0
            common_pref = 0
            for a_seg, b_seg in zip(parts[:-1], d.name.split(".")[:-1]):
                if a_seg == b_seg:
                    common_pref += 2
                elif a_seg.lower() == b_seg.lower():
                    common_pref += 1
                else:
                    break
            return (
                tier,
                0 if exact_query_suf else 1,
                -n_ns,
                -n_cone,
                -n_mod,
                1 if d.is_aux else 0,
                -common_pref,
                -sz,
                -round(sim, 3),
                0 if q_lo in d.name.lower() else 1,
                len(d.name),
                d.name,
            )

        ranked = sorted(seen.values(), key=sort_key)
        return [ResolveHit(d, dom_map.get(d.id, 0), tag) for d, tag in ranked[:limit]]

    def _finalize_suffix_candidates(
        self,
        cands: list[Decl],
        query: str,
        resolved_from: str,
        match_tag: str,
        limit: int,
        near: Optional[str],
    ) -> tuple[Decl, str]:
        pub = [c for c in cands if not c.name.startswith("_private.")]
        work = pub or cands
        non_aux = [c for c in work if not c.is_aux]
        if non_aux:
            work = non_aux
        if len(work) == 1:
            return work[0], resolved_from
        picked = self._pick_near_unique(work, near)
        if picked is not None:
            return picked, resolved_from
        near_ctx = self._near_context(near)
        dom_map = self.all_dom_map(c.id for c in work)
        hits = [ResolveHit(c, dom_map.get(c.id, 0), match_tag) for c in work]
        hits.sort(
            key=lambda h: (
                tuple(-x for x in self._near_score(h.decl, near_ctx)),
                1 if h.decl.is_aux else 0,
                -h.all_dom,
                len(h.decl.name),
                h.decl.name,
            )
        )
        sample = ", ".join(h.decl.name for h in hits[:8])
        more = f" (+{len(work) - 8} more)" if len(work) > 8 else ""
        raise ResolveError(
            f"ambiguous declaration suffix {resolved_from!r} ({len(work)} matches): {sample}{more}",
            query,
            hits=hits[:limit],
            ambiguous=True,
        )

    def resolve_unique(
        self,
        query: str,
        limit: int = 10,
        *,
        near: Optional[str] = None,
    ) -> tuple[Decl, Optional[str]]:
        """Resolve a declaration uniquely with strict exact-case priority before case-folding:

          1. Exact FQN match (exact case, including `consts`, `_root_.` strip, and exact-case
             module-qualified `<Module>.<Decl>`).
          2. Exact-case `.suffix` match (`d.name.endswith('.' + q)`, then `consts`).
          3. Exact-case unqualified match (already checked in 1 for bare queries and module-qualified).
          4. Case-insensitive fallback (exact FQN case-fold -> module-qualified case-fold -> `.suffix` case-fold).

        When `near` (`--near <decl>`) is provided, multi-module suffix ties are broken by longest shared
        namespace prefix (then local cone / module prefix) with `<decl>`.
        """
        q = query.strip()
        if not q:
            raise ResolveError("empty declaration query", query, [])

        # 1. Exact FQN match (exact case)
        exact = self.maybe(q)
        if exact is not None:
            return exact, None
        q_clean = q[7:] if q.startswith("_root_.") else q
        if q != q_clean:
            stripped = self.maybe(q_clean)
            if stripped is not None:
                return stripped, q

        has_dm: Optional[bool] = None
        if "." in q_clean:
            has_dm = self.k.execute("SELECT 1 FROM decl_module LIMIT 1").fetchone() is not None
            if has_dm:
                parts = q_clean.split(".")
                for split_idx in range(len(parts) - 1, 0, -1):
                    mod_cand = ".".join(parts[:split_idx])
                    tail_cand = ".".join(parts[split_idx:])
                    rows = self.k.execute(
                        self._DECL_SQL +
                        "WHERE d.name = ? AND (m.module = ? OR m.module LIKE ? ESCAPE '!') "
                        "ORDER BY d.id LIMIT 20",
                        (tail_cand, mod_cand, f"%.{_escape_like(mod_cand)}"),
                    ).fetchall()
                    exact_mod = [
                        self._mk(r)
                        for r in rows
                        if r[3] and (r[3] == mod_cand or r[3].endswith("." + mod_cand))
                    ]
                    if len(exact_mod) == 1:
                        return exact_mod[0], q
                    if len(exact_mod) > 1:
                        return self._finalize_suffix_candidates(exact_mod, query, q, "unqualified", limit, near)

        # 2. Exact-case `.suffix` match (via stem index or covering SQLite scan, zero LIMIT truncation)
        stem = q_clean.rsplit(".", 1)[-1]
        all_stem_decls = self._matching_stem_decls(stem) if stem else []
        dot_q = "." + q_clean
        exact_suf = [c for c in all_stem_decls if c.name.endswith(dot_q)]
        if exact_suf:
            return self._finalize_suffix_candidates(exact_suf, query, q, "suffix", limit, near)

        c_exact_rows = self.k.execute(
            "SELECT DISTINCT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id "
            "FROM consts c JOIN decls d ON d.id = c.decl_id "
            "LEFT JOIN decl_module m ON m.decl_id = d.id "
            "WHERE c.name LIKE ? ESCAPE '!' AND substr(c.name, -(length(?) + 1)) = '.' || ? "
            "ORDER BY d.id LIMIT 50",
            (f"%.{_escape_like(q_clean)}", q_clean, q_clean),
        ).fetchall()
        if c_exact_rows:
            c_decls = [self._mk(r) for r in c_exact_rows]
            if len(c_decls) == 1:
                return c_decls[0], q
            picked = self._pick_near_unique(c_decls, near)
            if picked is not None:
                return picked, q

        # 4. Case-insensitive fallback (only when no exact-case match exists)
        q_lo = q_clean.lower()
        ci_exact = [c for c in all_stem_decls if c.name.lower() == q_lo]
        if ci_exact:
            return self._finalize_suffix_candidates(ci_exact, query, q, "case_fold", limit, near)

        if "." in q_clean and has_dm:
            parts = q_clean.split(".")
            for split_idx in range(len(parts) - 1, 0, -1):
                mod_cand = ".".join(parts[:split_idx])
                tail_cand = ".".join(parts[split_idx:])
                rows = self.k.execute(
                    self._DECL_SQL +
                    "WHERE LOWER(d.name) = LOWER(?) AND (LOWER(m.module) = LOWER(?) OR m.module LIKE ? ESCAPE '!') "
                    "ORDER BY d.id LIMIT 10",
                    (tail_cand, mod_cand, f"%.{_escape_like(mod_cand)}"),
                ).fetchall()
                if len(rows) == 1:
                    return self._mk(rows[0]), q

        dot_q_lo = "." + q_lo
        ci_suf = [c for c in all_stem_decls if c.name.lower().endswith(dot_q_lo)]
        if ci_suf:
            return self._finalize_suffix_candidates(ci_suf, query, q, "case_fold", limit, near)

        c_ci_rows = self.k.execute(
            "SELECT DISTINCT d.id, d.name, d.kind, m.module, COALESCE(m.method,'unmatched:none'), m.src_decl_id "
            "FROM consts c JOIN decls d ON d.id = c.decl_id "
            "LEFT JOIN decl_module m ON m.decl_id = d.id "
            "WHERE c.name LIKE ? ESCAPE '!' ORDER BY d.id LIMIT 20",
            (f"%.{_escape_like(q_clean)}",),
        ).fetchall()
        if len(c_ci_rows) == 1:
            return self._mk(c_ci_rows[0]), q

        hits = self.resolve(query, limit=limit, near=near)
        raise ResolveError(f"declaration not found in kernel.db: {query}", query, hits=hits, ambiguous=False)

    def find_source_decls(self, query: str, limit: int = 20) -> list[dict]:
        """Look up declarations in `leanre.db` by exact name, module-qualified name, or `.suffix`
        (exact-case preferred before case-insensitive fallback)."""
        if self.l is None:
            return []
        q = query.strip()
        if not q:
            return []
        sql_base = (
            "SELECT d.id, d.name, d.kind, d.module, d.line_no, d.signature_snippet, m.file_path "
            "FROM declarations d JOIN modules m ON m.name = d.module "
        )

        def _pack(rows) -> list[dict]:
            return [
                {
                    "id": int(r[0]),
                    "name": r[1],
                    "kind": r[2],
                    "module": r[3],
                    "line": int(r[4]),
                    "snippet": r[5],
                    "file": r[6],
                }
                for r in rows
            ]

        cand_q = q[7:] if q.startswith("_root_.") else q
        rows = self.l.execute(sql_base + "WHERE d.name = ? ORDER BY d.id LIMIT ?", (cand_q, limit)).fetchall()
        if rows:
            return _pack(rows)

        if "." in cand_q:
            parts = cand_q.split(".")
            for split_idx in range(len(parts) - 1, 0, -1):
                mod_cand = ".".join(parts[:split_idx])
                tail_cand = ".".join(parts[split_idx:])
                rows = self.l.execute(
                    sql_base + "WHERE d.name = ? AND (d.module = ? OR d.module LIKE ? ESCAPE '!') "
                    "ORDER BY d.id LIMIT ?",
                    (tail_cand, mod_cand, f"%.{_escape_like(mod_cand)}", limit),
                ).fetchall()
                if rows:
                    return _pack(rows)

        rows_exact = self.l.execute(
            sql_base +
            "WHERE d.name LIKE ? ESCAPE '!' AND substr(d.name, -(length(?) + 1)) = '.' || ? "
            "ORDER BY length(d.name), d.id LIMIT ?",
            (f"%.{_escape_like(cand_q)}", cand_q, cand_q, limit),
        ).fetchall()
        if rows_exact:
            return _pack(rows_exact)

        rows = self.l.execute(
            sql_base + "WHERE d.name LIKE ? ESCAPE '!' ORDER BY length(d.name), d.id LIMIT ?",
            (f"%.{_escape_like(cand_q)}", limit),
        ).fetchall()
        return _pack(rows)

    # ---- edges --------------------------------------------------------
    def deps(self, d: int | str | Decl, kinds: tuple[int, ...] = (TYPE, VALUE, BOTH)) -> list[tuple[Decl, int]]:
        i = d.id if isinstance(d, Decl) else self.decl(d).id
        rows = self.k.execute("SELECT dst, kind FROM edges WHERE src=?", (i,)).fetchall()
        rows = [(int(a), int(b)) for a, b in rows if int(b) in kinds]
        ds = {x.id: x for x in self.decls([a for a, _ in rows])}
        return [(ds[a], b) for a, b in rows if a in ds]

    def users(self, d: int | str | Decl, limit: int = 1000) -> list[tuple[Decl, int]]:
        i = d.id if isinstance(d, Decl) else self.decl(d).id
        if limit <= 0:
            rows = self.k.execute("SELECT src, kind FROM edges WHERE dst=?", (i,)).fetchall()
        else:
            rows = self.k.execute("SELECT src, kind FROM edges WHERE dst=? LIMIT ?", (i, limit)).fetchall()
        ds = {x.id: x for x in self.decls([int(a) for a, _ in rows])}
        return [(ds[int(a)], int(b)) for a, b in rows if int(a) in ds]

    def edge_kind(self, src: int, dst: int) -> Optional[int]:
        r = self.k.execute("SELECT kind FROM edges WHERE src=? AND dst=?", (src, dst)).fetchone()
        return int(r[0]) if r else None

    def iter_out_batch(self, ids: list[int]) -> Iterator[tuple[int, int, int]]:
        for chunk in _chunks(ids, 900):
            q = f"SELECT src, dst, kind FROM edges WHERE src IN ({','.join('?' * len(chunk))})"
            yield from self.k.execute(q, chunk)

    # ---- dominator tree -----------------------------------------------
    def dom(self, d: int | str | Decl) -> Optional[DomNode]:
        i = d.id if isinstance(d, Decl) else self.decl(d).id
        r = self.k.execute("SELECT decl_id, idom, depth, subtree_size FROM dom WHERE tree_id=? AND decl_id=?",
                           (self.tree_id, i)).fetchone()
        return DomNode(int(r[0]), r[1], int(r[2]), int(r[3])) if r else None

    def dom_children(self, d: int | str | Decl | None, limit: int = 50, min_size: int = 1) -> list[DomNode]:
        if d is None:
            q = ("SELECT decl_id, idom, depth, subtree_size FROM dom WHERE tree_id=? AND idom IS NULL "
                 "AND subtree_size>=? ORDER BY subtree_size DESC, decl_id LIMIT ?")
            args: tuple = (self.tree_id, min_size, limit)
        else:
            i = d.id if isinstance(d, Decl) else self.decl(d).id
            q = ("SELECT decl_id, idom, depth, subtree_size FROM dom WHERE tree_id=? AND idom=? "
                 "AND subtree_size>=? ORDER BY subtree_size DESC, decl_id LIMIT ?")
            args = (self.tree_id, i, min_size, limit)
        return [DomNode(int(a), b, int(c), int(e)) for a, b, c, e in self.k.execute(q, args)]

    def dom_child_stats(self, d: int | str | Decl) -> dict:
        i = d.id if isinstance(d, Decl) else self.decl(d).id
        n, s, singles = self.k.execute(
            "SELECT count(*), COALESCE(sum(subtree_size),0), COALESCE(sum(subtree_size=1),0) FROM dom "
            "WHERE tree_id=? AND idom=?", (self.tree_id, i)).fetchone()
        return {"children": int(n), "children_subtree_total": int(s), "leaf_children": int(singles)}

    def dom_below_count(self, d: int | str | Decl, min_size: int) -> int:
        i = d.id if isinstance(d, Decl) else self.decl(d).id
        r = self.k.execute(
            "SELECT count(*) FROM dom WHERE tree_id=? AND idom=? AND subtree_size<?",
            (self.tree_id, i, min_size),
        ).fetchone()
        return int(r[0]) if r else 0

    def ground_id_set(self, ids: Iterable[int]) -> set[int]:
        """Return the subset of `ids` whose `decl_module.method` is in `GROUND_METHODS`."""
        id_list = list(ids)
        if not id_list:
            return set()
        ph = ",".join("?" * len(GROUND_METHODS))
        if len(id_list) > 10_000:
            id_set = set(id_list)
            q = f"SELECT decl_id FROM decl_module WHERE method IN ({ph})"
            return {int(did) for (did,) in self.k.execute(q, GROUND_METHODS) if int(did) in id_set}
        out: set[int] = set()
        for chunk in _chunks(id_list, 900):
            iph = ",".join("?" * len(chunk))
            q = f"SELECT decl_id FROM decl_module WHERE decl_id IN ({iph}) AND method IN ({ph})"
            for (did,) in self.k.execute(q, [*chunk, *GROUND_METHODS]):
                out.add(int(did))
        return out

    def dom_path(self, d: int | str | Decl) -> list[DomNode]:
        """idom chain from `d` up to the virtual root (d first)."""
        out: list[DomNode] = []
        node = self.dom(d)
        while node is not None:
            out.append(node)
            node = self.dom(int(node.idom)) if node.idom is not None else None
        return out

    def roots(self) -> list[tuple[int, str, int, str]]:
        return [(int(a), b, int(c), e) for a, b, c, e in self.k.execute("SELECT id,name,decl_id,grp FROM roots ORDER BY id")]

    # ---- source anchors -----------------------------------------------
    def src_row(self, d: Decl) -> Optional[dict]:
        """Phase 2 leanre.db row (module file + line + 1-line signature snippet) for a kernel decl."""
        if self.l is None or d.src_decl_id is None or not d.method.startswith(("leanre_db", "aux_prefix:leanre_db")):
            return None
        r = self.l.execute(
            "SELECT d.name, d.kind, d.module, d.line_no, d.signature_snippet, d.horn_requires_json, d.horn_proves, m.file_path "
            "FROM declarations d JOIN modules m ON m.name = d.module WHERE d.id=?", (d.src_decl_id,)).fetchone()
        if r is None:
            return None
        return {"name": r[0], "kind": r[1], "module": r[2], "line": int(r[3]), "snippet": r[4],
                "horn_requires": r[5], "horn_proves": r[6], "file": r[7]}

    def module_file(self, module: str) -> Optional[str]:
        if self.l is not None:
            r = self.l.execute("SELECT file_path FROM modules WHERE name=?", (module,)).fetchone()
            if r:
                return r[0]
        return module.replace(".", "/") + ".lean"


def resolve_leanre_db_path(kernel_db: str, leanre_db: Optional[str]) -> Optional[str]:
    """Return explicit `leanre_db` if provided; otherwise auto-detect `leanre.db` beside `kernel_db`."""
    if leanre_db is not None:
        return leanre_db
    kabs = os.path.abspath(kernel_db)
    kdir = os.path.dirname(kabs)
    beside = os.path.join(kdir, "leanre.db")
    if os.path.exists(beside):
        return beside
    if os.path.basename(kdir) == "kernel":
        parent = os.path.join(os.path.dirname(kdir), "leanre.db")
        if os.path.exists(parent):
            return parent
    if kabs == os.path.abspath(DEFAULT_KERNEL_DB) and os.path.exists(DEFAULT_LEANRE_DB):
        return DEFAULT_LEANRE_DB
    return None


def _chunks(xs: Iterable, n: int) -> Iterator[list]:
    buf = list(xs)
    for i in range(0, len(buf), n):
        yield buf[i:i + n]
