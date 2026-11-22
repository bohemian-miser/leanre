#!/usr/bin/env python3
"""Iterative graph algorithms for large Lean proof DAGs (175k+ modules, 50k+ TCB decls)."""
from __future__ import annotations

import collections
from typing import Dict, List, Optional, Sequence, Tuple


def bfs_shortest_paths(
    roots: Sequence[int], adj: Sequence[Sequence[int]], n: int
) -> Tuple[List[int], List[int]]:
    """Multi-source BFS from `roots`.
    Returns (dist, parent) where dist[v] = min hops from roots (-1 unreachable)
    and parent[v] = predecessor toward roots (-1 for roots/unreachable).
    """
    dist = [-1] * n
    parent = [-1] * n
    q: collections.deque[int] = collections.deque()
    for r in roots:
        if 0 <= r < n and dist[r] == -1:
            dist[r] = 0
            q.append(r)
    while q:
        u = q.popleft()
        du = dist[u] + 1
        for w in adj[u]:
            if dist[w] == -1:
                dist[w] = du
                parent[w] = u
                q.append(w)
    return dist, parent


def reconstruct_path_to_root(
    node: int, parent: Sequence[int], max_hops: int = 10000
) -> List[int]:
    """Return [node, ..., root] by walking BFS parent pointers."""
    path: List[int] = []
    cur = node
    seen = set()
    while cur != -1 and cur not in seen and len(path) < max_hops:
        path.append(cur)
        seen.add(cur)
        cur = parent[cur]
    return path


def rpo_from(root: int, adj: Sequence[Sequence[int]], n: int) -> List[int]:
    """Iterative Reverse Post-Order from `root` (topological order on DAGs)."""
    seen = bytearray(n)
    seen[root] = 1
    post: List[int] = []
    stack: List[int] = [root]
    its = [iter(adj[root])]
    while stack:
        for w in its[-1]:
            if not seen[w]:
                seen[w] = 1
                stack.append(w)
                its.append(iter(adj[w]))
                break
        else:
            post.append(stack.pop())
            its.pop()
    post.reverse()
    return post


def dominators_chk(
    root: int,
    adj: Sequence[Sequence[int]],
    radj: Sequence[Sequence[int]],
    n: int,
    weights: Optional[Sequence[int]] = None,
) -> Tuple[List[int], List[int], List[int], List[int], Dict[int, List[int]]]:
    """Cooper-Harvey-Kennedy iterative dominators from `root`.
    Returns (idom, rpo, subtree_size, subtree_weight, children_map).
    - idom[root] = root; idom[v] = -1 if unreachable from root.
    - subtree_size[v] includes self (so strictly dominated count = subtree_size[v] - 1).
    """
    rpo = rpo_from(root, adj, n)
    num = [-1] * n
    for i, v in enumerate(rpo):
        num[v] = i
    idom = [-1] * n
    idom[root] = root

    changed = True
    while changed:
        changed = False
        for v in rpo:
            if v == root:
                continue
            new_dom = -1
            for p in radj[v]:
                if idom[p] == -1:
                    continue
                if new_dom == -1:
                    new_dom = p
                else:
                    a, b = p, new_dom
                    while a != b:
                        while num[a] > num[b]:
                            a = idom[a]
                        while num[b] > num[a]:
                            b = idom[b]
                    new_dom = a
            if idom[v] != new_dom:
                idom[v] = new_dom
                changed = True

    sub_size = [0] * n
    sub_weight = [0] * n
    children: Dict[int, List[int]] = {}
    for v in rpo:
        sub_size[v] = 1
        sub_weight[v] = weights[v] if weights is not None else 1
    for v in reversed(rpo):
        if v == root:
            continue
        p = idom[v]
        if p != -1:
            sub_size[p] += sub_size[v]
            sub_weight[p] += sub_weight[v]
            children.setdefault(p, []).append(v)
    return idom, rpo, sub_size, sub_weight, children


def bottom_depths_dag(adj: Sequence[Sequence[int]], n: int) -> List[int]:
    """Longest path length from each node down to a 0-out-degree leaf.
    Matches drew2apps `depth`: 0 if no outgoing project imports, else 1 + max(depth[child]).
    Iterative Kahn's algorithm on reversed edges (leaves -> importers).
    """
    out_deg = [len(adj[v]) for v in range(n)]
    radj: List[List[int]] = [[] for _ in range(n)]
    for u in range(n):
        for w in adj[u]:
            radj[w].append(u)
    depth = [0] * n
    q: collections.deque[int] = collections.deque()
    for v in range(n):
        if out_deg[v] == 0:
            q.append(v)
    while q:
        v = q.popleft()
        dv = depth[v] + 1
        for u in radj[v]:
            if dv > depth[u]:
                depth[u] = dv
            out_deg[u] -= 1
            if out_deg[u] == 0:
                q.append(u)
    return depth


def topological_order_kahn(adj: Sequence[Sequence[int]], n: int) -> List[int]:
    """Topological order where u precedes w for every edge u -> w (best-effort if cyclic)."""
    in_deg = [0] * n
    for u in range(n):
        for w in adj[u]:
            in_deg[w] += 1
    q: collections.deque[int] = collections.deque(v for v in range(n) if in_deg[v] == 0)
    order: List[int] = []
    while q:
        u = q.popleft()
        order.append(u)
        for w in adj[u]:
            in_deg[w] -= 1
            if in_deg[w] == 0:
                q.append(w)
    if len(order) < n:
        seen = set(order)
        for v in range(n):
            if v not in seen:
                order.append(v)
    return order


def compute_rev_reach_exact(
    adj: Sequence[Sequence[int]], n: int, batch_size: int = 4096
) -> List[int]:
    """Exact reverse reachability count using Python native arbitrary-precision int bitsets.
    rev_reach[v] = exact number of OTHER nodes u that can reach v along directed edges u -> ... -> v.
    For import graphs (src imports dst), rev_reach[dst] = number of modules transitively importing dst!
    """
    topo = topological_order_kahn(adj, n)
    rev_reach = [0] * n
    for start in range(0, n, batch_size):
        end = min(n, start + batch_size)
        mask = [0] * n
        for idx in range(start, end):
            mask[idx] = 1 << (idx - start)
        for u in topo:
            m = mask[u]
            if m:
                for w in adj[u]:
                    mask[w] |= m
        for v in range(n):
            m = mask[v]
            if m:
                # Python 3.9 compatible popcount (int.bit_count added in 3.10)
                rev_reach[v] += bin(m).count("1")
    # Subtract self (each node had its own bit set in its own batch)
    return [max(0, c - 1) for c in rev_reach]
