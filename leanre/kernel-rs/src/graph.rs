//! Declaration graph: CSR adjacency, per-root reachability, dominator trees
//! (Cooper–Harvey–Kennedy over reverse post-order) and the brute-force
//! node-removal oracle used to cross-check them.

use crate::walk::DeclEdges;
use rayon::prelude::*;

pub const NONE: u32 = u32::MAX;
pub const E_TYPE: u8 = 1;
pub const E_VALUE: u8 = 2;

pub struct Graph {
    pub n: usize,
    pub foff: Vec<usize>,
    pub fdst: Vec<u32>,
    pub fkind: Vec<u8>,
    pub roff: Vec<usize>,
    pub rsrc: Vec<u32>,
    pub rkind: Vec<u8>,
    /// edges whose target does not precede the source in export order (0 => export order is topological)
    pub forward_refs: u64,
    pub n_type_only: u64,
    pub n_value_only: u64,
    pub n_both: u64,
}

impl Graph {
    pub fn build(edges: &[DeclEdges]) -> Graph {
        let n = edges.len();
        let mut foff = Vec::with_capacity(n + 1);
        let mut fdst = Vec::new();
        let mut fkind = Vec::new();
        let (mut fr, mut nt, mut nv, mut nb) = (0u64, 0u64, 0u64, 0u64);
        foff.push(0);
        for (u, e) in edges.iter().enumerate() {
            let (t, v) = (&e.trefs, &e.vrefs);
            let (mut i, mut j) = (0, 0);
            while i < t.len() || j < v.len() {
                let (d, k) = if j >= v.len() || (i < t.len() && t[i] < v[j]) {
                    i += 1;
                    (t[i - 1], E_TYPE)
                } else if i >= t.len() || v[j] < t[i] {
                    j += 1;
                    (v[j - 1], E_VALUE)
                } else {
                    i += 1;
                    j += 1;
                    (t[i - 1], E_TYPE | E_VALUE)
                };
                match k {
                    E_TYPE => nt += 1,
                    E_VALUE => nv += 1,
                    _ => nb += 1,
                }
                if d as usize >= u {
                    fr += 1;
                }
                fdst.push(d);
                fkind.push(k);
            }
            foff.push(fdst.len());
        }
        let mut roff = vec![0usize; n + 1];
        for &d in &fdst {
            roff[d as usize + 1] += 1;
        }
        for i in 0..n {
            roff[i + 1] += roff[i];
        }
        let mut cur = roff.clone();
        let mut rsrc = vec![0u32; fdst.len()];
        let mut rkind = vec![0u8; fdst.len()];
        for u in 0..n {
            for x in foff[u]..foff[u + 1] {
                let d = fdst[x] as usize;
                rsrc[cur[d]] = u as u32;
                rkind[cur[d]] = fkind[x];
                cur[d] += 1;
            }
        }
        Graph { n, foff, fdst, fkind, roff, rsrc, rkind, forward_refs: fr, n_type_only: nt, n_value_only: nv, n_both: nb }
    }

    #[inline]
    pub fn n_edges(&self) -> usize {
        self.fdst.len()
    }
    #[inline]
    pub fn fan_in(&self, v: usize) -> usize {
        self.roff[v + 1] - self.roff[v]
    }
    #[inline]
    pub fn fan_out(&self, v: usize) -> usize {
        self.foff[v + 1] - self.foff[v]
    }
    #[allow(dead_code)]
    pub fn edge_kind(&self, u: u32, v: u32) -> Option<u8> {
        let (s, e) = (self.foff[u as usize], self.foff[u as usize + 1]);
        self.fdst[s..e].binary_search(&v).ok().map(|p| self.fkind[s + p])
    }
}

/// `blocked[u]` (statement view): u's value-only edges are removed, i.e. only
/// u's TYPE is followed. `None` = proof view (all edges).
#[inline]
fn ok(blocked: Option<&[bool]>, u: usize, k: u8) -> bool {
    match blocked {
        None => true,
        Some(b) => k & E_TYPE != 0 || !b[u],
    }
}

/// Multi-source BFS (FIFO, neighbours in ascending id). Returns (depth, parent); -1 / NONE if unreachable.
pub fn bfs(g: &Graph, blocked: Option<&[bool]>, roots: &[u32]) -> (Vec<i32>, Vec<u32>) {
    let mut depth = vec![-1i32; g.n];
    let mut parent = vec![NONE; g.n];
    let mut q: Vec<u32> = Vec::new();
    for &r in roots {
        if depth[r as usize] < 0 {
            depth[r as usize] = 0;
            q.push(r);
        }
    }
    let mut h = 0;
    while h < q.len() {
        let u = q[h] as usize;
        h += 1;
        let du = depth[u] + 1;
        for x in g.foff[u]..g.foff[u + 1] {
            if !ok(blocked, u, g.fkind[x]) {
                continue;
            }
            let w = g.fdst[x] as usize;
            if depth[w] < 0 {
                depth[w] = du;
                parent[w] = u as u32;
                q.push(w as u32);
            }
        }
    }
    (depth, parent)
}

/// Phase 2 "pure definition cone": from the roots' statements, follow edges only
/// into non-theorem declarations and only out of roots / non-theorem declarations.
pub fn defcone(g: &Graph, blocked: Option<&[bool]>, roots: &[u32], is_thm: &[bool]) -> Vec<bool> {
    let mut seen = vec![false; g.n];
    let mut q: Vec<u32> = Vec::new();
    for &r in roots {
        if !seen[r as usize] {
            seen[r as usize] = true;
            q.push(r);
        }
    }
    let mut h = 0;
    while h < q.len() {
        let u = q[h] as usize;
        h += 1;
        for x in g.foff[u]..g.foff[u + 1] {
            let w = g.fdst[x] as usize;
            if !ok(blocked, u, g.fkind[x]) || is_thm[w] || seen[w] {
                continue;
            }
            seen[w] = true;
            q.push(w as u32);
        }
    }
    seen
}

pub struct Dom {
    /// index n = virtual root. idom[v] == NONE: unreachable; == n: child of the virtual root.
    pub idom: Vec<u32>,
    /// roots have depth 0
    pub depth: Vec<u32>,
    /// dominator-subtree size including the node itself (0 if unreachable)
    pub size: Vec<u32>,
    pub n_reach: usize,
    pub passes: u32,
    pub rpo: Vec<u32>,
}

/// Cooper–Harvey–Kennedy "A Simple, Fast Dominance Algorithm" from a virtual
/// root whose successors are `roots`. Exact on arbitrary digraphs (iterates to a
/// fixpoint; a DAG converges in the first pass and the second pass confirms).
pub fn dominators(g: &Graph, blocked: Option<&[bool]>, roots: &[u32]) -> Dom {
    let n = g.n;
    let vroot = n as u32;
    let mut is_root = vec![false; n];
    for &r in roots {
        is_root[r as usize] = true;
    }
    // iterative DFS post-order from the virtual root
    let mut state = vec![0u8; n];
    let mut post: Vec<u32> = Vec::new();
    let mut stack: Vec<(u32, usize)> = Vec::new();
    for &r in roots {
        if state[r as usize] != 0 {
            continue;
        }
        state[r as usize] = 1;
        stack.push((r, g.foff[r as usize]));
        while let Some(top) = stack.last_mut() {
            let u = top.0 as usize;
            if top.1 < g.foff[u + 1] {
                let x = top.1;
                top.1 += 1;
                if !ok(blocked, u, g.fkind[x]) {
                    continue;
                }
                let w = g.fdst[x];
                if state[w as usize] == 0 {
                    state[w as usize] = 1;
                    stack.push((w, g.foff[w as usize]));
                }
            } else {
                post.push(top.0);
                stack.pop();
            }
        }
    }
    let mut rpo: Vec<u32> = Vec::with_capacity(post.len() + 1);
    rpo.push(vroot);
    rpo.extend(post.iter().rev());
    let mut num = vec![NONE; n + 1];
    for (i, &v) in rpo.iter().enumerate() {
        num[v as usize] = i as u32;
    }
    let mut idom = vec![NONE; n + 1];
    idom[n] = vroot;
    let mut passes = 0;
    loop {
        passes += 1;
        let mut changed = false;
        for &v in &rpo[1..] {
            let vi = v as usize;
            let mut nd = if is_root[vi] { vroot } else { NONE };
            for x in g.roff[vi]..g.roff[vi + 1] {
                let p = g.rsrc[x];
                if idom[p as usize] == NONE || !ok(blocked, p as usize, g.rkind[x]) {
                    continue;
                }
                if nd == NONE {
                    nd = p;
                } else {
                    let (mut a, mut b) = (p, nd);
                    while a != b {
                        while num[a as usize] > num[b as usize] {
                            a = idom[a as usize];
                        }
                        while num[b as usize] > num[a as usize] {
                            b = idom[b as usize];
                        }
                    }
                    nd = a;
                }
            }
            if idom[vi] != nd {
                idom[vi] = nd;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut size = vec![0u32; n + 1];
    for &v in rpo.iter().rev() {
        let vi = v as usize;
        size[vi] += 1;
        if v != vroot {
            let p = idom[vi] as usize;
            size[p] += size[vi];
        }
    }
    let mut depth = vec![0u32; n + 1];
    for &v in &rpo[1..] {
        let p = idom[v as usize];
        depth[v as usize] = if p == vroot { 0 } else { depth[p as usize] + 1 };
    }
    Dom { idom, depth, size, n_reach: rpo.len() - 1, passes, rpo }
}

fn splitmix(x: &mut u64) -> u64 {
    *x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *x;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Deterministic sample: the `k_top` largest dominator subtrees plus `k_random`
/// distinct reachable nodes drawn with a fixed-seed generator.
pub fn pick_samples(dom: &Dom, k_random: usize, k_top: usize, seed: u64) -> Vec<u32> {
    let mut reach: Vec<u32> = dom.rpo[1..].to_vec();
    reach.sort_unstable();
    let mut by_size = reach.clone();
    by_size.sort_by(|&a, &b| dom.size[b as usize].cmp(&dom.size[a as usize]).then(a.cmp(&b)));
    let mut out: Vec<u32> = by_size.iter().take(k_top).copied().collect();
    let mut s = seed;
    let m = reach.len();
    for i in 0..k_random.min(m) {
        let j = i + (splitmix(&mut s) % (m - i) as u64) as usize;
        reach.swap(i, j);
        out.push(reach[i]);
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// Brute-force oracle. For each sampled node d: delete d, recompute plain
/// reachability from the roots, and require that the set of nodes that became
/// unreachable is exactly d's dominator subtree. Returns (node, mismatching nodes).
pub fn oracle(g: &Graph, blocked: Option<&[bool]>, roots: &[u32], dom: &Dom, samples: &[u32]) -> Vec<(u32, u64)> {
    let n = g.n;
    // Euler intervals of the dominator tree
    let mut coff = vec![0usize; n + 2];
    for v in 0..n {
        if dom.idom[v] != NONE {
            coff[dom.idom[v] as usize + 1] += 1;
        }
    }
    for i in 0..=n {
        coff[i + 1] += coff[i];
    }
    let mut cur = coff.clone();
    let mut child = vec![0u32; coff[n + 1]];
    for v in 0..n {
        if dom.idom[v] != NONE {
            let p = dom.idom[v] as usize;
            child[cur[p]] = v as u32;
            cur[p] += 1;
        }
    }
    let mut tin = vec![0u32; n + 1];
    let mut tout = vec![0u32; n + 1];
    let mut t = 0u32;
    let mut st: Vec<(u32, usize)> = vec![(n as u32, coff[n])];
    while let Some(top) = st.last_mut() {
        let u = top.0 as usize;
        if top.1 == coff[u] {
            tin[u] = t;
            t += 1;
        }
        if top.1 < coff[u + 1] {
            let c = child[top.1];
            top.1 += 1;
            st.push((c, coff[c as usize]));
        } else {
            tout[u] = t;
            st.pop();
        }
    }
    samples
        .par_iter()
        .map(|&d| {
            let mut seen = vec![false; n];
            let mut q: Vec<u32> = Vec::new();
            for &r in roots {
                if r != d && !seen[r as usize] {
                    seen[r as usize] = true;
                    q.push(r);
                }
            }
            let mut h = 0;
            while h < q.len() {
                let u = q[h] as usize;
                h += 1;
                for x in g.foff[u]..g.foff[u + 1] {
                    let w = g.fdst[x];
                    if w == d || seen[w as usize] || !ok(blocked, u, g.fkind[x]) {
                        continue;
                    }
                    seen[w as usize] = true;
                    q.push(w);
                }
            }
            let di = d as usize;
            let mut bad = 0u64;
            for v in 0..n {
                let expect_unreached = if dom.idom[v] == NONE { true } else { tin[di] <= tin[v] && tout[v] <= tout[di] };
                if expect_unreached == seen[v] {
                    bad += 1;
                }
            }
            (d, bad)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn graph_from(n: usize, es: &[(u32, u32, u8)]) -> Graph {
        let mut de = vec![DeclEdges::default(); n];
        for &(u, v, k) in es {
            if k & E_TYPE != 0 {
                de[u as usize].trefs.push(v);
            }
            if k & E_VALUE != 0 {
                de[u as usize].vrefs.push(v);
            }
        }
        for d in &mut de {
            d.trefs.sort_unstable();
            d.trefs.dedup();
            d.vrefs.sort_unstable();
            d.vrefs.dedup();
        }
        Graph::build(&de)
    }

    /// Independent textbook definition: dom(v) = nodes on every root->v path, via set intersection to a fixpoint.
    fn naive_idom(g: &Graph, blocked: Option<&[bool]>, roots: &[u32]) -> Vec<u32> {
        let n = g.n;
        let (depth, _) = bfs(g, blocked, roots);
        let full: Vec<bool> = vec![true; n + 1];
        let mut dom: Vec<Vec<bool>> = (0..n).map(|_| full.clone()).collect();
        let mut changed = true;
        while changed {
            changed = false;
            for v in 0..n {
                if depth[v] < 0 {
                    continue;
                }
                let mut nd = full.clone();
                if roots.contains(&(v as u32)) {
                    nd = vec![false; n + 1];
                    nd[n] = true;
                }
                for x in g.roff[v]..g.roff[v + 1] {
                    let p = g.rsrc[x] as usize;
                    if depth[p] < 0 || !ok(blocked, p, g.rkind[x]) {
                        continue;
                    }
                    for i in 0..=n {
                        nd[i] = nd[i] && dom[p][i];
                    }
                }
                nd[v] = true;
                if nd != dom[v] {
                    dom[v] = nd;
                    changed = true;
                }
            }
        }
        // idom(v) = the strict dominator with the largest dominator set
        (0..n)
            .map(|v| {
                if depth[v] < 0 {
                    return NONE;
                }
                let mut best = n as u32;
                let mut best_cnt = 0;
                for d in 0..n {
                    if d != v && dom[v][d] {
                        let c = dom[d].iter().filter(|&&x| x).count();
                        if c > best_cnt {
                            best_cnt = c;
                            best = d as u32;
                        }
                    }
                }
                best
            })
            .collect()
    }

    #[test]
    fn dominators_match_naive_and_oracle_on_random_graphs() {
        let mut s = 7u64;
        for case in 0..300 {
            let n = 2 + (splitmix(&mut s) % 40) as usize;
            let m = (splitmix(&mut s) % (3 * n as u64 + 1)) as usize;
            let dag = case % 3 != 0;
            let mut es = Vec::new();
            for _ in 0..m {
                let u = (splitmix(&mut s) % n as u64) as u32;
                let v = (splitmix(&mut s) % n as u64) as u32;
                if u == v || (dag && v > u) {
                    continue;
                }
                es.push((u, v, 1 + (splitmix(&mut s) % 3) as u8));
            }
            let g = graph_from(n, &es);
            let nroots = 1 + (splitmix(&mut s) % 3) as usize;
            let mut roots: Vec<u32> = (0..nroots).map(|_| (splitmix(&mut s) % n as u64) as u32).collect();
            roots.sort_unstable();
            roots.dedup();
            let mut blocked = vec![false; n];
            for &r in &roots {
                blocked[r as usize] = true;
            }
            for view in [None, Some(&blocked[..])] {
                let d = dominators(&g, view, &roots);
                let want = naive_idom(&g, view, &roots);
                assert_eq!(&d.idom[..n], &want[..], "case {case}");
                let all: Vec<u32> = (0..n as u32).filter(|&v| d.idom[v as usize] != NONE).collect();
                let res = oracle(&g, view, &roots, &d, &all);
                assert!(res.iter().all(|&(_, bad)| bad == 0), "oracle case {case}: {res:?}");
                let (depth, _) = bfs(&g, view, &roots);
                assert_eq!(d.n_reach, depth.iter().filter(|&&x| x >= 0).count());
                let tot: u32 = roots.iter().filter(|&&r| d.idom[r as usize] == n as u32).map(|&r| d.size[r as usize]).sum();
                let top: u32 = (0..n).filter(|&v| d.idom[v] == n as u32).map(|v| d.size[v]).sum();
                assert_eq!(top as usize, d.n_reach);
                assert!(tot as usize <= d.n_reach);
            }
        }
    }

    #[test]
    fn oracle_detects_a_wrong_tree() {
        // 0 -> 1 -> 3, 0 -> 2 -> 3 : idom(3) = 0. Corrupt it to 1 and the oracle must object.
        let g = graph_from(4, &[(0, 1, 1), (0, 2, 1), (1, 3, 1), (2, 3, 1)]);
        // ids here are not export-ordered; the algorithm must not care
        let mut d = dominators(&g, None, &[0]);
        assert_eq!(&d.idom[..4], &[4, 0, 0, 0]);
        assert_eq!(g.forward_refs, 4);
        assert!(oracle(&g, None, &[0], &d, &[0, 1, 2, 3]).iter().all(|x| x.1 == 0));
        d.idom[3] = 1;
        assert!(oracle(&g, None, &[0], &d, &[1]).iter().any(|x| x.1 > 0));
    }

    #[test]
    fn statement_view_drops_root_value_edges() {
        // root 3: type -> 1, value -> 2 ; 2 -> 0 ; 1 -> 0
        let g = graph_from(4, &[(3, 1, 1), (3, 2, 2), (2, 0, 3), (1, 0, 2)]);
        let blocked = vec![false, false, false, true];
        let (dp, _) = bfs(&g, None, &[3]);
        assert_eq!(dp, vec![2, 1, 1, 0]);
        let (ds, par) = bfs(&g, Some(&blocked), &[3]);
        assert_eq!(ds, vec![2, 1, -1, 0]);
        assert_eq!(par[0], 1);
        assert_eq!(g.edge_kind(3, 2), Some(2));
        assert_eq!(g.edge_kind(3, 0), None);
        assert_eq!((g.n_type_only, g.n_value_only, g.n_both), (1, 2, 1));
    }
}
