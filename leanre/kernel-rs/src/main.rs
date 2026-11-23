//! leanre-kernel: kernel-exact declaration graph extractor for lean4export
//! NDJSON (format 3.1.0). See docs/KERNEL.md for the output schema.

mod graph;
mod json;
mod parse;
mod reader;
mod sighash;
mod store;
mod walk;

use graph::{Dom, Graph};
use parse::*;
use rayon::prelude::*;
use serde_json::json;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::time::Instant;
use store::Store;

const SCHEMA_VERSION: u32 = 1;
const DEFAULT_ROOTS: [(&str, &str); 5] = [
    ("riemannHypothesis", "RH"),
    ("riemannZeta_eq_zero_re", "RH"),
    ("LFunction_ne_zero_of_half_lt_re", "GRH"),
    ("LFunction_eq_zero_re", "GRH"),
    ("LFunction_eq_zero_re_of_isPrimitive", "GRH"),
];

struct Args {
    input: String,
    out_dir: String,
    threads: usize,
    parse_threads: usize,
    roots: Vec<(String, String)>,
    rh_defaults: bool,
    no_default_roots: bool,
    oracle_random: usize,
    oracle_top: usize,
    force_slow: bool,
    lexicon: Option<String>,
}

fn usage() -> ! {
    eprintln!(
        "usage: leanre-kernel extract --input <export.ndjson[.zst]> --out-dir <dir>\n         [--threads N] [--parse-threads N] [--root NAME[:GROUP]]... [--rh-defaults | --no-default-roots]\n         [--oracle-random N] [--oracle-top N] [--local-lexicon FILE] [--force-slow-parser]"
    );
    std::process::exit(2)
}

fn parse_args_from(av: &[String]) -> Result<Args, String> {
    if av.len() < 2 || av[1] != "extract" {
        return Err("missing `extract` subcommand".into());
    }
    let mut a = Args {
        input: String::new(),
        out_dir: String::new(),
        threads: 32,
        parse_threads: 0,
        roots: vec![],
        rh_defaults: false,
        no_default_roots: false,
        oracle_random: 1000,
        oracle_top: 50,
        force_slow: false,
        lexicon: None,
    };
    let mut i = 2;
    let next_val = |i: &mut usize, flag: &str| -> Result<String, String> {
        *i += 1;
        av.get(*i).cloned().ok_or_else(|| format!("missing value for {flag}"))
    };
    while i < av.len() {
        match av[i].as_str() {
            "--input" => a.input = next_val(&mut i, "--input")?,
            "--out-dir" => a.out_dir = next_val(&mut i, "--out-dir")?,
            "--threads" => a.threads = next_val(&mut i, "--threads")?.parse().map_err(|_| "invalid --threads".to_string())?,
            "--parse-threads" => a.parse_threads = next_val(&mut i, "--parse-threads")?.parse().map_err(|_| "invalid --parse-threads".to_string())?,
            "--oracle-random" => a.oracle_random = next_val(&mut i, "--oracle-random")?.parse().map_err(|_| "invalid --oracle-random".to_string())?,
            "--oracle-top" => a.oracle_top = next_val(&mut i, "--oracle-top")?.parse().map_err(|_| "invalid --oracle-top".to_string())?,
            "--local-lexicon" => a.lexicon = Some(next_val(&mut i, "--local-lexicon")?),
            "--force-slow-parser" => a.force_slow = true,
            "--rh-defaults" => a.rh_defaults = true,
            "--no-default-roots" => a.no_default_roots = true,
            "--root" => {
                let v = next_val(&mut i, "--root")?;
                let (n, g) = match v.split_once(':') {
                    Some((n, g)) => (n.to_string(), g.to_string()),
                    None => (v.clone(), "ROOT".to_string()),
                };
                a.roots.push((n, g));
            }
            other => return Err(format!("unknown argument: {other}")),
        }
        i += 1;
    }
    if a.input.is_empty() || a.out_dir.is_empty() {
        return Err("both --input and --out-dir are required".into());
    }
    if a.rh_defaults && a.no_default_roots {
        return Err("--rh-defaults and --no-default-roots are mutually exclusive".into());
    }
    a.threads = a.threads.clamp(1, 64);
    if a.parse_threads == 0 {
        a.parse_threads = a.threads;
    }
    if a.roots.is_empty() && a.rh_defaults {
        a.roots = DEFAULT_ROOTS.iter().map(|(n, g)| (n.to_string(), g.to_string())).collect();
    }
    if a.roots.len() > 30 {
        return Err("at most 30 roots".into());
    }
    Ok(a)
}

fn parse_args() -> Args {
    let av: Vec<String> = std::env::args().collect();
    match parse_args_from(&av) {
        Ok(a) => a,
        Err(msg) => {
            eprintln!("error: {msg}");
            usage();
        }
    }
}

/// Resolve effective roots:
/// - Explicit `--root` values are used verbatim (never augmented with RH defaults).
/// - `--no-default-roots` keeps roots empty.
/// - `--rh-defaults` selects the 5 RH/GRH headline roots.
/// - Otherwise (legacy fallback with no flags): apply RH defaults only when all
///   5 RH roots exist in the export; generic exports proceed with 0 roots.
fn resolve_roots<F>(args: &Args, has_decl: F) -> Vec<(String, String)>
where
    F: Fn(&str) -> bool,
{
    if !args.roots.is_empty() {
        return args.roots.clone();
    }
    if args.no_default_roots {
        return Vec::new();
    }
    if args.rh_defaults || DEFAULT_ROOTS.iter().all(|(n, _)| has_decl(n)) {
        return DEFAULT_ROOTS.iter().map(|(n, g)| (n.to_string(), g.to_string())).collect();
    }
    Vec::new()
}

fn peak_rss_kib() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM:")).and_then(|l| l.split_whitespace().nth(1).and_then(|x| x.parse().ok())))
        .unwrap_or(0)
}

struct Hasher {
    h: Sha256,
    buf: Vec<u8>,
}
impl Hasher {
    fn new() -> Self {
        Hasher { h: Sha256::new(), buf: Vec::with_capacity(1 << 16) }
    }
    fn put(&mut self, b: &[u8]) {
        self.buf.extend_from_slice(b);
        if self.buf.len() >= (1 << 16) - 256 {
            self.h.update(&self.buf);
            self.buf.clear();
        }
    }
    fn u32(&mut self, x: u32) {
        self.put(&x.to_le_bytes());
    }
    fn i64(&mut self, x: i64) {
        self.put(&x.to_le_bytes());
    }
    fn s(&mut self, x: &str) {
        self.u32(x.len() as u32);
        self.put(x.as_bytes());
    }
    fn fin(mut self) -> String {
        self.h.update(&self.buf);
        reader::hex(&self.h.finalize())
    }
}

struct TreeSpec {
    label: String,
    view: &'static str,
    roots: Vec<usize>,
}

fn main() {
    if let Err(e) = real_main() {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}

fn real_main() -> Result<(), String> {
    let args = parse_args();
    let t0 = Instant::now();
    let mut timings: Vec<(String, f64)> = Vec::new();
    std::fs::create_dir_all(&args.out_dir).map_err(|e| format!("mkdir {}: {e}", args.out_dir))?;
    rayon::ThreadPoolBuilder::new().num_threads(args.threads).build_global().map_err(|e| e.to_string())?;

    // ---- 1. streaming parse -------------------------------------------------
    let mut store = Store::new();
    let mut last = Instant::now();
    let info = reader::run(&args.input, args.parse_threads, args.force_slow, |pc| {
        store.apply(pc)?;
        if last.elapsed().as_secs() >= 20 {
            last = Instant::now();
            eprintln!("[parse] {:>6.1}s lines={} exprs={} decls={} rss={:.1}GiB", t0.elapsed().as_secs_f64(), store.lines, store.tag.len(), store.decls.len(), peak_rss_kib() as f64 / 1048576.0);
        }
        Ok(())
    })?;
    store.finish()?;
    timings.push(("parse_s".into(), t0.elapsed().as_secs_f64()));
    eprintln!("[parse] done {:.1}s: {} lines, {} expr ids, {} names, {} levels, {} declaration records", t0.elapsed().as_secs_f64(), store.lines, store.tag.len(), store.n_kind.len(), store.l_kind.len(), store.decls.len());
    let undefined_expr = store.tag.iter().filter(|&&t| t == K_UNDEF).count() as u64;

    // ---- 2. constant names --------------------------------------------------
    let t = Instant::now();
    let nd = store.decls.len();
    let mut coff: Vec<usize> = Vec::with_capacity(nd + 1);
    let mut cname: Vec<String> = Vec::new();
    let mut cdecl: Vec<u32> = Vec::new();
    coff.push(0);
    for (di, d) in store.decls.iter().enumerate() {
        for c in &d.consts {
            cname.push(store.name_string(c.name));
            cdecl.push(di as u32);
        }
        coff.push(cname.len());
    }
    let mut by_name: HashMap<&str, u32> = HashMap::with_capacity(cname.len());
    let mut dup_names: Vec<String> = Vec::new();
    for (ci, n) in cname.iter().enumerate() {
        if by_name.insert(n.as_str(), ci as u32).is_some() {
            dup_names.push(n.clone());
        }
    }
    if !dup_names.is_empty() {
        return Err(format!("{} constant names collide after dotted rendering, e.g. {:?}", dup_names.len(), &dup_names[..dup_names.len().min(5)]));
    }
    let name_id_of = |n: &str| -> u32 {
        match by_name.get(n) {
            Some(&ci) => {
                let di = cdecl[ci as usize] as usize;
                store.decls[di].consts[ci as usize - coff[di]].name
            }
            None => u32::MAX - 1,
        }
    };
    let decl_of = |n: &str| -> Option<u32> { by_name.get(n).map(|&ci| cdecl[ci as usize]) };
    let markers = walk::Markers { eq_refl: name_id_of("Eq.refl"), bool_ty: name_id_of("Bool"), bool_true: name_id_of("Bool.true"), of_decide_eq_true: name_id_of("of_decide_eq_true") };
    timings.push(("names_s".into(), t.elapsed().as_secs_f64()));

    // ---- 3. exact type / value dependency edges ----------------------------
    let t = Instant::now();
    let mut edges = walk::extract_edges(&store, &markers);
    let dangling: u64 = edges.iter().map(|e| e.dangling as u64).sum();
    let mark = |names: &[&str]| -> Vec<u32> { names.iter().filter_map(|n| decl_of(n)).collect() };
    let m_rb = mark(&["Lean.ofReduceBool", "Lean.reduceBool"]);
    let m_rn = mark(&["Lean.ofReduceNat", "Lean.reduceNat"]);
    let m_sorry = mark(&["sorryAx"]);
    let m_tc = mark(&["Lean.trustCompiler"]);
    edges.par_iter_mut().for_each(|e| {
        let has = |ms: &[u32]| ms.iter().any(|m| e.trefs.binary_search(m).is_ok() || e.vrefs.binary_search(m).is_ok());
        if has(&m_rb) {
            e.flags |= walk::F_REDUCE_BOOL;
        }
        if has(&m_rn) {
            e.flags |= walk::F_REDUCE_NAT;
        }
        if has(&m_sorry) {
            e.flags |= walk::F_SORRY;
        }
        if has(&m_tc) {
            e.flags |= walk::F_TRUST_COMPILER;
        }
    });
    let g = Graph::build(&edges);
    timings.push(("edges_s".into(), t.elapsed().as_secs_f64()));
    eprintln!("[edges] {:.1}s: {} edges (type-only {}, value-only {}, both {}), forward refs {}, dangling const refs {}", t.elapsed().as_secs_f64(), g.n_edges(), g.n_type_only, g.n_value_only, g.n_both, g.forward_refs, dangling);

    // ---- 4. signature hashes (docs/SIGHASH.md) ------------------------------
    let t = Instant::now();
    let sig = sighash::compute_all(&store, &cname, &coff, args.lexicon.as_deref())?;
    timings.push(("sighash_s".into(), t.elapsed().as_secs_f64()));
    let store_bytes = store.mem_bytes();
    let expr_ids = store.tag.len();
    let name_ids = store.n_kind.len();
    let level_ids = store.l_kind.len();
    store.drop_expr_tables();
    eprintln!("[sighash] {:.1}s ({} constants); released {:.2} GiB expr tables", t.elapsed().as_secs_f64(), cname.len(), store_bytes as f64 / 1073741824.0);

    // ---- 5. roots, live/dead, statement cones ------------------------------
    let t = Instant::now();
    let eff_roots = resolve_roots(&args, |n| decl_of(n).is_some());
    if eff_roots.is_empty() && !args.no_default_roots {
        eprintln!("[roots] no --root specified and RH defaults absent; proceeding with 0 roots (pass --root NAME[:GROUP] or --no-default-roots)");
    }
    let mut root_idx: Vec<u32> = Vec::new();
    for (n, _) in &eff_roots {
        let di = decl_of(n).ok_or_else(|| format!("root `{n}` is not declared in this export"))?;
        if cname[coff[di as usize]] != *n {
            return Err(format!("root `{n}` is not the primary constant of its record"));
        }
        root_idx.push(di);
    }
    let nr = root_idx.len();
    let mut blocked = vec![false; nd];
    for &r in &root_idx {
        blocked[r as usize] = true;
    }
    let is_thm: Vec<bool> = store.decls.iter().map(|d| d.kind == D_THM).collect();
    let per_root: Vec<_> = root_idx
        .par_iter()
        .map(|&r| {
            let p = graph::bfs(&g, None, &[r]);
            let s = graph::bfs(&g, Some(&blocked), &[r]);
            let dc = graph::defcone(&g, Some(&blocked), &[r], &is_thm);
            (p, s, dc)
        })
        .collect();
    let mut live_mask = vec![0u32; nd];
    let mut stmt_mask = vec![0u32; nd];
    let mut defcone_mask = vec![0u32; nd];
    for (r, (p, s, dc)) in per_root.iter().enumerate() {
        for v in 0..nd {
            if p.0[v] >= 0 {
                live_mask[v] |= 1 << r;
            }
            if s.0[v] >= 0 {
                stmt_mask[v] |= 1 << r;
            }
            if dc[v] && v as u32 != root_idx[r] {
                defcone_mask[v] |= 1 << r;
            }
        }
    }
    timings.push(("reach_s".into(), t.elapsed().as_secs_f64()));

    // ---- 6. dominator trees + brute-force oracle ---------------------------
    let t = Instant::now();
    let mut specs: Vec<TreeSpec> = vec![TreeSpec { label: "ALL".into(), view: "proof", roots: (0..nr).collect() }];
    for r in 0..nr {
        specs.push(TreeSpec { label: format!("ROOT:{}", eff_roots[r].0), view: "proof", roots: vec![r] });
    }
    specs.push(TreeSpec { label: "STMT_ALL".into(), view: "stmt", roots: (0..nr).collect() });
    let doms: Vec<Dom> = specs
        .par_iter()
        .map(|sp| {
            let rs: Vec<u32> = sp.roots.iter().map(|&r| root_idx[r]).collect();
            graph::dominators(&g, if sp.view == "stmt" { Some(&blocked) } else { None }, &rs)
        })
        .collect();
    timings.push(("dominators_s".into(), t.elapsed().as_secs_f64()));
    let t = Instant::now();
    let mut oracle_json = Vec::new();
    let mut oracle_fail_total = 0u64;
    for (ti, sp) in specs.iter().enumerate() {
        let rs: Vec<u32> = sp.roots.iter().map(|&r| root_idx[r]).collect();
        let view = if sp.view == "stmt" { Some(&blocked[..]) } else { None };
        let samples = graph::pick_samples(&doms[ti], args.oracle_random, args.oracle_top, 0x5EED_0000 + ti as u64);
        let res = graph::oracle(&g, view, &rs, &doms[ti], &samples);
        let failed: Vec<_> = res.iter().filter(|x| x.1 > 0).map(|x| json!({"decl_id": x.0, "name": cname[coff[x.0 as usize]], "mismatched_nodes": x.1})).collect();
        eprintln!("[oracle] tree {} ({}): {} samples checked, {} failed ({:.1}s elapsed)", ti, sp.label, samples.len(), failed.len(), t.elapsed().as_secs_f64());
        oracle_fail_total += failed.len() as u64;
        oracle_json.push(json!({"tree_id": ti, "label": sp.label, "samples_checked": samples.len(), "top_k": args.oracle_top, "random_k": args.oracle_random, "seed": format!("0x{:X}", 0x5EED_0000u64 + ti as u64), "failed": failed.len(), "failures": failed.into_iter().take(20).collect::<Vec<_>>(), "chk_passes": doms[ti].passes}));
    }
    timings.push(("oracle_s".into(), t.elapsed().as_secs_f64()));
    eprintln!("[dom] {} trees, oracle failures: {}", specs.len(), oracle_fail_total);

    // ---- 7. SQLite ----------------------------------------------------------
    let t = Instant::now();
    let db_path = format!("{}/kernel.db", args.out_dir);
    for suffix in ["", "-journal", "-wal", "-shm"] {
        let _ = std::fs::remove_file(format!("{db_path}{suffix}"));
    }
    let mut hashes = serde_json::Map::new();
    let export_meta: serde_json::Value = store.meta.as_deref().and_then(|m| serde_json::from_str(m).ok()).unwrap_or(json!(null));
    let mut kind_counts = [0u64; 6];
    let (mut n_types, mut n_ctors, mut n_recs, mut n_mutual, mut n_unsafe, mut n_partial, mut n_all_gt1) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    for d in &store.decls {
        kind_counts[d.kind as usize] += 1;
        n_types += d.n_types as u64;
        n_ctors += d.n_ctors as u64;
        n_recs += d.n_recs as u64;
        if d.n_types > 1 {
            n_mutual += 1;
        }
        if d.attrs & ATTR_UNSAFE != 0 {
            n_unsafe += 1;
        }
        if d.attrs & ATTR_PARTIAL != 0 {
            n_partial += 1;
        }
        if d.n_all > 1 {
            n_all_gt1 += 1;
        }
    }
    let n_const = cname.len() as u64;
    {
        let mut conn = rusqlite::Connection::open(&db_path).map_err(|e| e.to_string())?;
        conn.execute_batch(
            "PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF; PRAGMA locking_mode=EXCLUSIVE; PRAGMA cache_size=-2000000; PRAGMA temp_store=MEMORY;
             CREATE TABLE meta(key TEXT PRIMARY KEY, value_json TEXT NOT NULL);
             CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL, n_consts INTEGER NOT NULL,
               type_nodes INTEGER NOT NULL, value_nodes INTEGER NOT NULL, fan_in INTEGER NOT NULL, fan_out INTEGER NOT NULL,
               fan_out_type INTEGER NOT NULL, fan_out_value INTEGER NOT NULL, flags INTEGER NOT NULL,
               live_mask INTEGER NOT NULL, stmt_mask INTEGER NOT NULL, defcone_mask INTEGER NOT NULL, attrs INTEGER NOT NULL,
               sighash TEXT, sighash_anon TEXT);
             CREATE TABLE consts(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, ckind TEXT NOT NULL, ord INTEGER NOT NULL,
               sighash TEXT, sighash_anon TEXT, sig_size INTEGER, n_local INTEGER);
             CREATE TABLE edges(src INTEGER NOT NULL, dst INTEGER NOT NULL, kind INTEGER NOT NULL, PRIMARY KEY(src,dst)) WITHOUT ROWID;
             CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT NOT NULL, decl_id INTEGER NOT NULL, grp TEXT NOT NULL);
             CREATE TABLE reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, depth INTEGER NOT NULL, parent INTEGER, PRIMARY KEY(root_id,decl_id)) WITHOUT ROWID;
             CREATE TABLE stmt_reach(root_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, depth INTEGER NOT NULL, parent INTEGER, PRIMARY KEY(root_id,decl_id)) WITHOUT ROWID;
             CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT NOT NULL, view TEXT NOT NULL, root_ids TEXT NOT NULL, n_nodes INTEGER NOT NULL);
             CREATE TABLE dom(tree_id INTEGER NOT NULL, decl_id INTEGER NOT NULL, idom INTEGER, depth INTEGER NOT NULL, subtree_size INTEGER NOT NULL, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
             CREATE VIEW axioms AS SELECT * FROM decls WHERE kind='axiom';",
        )
        .map_err(|e| e.to_string())?;
        let tx = conn.transaction().map_err(|e| e.to_string())?;
        {
            let e2s = |e: rusqlite::Error| e.to_string();
            let mut h = Hasher::new();
            let mut st = tx.prepare("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)").map_err(e2s)?;
            for (di, d) in store.decls.iter().enumerate() {
                let e = &edges[di];
                let c0 = coff[di];
                st.execute(rusqlite::params![di as i64, cname[c0], DECL_KIND_NAMES[d.kind as usize], d.consts.len() as i64, e.tnodes as i64, e.vnodes as i64, g.fan_in(di) as i64, g.fan_out(di) as i64, e.trefs.len() as i64, e.vrefs.len() as i64, e.flags, live_mask[di], stmt_mask[di], defcone_mask[di], d.attrs, sig.named(c0), sig.anon(c0)]).map_err(e2s)?;
                h.u32(di as u32);
                h.s(&cname[c0]);
                h.put(&[d.kind, d.attrs]);
                h.u32(d.consts.len() as u32);
                h.i64(e.tnodes as i64);
                h.i64(e.vnodes as i64);
                h.u32(e.flags);
                h.u32(live_mask[di]);
                h.u32(stmt_mask[di]);
                h.u32(defcone_mask[di]);
            }
            hashes.insert("decls".into(), json!(h.fin()));
            drop(st);
            let mut h = Hasher::new();
            let mut st = tx.prepare("INSERT INTO consts VALUES (?,?,?,?,?,?,?,?,?)").map_err(e2s)?;
            for (di, d) in store.decls.iter().enumerate() {
                for (k, c) in d.consts.iter().enumerate() {
                    let ci = coff[di] + k;
                    st.execute(rusqlite::params![ci as i64, cname[ci], di as i64, CONST_KIND_NAMES[c.ckind as usize], k as i64, sig.named(ci), sig.anon(ci), sig.size(ci), sig.n_local(ci)]).map_err(e2s)?;
                    h.s(&cname[ci]);
                    h.u32(di as u32);
                    h.put(&[c.ckind]);
                    h.s(sig.named(ci).as_deref().unwrap_or(""));
                    h.s(sig.anon(ci).as_deref().unwrap_or(""));
                }
            }
            hashes.insert("consts".into(), json!(h.fin()));
            drop(st);
            let mut h = Hasher::new();
            let mut st = tx.prepare("INSERT INTO edges VALUES (?,?,?)").map_err(e2s)?;
            for u in 0..nd {
                for x in g.foff[u]..g.foff[u + 1] {
                    st.execute(rusqlite::params![u as i64, g.fdst[x], g.fkind[x]]).map_err(e2s)?;
                    h.u32(u as u32);
                    h.u32(g.fdst[x]);
                    h.put(&[g.fkind[x]]);
                }
            }
            hashes.insert("edges".into(), json!(h.fin()));
            drop(st);
            let mut st = tx.prepare("INSERT INTO roots VALUES (?,?,?,?)").map_err(e2s)?;
            for (r, (n, grp)) in eff_roots.iter().enumerate() {
                st.execute(rusqlite::params![r as i64, n, root_idx[r], grp]).map_err(e2s)?;
            }
            drop(st);
            for (tbl, pick) in [("reach", 0usize), ("stmt_reach", 1usize)] {
                let mut h = Hasher::new();
                let mut st = tx.prepare(&format!("INSERT INTO {tbl} VALUES (?,?,?,?)")).map_err(e2s)?;
                for (r, pr) in per_root.iter().enumerate() {
                    let (depth, parent) = if pick == 0 { &pr.0 } else { &pr.1 };
                    for v in 0..nd {
                        if depth[v] >= 0 {
                            let par: Option<u32> = if parent[v] == graph::NONE { None } else { Some(parent[v]) };
                            st.execute(rusqlite::params![r as i64, v as i64, depth[v], par]).map_err(e2s)?;
                            h.u32(r as u32);
                            h.u32(v as u32);
                            h.u32(depth[v] as u32);
                            h.u32(parent[v]);
                        }
                    }
                }
                hashes.insert(tbl.into(), json!(h.fin()));
            }
            let mut h = Hasher::new();
            let mut st = tx.prepare("INSERT INTO dom VALUES (?,?,?,?,?)").map_err(e2s)?;
            let mut st2 = tx.prepare("INSERT INTO dom_trees VALUES (?,?,?,?,?)").map_err(e2s)?;
            for (ti, sp) in specs.iter().enumerate() {
                let d = &doms[ti];
                st2.execute(rusqlite::params![ti as i64, sp.label, sp.view, sp.roots.iter().map(|r| r.to_string()).collect::<Vec<_>>().join(","), d.n_reach as i64]).map_err(e2s)?;
                for v in 0..nd {
                    if d.idom[v] != graph::NONE {
                        let id: Option<u32> = if d.idom[v] as usize == nd { None } else { Some(d.idom[v]) };
                        st.execute(rusqlite::params![ti as i64, v as i64, id, d.depth[v], d.size[v]]).map_err(e2s)?;
                        h.u32(ti as u32);
                        h.u32(v as u32);
                        h.u32(d.idom[v]);
                        h.u32(d.depth[v]);
                        h.u32(d.size[v]);
                    }
                }
            }
            hashes.insert("dom".into(), json!(h.fin()));
            drop(st);
            drop(st2);
            let mut st = tx.prepare("INSERT INTO meta VALUES (?,?)").map_err(e2s)?;
            let metas = vec![
                ("schema_version", json!(SCHEMA_VERSION)),
                ("export_meta", export_meta.clone()),
                ("input", json!({"file_name": std::path::Path::new(&info.path).file_name().map(|x| x.to_string_lossy().to_string()), "file_bytes": info.file_bytes, "file_sha256": info.file_sha256, "is_zstd": info.is_zstd, "uncompressed_bytes": info.uncompressed_bytes, "uncompressed_sha256": info.uncompressed_sha256})),
                ("counts", json!({"ndjson_lines": store.lines, "declaration_records": nd, "constants": n_const, "edges": g.n_edges(), "expr_ids": expr_ids})),
                ("sighash", sig.meta()),
                ("content_hashes", serde_json::Value::Object(hashes.clone())),
            ];
            for (k, v) in metas {
                st.execute(rusqlite::params![k, v.to_string()]).map_err(e2s)?;
            }
        }
        tx.commit().map_err(|e| e.to_string())?;
        conn.execute_batch(
            "CREATE UNIQUE INDEX decls_name ON decls(name);
             CREATE UNIQUE INDEX consts_name ON consts(name);
             CREATE INDEX consts_decl ON consts(decl_id);
             CREATE INDEX consts_sighash ON consts(sighash);
             CREATE INDEX consts_sighash_anon ON consts(sighash_anon);
             CREATE INDEX edges_dst ON edges(dst, src);
             CREATE INDEX dom_idom ON dom(tree_id, idom, subtree_size DESC, decl_id);
             CREATE INDEX dom_top ON dom(tree_id, subtree_size DESC, decl_id);
             ANALYZE;",
        )
        .map_err(|e| e.to_string())?;
    }
    timings.push(("sqlite_s".into(), t.elapsed().as_secs_f64()));

    // ---- 8. summary ---------------------------------------------------------
    let t = Instant::now();
    let db_sha = {
        use std::io::Read;
        let mut f = std::fs::File::open(&db_path).map_err(|e| e.to_string())?;
        let mut h = Sha256::new();
        let mut buf = vec![0u8; 1 << 20];
        loop {
            let n = f.read(&mut buf).map_err(|e| e.to_string())?;
            if n == 0 {
                break;
            }
            h.update(&buf[..n]);
        }
        reader::hex(&h.finalize())
    };
    timings.push(("db_hash_s".into(), t.elapsed().as_secs_f64()));
    let cnt = |f: &dyn Fn(usize) -> bool| (0..nd).filter(|&v| f(v)).count();
    let grp_mask = |gname: &str| -> u32 { eff_roots.iter().enumerate().filter(|(_, (_, gr))| gr == gname).map(|(r, _)| 1u32 << r).sum() };
    let mut groups: Vec<String> = eff_roots.iter().map(|(_, g)| g.clone()).collect();
    groups.sort();
    groups.dedup();
    let root_json: Vec<_> = (0..nr)
        .map(|r| {
            let b = 1u32 << r;
            json!({"id": r, "name": eff_roots[r].0, "group": eff_roots[r].1, "decl_id": root_idx[r],
                "live": cnt(&|v| live_mask[v] & b != 0), "dead": cnt(&|v| live_mask[v] & b == 0),
                "live_only_this_root": cnt(&|v| live_mask[v] == b),
                "stmt_cone": cnt(&|v| stmt_mask[v] & b != 0), "defcone": cnt(&|v| defcone_mask[v] & b != 0),
                "max_depth": per_root[r].0 .0.iter().copied().max().unwrap_or(-1)})
        })
        .collect();
    let group_json: Vec<_> = groups
        .iter()
        .map(|gname| {
            let m = grp_mask(gname);
            json!({"group": gname, "mask": m, "live_union": cnt(&|v| live_mask[v] & m != 0), "live_intersection": cnt(&|v| live_mask[v] & m == m),
                "stmt_union": cnt(&|v| stmt_mask[v] & m != 0), "defcone_union": cnt(&|v| defcone_mask[v] & m != 0),
                "live_exclusive": cnt(&|v| live_mask[v] != 0 && live_mask[v] & !m == 0)})
        })
        .collect();
    let all_mask: u32 = if nr == 0 { 0 } else { (1u32 << nr) - 1 };
    let dead: Vec<usize> = (0..nd).filter(|&v| live_mask[v] == 0).collect();
    let mut dead_kind = [0u64; 6];
    for &v in &dead {
        dead_kind[store.decls[v].kind as usize] += 1;
    }
    let kinds_json = |arr: &[u64; 6]| -> serde_json::Value { json!(DECL_KIND_NAMES.iter().zip(arr.iter()).map(|(k, v)| (k.to_string(), json!(v))).collect::<serde_json::Map<_, _>>()) };
    let axioms: Vec<_> = (0..nd)
        .filter(|&v| store.decls[v].kind == D_AXIOM)
        .map(|v| json!({"decl_id": v, "name": cname[coff[v]], "fan_in": g.fan_in(v), "live_mask": live_mask[v], "stmt_mask": stmt_mask[v]}))
        .collect();
    let named = |n: &str| -> serde_json::Value {
        match decl_of(n) {
            None => json!({"name": n, "present": false}),
            Some(d) => {
                let v = d as usize;
                let users: Vec<_> = (g.roff[v]..g.roff[v + 1]).take(50).map(|x| json!({"name": cname[coff[g.rsrc[x] as usize]], "edge_kind": g.rkind[x]})).collect();
                json!({"name": n, "present": true, "decl_id": d, "kind": DECL_KIND_NAMES[store.decls[v].kind as usize], "fan_in": g.fan_in(v), "live_mask": live_mask[v], "stmt_mask": stmt_mask[v], "direct_users_first50": users})
            }
        }
    };
    let flag_counts: Vec<_> = [(walk::F_REFL_TRUE, "refl_true"), (walk::F_OF_DECIDE, "of_decide_eq_true_refl"), (walk::F_REDUCE_BOOL, "reduceBool"), (walk::F_REDUCE_NAT, "reduceNat"), (walk::F_SORRY, "sorryAx"), (walk::F_TRUST_COMPILER, "trustCompiler")]
        .iter()
        .map(|&(b, n)| json!({"flag": b, "name": n, "decls": cnt(&|v| edges[v].flags & b != 0), "live_decls": cnt(&|v| edges[v].flags & b != 0 && live_mask[v] != 0)}))
        .collect();
    let trees_json: Vec<_> = specs
        .iter()
        .enumerate()
        .map(|(ti, sp)| {
            let d = &doms[ti];
            let mut order: Vec<u32> = (0..nd as u32).filter(|&v| d.idom[v as usize] != graph::NONE).collect();
            order.sort_by(|&a, &b| d.size[b as usize].cmp(&d.size[a as usize]).then(a.cmp(&b)));
            let top: Vec<_> = order
                .iter()
                .take(50)
                .map(|&v| {
                    let vi = v as usize;
                    let p = d.idom[vi] as usize;
                    json!({"decl_id": v, "name": cname[coff[vi]], "kind": DECL_KIND_NAMES[store.decls[vi].kind as usize], "subtree_size": d.size[vi], "depth": d.depth[vi], "idom": if p == nd { serde_json::Value::Null } else { json!(cname[coff[p]]) }})
                })
                .collect();
            json!({"id": ti, "label": sp.label, "view": sp.view, "root_ids": sp.roots, "n_nodes": d.n_reach, "max_depth": order.iter().map(|&v| d.depth[v as usize]).max().unwrap_or(0), "top50": top})
        })
        .collect();
    timings.push(("total_s".into(), t0.elapsed().as_secs_f64()));
    let stats = json!({
        "tool": {"name": "leanre-kernel", "version": env!("CARGO_PKG_VERSION"), "schema_version": SCHEMA_VERSION, "threads": args.threads, "parse_threads": args.parse_threads},
        "input": {"path": info.path, "file_bytes": info.file_bytes, "file_sha256": info.file_sha256, "is_zstd": info.is_zstd, "uncompressed_bytes": info.uncompressed_bytes, "uncompressed_sha256": info.uncompressed_sha256},
        "export_meta": export_meta,
        "stream": {"ndjson_lines": store.lines, "serde_path_lines": store.slow_lines, "chunks": info.chunks, "expr_lines": store.expr_lines, "expr_ids": expr_ids, "name_lines": store.name_lines, "name_ids": name_ids, "level_lines": store.level_lines, "level_ids": level_ids,
            "expr_kind_lines": {"bvar": store.expr_kind_counts[0], "sort": store.expr_kind_counts[1], "const": store.expr_kind_counts[2], "app": store.expr_kind_counts[3], "lam": store.expr_kind_counts[4], "forallE": store.expr_kind_counts[5], "letE": store.expr_kind_counts[6], "proj": store.expr_kind_counts[7], "natVal": store.expr_kind_counts[8], "strVal": store.expr_kind_counts[9], "mdata": store.expr_kind_counts[10]},
            "anomalies": {"undefined_expr_ids": undefined_expr, "duplicate_expr_ids": store.dup_expr, "duplicate_name_ids": store.dup_name, "duplicate_level_ids": store.dup_level, "duplicate_constant_names": store.dup_const, "dangling_constant_refs": dangling, "edges_not_in_export_order": g.forward_refs}},
        "declarations": {"records": nd, "by_kind": kinds_json(&kind_counts),
            "inductive": {"records": kind_counts[D_INDUCTIVE as usize], "types": n_types, "ctors": n_ctors, "recs": n_recs, "mutual_blocks": n_mutual},
            "constants_unpacked": n_const, "unsafe_records": n_unsafe, "partial_records": n_partial, "records_in_mutual_all_group": n_all_gt1},
        "edges": {"total": g.n_edges(), "type_only": g.n_type_only, "value_only": g.n_value_only, "both": g.n_both},
        "roots": root_json, "groups": group_json,
        "union": {"mask": all_mask, "live": cnt(&|v| live_mask[v] != 0), "dead": dead.len(), "live_all_roots": if nr == 0 { 0 } else { cnt(&|v| live_mask[v] == all_mask) }, "stmt_cone": cnt(&|v| stmt_mask[v] != 0), "defcone": cnt(&|v| defcone_mask[v] != 0),
            "dead_by_kind": kinds_json(&dead_kind), "dead_names_first200": dead.iter().take(200).map(|&v| cname[coff[v]].clone()).collect::<Vec<_>>()},
        "axioms": axioms,
        "special": {"sorryAx": named("sorryAx"), "Lean.ofReduceBool": named("Lean.ofReduceBool"), "Lean.reduceBool": named("Lean.reduceBool"), "Lean.ofReduceNat": named("Lean.ofReduceNat"), "Lean.reduceNat": named("Lean.reduceNat"), "Lean.trustCompiler": named("Lean.trustCompiler"), "of_decide_eq_true": named("of_decide_eq_true")},
        "kernel_pattern_flags": flag_counts,
        "dominators": {"algorithm": "Cooper-Harvey-Kennedy (RPO fixpoint) from a virtual root", "trees": trees_json, "oracle": oracle_json, "oracle_failures_total": oracle_fail_total},
        "sighash": sig.meta(),
        "content_hashes": serde_json::Value::Object(hashes),
        "kernel_db_sha256": db_sha,
        "run": {"timings": timings.iter().map(|(k, v)| (k.clone(), json!((v * 100.0).round() / 100.0))).collect::<serde_json::Map<_, _>>(), "peak_rss_kib": peak_rss_kib(), "store_bytes": store_bytes},
    });
    let stats_path = format!("{}/run_stats.json", args.out_dir);
    std::fs::write(&stats_path, serde_json::to_string_pretty(&stats).unwrap() + "\n").map_err(|e| e.to_string())?;
    eprintln!("[done] {:.1}s total, peak RSS {:.2} GiB -> {} , {}", t0.elapsed().as_secs_f64(), peak_rss_kib() as f64 / 1048576.0, db_path, stats_path);
    if oracle_fail_total > 0 {
        return Err("dominator oracle reported mismatches".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sv(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn explicit_root_never_injects_rh_defaults() {
        let a = parse_args_from(&sv(&[
            "leanre-kernel",
            "extract",
            "--input",
            "in.ndjson",
            "--out-dir",
            "out",
            "--root",
            "MyPkg.mainThm:MAIN",
        ]))
        .unwrap();
        let roots = resolve_roots(&a, |_| true);
        assert_eq!(roots, vec![("MyPkg.mainThm".to_string(), "MAIN".to_string())]);
    }

    #[test]
    fn no_default_roots_keeps_roots_empty() {
        let a = parse_args_from(&sv(&[
            "leanre-kernel",
            "extract",
            "--input",
            "in.ndjson",
            "--out-dir",
            "out",
            "--no-default-roots",
        ]))
        .unwrap();
        assert!(a.no_default_roots);
        assert!(resolve_roots(&a, |_| true).is_empty());
    }

    #[test]
    fn rh_defaults_flag_selects_five_rh_roots() {
        let a = parse_args_from(&sv(&[
            "leanre-kernel",
            "extract",
            "--input",
            "in.ndjson",
            "--out-dir",
            "out",
            "--rh-defaults",
        ]))
        .unwrap();
        let roots = resolve_roots(&a, |_| false);
        assert_eq!(roots.len(), 5);
        assert_eq!(roots[0], ("riemannHypothesis".to_string(), "RH".to_string()));
    }

    #[test]
    fn generic_export_without_flags_does_not_inject_missing_rh_roots() {
        let a = parse_args_from(&sv(&[
            "leanre-kernel",
            "extract",
            "--input",
            "in.ndjson",
            "--out-dir",
            "out",
        ]))
        .unwrap();
        // Generic export lacks riemannHypothesis -> empty roots instead of crashing
        assert!(resolve_roots(&a, |n| n == "MyTheorem").is_empty());
        // Legacy RH export containing all 5 RH roots retains backward-compatible fallback
        assert_eq!(
            resolve_roots(&a, |n| DEFAULT_ROOTS.iter().any(|(r, _)| *r == n)).len(),
            5
        );
    }

    #[test]
    fn rejects_mutually_exclusive_root_flags() {
        let err = parse_args_from(&sv(&[
            "leanre-kernel",
            "extract",
            "--input",
            "in.ndjson",
            "--out-dir",
            "out",
            "--rh-defaults",
            "--no-default-roots",
        ]))
        .err()
        .unwrap();
        assert!(err.contains("mutually exclusive"));
    }
}
