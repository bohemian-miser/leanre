// Verifier-owned independent C++17 brute-force dominator tree checker (K5).
// Uses ONLY naive node-removal BFS (zero fast-dominator code) + exhaustive parent-property
// certificate across all edges. Capped to <=16 OpenMP threads.
//
// Build: g++ -O3 -fopenmp -std=c++17 verify/dom_oracle.cpp -o verify/out/dom_oracle
// Usage: verify/out/dom_oracle <oracle_prefix> <tree_bin> <view:proof|stmt> <roots_csv> <samples> <seed> <threads>
//
// <tree_bin> is N rows of int32 triples (decl_id, idom_or_-1, subtree_size).

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <numeric>
#include <omp.h>
#include <random>
#include <string>
#include <vector>

template <typename T>
static std::vector<T> read_vec(const std::string &path) {
    FILE *f = std::fopen(path.c_str(), "rb");
    if (!f) { std::perror(path.c_str()); std::exit(1); }
    std::fseek(f, 0, SEEK_END);
    long sz = std::ftell(f);
    std::fseek(f, 0, SEEK_SET);
    std::vector<T> v((size_t)sz / sizeof(T));
    if (sz && std::fread(v.data(), 1, (size_t)sz, f) != (size_t)sz) { std::perror("fread"); std::exit(1); }
    std::fclose(f);
    return v;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        std::fprintf(stderr, "usage: %s <oracle_prefix> <tree_bin> <proof|stmt> <roots_csv> <samples> <seed> <threads>\n", argv[0]);
        return 2;
    }
    std::string pref = argv[1], tbin = argv[2], view = argv[3], rcsv = argv[4];
    int samples = std::atoi(argv[5]);
    uint64_t seed = std::strtoull(argv[6], nullptr, 10);
    int threads = std::min(16, std::max(1, std::atoi(argv[7])));
    omp_set_num_threads(threads);

    auto rec_kind = read_vec<int8_t>(pref + ".rec_kind.i8");
    int N = (int)rec_kind.size();
    auto src = read_vec<int32_t>(pref + ".src.i32");
    auto dst = read_vec<int32_t>(pref + ".dst.i32");
    auto ek = read_vec<int8_t>(pref + ".kind.i8");

    std::vector<int> roots;
    {
        size_t pos = 0;
        while (pos < rcsv.size()) {
            size_t c = rcsv.find(',', pos);
            std::string tok = (c == std::string::npos) ? rcsv.substr(pos) : rcsv.substr(pos, c - pos);
            if (!tok.empty()) roots.push_back(std::atoi(tok.c_str()));
            if (c == std::string::npos) break;
            pos = c + 1;
        }
    }
    std::vector<uint8_t> is_root(N, 0);
    for (int r : roots) is_root[r] = 1;

    // Build CSR for the requested view
    std::vector<uint64_t> ptr(N + 1, 0);
    bool is_stmt = (view == "stmt");
    size_t M = src.size();
    for (size_t i = 0; i < M; ++i) {
        if (is_stmt && is_root[src[i]] && ek[i] == 2) continue;
        ptr[(size_t)src[i] + 1]++;
    }
    for (int i = 0; i < N; ++i) ptr[i + 1] += ptr[i];
    std::vector<int32_t> adj(ptr[N]);
    {
        std::vector<uint64_t> cur = ptr;
        for (size_t i = 0; i < M; ++i) {
            if (is_stmt && is_root[src[i]] && ek[i] == 2) continue;
            adj[cur[src[i]]++] = dst[i];
        }
    }
    // Free raw edge arrays
    src.clear(); src.shrink_to_fit(); dst.clear(); dst.shrink_to_fit(); ek.clear(); ek.shrink_to_fit();

    // Load claimed dominator tree
    auto raw_tree = read_vec<int32_t>(tbin);
    size_t T = raw_tree.size() / 3;
    std::vector<int32_t> idom(N, -2), sub(N, 0), tnodes(T);
    for (size_t i = 0; i < T; ++i) {
        int32_t v = raw_tree[3 * i], p = raw_tree[3 * i + 1], s = raw_tree[3 * i + 2];
        tnodes[i] = v; idom[v] = p; sub[v] = s;
    }

    // 1. Base reachability BFS (with parent pointers to reconstruct a root->v path for any v)
    std::vector<int32_t> base_par(N, -2);
    std::vector<int32_t> q;
    q.reserve(N);
    for (int r : roots) {
        if (base_par[r] == -2) { base_par[r] = -1; q.push_back(r); }
    }
    for (size_t qi = 0; qi < q.size(); ++qi) {
        int u = q[qi];
        for (uint64_t e = ptr[u]; e < ptr[u + 1]; ++e) {
            int w = adj[e];
            if (base_par[w] == -2) { base_par[w] = u; q.push_back(w); }
        }
    }
    size_t n_reach = q.size();
    bool cover_ok = (T == n_reach);
    for (int v : tnodes) if (base_par[v] == -2) cover_ok = false;

    // 2. Check tree structure + recompute subtree sizes + Euler tin/tout
    std::vector<std::vector<int32_t>> ch(N + 1); // index N = virtual root (-1)
    for (int v : tnodes) {
        int p = idom[v];
        int pi = (p < 0) ? N : p;
        ch[pi].push_back(v);
    }
    std::vector<int32_t> tin(N + 1, -1), tout(N + 1, -1);
    int32_t timer = 0;
    size_t visited_tree = 0;
    {
        std::vector<std::pair<int, int>> st;
        st.reserve(T + 2);
        st.push_back({N, 0});
        while (!st.empty()) {
            auto [u, state] = st.back();
            st.pop_back();
            if (state == 0) {
                tin[u] = timer++;
                visited_tree++;
                st.push_back({u, 1});
                for (int w : ch[u]) st.push_back({w, 0});
            } else {
                tout[u] = timer;
            }
        }
    }
    bool is_tree = (visited_tree == T + 1);
    int sub_bad = 0;
    for (int v : tnodes) {
        if (tout[v] - tin[v] != sub[v]) sub_bad++;
    }

    // 3. Exhaustive parent-property check across ALL reachable edges:
    //    for every reachable edge u->v, idom(v) must be an ancestor-or-self of u (or virtual root -1).
    uint64_t checked_edges = 0, pp_viol = 0;
    for (int u : q) {
        int tu = tin[u];
        for (uint64_t e = ptr[u]; e < ptr[u + 1]; ++e) {
            int v = adj[e];
            checked_edges++;
            int p = idom[v];
            if (p >= 0) {
                if (!(tin[p] <= tu && tu < tout[p])) pp_viol++;
            }
        }
    }

    // 4. Select top-50 non-root dominators by subtree_size + random sample of non-root nodes
    std::vector<int32_t> nonroot;
    nonroot.reserve(T);
    for (int v : tnodes) if (!is_root[v]) nonroot.push_back(v);
    std::vector<int32_t> top = nonroot;
    std::stable_sort(top.begin(), top.end(), [&](int a, int b) {
        return sub[a] != sub[b] ? sub[a] > sub[b] : a < b;
    });
    if (top.size() > 50) top.resize(50);

    std::mt19937_64 rng(seed);
    std::vector<int32_t> shuffled = nonroot;
    std::shuffle(shuffled.begin(), shuffled.end(), rng);
    if ((int)shuffled.size() > samples) shuffled.resize((size_t)samples);

    std::vector<int32_t> samp = shuffled;
    samp.insert(samp.end(), top.begin(), top.end());
    std::sort(samp.begin(), samp.end());
    samp.erase(std::unique(samp.begin(), samp.end()), samp.end());

    // 5. Parallel brute-force node-removal idom check for every v in samp:
    //    Since (3) already proved idom(v) dominates v (if pp_viol == 0), we STILL independently
    //    verify BOTH (a) v is unreachable when idom(v) is removed, AND (b) no node strictly
    //    between idom(v) and v on a root->v path dominates v!
    int idom_errs = 0;
    std::vector<std::string> err_msgs;

    #pragma omp parallel
    {
        std::vector<uint32_t> vis(N, 0);
        uint32_t gen = 0;
        std::vector<int32_t> bfsq;
        bfsq.reserve(1 << 16);

        auto reachable_without = [&](int removed, int target) -> bool {
            if (++gen == 0) { std::fill(vis.begin(), vis.end(), 0); gen = 1; }
            if (removed >= 0) vis[removed] = gen;
            bfsq.clear();
            for (int r : roots) {
                if (r != removed && vis[r] != gen) {
                    if (r == target) return true;
                    vis[r] = gen; bfsq.push_back(r);
                }
            }
            for (size_t i = 0; i < bfsq.size(); ++i) {
                int u = bfsq[i];
                for (uint64_t e = ptr[u]; e < ptr[u + 1]; ++e) {
                    int w = adj[e];
                    if (vis[w] != gen) {
                        if (w == target) return true;
                        vis[w] = gen; bfsq.push_back(w);
                    }
                }
            }
            return false;
        };

        // Also find a path from start -> target in the graph
        std::vector<int32_t> path_nodes;
        #pragma omp for schedule(dynamic, 8)
        for (size_t idx = 0; idx < samp.size(); ++idx) {
            int v = samp[idx];
            int p = idom[v];
            // (a) claimed idom p must dominate v
            if (p >= 0 && reachable_without(p, v)) {
                #pragma omp critical
                {
                    idom_errs++;
                    if (err_msgs.size() < 5) {
                        char buf[160];
                        std::snprintf(buf, sizeof(buf), "v=%d: claimed idom=%d does NOT dominate", v, p);
                        err_msgs.push_back(buf);
                    }
                }
                continue;
            }
            // (b) extract a path root ~> v using base_par; every strict dominator of v
            //     must lie on this path! Check every node strictly below p on this path.
            path_nodes.clear();
            for (int x = v; x != -1; x = base_par[x]) path_nodes.push_back(x);
            std::reverse(path_nodes.begin(), path_nodes.end());
            // Find position of p in path_nodes (p MUST be on the path since p dominates v)
            size_t start_pos = 0;
            if (p >= 0) {
                auto it = std::find(path_nodes.begin(), path_nodes.end(), p);
                if (it == path_nodes.end()) {
                    #pragma omp critical
                    {
                        idom_errs++;
                        if (err_msgs.size() < 5) {
                            char buf[160];
                            std::snprintf(buf, sizeof(buf), "v=%d: claimed idom=%d not on root->v path", v, p);
                            err_msgs.push_back(buf);
                        }
                    }
                    continue;
                }
                start_pos = (size_t)(it - path_nodes.begin()) + 1;
            }
            // Test every interior node d strictly between p and v on the path
            for (size_t j = start_pos; j + 1 < path_nodes.size(); ++j) {
                int d = path_nodes[j];
                if (!reachable_without(d, v)) {
                    #pragma omp critical
                    {
                        idom_errs++;
                        if (err_msgs.size() < 5) {
                            char buf[160];
                            std::snprintf(buf, sizeof(buf), "v=%d: d=%d dominates v below claimed idom=%d", v, d, p);
                            err_msgs.push_back(buf);
                        }
                    }
                    break;
                }
            }
        }
    }

    // 6. Parallel brute-force dominated-set-size check on all top-50 dominators
    std::vector<int32_t> bf_sizes(top.size(), 0);
    #pragma omp parallel
    {
        std::vector<uint32_t> vis(N, 0);
        uint32_t gen = 0;
        std::vector<int32_t> bfsq;
        bfsq.reserve(N);

        #pragma omp for schedule(dynamic, 1)
        for (size_t idx = 0; idx < top.size(); ++idx) {
            int d = top[idx];
            if (++gen == 0) { std::fill(vis.begin(), vis.end(), 0); gen = 1; }
            vis[d] = gen;
            bfsq.clear();
            for (int r : roots) {
                if (r != d && vis[r] != gen) { vis[r] = gen; bfsq.push_back(r); }
            }
            for (size_t i = 0; i < bfsq.size(); ++i) {
                int u = bfsq[i];
                for (uint64_t e = ptr[u]; e < ptr[u + 1]; ++e) {
                    int w = adj[e];
                    if (vis[w] != gen) { vis[w] = gen; bfsq.push_back(w); }
                }
            }
            bf_sizes[idx] = (int32_t)(n_reach - bfsq.size());
        }
    }
    int size_bad = 0;
    for (size_t i = 0; i < top.size(); ++i) {
        if (bf_sizes[i] != sub[top[i]]) size_bad++;
    }

    std::printf("RESULT cover=%d is_tree=%d sub_bad=%d checked_edges=%llu pp_viol=%llu sampled=%zu top=%zu idom_errs=%d size_bad=%d\n",
                (int)cover_ok, (int)is_tree, sub_bad, (unsigned long long)checked_edges, (unsigned long long)pp_viol,
                samp.size(), top.size(), idom_errs, size_bad);
    for (const auto &e : err_msgs) std::printf("ERR %s\n", e.c_str());
    for (size_t i = 0; i < std::min<size_t>(5, top.size()); ++i)
        std::printf("TOP %d claimed=%d bruteforce=%d\n", top[i], sub[top[i]], bf_sizes[i]);
    return (cover_ok && is_tree && sub_bad == 0 && pp_viol == 0 && idom_errs == 0 && size_bad == 0) ? 0 : 1;
}
