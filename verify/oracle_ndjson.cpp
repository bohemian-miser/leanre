// Verifier-owned independent C++17 streaming parser for lean4export NDJSON (v3.1.0).
// Zero external dependencies; completely independent of leanre/ndjson.py and leanre/kernel-rs.
// Cross-checked bit-for-bit against verify/oracle_ndjson.py on data/challenge.ndjson.zst
// before trusting on data/solution.ndjson.zst.
//
// Build: g++ -O3 -std=c++17 verify/oracle_ndjson.cpp -o verify/out/oracle_ndjson
// Usage: verify/out/oracle_ndjson <input.ndjson[.zst]> <out_prefix>

#include <algorithm>
#include <cassert>
#include <cerrno>
#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <map>
#include <string>
#include <sys/resource.h>
#include <unordered_map>
#include <vector>

// ---------------- Minimal, order-independent, zero-churn arena JSON parser ----------------
struct JVal {
    enum Type : uint8_t { JNULL, JBOOL, JINT, JSTR, JARR, JOBJ } type = JNULL;
    int64_t ival = 0;
    uint32_t s_off = 0, s_len = 0;  // slice in strbuf
    uint32_t first = 0, count = 0;  // for JARR: elems[first..+count]; for JOBJ: kv[first..+count]
};
struct JKV { uint32_t k_off, k_len, v_idx; };

struct JArena {
    std::vector<JVal> vals;
    std::vector<uint32_t> elems;
    std::vector<JKV> kvs;
    std::string strbuf;

    void clear() { vals.clear(); elems.clear(); kvs.clear(); strbuf.clear(); }

    std::string_view sv(uint32_t off, uint32_t len) const {
        return std::string_view(strbuf.data() + off, len);
    }
    std::string_view sv(const JVal &v) const { return sv(v.s_off, v.s_len); }

    int find(uint32_t obj_idx, const char *key) const {
        const JVal &o = vals[obj_idx];
        if (o.type != JVal::JOBJ) return -1;
        size_t klen = std::strlen(key);
        for (uint32_t i = 0; i < o.count; ++i) {
            const JKV &kv = kvs[o.first + i];
            if (kv.k_len == klen && std::memcmp(strbuf.data() + kv.k_off, key, klen) == 0)
                return (int)kv.v_idx;
        }
        return -1;
    }
};

struct JParser {
    const char *p, *end;
    JArena &A;

    void ws() { while (p < end && (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n')) ++p; }

    static void append_utf8(std::string &out, uint32_t cp) {
        if (cp < 0x80) out.push_back((char)cp);
        else if (cp < 0x800) {
            out.push_back((char)(0xC0 | (cp >> 6)));
            out.push_back((char)(0x80 | (cp & 0x3F)));
        } else if (cp < 0x10000) {
            out.push_back((char)(0xE0 | (cp >> 12)));
            out.push_back((char)(0x80 | ((cp >> 6) & 0x3F)));
            out.push_back((char)(0x80 | (cp & 0x3F)));
        } else {
            out.push_back((char)(0xF0 | (cp >> 18)));
            out.push_back((char)(0x80 | ((cp >> 12) & 0x3F)));
            out.push_back((char)(0x80 | ((cp >> 6) & 0x3F)));
            out.push_back((char)(0x80 | (cp & 0x3F)));
        }
    }

    uint32_t parse_hex4() {
        uint32_t v = 0;
        for (int i = 0; i < 4; ++i) {
            if (p >= end) { std::fprintf(stderr, "truncated \\u escape\n"); std::exit(2); }
            char c = *p++;
            v <<= 4;
            if (c >= '0' && c <= '9') v |= (uint32_t)(c - '0');
            else if (c >= 'a' && c <= 'f') v |= (uint32_t)(c - 'a' + 10);
            else if (c >= 'A' && c <= 'F') v |= (uint32_t)(c - 'A' + 10);
            else { std::fprintf(stderr, "bad hex char '%c'\n", c); std::exit(2); }
        }
        return v;
    }

    void parse_str(uint32_t &off, uint32_t &len) {
        assert(p < end && *p == '"');
        ++p;
        off = (uint32_t)A.strbuf.size();
        const char *q = p;
        while (q < end && *q != '"' && *q != '\\') ++q;
        if (q < end && *q == '"') {
            A.strbuf.append(p, (size_t)(q - p));
            len = (uint32_t)(q - p);
            p = q + 1;
            return;
        }
        while (p < end) {
            char c = *p++;
            if (c == '"') break;
            if (c != '\\') { A.strbuf.push_back(c); continue; }
            if (p >= end) { std::fprintf(stderr, "truncated escape\n"); std::exit(2); }
            char e = *p++;
            switch (e) {
                case '"': case '\\': case '/': A.strbuf.push_back(e); break;
                case 'b': A.strbuf.push_back('\b'); break;
                case 'f': A.strbuf.push_back('\f'); break;
                case 'n': A.strbuf.push_back('\n'); break;
                case 'r': A.strbuf.push_back('\r'); break;
                case 't': A.strbuf.push_back('\t'); break;
                case 'u': {
                    uint32_t cp = parse_hex4();
                    if (cp >= 0xD800 && cp <= 0xDBFF && p + 2 <= end && p[0] == '\\' && p[1] == 'u') {
                        p += 2;
                        uint32_t lo = parse_hex4();
                        if (lo >= 0xDC00 && lo <= 0xDFFF)
                            cp = 0x10000 + (((cp - 0xD800) << 10) | (lo - 0xDC00));
                    }
                    append_utf8(A.strbuf, cp);
                    break;
                }
                default: A.strbuf.push_back(e); break;
            }
        }
        len = (uint32_t)A.strbuf.size() - off;
    }

    uint32_t parse_val() {
        ws();
        if (p >= end) { std::fprintf(stderr, "unexpected EOF in JSON\n"); std::exit(2); }
        uint32_t idx = (uint32_t)A.vals.size();
        A.vals.push_back({});
        char c = *p;
        if (c == '{') {
            ++p; ws();
            std::vector<JKV> local;
            if (p < end && *p == '}') { ++p; }
            else {
                while (true) {
                    ws();
                    uint32_t ko, kl;
                    parse_str(ko, kl);
                    ws();
                    if (p >= end || *p != ':') { std::fprintf(stderr, "expected ':'\n"); std::exit(2); }
                    ++p;
                    uint32_t vi = parse_val();
                    local.push_back({ko, kl, vi});
                    ws();
                    if (p < end && *p == ',') { ++p; continue; }
                    if (p < end && *p == '}') { ++p; break; }
                    std::fprintf(stderr, "expected ',' or '}'\n"); std::exit(2);
                }
            }
            A.vals[idx].type = JVal::JOBJ;
            A.vals[idx].first = (uint32_t)A.kvs.size();
            A.vals[idx].count = (uint32_t)local.size();
            A.kvs.insert(A.kvs.end(), local.begin(), local.end());
            return idx;
        }
        if (c == '[') {
            ++p; ws();
            std::vector<uint32_t> local;
            if (p < end && *p == ']') { ++p; }
            else {
                while (true) {
                    local.push_back(parse_val());
                    ws();
                    if (p < end && *p == ',') { ++p; continue; }
                    if (p < end && *p == ']') { ++p; break; }
                    std::fprintf(stderr, "expected ',' or ']'\n"); std::exit(2);
                }
            }
            A.vals[idx].type = JVal::JARR;
            A.vals[idx].first = (uint32_t)A.elems.size();
            A.vals[idx].count = (uint32_t)local.size();
            A.elems.insert(A.elems.end(), local.begin(), local.end());
            return idx;
        }
        if (c == '"') {
            uint32_t so, sl;
            parse_str(so, sl);
            A.vals[idx].type = JVal::JSTR;
            A.vals[idx].s_off = so; A.vals[idx].s_len = sl;
            return idx;
        }
        if (c == 't' && end - p >= 4 && std::memcmp(p, "true", 4) == 0) {
            p += 4; A.vals[idx].type = JVal::JBOOL; A.vals[idx].ival = 1; return idx;
        }
        if (c == 'f' && end - p >= 5 && std::memcmp(p, "false", 5) == 0) {
            p += 5; A.vals[idx].type = JVal::JBOOL; A.vals[idx].ival = 0; return idx;
        }
        if (c == 'n' && end - p >= 4 && std::memcmp(p, "null", 4) == 0) {
            p += 4; A.vals[idx].type = JVal::JNULL; return idx;
        }
        // number: record both raw slice (for huge ints like Name.num) and int64
        const char *start = p;
        bool neg = false;
        if (*p == '-') { neg = true; ++p; }
        uint64_t u = 0;
        while (p < end && *p >= '0' && *p <= '9') { u = u * 10 + (uint64_t)(*p - '0'); ++p; }
        if (p < end && (*p == '.' || *p == 'e' || *p == 'E')) {
            while (p < end && (*p == '.' || *p == 'e' || *p == 'E' || *p == '+' || *p == '-' || (*p >= '0' && *p <= '9'))) ++p;
        }
        uint32_t off = (uint32_t)A.strbuf.size();
        A.strbuf.append(start, (size_t)(p - start));
        A.vals[idx].type = JVal::JINT;
        A.vals[idx].ival = neg ? -(int64_t)u : (int64_t)u;
        A.vals[idx].s_off = off; A.vals[idx].s_len = (uint32_t)(p - start);
        return idx;
    }
};

// ---------------- Compact NDJSON state ----------------
enum EKind : uint8_t { K_LEAF = 0, K_CONST = 1, K_BIN = 2, K_LET = 3, K_PROJ = 4, K_MDATA = 5 };
struct LetE { uint32_t ty, val, body; };
struct NameNode { uint32_t pre; uint32_t off; uint32_t len; };

static std::string json_escape(std::string_view s) {
    std::string o;
    o.reserve(s.size() + 2);
    o.push_back('"');
    for (unsigned char c : s) {
        switch (c) {
            case '"': o += "\\\""; break;
            case '\\': o += "\\\\"; break;
            case '\b': o += "\\b"; break;
            case '\f': o += "\\f"; break;
            case '\n': o += "\\n"; break;
            case '\r': o += "\\r"; break;
            case '\t': o += "\\t"; break;
            default:
                if (c < 0x20) {
                    char buf[8];
                    std::snprintf(buf, sizeof(buf), "\\u%04x", c);
                    o += buf;
                } else o.push_back((char)c);
        }
    }
    o.push_back('"');
    return o;
}

static bool is_leaf_key(std::string_view k) {
    return k == "sort" || k == "bvar" || k == "natVal" || k == "strVal" || k == "lit" || k == "fvar" || k == "mvar";
}

// Record kind indices matching verify/oracle_full.py KINDS:
// 0=thm, 1=def, 2=opaque, 3=axiom, 4=quot, 5=inductive
static int decl_kind_id(std::string_view k) {
    if (k == "thm") return 0;
    if (k == "def") return 1;
    if (k == "opaque") return 2;
    if (k == "axiom") return 3;
    if (k == "quot") return 4;
    if (k == "inductive") return 5;
    return -1;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        std::fprintf(stderr, "usage: %s <input.ndjson[.zst]> <out_prefix>\n", argv[0]);
        return 2;
    }
    std::string in_path = argv[1];
    std::string out_pref = argv[2];
    timespec ts0{}, ts1{};
    clock_gettime(CLOCK_MONOTONIC, &ts0);

    FILE *fp = nullptr;
    bool is_pipe = false;
    if (in_path.size() >= 4 && in_path.compare(in_path.size() - 4, 4, ".zst") == 0) {
        std::string cmd = "zstd -d -c --long=31 '" + in_path + "'";
        fp = popen(cmd.c_str(), "r");
        is_pipe = true;
    } else {
        fp = std::fopen(in_path.c_str(), "rb");
    }
    if (!fp) { std::perror("open input"); return 1; }
    static std::vector<char> io_buf(1 << 22);
    std::setvbuf(fp, io_buf.data(), _IOFBF, io_buf.size());

    // Compact expression storage (~9 bytes/expr; letE stored out-of-line)
    std::vector<uint8_t> ekind;
    std::vector<uint32_t> eA, eB;
    std::vector<LetE> lets;

    // Compact name storage: parent id + segment slice in a flat char pool
    std::vector<NameNode> names(1, {0, 0, 0});
    std::string name_pool;
    name_pool.reserve(1 << 24);
    auto build_name = [&](uint32_t nid) -> std::string {
        std::vector<uint32_t> chain;
        uint32_t cur = nid;
        while (cur != 0 && cur < names.size()) {
            chain.push_back(cur);
            cur = names[cur].pre;
        }
        std::string res;
        for (size_t i = chain.size(); i-- > 0;) {
            if (!res.empty()) res.push_back('.');
            const auto &nn = names[chain[i]];
            res.append(name_pool.data() + nn.off, nn.len);
        }
        return res;
    };

    // Declaration records and streaming edge extraction
    std::vector<uint32_t> rec_primary_nid;
    std::vector<uint8_t> rec_kind;
    std::vector<int32_t> rec_n_consts;
    std::vector<std::pair<uint32_t, uint32_t>> all_const_pairs;  // (nid, rec_idx)
    std::vector<int32_t> nid_to_rec;  // -1 if unowned

    std::vector<uint32_t> seen_gen;
    uint32_t cur_gen = 0;
    std::vector<uint32_t> walk_stack;
    std::vector<uint32_t> tmp_nids;

    // Edges output buffers (streamed as decls arrive; unresolved forward refs patched at EOF)
    struct PendingRef { uint32_t rec_idx; uint8_t mask; uint32_t nid; };
    std::vector<PendingRef> pending_refs;
    std::vector<int32_t> edge_src, edge_dst;
    std::vector<int8_t> edge_kind;
    edge_src.reserve(1 << 20); edge_dst.reserve(1 << 20); edge_kind.reserve(1 << 20);

    std::map<std::string, uint64_t> top_keys, leaf_kinds, unknown_expr, unknown_top;
    uint64_t ind_types = 0, ind_ctors = 0, ind_recs = 0;
    uint64_t nlines = 0, dup_const_ids = 0;
    int64_t max_eid = -1;
    std::string meta_raw = "null";

    auto ensure_expr = [&](uint32_t eid) {
        if ((int64_t)eid > max_eid) max_eid = (int64_t)eid;
        if (eid >= ekind.size()) {
            size_t ns = std::max<size_t>((size_t)eid + 1, ekind.size() ? ekind.size() * 2 : (1u << 20));
            ekind.resize(ns, 0);
            eA.resize(ns, 0);
            eB.resize(ns, 0);
        }
    };
    auto ensure_nid = [&](uint32_t nid) {
        if (nid >= names.size()) names.resize((size_t)nid + 1, {0, 0, 0});
        if (nid >= nid_to_rec.size()) nid_to_rec.resize((size_t)nid + 1, -1);
    };

    auto collect_refs = [&](const std::vector<uint32_t> &roots, std::vector<uint32_t> &out_nids) {
        out_nids.clear();
        if (roots.empty()) return;
        if (seen_gen.size() < ekind.size()) seen_gen.resize(ekind.size(), 0);
        ++cur_gen;
        if (cur_gen == 0) { std::fill(seen_gen.begin(), seen_gen.end(), 0); cur_gen = 1; }
        uint32_t g = cur_gen;
        walk_stack.clear();
        for (uint32_t r : roots) {
            if (r >= ekind.size()) {
                std::fprintf(stderr, "FATAL: expr root %u out of range (%zu)\n", r, ekind.size());
                std::exit(3);
            }
            if (seen_gen[r] != g) { seen_gen[r] = g; walk_stack.push_back(r); }
        }
        while (!walk_stack.empty()) {
            uint32_t e = walk_stack.back();
            walk_stack.pop_back();
            uint8_t k = ekind[e];
            if (k == K_BIN) {
                uint32_t a = eA[e], b = eB[e];
                if (seen_gen[a] != g) { seen_gen[a] = g; walk_stack.push_back(a); }
                if (seen_gen[b] != g) { seen_gen[b] = g; walk_stack.push_back(b); }
            } else if (k == K_CONST) {
                out_nids.push_back(eA[e]);
            } else if (k == K_LET) {
                const LetE &L = lets[eA[e]];
                if (seen_gen[L.ty] != g) { seen_gen[L.ty] = g; walk_stack.push_back(L.ty); }
                if (seen_gen[L.val] != g) { seen_gen[L.val] = g; walk_stack.push_back(L.val); }
                if (seen_gen[L.body] != g) { seen_gen[L.body] = g; walk_stack.push_back(L.body); }
            } else if (k == K_PROJ) {
                out_nids.push_back(eB[e]);
                uint32_t a = eA[e];
                if (seen_gen[a] != g) { seen_gen[a] = g; walk_stack.push_back(a); }
            } else if (k == K_MDATA) {
                uint32_t a = eA[e];
                if (seen_gen[a] != g) { seen_gen[a] = g; walk_stack.push_back(a); }
            }
        }
    };

    JArena A;
    char *line = nullptr;
    size_t cap = 0;
    ssize_t len = 0;
    std::vector<uint32_t> troots, vroots, t_nids, v_nids;
    std::vector<std::pair<int32_t, int8_t>> rec_edges;

    while ((len = ::getline(&line, &cap, fp)) > 0) {
        ++nlines;
        if (nlines % 50000000ULL == 0) {
            clock_gettime(CLOCK_MONOTONIC, &ts1);
            double dt = (ts1.tv_sec - ts0.tv_sec) + (ts1.tv_nsec - ts0.tv_nsec) * 1e-9;
            std::fprintf(stderr, "  .. %" PRIu64 " lines, %zu records, %" PRId64 " max_eid, %.1fs\n",
                         nlines, rec_kind.size(), max_eid, dt);
        }
        A.clear();
        JParser P{line, line + len, A};
        uint32_t root = P.parse_val();
        const JVal &O = A.vals[root];
        assert(O.type == JVal::JOBJ);

        int i_ie = A.find(root, "ie");
        if (i_ie >= 0) {
            uint32_t eid = (uint32_t)A.vals[i_ie].ival;
            ensure_expr(eid);
            int f;
            if ((f = A.find(root, "app")) >= 0) {
                ekind[eid] = K_BIN;
                eA[eid] = (uint32_t)A.vals[A.find(f, "fn")].ival;
                eB[eid] = (uint32_t)A.vals[A.find(f, "arg")].ival;
            } else if ((f = A.find(root, "const")) >= 0) {
                ekind[eid] = K_CONST;
                eA[eid] = (uint32_t)A.vals[A.find(f, "name")].ival;
            } else if ((f = A.find(root, "lam")) >= 0) {
                ekind[eid] = K_BIN;
                eA[eid] = (uint32_t)A.vals[A.find(f, "type")].ival;
                eB[eid] = (uint32_t)A.vals[A.find(f, "body")].ival;
            } else if ((f = A.find(root, "forallE")) >= 0) {
                ekind[eid] = K_BIN;
                eA[eid] = (uint32_t)A.vals[A.find(f, "type")].ival;
                eB[eid] = (uint32_t)A.vals[A.find(f, "body")].ival;
            } else if ((f = A.find(root, "letE")) >= 0) {
                ekind[eid] = K_LET;
                uint32_t li = (uint32_t)lets.size();
                lets.push_back({(uint32_t)A.vals[A.find(f, "type")].ival,
                                (uint32_t)A.vals[A.find(f, "value")].ival,
                                (uint32_t)A.vals[A.find(f, "body")].ival});
                eA[eid] = li;
            } else if ((f = A.find(root, "proj")) >= 0) {
                ekind[eid] = K_PROJ;
                eA[eid] = (uint32_t)A.vals[A.find(f, "struct")].ival;
                eB[eid] = (uint32_t)A.vals[A.find(f, "typeName")].ival;
            } else if ((f = A.find(root, "mdata")) >= 0) {
                ekind[eid] = K_MDATA;
                eA[eid] = (uint32_t)A.vals[A.find(f, "expr")].ival;
            } else {
                ekind[eid] = K_LEAF;
                std::string k0 = "?";
                for (uint32_t i = 0; i < O.count; ++i) {
                    auto ks = A.sv(A.kvs[O.first + i].k_off, A.kvs[O.first + i].k_len);
                    if (ks != "ie") { k0.assign(ks); break; }
                }
                if (!is_leaf_key(k0)) unknown_expr[k0]++;
                leaf_kinds[k0]++;
            }
            continue;
        }
        int i_in = A.find(root, "in");
        if (i_in >= 0) {
            uint32_t nid = (uint32_t)A.vals[i_in].ival;
            ensure_nid(nid);
            int f;
            if ((f = A.find(root, "str")) >= 0) {
                uint32_t pre = (uint32_t)A.vals[A.find(f, "pre")].ival;
                auto s = A.sv(A.vals[A.find(f, "str")]);
                uint32_t off = (uint32_t)name_pool.size();
                name_pool.append(s.data(), s.size());
                names[nid] = {pre, off, (uint32_t)s.size()};
            } else if ((f = A.find(root, "num")) >= 0) {
                uint32_t pre = (uint32_t)A.vals[A.find(f, "pre")].ival;
                auto s = A.sv(A.vals[A.find(f, "i")]);
                uint32_t off = (uint32_t)name_pool.size();
                name_pool.append(s.data(), s.size());
                names[nid] = {pre, off, (uint32_t)s.size()};
            } else {
                unknown_top["in:other"]++;
            }
            continue;
        }
        if (A.find(root, "il") >= 0) { top_keys["il"]++; continue; }

        // Check declaration record keys
        bool hit = false;
        for (uint32_t ki = 0; ki < O.count; ++ki) {
            const JKV &kv = A.kvs[O.first + ki];
            auto ks = A.sv(kv.k_off, kv.k_len);
            int dk = decl_kind_id(ks);
            if (dk < 0) continue;
            hit = true;
            top_keys[std::string(ks)]++;
            uint32_t d_idx = kv.v_idx;
            uint32_t ridx = (uint32_t)rec_kind.size();
            troots.clear(); vroots.clear();
            uint32_t prim_nid = 0;
            int32_t nc = 0;
            if (dk == 5) {  // inductive
                int ft = A.find(d_idx, "types"), fc = A.find(d_idx, "ctors"), fr = A.find(d_idx, "recs");
                auto add_arr = [&](int fi, uint64_t &ctr, bool is_types, bool is_recs) {
                    if (fi < 0) return;
                    const JVal &arr = A.vals[fi];
                    ctr += arr.count;
                    for (uint32_t j = 0; j < arr.count; ++j) {
                        uint32_t item = A.elems[arr.first + j];
                        uint32_t cnid = (uint32_t)A.vals[A.find(item, "name")].ival;
                        if (is_types && j == 0) prim_nid = cnid;
                        ensure_nid(cnid);
                        if (nid_to_rec[cnid] != -1) dup_const_ids++;
                        nid_to_rec[cnid] = (int32_t)ridx;
                        all_const_pairs.push_back({cnid, ridx});
                        nc++;
                        troots.push_back((uint32_t)A.vals[A.find(item, "type")].ival);
                        if (is_recs) {
                            int frules = A.find(item, "rules");
                            if (frules >= 0) {
                                const JVal &ra = A.vals[frules];
                                for (uint32_t m = 0; m < ra.count; ++m) {
                                    uint32_t rl = A.elems[ra.first + m];
                                    vroots.push_back((uint32_t)A.vals[A.find(rl, "rhs")].ival);
                                }
                            }
                        }
                    }
                };
                add_arr(ft, ind_types, true, false);
                add_arr(fc, ind_ctors, false, false);
                add_arr(fr, ind_recs, false, true);
            } else {
                prim_nid = (uint32_t)A.vals[A.find(d_idx, "name")].ival;
                ensure_nid(prim_nid);
                if (nid_to_rec[prim_nid] != -1) dup_const_ids++;
                nid_to_rec[prim_nid] = (int32_t)ridx;
                all_const_pairs.push_back({prim_nid, ridx});
                nc = 1;
                troots.push_back((uint32_t)A.vals[A.find(d_idx, "type")].ival);
                int fv = A.find(d_idx, "value");
                if (fv >= 0) vroots.push_back((uint32_t)A.vals[fv].ival);
            }
            rec_primary_nid.push_back(prim_nid);
            rec_kind.push_back((uint8_t)dk);
            rec_n_consts.push_back(nc);

            // Walk expressions now and emit edges
            collect_refs(troots, t_nids);
            collect_refs(vroots, v_nids);
            rec_edges.clear();
            for (uint32_t nid : t_nids) {
                int32_t j = (nid < nid_to_rec.size()) ? nid_to_rec[nid] : -1;
                if (j < 0) pending_refs.push_back({ridx, 1, nid});
                else if ((uint32_t)j != ridx) rec_edges.push_back({j, 1});
            }
            for (uint32_t nid : v_nids) {
                int32_t j = (nid < nid_to_rec.size()) ? nid_to_rec[nid] : -1;
                if (j < 0) pending_refs.push_back({ridx, 2, nid});
                else if ((uint32_t)j != ridx) rec_edges.push_back({j, 2});
            }
            std::sort(rec_edges.begin(), rec_edges.end());
            for (size_t i = 0; i < rec_edges.size();) {
                int32_t dst = rec_edges[i].first;
                int8_t mk = 0;
                while (i < rec_edges.size() && rec_edges[i].first == dst) { mk |= rec_edges[i].second; ++i; }
                edge_src.push_back((int32_t)ridx);
                edge_dst.push_back(dst);
                edge_kind.push_back(mk);
            }
            break;
        }
        if (!hit) {
            if (A.find(root, "meta") >= 0) {
                // extract raw meta value from line
                std::string_view lv(line, (size_t)len);
                while (!lv.empty() && (lv.back() == '\n' || lv.back() == '\r')) lv.remove_suffix(1);
                meta_raw.assign(lv);
            } else {
                std::string ks;
                for (uint32_t i = 0; i < O.count; ++i) {
                    if (i) ks.push_back(',');
                    ks.append(A.sv(A.kvs[O.first + i].k_off, A.kvs[O.first + i].k_len));
                }
                unknown_top[ks]++;
            }
        }
    }
    std::free(line);
    if (is_pipe) {
        int rc = pclose(fp);
        if (rc != 0) { std::fprintf(stderr, "zstd exit %d\n", rc); return 1; }
    } else {
        std::fclose(fp);
    }

    // Resolve any forward refs (or record dangling refs)
    std::map<std::string, uint64_t> dangling;
    uint64_t resolved_forward = 0;
    if (!pending_refs.empty()) {
        std::vector<std::tuple<int32_t, int32_t, int8_t>> extra;
        for (const auto &pr : pending_refs) {
            int32_t j = (pr.nid < nid_to_rec.size()) ? nid_to_rec[pr.nid] : -1;
            if (j < 0) dangling[build_name(pr.nid)]++;
            else if ((uint32_t)j != pr.rec_idx) {
                resolved_forward++;
                extra.push_back({(int32_t)pr.rec_idx, j, (int8_t)pr.mask});
            }
        }
        if (!extra.empty()) {
            // Merge into edge arrays
            std::vector<std::tuple<int32_t, int32_t, int8_t>> all;
            all.reserve(edge_src.size() + extra.size());
            for (size_t i = 0; i < edge_src.size(); ++i) all.push_back({edge_src[i], edge_dst[i], edge_kind[i]});
            all.insert(all.end(), extra.begin(), extra.end());
            std::sort(all.begin(), all.end());
            edge_src.clear(); edge_dst.clear(); edge_kind.clear();
            for (size_t i = 0; i < all.size();) {
                int32_t s = std::get<0>(all[i]), d = std::get<1>(all[i]);
                int8_t mk = 0;
                while (i < all.size() && std::get<0>(all[i]) == s && std::get<1>(all[i]) == d) {
                    mk |= std::get<2>(all[i]); ++i;
                }
                edge_src.push_back(s); edge_dst.push_back(d); edge_kind.push_back(mk);
            }
        }
    }

    // Free large expression arrays before writing outputs
    ekind.clear(); ekind.shrink_to_fit();
    eA.clear(); eA.shrink_to_fit();
    eB.clear(); eB.shrink_to_fit();
    lets.clear(); lets.shrink_to_fit();
    seen_gen.clear(); seen_gen.shrink_to_fit();

    auto write_bin = [&](const std::string &suf, const void *ptr, size_t bytes) {
        std::string p = out_pref + suf;
        FILE *f = std::fopen(p.c_str(), "wb");
        if (!f) { std::perror(p.c_str()); std::exit(1); }
        if (bytes && std::fwrite(ptr, 1, bytes, f) != bytes) { std::perror("fwrite"); std::exit(1); }
        std::fclose(f);
    };
    write_bin(".src.i32", edge_src.data(), edge_src.size() * sizeof(int32_t));
    write_bin(".dst.i32", edge_dst.data(), edge_dst.size() * sizeof(int32_t));
    write_bin(".kind.i8", edge_kind.data(), edge_kind.size() * sizeof(int8_t));
    write_bin(".rec_kind.i8", rec_kind.data(), rec_kind.size() * sizeof(uint8_t));
    write_bin(".n_consts.i32", rec_n_consts.data(), rec_n_consts.size() * sizeof(int32_t));

    uint64_t e_type = 0, e_val = 0, e_both = 0, fwd_refs = 0;
    for (size_t i = 0; i < edge_kind.size(); ++i) {
        if (edge_kind[i] == 1) e_type++;
        else if (edge_kind[i] == 2) e_val++;
        else if (edge_kind[i] == 3) e_both++;
        if (edge_dst[i] >= edge_src[i]) fwd_refs++;
    }

    // Write .names.json + count duplicates
    std::unordered_map<std::string, uint32_t> uniq_rec, uniq_const;
    uniq_rec.reserve(rec_primary_nid.size() * 2);
    uniq_const.reserve(all_const_pairs.size() * 2);
    {
        std::string np = out_pref + ".names.json";
        FILE *f = std::fopen(np.c_str(), "wb");
        if (!f) { std::perror(np.c_str()); return 1; }
        std::setvbuf(f, io_buf.data(), _IOFBF, io_buf.size());
        std::fputs("{\"rec_names\":[", f);
        for (size_t i = 0; i < rec_primary_nid.size(); ++i) {
            if (i) std::fputc(',', f);
            std::string s = build_name(rec_primary_nid[i]);
            uniq_rec[s]++;
            std::string es = json_escape(s);
            std::fwrite(es.data(), 1, es.size(), f);
        }
        std::fputs("],\"const_to_rec\":{", f);
        bool first_c = true;
        for (const auto &pr : all_const_pairs) {
            std::string s = build_name(pr.first);
            auto it = uniq_const.find(s);
            if (it == uniq_const.end()) {
                uniq_const.emplace(s, pr.second);
                if (!first_c) std::fputc(',', f);
                first_c = false;
                std::string es = json_escape(s);
                std::fwrite(es.data(), 1, es.size(), f);
                std::fprintf(f, ":%u", pr.second);
            }
        }
        std::fputs("}}\n", f);
        std::fclose(f);
    }

    clock_gettime(CLOCK_MONOTONIC, &ts1);
    double wall_s = (ts1.tv_sec - ts0.tv_sec) + (ts1.tv_nsec - ts0.tv_nsec) * 1e-9;
    rusage ru{};
    getrusage(RUSAGE_SELF, &ru);

    auto write_map = [&](FILE *f, const std::map<std::string, uint64_t> &m) {
        std::fputc('{', f);
        bool first = true;
        for (const auto &[k, v] : m) {
            if (!first) std::fputc(',', f);
            first = false;
            std::string ek = json_escape(k);
            std::fprintf(f, "%s:%" PRIu64, ek.c_str(), v);
        }
        std::fputc('}', f);
    };

    std::string sp = out_pref + ".summary.json";
    FILE *sf = std::fopen(sp.c_str(), "wb");
    if (!sf) { std::perror(sp.c_str()); return 1; }
    std::fprintf(sf, "{\n");
    std::fprintf(sf, " \"UNKNOWN_expr_kinds\": "); write_map(sf, unknown_expr); std::fprintf(sf, ",\n");
    std::fprintf(sf, " \"UNKNOWN_top_keys\": "); write_map(sf, unknown_top); std::fprintf(sf, ",\n");
    std::fprintf(sf, " \"constants\": %zu,\n", all_const_pairs.size());
    std::fprintf(sf, " \"dangling_const_refs\": %zu,\n", dangling.size());
    std::fprintf(sf, " \"dup_const_ids\": %" PRIu64 ",\n", dup_const_ids);
    std::fprintf(sf, " \"dup_const_names\": %zu,\n", all_const_pairs.size() - uniq_const.size());
    std::fprintf(sf, " \"dup_record_names\": %zu,\n", rec_primary_nid.size() - uniq_rec.size());
    std::fprintf(sf, " \"edges_by_kind\": {\"both\":%" PRIu64 ",\"type\":%" PRIu64 ",\"value\":%" PRIu64 "},\n", e_both, e_type, e_val);
    std::fprintf(sf, " \"edges_union\": %zu,\n", edge_src.size());
    std::fprintf(sf, " \"expr_leaf_kinds\": "); write_map(sf, leaf_kinds); std::fprintf(sf, ",\n");
    std::fprintf(sf, " \"forward_refs\": %" PRIu64 ",\n", fwd_refs);
    std::fprintf(sf, " \"inductive_ctors\": %" PRIu64 ",\n", ind_ctors);
    std::fprintf(sf, " \"inductive_recs\": %" PRIu64 ",\n", ind_recs);
    std::fprintf(sf, " \"inductive_types\": %" PRIu64 ",\n", ind_types);
    std::fprintf(sf, " \"meta_line\": %s,\n", meta_raw.c_str());
    std::fprintf(sf, " \"n_expr\": %" PRId64 ",\n", max_eid + 1);
    std::fprintf(sf, " \"ndjson_lines\": %" PRIu64 ",\n", nlines);
    std::fprintf(sf, " \"peak_rss_kib\": %ld,\n", ru.ru_maxrss);
    std::fprintf(sf, " \"record_kinds\": "); write_map(sf, top_keys); std::fprintf(sf, ",\n");
    std::fprintf(sf, " \"records\": %zu,\n", rec_kind.size());
    std::fprintf(sf, " \"resolved_forward_refs\": %" PRIu64 ",\n", resolved_forward);
    std::fprintf(sf, " \"wall_s\": %.1f\n", wall_s);
    std::fprintf(sf, "}\n");
    std::fclose(sf);

    // Print summary to stdout
    FILE *rf = std::fopen(sp.c_str(), "rb");
    char buf[4096];
    size_t nread;
    while ((nread = std::fread(buf, 1, sizeof(buf), rf)) > 0) std::fwrite(buf, 1, nread, stdout);
    std::fclose(rf);
    return 0;
}
