/*
 * leanre/xref_fast.c — High-speed C99 + OpenMP streaming exporter for LXRF v1
 * static full-graph cross-reference shards (kernel.db -> out_dir/).
 *
 * License: AGPL-3.0-or-later
 * Build:   gcc -O3 -Wall -Wextra -Werror -std=c99 -fopenmp leanre/xref_fast.c \
 *              -lsqlite3 -lz -o /tmp/leanre_xref_fast
 *
 * Reads SQLite databases strictly read-only (SQLITE_OPEN_READONLY).
 * Never embeds raw .lean source or proof bodies.
 */
#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <inttypes.h>
#include <omp.h>
#include <sqlite3.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <zlib.h>

#define LXRF_VERSION 1u
#define DIR_FWD 0u
#define DIR_REV 1u
#define DIR_REV_HUB 2u
#define HUB_SENTINEL 0xFFFFFFFFu

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) {
        fprintf(stderr, "xref_fast: out of memory allocating %zu bytes\n", n);
        exit(2);
    }
    return p;
}

static void *xcalloc(size_t nmemb, size_t size) {
    void *p = calloc(nmemb ? nmemb : 1, size ? size : 1);
    if (!p) {
        fprintf(stderr, "xref_fast: out of memory calloc %zu x %zu\n", nmemb, size);
        exit(2);
    }
    return p;
}

static void *xrealloc(void *ptr, size_t n) {
    void *p = realloc(ptr, n ? n : 1);
    if (!p) {
        fprintf(stderr, "xref_fast: out of memory realloc %zu bytes\n", n);
        exit(2);
    }
    return p;
}

/* Growable byte buffer */
typedef struct {
    uint8_t *data;
    size_t len;
    size_t cap;
} buf_t;

static void buf_init(buf_t *b, size_t cap) {
    b->cap = cap ? cap : 256;
    b->data = (uint8_t *)xmalloc(b->cap);
    b->len = 0;
}

static void buf_free(buf_t *b) {
    free(b->data);
    b->data = NULL;
    b->len = 0;
    b->cap = 0;
}

static inline void buf_reserve(buf_t *b, size_t extra) {
    if (b->len + extra > b->cap) {
        size_t ncap = b->cap ? b->cap : 256;
        while (ncap < b->len + extra) {
            ncap = (ncap < (1u << 26)) ? (ncap * 2) : (ncap + (ncap / 2) + extra);
        }
        b->data = (uint8_t *)xrealloc(b->data, ncap);
        b->cap = ncap;
    }
}

static inline void buf_append(buf_t *b, const void *src, size_t n) {
    if (!n) return;
    buf_reserve(b, n);
    memcpy(b->data + b->len, src, n);
    b->len += n;
}

static inline void buf_putc(buf_t *b, uint8_t c) {
    buf_reserve(b, 1);
    b->data[b->len++] = c;
}

static uint64_t pool_add_sanitized(buf_t *pool, const char *s, size_t slen) {
    uint64_t off = (uint64_t)pool->len;
    buf_reserve(pool, slen + 1);
    uint8_t *dst = pool->data + pool->len;
    for (size_t i = 0; i < slen; i++) {
        unsigned char c = (unsigned char)s[i];
        if (c == '\t' || c == '\n' || c == '\r') {
            dst[i] = ' ';
        } else {
            dst[i] = c;
        }
    }
    dst[slen] = 0;
    pool->len += slen + 1;
    return off;
}

/* UTF-16 code-unit comparator matching JS `a < b ? -1 : a > b ? 1 : 0` */
typedef struct {
    const unsigned char *p;
    uint16_t pending_low;
} utf16_iter_t;

static inline int utf16_next(utf16_iter_t *it) {
    if (it->pending_low) {
        uint16_t v = it->pending_low;
        it->pending_low = 0;
        return (int)v;
    }
    unsigned char b0 = *it->p;
    if (b0 == 0) return -1;
    if (b0 < 0x80) {
        it->p += 1;
        return (int)b0;
    }
    uint32_t cp = 0;
    if ((b0 & 0xE0) == 0xC0 && it->p[1]) {
        cp = ((uint32_t)(b0 & 0x1F) << 6) | (uint32_t)(it->p[1] & 0x3F);
        it->p += 2;
    } else if ((b0 & 0xF0) == 0xE0 && it->p[1] && it->p[2]) {
        cp = ((uint32_t)(b0 & 0x0F) << 12) |
             ((uint32_t)(it->p[1] & 0x3F) << 6) |
             (uint32_t)(it->p[2] & 0x3F);
        it->p += 3;
    } else if ((b0 & 0xF8) == 0xF0 && it->p[1] && it->p[2] && it->p[3]) {
        cp = ((uint32_t)(b0 & 0x07) << 18) |
             ((uint32_t)(it->p[1] & 0x3F) << 12) |
             ((uint32_t)(it->p[2] & 0x3F) << 6) |
             (uint32_t)(it->p[3] & 0x3F);
        it->p += 4;
    } else {
        it->p += 1;
        return (int)b0;
    }
    if (cp <= 0xFFFFu) {
        return (int)cp;
    }
    cp -= 0x10000u;
    it->pending_low = (uint16_t)(0xDC00u + (cp & 0x3FFu));
    return (int)(0xD800u + (cp >> 10));
}

static int cmp_utf16(const char *a, const char *b) {
    const unsigned char *pa = (const unsigned char *)a;
    const unsigned char *pb = (const unsigned char *)b;
    while (*pa && *pb && *pa < 0x80 && *pb < 0x80) {
        if (*pa != *pb) return (*pa < *pb) ? -1 : 1;
        pa++;
        pb++;
    }
    if (*pa == 0 && *pb == 0) return 0;
    if (*pa == 0) return -1;
    if (*pb == 0) return 1;
    utf16_iter_t ia = { pa, 0 };
    utf16_iter_t ib = { pb, 0 };
    for (;;) {
        int ca = utf16_next(&ia);
        int cb = utf16_next(&ib);
        if (ca != cb) return (ca < cb) ? -1 : 1;
        if (ca == -1) return 0;
    }
}

static int cmp_cstr_ptr(const void *a, const void *b) {
    const char *sa = *(const char *const *)a;
    const char *sb = *(const char *const *)b;
    return strcmp(sa, sb);
}

/* Global context for single-threaded qsort of declaration IDs by UTF-16 name */
static const uint8_t *g_name_pool_data = NULL;
static const uint64_t *g_name_offsets = NULL;

static int cmp_decl_by_name_utf16(const void *a, const void *b) {
    uint32_t ia = *(const uint32_t *)a;
    uint32_t ib = *(const uint32_t *)b;
    const char *sa = (const char *)(g_name_pool_data + g_name_offsets[ia]);
    const char *sb = (const char *)(g_name_pool_data + g_name_offsets[ib]);
    int c = cmp_utf16(sa, sb);
    if (c != 0) return c;
    return (ia < ib) ? -1 : (ia > ib ? 1 : 0);
}

static int mkdir_p(const char *path) {
    char tmp[4096];
    size_t len = strlen(path);
    if (len == 0 || len >= sizeof(tmp)) return -1;
    memcpy(tmp, path, len + 1);
    while (len > 1 && tmp[len - 1] == '/') {
        tmp[--len] = '\0';
    }
    for (char *p = tmp + 1; *p; p++) {
        if (*p == '/') {
            *p = '\0';
            if (mkdir(tmp, 0755) != 0 && errno != EEXIST) return -1;
            *p = '/';
        }
    }
    if (mkdir(tmp, 0755) != 0 && errno != EEXIST) return -1;
    return 0;
}

static int write_gzip9_file(const char *path, const uint8_t *raw, size_t raw_len, uint64_t *out_bytes) {
    z_stream zs;
    memset(&zs, 0, sizeof(zs));
    int rc = deflateInit2(&zs, Z_BEST_COMPRESSION, Z_DEFLATED, 15 + 16, 8, Z_DEFAULT_STRATEGY);
    if (rc != Z_OK) {
        fprintf(stderr, "xref_fast: deflateInit2 failed (%d) for %s\n", rc, path);
        return -1;
    }
    gz_header hdr;
    memset(&hdr, 0, sizeof(hdr));
    hdr.os = 3; /* Unix, deterministic mtime=0 */
    deflateSetHeader(&zs, &hdr);

    uLong bound = deflateBound(&zs, (uLong)raw_len) + 64u;
    uint8_t *out = (uint8_t *)xmalloc((size_t)bound);

    zs.next_in = (Bytef *)(uintptr_t)raw;
    zs.avail_in = (uInt)raw_len;
    /* Handle >4GB defensively (never happens for a shard, but clean) */
    if ((size_t)zs.avail_in != raw_len) {
        deflateEnd(&zs);
        free(out);
        fprintf(stderr, "xref_fast: shard raw_len overflow for %s\n", path);
        return -1;
    }

    size_t out_cap = (size_t)bound;
    size_t out_pos = 0;
    for (;;) {
        zs.next_out = out + out_pos;
        size_t avail = out_cap - out_pos;
        zs.avail_out = (avail > 0x7FFFFFFFu) ? 0x7FFFFFFFu : (uInt)avail;
        rc = deflate(&zs, Z_FINISH);
        out_pos = out_cap - (size_t)zs.avail_out;
        if (rc == Z_STREAM_END) {
            break;
        }
        if (rc != Z_OK && rc != Z_BUF_ERROR) {
            fprintf(stderr, "xref_fast: deflate failed (%d) for %s\n", rc, path);
            deflateEnd(&zs);
            free(out);
            return -1;
        }
        out_cap = out_cap * 2 + 1024;
        out = (uint8_t *)xrealloc(out, out_cap);
    }
    size_t total_out = (size_t)zs.total_out;
    deflateEnd(&zs);

    FILE *fp = fopen(path, "wb");
    if (!fp) {
        fprintf(stderr, "xref_fast: cannot open %s for writing: %s\n", path, strerror(errno));
        free(out);
        return -1;
    }
    if (total_out > 0 && fwrite(out, 1, total_out, fp) != total_out) {
        fprintf(stderr, "xref_fast: write failed for %s: %s\n", path, strerror(errno));
        fclose(fp);
        free(out);
        return -1;
    }
    if (fclose(fp) != 0) {
        fprintf(stderr, "xref_fast: close failed for %s: %s\n", path, strerror(errno));
        free(out);
        return -1;
    }
    free(out);
    if (out_bytes) *out_bytes = (uint64_t)total_out;
    return 0;
}

static inline void put_u16_le(uint8_t *p, uint16_t v) {
    p[0] = (uint8_t)(v & 0xFFu);
    p[1] = (uint8_t)((v >> 8) & 0xFFu);
}

static inline void put_u32_le(uint8_t *p, uint32_t v) {
    p[0] = (uint8_t)(v & 0xFFu);
    p[1] = (uint8_t)((v >> 8) & 0xFFu);
    p[2] = (uint8_t)((v >> 16) & 0xFFu);
    p[3] = (uint8_t)((v >> 24) & 0xFFu);
}

static inline uint8_t *put_uleb128(uint8_t *p, uint32_t v) {
    while (v >= 0x80u) {
        *p++ = (uint8_t)((v & 0x7Fu) | 0x80u);
        v >>= 7;
    }
    *p++ = (uint8_t)v;
    return p;
}

/* Encode one LXRF v1 adjacency shard (dir=0 fwd, 1 rev, 2 rev_hub) and write gzip-9 */
static int encode_and_write_adj_shard(
    const char *path,
    uint8_t dir,
    uint32_t start_id,
    uint32_t count,
    const uint64_t *offsets,
    const uint32_t *targets,
    const uint8_t *kinds,
    uint32_t hub_threshold,
    uint64_t *out_bytes
) {
    uint64_t total_edges = 0;
    for (uint32_t i = 0; i < count; i++) {
        uint32_t id = start_id + i;
        uint64_t deg = offsets[id + 1] - offsets[id];
        if (dir == DIR_REV && deg >= (uint64_t)hub_threshold) {
            continue;
        }
        total_edges += deg;
    }

    size_t kind_bytes = (size_t)((total_edges + 3u) >> 2);
    size_t max_raw = 16u + (size_t)count * 4u + (size_t)total_edges * 5u + kind_bytes;
    uint8_t *raw = (uint8_t *)xmalloc(max_raw);

    /* 16-byte LE header */
    raw[0] = 'L'; raw[1] = 'X'; raw[2] = 'R'; raw[3] = 'F';
    raw[4] = (uint8_t)LXRF_VERSION;
    raw[5] = dir;
    put_u16_le(raw + 6, 0u);
    put_u32_le(raw + 8, start_id);
    put_u32_le(raw + 12, count);

    /* Degree table */
    uint8_t *p = raw + 16;
    for (uint32_t i = 0; i < count; i++) {
        uint32_t id = start_id + i;
        uint32_t deg = (uint32_t)(offsets[id + 1] - offsets[id]);
        if (dir == DIR_REV && deg >= hub_threshold) {
            put_u32_le(p, HUB_SENTINEL);
        } else {
            put_u32_le(p, deg);
        }
        p += 4;
    }

    /* Stream 1: LEB128 target deltas */
    for (uint32_t i = 0; i < count; i++) {
        uint32_t id = start_id + i;
        uint64_t s = offsets[id];
        uint64_t e = offsets[id + 1];
        uint64_t deg = e - s;
        if (deg == 0 || (dir == DIR_REV && deg >= (uint64_t)hub_threshold)) {
            continue;
        }
        uint32_t prev = targets[s];
        p = put_uleb128(p, prev);
        for (uint64_t k = s + 1; k < e; k++) {
            uint32_t cur = targets[k];
            if (cur <= prev) {
                fprintf(stderr, "xref_fast: non-ascending target in dir=%u id=%u (%u <= %u)\n",
                        (unsigned)dir, id, cur, prev);
                free(raw);
                return -1;
            }
            p = put_uleb128(p, cur - prev - 1u);
            prev = cur;
        }
    }

    /* Stream 2: 2-bit packed kinds, LSB-first */
    if (kind_bytes > 0) {
        memset(p, 0, kind_bytes);
        uint64_t edge_idx = 0;
        for (uint32_t i = 0; i < count; i++) {
            uint32_t id = start_id + i;
            uint64_t s = offsets[id];
            uint64_t e = offsets[id + 1];
            uint64_t deg = e - s;
            if (deg == 0 || (dir == DIR_REV && deg >= (uint64_t)hub_threshold)) {
                continue;
            }
            for (uint64_t k = s; k < e; k++) {
                uint8_t kd = kinds[k] & 3u;
                p[edge_idx >> 2] |= (uint8_t)(kd << ((edge_idx & 3u) * 2u));
                edge_idx++;
            }
        }
        p += kind_bytes;
    }

    size_t raw_len = (size_t)(p - raw);
    int rc = write_gzip9_file(path, raw, raw_len, out_bytes);
    free(raw);
    return rc;
}

static int table_exists(sqlite3 *db, const char *name) {
    sqlite3_stmt *st = NULL;
    const char *sql = "SELECT 1 FROM sqlite_master WHERE type='table' AND name=? LIMIT 1";
    if (sqlite3_prepare_v2(db, sql, -1, &st, NULL) != SQLITE_OK) return 0;
    sqlite3_bind_text(st, 1, name, -1, SQLITE_STATIC);
    int found = (sqlite3_step(st) == SQLITE_ROW) ? 1 : 0;
    sqlite3_finalize(st);
    return found;
}

static void json_write_escaped(FILE *fp, const char *s) {
    fputc('"', fp);
    for (const unsigned char *p = (const unsigned char *)s; *p; p++) {
        unsigned char c = *p;
        switch (c) {
            case '"':  fputs("\\\"", fp); break;
            case '\\': fputs("\\\\", fp); break;
            case '\b': fputs("\\b", fp); break;
            case '\f': fputs("\\f", fp); break;
            case '\n': fputs("\\n", fp); break;
            case '\r': fputs("\\r", fp); break;
            case '\t': fputs("\\t", fp); break;
            default:
                if (c < 0x20u) {
                    fprintf(fp, "\\u%04x", (unsigned)c);
                } else {
                    fputc((int)c, fp);
                }
                break;
        }
    }
    fputc('"', fp);
}

typedef struct {
    int64_t id;
    int32_t line_no;
} src_line_pair_t;

static int32_t lookup_src_line(const src_line_pair_t *arr, size_t n, int64_t key) {
    size_t lo = 0, hi = n;
    while (lo < hi) {
        size_t mid = lo + ((hi - lo) >> 1);
        if (arr[mid].id < key) {
            lo = mid + 1;
        } else if (arr[mid].id > key) {
            hi = mid;
        } else {
            return arr[mid].line_no;
        }
    }
    return 0;
}

static int32_t find_cstr(const char *const *arr, size_t n, const char *key) {
    size_t lo = 0, hi = n;
    while (lo < hi) {
        size_t mid = lo + ((hi - lo) >> 1);
        int c = strcmp(arr[mid], key);
        if (c < 0) lo = mid + 1;
        else if (c > 0) hi = mid;
        else return (int32_t)mid;
    }
    return -1;
}

static void usage(void) {
    fprintf(stderr,
        "Usage: xref_fast --kernel-db <path> --out-dir <dir> [options]\n"
        "  --leanre-db <path>        Optional leanre.db for source line numbers\n"
        "  --shard-size <int>        Adjacency shard size (default 4096)\n"
        "  --meta-shard-size <int>   Meta shard size (default 16384)\n"
        "  --name-shards <int>       Sorted name shards (0 = auto, default 0)\n"
        "  --hub-threshold <int>     Reverse mega-hub split threshold (default 16384)\n"
        "  --threads <int>           OpenMP thread count (0 = auto)\n"
        "  --quiet                   Suppress progress logs\n"
    );
}

int main(int argc, char **argv) {
    const char *kernel_db_path = NULL;
    const char *leanre_db_path = NULL;
    const char *out_dir = NULL;
    uint32_t shard_size = 4096;
    uint32_t meta_shard_size = 16384;
    uint32_t req_name_shards = 0; /* 0 = auto */
    uint32_t hub_threshold = 16384;
    int threads = 0;
    int quiet = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--kernel-db") == 0 && i + 1 < argc) {
            kernel_db_path = argv[++i];
        } else if (strcmp(argv[i], "--leanre-db") == 0 && i + 1 < argc) {
            leanre_db_path = argv[++i];
        } else if (strcmp(argv[i], "--out-dir") == 0 && i + 1 < argc) {
            out_dir = argv[++i];
        } else if (strcmp(argv[i], "--shard-size") == 0 && i + 1 < argc) {
            shard_size = (uint32_t)strtoul(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "--meta-shard-size") == 0 && i + 1 < argc) {
            meta_shard_size = (uint32_t)strtoul(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "--name-shards") == 0 && i + 1 < argc) {
            req_name_shards = (uint32_t)strtoul(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "--hub-threshold") == 0 && i + 1 < argc) {
            hub_threshold = (uint32_t)strtoul(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "--threads") == 0 && i + 1 < argc) {
            threads = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--quiet") == 0) {
            quiet = 1;
        } else {
            usage();
            return 2;
        }
    }

    if (!kernel_db_path || !out_dir || shard_size == 0 || meta_shard_size == 0) {
        usage();
        return 2;
    }

    if (threads <= 0) {
        int max_t = omp_get_max_threads();
        threads = (max_t > 64) ? 64 : max_t;
    }
    omp_set_num_threads(threads);

    double t0 = now_sec();

    /* Open kernel.db strictly read-only */
    sqlite3 *kdb = NULL;
    if (sqlite3_open_v2(kernel_db_path, &kdb, SQLITE_OPEN_READONLY, NULL) != SQLITE_OK) {
        fprintf(stderr, "xref_fast: cannot open kernel.db %s: %s\n",
                kernel_db_path, kdb ? sqlite3_errmsg(kdb) : "oom");
        if (kdb) sqlite3_close(kdb);
        return 1;
    }
    sqlite3_exec(kdb, "PRAGMA query_only=1; PRAGMA mmap_size=2147483648; PRAGMA cache_size=-262144;", NULL, NULL, NULL);

    /* Query declaration count & edge count hint */
    uint32_t n_decls = 0;
    uint64_t edge_hint = 0;
    {
        sqlite3_stmt *st = NULL;
        if (sqlite3_prepare_v2(kdb, "SELECT COUNT(*), COALESCE(SUM(fan_out), 0) FROM decls", -1, &st, NULL) != SQLITE_OK) {
            fprintf(stderr, "xref_fast: failed counting decls: %s\n", sqlite3_errmsg(kdb));
            sqlite3_close(kdb);
            return 1;
        }
        if (sqlite3_step(st) == SQLITE_ROW) {
            n_decls = (uint32_t)sqlite3_column_int64(st, 0);
            edge_hint = (uint64_t)sqlite3_column_int64(st, 1);
        }
        sqlite3_finalize(st);
    }

    /* Load distinct sorted kind labels */
    char **kind_labels = NULL;
    size_t n_kinds = 0;
    {
        sqlite3_stmt *st = NULL;
        if (sqlite3_prepare_v2(kdb, "SELECT DISTINCT kind FROM decls ORDER BY kind", -1, &st, NULL) != SQLITE_OK) {
            fprintf(stderr, "xref_fast: failed querying kinds: %s\n", sqlite3_errmsg(kdb));
            sqlite3_close(kdb);
            return 1;
        }
        size_t cap = 16;
        kind_labels = (char **)xmalloc(cap * sizeof(char *));
        while (sqlite3_step(st) == SQLITE_ROW) {
            const char *s = (const char *)sqlite3_column_text(st, 0);
            if (!s) s = "";
            if (n_kinds == cap) {
                cap *= 2;
                kind_labels = (char **)xrealloc(kind_labels, cap * sizeof(char *));
            }
            kind_labels[n_kinds++] = strdup(s);
        }
        sqlite3_finalize(st);
        if (n_kinds > 1) {
            qsort(kind_labels, n_kinds, sizeof(char *), cmp_cstr_ptr);
        }
    }

    /* Allocate declaration metadata arrays */
    buf_t name_pool;
    buf_init(&name_pool, (size_t)n_decls * 48u + 1024u);
    uint64_t *name_off = (uint64_t *)xcalloc(n_decls, sizeof(uint64_t));
    uint16_t *kind_idx = (uint16_t *)xcalloc(n_decls, sizeof(uint16_t));
    uint32_t *live_mask = (uint32_t *)xcalloc(n_decls, sizeof(uint32_t));
    uint32_t *type_nodes = (uint32_t *)xcalloc(n_decls, sizeof(uint32_t));
    uint32_t *value_nodes = (uint32_t *)xcalloc(n_decls, sizeof(uint32_t));
    uint32_t *dom_size = (uint32_t *)xcalloc(n_decls, sizeof(uint32_t));
    int32_t *mod_idx = (int32_t *)xmalloc((n_decls ? n_decls : 1) * sizeof(int32_t));
    int32_t *line_no = (int32_t *)xcalloc(n_decls, sizeof(int32_t));
    for (uint32_t i = 0; i < n_decls; i++) mod_idx[i] = -1;

    /* Load decls */
    {
        sqlite3_stmt *st = NULL;
        const char *sql =
            "SELECT id, name, kind, live_mask, type_nodes, value_nodes "
            "FROM decls ORDER BY id";
        if (sqlite3_prepare_v2(kdb, sql, -1, &st, NULL) != SQLITE_OK) {
            fprintf(stderr, "xref_fast: failed preparing decls query: %s\n", sqlite3_errmsg(kdb));
            sqlite3_close(kdb);
            return 1;
        }
        uint32_t expected = 0;
        while (sqlite3_step(st) == SQLITE_ROW) {
            int64_t id = sqlite3_column_int64(st, 0);
            if (id != (int64_t)expected || expected >= n_decls) {
                fprintf(stderr, "xref_fast: decls.id must be contiguous 0..N-1 (got %" PRId64 ", expected %u)\n",
                        id, expected);
                sqlite3_finalize(st);
                sqlite3_close(kdb);
                return 1;
            }
            const char *nm = (const char *)sqlite3_column_text(st, 1);
            int nm_len = sqlite3_column_bytes(st, 1);
            if (!nm) { nm = ""; nm_len = 0; }
            name_off[expected] = pool_add_sanitized(&name_pool, nm, (size_t)nm_len);

            const char *kd = (const char *)sqlite3_column_text(st, 2);
            if (!kd) kd = "";
            int32_t kidx = find_cstr((const char *const *)kind_labels, n_kinds, kd);
            kind_idx[expected] = (kidx >= 0) ? (uint16_t)kidx : 0u;

            live_mask[expected] = (uint32_t)sqlite3_column_int64(st, 3);
            type_nodes[expected] = (uint32_t)sqlite3_column_int64(st, 4);
            value_nodes[expected] = (uint32_t)sqlite3_column_int64(st, 5);
            expected++;
        }
        sqlite3_finalize(st);
        if (expected != n_decls) {
            fprintf(stderr, "xref_fast: decl count mismatch (%u vs %u)\n", expected, n_decls);
            sqlite3_close(kdb);
            return 1;
        }
    }

    /* Optional dom table (tree_id=0) */
    if (table_exists(kdb, "dom")) {
        sqlite3_stmt *st = NULL;
        if (sqlite3_prepare_v2(kdb, "SELECT decl_id, subtree_size FROM dom WHERE tree_id = 0", -1, &st, NULL) == SQLITE_OK) {
            while (sqlite3_step(st) == SQLITE_ROW) {
                int64_t did = sqlite3_column_int64(st, 0);
                int64_t sz = sqlite3_column_int64(st, 1);
                if (did >= 0 && (uint64_t)did < n_decls && sz >= 0) {
                    dom_size[did] = (uint32_t)sz;
                }
            }
            sqlite3_finalize(st);
        }
    }

    /* Optional leanre.db declarations(id, line_no) for source line numbers */
    src_line_pair_t *src_lines = NULL;
    size_t n_src_lines = 0;
    if (leanre_db_path && leanre_db_path[0] != '\0') {
        sqlite3 *ldb = NULL;
        if (sqlite3_open_v2(leanre_db_path, &ldb, SQLITE_OPEN_READONLY, NULL) != SQLITE_OK) {
            fprintf(stderr, "xref_fast: cannot open leanre.db %s: %s\n",
                    leanre_db_path, ldb ? sqlite3_errmsg(ldb) : "oom");
            if (ldb) sqlite3_close(ldb);
            sqlite3_close(kdb);
            return 1;
        }
        sqlite3_exec(ldb, "PRAGMA query_only=1; PRAGMA mmap_size=536870912;", NULL, NULL, NULL);
        if (table_exists(ldb, "declarations")) {
            sqlite3_stmt *st = NULL;
            size_t cap = 65536;
            src_lines = (src_line_pair_t *)xmalloc(cap * sizeof(src_line_pair_t));
            if (sqlite3_prepare_v2(ldb, "SELECT id, line_no FROM declarations ORDER BY id", -1, &st, NULL) == SQLITE_OK) {
                while (sqlite3_step(st) == SQLITE_ROW) {
                    if (n_src_lines == cap) {
                        cap *= 2;
                        src_lines = (src_line_pair_t *)xrealloc(src_lines, cap * sizeof(src_line_pair_t));
                    }
                    src_lines[n_src_lines].id = sqlite3_column_int64(st, 0);
                    src_lines[n_src_lines].line_no = (int32_t)sqlite3_column_int64(st, 1);
                    n_src_lines++;
                }
                sqlite3_finalize(st);
            }
        }
        sqlite3_close(ldb);
    }

    /* Optional decl_module table -> unique sorted modules + mod_idx + line_no */
    char **modules = NULL;
    size_t n_modules = 0;
    if (table_exists(kdb, "decl_module")) {
        /* Pass 1: distinct sorted non-empty module names */
        sqlite3_stmt *st = NULL;
        if (sqlite3_prepare_v2(
                kdb,
                "SELECT DISTINCT module FROM decl_module WHERE module IS NOT NULL AND module != '' ORDER BY module",
                -1, &st, NULL) == SQLITE_OK) {
            size_t cap = 1024;
            modules = (char **)xmalloc(cap * sizeof(char *));
            while (sqlite3_step(st) == SQLITE_ROW) {
                const char *m = (const char *)sqlite3_column_text(st, 0);
                if (!m || !m[0]) continue;
                if (n_modules == cap) {
                    cap *= 2;
                    modules = (char **)xrealloc(modules, cap * sizeof(char *));
                }
                modules[n_modules++] = strdup(m);
            }
            sqlite3_finalize(st);
            if (n_modules > 1) {
                qsort(modules, n_modules, sizeof(char *), cmp_cstr_ptr);
            }
        }
        /* Pass 2: assign mod_idx and line_no */
        if (sqlite3_prepare_v2(kdb, "SELECT decl_id, module, src_decl_id FROM decl_module", -1, &st, NULL) == SQLITE_OK) {
            while (sqlite3_step(st) == SQLITE_ROW) {
                int64_t did = sqlite3_column_int64(st, 0);
                if (did < 0 || (uint64_t)did >= n_decls) continue;
                if (sqlite3_column_type(st, 1) != SQLITE_NULL) {
                    const char *m = (const char *)sqlite3_column_text(st, 1);
                    if (m && m[0]) {
                        mod_idx[did] = find_cstr((const char *const *)modules, n_modules, m);
                    }
                }
                if (n_src_lines > 0 && sqlite3_column_type(st, 2) != SQLITE_NULL) {
                    int64_t sid = sqlite3_column_int64(st, 2);
                    line_no[did] = lookup_src_line(src_lines, n_src_lines, sid);
                }
            }
            sqlite3_finalize(st);
        }
    }
    free(src_lines);
    src_lines = NULL;

    double t_meta_read = now_sec();
    if (!quiet) {
        fprintf(stderr, "[xref_fast] loaded %u decls, %zu modules in %.2fs\n",
                n_decls, n_modules, t_meta_read - t0);
    }

    /* Stream edges once in (src, dst) PK order -> build fwd CSR directly + count rev degrees */
    uint32_t *fwd_deg = (uint32_t *)xcalloc(n_decls, sizeof(uint32_t));
    uint32_t *fwd_type_deg = (uint32_t *)xcalloc(n_decls, sizeof(uint32_t));
    uint32_t *fwd_val_deg = (uint32_t *)xcalloc(n_decls, sizeof(uint32_t));
    uint32_t *rev_deg = (uint32_t *)xcalloc(n_decls, sizeof(uint32_t));

    uint64_t edge_cap = (edge_hint > 1024u) ? edge_hint : 1024u;
    uint32_t *fwd_dst = (uint32_t *)xmalloc((size_t)edge_cap * sizeof(uint32_t));
    uint8_t *fwd_kind = (uint8_t *)xmalloc((size_t)edge_cap * sizeof(uint8_t));
    uint64_t n_edges = 0;
    uint64_t kind_counts[4] = { 0, 0, 0, 0 };

    {
        sqlite3_stmt *st = NULL;
        if (sqlite3_prepare_v2(kdb, "SELECT src, dst, kind FROM edges ORDER BY src, dst", -1, &st, NULL) != SQLITE_OK) {
            fprintf(stderr, "xref_fast: failed preparing edges query: %s\n", sqlite3_errmsg(kdb));
            sqlite3_close(kdb);
            return 1;
        }
        int64_t prev_src = -1;
        int64_t prev_dst = -1;
        while (sqlite3_step(st) == SQLITE_ROW) {
            int64_t s = sqlite3_column_int64(st, 0);
            int64_t d = sqlite3_column_int64(st, 1);
            int k = sqlite3_column_int(st, 2);
            if (s < 0 || (uint64_t)s >= n_decls || d < 0 || (uint64_t)d >= n_decls) {
                fprintf(stderr, "xref_fast: edge out of bounds (%" PRId64 " -> %" PRId64 ")\n", s, d);
                sqlite3_finalize(st);
                sqlite3_close(kdb);
                return 1;
            }
            if (k < 1 || k > 3) {
                fprintf(stderr, "xref_fast: invalid edge kind %d for (%" PRId64 " -> %" PRId64 ")\n", k, s, d);
                sqlite3_finalize(st);
                sqlite3_close(kdb);
                return 1;
            }
            if (s < prev_src || (s == prev_src && d <= prev_dst)) {
                fprintf(stderr, "xref_fast: duplicate or unsorted edge (%" PRId64 ", %" PRId64 ")\n", s, d);
                sqlite3_finalize(st);
                sqlite3_close(kdb);
                return 1;
            }
            prev_src = s;
            prev_dst = d;

            if (n_edges == edge_cap) {
                edge_cap = edge_cap + (edge_cap >> 1) + 1024u;
                fwd_dst = (uint32_t *)xrealloc(fwd_dst, (size_t)edge_cap * sizeof(uint32_t));
                fwd_kind = (uint8_t *)xrealloc(fwd_kind, (size_t)edge_cap * sizeof(uint8_t));
            }
            fwd_dst[n_edges] = (uint32_t)d;
            fwd_kind[n_edges] = (uint8_t)k;
            n_edges++;

            fwd_deg[s]++;
            if (k & 1) fwd_type_deg[s]++;
            if (k & 2) fwd_val_deg[s]++;
            rev_deg[d]++;
            kind_counts[k]++;
        }
        sqlite3_finalize(st);
    }
    sqlite3_close(kdb);
    kdb = NULL;

    double t_edges_read = now_sec();
    if (!quiet) {
        fprintf(stderr, "[xref_fast] streamed %" PRIu64 " edges (type=%" PRIu64 ", value=%" PRIu64 ", both=%" PRIu64 ") in %.2fs\n",
                n_edges, kind_counts[1], kind_counts[2], kind_counts[3], t_edges_read - t_meta_read);
    }

    /* Build CSR offsets */
    uint64_t *fwd_off = (uint64_t *)xmalloc(((size_t)n_decls + 1u) * sizeof(uint64_t));
    uint64_t *rev_off = (uint64_t *)xmalloc(((size_t)n_decls + 1u) * sizeof(uint64_t));
    fwd_off[0] = 0;
    rev_off[0] = 0;
    uint32_t n_rev_hubs = 0;
    for (uint32_t i = 0; i < n_decls; i++) {
        fwd_off[i + 1] = fwd_off[i] + fwd_deg[i];
        rev_off[i + 1] = rev_off[i] + rev_deg[i];
        if (rev_deg[i] >= hub_threshold) n_rev_hubs++;
    }
    if (fwd_off[n_decls] != n_edges || rev_off[n_decls] != n_edges) {
        fprintf(stderr, "xref_fast: CSR offset invariant violation\n");
        return 1;
    }

    uint32_t *rev_hub_ids = (uint32_t *)xmalloc((n_rev_hubs ? n_rev_hubs : 1u) * sizeof(uint32_t));
    {
        uint32_t h = 0;
        for (uint32_t i = 0; i < n_decls; i++) {
            if (rev_deg[i] >= hub_threshold) rev_hub_ids[h++] = i;
        }
    }

    /* Transpose fwd -> rev sequentially in ascending src order (guarantees sorted rev targets!) */
    uint32_t *rev_dst = (uint32_t *)xmalloc((n_edges ? (size_t)n_edges : 1u) * sizeof(uint32_t));
    uint8_t *rev_kind = (uint8_t *)xmalloc((n_edges ? (size_t)n_edges : 1u) * sizeof(uint8_t));
    uint64_t *rev_cur = (uint64_t *)xmalloc(((size_t)n_decls + 1u) * sizeof(uint64_t));
    memcpy(rev_cur, rev_off, ((size_t)n_decls + 1u) * sizeof(uint64_t));

    for (uint32_t src = 0; src < n_decls; src++) {
        uint64_t s = fwd_off[src];
        uint64_t e = fwd_off[src + 1];
        for (uint64_t idx = s; idx < e; idx++) {
            uint32_t dst = fwd_dst[idx];
            uint64_t pos = rev_cur[dst]++;
            rev_dst[pos] = src;
            rev_kind[pos] = fwd_kind[idx];
        }
    }
    free(rev_cur);
    rev_cur = NULL;

    double t_transpose = now_sec();
    if (!quiet) {
        fprintf(stderr, "[xref_fast] built rev CSR (%u mega-hubs >= %u) in %.2fs\n",
                n_rev_hubs, hub_threshold, t_transpose - t_edges_read);
    }

    /* Sort declaration IDs by UTF-16 code-unit name order */
    uint32_t *sorted_ids = (uint32_t *)xmalloc((n_decls ? n_decls : 1u) * sizeof(uint32_t));
    for (uint32_t i = 0; i < n_decls; i++) sorted_ids[i] = i;
    if (n_decls > 1) {
        g_name_pool_data = name_pool.data;
        g_name_offsets = name_off;
        qsort(sorted_ids, n_decls, sizeof(uint32_t), cmp_decl_by_name_utf16);
    }

    double t_sort = now_sec();
    if (!quiet) {
        fprintf(stderr, "[xref_fast] sorted %u names (UTF-16 order) in %.2fs\n",
                n_decls, t_sort - t_transpose);
    }

    /* Create output directories */
    char sub_path[4096];
    const char *subdirs[5] = { "fwd", "rev", "rev_hub", "meta", "names" };
    if (mkdir_p(out_dir) != 0) {
        fprintf(stderr, "xref_fast: cannot create %s\n", out_dir);
        return 1;
    }
    for (int i = 0; i < 5; i++) {
        snprintf(sub_path, sizeof(sub_path), "%s/%s", out_dir, subdirs[i]);
        if (mkdir_p(sub_path) != 0) {
            fprintf(stderr, "xref_fast: cannot create %s\n", sub_path);
            return 1;
        }
    }

    uint32_t n_shards = (n_decls > 0) ? ((n_decls + shard_size - 1u) / shard_size) : 0u;
    uint32_t n_meta_shards = (n_decls > 0) ? ((n_decls + meta_shard_size - 1u) / meta_shard_size) : 0u;
    uint32_t n_name_shards = 0;
    if (n_decls > 0) {
        if (req_name_shards == 0) {
            uint32_t auto_n = (n_decls + 255u) / 256u;
            n_name_shards = (auto_n > 256u) ? 256u : (auto_n < 1u ? 1u : auto_n);
        } else {
            n_name_shards = (req_name_shards > n_decls) ? n_decls : req_name_shards;
        }
    }

    /* Write modules.lxrf */
    uint64_t modules_bytes = 0;
    {
        buf_t mb;
        buf_init(&mb, n_modules * 48u + 64u);
        for (size_t i = 0; i < n_modules; i++) {
            size_t ml = strlen(modules[i]);
            buf_append(&mb, modules[i], ml);
            buf_putc(&mb, '\n');
        }
        snprintf(sub_path, sizeof(sub_path), "%s/modules.lxrf", out_dir);
        if (write_gzip9_file(sub_path, mb.data, mb.len, &modules_bytes) != 0) {
            buf_free(&mb);
            return 1;
        }
        buf_free(&mb);
    }

    /* Per-shard byte counts for exact stats */
    uint64_t *fwd_sizes = (uint64_t *)xcalloc(n_shards, sizeof(uint64_t));
    uint64_t *rev_sizes = (uint64_t *)xcalloc(n_shards, sizeof(uint64_t));
    uint64_t *hub_sizes = (uint64_t *)xcalloc(n_rev_hubs, sizeof(uint64_t));
    uint64_t *meta_sizes = (uint64_t *)xcalloc(n_meta_shards, sizeof(uint64_t));
    uint64_t *name_sizes = (uint64_t *)xcalloc(n_name_shards, sizeof(uint64_t));

    int any_err = 0;

    /* Parallel write: fwd shards */
    #pragma omp parallel for schedule(dynamic, 1) reduction(|:any_err)
    for (uint32_t s = 0; s < n_shards; s++) {
        char pbuf[4096];
        uint32_t start_id = s * shard_size;
        uint32_t cnt = (start_id + shard_size <= n_decls) ? shard_size : (n_decls - start_id);
        snprintf(pbuf, sizeof(pbuf), "%s/fwd/%u.lxrf", out_dir, s);
        if (encode_and_write_adj_shard(pbuf, DIR_FWD, start_id, cnt,
                                       fwd_off, fwd_dst, fwd_kind, hub_threshold,
                                       &fwd_sizes[s]) != 0) {
            any_err = 1;
        }
    }

    /* Parallel write: rev shards */
    #pragma omp parallel for schedule(dynamic, 1) reduction(|:any_err)
    for (uint32_t s = 0; s < n_shards; s++) {
        char pbuf[4096];
        uint32_t start_id = s * shard_size;
        uint32_t cnt = (start_id + shard_size <= n_decls) ? shard_size : (n_decls - start_id);
        snprintf(pbuf, sizeof(pbuf), "%s/rev/%u.lxrf", out_dir, s);
        if (encode_and_write_adj_shard(pbuf, DIR_REV, start_id, cnt,
                                       rev_off, rev_dst, rev_kind, hub_threshold,
                                       &rev_sizes[s]) != 0) {
            any_err = 1;
        }
    }

    /* Parallel write: rev_hub shards */
    #pragma omp parallel for schedule(dynamic, 1) reduction(|:any_err)
    for (uint32_t h = 0; h < n_rev_hubs; h++) {
        char pbuf[4096];
        uint32_t did = rev_hub_ids[h];
        snprintf(pbuf, sizeof(pbuf), "%s/rev_hub/%u.lxrf", out_dir, did);
        if (encode_and_write_adj_shard(pbuf, DIR_REV_HUB, did, 1u,
                                       rev_off, rev_dst, rev_kind, hub_threshold,
                                       &hub_sizes[h]) != 0) {
            any_err = 1;
        }
    }

    /* Parallel write: meta shards */
    #pragma omp parallel for schedule(dynamic, 1) reduction(|:any_err)
    for (uint32_t m = 0; m < n_meta_shards; m++) {
        char pbuf[4096];
        uint32_t start_id = m * meta_shard_size;
        uint32_t cnt = (start_id + meta_shard_size <= n_decls) ? meta_shard_size : (n_decls - start_id);
        buf_t tb;
        buf_init(&tb, (size_t)cnt * 80u + 256u);
        char line[256];
        for (uint32_t i = 0; i < cnt; i++) {
            uint32_t id = start_id + i;
            const char *nm = (const char *)(name_pool.data + name_off[id]);
            buf_append(&tb, nm, strlen(nm));
            int n = snprintf(
                line, sizeof(line),
                "\t%u\t%u\t%u\t%u\t%u\t%d\t%d\t%u\t%u\t%u\t%u\n",
                (unsigned)kind_idx[id],
                rev_deg[id],
                fwd_deg[id],
                fwd_type_deg[id],
                fwd_val_deg[id],
                mod_idx[id],
                line_no[id],
                live_mask[id],
                dom_size[id],
                type_nodes[id],
                value_nodes[id]
            );
            if (n > 0) buf_append(&tb, line, (size_t)n);
        }
        snprintf(pbuf, sizeof(pbuf), "%s/meta/%u.lxrf", out_dir, m);
        if (write_gzip9_file(pbuf, tb.data, tb.len, &meta_sizes[m]) != 0) {
            any_err = 1;
        }
        buf_free(&tb);
    }

    /* Parallel write: sorted name index shards */
    #pragma omp parallel for schedule(dynamic, 1) reduction(|:any_err)
    for (uint32_t n = 0; n < n_name_shards; n++) {
        char pbuf[4096];
        uint32_t lo = (uint32_t)(((uint64_t)n * n_decls) / n_name_shards);
        uint32_t hi = (uint32_t)(((uint64_t)(n + 1u) * n_decls) / n_name_shards);
        buf_t tb;
        buf_init(&tb, (size_t)(hi - lo) * 64u + 256u);
        char line[192];
        for (uint32_t pos = lo; pos < hi; pos++) {
            uint32_t id = sorted_ids[pos];
            const char *nm = (const char *)(name_pool.data + name_off[id]);
            buf_append(&tb, nm, strlen(nm));
            int w = snprintf(
                line, sizeof(line),
                "\t%u\t%u\t%u\t%u\t%d\t%d\n",
                id,
                (unsigned)kind_idx[id],
                rev_deg[id],
                fwd_deg[id],
                mod_idx[id],
                line_no[id]
            );
            if (w > 0) buf_append(&tb, line, (size_t)w);
        }
        snprintf(pbuf, sizeof(pbuf), "%s/names/%u.lxrf", out_dir, n);
        if (write_gzip9_file(pbuf, tb.data, tb.len, &name_sizes[n]) != 0) {
            any_err = 1;
        }
        buf_free(&tb);
    }

    if (any_err) {
        fprintf(stderr, "xref_fast: one or more shard writes failed\n");
        return 1;
    }

    /* Compute exact stats across all .lxrf files */
    uint64_t total_bytes = modules_bytes;
    uint64_t file_count = 1u; /* modules.lxrf */
    uint64_t max_shard_bytes = modules_bytes;
    char max_shard_path[256] = "modules.lxrf";

    for (uint32_t s = 0; s < n_shards; s++) {
        total_bytes += fwd_sizes[s];
        file_count++;
        if (fwd_sizes[s] > max_shard_bytes) {
            max_shard_bytes = fwd_sizes[s];
            snprintf(max_shard_path, sizeof(max_shard_path), "fwd/%u.lxrf", s);
        }
    }
    for (uint32_t s = 0; s < n_shards; s++) {
        total_bytes += rev_sizes[s];
        file_count++;
        if (rev_sizes[s] > max_shard_bytes) {
            max_shard_bytes = rev_sizes[s];
            snprintf(max_shard_path, sizeof(max_shard_path), "rev/%u.lxrf", s);
        }
    }
    for (uint32_t h = 0; h < n_rev_hubs; h++) {
        total_bytes += hub_sizes[h];
        file_count++;
        if (hub_sizes[h] > max_shard_bytes) {
            max_shard_bytes = hub_sizes[h];
            snprintf(max_shard_path, sizeof(max_shard_path), "rev_hub/%u.lxrf", rev_hub_ids[h]);
        }
    }
    for (uint32_t m = 0; m < n_meta_shards; m++) {
        total_bytes += meta_sizes[m];
        file_count++;
        if (meta_sizes[m] > max_shard_bytes) {
            max_shard_bytes = meta_sizes[m];
            snprintf(max_shard_path, sizeof(max_shard_path), "meta/%u.lxrf", m);
        }
    }
    for (uint32_t n = 0; n < n_name_shards; n++) {
        total_bytes += name_sizes[n];
        file_count++;
        if (name_sizes[n] > max_shard_bytes) {
            max_shard_bytes = name_sizes[n];
            snprintf(max_shard_path, sizeof(max_shard_path), "names/%u.lxrf", n);
        }
    }

    /* Write manifest.json */
    snprintf(sub_path, sizeof(sub_path), "%s/manifest.json", out_dir);
    FILE *mf = fopen(sub_path, "wb");
    if (!mf) {
        fprintf(stderr, "xref_fast: cannot open %s for writing\n", sub_path);
        return 1;
    }
    fprintf(mf, "{\n");
    fprintf(mf, "  \"schema\": \"leanre.xrefs/1\",\n");
    fprintf(mf, "  \"mode\": \"kernel\",\n");
    fprintf(mf, "  \"n_decls\": %u,\n", n_decls);
    fprintf(mf, "  \"n_edges\": %" PRIu64 ",\n", n_edges);
    fprintf(mf, "  \"edge_kind_counts\": {\"type\": %" PRIu64 ", \"value\": %" PRIu64 ", \"both\": %" PRIu64 "},\n",
            kind_counts[1], kind_counts[2], kind_counts[3]);
    fprintf(mf, "  \"shard_size\": %u,\n", shard_size);
    fprintf(mf, "  \"n_shards\": %u,\n", n_shards);
    fprintf(mf, "  \"meta_shard_size\": %u,\n", meta_shard_size);
    fprintf(mf, "  \"n_meta_shards\": %u,\n", n_meta_shards);
    fprintf(mf, "  \"name_shards\": %u,\n", n_name_shards);
    fprintf(mf, "  \"name_order\": \"utf16\",\n");
    fprintf(mf, "  \"name_ranges\": [");
    for (uint32_t n = 0; n < n_name_shards; n++) {
        uint32_t lo = (uint32_t)(((uint64_t)n * n_decls) / n_name_shards);
        uint32_t hi = (uint32_t)(((uint64_t)(n + 1u) * n_decls) / n_name_shards);
        const char *first_nm = (const char *)(name_pool.data + name_off[sorted_ids[lo]]);
        const char *last_nm = (const char *)(name_pool.data + name_off[sorted_ids[hi - 1u]]);
        if (n > 0) fputc(',', mf);
        fputc('[', mf);
        json_write_escaped(mf, first_nm);
        fputc(',', mf);
        json_write_escaped(mf, last_nm);
        fprintf(mf, ",%u]", hi - lo);
    }
    fprintf(mf, "],\n");
    fprintf(mf, "  \"hub_threshold\": %u,\n", hub_threshold);
    fprintf(mf, "  \"rev_hub_ids\": [");
    for (uint32_t h = 0; h < n_rev_hubs; h++) {
        if (h > 0) fputc(',', mf);
        fprintf(mf, "%u", rev_hub_ids[h]);
    }
    fprintf(mf, "],\n");
    fprintf(mf, "  \"kind_labels\": [");
    for (size_t k = 0; k < n_kinds; k++) {
        if (k > 0) fputc(',', mf);
        json_write_escaped(mf, kind_labels[k]);
    }
    fprintf(mf, "],\n");
    fprintf(mf, "  \"modules_url\": \"modules.lxrf\",\n");
    fprintf(mf, "  \"n_modules\": %zu,\n", n_modules);
    fprintf(mf, "  \"paths\": {\"fwd\": \"fwd/{s}.lxrf\", \"rev\": \"rev/{s}.lxrf\", \"rev_hub\": \"rev_hub/{id}.lxrf\", \"meta\": \"meta/{m}.lxrf\", \"names\": \"names/{n}.lxrf\"},\n");
    fprintf(mf, "  \"pad\": {\"fwd\": 0, \"rev\": 0, \"rev_hub\": 0, \"meta\": 0, \"names\": 0},\n");
    fprintf(mf, "  \"meta_columns\": [\"name\",\"kind_idx\",\"fan_in\",\"fan_out\",\"fan_out_type\",\"fan_out_value\",\"mod_idx\",\"line_no\",\"live_mask\",\"dom_size\",\"type_nodes\",\"value_nodes\"],\n");
    fprintf(mf, "  \"name_columns\": [\"name\",\"decl_id\",\"kind_idx\",\"fan_in\",\"fan_out\",\"mod_idx\",\"line_no\"],\n");
    fprintf(mf, "  \"stats\": {\"total_bytes\": %" PRIu64 ", \"file_count\": %" PRIu64 ", \"max_shard_bytes\": %" PRIu64 ", \"max_shard_path\": ",
            total_bytes, file_count, max_shard_bytes);
    json_write_escaped(mf, max_shard_path);
    fprintf(mf, "}\n}\n");
    if (fclose(mf) != 0) {
        fprintf(stderr, "xref_fast: failed closing manifest.json\n");
        return 1;
    }

    double t_end = now_sec();
    if (!quiet) {
        fprintf(stderr,
                "[xref_fast] wrote %" PRIu64 " .lxrf files (%.2f MB total, max=%s %.1f KB) in %.2fs total\n",
                file_count, (double)total_bytes / (1024.0 * 1024.0),
                max_shard_path, (double)max_shard_bytes / 1024.0,
                t_end - t0);
    }

    /* Clean up */
    free(fwd_sizes); free(rev_sizes); free(hub_sizes); free(meta_sizes); free(name_sizes);
    free(sorted_ids); free(rev_hub_ids);
    free(rev_dst); free(rev_kind); free(fwd_dst); free(fwd_kind);
    free(fwd_off); free(rev_off);
    free(fwd_deg); free(fwd_type_deg); free(fwd_val_deg); free(rev_deg);
    free(name_off); free(kind_idx); free(live_mask); free(type_nodes); free(value_nodes);
    free(dom_size); free(mod_idx); free(line_no);
    buf_free(&name_pool);
    for (size_t k = 0; k < n_kinds; k++) free(kind_labels[k]);
    free(kind_labels);
    for (size_t m = 0; m < n_modules; m++) free(modules[m]);
    free(modules);

    return 0;
}
