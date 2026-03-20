//  cone.c — C-ONE: merge a C project into a single file
//
//  Discovers all project files by crawling the #include graph from root
//  files or directories.  No need to list every .h and .c manually.
//
//  Build:
//    cc -O2 -o cone cone.c
//
//  Usage:
//    cone [options] <root.h | directory> ...
//
//  Options:
//    -I <dir>          Include search path (repeatable)
//    -o <file>         Output file (default: stdout)
//    -m, --mode <M>    Output mode: stb (default) or split
//    -x <pattern>      Exclude files/dirs matching pattern (repeatable, globs)
//    --no-strip        Keep include guards (default: strip them)
//    --no-source       Skip .c auto-discovery
//    --list            Print discovered files, don't emit
//    --stats           Print timing and size metrics
//    --watch           Re-run when source files change
//    --help            Show usage
//
//  Modes:
//    stb    Single-file STB-style output with #ifdef PREFIX_IMPLEMENTATION
//    split  Two files: .h (headers) + .c (sources with #include "the.h")
//
//  The output prefix (used for guards in stb mode and as the .c companion
//  filename in split mode) is derived from the -o filename (strip extension,
//  uppercase).  If -o is not given, the first root's basename is used instead.
//
//  Examples:
//    cone -I src/ -o mylib.h src/mylib.h
//    cone -I src/ -o mylib.h -m split src/mylib.h
//    cone -I src/ -o mylib.h -m stb -x test -x "*.gen.*" src/
//    cone -I src/ -o mylib.h --list src/
//    cone -I src/ -o mylib.h --watch src/mylib.h
//
//  License: Public domain — do whatever you want with it.

// Check OS
#if defined(_WIN32) || defined(_WIN64)
  #define OS_WINDOWS 1
#else
  #define OS_UNIX 1
#endif

// Check compiler
#if defined(_MSC_VER)
  #define COMPILER_MSVC 1
#elif defined(__GNUC__) || defined(__clang__)
  #define COMPILER_GCC 1
#else
  #error "Unsupported compiler"
#endif


#if COMPILER_GCC
  #define _GNU_SOURCE
#endif

#include <ctype.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifdef OS_WINDOWS
  #define WIN32_LEAN_AND_MEAN
  #include <windows.h>
  #include <io.h>
  #include <direct.h>
  #define HAS_MMAP 0
#else
  #include <sys/mman.h>
  #include <sys/stat.h>
  #include <dirent.h>
  #include <unistd.h>
  #define HAS_MMAP 1
#endif

// =============================================================================
// Defines and types
// =============================================================================

typedef int8_t    i8;
typedef int16_t   i16;
typedef int32_t   i32;
typedef int64_t   i64;
typedef uint8_t   u8;
typedef uint16_t  u16;
typedef uint32_t  u32;
typedef uint64_t  u64;
typedef float     f32;
typedef double    f64;
typedef uintptr_t usize;
typedef intptr_t  isize;

#define MIN(a,b) ((a) < (b) ? (a) : (b))
#define MAX(a,b) ((a) > (b) ? (a) : (b))

#define ARRAY_COUNT(arr) (sizeof(arr) / sizeof((arr)[0]))

// =============================================================================
// Limits
// =============================================================================

#define MAX_FILES         1024
#define MAX_SEARCH        32
#define MAX_EXCLUDE       32
#define MAX_PATH_LEN      4096
#define MAX_PATH_CONCAT   (MAX_PATH_LEN + 256)
#define MAX_GUARD_LEN     256
#define ARENA_RESERVE     (256UL * 1024 * 1024)

// =============================================================================
// Base
// =============================================================================

static usize
os_page_size(void)
{
#ifdef OS_WINDOWS
    SYSTEM_INFO si;
    GetSystemInfo(&si);
    return (usize)si.dwPageSize;
#else
    usize ps = sysconf(_SC_PAGESIZE);
    return (ps > 0) ? ps : 4096;
#endif
}

inline static usize
align_up(usize val, usize a)
{
    return (val + a - 1) & ~(a - 1);
}

// =============================================================================
// Arena allocator
// =============================================================================

typedef struct {
    u8    *base;
    usize  size;
    usize  pos;
    usize  pos_commit;
    usize  alignment;
} arena_t;

static arena_t *
arena_create(usize reserve_size, usize alignment)
{
    usize page_size = os_page_size();
    usize reserved  = align_up(reserve_size, page_size);

    const usize initial_commit = 1024 * 64; // 64 KB

    void *base = NULL;
    #if HAS_MMAP
        base = mmap(NULL, reserved, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (base == MAP_FAILED) return NULL;
        if (mprotect(base, initial_commit, PROT_READ | PROT_WRITE) != 0) return NULL;
    #else
        base = VirtualAlloc(NULL, reserved, MEM_RESERVE, PAGE_NOACCESS);
        if (!base) return NULL;
        if (!VirtualAlloc(base, initial_commit, MEM_COMMIT, PAGE_READWRITE)) {
            VirtualFree(base, 0, MEM_RELEASE);
            return NULL;
        }
    #endif

    arena_t *a    = (arena_t *)base;
    a->base       = (u8 *)base;
    a->size       = reserved;
    a->pos        = sizeof(arena_t);
    a->pos_commit = initial_commit;
    a->alignment  = alignment;
    return a;
}

static int
arena_ensure(arena_t *a, usize needed)
{
    if (needed <= a->pos_commit) return 1;
    usize nc = align_up(needed, a->alignment);
    if (nc > a->size) return 0;
#if HAS_MMAP
    if (mprotect(a->base, nc, PROT_READ | PROT_WRITE) != 0) return 0;
#else
    if (!VirtualAlloc(a->base + a->pos_commit, nc - a->pos_commit, MEM_COMMIT, PAGE_READWRITE)) return 0;
#endif
    a->pos_commit = nc;
    return 1;
}

static void *
arena_push(arena_t *a, usize size)
{
    usize off = align_up(a->pos, a->alignment);
    usize end = off + size;
    if (!arena_ensure(a, end)) return NULL;
    a->pos = end;
    return a->base + off;
}

#define arena_push_struct(a, T)     (T *)arena_push(a, sizeof(T))
#define arena_push_array(a, T, cnt) (T *)arena_push(a, sizeof(T) * (cnt))

// Reset arena to empty (only the arena header survives).
inline static void
arena_reset(arena_t *a)
{
    a->pos = sizeof(arena_t);
}

// Restore arena position to a previously saved point.
inline static void
arena_set_pos(arena_t *a, usize saved_pos)
{
    if (saved_pos >= sizeof(arena_t) && saved_pos <= a->pos)
        a->pos = saved_pos;
}

static void
arena_destroy(arena_t *a)
{
    if (!a || !a->base) return;
    u8 *base = a->base;
    usize size = a->size;
#if HAS_MMAP
    munmap(base, size);
#else
    VirtualFree(base, 0, MEM_RELEASE);
#endif
}

typedef struct tmp_arena tmp_arena_t;
struct tmp_arena
{
    arena_t *arena;
    usize    pos;
};

inline static tmp_arena_t tmp_arena_begin (arena_t *a)    { tmp_arena_t t = { a, a->pos }; return t; }
inline static void        tmp_arena_end   (tmp_arena_t t) { t.arena->pos = t.pos; }

// =============================================================================
// Utility
// =============================================================================

static void
die(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    fprintf(stderr, "cone: ");
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    exit(1);
}

// =============================================================================
// Scratch Arena
//
// Singleton arena for temporary allocations during processing.
// Not thread-safe, but that's fine since cone is single-threaded.
// Avoids the need to pass an arena pointer around everywhere.
// =============================================================================

static tmp_arena_t
scratch_begin(void)
{
    static const usize scratch_arena_size = 1024 * 1024; // 1 MB
    static arena_t *scratch               = NULL;
    if (!scratch) {
        scratch = arena_create(scratch_arena_size, sizeof(void *));
        if (!scratch) die("cannot create scratch arena");
    }
    return tmp_arena_begin(scratch);
}

inline static void scratch_end(tmp_arena_t t) { tmp_arena_end(t); }

// =============================================================================
// Timer
// =============================================================================

static inline f64
time_now(void)
{
#ifdef OS_WINDOWS
    LARGE_INTEGER freq, cnt;
    QueryPerformanceFrequency(&freq);
    QueryPerformanceCounter(&cnt);
    return (f64)cnt.QuadPart / (f64)freq.QuadPart;
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (f64)ts.tv_sec + (f64)ts.tv_nsec * 1e-9;
#endif
}

// =============================================================================
// String
// =============================================================================

typedef struct string string_t;
struct string
{
    u8    *data;
    usize  len;
};

typedef u8* zstring_t; // null-terminated utf-8 string

#define S_EMPTY      (string_t) { NULL, 0 }
#define S(cstr)      (string_t) { (u8*)(cstr), sizeof(cstr) - 1 }
#define S_COMP(cstr) { (u8*)(cstr), sizeof(cstr) - 1 }
#define S_PRI        "%.*s"
#define S_VARG(s)    (int)(s).len, (char *)(s).data
#define TO_CSTR(s)   ((const char *)(s).data)

inline static string_t str_make              (u8 *data, usize len)         { return (string_t) { data, len }; }
inline static string_t str_from_cstr         (const char *cstr)            { return str_make((u8 *)cstr, strlen(cstr)); }
inline static bool     str_is_empty          (string_t s)                  { return s.len == 0; }
inline static bool     str_eq                (string_t a, string_t b)      { return a.len == b.len && memcmp(a.data, b.data, a.len) == 0; }
inline static bool     str_starts_with       (string_t s, string_t prefix) { return s.len >= prefix.len && memcmp(s.data, prefix.data, prefix.len) == 0; }
inline static bool     str_ends_with         (string_t s, string_t suffix) { return s.len >= suffix.len && memcmp(s.data + s.len - suffix.len, suffix.data, suffix.len) == 0; }
inline static string_t str_chop_at_char      (string_t s, char c)          { for (usize i = 0; i < s.len; i++) { if (s.data[i] == c) return str_make(s.data, i); } return s; }
inline static string_t str_chop_at_last_char (string_t s, char c)          { for (isize i = (isize)s.len - 1; i >= 0; i--) { if (s.data[i] == c) return str_make(s.data, (usize)i); } return s; }
inline static string_t str_skip              (string_t s, usize n)         { return (n < s.len) ? str_make(s.data + n, s.len - n) : S_EMPTY; }
inline static string_t str_trim_start        (string_t s)                  { usize i = 0; while (i < s.len && isspace(s.data[i])) i++; return str_skip(s, i); }
inline static string_t str_trim_end          (string_t s)                  { isize i = (isize)s.len - 1; while (i >= 0 && isspace(s.data[i])) i--; return str_make(s.data, (usize)(i + 1)); }
inline static string_t str_trim              (string_t s)                  { return str_trim_end(str_trim_start(s)); }
inline static char     str_char_at           (string_t s, usize idx)       { return (idx < s.len) ? (char)s.data[idx] : '\0'; }

// Find first occurrence of character in string, returns index or -1
inline static isize str_find_char(string_t s, char c)
{
    for (usize i = 0; i < s.len; i++)
        if (s.data[i] == (u8)c) return (isize)i;
    return -1;
}

// Find last occurrence of character in string, returns index or -1
inline static isize str_find_last_char(string_t s, char c)
{
    for (isize i = (isize)s.len - 1; i >= 0; i--)
        if (s.data[i] == (u8)c) return i;
    return -1;
}

// Check if string contains a character
inline static bool str_contains_char(string_t s, char c)
{
    return str_find_char(s, c) >= 0;
}

// Extract substring [start, start+len)
inline static string_t str_substr(string_t s, usize start, usize len)
{
    if (start >= s.len) return S_EMPTY;
    usize max_len = s.len - start;
    if (len > max_len) len = max_len;
    return str_make(s.data + start, len);
}

// Skip past first occurrence of char, returns everything after it (or empty)
inline static string_t str_skip_past_char(string_t s, char c)
{
    isize idx = str_find_char(s, c);
    return (idx >= 0) ? str_skip(s, (usize)idx + 1) : S_EMPTY;
}

// Get the filename from a path (everything after last separator)
inline static string_t str_basename(string_t path)
{
    for (isize i = (isize)path.len - 1; i >= 0; i--) {
        if (path.data[i] == '/' || path.data[i] == '\\')
            return str_skip(path, (usize)i + 1);
    }
    return path;
}

// Strip the extension from a filename (everything before last dot)
inline static string_t str_strip_extension(string_t s)
{
    for (isize i = (isize)s.len - 1; i >= 0; i--) {
        if (s.data[i] == '.') return str_make(s.data, (usize)i);
        if (s.data[i] == '/' || s.data[i] == '\\') break;
    }
    return s;
}

// Uppercase a string into an arena-allocated copy
static string_t
str_to_upper(arena_t *a, string_t s)
{
    u8 *p = (u8 *)arena_push(a, s.len);
    if (!p) return S_EMPTY;
    for (usize i = 0; i < s.len; i++)
        p[i] = (u8)toupper(s.data[i]);
    return str_make(p, s.len);
}

inline static string_t
str_concat(arena_t *a, string_t s1, string_t s2)
{
    usize len = s1.len + s2.len;
    u8 *p = (u8 *)arena_push(a, len);
    if (p) {
        memcpy(p, s1.data, s1.len);
        memcpy(p + s1.len, s2.data, s2.len);
    }
    return str_make(p, len);
}

static string_t
str_fmtv(arena_t *a, const char *fmt, va_list ap)
{
    va_list ap_copy;
    va_copy(ap_copy, ap);
    int needed = vsnprintf(NULL, 0, fmt, ap_copy);
    va_end(ap_copy);
    if (needed < 0) return S_EMPTY;
    u8 *buf = (u8 *)arena_push(a, (usize)(needed + 1));
    if (!buf) return S_EMPTY;
    vsnprintf((char *)buf, (usize)(needed + 1), fmt, ap);
    return str_make(buf, (usize)needed);
}

static string_t
str_fmt(arena_t *a, const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    string_t result = str_fmtv(a, fmt, ap);
    va_end(ap);
    return result;
}

static string_t
str_copy(arena_t *a, string_t s)
{
    u8 *p = (u8 *)arena_push(a, s.len);
    if (p) { memcpy(p, s.data, s.len); }
    return str_make(p, s.len);
}

static string_t
str_copy_zstr(arena_t *a, const char *cstr)
{
    usize len = strlen(cstr);
    u8 *p = (u8 *)arena_push(a, len);
    if (p) { memcpy(p, cstr, len); }
    return str_make(p, len);
}

static zstring_t
zstr_copy_str(arena_t *a, string_t s)
{
    zstring_t zstr = (zstring_t)arena_push(a, s.len + 1);
    if (zstr) { memcpy(zstr, s.data, s.len); zstr[s.len] = '\0'; }
    return zstr;
}

static zstring_t
zstr_fmtv(arena_t *a, const char *fmt, va_list ap)
{
    va_list ap_copy;
    va_copy(ap_copy, ap);
    int needed = vsnprintf(NULL, 0, fmt, ap_copy);
    va_end(ap_copy);
    if (needed < 0) return NULL;
    usize sz = (usize)(needed + 1);
    zstring_t result = (zstring_t)arena_push(a, sz);
    if (!result) return NULL;
    vsnprintf((char *)result, sz, fmt, ap);
    result[needed] = '\0';
    return result;
}

static zstring_t
zstr_fmt(arena_t *a, const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    zstring_t result = zstr_fmtv(a, fmt, ap);
    va_end(ap);
    return result;
}

// Check if arg exactly matches either the long or short option form
inline static bool str_arg_eq(string_t arg, string_t a_long, string_t a_short)
{
    return str_eq(arg, a_long) || (!str_is_empty(a_short) && str_eq(arg, a_short));
}

// Check if arg starts with either the long or short option prefix
inline static bool str_arg_starts_with(string_t arg, string_t a_long, string_t a_short)
{
    return str_starts_with(arg, a_long) || (!str_is_empty(a_short) && str_starts_with(arg, a_short));
}

// =============================================================================
// Glob matching
//
// Supports * (match any sequence) and ? (match single char).
// Used for -x exclude patterns.
// =============================================================================

static bool
glob_match(string_t pattern, string_t str)
{
    usize pi = 0, si = 0;
    usize star_pi = (usize)-1, star_si = 0;

    while (si < str.len) {
        if (pi < pattern.len && (pattern.data[pi] == '?' || pattern.data[pi] == str.data[si])) {
            pi++; si++;
        } else if (pi < pattern.len && pattern.data[pi] == '*') {
            star_pi = pi++;
            star_si = si;
        } else if (star_pi != (usize)-1) {
            pi = star_pi + 1;
            si = ++star_si;
        } else {
            return false;
        }
    }
    while (pi < pattern.len && pattern.data[pi] == '*') pi++;
    return pi == pattern.len;
}

// =============================================================================
// Filesystem
// =============================================================================

typedef u32 fs_error_t;
enum {
    FS_ERROR_NONE = 0,
    FS_ERROR_NOT_FOUND,
    FS_ERROR_NOT_ENOUGH_MEMORY,
    FS_ERROR_READ,
};

static const char *fs_error_string(fs_error_t err) {
    switch (err) {
        case FS_ERROR_NONE: return "no error";
        case FS_ERROR_NOT_FOUND: return "file not found";
        case FS_ERROR_NOT_ENOUGH_MEMORY: return "not enough memory";
        case FS_ERROR_READ: return "read error";
        default: return "unknown error";
    }
}

typedef struct file_result file_result_t;
struct file_result
{
    string_t    content;
    fs_error_t  error;
};

static file_result_t
fs_read_entire_file(arena_t *a, string_t path)
{
    file_result_t res = {
        .content = S_EMPTY,
        .error   = FS_ERROR_NONE,
    };

    tmp_arena_t scratch = scratch_begin();
    zstring_t   zpath   = zstr_copy_str(scratch.arena, path);
    FILE *f = fopen((const char *)zpath, "rb");
    if (!f) { res.error = FS_ERROR_NOT_FOUND; goto done; }

    fseek(f, 0, SEEK_END);
    long raw = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (raw <= 0) goto done;

    usize sz  = (usize)raw;
    u8   *buf = (u8 *)arena_push(a, sz + 1);
    if (!buf) { res.error = FS_ERROR_NOT_ENOUGH_MEMORY; goto done; }
    if (fread(buf, 1, sz, f) != sz) { res.error = FS_ERROR_READ; goto done; }
    buf[sz] = 0;
    res.content = str_make(buf, sz);

done:
    if (f) fclose(f);
    scratch_end(scratch);
    return res;
}

// Get directory portion of path (including trailing separator)
inline static string_t
fs_dirname(string_t path)
{
    for (isize i = (isize)path.len - 1; i >= 0; i--) {
        if (path.data[i] == '/' || path.data[i] == '\\')
            return str_make(path.data, (usize)(i + 1));
    }
    return S_EMPTY;
}

// Get file extension (including the dot), e.g. ".c", ".h"
inline static string_t
fs_extension(string_t path)
{
    for (isize i = (isize)path.len - 1; i >= 0; i--) {
        if (path.data[i] == '.') return str_make(path.data + i, path.len - (usize)i);
        if (path.data[i] == '/' || path.data[i] == '\\') break;
    }
    return S_EMPTY;
}

inline static bool
fs_exists(string_t path)
{
    tmp_arena_t scratch = scratch_begin();
    zstring_t zpath = zstr_copy_str(scratch.arena, path);
#ifdef OS_WINDOWS
    bool res = _access((const char *)zpath, 0) == 0;
#else
    bool res = access((const char *)zpath, F_OK) == 0;
#endif
    scratch_end(scratch);
    return res;
}

inline static bool
fs_is_dir(string_t path)
{
    tmp_arena_t scratch = scratch_begin();
    zstring_t zpath = zstr_copy_str(scratch.arena, path);
#ifdef OS_WINDOWS
    DWORD attr = GetFileAttributesA((const char *)zpath);
    bool res = (attr != INVALID_FILE_ATTRIBUTES) && (attr & FILE_ATTRIBUTE_DIRECTORY);
#else
    struct stat st;
    bool res = (stat((const char *)zpath, &st) == 0) && S_ISDIR(st.st_mode);
#endif
    scratch_end(scratch);
    return res;
}

static string_t
fs_canonicalize(arena_t *a, string_t path)
{
    tmp_arena_t scratch = scratch_begin();
    zstring_t zpath = zstr_copy_str(scratch.arena, path);
    char resolved[MAX_PATH_LEN];
    string_t res = S_EMPTY;
#ifdef OS_WINDOWS
    if (_fullpath(resolved, (const char *)zpath, sizeof(resolved)))
        res = str_copy_zstr(a, resolved);
#else
    if (realpath((const char *)zpath, resolved))
        res = str_copy_zstr(a, resolved);
#endif
    scratch_end(scratch);
    return res;
}

// Get modification time as a comparable timestamp
static f64
fs_mtime(string_t path)
{
    tmp_arena_t scratch = scratch_begin();
    zstring_t zpath = zstr_copy_str(scratch.arena, path);
    f64 mt = 0;
#ifdef OS_WINDOWS
    WIN32_FILE_ATTRIBUTE_DATA fad;
    if (GetFileAttributesExA((const char *)zpath, GetFileExInfoStandard, &fad)) {
        ULARGE_INTEGER uli;
        uli.LowPart  = fad.ftLastWriteTime.dwLowDateTime;
        uli.HighPart = fad.ftLastWriteTime.dwHighDateTime;
        mt = (f64)uli.QuadPart;
    }
#else
    struct stat st;
    if (stat((const char *)zpath, &st) == 0)
        mt = (f64)st.st_mtime + (f64)st.st_mtim.tv_nsec * 1e-9;
#endif
    scratch_end(scratch);
    return mt;
}

// Join two path components with a separator
static string_t
fs_path_join(arena_t *a, string_t dir, string_t file)
{
    if (str_is_empty(dir))  return str_copy(a, file);
    if (str_is_empty(file)) return str_copy(a, dir);
    char last = (char)dir.data[dir.len - 1];
    if (last == '/' || last == '\\')
        return str_concat(a, dir, file);
    usize len = dir.len + 1 + file.len;
    u8 *p = (u8 *)arena_push(a, len);
    if (!p) return S_EMPTY;
    memcpy(p, dir.data, dir.len);
    p[dir.len] = '/';
    memcpy(p + dir.len + 1, file.data, file.len);
    return str_make(p, len);
}

// Make a path relative to a base directory
// If the path starts with base, strip the base prefix; otherwise return as-is
static string_t
fs_make_relative(string_t path, string_t base)
{
    if (str_is_empty(base)) return path;
    if (str_starts_with(path, base)) {
        string_t rel = str_skip(path, base.len);
        // Skip leading separator if present
        if (!str_is_empty(rel) && (rel.data[0] == '/' || rel.data[0] == '\\'))
            rel = str_skip(rel, 1);
        return str_is_empty(rel) ? path : rel;
    }
    return path;
}

/* ================================================================== */
/* Exclude patterns (with glob support)                                */
/* ================================================================== */

static string_t exclude_patterns[MAX_EXCLUDE];
static int      exclude_count;

/*
 * Check if a path matches any exclude pattern.
 *
 * For each pattern, the match is tested against individual path components
 * (split by / or \).  This way:
 *   -x test         excludes "src/test/foo.c" (component "test" matches)
 *   -x "*.gen.*"    excludes "src/foo.gen.c"  (component glob match)
 *   -x stb_image.h  excludes any path containing that filename
 *
 * Plain patterns without glob chars (*, ?) do exact component matching.
 * Patterns with glob chars use glob_match for each component.
 */
static bool
cone_path_is_excluded(string_t path)
{
    for (int i = 0; i < exclude_count; i++) {
        string_t pat = exclude_patterns[i];
        bool has_glob = str_contains_char(pat, '*') || str_contains_char(pat, '?');
        usize start = 0;
        for (usize j = 0; j <= path.len; j++) {
            if (j == path.len || path.data[j] == '/' || path.data[j] == '\\') {
                string_t comp = str_make(path.data + start, j - start);
                if (!str_is_empty(comp)) {
                    if (has_glob ? glob_match(pat, comp) : str_eq(comp, pat))
                        return true;
                }
                start = j + 1;
            }
        }
    }
    return false;
}

/* ================================================================== */
/* File registry                                                       */
/* ================================================================== */

typedef u32 file_state_t;
enum {
    STATE_UNVISITED = 0,
    STATE_IN_PROGRESS,
    STATE_EMITTED
};

typedef u32 file_kind_t;
enum {
    KIND_HEADER,
    KIND_SOURCE
};

static const string_t s_header_extensions[] = {
    S_COMP(".h"),
    S_COMP(".H"),
    S_COMP(".hpp"),
    S_COMP(".hxx")
};

static const string_t s_source_extensions[] = {
    S_COMP(".c"),
    S_COMP(".C"),
    S_COMP(".cc"),
    S_COMP(".cpp"),
    S_COMP(".cxx")
};

inline static bool cone_file_is_header(string_t s) { for (usize i = 0; i < ARRAY_COUNT(s_header_extensions); i++) { if (str_ends_with(s, s_header_extensions[i])) return true; } return false; }
inline static bool cone_file_is_source(string_t s) { for (usize i = 0; i < ARRAY_COUNT(s_source_extensions); i++) { if (str_ends_with(s, s_source_extensions[i])) return true; } return false; }

typedef u32 output_mode_t;
enum {
    MODE_STB = 0,
    MODE_SPLIT,
};

typedef struct {
    string_t      path;         // canonical (for dedup)
    string_t      display_path; // relative (for output)
    u8           *buf;
    usize         len;
    file_state_t  state;
    file_kind_t   kind;
} file_entry_t;

typedef struct ctx ctx_t;
struct ctx
{
    arena_t       *perm;         // permanent arena (cwd, prefix, etc.)
    arena_t       *arena;        // per-run arena (files, paths — reset each cycle)
    file_entry_t   files[MAX_FILES];
    int            file_count;
    string_t       search_dirs[MAX_SEARCH];
    int            search_count;
    FILE          *out;
    bool           strip_guards;
    bool           discover_src;
    output_mode_t  mode;
    string_t       prefix;       // derived from -o or root (UPPERCASED)
    string_t       cwd;          // for relative display paths
    usize          bytes_read;
    usize          bytes_written;
};

static ctx_t *g_ctx = NULL;

static int
cone_file_registry_find(string_t path) {
    for (int i = 0; i < g_ctx->file_count; i++)
        if (str_eq(g_ctx->files[i].path, path))
            return i;
    return -1;
}

// Forward declaration (circular dependency with cone_scan_and_register_includes)
static int cone_file_register(string_t path, file_kind_t kind);

inline static void
skip_space(const char **p) {
    while (**p && isspace((unsigned char)**p)) (*p)++;
}

static string_t
cone_resolve_include(string_t includer, string_t target)
{
    tmp_arena_t scratch = scratch_begin();
    string_t result = S_EMPTY;

    if (!str_is_empty(includer)) {
        string_t dir     = fs_dirname(includer);
        string_t attempt = fs_path_join(scratch.arena, dir, target);
        if (fs_exists(attempt)) {
            result = str_copy(g_ctx->arena, attempt);
            goto done;
        }
    }

    for (int i = 0; i < g_ctx->search_count; i++) {
        string_t attempt = fs_path_join(scratch.arena, g_ctx->search_dirs[i], target);
        if (fs_exists(attempt)) {
            result = str_copy(g_ctx->arena, attempt);
            goto done;
        }
    }

done:
    scratch_end(scratch);
    return result;
}

static void
cone_scan_and_register_includes(int idx) {
    file_entry_t *fe = &g_ctx->files[idx];
    const char *p = (const char *)fe->buf;
    const char *end = (const char *)fe->buf + fe->len;

    while (p < end) {
        const char *eol = p;
        while (eol < end && *eol != '\n') eol++;
        const char *t = p;
        skip_space(&t);
        if (t < eol && *t == '#') {
            t++; skip_space(&t);
            if (eol - t >= 7 && strncmp(t, "include", 7) == 0) {
                t += 7; skip_space(&t);
                if (t < eol && *t == '"') {
                    t++;
                    const char *ns = t;
                    while (t < eol && *t != '"') t++;
                    if (t < eol && *t == '"') {
                        usize nl = (usize)(t - ns);
                        if (nl > 0 && nl < MAX_PATH_LEN) {
                            char inc[MAX_PATH_LEN];
                            memcpy(inc, ns, nl); inc[nl] = '\0';
                            string_t resolved = cone_resolve_include(fe->path, str_from_cstr(inc));
                            if (!str_is_empty(resolved)) {
                                file_kind_t k = cone_file_is_header(resolved)
                                    ? KIND_HEADER : KIND_SOURCE;
                                cone_file_register(resolved, k);
                            }
                        }
                    }
                }
            }
        }
        p = (eol < end) ? eol + 1 : eol;
    }
}

// =============================================================================
// Source discovery
// =============================================================================

#define MAX_SCANNED_DIRS 256
static string_t scanned_dirs[MAX_SCANNED_DIRS];
static int   scanned_dir_count;

static void
cone_discover_sources_in_dir(string_t header_path)
{
    string_t dir = fs_dirname(header_path);
    if (str_is_empty(dir)) return;

    string_t canon_dir = fs_canonicalize(g_ctx->arena, dir);
    for (int i = 0; i < scanned_dir_count; i++)
        if (str_eq(canon_dir, scanned_dirs[i]))
            return;
    if (scanned_dir_count < MAX_SCANNED_DIRS)
        scanned_dirs[scanned_dir_count++] = canon_dir;

    tmp_arena_t scratch = scratch_begin();

#ifdef OS_WINDOWS
    string_t glob = str_concat(scratch.arena, dir, S("*"));
    zstring_t zglob = zstr_copy_str(scratch.arena, glob);
    WIN32_FIND_DATAA fd;
    HANDLE h = FindFirstFileA((const char *)zglob, &fd);
    if (h == INVALID_HANDLE_VALUE) { scratch_end(scratch); return; }
    do {
        if (fd.cFileName[0] == '.') continue;
        if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) continue;
        string_t name = str_from_cstr(fd.cFileName);
        if (!cone_file_is_source(name)) continue;
        string_t full = str_concat(scratch.arena, dir, name);
        if (!cone_path_is_excluded(full))
            cone_file_register(full, KIND_SOURCE);
    } while (FindNextFileA(h, &fd));
    FindClose(h);
#else
    zstring_t zdir = zstr_copy_str(scratch.arena, dir);
    DIR *d = opendir((const char *)zdir);
    if (!d) { scratch_end(scratch); return; }
    struct dirent *ent;
    while ((ent = readdir(d)) != NULL) {
        if (ent->d_name[0] == '.') continue;
        string_t name = str_from_cstr(ent->d_name);
        if (!cone_file_is_source(name)) continue;
        string_t full = str_concat(scratch.arena, dir, name);
        if (!cone_path_is_excluded(full))
            cone_file_register(full, KIND_SOURCE);
    }
    closedir(d);
#endif

    scratch_end(scratch);
}

static int
cone_file_register(string_t path, file_kind_t kind)
{
    if (cone_path_is_excluded(path)) return -1;

    string_t canon = fs_canonicalize(g_ctx->arena, path);

    int existing = cone_file_registry_find(canon);
    if (existing >= 0) return existing;

    if (g_ctx->file_count >= MAX_FILES)
        die("too many files (max %d)", MAX_FILES);

    int idx = g_ctx->file_count++;
    file_entry_t *fe = &g_ctx->files[idx];
    fe->path         = canon;
    // Store relative display path
    fe->display_path = str_copy(g_ctx->arena, fs_make_relative(path, g_ctx->cwd));
    fe->state        = STATE_UNVISITED;
    fe->kind         = kind;

    file_result_t res = fs_read_entire_file(g_ctx->arena, canon);
    if (res.error != FS_ERROR_NONE)
        die("cannot read file " S_PRI ": %s", S_VARG(path), fs_error_string(res.error));
    fe->buf = res.content.data;
    fe->len = res.content.len;
    g_ctx->bytes_read += fe->len;

    cone_scan_and_register_includes(idx);

    if (kind == KIND_HEADER && g_ctx->discover_src)
        cone_discover_sources_in_dir(path);

    return idx;
}

// =============================================================================
// Directory scanning
// =============================================================================

static void
cone_scan_directory(string_t path)
{
    tmp_arena_t scratch = scratch_begin();
#ifdef OS_WINDOWS
    zstring_t pattern = zstr_fmt(scratch.arena, S_PRI "\\*", S_VARG(path));
    WIN32_FIND_DATAA fd;
    HANDLE h = FindFirstFileA((const char *)pattern, &fd);
    if (h == INVALID_HANDLE_VALUE) {
        scratch_end(scratch);
        die("cannot open directory: " S_PRI, S_VARG(path));
    }
    do {
        if (fd.cFileName[0] == '.') continue;
        string_t name = str_from_cstr(fd.cFileName);
        string_t full = fs_path_join(scratch.arena, path, name);
        if (cone_path_is_excluded(full))                    continue;
        if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) cone_scan_directory(full);
        else if (cone_file_is_header(full))                 cone_file_register(full, KIND_HEADER);
        else if (cone_file_is_source(full))                 cone_file_register(full, KIND_SOURCE);
    } while (FindNextFileA(h, &fd));
    FindClose(h);
#else
    zstring_t zpath = zstr_copy_str(scratch.arena, path);
    DIR *d = opendir((const char *)zpath);
    if (!d) {
        scratch_end(scratch);
        die("cannot open directory: " S_PRI, S_VARG(path));
    }
    struct dirent *ent;
    while ((ent = readdir(d)) != NULL) {
        if (ent->d_name[0] == '.') continue;
        string_t name = str_from_cstr(ent->d_name);
        string_t full = fs_path_join(scratch.arena, path, name);
        if (cone_path_is_excluded(full)) continue;
        if (fs_is_dir(full))             cone_scan_directory(full);
        else if (cone_file_is_header(full)) cone_file_register(full, KIND_HEADER);
        else if (cone_file_is_source(full)) cone_file_register(full, KIND_SOURCE);
    }
    closedir(d);
#endif
    scratch_end(scratch);
}

/* ================================================================== */
/* Include guard detection                                             */
/* ================================================================== */

typedef struct {
    int found;
    int ifndef_line, define_line, endif_line;
    int pragma_once_line;
} guard_info_t;

static guard_info_t detect_guard(const char *buf, usize len);

static guard_info_t
detect_guard(const char *buf, usize len)
{
    guard_info_t gi = {0};
    gi.ifndef_line = gi.define_line = gi.endif_line = gi.pragma_once_line = -1;

    const char *p = buf, *end = buf + len;
    int line_no = 0, first_code = -1, second_code = -1, last_endif = -1;
    char guard[MAX_GUARD_LEN] = {0};

    while (p < end) {
        const char *ls = p, *eol = p;
        while (eol < end && *eol != '\n') eol++;
        usize ll = (usize)(eol - ls);
        const char *t = ls; skip_space(&t);
        int empty = (t >= eol || *t == '\n' || *t == '\r');

        if (!empty) {
            if (first_code < 0 && *t == '#' && ll >= 12) {
                const char *d2 = t + 1; skip_space(&d2);
                if (strncmp(d2, "pragma", 6) == 0) {
                    d2 += 6; skip_space(&d2);
                    if (strncmp(d2, "once", 4) == 0)
                        gi.pragma_once_line = line_no;
                }
            }
            if (first_code < 0)       first_code = line_no;
            else if (second_code < 0) second_code = line_no;
            if (*t == '#') {
                const char *d2 = t + 1; skip_space(&d2);
                if (strncmp(d2, "endif", 5) == 0) last_endif = line_no;
            }
        }
        p = (eol < end) ? eol + 1 : eol;
        line_no++;
    }

    if (first_code < 0 || second_code < 0) return gi;

    int chk[2] = { first_code, second_code };
    if (gi.pragma_once_line == first_code) {
        p = buf; line_no = 0; int nth = 0, third = -1;
        while (p < end) {
            const char *eol2 = p;
            while (eol2 < end && *eol2 != '\n') eol2++;
            const char *t2 = p; skip_space(&t2);
            if (!(t2 >= eol2 || *t2 == '\n' || *t2 == '\r'))
                if (++nth == 3) { third = line_no; break; }
            p = (eol2 < end) ? eol2 + 1 : eol2;
            line_no++;
        }
        if (third < 0) return gi;
        chk[0] = second_code; chk[1] = third;
    }

    p = buf; line_no = 0;
    while (p < end) {
        const char *ls = p, *eol2 = p;
        while (eol2 < end && *eol2 != '\n') eol2++;

        if (line_no == chk[0]) {
            const char *t2 = ls; skip_space(&t2);
            if (*t2 == '#') {
                const char *d2 = t2 + 1; skip_space(&d2);
                if (strncmp(d2, "ifndef", 6) == 0) {
                    d2 += 6; skip_space(&d2);
                    const char *ms = d2;
                    while (d2 < eol2 && !isspace((unsigned char)*d2)) d2++;
                    usize ml = (usize)(d2 - ms);
                    if (ml > 0 && ml < MAX_GUARD_LEN) {
                        memcpy(guard, ms, ml); guard[ml] = '\0';
                        gi.ifndef_line = line_no;
                    }
                }
            }
        }
        if (line_no == chk[1] && gi.ifndef_line >= 0) {
            const char *t2 = ls; skip_space(&t2);
            if (*t2 == '#') {
                const char *d2 = t2 + 1; skip_space(&d2);
                if (strncmp(d2, "define", 6) == 0) {
                    d2 += 6; skip_space(&d2);
                    usize gl = strlen(guard);
                    if (strncmp(d2, guard, gl) == 0) {
                        const char *after = d2 + gl;
                        if (after >= eol2 || isspace((unsigned char)*after)) {
                            gi.define_line = line_no;
                            gi.endif_line  = last_endif;
                            gi.found       = 1;
                        }
                    }
                }
            }
        }
        p = (eol2 < end) ? eol2 + 1 : eol2;
        line_no++;
    }
    return gi;
}

/* ================================================================== */
/* Core: DFS emit                                                      */
/* ================================================================== */

static int
parse_local_include(const char *line, usize len, char *out, usize out_sz)
{
    const char *p = line, *end = line + len;
    skip_space(&p);
    if (p >= end || *p != '#') return 0;
    p++; skip_space(&p);
    if (end - p < 7 || strncmp(p, "include", 7) != 0) return 0;
    p += 7; skip_space(&p);
    if (p >= end || *p != '"') return 0;
    p++;
    const char *s = p;
    while (p < end && *p != '"' && *p != '\n') p++;
    if (p >= end || *p != '"') return 0;
    usize n = (usize)(p - s);
    if (n == 0 || n >= out_sz) return 0;
    memcpy(out, s, n); out[n] = '\0';
    return 1;
}

static void
emit_banner(ctx_t *ctx, string_t path)
{
    int pos = 3 + (int)path.len + 1;
    int pad  = 76 - pos;
    if (pad < 4) pad = 4;
    int n = fprintf(ctx->out, "// " S_PRI " ", S_VARG(path));
    for (int i = 0; i < pad; i++) n += fputc('=', ctx->out) != EOF ? 1 : 0;
    fputc('\n', ctx->out);
    ctx->bytes_written += (usize)(n + 1);
}

static void
emit_file(ctx_t *ctx, int file_idx)
{
    file_entry_t *fe = &ctx->files[file_idx];
    if (fe->state == STATE_EMITTED)     return;
    if (fe->state == STATE_IN_PROGRESS) die("cyclic include: " S_PRI, S_VARG(fe->display_path));

    fe->state = STATE_IN_PROGRESS;

    guard_info_t gi = {0};
    gi.ifndef_line = gi.define_line = gi.endif_line = gi.pragma_once_line = -1;
    if (ctx->strip_guards)
        gi = detect_guard((const char *)fe->buf, fe->len);

    emit_banner(ctx, fe->display_path);

    const char *p = (const char *)fe->buf;
    const char *end = (const char *)fe->buf + fe->len;
    int line_no = 0;

    while (p < end) {
        const char *ls = p, *eol = p;
        while (eol < end && *eol != '\n') eol++;
        usize ll = (usize)(eol - ls);

        int skip = 0;
        if (ctx->strip_guards) {
            if (gi.found &&
                (line_no == gi.ifndef_line ||
                 line_no == gi.define_line ||
                 line_no == gi.endif_line))
                skip = 1;
            if (gi.pragma_once_line >= 0 && line_no == gi.pragma_once_line)
                skip = 1;
        }

        if (!skip) {
            // Replace local #include with inline emission
            char inc[MAX_PATH_LEN];
            if (parse_local_include(ls, ll, inc, sizeof(inc))) {
                string_t resolved = cone_resolve_include(fe->display_path, str_from_cstr(inc));
                if (!str_is_empty(resolved)) {
                    string_t canon = fs_canonicalize(ctx->arena, resolved);
                    int child = cone_file_registry_find(canon);
                    if (child >= 0) {
                        emit_file(ctx, child);
                        goto next;
                    }
                }
            }
            fwrite(ls, 1, ll, ctx->out);
            fputc('\n', ctx->out);
            ctx->bytes_written += ll + 1;
        }
next:
        p = (eol < end) ? eol + 1 : eol;
        line_no++;
    }

    fe->state = STATE_EMITTED;
}

static void
emit_generated_banner(ctx_t *ctx, int nh, int ns)
{
    int n = fprintf(ctx->out,
        "// Generated by cone — %d headers + %d sources = %d files\n\n",
        nh, ns, nh + ns);
    ctx->bytes_written += (usize)n;
}

/* ================================================================== */
/* Derive prefix from output path or root input                        */
/* ================================================================== */

static string_t
derive_prefix(arena_t *a, string_t outpath, string_t first_root)
{
    string_t base = S_EMPTY;
    if (!str_is_empty(outpath)) {
        base = str_basename(outpath);
    } else {
        base = str_basename(first_root);
    }
    // Strip extension
    string_t stem = str_strip_extension(base);
    if (str_is_empty(stem)) stem = base;
    // Replace non-alnum with _
    u8 *buf = (u8 *)arena_push(a, stem.len);
    if (!buf) return S_EMPTY;
    for (usize i = 0; i < stem.len; i++)
        buf[i] = isalnum(stem.data[i]) ? (u8)toupper(stem.data[i]) : '_';
    return str_make(buf, stem.len);
}

// =============================================================================
// Main
// =============================================================================

static void
usage(void)
{
    fprintf(stderr,
        "Usage: cone [options] <file_or_dir> ...\n"
        "\n"
        "Discovers project files by crawling the #include graph.\n"
        "Give it a root header or a directory — it finds the rest.\n"
        "\n"
        "Options:\n"
        "  -I <dir>       Include search path (repeatable)\n"
        "  -o <file>      Output file (default: stdout)\n"
        "  -m, --mode <M> Output mode: stb (default) or split\n"
        "  -x <pattern>   Exclude matching names (supports * and ? globs)\n"
        "  --no-strip     Keep include guards (default: strip them)\n"
        "  --no-source    Skip .c auto-discovery\n"
        "  --list         Print discovered files, don't emit output\n"
        "  --stats        Print timing and size metrics\n"
        "  --watch        Re-run when source files change\n"
        "  --help         Show this message\n"
        "\n"
        "Modes:\n"
        "  stb            Single-file output with #ifdef PREFIX_IMPLEMENTATION\n"
        "  split          Two files: .h (headers) + .c (sources)\n"
        "\n"
        "The prefix for guards is derived from the -o filename (or root input),\n"
        "e.g. -o mylib.h produces prefix MYLIB.\n"
        "\n"
        "Examples:\n"
        "  cone -I src/ -o mylib.h src/mylib.h\n"
        "  cone -I src/ -o mylib.h -m split src/mylib.h\n"
        "  cone -I src/ -o mylib.h -x test -x \"*.gen.*\" src/\n"
        "  cone -I src/ --list src/\n"
        "  cone -I src/ -o mylib.h --watch src/mylib.h\n"
    );
    exit(1);
}

// Run the full discovery + emit pipeline; returns 0 on success.
// Extracted so --watch can re-invoke it.
static int
cone_run(ctx_t *ctx, string_t outpath, string_t roots[], u32 root_count,
         bool show_stats, bool list_only)
{
    f64 t_start = time_now();

    // =========================================================================
    // Discovery
    // =========================================================================

    for (u32 i = 0; i < root_count; i++) {
        if (fs_is_dir(roots[i]))
            cone_scan_directory(roots[i]);
        else {
            file_kind_t file_kind = cone_file_is_source(roots[i]) ? KIND_SOURCE : KIND_HEADER;
            cone_file_register(roots[i], file_kind);
        }
    }

    f64 t_discovered = time_now();

    int nh = 0, ns = 0;
    for (int i = 0; i < ctx->file_count; i++)
        if (ctx->files[i].kind == KIND_HEADER) nh++; else ns++;
    fprintf(stderr, "cone: %d headers + %d sources = %d files\n", nh, ns, ctx->file_count);

    // =========================================================================
    // --list mode: just print the file list and return
    // =========================================================================

    if (list_only) {
        for (int i = 0; i < ctx->file_count; i++) {
            const char *kind = ctx->files[i].kind == KIND_HEADER ? "H" : "S";
            fprintf(stderr, "  [%s] " S_PRI "\n", kind, S_VARG(ctx->files[i].display_path));
        }
        return 0;
    }

    // =========================================================================
    // Open output file(s)
    // =========================================================================

    FILE *out_src = NULL;
    string_t src_path = S_EMPTY;

    if (!str_is_empty(outpath)) {
        tmp_arena_t scratch = scratch_begin();
        zstring_t zpath = zstr_copy_str(scratch.arena, outpath);
        ctx->out = fopen((const char *)zpath, "wb");
        if (!ctx->out) die("cannot open: " S_PRI, S_VARG(outpath));
        scratch_end(scratch);

        if (ctx->mode == MODE_SPLIT && ns > 0) {
            // Derive .c path from .h path
            string_t stem = str_strip_extension(outpath);
            if (str_is_empty(stem)) stem = outpath;
            tmp_arena_t scratch2 = scratch_begin();
            src_path = str_concat(ctx->arena, stem, S(".c"));
            zstring_t zsrc = zstr_copy_str(scratch2.arena, src_path);
            out_src = fopen((const char *)zsrc, "wb");
            if (!out_src) die("cannot open: " S_PRI, S_VARG(src_path));
            scratch_end(scratch2);
        }
    }

    // =========================================================================
    // Emit
    // =========================================================================

    string_t prefix = ctx->prefix;
    bool use_stb = (ctx->mode == MODE_STB);
    bool use_split = (ctx->mode == MODE_SPLIT);

    // --- Emit headers ---
    emit_generated_banner(ctx, nh, ns);

    if (use_stb) {
        fprintf(ctx->out, "#ifndef " S_PRI "_H\n#define " S_PRI "_H\n\n",
                S_VARG(prefix), S_VARG(prefix));
    }

    for (int i = 0; i < ctx->file_count; i++)
        if (ctx->files[i].kind == KIND_HEADER)
            emit_file(ctx, i);

    if (use_stb) {
        fprintf(ctx->out, "\n#endif /* " S_PRI "_H */\n",
                S_VARG(prefix));
    }

    // --- Emit sources ---
    int have_src = 0;
    for (int i = 0; i < ctx->file_count; i++)
        if (ctx->files[i].kind == KIND_SOURCE) { have_src = 1; break; }

    if (have_src) {
        if (use_split && out_src) {
            // Switch output to the .c file
            FILE *prev_out = ctx->out;
            ctx->out = out_src;
            ctx->bytes_written = 0;

            // The .c file includes the .h
            string_t hdr_basename = str_basename(outpath);
            int n = fprintf(ctx->out, "// Generated by cone — source amalgamation\n\n");
            ctx->bytes_written += (usize)n;

            n = fprintf(ctx->out, "#include \"" S_PRI "\"\n\n", S_VARG(hdr_basename));
            ctx->bytes_written += (usize)n;

            // Reset states so sources can be emitted fresh
            for (int i = 0; i < ctx->file_count; i++)
                if (ctx->files[i].kind == KIND_SOURCE)
                    ctx->files[i].state = STATE_UNVISITED;

            for (int i = 0; i < ctx->file_count; i++)
                if (ctx->files[i].kind == KIND_SOURCE)
                    emit_file(ctx, i);

            fclose(out_src);
            ctx->out = prev_out;
            fprintf(stderr, "cone: wrote " S_PRI "\n", S_VARG(src_path));
        } else if (use_stb) {
            fprintf(ctx->out,
                "\n#ifdef " S_PRI "_IMPLEMENTATION\n"
                "#ifndef " S_PRI "_IMPLEMENTATION_GUARD\n"
                "#define " S_PRI "_IMPLEMENTATION_GUARD\n\n",
                S_VARG(prefix), S_VARG(prefix), S_VARG(prefix));

            for (int i = 0; i < ctx->file_count; i++)
                if (ctx->files[i].kind == KIND_SOURCE)
                    emit_file(ctx, i);

            fprintf(ctx->out,
                "\n#endif /* " S_PRI "_IMPLEMENTATION_GUARD */\n"
                "#endif /* " S_PRI "_IMPLEMENTATION */\n",
                S_VARG(prefix), S_VARG(prefix));
        } else {
            // Default (stb without sources needing special wrap shouldn't happen,
            // but emit them after headers in case)
            for (int i = 0; i < ctx->file_count; i++)
                if (ctx->files[i].kind == KIND_SOURCE)
                    emit_file(ctx, i);
        }
    }

    if (ctx->out != stdout) {
        fclose(ctx->out);
        ctx->out = stdout;
        fprintf(stderr, "cone: wrote " S_PRI "\n", S_VARG(outpath));
    }

    f64 t_done = time_now();
    if (show_stats) {
        f64 total_ms = (t_done - t_start) * 1000.0;
        f64 disc_ms  = (t_discovered - t_start) * 1000.0;
        f64 emit_ms  = (t_done - t_discovered) * 1000.0;
        fprintf(stderr, "\n");
        fprintf(stderr, "cone: --- stats ---\n");
        fprintf(stderr, "cone: files      %d (%d headers, %d sources)\n",        ctx->file_count, nh, ns);
        fprintf(stderr, "cone: read       %zu bytes (%.1f KB)\n",                ctx->bytes_read, (f64)ctx->bytes_read / 1024.0);
        fprintf(stderr, "cone: written    %zu bytes (%.1f KB)\n",                ctx->bytes_written, (f64)ctx->bytes_written / 1024.0);
        fprintf(stderr, "cone: arena      %zu / %zu bytes (pos / commit)\n",      ctx->arena->pos, ctx->arena->pos_commit);
        fprintf(stderr, "cone: perm       %zu / %zu bytes (pos / commit)\n",     ctx->perm->pos, ctx->perm->pos_commit);
        fprintf(stderr, "cone: discover   %.2f ms\n",                            disc_ms);
        fprintf(stderr, "cone: emit       %.2f ms\n",                            emit_ms);
        fprintf(stderr, "cone: total      %.2f ms\n",                            total_ms);
    }

    return 0;
}

int
main(int argc, char *argv[])
{
    if (argc < 2) usage();

    ctx_t ctx        = {0};
    ctx.perm         = arena_create(1024 * 1024, sizeof(void *)); // 1 MB for permanent data
    if (!ctx.perm)   die("cannot create permanent arena");
    ctx.arena        = arena_create(ARENA_RESERVE, sizeof(void *));
    if (!ctx.arena)  die("cannot create arena");
    ctx.out          = stdout;
    ctx.strip_guards = true;
    ctx.discover_src = true;
    ctx.mode         = MODE_STB;
    g_ctx            = &ctx;

    // Get CWD for relative paths
    {
        char cwd_buf[MAX_PATH_LEN];
#ifdef OS_WINDOWS
        if (_getcwd(cwd_buf, sizeof(cwd_buf)))
#else
        if (getcwd(cwd_buf, sizeof(cwd_buf)))
#endif
        {
            usize len = strlen(cwd_buf);
            if (len > 0 && cwd_buf[len - 1] != '/' && cwd_buf[len - 1] != '\\') {
                cwd_buf[len] = '/';
                cwd_buf[len + 1] = '\0';
            }
            ctx.cwd = str_copy(ctx.perm, str_from_cstr(cwd_buf));
        }
    }

    string_t outpath    = S_EMPTY;
    bool     show_stats = false;
    bool     list_only  = false;
    bool     watch_mode = false;
    string_t roots[MAX_FILES];
    u32      root_count = 0;

    for (int i = 1; i < argc; i++)
    {
        string_t arg = str_from_cstr(argv[i]);
        if (str_arg_eq(arg, S("--help"), S("-h"))) {
            usage();
        }
        else if (str_arg_starts_with(arg, S("--include-dir"), S("-I")))
        {
            string_t dir = S_EMPTY;
            if (str_starts_with(arg, S("--include-dir="))) {
                dir = str_skip(arg, sizeof("--include-dir=") - 1);
            } else if (str_starts_with(arg, S("-I")) && arg.len > 2) {
                dir = str_skip(arg, 2);
            } else {
                if (++i >= argc) die("-I requires an argument");
                dir = str_from_cstr(argv[i]);
            }
            if (ctx.search_count >= MAX_SEARCH) die("too many -I paths");
            ctx.search_dirs[ctx.search_count++] = dir;
        }
        else if (str_arg_eq(arg, S("--output"), S("-o"))) {
            if (++i >= argc) die("-o requires an argument");
            outpath = str_from_cstr(argv[i]);
        }
        else if (str_arg_eq(arg, S("--mode"), S("-m"))) {
            if (++i >= argc) die("--mode requires an argument (stb or split)");
            string_t mode_str = str_from_cstr(argv[i]);
            if (str_eq(mode_str, S("stb")))        ctx.mode = MODE_STB;
            else if (str_eq(mode_str, S("split")))  ctx.mode = MODE_SPLIT;
            else die("unknown mode: " S_PRI " (expected 'stb' or 'split')", S_VARG(mode_str));
        }
        else if (str_arg_eq(arg, S("--exclude"), S("-x"))) {
            if (++i >= argc) die("-x requires a pattern");
            if (exclude_count >= MAX_EXCLUDE) die("too many -x patterns");
            exclude_patterns[exclude_count++] = str_from_cstr(argv[i]);
        }
        else if (str_arg_eq(arg, S("--no-strip"), S_EMPTY))         ctx.strip_guards = false;
        else if (str_arg_eq(arg, S("--no-source"), S_EMPTY))        ctx.discover_src = false;
        else if (str_arg_eq(arg, S("--stats"), S_EMPTY))            show_stats       = true;
        else if (str_arg_eq(arg, S("--list"), S_EMPTY))             list_only        = true;
        else if (str_arg_eq(arg, S("--watch"), S("-w")))             watch_mode       = true;
        else if (!str_is_empty(arg) && str_char_at(arg, 0) == '-')  die("unknown option: " S_PRI, S_VARG(arg));
        else {
            if (root_count >= MAX_FILES) die("too many root inputs");
            roots[root_count++] = arg;
        }
    }

    if (root_count == 0) { fprintf(stderr, "cone: no input files\n\n"); usage(); }

    // Derive prefix from -o or first root
    ctx.prefix = derive_prefix(ctx.perm, outpath, roots[0]);

    if (!watch_mode) {
        cone_run(&ctx, outpath, roots, root_count, show_stats, list_only);
    } else {
        // --watch loop: poll file mtimes and re-run when anything changes
        fprintf(stderr, "cone: watching for changes (Ctrl+C to stop)...\n");

        // Initial run
        cone_run(&ctx, outpath, roots, root_count, show_stats, list_only);

        // Collect initial mtimes (allocated from the per-run arena after cone_run)
        f64 *mtimes = arena_push_array(ctx.arena, f64, ctx.file_count);
        if (!mtimes) die("cannot allocate mtime array");
        for (int i = 0; i < ctx.file_count; i++)
            mtimes[i] = fs_mtime(ctx.files[i].path);

        // Track root directory mtimes so new files trigger a rebuild
        f64 root_mtimes[MAX_FILES];
        u32 root_dir_count = 0;
        for (u32 i = 0; i < root_count; i++) {
            if (fs_is_dir(roots[i])) {
                root_mtimes[root_dir_count++] = fs_mtime(roots[i]);
            }
        }

        for (;;) {
            // Sleep 500ms
#ifdef OS_WINDOWS
            Sleep(500);
#else
            usleep(500000);
#endif
            // Check for changes in discovered files
            bool changed = false;
            for (int i = 0; i < ctx.file_count; i++) {
                f64 mt = fs_mtime(ctx.files[i].path);
                if (mt != mtimes[i]) {
                    fprintf(stderr, "cone: changed: " S_PRI "\n",
                            S_VARG(ctx.files[i].display_path));
                    changed = true;
                    break;
                }
            }

            // Check if root directories changed (new/removed files)
            if (!changed) {
                u32 di = 0;
                for (u32 i = 0; i < root_count; i++) {
                    if (fs_is_dir(roots[i])) {
                        f64 mt = fs_mtime(roots[i]);
                        if (mt != root_mtimes[di]) {
                            fprintf(stderr, "cone: directory changed: " S_PRI "\n",
                                    S_VARG(roots[i]));
                            changed = true;
                            break;
                        }
                        di++;
                    }
                }
            }

            if (!changed) continue;

            // Re-run: reset the per-run arena (cwd + prefix live in perm arena)
            arena_reset(ctx.arena);
            ctx.file_count    = 0;
            ctx.bytes_read    = 0;
            ctx.bytes_written = 0;
            scanned_dir_count = 0;

            fprintf(stderr, "\ncone: rebuilding...\n");
            cone_run(&ctx, outpath, roots, root_count, show_stats, list_only);

            // Re-collect file mtimes from the per-run arena
            mtimes = arena_push_array(ctx.arena, f64, ctx.file_count);
            if (!mtimes && ctx.file_count > 0) die("cannot allocate mtime array");
            for (int i = 0; i < ctx.file_count; i++)
                mtimes[i] = fs_mtime(ctx.files[i].path);

            // Re-collect root directory mtimes
            root_dir_count = 0;
            for (u32 i = 0; i < root_count; i++) {
                if (fs_is_dir(roots[i]))
                    root_mtimes[root_dir_count++] = fs_mtime(roots[i]);
            }
        }
    }

    arena_destroy(ctx.arena);
    arena_destroy(ctx.perm);
    return 0;
}
