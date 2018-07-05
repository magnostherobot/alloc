#if 0
  (
    echo "PROJECT_NAME=alloc"
    echo "INPUT=myalloc.c"
    echo "OPTIMIZE_OUTPUT_FOR_C=YES"
    echo "EXTRACT_STATIC=YES"
    echo "GENERATE_LATEX=NO"
    echo "GENERATE_HTML=YES"
    echo "HTML_OUTPUT=docs"
  ) | doxygen -
  exit
#endif

/**
 * @file myalloc.c
 * @author Stuart Norcross
 * @author Tom Harley
 * $Date: 4 Oct 2017 $
 * @brief Implementation of malloc and free
 *
 * Implemented `malloc` and `free` under the names `myalloc` and
 * `myfree` respectively.
 *
 * This file was originally created by Stuart Norcross on 12/03/2010
 * and has been edited by Tom Harley.
 */

// for sysconf():
#include <unistd.h>
// for bool:
#include <stdbool.h>
// for size_t:
#include <stddef.h>
// for mmap(), munmap() and associated constants:
#include <sys/mman.h>
// for uintptr_t:
#include <stdint.h>
// for assert():
#include <assert.h>

#include "myalloc.h"

/**
 * @brief Returns `n` rounded up the nearest multiple of `t`.
 *
 * If `n` is already a multiple of `t`, `n` is returned.
 *
 * @param n The value to round up.
 * @param t The modulus to use when rounding.
 */
#define round_up(n, t) (((n) % (t)) ? (((n) / (t)) + 1) * (t) : (n))

/**
 * @brief A data type exactly one byte wide.
 *
 * A simple zero-cost abstraction since logically chars are not being used.
 */
typedef char byte;

/**
 * @brief Header containing persistent information about the
 * directly-following memory.
 *
 * Although this `struct` only contains one value, it is left as
 * a `struct`:
 *  - to promote alignment of the following memory by the compiler,
 *  - to allow the addition of other values at a later date.
 */
typedef struct header {
  /** The size of the headed memory space, in bytes. */
  size_t size;
} header;

/**
 * @brief Non-persistent information related to a memory space.
 *
 * Any information related to a memory space that is unreliable after
 * being given to a user and later returned should go here.
 *
 * This `struct` is placed straight after the memory space's `header`,
 * inside the memory that would be given to the user, and is
 * theoretically overwritten by the user. This is done to reduce the
 * space taken up by `header`s.
 */
typedef struct flnode {
  /** The next `flnode` in the free-list. */
  struct flnode* next;
  /** The previous `flnode` in the free-list. */
  struct flnode* prev;
} flnode;

/**
 * @brief Total size required to store information about a chunk of memory.
 */
static const size_t META_SIZE = sizeof(header) + sizeof(flnode);

/**
 * @brief Global marker representing start of free-list.
 */
static header* start = NULL;

/**
 * @brief Global marker representing end of free-list.
 */
static header* end = NULL;

/**
 * @brief Global "constant" representing the size of a page in bytes.
 *
 * Calculated at runtime.
 */
static long PAGE_SIZE = 0;

/**
 * @brief Returns the `header` associated with the given `node`.
 *
 * @param n The `node` to find the `header` for.
 * @returns The `header` associated with the given `node`.
 */
static header* get_header(flnode* n);

/**
 * @brief Returns the `node` associated with the given `header`.
 *
 * @param h The `header` to find the `node` for.
 * @returns The `node` associated with the given `header`.
 */
static flnode* get_node(header* h);

/**
 * @brief Returns a pointer pointing at the "end" of the given `header`.
 *
 * @param h The `header` to find the "end" of.
 * @returns A pointer pointing to the "end" of the given `header`.
 */
static byte* end_of_header(header* h);

/**
 * @brief Returns the last `flnode` in a free-list.
 *
 * @param start_of_list The start of the list to find the end of.
 * @returns The `flnode` of the last item in the list.
 */
static flnode* last_node(header* start_of_list);

/**
 * @brief Finds the first item in a free-list with enough space to store
 * data of size `s`.
 *
 * @param minimum_size The minimum size of the `flnode`-to-be-returned, in
 * bytes.
 * @param start_of_list The free-list to search through.
 * @returns The first item in the free-list with enough space to store data
 * of `s` bytes; `NULL` otherwise.
 */
static header* first_enough_space(
  size_t minimum_size, flnode* start_of_list);

/**
 * @brief Finds the first item in a free-list with enough space to store
 * data of size `s`.
 *
 * @param minimum_size The minimum size of the `flnode`-to-be-returned, in
 * bytes.
 * @param start_of_list The free-list to search through.
 * @returns The smallest item in the free-list with enough space to store
 * data of `s` bytes; `NULL` otherwise.
 */
static header* smallest_enough_space(
  size_t minimum_size, flnode* start_of_list);

/**
 * @brief Finds the last item in a free-list that precedes a given `flnode`.
 *
 * If `m` is `NULL`, uses the global variable `start` in its place.
 *
 * @param n The `flnode` to check against.
 * @param start_of_list The start of the free-list to traverse.
 * @returns The `flnode` that would be before `n` in the free-list,
 * were `n` in the free-list.
 */
static flnode* node_before(flnode* n, flnode* start_of_list);

/**
 * @brief Checks if two `flnode`s represent spaces directly adjacent in
 * memory.
 *
 * @param left_node The "left" (smaller-address) `flnode`.
 * @param right_node The "right" (larger-address) `flnode`.
 * @returns `TRUE` if `n` directly precedes `m` in memory, `FALSE`
 * otherwise.
 */
static bool is_contiguous(flnode* left_node, flnode* right_node);

/**
 * @brief Stitches two contiguous `flnode`s together.
 *
 * The size of the new `flnode` is calculated as the sum of the sizes of the
 * two given `flnode`s, plus the size of a `header`.
 *
 * @param left_node The "left" (smaller-address) `flnode`.
 * @param right_node The "right" (larger-address) `flnode`.
 * @returns The `flnode` produced from the stitch (usually `n`).
 */
static flnode* stitch(flnode* left_node, flnode* right_node);

/**
 * @brief Splits a memory space into two.
 *
 * The `header` given as `l` will always be preserved, and will never be
 * the `header` returned by `split`.
 *
 * @param to_split The `header` of the memory to split.
 * @param minimum_split_size The minimum size of the resulting memory space.
 * @param size_includes_header Whether or not `size` includes the size of a
 * `header`.
 * @returns The `header` of the new space produced by the split.
 */
static header* split(header* to_split, size_t minimum_split_size,
    bool size_includes_header);

/**
 * @brief Removes a `flnode` from a free-list.
 *
 * @param to_remove The `flnode` to remove.
 */
static void remove_node(flnode* to_remove);

/**
 * @brief Adds a `flnode` to a free-list.
 *
 * The `flnode`-to-be-added may be stitched together with an adjacent
 * `flnode`(s). For this reason, it's important to use the value returned
 * by `add_node`.
 *
 * @param to_add The `flnode` to add to the free-list.
 * @returns The `flnode` added to the free-list.
 */
static flnode* add_node(flnode* to_add);

/**
 * @brief `munmap`s all pages contained _entirely_ by the given memory
 * space.
 *
 * @param h The `header` to `munmap` from.
 * @returns The `header` heading the remainder space on the other side
 * of the unmapped memory from `h` (or `NULL` if there is no remainder
 * there).
 */
static header* unmap_excess_pages(header* h);

/**
 * @brief `mmap`s for extra pages.
 *
 * @param minimum_size The minimum number of bytes of memory required.
 * @returns The `header` of some newly-allocated space capable of storing
 * at least `min` bytes.
 */
static header* more_memory(size_t minimum_size);

/**
 * @brief Allocates memory for the user to use for data storage.
 *
 * @param size The size of the memory space requested, in bytes.
 * @returns A pointer to memory, at least the size of that requested,
 * that the user can write to, or `NULL` if such memory cannot be
 * allocated.
 */
void* myalloc(int size);

/**
 * @brief Frees a chunk of memory, allowing other processes to use it.
 *
 * @param ptr A pointer to the start of the memory that should be freed.
 */
void myfree(void* ptr);

#ifdef MYALLOC_DEBUG
  #include <stdio.h>

  #define debug(...) fprintf(stderr, __VA_ARGS__)

  void debug_print_list(header* s) {
    long unsigned i = 0;
    while (s && get_node(s)) {
      debug("|%p -> %p|\n", s, end_of_header(s) + s->size);
      s = get_header(get_node(s)->next);
      ++i;
    }
    debug("free-list is %lu items long\n", i);
  }
#else
  #define debug(...)
  #define debug_print_list(s)
#endif

static header* get_header(flnode* n) {
  return ((header*) n) - 1;
}

static flnode* get_node(header* h) {
  return (flnode*) (h + 1);
}

static byte* end_of_header(header* h) {
  return (byte*) (h + 1);
}

static flnode* last_node(header* h) {
  flnode* n = get_node(h);
  for (; n->next; n = n->next);
  return n;
}

static header* first_enough_space(size_t s, flnode* n) {
  for (; n; n = n->next) {
    header* h = get_header(n);
    if (h->size >= s) {
      return h;
    }
  }
  return NULL;
}

static header* smallest_enough_space(size_t s, flnode* n) {
  struct { header* adr; size_t size; } t;
  t.adr = NULL;
  for (; n; n = n->next) {
    header* h = get_header(n);
    size_t x = h->size;
    if (x == s) {
      return h;
    }
    if (x > s) {
      if ((!t.adr) || (x < t.size)) {
        t.adr = h;
        t.size = x;
      }
    }
  }
  return t.adr;
}

static flnode* node_before(flnode* n, flnode* m) {
  debug("finding node before %p...", n);
  m = m ? m : get_node(start);
  flnode* p = NULL;
  while (m) {
    if (m >= n) {
      break;
    }
    p = m;
    m = m->next;
  }
  debug("got %p\n", p);
  return p;
}

static bool is_contiguous(flnode* n, flnode* m) {
  header* nh = get_header(n);
  header* mh = get_header(m);
  bool ret = (header*) (end_of_header(nh) + (nh->size)) == mh;
  debug("is %p + %zu + %i == %p? %s\n", nh, nh->size, sizeof(header), mh,
    ret ? "yes" : "no");
  return ret;
}

static flnode* stitch(flnode* n, flnode* m) {
  debug("stitching %p to %p...", n, m);
  get_header(n)->size += get_header(m)->size + sizeof(header);
  debug("done\n");
  return n;
}

static header* split(header* l, size_t size, bool size_includes_header) {
  size_t rs = size - (size_includes_header ? sizeof(header) : 0);
  if (rs < sizeof(flnode)) {
    rs = sizeof(flnode);
  }
  rs = round_up(rs, sizeof(header));

  if (l->size < (rs + (size_includes_header ? 0 : sizeof(header)))) {
    return NULL;
  }
  size_t ls = l->size - rs - (size_includes_header ? 0 : sizeof(header));
  if (ls < sizeof(flnode)) {
    return NULL;
  }

  debug("splitting node at %p (%zu", l, l->size);
  l->size = ls;
  header* r = (header*) (end_of_header(l) + ls);
  r->size = rs;
  debug("->>%zu) new node at %p\n", l->size, r);

  return r;
}

static void remove_node(flnode* n) {
  debug("removing %p from free-list (%p and %p)\n", n, n->next, n->prev);
  if (n == get_node(start)) start = n->next ? get_header(n->next) : NULL;
  if (n->next) n->next->prev = n->prev;
  if (n->prev) n->prev->next = n->next;
  if (n == get_node(end)) end = n->prev ? get_header(n->prev) : NULL;
}

static flnode* add_node(flnode* n) {
  flnode* m;

  debug("adding %p to freelist...\n", n);
  m = node_before(n, NULL);
  if (m) {
    // if there is a node before n in the freelist
    if (is_contiguous(m, n)) {
      // if n is directly after the node before it
      stitch(m, n);
      n = m;
    } else {
      if (m->next) {
        // if n isn't the new last node in the list
        m->next->prev = n;
      } else {
        // if n is the new last node in the list
        end = get_header(n);
      }
      n->next = m->next;
      n->prev = m;
      m->next = n;
    }
  } else {
    // if there is not a node preceding n in the list
    get_node(start)->prev = n;
    n->next = get_node(start);
    start = get_header(n);
  }

  m = n->next;
  if (m && is_contiguous(n, m)) {
    stitch(n, m);
    remove_node(m);
  }

  return n;
}

static header* unmap_excess_pages(header* h) {
  debug("investigating %p for free pages...", h);
  if ((h->size + sizeof(header)) < PAGE_SIZE) {
    return h;
  }

  // find the first page boundary after the start of the node
  byte* p = (byte*) h;

  // some casting for pointer arithmetic
  uintptr_t pi = (uintptr_t) p;
  uintptr_t qi = pi;
  if (qi % PAGE_SIZE) {
    qi = round_up(qi + META_SIZE, PAGE_SIZE);
  }

  byte* q = (byte*) qi;
  byte* e = p + h->size + sizeof(header);

  // find number of free pages
  int pages = (e - q) / PAGE_SIZE;
  debug("found %i pages to unmap\n", pages);

  // I can't find anywhere what munmap-ing with a range of 0 does,
  // so this is just in case it would do something bad:
  if (!pages) {
    return h;
  }

  size_t r = e - (q + (pages * PAGE_SIZE));

  header* rh = NULL;
  if (r) {
    rh = split(h, r, true);
    if (!rh) {
      --pages;
      if (!pages) {
        return h;
      }
      rh = split(h, r + PAGE_SIZE, true);
    }
  }

  if (q == (byte*) h) {
    remove_node(get_node(h));
  } else {
    h->size = q - end_of_header(h);
  }

  munmap(q, pages * PAGE_SIZE);

  return rh;
}

static header* more_memory(size_t min) {
  static const int PFLAGS = PROT_EXEC | PROT_READ | PROT_WRITE;
  static const int FLAGS = MAP_ANONYMOUS | MAP_PRIVATE;

  if (!PAGE_SIZE) {
    PAGE_SIZE = sysconf(_SC_PAGESIZE);
    assert((META_SIZE / PAGE_SIZE) == 0);
  }

  size_t claimed_size = round_up(min + sizeof(header), PAGE_SIZE);

  debug("asking for %luB (<=%lu page(s))...", min, claimed_size / PAGE_SIZE);
  header* out = (header*) mmap(NULL, claimed_size, PFLAGS, FLAGS, -1, 0);
  debug("got %p -> %p\n", out, ((byte*) out) + claimed_size);

  out->size = claimed_size - sizeof(header);

  flnode* outn = get_node(out);
  outn->next = NULL;
  outn->prev = NULL;

  return out;
}

void* myalloc(int size) {
  if (size < 1) {
    return NULL;
  }

  size_t min = (size_t) size;

  if (!start) {
    // we should get some memory
    start = more_memory(min);
    end = start;
  }

  header* h = smallest_enough_space(min, get_node(start));
  if (!h) {
    // we need a bigger contiguous space
    h = get_header(add_node(get_node(more_memory(min))));
  }

  header* g = split(h, min, false);
  if (!g) {
    remove_node(get_node(h));
    g = h;
    if (g == start) {
      start = NULL;
    }
  }

  debug_print_list(start);

  return end_of_header(g);
}

void myfree(void* ptr){
  flnode* n = (flnode*) ptr;
  n->next = NULL;
  n->prev = NULL;
  debug("%p has been freed!\n", ptr);
  if (!start) {
    start = get_header(n);
  } else {
	  n = add_node(n);
    unmap_excess_pages(get_header(n));
  }
  debug_print_list(start);
}
