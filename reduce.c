#include "reduce.h"
#include "barrier.h"
#include "macros.h"
#include "message.h"
#include "report.h"
#include "reapropagate.h"
#include "ring.h"
#include "trace.h"
#include "utilities.h"

#include <inttypes.h>
#include <math.h>

bool reducing (struct ring *ring) {
  return ring->limits.reduce < SEARCH_CONFLICTS;
}

void check_clause_statistics (struct ring *ring) {
#ifndef NDEBUG
  {
    size_t redundant = 0;
    size_t irredundant = 0;

    for (all_ring_literals (lit)) {
      struct references *watches = &REFERENCES (lit);
      for (all_watches (watch, *watches)) {
        if (!is_binary_pointer (watch))
          continue;
        assert (lit == lit_pointer (watch));
        unsigned other = other_pointer (watch);
        if (lit < other)
          continue;
        assert (redundant_pointer (watch));
        redundant++;
      }

      unsigned *binaries = watches->binaries;
      if (!binaries)
        continue;
      for (unsigned *p = binaries, other; (other = *p) != INVALID; p++)
        if (lit < other)
          irredundant++;
    }

    for (all_watchers (watcher)) {
      if (watcher->garbage)
        continue;
      assert (watcher->clause->redundant == watcher->redundant);
      if (watcher->redundant)
        redundant++;
      else
        irredundant++;
    }

    struct ring_statistics *statistics = &ring->statistics;
    assert (statistics->redundant == redundant);
    assert (statistics->irredundant == irredundant);
  }
#else
  (void) ring;
#endif
}

void check_redundant_and_tier2_offsets (struct ring *ring) {
#ifndef NDBEUG
  struct watchers *watchers = &ring->watchers;
  struct watcher *begin = watchers->begin;
  struct watcher *redundant = begin + ring->redundant;
  struct watcher *tier2 = begin + ring->tier2;
  struct watcher *end = watchers->end;

  for (struct watcher *watcher = begin; watcher != redundant; watcher++)
    assert (!watcher->redundant);

  assert (begin <= redundant);
  assert (redundant <= end);

  for (struct watcher *watcher = redundant; watcher != tier2; watcher++) {
    assert (watcher->redundant);
    assert (watcher->glue <= TIER1_GLUE_LIMIT);
  }

  assert (redundant <= tier2);
  assert (tier2 <= end);

  for (struct watcher *watcher = tier2; watcher != end; watcher++)
    assert (watcher->redundant);
#else
  (void) ring;
#endif
}

#define all_literals_on_trail_with_reason(LIT) \
  unsigned *P_##LIT = ring->trail.begin, *END_##LIT = ring->trail.end, \
           LIT; \
  P_##LIT != END_##LIT && (LIT = *P_##LIT, true); \
  ++P_##LIT

static void mark_reasons (struct ring *ring, unsigned start) {
  for (all_literals_on_trail_with_reason (lit)) {
    struct variable *v = VAR (lit);
    struct watch *watch = v->reason;
    if (!watch)
      continue;
    if (is_binary_pointer (watch))
      continue;
    unsigned src = index_pointer (watch);
    if (src < start)
      continue;
    struct watcher *watcher = index_to_watcher (ring, src);
    assert (!watcher->reason);
    watcher->reason = true;
  }
}

static unsigned map_idx (unsigned src, unsigned start, unsigned *map) {
  return (src < start) ? src : map[src - start];
}

static void unmark_reasons (struct ring *ring, unsigned start,
                            unsigned *map) {
  for (all_literals_on_trail_with_reason (lit)) {
    struct variable *v = VAR (lit);
    struct watch *watch = v->reason;
    if (!watch)
      continue;
    if (is_binary_pointer (watch))
      continue;
    unsigned src = index_pointer (watch);
    if (src < start)
      continue;
    unsigned dst = map_idx (src, start, map);
    assert (dst);
    struct watcher *watcher = index_to_watcher (ring, dst);
    assert (watcher->reason);
    watcher->reason = false;
    bool redundant = redundant_pointer (watch);
    unsigned other = other_pointer (watch);
    struct watch *mapped = tag_index (redundant, dst, other);
    v->reason = mapped;
  }
}

static void gather_reduce_candidates (struct ring *ring,
                                      struct unsigneds *candidates) {
  struct watchers *watchers = &ring->watchers;
  struct watcher *begin = watchers->begin;
  struct watcher *end = watchers->end;
  struct watcher *tier2 = begin + ring->tier2;
  for (struct watcher *watcher = tier2; watcher != end; watcher++) {
    if (watcher->garbage)
      continue;
    if (watcher->reason)
      continue;
    if (!watcher->redundant)
      continue;
    if (watcher->glue <= TIER1_GLUE_LIMIT)
      continue;
    if (watcher->used) {
      watcher->used--;
      continue;
    }
    unsigned idx = watcher_to_index (ring, watcher);
    PUSH (*candidates, idx);
  }
  verbose (ring, "gathered %zu reduce candidates %.0f%%",
           SIZE (*candidates),
           percent (SIZE (*candidates), ring->statistics.redundant));
}

static void
mark_reduce_candidates_as_garbage (struct ring *ring,
                                   struct unsigneds *candidates) {
  size_t size = SIZE (*candidates);
  size_t target = REDUCE_FRACTION * size;
  size_t reduced = 0;
  for (all_elements_on_stack (unsigned, idx, *candidates)) {
    struct watcher *watcher = index_to_watcher (ring, idx);
    mark_garbage_watcher (ring, watcher);
    if (++reduced == target)
      break;
  }
  verbose (ring, "reduced %zu clauses %.0f%%", reduced,
           percent (reduced, size));
}

static void flush_references (struct ring *ring, bool fixed, unsigned start,
                              unsigned *map) {
#if !defined(QUIET) || !defined(NDEBUG)
  size_t flushed = 0;
#endif
  signed char *values = ring->values;
  struct variable *variables = ring->variables;
  for (all_ring_literals (lit)) {
    signed char lit_value = values[lit];
    if (lit_value > 0) {
      if (variables[IDX (lit)].level)
        lit_value = 0;
    }
    struct references *watches = &REFERENCES (lit);
    struct watch **begin = watches->begin, **q = begin;
    struct watch **end = watches->end;
    for (struct watch **p = begin; p != end; p++) {
      struct watch *watch = *p;
      if (is_binary_pointer (watch)) {
        assert (lit == lit_pointer (watch));
        if (!fixed) {
          *q++ = watch;
          continue;
        }
        unsigned other = other_pointer (watch);
        assert (lit != other);
        signed char other_value = values[other];
        if (other_value > 0) {
          if (variables[IDX (other)].level)
            other_value = 0;
        }
        if (lit_value > 0 || other_value > 0) {
          if (lit < other) {
            bool redundant = redundant_pointer (watch);
            dec_clauses (ring, redundant);
            trace_delete_binary (&ring->trace, lit, other);
          }
#if !defined(QUIET) || !defined(NDEBUG)
          flushed++;
#endif
        } else
          *q++ = watch;
      } else {
        unsigned src = index_pointer (watch);
        unsigned dst = map_idx (src, start, map);
        if (dst) {
          assert (dst);
          bool redundant = redundant_pointer (watch);
          unsigned other = other_pointer (watch);
          struct watch *mapped = tag_index (redundant, dst, other);
          *q++ = mapped;
        } else {
#if !defined(QUIET) || !defined(NDEBUG)
          flushed++;
#endif
        }
      }
    }
    watches->end = q;
    SHRINK_STACK (*watches);
  }
  assert (!(flushed & 1));
  verbose (ring, "flushed %zu garbage watches from watch lists", flushed);
}

void reduce (struct ring *ring) {
  START (ring, reduce);
  clear_elevated_from_trail (ring);
  check_clause_statistics (ring);
  check_redundant_and_tier2_offsets (ring);
  struct ring_statistics *statistics = &ring->statistics;
  struct ring_limits *limits = &ring->limits;
  statistics->reductions++;
  verbose (ring, "reduction %" PRIu64 " at %" PRIu64 " conflicts",
           statistics->reductions, SEARCH_CONFLICTS);
  bool fixed = ring->last.fixed != ring->statistics.fixed;
  unsigned start = 1;
  if (fixed)
    mark_satisfied_watchers_as_garbage (ring);
  else
    start = ring->tier2;
  mark_reasons (ring, start);
  struct unsigneds candidates;
  INIT (candidates);
  gather_reduce_candidates (ring, &candidates);
  sort_redundant_watcher_indices (ring, SIZE (candidates),
                                  candidates.begin);
  mark_reduce_candidates_as_garbage (ring, &candidates);
  RELEASE (candidates);
  unsigned *map = flush_watchers (ring, start);
  unmark_reasons (ring, start, map);
  flush_references (ring, fixed, start, map);
  free (map);
  check_clause_statistics (ring);
  check_redundant_and_tier2_offsets (ring);
  limits->reduce = SEARCH_CONFLICTS;
  unsigned interval = ring->options.reduce_interval;
  assert (interval);
  limits->reduce += interval * sqrt (statistics->reductions);
  very_verbose (ring, "next reduce limit at %" PRIu64 " conflicts",
                limits->reduce);
  report (ring, '-');
  STOP (ring, reduce);
}
