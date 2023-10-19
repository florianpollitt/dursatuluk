#include "reapalyze.h"

#include <string.h>

#include "assign.h"
#include "backtrack.h"
#include "bump.h"
#include "export.h"
#include "macros.h"
#include "minimize.h"
#include "reapropagate.h"
#include "ring.h"
#include "sort.h"
#include "trace.h"
#include "utilities.h"
#include "variable.h"

static void reap_bump_reason (struct ring *ring, struct watcher *watcher) {
  if (!watcher->redundant)
    return;
  if (watcher->glue <= TIER1_GLUE_LIMIT)
    return;
  if (watcher->glue <= TIER2_GLUE_LIMIT)
    watcher->used = 2;
  else
    watcher->used = 1;
}

static bool reapalyze_reason_side_literal (struct ring *ring, unsigned lit) {
  unsigned idx = IDX (lit);
  struct variable *v = ring->variables + idx;
  if (!v->level)
    return false;
  if (v->seen)
    return false;
  v->seen = true;
  PUSH (ring->analyzed, idx);
  return true;
}

static void reapalyze_reason_side_literals (struct ring *ring) {
  if (!ring->options.bump_reasons)
    return;

  uint64_t *count = &ring->delay.bump_reason.count;
  if (*count) {
    *count -= 1;
    return;
  }

  if (ring->averages[ring->stable].decisions.value > 10)
    return;

  size_t original = SIZE (ring->analyzed);
  size_t limit = 10 * original;
  uint64_t ticks = 0;

  for (all_elements_on_stack (unsigned, lit, ring->clause)) {
    struct variable *v = VAR (lit);
    if (!v->level)
      continue;
    struct watch *reason = v->reason;
    if (!reason)
      continue;
    assert (v->seen || v->shrinkable);
    if (is_binary_pointer (reason)) {
      assert (NOT (lit) == lit_pointer (reason));
      if (reapalyze_reason_side_literal (ring, other_pointer (reason)) &&
          SIZE (ring->analyzed) > limit)
        break;
    } else {
      const unsigned not_lit = NOT (lit);
      struct watcher *watcher = get_watcher (ring, reason);
      ticks++;
      for (all_watcher_literals (other, watcher))
        if (other != not_lit && reapalyze_reason_side_literal (ring, other) &&
            SIZE (ring->analyzed) > limit)
          break;
    }
  }

  ring->statistics.contexts[ring->context].ticks += ticks;

  uint64_t *current = &ring->delay.bump_reason.current;

  if (SIZE (ring->analyzed) > limit) {
    while (SIZE (ring->analyzed) > original)
      ring->variables[POP (ring->analyzed)].seen = false;
    *current += 1;
  } else if (*current)
    *current /= 2;

  *count = *current;
}

static bool reap_larger_trail_position (unsigned *pos, struct variable *vars, unsigned a, unsigned b) {
  unsigned i = IDX (a);
  unsigned j = IDX (b);
  // TODO: check correctness
  return (vars[i].level == vars[j].level && pos[i] > pos[j]) || vars[i].level > vars[j].level;
}

#define REAP_LARGER_TRAIL_POS(A, B) reap_larger_trail_position (pos, vars, (A), (B))

static void reap_sort_deduced_clause (struct ring *ring) {
  LOGTMP ("clause before sorting");
  unsigned *pos = ring->trail.pos;
  struct variable *vars = ring->variables;
  SORT_STACK (unsigned, ring->clause, REAP_LARGER_TRAIL_POS);
  LOGTMP ("clause after sorting");
}

static void reap_clear_analyzed (struct ring *ring) {
  struct unsigneds *analyzed = &ring->analyzed;
  struct variable *variables = ring->variables;
  for (all_elements_on_stack (unsigned, idx, *analyzed)) {
    struct variable *v = variables + idx;
    assert (v->seen);
    v->seen = false;
  }
  CLEAR (*analyzed);

  struct unsigneds *levels = &ring->levels;
  unsigned *used = ring->used;
  for (all_elements_on_stack (unsigned, used_level, *levels))
    used[used_level] = 0;
  CLEAR (*levels);
}

static void reap_update_decision_rate (struct ring *ring) {
  uint64_t current = SEARCH_DECISIONS;
  uint64_t previous = ring->last.decisions;
  assert (current >= previous);
  uint64_t delta = current - previous;
  struct averages *a = ring->averages + ring->stable;
  update_average (ring, &a->decisions, "decision rate", SLOW_ALPHA, delta);
  ring->last.decisions = current;
}

#define REAP_RESOLVE_LITERAL(OTHER) \
  do { \
    if (OTHER == uip) \
      break; \
    assert (ring->values[OTHER] < 0); \
    unsigned OTHER_IDX = IDX (OTHER); \
    struct variable *V = variables + OTHER_IDX; \
    unsigned OTHER_LEVEL = V->level; \
    assert (OTHER_LEVEL <= conflict_level); \
    if (!OTHER_LEVEL) \
      break; \
    if (V->seen) \
      break; \
    V->seen = true; \
    PUSH (*analyzed, OTHER_IDX); \
    if (OTHER_LEVEL == conflict_level) { \
      uint64_t pos = trail->pos[OTHER_IDX]; \
      pos = -pos - 1; \
      assert (reap_size (&ring->reap) < ring->size); \
      reap_push (reap, pos); \
      open++; \
      break; \
    } \
    PUSH (*ring_clause, OTHER); \
    if (!used[OTHER_LEVEL]) { \
      glue++; \
      used[OTHER_LEVEL] = 1; \
      PUSH (*levels, OTHER_LEVEL); \
      if (OTHER_LEVEL > jump) \
        jump = OTHER_LEVEL; \
    } \
  } while (0)

#define REAP_CONFLICT_LITERAL(LIT_ARG) \
  do { \
    unsigned LIT = (LIT_ARG); \
    unsigned LIT_IDX = IDX (LIT); \
    struct variable *V = ring->variables + LIT_IDX; \
    unsigned LIT_LEVEL = V->level; \
    if (forced_literal == INVALID_LIT || LIT_LEVEL > conflict_level) { \
      conflict_level = LIT_LEVEL; \
      literals_on_conflict_level = 1; \
      forced_literal = LIT; \
    } else if (LIT_LEVEL == conflict_level) \
      literals_on_conflict_level++; \
  } while (0)

bool reapalyze (struct ring *ring, struct watch *reason) {
  assert (!ring->inconsistent);
  if (!ring->level) {
    set_inconsistent (ring, "conflict on root-level produces empty clause");
    return false;
  }
  unsigned conflict_level = 0;
  unsigned literals_on_conflict_level = 0;
  unsigned forced_literal = INVALID_LIT;
  assert (reason);
  if (is_binary_pointer (reason)) {
    unsigned lit = lit_pointer (reason);
    unsigned other = other_pointer (reason);
    REAP_CONFLICT_LITERAL (lit);
    REAP_CONFLICT_LITERAL (other);
  } else {
    struct watcher *watcher = get_watcher (ring, reason);
    for (all_watcher_literals (lit, watcher))
      REAP_CONFLICT_LITERAL (lit);
  }
  assert (conflict_level <= ring->level);
  if (conflict_level < ring->level) {
    LOG ("forced to backtrack to conflict level %u", conflict_level);
    backtrack (ring, conflict_level);
  } else
    LOG ("conflict level %u matches decision level", conflict_level);
  if (!conflict_level) {
    set_inconsistent (ring, "conflict on root-level produces empty clause");
    return false;
  }
  if (literals_on_conflict_level == 1) {
    LOG ("only literal %s on conflict level", LOGLIT (forced_literal));
    // assert (false);   // reimply should completely avoid this!! obviously wrong?
    backtrack (ring, conflict_level - 1);
    LOGWATCH (reason, "forcing %s through", LOGLIT (forced_literal));
    if (is_binary_pointer (reason)) {
      unsigned lit = lit_pointer (reason);
      unsigned other = other_pointer (reason);
      assert (lit == forced_literal || other == forced_literal);
      other = lit ^ other ^ forced_literal;
      assert (other != forced_literal);
      bool redundant = redundant_pointer (reason);
      reason = tag_binary (redundant, forced_literal, other);
    }
    // push reapropagate_later lits on reap.
    push_reapropagate_later (ring);
    assign_with_reason (ring, forced_literal, reason);
    return true;
  } else
    LOG ("conflict has %u literals on conflict level",
         literals_on_conflict_level);
  struct unsigneds *ring_clause = &ring->clause;
  struct unsigneds *analyzed = &ring->analyzed;
  struct unsigneds *levels = &ring->levels;
  assert (EMPTY (*ring_clause));
  assert (EMPTY (*analyzed));
  assert (EMPTY (*levels));
  unsigned *used = ring->used;
  struct variable *variables = ring->variables;
  struct ring_trail *trail = &ring->trail;
  struct reap *reap = &ring->analyze_reap;
  assert (reap_empty (reap));
#ifndef NDEBUG
  unsigned *t = trail->end;
#endif
  PUSH (*ring_clause, INVALID);
  const unsigned level = ring->level;
  unsigned uip = INVALID, jump = 0, glue = 0, open = 0;
  for (;;) {
    assert (reason);
    LOGWATCH (reason, "analyzing");
    if (is_binary_pointer (reason)) {
      unsigned lit = lit_pointer (reason);
      unsigned other = other_pointer (reason);
      REAP_RESOLVE_LITERAL (lit);
      REAP_RESOLVE_LITERAL (other);
    } else {
      struct watcher *watcher = get_watcher (ring, reason);
      reap_bump_reason (ring, watcher);
      for (all_watcher_literals (lit, watcher))
        REAP_RESOLVE_LITERAL (lit);
    }
    const unsigned pos = -(reap_pop (reap) + 1);
    uip = trail->begin[pos];
#ifndef NDEBUG
    struct variable *v;
    unsigned debug_lit;
    do {
      assert (t > ring->trail.begin);
      debug_lit = *--t;
      unsigned uip_idx = IDX (debug_lit);
      v = ring->variables + uip_idx;
    } while (debug_lit == INVALID_LIT || !v->seen || v->level != conflict_level);
    assert (uip == debug_lit);
#endif
    --open;
    assert ((size_t) open == reap_size (reap));
    if (reap_empty (reap)) break;

    reason = variables[IDX (uip)].reason;
    assert (reason);
  }
  assert (reap_empty (reap));
  reap_clear (reap);
  LOG ("back jump level %u", jump);
  struct averages *a = ring->averages + ring->stable;
  update_average (ring, &a->level, "level", SLOW_ALPHA, jump);
  LOG ("glucose level (LBD) %u", glue);
  update_average (ring, &a->glue.slow, "slow glue", SLOW_ALPHA, glue);
  update_average (ring, &a->glue.fast, "fast glue", FAST_ALPHA, glue);
  unsigned assigned = SIZE (ring->trail);
  double filled = percent (assigned, ring->size);
  LOG ("assigned %u variables %.0f%% filled", assigned, filled);
  update_average (ring, &a->trail, "trail", SLOW_ALPHA, filled);
  reap_update_decision_rate (ring);
  unsigned *literals = ring_clause->begin;
  const unsigned not_uip = NOT (uip);
  literals[0] = not_uip;
  LOGTMP ("first UIP %s", LOGLIT (uip));
  shrink_or_minimize_clause (ring, glue);
  reapalyze_reason_side_literals (ring);
  bump_variables (ring);
  unsigned back = level - 1;
  backtrack (ring, back);
  update_best_and_target_phases (ring);
  if (jump != back) {
    if (!ring->options.chronological ||
        back < ring->options.backjump_limit ||
        back - ring->options.backjump_limit <= jump)
      backtrack (ring, jump);
    else {
      LOG ("chronological backtracking only (staying at %u not %u)", back,
           jump);
      ring->statistics.contexts[ring->context].chronological++;
    }
  }
  // push reapropagate_later lits on reap.
  push_reapropagate_later (ring);
  unsigned size = SIZE (*ring_clause);
  assert (size);
  if (size == 1) {
    trace_add_unit (&ring->trace, not_uip);
    assign_ring_unit (ring, not_uip);
    ring->iterating = 1;
  } else {
    unsigned other = literals[1];
    struct watch *learned;
    if (size == 2) {
      assert (VAR (other)->level == jump);
      learned = new_local_binary_clause (ring, true, not_uip, other);
      trace_add_binary (&ring->trace, not_uip, other);
      export_binary_clause (ring, learned);
    } else {
      if (ring->options.sort_deduced)
        reap_sort_deduced_clause (ring);
      else if (VAR (other)->level != jump) {  // TODO: check correctness
        unsigned *p = literals + 2, replacement;
        while (assert (p != ring_clause->end),
               VAR (replacement = *p)->level != jump)
          p++;
        literals[1] = replacement;
        assert (VAR (replacement)->level == jump);
        *p = other;
      }
      assert (VAR (literals[1])->level >= jump);
      struct clause *learned_clause =
          new_large_clause (size, literals, true, glue);
      learned_clause->origin = ring->id;
      LOGCLAUSE (learned_clause, "new");
      learned =
          watch_first_two_literals_in_large_clause (ring, learned_clause);
      assert (!is_binary_pointer (learned));
      trace_add_clause (&ring->trace, learned_clause);
      export_large_clause (ring, learned_clause);
    }
    assign_with_reason (ring, not_uip, learned);
  }
  CLEAR (*ring_clause);
  reap_clear_analyzed (ring);

  return true;
}
