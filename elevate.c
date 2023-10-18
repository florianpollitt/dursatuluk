#include "assign.h"
#include "macros.h"
#include "ruler.h"
#include "trace.h"

// potentially useful modes: find level vs use given level
//                           maybe elevate vs definitely elevate
#define UNIT_REASON 0
#define USE_LEVEL 1
#define USE_REASON_MAYBE 2
#define USE_REASON 3

static unsigned elevate (struct ring *ring, unsigned lit, struct watch *reason,
                    unsigned assignment_level, int type) {

  if (ring->elevated_on_trail == ring->size)
    clear_elevated_from_trail (ring);
  
  assert (ring->elevated_on_trail < ring->size);
  ring->elevated_on_trail++;

  unsigned idx = IDX (lit);

  assert (idx < ring->size);
  assert (ring->values[lit] > 0);
  assert (ring->values[NOT (lit)] < 0);
  assert (!ring->inactive[idx] || type == USE_REASON_MAYBE);

  struct variable *v = ring->variables + idx;
  const unsigned level = v->level;
  unsigned replacement = INVALID_LIT;
  assert (level <= ring->level);
  assert (ring->level > 0 || type == USE_REASON_MAYBE);
  if (type == UNIT_REASON) {
    assert (!assignment_level);
    assert (!reason);
    assignment_level = 0, reason = 0;
  } else if (type == USE_LEVEL) {
    // TODO: maybe allow binary reasons and change reason sometimes like below??
    assert (!reason || !is_binary_pointer (reason));
  } else if (is_binary_pointer (reason)) {
    unsigned other = other_pointer (reason);
    unsigned other_idx = IDX (other);
    struct variable *u = ring->variables + other_idx;
    assignment_level = u->level;
    replacement = other;
    if (type == USE_REASON_MAYBE && assignment_level >= level) {
      LOGWATCH (reason, "not elevating %s reason", LOGLIT (lit));
      return replacement;
    }
    if (assignment_level && is_binary_pointer (u->reason)) {
      bool redundant =
          redundant_pointer (reason) || redundant_pointer (u->reason);
      reason = tag_binary (redundant, lit, other_pointer (u->reason));
    }
  } else {
    assignment_level = 0;
    struct watcher *watcher = get_watcher (ring, reason);
    for (all_watcher_literals (other, watcher)) {
      if (other == lit)
        continue;
      unsigned other_idx = IDX (other);
      struct variable *u = ring->variables + other_idx;
      unsigned other_level = u->level;
      if (other_level > assignment_level) {
        assignment_level = other_level;
        replacement = other;
      }
    }
  }

  assert (type == UNIT_REASON || type == USE_LEVEL || replacement != INVALID_LIT);
  assert (assignment_level <= ring->level);
  if (type == USE_REASON_MAYBE && assignment_level >= level) {
    assert (reason);
    LOGWATCH (reason, "not elevating %s reason", LOGLIT (lit));
    return replacement;
  }
  assert (assignment_level < level);
  v->level = assignment_level;

  if (!assignment_level) {
    if (reason)
      trace_add_unit (&ring->trace, lit);
    v->reason = 0;
    ring->statistics.fixed++;
    assert (ring->statistics.active);
    ring->statistics.active--;
    assert (!ring->inactive[idx]);
    ring->inactive[idx] = true;
    *ring->ring_units.end++ = lit;
  } else
    v->reason = reason;

  struct ring_trail *trail = &ring->trail;
  
  // clearing old trail position to avoid confusion
  size_t old_pos = trail->pos[idx];
  *(trail->begin + old_pos) = INVALID_LIT;
  
  size_t pos = SIZE (*trail);
  // assert (pos < ring->size);
  trail->pos[idx] = pos;
  // might fail...
  // assert (trail->end < trail->begin + ring->size);
  *trail->end++ = lit;

  assert (ring->options.reimply);
  uint64_t res = assignment_level;
  assert (pos < UINT_MAX);
  res <<= 32;
  res |= pos;
  LOG ("push %s on reap with level %d and pos %ld = key %"
       PRId64, LOGLIT (lit), assignment_level, pos, res);
  assert (reap_size (&ring->reap) < ring->size);
  reap_push (&ring->reap, res);
  
#ifdef LOGGING
  if (reason)
    LOGWATCH (reason, "elevating %s reason", LOGLIT (lit));
  else
    LOG ("elevating %s", LOGLIT (lit));
#endif
  return replacement;
}

void elevate_with_reason_and_level (struct ring *ring, unsigned lit, unsigned level,
                         struct watch *reason) {
  assert (reason);
  (void) elevate (ring, lit, reason, level, USE_LEVEL);
  LOGWATCH (reason, "elevate %s with reason and level", LOGLIT (lit));
}

void elevate_with_reason (struct ring *ring, unsigned lit,
                         struct watch *reason) {
  assert (reason);
  (void) elevate (ring, lit, reason, 0, USE_REASON);
  LOGWATCH (reason, "elevate %s with reason", LOGLIT (lit));
}

unsigned maybe_elevate_with_reason (struct ring *ring, unsigned lit,
                         struct watch *reason) {
  assert (reason);
  unsigned replacement = elevate (ring, lit, reason, 0, USE_REASON_MAYBE);
  
#ifdef LOGGING
  if (replacement != INVALID_LIT)
    LOGWATCH (reason, "elevate %s with reason", LOGLIT (lit));
#endif
  return replacement;
}


void elevate_ring_unit (struct ring *ring, unsigned unit) {
  (void) elevate (ring, unit, 0, 0, UNIT_REASON);
  LOG ("elevate %s unit", LOGLIT (unit));
}
