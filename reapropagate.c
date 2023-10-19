#include "reapropagate.h"
#include "assign.h"
#include "elevate.h"
#include "macros.h"
#include "message.h"
#include "reap.h"
#include "ruler.h"
#include "utilities.h"


void clear_elevated_from_trail (struct ring *ring) {
  if (!ring->options.reimply || !ring->elevated_on_trail) return;
  LOG ("clearing %d elevated literals from trail", ring->elevated_on_trail);
  struct ring_trail *trail = &ring->trail;
  unsigned *begin = trail->begin, *p = begin;
  unsigned *end = trail->end, *q = begin;
  size_t pos = 0;
  while (p != end) {
    unsigned lit = *q++ = *p++;
    if (lit == INVALID_LIT) { 
      q--;
      continue;
    }
    unsigned idx = IDX (lit);
    trail->pos[idx] = pos++;
  }
  trail->end = q;
  ring->elevated_on_trail = 0;
  ring->statistics.trail_clears++;
  assert (SIZE (*trail) == pos);
}

void push_reapropagate_later (struct ring *ring) {
  struct reap *reap = &ring->reap;
  struct unsigneds *later = &ring->reapropagate_later;
  assert (reap_empty (reap));
  LOG ("push up to %ld literals from reapropagate later on reap", SIZE (*later));
  for (unsigned *p = later->begin; p != later->end; ++p) {
    unsigned lit = *p;
    assert (ring->values[lit] >= 0);  // TODO: this assertion might not be true
    if (ring->values[lit] > 0)
      REAP_PUSH (lit, ring);
  }
  CLEAR (*later);
}

void init_reapropagate (struct ring *ring, unsigned *propagate) {
  // only used after walk
  struct ring_trail *trail = &ring->trail;
  struct reap *reap = &ring->reap;
  assert (reap_empty (reap));
  // reap_clear (reap);
  const unsigned *end = trail->end;
  for (unsigned *p = propagate; p != end; ++p) {
    int lit = *p;
    if (lit == INVALID_LIT) continue;
    // assert (ring->values[lit] > 0); -> fails because values are fixed later
    REAP_PUSH (lit, ring);
  }
}

struct watch *ring_reapropagate (struct ring *ring, bool stop_at_conflict,
                                struct clause *ignore) {
  assert (ring->options.reimply);
  assert (!ring->inconsistent);
  assert (!ignore || !is_binary_pointer (ignore));
  struct ring_trail *trail = &ring->trail;
  struct reap *reap = &ring->reap;
  struct variable *variables = ring->variables;
  struct watch *conflict = 0;
  struct watch *saved_conflict = 0;
  unsigned saved_conflict_level = INVALID;
#ifdef METRICS
  uint64_t *visits = ring->statistics.contexts[ring->context].visits;
#endif
  signed char *values = ring->values;
  uint64_t ticks = 0, propagations = 0, elevations = 0;
  while (!reap_empty (reap)) {
    uint64_t reap_element = reap_pop (reap);
    unsigned pos = (unsigned) reap_element;  // is this cast always correct?
    unsigned lit = trail->begin[pos];
    if (lit == INVALID_LIT) continue;  // trail pos gets cleared for elevated literals
    struct variable *v = variables + IDX (lit);
    assert ((unsigned) (reap_element >> 32) == v->level);
    if (v->level >= saved_conflict_level) {
      assert (saved_conflict);
      conflict = saved_conflict;
    }
    if (stop_at_conflict && conflict)
      break;
    bool reapropagate_later = false;
    // assert (*trail->propagate == lit);  // breaks with reimply
    // needed for phases...?  need different solution for reimply...
    // difference between global assignments and unpropagated literals.
    // trail->propagate++;

    LOG ("reapropagating %s", LOGLIT (lit));
    propagations++;
    unsigned not_lit = NOT (lit);
    assert (values[not_lit] < 0);
    struct references *watches = &REFERENCES (not_lit);

    // First traverse all irredundant (globally shared) binary clauses
    // with this literal (negation of propagated one) if there are any.
    // These binary clauses are encoded by a flat array of the 'other'
    // literals in binary clauses for each literal (including this one)
    // and only need to be allocated once and can thus be shared among all
    // threads, since these irredundant binary clauses do not change
    // during search (and are collected during cloning of rings).

    unsigned *binaries = watches->binaries;
    if (binaries) {
      unsigned other, *p;
      for (p = binaries; (other = *p) != INVALID; p++) {
        struct watch *watch = tag_binary (false, other, not_lit);
        signed char other_value = values[other];
        if (other_value < 0) {
          // fake conflicts need to be fixed later
          unsigned cl = (variables + IDX (other))->level;
          if (cl > v->level) {
            if (!reapropagate_later) {
              reapropagate_later = true;
              PUSH (ring->reapropagate_later, lit);
            }
            if (!saved_conflict || cl < saved_conflict_level) {
              saved_conflict_level = cl;
              saved_conflict = watch;
            }
          } else
            conflict = watch;
          if (conflict && stop_at_conflict)
            break;
        } else if (!other_value) {
          struct watch *reason = tag_binary (false, other, not_lit);
          assign_with_reason (ring, other, reason);
          ticks++;
        } else {
          // maybe elevate
          struct watch *reason = tag_binary (false, other, not_lit);
          (void) maybe_elevate_with_reason (ring, other, reason);
          elevations++;
          ticks++;  // not sure exactly but probably need to increase ticks.
        }
      }

      ticks += cache_lines (p, binaries);
      if (stop_at_conflict && conflict)
        break;
    }

    // Then traverse (and update) the watch list of the literal.

    struct watch **begin = watches->begin, **q = begin;
    struct watch **end = watches->end, **p = begin;

    ticks++;

    while (p != end) {
      assert (!stop_at_conflict || !conflict);
      struct watch *watch = *q++ = *p++;

      // This tagged 'watch' pointer is either a binary watch or an
      // index to the corresponding watcher in the (ring/thread local)
      // watcher stack.  Tagging uses bit-stuffing to distinguish these
      // two cases, through the least significand bit actually.

      // If the clause is binary (least significand bit set) we find the
      // other literal of the binary clause in the upper half of the
      // pointer (together with another bit which encodes redundancy).
      // The lower half of the pointer encodes the negation of the
      // propagated literal.

      // For larger (non-binary) clauses we have a similar situation and
      // store in the upper half of the watch pointer word the blocking
      // literal (conceptually an abitrary literal of the clause but
      // supposed to be different from the negated propagaged literal).
      // The other literal of binary clauses plays the same role.

      // Now we check first, which often happens, whether this blocking
      // literal of both binary and large clauses is actually already
      // satisfied, in which case we just continue (and keep the watch).

      unsigned blocking = other_pointer (watch);
      assert (lit != blocking);
      assert (not_lit != blocking);
      signed char blocking_value = values[blocking];
      unsigned blocking_idx = IDX (blocking);
      struct variable *vblock = variables + blocking_idx;
      
      // TODO: not sure if this breaks watch invariant for reimply
      // if blocking != other
      if (vblock->level <= v->level && blocking_value > 0)
        continue;

      if (is_binary_pointer (watch)) {
        assert (lit_pointer (watch) == not_lit);
        if (blocking_value < 0) {
          if (vblock->level > v->level) {
            if (!reapropagate_later) {
              reapropagate_later = true;
              PUSH (ring->reapropagate_later, lit);
            }
            if (!saved_conflict || vblock->level < saved_conflict_level) {
              saved_conflict_level = vblock->level;
              saved_conflict = watch;
            }
          } else
            conflict = watch;
          if (conflict && stop_at_conflict)
            break;
        } else if (!blocking_value) {
          // Only learned and thus redundant clauses are kept as
          // virtual binary clauses, where virtual means that
          // they only exist in the watch list of this ring.  They
          // are thus really copied (if shared among rings).

          assert (redundant_pointer (watch));

          // The 'assign' function expects the literals in the
          // opposite order as 'watch' and we have in essence to
          // swap upper and lower half of the watch pointer word.

          struct watch *reason = tag_binary (true, blocking, not_lit);

          assert (reason != watch);
          assign_with_reason (ring, blocking, reason);
          ticks++;
        } else {
          if (vblock->level <= v->level) continue;
          // elevate
          struct watch *reason = tag_binary (true, blocking, not_lit);
          elevate_with_reason (ring, blocking, reason);
          elevations++;
          ticks++;  // not sure exactly but probably need to increase ticks.
        }
      } else {
        // We now have to access the actual watcher data ...

        unsigned idx = index_pointer (watch);
        struct watcher *watcher = index_to_watcher (ring, idx);

        ticks++; // ... and pay the prize.

        // Satisfied (and vivified) but not removed clauses (actually
        // watchers to the clause) might still be watched and should
        // be ignored during propagation.

        if (watcher->garbage) // This induces the 'tick' above.
          continue;

        // Ignore the vivified clause during vivification.

        struct clause *clause = watcher->clause;
        if (ignore && clause == ignore)
          continue;

        // The watchers need to precisely know the two watched
        // literals, which might be different from the blocking
        // literal.  Otherwise unit propagation is not efficient
        // (other invariants might also break).

        // However as watchers are only accessed while traversing a
        // watch list we always know during such a traversal already
        // one of the two literals.  Therefore we can simply use the
        // XOR trick and only store the bit-wise difference (the
        // 'XOR') between the two watched literals in the watcher
        // instead of both literals and get the other watched literal
        // during traversal by adding (with 'XOR') to that difference.

        unsigned other = watcher->sum ^ not_lit;
        unsigned conflict_on_level = v->level;

        signed char other_value;
        struct variable *u;

        if (other == blocking) {
          other_value = blocking_value;
          u = vblock;
          if (conflict_on_level < vblock->level) conflict_on_level = vblock->level;
        } else {
          other_value = values[other];
          unsigned other_idx = IDX (other);
          u = variables + other_idx;
          if (conflict_on_level < u->level) conflict_on_level = u->level;
          if (other_value > 0 && u->level <= v->level) {
            bool redundant = redundant_pointer (watch);
            watch = tag_index (redundant, idx, other);
            q[-1] = watch;
            continue;
          }
        }

        // Now the irredundant and virtual redundant binary clauses
        // are handled and neither the blocking literal nor the other
        // watched literal (if different) are assigned to true, and
        // it is time to either find a non-false replacement watched
        // literal, or determine that the clause is unit or
        // conflicting (all replacement candidates are false).

        unsigned replacement = INVALID;
        signed char replacement_value = -1;
        
        unsigned second_replacement = other;
        signed char second_replacement_value = other_value;

        // The watchers can store literals of short clauses (currently
        // three or four literals long) directly in the watcher data
        // structure in order to avoid a second pointer dereference
        // (not needed for sequential solvers) to the actual clause
        // data (the latter being shared among threads).  While
        // initializing the watcher the size field is set to the
        // actual size of the clause if it is short enough and to zero
        // if it is too long (has more than four literals).
                
        
        unsigned watcher_size = watcher->size;
        if (watcher_size) {
          unsigned *literals = watcher->aux;
          unsigned *end_literals = literals + watcher_size;
          for (unsigned *r = literals; r != end_literals; r++) {
            replacement = *r;
            if (replacement != not_lit && replacement != other) {
              replacement_value = values[replacement];
              if (replacement_value >= 0) {
                if (second_replacement_value >= 0) break;
                second_replacement = replacement;
                second_replacement_value = replacement_value;
                replacement_value = -1;
                continue;
              }
              unsigned cl = (variables + IDX (replacement))->level;
              if (conflict_on_level < cl)
                conflict_on_level = cl;
            }
          }
        } else {
          // Now we pay the prize of accessing the actual clause too
          // (one of the following 'clause->size' accesses).

          // During propagation the 'tick' above for accessing
          // watchers and this one form the hot-spots of the solver,
          // due to irregular memory access (cache read misses).
          // All this special treatment of binary clauses, the
          // blocking literal and keeping short clause literals
          // directly in the watcher data-structure are all only
          // used to reduce the time spent in these two hot-spots.

          // The following code matches the same standard
          // propagation code in for instance CaDiCaL and Kissat.

          ticks++;
#ifdef METRICS
          assert (clause->size > 2);
          if (clause->size >= SIZE_VISITS)
            visits[0]++;
          else
            visits[clause->size]++;
#endif
          unsigned *literals = clause->literals;
          unsigned *end_literals = literals + clause->size;
          assert (watcher->aux[0] <= clause->size);
          unsigned *middle_literals = literals + watcher->aux[0];
          unsigned *r = middle_literals;
          while (r != end_literals) {
            replacement = *r;
            if (replacement != not_lit && replacement != other) {
              replacement_value = values[replacement];
              if (replacement_value >= 0) {
                if (second_replacement_value >= 0)
                  break;
                second_replacement = replacement;
                second_replacement_value = replacement_value;
                replacement_value = -1;
                continue;
              }
              unsigned cl = (variables + IDX (replacement))->level;
              if (conflict_on_level < cl)
                conflict_on_level = cl;
            }
            r++;
          }
          if (replacement_value < 0) {
            r = literals;
            while (r != middle_literals) {
              replacement = *r;
              if (replacement != not_lit && replacement != other) {
                replacement_value = values[replacement];
                if (replacement_value >= 0) {
                  if (second_replacement_value >= 0)
                    break;
                  second_replacement = replacement;
                  second_replacement_value = replacement_value;
                  replacement_value = -1;
                  continue;
                }
                unsigned cl = (variables + IDX (replacement))->level;
                if (conflict_on_level < cl)
                  conflict_on_level = cl;
              }
              r++;
            }
          }
          watcher->aux[0] = r - literals;
        }

        if (replacement_value >= 0) {
          // not a conflict, at least two literals unassigned or positive
          assert (second_replacement_value >= 0);
          assert (replacement != other);
          watcher->sum = other ^ replacement;
          LOGCLAUSE (clause, "unwatching %s in", LOGLIT (not_lit));
          watch_literal (ring, replacement, other, watcher);
          ticks++;
          q--;
        } else if (second_replacement_value > 0) {
          // only one literal positive, elevate
          replacement = maybe_elevate_with_reason (ring, second_replacement, watch);
          elevations++;
          assert (replacement != INVALID_LIT || !(ring->variables + IDX (second_replacement))->level);
          if (second_replacement != other) {
            assert (other_value < 0);
            watcher->sum = other ^ second_replacement;
            LOGCLAUSE (clause, "unwatching %s in", LOGLIT (not_lit));
            watch_literal (ring, second_replacement, other, watcher);
            ticks++;
            q--;
          } else if (v->level < u->level && replacement != not_lit && replacement != INVALID_LIT) {
            watcher->sum = other ^ replacement;
            LOGCLAUSE (clause, "unwatching %s in", LOGLIT (not_lit));
            watch_literal (ring, replacement, other, watcher);
            ticks++;
            q--;
          }
          ticks++;
        } else if (!second_replacement_value) {
          // only one literal unassigned, assign
          replacement = replace_assign_with_reason (ring, second_replacement, watch);
          assert (replacement != INVALID_LIT || !(ring->variables + IDX (other))->level);
          if (second_replacement != other) {
            assert (other_value < 0);
            watcher->sum = other ^ second_replacement;
            LOGCLAUSE (clause, "unwatching %s in", LOGLIT (not_lit));
            watch_literal (ring, second_replacement, other, watcher);
            ticks++;
            q--;
          } else if (v->level < u->level && replacement != not_lit && replacement != INVALID_LIT) {
            watcher->sum = other ^ replacement;
            LOGCLAUSE (clause, "unwatching %s in", LOGLIT (not_lit));
            watch_literal (ring, replacement, other, watcher);
            ticks++;
            q--;
          }
          ticks++;
        } else if (conflict_on_level > v->level) {
          // not true conflict, fix watches later (TODO: check if it necessary to change watches here...)
          assert (other_value < 0 && second_replacement_value < 0 && replacement_value < 0);
          if (!reapropagate_later) {
            reapropagate_later = true;
            PUSH (ring->reapropagate_later, lit);
          }
          if (!saved_conflict || conflict_on_level < saved_conflict_level) {
            saved_conflict_level = conflict_on_level;
            saved_conflict = watch;
          }
        } else {
          // true conflict
          assert (other_value < 0 && second_replacement_value < 0 && replacement_value < 0);
          conflict = watch;
          if (conflict && stop_at_conflict)
            break;
        } 
      }
    }
    while (p != end)
      *q++ = *p++;
    ticks += cache_lines (p, begin);
    watches->end = q;
    if (q == watches->begin)
      RELEASE (*watches);
#ifndef NDEBUG
    if (!conflict && !reapropagate_later)
      test_watch_invariant_for_lit (ring, not_lit, ignore);
#endif
  }

  struct ring_statistics *statistics = &ring->statistics;
  struct context *context = statistics->contexts + ring->context;

  if (!conflict && saved_conflict) {
    assert (saved_conflict_level <= ring->level);
    conflict = saved_conflict;
  }
  if (conflict) {
    LOGWATCH (conflict, "conflicting");
    context->conflicts++;
    ring->import_after_propagation_and_conflict = true;

    if (ring->context == SEARCH_CONTEXT && ring->randec) {
      if (!--ring->randec)
        very_verbose (ring, "last random decision conflict");
      else if (ring->randec == 1)
        very_verbose (ring, "one more random decision conflict to go");
      else
        very_verbose (ring, "%u more random decision conflicts to go",
                      ring->randec);
    }
  }

#ifndef NDEBUG
  if (!conflict)
    test_watch_invariant (ring, ignore);
#endif
  
  context->propagations += propagations;
  context->elevations += elevations;
  context->ticks += ticks;

  LOG ("clear reap after propagation");
  reap_clear (reap);
  return conflict;
}
