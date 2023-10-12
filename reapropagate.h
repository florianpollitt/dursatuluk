#ifndef _reapropagate_h_INCLUDED
#define _reapropagate_h_INCLUDED

#include <stdbool.h>

struct clause;
struct ring;

void init_reapropagate (struct ring *ring, unsigned *propagate);

struct watch *ring_reapropagate (struct ring *, bool stop_at_conflict,
                                 struct clause *ignored_large_clause);



#define REAP_PUSH(LIT_ARG, RING_ARG) \
  do { \
    struct ring *RING = (RING_ARG); \
    struct ring_trail *TRAIL = &RING->trail; \
    unsigned LIT = (LIT_ARG); \
    unsigned LIT_IDX = IDX (LIT); \
    struct variable *V = RING->variables + LIT_IDX; \
    unsigned LIT_LEVEL = V->level; \
    uint64_t RES = LIT_LEVEL; \
    const size_t POS = TRAIL->pos[LIT_IDX]; \
    assert (POS < UINT_MAX); \
    RES <<= 32; \
    RES |= POS; \
    LOG ("push %s on reap with level %d and pos %ld = key %" PRId64, LOGLIT (lit), LIT_LEVEL, POS, RES); \
    reap_push (&RING->reap, RES); \
  } while (0)

#endif
