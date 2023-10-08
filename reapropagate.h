#ifndef _reapropagate_h_INCLUDED
#define _reapropagate_h_INCLUDED

#include <stdbool.h>

struct clause;
struct ring;

void init_reapropagate (struct ring *ring, unsigned *propagate);

struct watch *ring_reapropagate (struct ring *, bool stop_at_conflict,
                                 struct clause *ignored_large_clause);

#endif
