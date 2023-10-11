#ifndef _elevate_h_INCLUDED
#define _elevate_h_INCLUDED

struct ring;
struct watch;


void elevate_with_reason_and_level (struct ring *ring, unsigned lit, unsigned level,
                         struct watch *reason);

void elevate_with_reason (struct ring *ring, unsigned lit,
                         struct watch *reason);

void maybe_elevate_with_reason (struct ring *ring, unsigned lit,
                         struct watch *reason);

void elevate_ring_unit (struct ring *ring, unsigned unit);

#endif
