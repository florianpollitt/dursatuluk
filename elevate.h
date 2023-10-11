#ifndef _assign_h_INCLUDED
#define _assign_h_INCLUDED

struct ring;
struct watch;

void elevate_with_reason (struct ring *, unsigned lit,
                          struct watch *reason, unsigned assignment_level);
void elevate_ring_unit (struct ring *, unsigned unit);

#endif
