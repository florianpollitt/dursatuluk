#ifndef _reapalyze_h_INCLUDED
#define _reapalyze_h_INCLUDED

#include <stdbool.h>

struct ring;
struct watch;

bool reapalyze (struct ring *, struct watch *conflict);

#endif
