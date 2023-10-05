#ifndef _reap_h_INCLUDED
#define _reap_h_INCLUDED

#include "stack.h"
#include <stdbool.h>


struct reap {
  size_t num_elements;
  unsigned last_deleted;
  unsigned min_bucket;
  unsigned max_bucket;
  
  struct unsigneds buckets[33];
};

void reap_init (struct reap *);
void reap_release (struct reap *);
void reap_push (struct reap *, unsigned);
void reap_clear (struct reap *);
unsigned reap_pop (struct reap *);


static inline bool reap_empty (struct reap *reap) { return !reap->num_elements; }
static inline size_t reap_size (struct reap *reap) { return reap->num_elements; }

#endif
