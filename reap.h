#ifndef _reap_h_INCLUDED
#define _reap_h_INCLUDED

#include "stack.h"
#include <stdbool.h>
#include <stdint.h>


struct reap {
  size_t num_elements;
  uint64_t last_deleted;
  unsigned min_bucket;
  unsigned max_bucket;
  
  struct uint64_ts buckets[65];
};

void reap_init (struct reap *);
void reap_release (struct reap *);
void reap_push (struct reap *, uint64_t);
void reap_clear (struct reap *);
uint64_t reap_pop (struct reap *);

static inline bool reap_empty (struct reap *reap) { return !reap->num_elements; }
static inline size_t reap_size (struct reap *reap) { return reap->num_elements; }

#endif
