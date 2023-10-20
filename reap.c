#include "reap.h"
#include <assert.h>
#include <limits.h>
#include <string.h>
#include <stdint.h>

#ifndef NDEBUG
#include "logging.h"
#include "ring.h"

void reap_elements (struct reap *reap, struct ring *ring) {
  for (unsigned i = 0; i < 65; i++) {
    for (uint64_t *e = reap->buckets[i].begin; e != reap->buckets[i].end; e++) {
      unsigned pos = (unsigned) *e;  // is this cast always correct?
      unsigned level = *e >> 32;
      LOG ("key %" PRId64 " level %d trail %d", *e, level, pos);
    }
  }
}
#endif

void reap_init (struct reap *reap) {
  reap->num_elements = 0;
  reap->last_deleted = 0;
  reap->min_bucket = 64;
  reap->max_bucket = 0;
  
  for (unsigned i = 0; i < 65; i++)
    INIT (reap->buckets[i]); // unnecessary?
}

void reap_release (struct reap *reap) {
  // delete buckets necessary? memleak?
  for (unsigned i = 0; i < 65; i++)
    RELEASE (reap->buckets[i]);
  reap->num_elements = 0;
  reap->last_deleted = 0;
  reap->min_bucket = 64;
  reap->max_bucket = 0;
}

void reap_clear (struct reap *reap) {
  assert (reap->max_bucket <= 64);
  for (unsigned i = 0; i < 65; i++)
    CLEAR (reap->buckets[i]);
  reap->num_elements = 0;
  reap->last_deleted = 0;
  reap->min_bucket = 64;
  reap->max_bucket = 0;
}

static inline unsigned leading_zeroes_of_uint64_t (uint64_t x) {
  const unsigned front = (unsigned) (x >> 32);
  if (front) return __builtin_clz (front);
  const unsigned back = (unsigned) x;
  if (back) return __builtin_clz (back) + sizeof (unsigned) * 8;
  return sizeof (uint64_t) * 8;
}

void reap_push (struct reap *reap, uint64_t e) {
  assert (reap->last_deleted <= e);
  const uint64_t diff = e ^ reap->last_deleted;
  const unsigned bucket = 64 - leading_zeroes_of_uint64_t (diff);
  PUSH (reap->buckets[bucket], e);
  if (reap->min_bucket > bucket)
    reap->min_bucket = bucket;
  if (reap->max_bucket < bucket)
    reap->max_bucket = bucket;
  assert (reap->num_elements != UINT_MAX);
  reap->num_elements++;
}

uint64_t reap_pop (struct reap *reap) {
  assert (reap->num_elements > 0);
  unsigned i = reap->min_bucket;
  for (;;) {
    assert (i < 65);
    assert (i <= reap->max_bucket);
    struct uint64_ts *s = &reap->buckets[i];
    if (EMPTY (*s)) {
      reap->min_bucket = ++i;
      continue;
    }
    uint64_t res;
    if (i) {   // (A)
      res = UINT64_MAX; // needs stdint header
      uint64_t *begin = s->begin;
      const uint64_t *end = s->end;
      uint64_t *q = s->begin;
      assert (begin < end);
      for (uint64_t *p = begin; p != end; ++p) {
        const uint64_t tmp = *p;
        if (tmp >= res)
          continue;
        res = tmp;
        q = p;
      }
      assert (reap->last_deleted <= res);

      for (uint64_t *p = begin; p != end; ++p) {
        if (p == q)
          continue;
        const uint64_t other = *p;
        const uint64_t diff = other ^ res;
        assert (sizeof (uint64_t) == 8);
        const unsigned j = 64 - leading_zeroes_of_uint64_t (diff);
        assert (j < i);
        PUSH (reap->buckets[j], other);
        if (reap->min_bucket > j)
          reap->min_bucket = j;
      }

      CLEAR (*s);

      if (i && reap->max_bucket == i) {
#ifndef NDEBUG
        for (unsigned j = i + 1; j < 65; j++)
          assert (EMPTY (reap->buckets[j]));
#endif
        assert (EMPTY (*s)); // always true?
        if (EMPTY (*s))
          reap->max_bucket = i - 1;
      }
    } else {    // (B)
      // can only happen if same element is pushed multiple times or 0 is pushed
      assert (!EMPTY (reap->buckets[0]));
      assert (PEEK (reap->buckets[0], 0) == reap->last_deleted);
      res = POP (reap->buckets[0]);
    }

    if (reap->min_bucket == i) {
#ifndef NDEBUG
      for (unsigned j = 0; j < i; j++)
        assert (EMPTY (reap->buckets[j]));
#endif
      // always empty except (B) triggers
      assert (EMPTY (*s) || res == reap->last_deleted);
      if (EMPTY (*s))
        reap->min_bucket = (int) i + 1 < 64 ? (int) i + 1 : 64;
    }

    --reap->num_elements;
    assert (reap->last_deleted <= res);
    reap->last_deleted = res;

    return res;
  }
}

