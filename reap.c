#include "reap.h"
#include <assert.h>
#include <limits.h>
#include <string.h>

void reap_init (struct reap *reap) {
  reap->num_elements = 0;
  reap->last_deleted = 0;
  reap->min_bucket = 32;
  reap->max_bucket = 0;
  for (unsigned i = 0; i < 33; i++)
    INIT (reap->buckets[i]); // unnecessary?
}

void reap_release (struct reap *reap) {
  // delete buckets necessary? memleak?
  for (unsigned i = 0; i < 33; i++)
    RELEASE (reap->buckets[i]);
  reap->num_elements = 0;
  reap->last_deleted = 0;
  reap->min_bucket = 32;
  reap->max_bucket = 0;
}

void reap_clear (struct reap *reap) {
  assert (reap->max_bucket <= 32);
  for (unsigned i = 0; i < 33; i++)
    CLEAR (reap->buckets[i]);
  reap->num_elements = 0;
  reap->last_deleted = 0;
  reap->min_bucket = 32;
  reap->max_bucket = 0;
}

static inline unsigned leading_zeroes_of_unsigned (unsigned x) {
  return x ? __builtin_clz (x) : sizeof (unsigned) * 8;
}

void reap_push (struct reap *reap, unsigned e) {
  assert (reap->last_deleted <= e);
  const unsigned diff = e ^ reap->last_deleted;
  const unsigned bucket = 32 - leading_zeroes_of_unsigned (diff);
  PUSH (reap->buckets[bucket], e);
  if (reap->min_bucket > bucket)
    reap->min_bucket = bucket;
  if (reap->max_bucket < bucket)
    reap->max_bucket = bucket;
  assert (reap->num_elements != UINT_MAX);
  reap->num_elements++;
}

unsigned reap_pop (struct reap *reap) {
  assert (reap->num_elements > 0);
  unsigned i = reap->min_bucket;
  for (;;) {
    assert (i < 33);
    assert (i <= reap->max_bucket);
    struct unsigneds s = reap->buckets[i];
    if (EMPTY (s)) {
      reap->min_bucket = ++i;
      continue;
    }
    unsigned res;
    if (i) {
      res = UINT_MAX;
      const unsigned *begin = s.begin;
      const unsigned *end = s.end;
      unsigned *q = s.begin;
      assert (begin < end);
      for (unsigned *p = begin; p != end; ++p) {
        const unsigned tmp = *p;
        if (tmp >= res)
          continue;
        res = tmp;
        q = p;
      }

      for (unsigned *p = begin; p != end; ++p) {
        if (p == q)
          continue;
        const unsigned other = *p;
        const unsigned diff = other ^ res;
        assert (sizeof (unsigned) == 4);
        const unsigned j = 32 - leading_zeroes_of_unsigned (diff);
        assert (j < i);
        PUSH (reap->buckets[j], other);
        if (reap->min_bucket > j)
          reap->min_bucket = j;
      }

      CLEAR (s);

      if (i && reap->max_bucket == i) {
#ifndef NDEBUG
        for (unsigned j = i + 1; j < 33; j++)
          assert (EMPTY (reap->buckets[j]));
#endif
        if (EMPTY (s)) // always true?
          reap->max_bucket = i - 1;
      }
    } else {
      res = reap->last_deleted;
      assert (!EMPTY (reap->buckets[0]));
      assert (PEEK (reap->buckets[0], 0) == res);
      POP (reap->buckets[0]);
    }

    if (reap->min_bucket == i) {
#ifndef NDEBUG
      for (unsigned j = 0; j < i; j++)
        assert (EMPTY (reap->buckets[j]));
#endif
      if (EMPTY (s)) // always true?
        reap->min_bucket = (int) i + 1 < 32 ? (int) i + 1 : 32;
    }

    --reap->num_elements;
    assert (reap->last_deleted <= res);
    reap->last_deleted = res;

    return res;
  }
}

