#include "assign.h"
#include "decide.h"
#include "macros.h"
#include "options.h"
#include "random.h"
#include "ring.h"
#include "utilities.h"

signed char
initial_phase (struct ring *ring)
{
  return ring->options.phase ? 1 : -1;
}

signed char
decide_phase (struct ring *ring, unsigned idx)
{
  struct phases *p = ring->phases + idx;
  signed char res = 0;
  if (ring->options.force_phase)
    res = initial_phase (ring);
  if (!res && ring->stable)
    res = p->target;
  if (!res)
    res = p->saved;
  if (!res)
    res = initial_phase (ring);
  return res;
}

static unsigned
random_decision (struct ring *ring)
{
  assert (ring->unassigned);

  signed char *values = ring->values;
  bool *inactive = ring->inactive;
  unsigned size = ring->size;

  unsigned idx = random_modulo (&ring->random, size);
  unsigned lit = LIT (idx);

  if (inactive[idx] || values[lit])
    {
      unsigned delta = random_modulo (&ring->random, size);
      while (gcd (delta, size) != 1)
	if (++delta == size)
	  delta = 1;
      assert (delta < size);
      do
	{
	  idx += delta;
	  if (idx >= size)
	    idx -= size;
	  lit = LIT (idx);
	}
      while (inactive[idx] || values[lit]);
    }

  LOG ("random decision %s", LOGVAR (idx));

  if (ring->context == SEARCH_CONTEXT)
    ring->statistics.decisions.random++;


  return idx;
}

static unsigned
best_decision_on_heap (struct ring *ring)
{
  assert (ring->unassigned);

  signed char *values = ring->values;
  struct heap *heap = &ring->heap;
  struct node *nodes = heap->nodes;

  unsigned idx;
  for (;;)
    {
      struct node *root;
      root = heap->root;
      assert (root);
      assert (root - nodes < ring->size);
      idx = root - nodes;
      unsigned lit = LIT (idx);
      if (!values[lit])
	break;
      pop_heap (heap);
    }

  LOG ("best decision %s on heap with score %g",
       LOGVAR (idx), nodes[idx].score);

  if (ring->context == SEARCH_CONTEXT)
    ring->statistics.decisions.heap++;

  return idx;
}

static unsigned
best_decision_on_queue (struct ring *ring)
{
  assert (ring->unassigned);

  signed char *values = ring->values;
  struct queue *queue = &ring->queue;
  struct link *links = queue->links;
  struct link *search = queue->search;

  unsigned lit, idx;
  for (;;)
    {
      assert (search);
      idx = search - links;
      lit = LIT (idx);
      if (!values[lit])
	break;
      search = search->prev;
    }
  queue->search = search;

  LOG ("best decision %s on queue with stamp %" PRIu64,
       LOGVAR (idx), search->stamp);

  if (ring->context == SEARCH_CONTEXT)
    ring->statistics.decisions.queue++;

  return idx;
}

void
decide (struct ring *ring)
{
  struct context *context = ring->statistics.contexts;
  context += ring->context;
  uint64_t decisions = context->decisions++;

  unsigned idx;
  if (ring->id && decisions < ring->options.random_decisions)
    idx = random_decision (ring);
  else if (ring->stable)
    idx = best_decision_on_heap (ring);
  else
    idx = best_decision_on_queue (ring);

  signed char phase = decide_phase (ring, idx);
  unsigned lit = LIT (idx);

  if (phase < 0)
    lit = NOT (lit);

  if (ring->context == SEARCH_CONTEXT)
    {
      if (phase < 0)
	ring->statistics.decisions.negative++;
      else
	ring->statistics.decisions.positive++;
    }

  ring->level++;
  assign_decision (ring, lit);
}
