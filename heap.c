#include "heap.h"

#ifdef USE_BINARY_HEAP

#if 0

void
check_heap (struct heap * heap)
{
  size_t size = SIZE (heap->stack);
  unsigned * stack = heap->stack.begin;
  struct node * nodes = heap->nodes;
  for (int idx_pos = 0; idx_pos != size; idx_pos++)
    {
      unsigned idx = stack[idx_pos];
      struct node * node = nodes + idx;
      assert (node->pos == idx_pos);
      int child_pos = 2 * idx_pos + 1;
      int parent_pos = (child_pos - 1) / 2;
      assert (parent_pos == idx_pos);
      if (child_pos >= size)
	continue;
      unsigned child_idx = stack[child_pos];
      struct node * child = nodes + child_idx;
      assert (child->pos == child_pos);
      assert (node->score >= child->score);
      if (++child_pos >= size)
	continue;
      parent_pos = (child_pos - 1)/2;
      assert (parent_pos == idx_pos);
      child_idx = stack[child_pos];
      child = nodes + child_idx;
      assert (child->pos == child_pos);
      assert (node->score >= child->score);
    }
}

#else

#define check_heap(...) do { } while (0)

#endif

static void
bubble_up (struct heap * heap, unsigned idx)
{
  unsigned * stack = heap->stack.begin;
  struct node * nodes = heap->nodes;
  struct node * node = nodes + idx;
  int idx_pos = node->pos;
  double idx_score = node->score;
  while (idx_pos)
    {
      int parent_pos = (idx_pos - 1) / 2;
      unsigned parent_idx = stack[parent_pos];
      struct node * parent = nodes + parent_idx;
      double parent_score = parent->score;
      if (parent_score >= idx_score)
	break;
      stack[idx_pos] = parent_idx;
      parent->pos = idx_pos;
      idx_pos = parent_pos;
    }
  stack[idx_pos] = idx;
  node->pos = idx_pos;
  check_heap (heap);
}

static void
bubble_down (struct heap * heap, unsigned idx)
{
  size_t size = SIZE (heap->stack);
  unsigned * stack = heap->stack.begin;
  struct node * nodes = heap->nodes;
  struct node * node = nodes + idx;
  int idx_pos = node->pos;
  double idx_score = node->score;
  for (;;)
    {
      int child_pos = 2 * idx_pos + 1;
      if (child_pos >= size)
	break;
      unsigned child_idx = stack[child_pos];
      struct node * child = nodes + child_idx;
      double child_score = child->score;
      int sibling_pos = child_pos + 1;
      if (sibling_pos < size)
	{
	  unsigned sibling_idx = stack[sibling_pos];
	  struct node * sibling = nodes + sibling_idx;
	  double sibling_score = sibling->score;
	  if (sibling_score > child_score)
	    {
	      child = sibling;
	      child_idx = sibling_idx;
	      child_pos = sibling_pos;
	      child_score = sibling_score;
	    }
	}
      if (child_score <= idx_score)
	break;
      stack[idx_pos] = child_idx;
      child->pos = idx_pos;
      idx_pos = child_pos;
    }
  stack[idx_pos] = idx;
  node->pos = idx_pos;
  check_heap (heap);
}


void
push_heap (struct heap * heap, struct node * node)
{
  unsigned size = SIZE (heap->stack);
  assert (node->pos == INVALID_POSITION);
  node->pos = size;
  unsigned idx = node - heap->nodes;
  PUSH (heap->stack, idx);
  bubble_up (heap, idx);
}

void
pop_heap (struct heap * heap)
{
  check_heap (heap);
  assert (!EMPTY (heap->stack));
  struct node * nodes = heap->nodes;
  unsigned * stack = heap->stack.begin;
  unsigned idx = stack[0];
  struct node * node = nodes + idx;
  assert (!node->pos);
  node->pos = INVALID_POSITION;
  unsigned last_idx = POP (heap->stack);
  struct node * last = nodes + last_idx;
  if (!last->pos)
    return;
  last->pos = 0;
  stack[0] = last_idx;
  bubble_down (heap, last_idx);
}

void
update_heap (struct heap * heap, struct node * node, double new_score)
{
  assert (node->score < new_score);
  node->score = new_score;
  if (node->pos == INVALID_POSITION)
    return;
  unsigned idx = node - heap->nodes;
  bubble_up (heap, idx);
}

#else

static struct node *
merge_nodes (struct node *a, struct node *b)
{
  if (!a)
    return b;
  if (!b)
    return a;
  assert (a != b);
  struct node *parent, *child;
  if (b->score > a->score)
    parent = b, child = a;
  else
    parent = a, child = b;
  struct node *parent_child = parent->child;
  child->next = parent_child;
  if (parent_child)
    parent_child->prev = child;
  child->prev = parent;
  parent->child = child;
  parent->prev = parent->next = 0;

  return parent;
}

static struct node *
collapse_node (struct node *node)
{
  if (!node)
    return 0;

  struct node *next = node, *tail = 0;

  do
    {
      struct node *a = next;
      assert (a);
      struct node *b = a->next;
      if (b)
	{
	  next = b->next;
	  struct node *tmp = merge_nodes (a, b);
	  assert (tmp);
	  tmp->prev = tail;
	  tail = tmp;
	}
      else
	{
	  a->prev = tail;
	  tail = a;
	  break;
	}
    }
  while (next);

  struct node *res = 0;
  while (tail)
    {
      struct node *prev = tail->prev;
      res = merge_nodes (res, tail);
      tail = prev;
    }

  return res;
}

static void
deheap_node (struct node *node)
{
  assert (node);
  struct node *prev = node->prev;
  struct node *next = node->next;
  assert (prev);
  node->prev = 0;
  if (prev->child == node)
    prev->child = next;
  else
    prev->next = next;
  if (next)
    next->prev = prev;
}

void
pop_heap (struct heap *heap)
{
  struct node *root = heap->root;
  struct node *child = root->child;
  heap->root = collapse_node (child);
  assert (!heap_contains (heap, node));
}

void
push_heap (struct heap *heap, struct node *node)
{
  assert (!heap_contains (heap, node));
  node->child = 0;
  heap->root = merge_nodes (heap->root, node);
  assert (heap_contains (heap, node));
}

void
update_heap (struct heap *heap, struct node *node, double new_score)
{
  double old_score = node->score;
  assert (old_score <= new_score);
  if (old_score == new_score)
    return;
  node->score = new_score;
  struct node *root = heap->root;
  if (root == node)
    return;
  if (!node->prev)
    return;
  deheap_node (node);
  heap->root = merge_nodes (root, node);
}

#endif
