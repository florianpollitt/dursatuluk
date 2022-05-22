#ifndef _clause_h_INCLUDED
#define _clause_h_INCLUDED

#include <stdatomic.h>
#include <stdbool.h>
#include <stdlib.h>

#ifdef LOGGING
#include <stdint.h>
#endif

struct ring;

struct clause
{
#ifdef LOGGING
  uint64_t id;
#endif
  atomic_ushort shared;
  volatile unsigned char glue;
  bool dirty:1;
  bool garbage:1;
  bool redundant:1;
  bool subsume:1;
  unsigned size;
  unsigned literals[];
};

struct clauses
{
  struct clause **begin, **end, **allocated;
};

/*------------------------------------------------------------------------*/

#define all_clauses(ELEM,CLAUSES) \
  all_pointers_on_stack (struct clause, ELEM, CLAUSES)

#define all_literals_in_clause(LIT,CLAUSE) \
  unsigned * P_ ## LIT = (CLAUSE)->literals, \
           * END_ ## LIT = P_ ## LIT + (CLAUSE)->size, LIT;\
  P_ ## LIT != END_ ## LIT && (LIT = *P_ ## LIT, true); \
  ++ P_ ## LIT

/*------------------------------------------------------------------------*/

struct clause *new_large_clause (size_t, unsigned *,
				 bool redundant, unsigned glue);

void mark_clause (signed char *marks, struct clause *, unsigned except);
void unmark_clause (signed char *marks, struct clause *, unsigned except);

void reference_clause (struct ring *, struct clause *, unsigned inc);
void dereference_clause (struct ring *, struct clause *);

#endif
