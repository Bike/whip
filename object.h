#pragma once

#include <stdio.h> // FILE
#include <stdbool.h>
#include "header.h"

/* DATA TYPES */


/* obj_t -- scheme object type
 *
 * obj_t is a pointer to a union, obj_u, which has members for
 * each scheme representation.
 *
 * The obj_u also has a "type" member.  Each representation
 * structure also has a "type" field first.  ANSI C guarantees
 * that these type fields correspond [section?].
 *
 * Objects are allocated by allocating one of the representation
 * structures and casting the pointer to it to type obj_t.  This
 * allows objects of different sizes to be represented by the
 * same type.
 *
 * To access an object, check its type by reading TYPE(obj), then
 * access the fields of the representation, e.g.
 *   if(TYPE(obj) == TYPE_PAIR) fiddle_with(CAR(obj));
 */

typedef union obj_u *obj_t;

typedef obj_t (*entry_t)(obj_t env, obj_t op_env, obj_t operator, obj_t rands);

typedef int type_t;
enum {
  TYPE_PAIR,
  TYPE_INTEGER,
  TYPE_SYMBOL,
  TYPE_SPECIAL,
  TYPE_OPERATOR,
  TYPE_STRING,
  TYPE_PORT,
  TYPE_PROMISE,
  TYPE_CHARACTER,
  TYPE_VECTOR,
  TYPE_TABLE,
  TYPE_BUCKETS
};

// Not a real type - used to get the header from the union
typedef struct type_s {
  struct gc_header header;
} type_s;

typedef struct pair_s {
  struct gc_header header;
  obj_t car, cdr;               /* first and second projections */
} pair_s;

typedef struct promise_s {
  struct gc_header header;
  bool fulfilledp;
  obj_t fulfiller;
} promise_s;

typedef struct symbol_s {
  struct gc_header header;                  /* TYPE_SYMBOL */
  size_t length;                /* length of symbol string (excl. NUL) */
  char string[];                /* symbol string, NUL terminated */
} symbol_s;

typedef struct integer_s {
  struct gc_header header;                  /* TYPE_INTEGER */
  long integer;                 /* the integer */
} integer_s;

typedef struct special_s {
  struct gc_header header;                  /* TYPE_SPECIAL */
  char *name;                   /* printed representation, NUL terminated */
} special_s;

typedef struct operator_s {
  struct gc_header header;                  /* TYPE_OPERATOR */
  char *name;                   /* printed name, NUL terminated */
  entry_t entry;                /* entry point -- see eval() */
  obj_t arguments, body;        /* function arguments and code */
  obj_t env, op_env;            /* closure environments */
} operator_s;

typedef struct string_s {
  struct gc_header header;                  /* TYPE_STRING */
  size_t length;                /* number of chars in string */
  char string[];                /* string, NUL terminated */
} string_s;

typedef struct port_s {
  struct gc_header header;                  /* TYPE_PORT */
  obj_t name;                   /* name of stream */
  FILE *stream;
} port_s;

typedef struct character_s {
  struct gc_header header;                  /* TYPE_CHARACTER */
  char c;                       /* the character */
} character_s;

typedef struct vector_s {
  struct gc_header header;                  /* TYPE_VECTOR */
  size_t length;                /* number of elements */
  obj_t vector[];               /* vector elements */
} vector_s;

typedef unsigned long (*hash_t)(obj_t obj);
typedef int (*cmp_t)(obj_t obj1, obj_t obj2);

typedef struct table_s {
  struct gc_header header;                  /* TYPE_TABLE */
  hash_t hash;                  /* hash function */
  cmp_t cmp;                    /* comparison function */
  obj_t buckets;                /* hash buckets */
} table_s;

typedef struct buckets_s {
  struct gc_header header;                  /* TYPE_BUCKETS */
  size_t length;                /* number of buckets */
  size_t used;                  /* number of buckets in use */
  size_t deleted;               /* number of deleted buckets */
  struct bucket_s {
    obj_t key, value;
  } bucket[];                   /* hash buckets */
} buckets_s;

/* structure macros */

#define TYPE(obj) (header_live_alloc_kind((obj)->type.header.header))

#define FOR_EACH_HEAP_OBJECT_KIND(OP)           \
  OP(pair, Pair, PAIR)                          \
       OP(promise, Promise, PROMISE)            \
       OP(symbol, Symbol, SYMBOL)               \
       OP(integer, Integer, INTEGER)            \
       OP(special, Special, SPECIAL)            \
       OP(operator, Operator, OPERATOR)         \
       OP(string, String, STRING)               \
       OP(port, Port, PORT)                     \
       OP(character, Character, CHARACTER)      \
  OP(vector, Vector, VECTOR)                    \
  OP(table, Table, TABLE)                       \
  OP(buckets, Buckets, BUCKETS)

typedef union obj_u {
  type_s type;                  /* one of TYPE_* */
#define UNION_FIELD(name, Name, NAME) name##_s name;
  FOR_EACH_HEAP_OBJECT_KIND(UNION_FIELD)
#undef UNION_FIELD
} obj_s;

/* Accessing typed objects
 * Abstracted through functions for when I need to change stuff later.
 * cTYPE(obj_t) gets you a TYPE_s. c is for cast.
 * Does not type check.
 */

#define DEFCASTER(name, Name, NAME) \
  static inline name##_s* c##name(obj_t o) { return &o->name; }
FOR_EACH_HEAP_OBJECT_KIND(DEFCASTER)
#undef DEFCASTER

/* Sizing objects
 * These are used by the GC in gc-embed.h, but also by us.
 */

#define DEFINE_SIZEOF(name)                             \
  static inline size_t name##_osize(name##_s *name) {   \
    return sizeof(name##_s);                            \
  }

DEFINE_SIZEOF(pair);
DEFINE_SIZEOF(promise);

static inline size_t symbol_osize(symbol_s *s) {
  return sizeof(symbol_s) + s->length+1;
}

DEFINE_SIZEOF(integer);
DEFINE_SIZEOF(special);
DEFINE_SIZEOF(operator);

static inline size_t string_osize(string_s *s) {
  return sizeof(string_s) + s->length+1;
}

DEFINE_SIZEOF(port);
DEFINE_SIZEOF(character);

static inline size_t vector_osize(vector_s *v) {
  return sizeof(vector_s) + v->length * sizeof(obj_t);
}

DEFINE_SIZEOF(table);

static inline size_t buckets_osize(buckets_s *b) {
  return sizeof(buckets_s) + b->length * 2 * sizeof(obj_t);
}

#undef DEFINE_SIZEOF
