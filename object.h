#pragma once

#include <stdio.h> // FILE
#include <stdbool.h>
#include <stdatomic.h>
#include <pthread.h>
#include "header.h"
#include "gc-ephemeron.h"

/* DATA TYPES */


/* obj_t -- scheme object type
 *
 * obj_t is a void*. This is proximally because whippet
 * ephemerons are in a different translation unit, but also this
 * matches the complexity of a real Lisp system with a bunch of
 * different types - they're not all going into a union.
 *
 * Each representation structure also has a "header" field first.
 * ANSI C guarantees that these header fields correspond [section?].
 *
 * Objects are allocated by allocating one of the representation
 * structures and casting the pointer to it to type obj_t.  This
 * allows objects of different sizes to be represented by the
 * same type.
 *
 * To access an object, check its type by reading type(obj), then
 * access the fields of the representation, e.g.
 *   if(type(obj) == TYPE_PAIR) fiddle_with(CAR(obj));
 */

typedef void *obj_t;

typedef obj_t (*entry_t)(obj_t env, obj_t op_env, obj_t operator, obj_t rands);

enum type_t {
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
  TYPE_BUCKETS,
  TYPE_THREAD,
  TYPE_WEAK_BOX,
  TYPE_EPHEMERON
};

// Not a real type - used to get the header from the union
typedef struct type_s {
  struct gc_header header;
} type_s;

typedef struct pair_s {
  struct gc_header header;
  _Atomic(obj_t) car, cdr;        /* first and second projections */
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
  intptr_t integer;                 /* the integer */
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

typedef size_t (*hash_t)(obj_t obj);
typedef bool (*cmp_t)(obj_t obj1, obj_t obj2);

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

typedef struct thread_s {
  struct gc_header header;
  obj_t thunk;
  pthread_t native;
} thread_s;

typedef struct gc_ephemeron weak_box_s;
typedef struct gc_ephemeron ephemeron_s;

/* structure macros */

static inline enum type_t type(obj_t obj) {
  return header_live_alloc_kind(((type_s*)(obj))->header.header);
}

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
  OP(buckets, Buckets, BUCKETS)                 \
  OP(thread, Thread, THREAD)                    \
  OP(weak_box, WeakBox, WEAK_BOX)               \
  OP(ephemeron, Ephemeron, EPHEMERON)

/* Accessing typed objects
 * Abstracted through functions for when I need to change stuff later.
 * cTYPE(obj_t) gets you a TYPE_s. c is for cast.
 * Does not type check.
 */

#define DEFCASTER(name, Name, NAME) \
  static inline name##_s* c##name(obj_t o) { return (name##_s*)o; }
FOR_EACH_HEAP_OBJECT_KIND(DEFCASTER)
#undef DEFCASTER

// Special case for fixnums.
static inline intptr_t fixnum(obj_t o) { return cinteger(o)->integer; }

/* Sizing objects
 * These are used by the GC in embed.h, but also by us.
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

DEFINE_SIZEOF(thread);

static inline size_t weak_box_osize(weak_box_s *b) {
  return gc_ephemeron_size();
}

static inline size_t ephemeron_osize(ephemeron_s *b) {
  return gc_ephemeron_size();
}

#undef DEFINE_SIZEOF
