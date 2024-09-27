/* scheme.c -- SCHEME INTERPRETER EXAMPLE FOR THE MEMORY POOL SYSTEM
 *
 * Copyright (c) 2001-2020 Ravenbrook Limited.  See end of file for license.
 *
 * TO DO
 * - unbounded integers, other number types.
 * - named let.
 * - quasiquote: vectors; nested; dotted.
 * - Lots of library.
 * - \#foo unsatisfactory in read and print
 */

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <stdbool.h> // bool
#include <threads.h> // thread_local

#include "object.h"
#include "roots.h"
#include "allocate.h"
#include "gc-api.h"
#include "gc-basic-stats.h"

/* LANGUAGE EXTENSION */

#define unless(c)       if(!(c))
#define LENGTH(array)   (sizeof(array) / sizeof(array[0]))


/* CONFIGURATION PARAMETERS */

#define SYMMAX          ((size_t)255)   /* max length of a symbol */
#define MSGMAX          ((size_t)255)   /* max length of error message */
#define STRMAX          ((size_t)255)   /* max length of a string */

/* GLOBAL DATA */

static struct gc_heap_roots global_roots = {.roots = NULL};
struct handle *add_heap_root(void**, size_t);
bool remove_heap_root(struct handle*);

/* symtab -- symbol table
 *
 * The symbol table is a hash-table containing objects of TYPE_SYMBOL.
 * When a string is "interned" it is looked up in the table, and added
 * only if it is not there.  This guarantees that all symbols which
 * are equal are actually the same object.
 */

static obj_t *symtab;
static size_t symtab_size;
// GC root representing the above
struct handle *symtab_root;

/* special objects
 *
 * These global variables are initialized to point to objects of
 * TYPE_SPECIAL by main.  They are used as markers for various
 * special purposes.
 */

static obj_t obj_empty;         /* (), the empty list */
static obj_t obj_eof;           /* end of file */
static obj_t obj_error;         /* error indicator */
static obj_t obj_true;          /* #t, boolean true */
static obj_t obj_false;         /* #f, boolean false */
static obj_t obj_undefined;     /* undefined result indicator */
static obj_t obj_tail;          /* tail recursion indicator */
static obj_t obj_deleted;       /* deleted key in hashtable */


/* predefined symbols
 *
 * These global variables are initialized to point to interned
 * objects of TYPE_SYMBOL.  They have special meaning in the
 * Scheme language, and are used by the evaluator to parse code.
 */

static obj_t obj_quote;         /* "quote" symbol */
static obj_t obj_quasiquote;    /* "quasiquote" symbol */
static obj_t obj_lambda;        /* "lambda" symbol */
static obj_t obj_begin;         /* "begin" symbol */
static obj_t obj_else;          /* "else" symbol */
static obj_t obj_unquote;       /* "unquote" symbol */
static obj_t obj_unquote_splic; /* "unquote-splicing" symbol */


/* error handler
 *
 * The error_handler variable is initialized to point at a
 * jmp_buf to which the "error" function longjmps if there is
 * any kind of error during evaluation.  It can be set up by
 * any enclosing function that wants to catch errors.  There
 * is a default error handler in main, in the read-eval-print
 * loop.  The error function also writes an error message
 * into "error_message" before longjmping, and this can be
 * displayed to the user when catching the error.
 *
 * [An error code should also be passed so that the error can
 *  be decoded by enclosing code.]
 */

static jmp_buf *error_handler = NULL;
static char error_message[MSGMAX+1];

/* THREAD-LOCAL DATA */

// The Whippet mutator for a thread.
thread_local struct gc_mutator *mutator;
// Stats collector.
thread_local struct gc_basic_stats gcstats;

/* SUPPORT FUNCTIONS */


/* error -- throw an error condition
 *
 * The "error" function takes a printf-style format string
 * and arguments, writes the message into error_message and
 * longjmps to *error_handler.  There must be a setjmp at
 * the other end to catch the condition and display the
 * message.
 */

static void error(char *format, ...)
{
  va_list args;

  va_start(args, format);
  vsnprintf(error_message, sizeof error_message, format, args);
  va_end(args);

  if (error_handler) {
    longjmp(*error_handler, 1);
  } else {
    fflush(stdout);
    fprintf(stderr, "Fatal error during initialization: %s\n",
            error_message);
    abort();
  }
}

/* make_* -- object constructors
 *
 * Each object type has a function here which allocates an
 * instance of that type.
 */

static obj_t make_bool(int condition)
{
  return condition ? obj_true : obj_false;
}

static obj_t make_pair(obj_t car, obj_t cdr)
{
  obj_t obj = gc_allocate_with_type(mutator, TYPE_PAIR, sizeof(pair_s));
  cpair(obj)->car = car;
  cpair(obj)->cdr = cdr;
  return obj;
}

static obj_t make_promise(obj_t fulfiller)
{
  obj_t obj = gc_allocate_with_type(mutator, TYPE_PROMISE, sizeof(promise_s));
  cpromise(obj)->fulfilledp = false;
  cpromise(obj)->fulfiller = fulfiller;
  return obj;
}

static obj_t make_integer(long integer)
{
  obj_t obj = gc_allocate_with_type(mutator, TYPE_INTEGER, sizeof(integer_s));
  cinteger(obj)->integer = integer;
  return obj;
}

static obj_t make_symbol(size_t length, char string[])
{
  size_t size = offsetof(symbol_s, string) + length+1; // null terminator
  obj_t obj = gc_allocate_with_type(mutator, TYPE_SYMBOL, size);
  csymbol(obj)->length = length;
  memcpy(csymbol(obj)->string, string, length+1);
  return obj;
}

static obj_t make_string(size_t length, char string[])
{
  size_t size = offsetof(string_s, string) + length+1;
  obj_t obj = gc_allocate_with_type(mutator, TYPE_STRING, size);
  cstring(obj)->length = length;
  if (string) memcpy(cstring(obj)->string, string, length+1);
  else memset(cstring(obj)->string, 0, length+1);
  return obj;
}

static obj_t make_special(char *string)
{
  obj_t obj = gc_allocate_with_type(mutator, TYPE_SPECIAL, sizeof(special_s));
  cspecial(obj)->name = string;
  return obj;
}

static obj_t make_operator(char *name,
                           entry_t entry, obj_t arguments,
                           obj_t body, obj_t env, obj_t op_env)
{
  obj_t obj = gc_allocate_with_type(mutator, TYPE_OPERATOR, sizeof(operator_s));
  coperator(obj)->name = name;
  coperator(obj)->entry = entry;
  coperator(obj)->arguments = arguments;
  coperator(obj)->body = body;
  coperator(obj)->env = env;
  coperator(obj)->op_env = op_env;
  return obj;
}

static obj_t make_port(obj_t name, FILE *stream)
{
  obj_t obj = gc_allocate_with_type(mutator, TYPE_PORT, sizeof(port_s));
  cport(obj)->name = name;
  cport(obj)->stream = stream;
  return obj;
}

static obj_t make_character(char c)
{
  obj_t obj = gc_allocate_with_type(mutator, TYPE_CHARACTER, sizeof(character_s));
  ccharacter(obj)->c = c;
  return obj;
}

static obj_t make_vector(size_t length, obj_t fill)
{
  size_t size = offsetof(vector_s, vector) + length * sizeof(obj_t);
  size_t i;
  obj_t obj = gc_allocate_with_type(mutator, TYPE_VECTOR, size);
  cvector(obj)->length = length;
  for(i = 0; i < length; ++i)
    cvector(obj)->vector[i] = fill;
  return obj;
}

static obj_t make_buckets(size_t length)
{
  size_t i, size = offsetof(buckets_s, bucket) + length * 2 * sizeof(obj_t);
  obj_t obj = gc_allocate_with_type(mutator, TYPE_BUCKETS, size);
  cbuckets(obj)->length = length;
  cbuckets(obj)->used = 0;
  cbuckets(obj)->deleted = 0;
  for(i = 0; i < length; ++i) {
    cbuckets(obj)->bucket[i].key = NULL;
    cbuckets(obj)->bucket[i].value = NULL;
  }
  return obj;
}

static obj_t make_table(size_t length, hash_t hashf, cmp_t cmpf)
{
  size_t l, size = sizeof(table_s);
  obj_t obj = gc_allocate_with_type(mutator, TYPE_TABLE, size);
  ctable(obj)->hash = hashf;
  ctable(obj)->cmp = cmpf;
  /* round up to next power of 2 */
  for(l = 1; l < length; l *= 2);
  ctable(obj)->buckets = make_buckets(l);
  return obj;
}

// A weak box is just an ephemeron with irrelevant value.
// We use the object itself as a value to avoid having to reference
// any global objects, but I don't think it's important.
// The basic ephemeron rule is that the key is not traced through the
// ephemeron, and the value is only traced if the key ended up being
// traced (from some other reference).
static obj_t make_weak_box(obj_t object) {
  weak_box_s* r = gc_allocate_ephemeron(mutator);

  ((type_s*)r)->header.header = header_live(TYPE_WEAK_BOX);
  gc_ephemeron_init(mutator, r,
                    gc_ref_from_heap_object(object),
                    gc_ref_from_heap_object(object));

  return r;
}

/* list access */

static inline obj_t car(obj_t pair) { return cpair(pair)->car; }
static inline obj_t cdr(obj_t pair) { return cpair(pair)->cdr; }
static inline obj_t caar(obj_t pair) { return car(car(pair)); }
static inline obj_t cadr(obj_t pair) { return car(cdr(pair)); }
static inline obj_t cdar(obj_t pair) { return cdr(car(pair)); }
static inline obj_t cddr(obj_t pair) { return cdr(cdr(pair)); }
static inline obj_t caaar(obj_t pair) { return car(car(car(pair))); }
static inline obj_t caadr(obj_t pair) { return car(car(cdr(pair))); }
static inline obj_t cadar(obj_t pair) { return car(cdr(car(pair))); }
static inline obj_t caddr(obj_t pair) { return car(cdr(cdr(pair))); }
static inline obj_t cdaar(obj_t pair) { return cdr(car(car(pair))); }
static inline obj_t cdadr(obj_t pair) { return cdr(car(cdr(pair))); }
static inline obj_t cddar(obj_t pair) { return cdr(cdr(car(pair))); }
static inline obj_t cdddr(obj_t pair) { return cdr(cdr(cdr(pair))); }

static inline void set_car(obj_t pair, obj_t value) {
  gc_write_barrier(gc_ref_from_heap_object(pair), sizeof(pair_s),
                   gc_edge(&cpair(pair)->car), gc_ref_from_heap_object(value));
  cpair(pair)->car = value;
}
static inline void set_cdr(obj_t pair, obj_t value) {
  gc_write_barrier(gc_ref_from_heap_object(pair), sizeof(pair_s),
                   gc_edge(&cpair(pair)->cdr), gc_ref_from_heap_object(value));
  cpair(pair)->cdr = value;
}

/* vector access */

static inline obj_t vref(obj_t vec, size_t i) {
  return cvector(vec)->vector[i];
}
static inline void vset(obj_t vec, size_t i, obj_t value) {
  gc_write_barrier(gc_ref_from_heap_object(vec), vector_osize(cvector(vec)),
                   gc_edge(&cvector(vec)->vector[i]),
                   gc_ref_from_heap_object(value));
  cvector(vec)->vector[i] = value;
}

/* weak box access */

static inline obj_t weak_box_value(obj_t box, obj_t defact) {
  struct gc_ref ref = gc_ephemeron_key(cweak_box(box));
  if (gc_ref_is_heap_object(ref))
    return gc_ref_heap_object(ref);
  else
    return defact;
}

/* getnbc -- get next non-blank char from stream */

static int getnbc(FILE *stream)
{
  int c;
  do {
    c = getc(stream);
    if(c == ';') {
      do
        c = getc(stream);
      while(c != EOF && c != '\n');
    }
  } while(isspace(c));
  return c;
}


/* isealpha -- test for "extended alphabetic" char
 *
 * Scheme symbols may contain any "extended alphabetic"
 * character (see section 2.1 of R4RS).  This function
 * returns non-zero if a character is in the set of
 * extended characters.
 */

static int isealpha(int c)
{
  return strchr("+-.*/<=>!?:$%_&~^", c) != NULL;
}


/* hash -- hash a string to an unsigned long
 *
 * This hash function was derived (with permission) from
 * Paul Haahr's hash in the most excellent rc 1.4.
 */

static unsigned long hash(const char *s, size_t length) {
  char c;
  unsigned long h=0;
  size_t i = 0;
  switch(length % 4) {
    do {
      c=s[i++]; h+=(c<<17)^(c<<11)^(c<<5)^(c>>1);
    case 3:
      c=s[i++]; h^=(c<<14)+(c<<7)+(c<<4)+c;
    case 2:
      c=s[i++]; h^=(~c<<11)|((c<<3)^(c>>1));
    case 1:
      c=s[i++]; h-=(c<<16)|(c<<9)|(c<<2)|(c&3);
    case 0:
      ;
    } while(i < length);
  }
  return h;
}


/* find -- find entry for symbol in symbol table
 *
 * Look for a symbol matching the string in the symbol table.
 * If the symbol was found, returns the address of the symbol
 * table entry which points to the symbol.  Otherwise it
 * either returns the address of a NULL entry into which the
 * new symbol should be inserted, or NULL if the symbol table
 * is full.
 */

static obj_t *find(char *string) {
  unsigned long i, h, probe;

  h = hash(string, strlen(string));
  probe = (h >> 8) | 1;
  h &= (symtab_size-1);
  i = h;
  do {
    if(symtab[i] == NULL ||
       strcmp(string, csymbol(symtab[i])->string) == 0)
      return &symtab[i];
    i = (i+probe) & (symtab_size-1);
  } while(i != h);

  return NULL;
}


/* rehash -- double size of symbol table */

static void rehash(void) {
  obj_t *old_symtab = symtab;
  unsigned old_symtab_size = symtab_size;
  struct handle *old_symtab_root = symtab_root;
  unsigned i;

  symtab_size *= 2;
  symtab = malloc(sizeof(obj_t) * symtab_size);
  if(symtab == NULL) error("out of memory");

  /* Initialize the new table to NULL so that "find" will work. */
  for(i = 0; i < symtab_size; ++i)
    symtab[i] = NULL;

  for(i = 0; i < old_symtab_size; ++i)
    if(old_symtab[i] != NULL) {
      obj_t *where = find(csymbol(old_symtab[i])->string);
      assert(where != NULL);    /* new table shouldn't be full */
      assert(*where == NULL);   /* shouldn't be in new table */
      *where = old_symtab[i];
    }

  // Now that the new symtab is in place, inform the GC.
  symtab_root = add_heap_root((void**)symtab, symtab_size);
  remove_heap_root(old_symtab_root);

  free(old_symtab);
}

/* union-find string in symbol table, rehashing if necessary */
static obj_t intern(char *string) {
  obj_t *where;

  where = find(string);

  if(where == NULL) {
    rehash();
    where = find(string);
    assert(where != NULL);      /* shouldn't be full after rehash */
  }

  if(*where == NULL)            /* symbol not found in table */
    *where = make_symbol(strlen(string), string);

  return *where;
}


/* Hash table implementation */

static unsigned long eq_hash(obj_t obj)
{
  union {char s[sizeof(obj_t)]; obj_t addr;} u = {""};
  u.addr = obj;
  return hash(u.s, sizeof(obj_t));
}

static int eqp(obj_t obj1, obj_t obj2)
{
  return obj1 == obj2;
}

static unsigned long eqv_hash(obj_t obj)
{
  switch(TYPE(obj)) {
  case TYPE_INTEGER:
    return cinteger(obj)->integer;
  case TYPE_CHARACTER:
    return ccharacter(obj)->c;
  default:
    return eq_hash(obj);
  }
}

static int eqvp(obj_t obj1, obj_t obj2)
{
  if (obj1 == obj2)
    return 1;
  if (TYPE(obj1) != TYPE(obj2))
    return 0;
  switch(TYPE(obj1)) {
  case TYPE_INTEGER:
    return cinteger(obj1)->integer == cinteger(obj2)->integer;
  case TYPE_CHARACTER:
    return ccharacter(obj1)->c == ccharacter(obj2)->c;
  default:
    return 0;
  }
}

static unsigned long string_hash(obj_t obj)
{
  unless(TYPE(obj) == TYPE_STRING)
    error("string-hash: argument must be a string");
  return hash(cstring(obj)->string, cstring(obj)->length);
}

static int string_equalp(obj_t obj1, obj_t obj2)
{
  return obj1 == obj2 ||
         (TYPE(obj1) == TYPE_STRING &&
          TYPE(obj2) == TYPE_STRING &&
          cstring(obj1)->length == cstring(obj2)->length &&
          0 == strcmp(cstring(obj1)->string, cstring(obj2)->string));
}

static struct bucket_s *buckets_find(obj_t tbl, obj_t buckets, obj_t key)
{
  unsigned long i, h, probe;
  struct bucket_s *result = NULL;
  assert(TYPE(tbl) == TYPE_TABLE);
  assert(TYPE(buckets) == TYPE_BUCKETS);
  h = ctable(tbl)->hash(key);
  probe = (h >> 8) | 1;
  h &= (cbuckets(buckets)->length-1);
  i = h;
  do {
    struct bucket_s *b = &cbuckets(buckets)->bucket[i];
    if(b->key == NULL || ctable(tbl)->cmp(b->key, key))
      return b;
    if(result == NULL && b->key == obj_deleted)
      result = b;
    i = (i+probe) & (cbuckets(buckets)->length-1);
  } while(i != h);
  return result;
}

static size_t table_size(obj_t tbl)
{
  size_t used, deleted;
  assert(TYPE(tbl) == TYPE_TABLE);
  used = cbuckets(ctable(tbl)->buckets)->used;
  deleted = cbuckets(ctable(tbl)->buckets)->deleted;
  assert(used >= deleted);
  return used - deleted;
}

static void table_rehash(obj_t tbl)
{
  size_t i, old_length, new_length;
  obj_t new_buckets;

  assert(TYPE(tbl) == TYPE_TABLE);
  old_length = cbuckets(ctable(tbl)->buckets)->length;
  new_length = old_length * 2;
  new_buckets = make_buckets(new_length);

  for (i = 0; i < old_length; ++i) {
    struct bucket_s *old_b = &cbuckets(ctable(tbl)->buckets)->bucket[i];
    if (old_b->key != NULL && old_b->key != obj_deleted) {
      struct bucket_s *b = buckets_find(tbl, new_buckets, old_b->key);
      assert(b != NULL);        /* new table shouldn't be full */
      assert(b->key == NULL);   /* shouldn't be in new table */
      *b = *old_b;
      ++ cbuckets(new_buckets)->used;
    }
  }

  assert(cbuckets(new_buckets)->used == table_size(tbl));
  gc_write_barrier(gc_ref_from_heap_object(tbl), sizeof(table_s),
                   gc_edge(&ctable(tbl)->buckets),
                   gc_ref_from_heap_object(new_buckets));
  ctable(tbl)->buckets = new_buckets;
}

static obj_t table_ref(obj_t tbl, obj_t key)
{
  struct bucket_s *b;
  assert(TYPE(tbl) == TYPE_TABLE);
  b = buckets_find(tbl, ctable(tbl)->buckets, key);
  if (b && b->key != NULL && b->key != obj_deleted)
    return b->value;
  return NULL;
}

static int table_full(obj_t tbl)
{
  assert(TYPE(tbl) == TYPE_TABLE);
  return cbuckets(ctable(tbl)->buckets)->used >= cbuckets(ctable(tbl)->buckets)->length / 2;
}

static void table_set(obj_t tbl, obj_t key, obj_t value)
{
  struct bucket_s *b;
  assert(TYPE(tbl) == TYPE_TABLE);
  if (table_full(tbl) || (b = buckets_find(tbl, ctable(tbl)->buckets, key)) == NULL) {
    table_rehash(tbl);
    b = buckets_find(tbl, ctable(tbl)->buckets, key);
    assert(b != NULL);          /* shouldn't be full after rehash */
  }
  if (b->key == NULL) {
    b->key = key;
    ++ cbuckets(ctable(tbl)->buckets)->used;
  } else if (b->key == obj_deleted) {
    b->key = key;
    assert(cbuckets(ctable(tbl)->buckets)->deleted > 0);
    -- cbuckets(ctable(tbl)->buckets)->deleted;
  }
  b->value = value;
}

static void table_delete(obj_t tbl, obj_t key)
{
  struct bucket_s *b;
  assert(TYPE(tbl) == TYPE_TABLE);
  b = buckets_find(tbl, ctable(tbl)->buckets, key);
  if (b != NULL && b->key != NULL) {
    b->key = obj_deleted;
    ++ cbuckets(ctable(tbl)->buckets)->deleted;
  }
}


static void print(obj_t obj, unsigned depth, FILE *stream)
{
  switch(TYPE(obj)) {
    case TYPE_INTEGER: {
      fprintf(stream, "%ld", cinteger(obj)->integer);
    } break;

    case TYPE_SYMBOL: {
      fputs(csymbol(obj)->string, stream);
    } break;

    case TYPE_SPECIAL: {
      fputs(cspecial(obj)->name, stream);
    } break;

    case TYPE_PORT: {
      assert(TYPE(cport(obj)->name) == TYPE_STRING);
      fprintf(stream, "#[port \"%s\"]",
              cstring(cport(obj)->name)->string);
    } break;

    case TYPE_STRING: {
      size_t i;
      putc('"', stream);
      for(i = 0; i < cstring(obj)->length; ++i) {
        char c = cstring(obj)->string[i];
        switch(c) {
          case '\\': fputs("\\\\", stream); break;
          case '"': fputs("\\\"", stream); break;
          default: putc(c, stream); break;
        }
      }
      putc('"', stream);
    } break;

    case TYPE_PROMISE: {
      fprintf(stream, "#[%sevaluated promise ",
              cpromise(obj)->fulfilledp ? "" : "un");
      print(cpromise(obj)->fulfiller, depth - 1, stream);
      putc(']', stream);
    } break;

    case TYPE_PAIR: {
      if(TYPE(car(obj)) == TYPE_SYMBOL &&
         TYPE(cdr(obj)) == TYPE_PAIR &&
         cddr(obj) == obj_empty) {
        if(car(obj) == obj_quote) {
          putc('\'', stream);
          if(depth == 0)
            fputs("...", stream);
          else
            print(cadr(obj), depth - 1, stream);
          break;
        }
        if(car(obj) == obj_quasiquote) {
          putc('`', stream);
          if(depth == 0)
            fputs("...", stream);
          else
            print(cadr(obj), depth - 1, stream);
          break;
        }
        if(car(obj) == obj_unquote) {
          putc(',', stream);
          if(depth == 0)
            fputs("...", stream);
          else
            print(cadr(obj), depth - 1, stream);
          break;
        }
        if(car(obj) == obj_unquote_splic) {
          fputs(",@", stream);
          if(depth == 0)
            fputs("...", stream);
          else
            print(cadr(obj), depth - 1, stream);
          break;
        }
      }
      putc('(', stream);
      if(depth == 0)
        fputs("...", stream);
      else {
        for(;;) {
          print(car(obj), depth - 1, stream);
          obj = cdr(obj);
          if(TYPE(obj) != TYPE_PAIR) break;
          putc(' ', stream);
        }
        if(obj != obj_empty) {
          fputs(" . ", stream);
          print(obj, depth - 1, stream);
        }
      }
      putc(')', stream);
    } break;

    case TYPE_VECTOR: {
      fputs("#(", stream);
      if(depth == 0)
        fputs("...", stream);
      else {
        size_t i;
        for(i = 0; i < cvector(obj)->length; ++i) {
          if(i > 0) putc(' ', stream);
          print(vref(obj, i), depth - 1, stream);
        }
      }
      putc(')', stream);
    } break;

    case TYPE_BUCKETS: {
      size_t i;
      for(i = 0; i < cbuckets(obj)->length; ++i) {
        struct bucket_s *b = &cbuckets(obj)->bucket[i];
        if(b->key != NULL && b->key != obj_deleted) {
          fputs(" (", stream);
          print(b->key, depth - 1, stream);
          putc(' ', stream);
          print(b->value, depth - 1, stream);
          putc(')', stream);
        }
      }
    } break;

    case TYPE_TABLE: {
      fputs("#[hashtable", stream);
      print(ctable(obj)->buckets, depth - 1, stream);
      putc(']', stream);
    } break;

    case TYPE_OPERATOR: {
      fprintf(stream, "#[operator \"%s\" %p ",
              coperator(obj)->name,
              (void *)obj);
      if(depth == 0)
        fputs("...", stream);
      else {
        print(coperator(obj)->arguments, depth - 1, stream);
        putc(' ', stream);
        print(coperator(obj)->body, depth - 1, stream);
        putc(' ', stream);
        print(coperator(obj)->env, depth - 1, stream);
        putc(' ', stream);
        print(coperator(obj)->op_env, depth - 1, stream);
      }
      putc(']', stream);
    } break;

    case TYPE_CHARACTER: {
      fprintf(stream, "#\\%c", ccharacter(obj)->c);
    } break;

    case TYPE_WEAK_BOX: {
      fputs("#[weak-box ", stream);
      print(weak_box_value(obj, obj_false), depth - 1, stream);
      putc(']', stream);
    } break;

    default:
      assert(0);
      abort();
  }
}


static obj_t read_integer(FILE *stream, int c)
{
  long integer = 0;

  do {
    integer = integer*10 + c-'0';
    c = getc(stream);
  } while(isdigit(c));
  ungetc(c, stream);

  return make_integer(integer);
}


static obj_t read_symbol(FILE *stream, int c)
{
  int length = 0;
  char string[SYMMAX+1];

  do {
    string[length++] = tolower(c);
    c = getc(stream);
  } while(length < SYMMAX && (isalnum(c) || isealpha(c)));

  if(isalnum(c) || isealpha(c))
    error("read: symbol too long");

  string[length] = '\0';

  ungetc(c, stream);

  return intern(string);
}


static obj_t read_string(FILE *stream, int c)
{
  int length = 0;
  char string[STRMAX+1];

  for(;;) {
    c = getc(stream);
    if(c == EOF)
      error("read: end of file during string");
    if(c == '"') break;
    if(length >= STRMAX)
      error("read: string too long");
    if(c == '\\') {
      c = getc(stream);
      switch(c) {
        case '\\': break;
        case '"': break;
        case 'n': c = '\n'; break;
        case 't': c = '\t'; break;
        case EOF:
          error("read: end of file in escape sequence in string");
        default:
          error("read: unknown escape '%c'", c);
      }
    }
    string[length++] = c;
  }

  string[length] = '\0';

  return make_string(length, string);
}


static obj_t read_(FILE *stream);


static obj_t read_quote(FILE *stream, int c)
{
  return make_pair(obj_quote, make_pair(read_(stream), obj_empty));
}


static obj_t read_quasiquote(FILE *stream, int c)
{
  return make_pair(obj_quasiquote, make_pair(read_(stream), obj_empty));
}


static obj_t read_unquote(FILE *stream, int c)
{
  c = getc(stream);
  if(c == '@')
    return make_pair(obj_unquote_splic, make_pair(read_(stream), obj_empty));
  ungetc(c, stream);
  return make_pair(obj_unquote, make_pair(read_(stream), obj_empty));
}


static obj_t read_list(FILE *stream, int c)
{
  obj_t list, new, end;

  list = obj_empty;
  end = NULL;                   /* suppress "uninitialized" warning in GCC */

  for(;;) {
    c = getnbc(stream);
    if(c == ')' || c == '.' || c == EOF) break;
    ungetc(c, stream);
    new = make_pair(read_(stream), obj_empty);
    if(list == obj_empty) {
      list = new;
      end = new;
    } else {
      set_cdr(end, new);
      end = new;
    }
  }

  if(c == '.') {
    if(list == obj_empty)
      error("read: unexpected dot");
    set_cdr(end, read_(stream));
    c = getnbc(stream);
  }

  if(c != ')')
    error("read: expected close parenthesis");

  return list;
}


static obj_t list_to_vector(obj_t list)
{
  size_t i;
  obj_t l, vector;
  i = 0;
  l = list;
  while(TYPE(l) == TYPE_PAIR) {
    ++i;
    l = cdr(l);
  }
  if(l != obj_empty)
    return obj_error;
  vector = make_vector(i, obj_undefined);
  i = 0;
  l = list;
  while(TYPE(l) == TYPE_PAIR) {
    vset(vector, i, car(l));
    ++i;
    l = cdr(l);
  }
  return vector;
}


static obj_t read_special(FILE *stream, int c)
{
  c = getnbc(stream);
  switch(tolower(c)) {
    case 't': return obj_true;
    case 'f': return obj_false;
    case '\\': {                /* character (R4RS 6.6) */
      c = getc(stream);
      if(c == EOF)
        error("read: end of file reading character literal");
      return make_character(c);
    }
    case '(': {                 /* vector (R4RS 6.8) */
      obj_t list = read_list(stream, c);
      obj_t vector = list_to_vector(list);
      if(vector == obj_error)
        error("read: illegal vector syntax");
      return vector;
    }
  }
  error("read: unknown special '%c'", c);
  return obj_error;
}


static obj_t read_(FILE *stream)
{
  int c;

  c = getnbc(stream);
  if(c == EOF) return obj_eof;

  if(isdigit(c))
    return read_integer(stream, c);

  switch(c) {
    case '\'': return read_quote(stream, c);
    case '`':  return read_quasiquote(stream, c);
    case ',':  return read_unquote(stream, c);
    case '(':  return read_list(stream, c);
    case '#':  return read_special(stream, c);
    case '"':  return read_string(stream, c);
    case '-': case '+': {
      int next = getc(stream);
      if(isdigit(next)) {
        obj_t integer = read_integer(stream, next);
        if(c == '-')
          cinteger(integer)->integer = -cinteger(integer)->integer;
        return integer;
      }
      ungetc(next, stream);
    } break; /* fall through to read as symbol */
  }

  if(isalpha(c) || isealpha(c))
    return read_symbol(stream, c);

  error("read: illegal char '%c'", c);
  return obj_error;
}


/* lookup_in_frame -- look up a symbol in single frame
 *
 * Search a single frame of the environment for a symbol binding.
 */

static obj_t lookup_in_frame(obj_t frame, obj_t symbol)
{
  while(frame != obj_empty) {
    assert(TYPE(frame) == TYPE_PAIR);
    assert(TYPE(car(frame)) == TYPE_PAIR);
    assert(TYPE(caar(frame)) == TYPE_SYMBOL);
    if(caar(frame) == symbol)
      return car(frame);
    frame = cdr(frame);
  }
  return obj_undefined;
}


/* lookup -- look up symbol in environment
 *
 * Search an entire environment for a binding of a symbol.
 */

static obj_t lookup(obj_t env, obj_t symbol)
{
  obj_t binding;
  while(env != obj_empty) {
    assert(TYPE(env) == TYPE_PAIR);
    binding = lookup_in_frame(car(env), symbol);
    if(binding != obj_undefined)
      return binding;
    env = cdr(env);
  }
  return obj_undefined;
}


/* define -- define symbol in environment
 *
 * In Scheme, define will actually rebind (i.e. set) a symbol in the
 * same frame of the environment, or add a binding if it wasn't already
 * set.  This has the effect of making bindings local to functions
 * (see how entry_interpret adds an empty frame to the environments),
 * allowing recursion, and allowing redefinition at the top level.
 * See R4R2 section 5.2 for details.
 */

static void define(obj_t env, obj_t symbol, obj_t value)
{
  obj_t binding;
  assert(TYPE(env) == TYPE_PAIR);       /* always at least one frame */
  binding = lookup_in_frame(car(env), symbol);
  if(binding != obj_undefined)
    set_cdr(binding, value);
  else
    set_car(env, make_pair(make_pair(symbol, value), car(env)));
}


static obj_t eval(obj_t env, obj_t op_env, obj_t exp);

static obj_t eval(obj_t env, obj_t op_env, obj_t exp)
{
  for(;;) {
    obj_t operator;
    obj_t result;

    /* self-evaluating */
    if(TYPE(exp) == TYPE_INTEGER ||
       (TYPE(exp) == TYPE_SPECIAL && exp != obj_empty) ||
       TYPE(exp) == TYPE_STRING ||
       TYPE(exp) == TYPE_CHARACTER ||
       TYPE(exp) == TYPE_OPERATOR)
      return exp;

    /* symbol lookup */
    if(TYPE(exp) == TYPE_SYMBOL) {
      obj_t binding = lookup(env, exp);
      if(binding == obj_undefined)
        error("eval: unbound symbol \"%s\"", csymbol(exp)->string);
      return cdr(binding);
    }

    if(TYPE(exp) != TYPE_PAIR) {
      error("eval: unknown syntax");
      return obj_error;
    }

    /* apply operator or function */
    if(TYPE(car(exp)) == TYPE_SYMBOL) {
      obj_t binding = lookup(op_env, car(exp));
      if(binding != obj_undefined) {
        operator = cdr(binding);
        assert(TYPE(operator) == TYPE_OPERATOR);
        result = (*coperator(operator)->entry)(env, op_env, operator, cdr(exp));
        goto found;
      }
    }
    operator = eval(env, op_env, car(exp));
    unless(TYPE(operator) == TYPE_OPERATOR)
      error("eval: application of non-function");
    result = (*coperator(operator)->entry)(env, op_env, operator, cdr(exp));

  found:
    if (!(TYPE(result) == TYPE_PAIR && car(result) == obj_tail))
      return result;

    env = cadr(result);
    op_env = caddr(result);
    exp = car(cdddr(result));
  }
}


static obj_t load(obj_t env, obj_t op_env, const char *filename) {
  obj_t result = obj_undefined;
  FILE *stream = fopen(filename, "r");
  if(stream == NULL)
    error("load: cannot open %s: %s", filename, strerror(errno));
  for(;;) {
    obj_t obj = read_(stream);
    if(obj == obj_eof) break;
    result = eval(env, op_env, obj);
  }
  /* TODO: if there was an error, this doesn't get closed */
  fclose(stream);
  return result;
}


/* OPERATOR UTILITIES */


/* eval_list -- evaluate list of expressions giving list of results
 *
 * eval_list evaluates a list of expressions and yields a list of their
 * results, in order.  If the list is badly formed, an error is thrown
 * using the message given.
 */

static obj_t eval_list(obj_t env, obj_t op_env, obj_t list, char *message)
{
  obj_t result, end, pair;
  result = obj_empty;
  end = NULL;                   /* suppress "uninitialized" warning in GCC */
  while(list != obj_empty) {
    if(TYPE(list) != TYPE_PAIR)
      error(message);
    pair = make_pair(eval(env, op_env, car(list)), obj_empty);
    if(result == obj_empty)
      result = pair;
    else
      set_cdr(end, pair);
    end = pair;
    list = cdr(list);
  }
  return result;
}


/* eval_args1 -- evaluate some operator arguments
 *
 * See eval_args and eval_args_rest for usage.
 */

static obj_t eval_args1(char *name, obj_t env, obj_t op_env,
                        obj_t operands, unsigned n, va_list args)
{
  unsigned i;
  for(i = 0; i < n; ++i) {
    unless(TYPE(operands) == TYPE_PAIR)
      error("eval: too few arguments to %s", name);
    *va_arg(args, obj_t *) = eval(env, op_env, car(operands));
    operands = cdr(operands);
  }
  return operands;
}


/* eval_args -- evaluate operator arguments without rest list
 *
 * eval_args evaluates the first "n" expressions from the list of
 * expressions in "operands", returning the rest of the operands
 * unevaluated.  It puts the results of evaluation in the addresses
 * passed in the vararg list.  If the operands list is badly formed
 * an error is thrown using the operator name passed.  For example:
 *
 *   eval_args("foo", env, op_env, operands, 2, &arg1, &arg2);
 */

static void eval_args(char *name, obj_t env, obj_t op_env,
                      obj_t operands, unsigned n, ...)
{
  va_list args;
  va_start(args, n);
  operands = eval_args1(name, env, op_env, operands, n, args);
  unless(operands == obj_empty)
    error("eval: too many arguments to %s", name);
  va_end(args);
}


/* eval_args_rest -- evaluate operator arguments with rest list
 *
 * eval_args_rest evaluates the first "n" expressions from the list of
 * expressions in "operands", then evaluates the rest of the operands
 * using eval_list and puts the result at *restp.  It puts the results
 * of evaluating the first "n" operands in the addresses
 * passed in the vararg list.  If the operands list is badly formed
 * an error is thrown using the operator name passed.  For example:
 *
 *   eval_args_rest("foo", env, op_env, operands, &rest, 2, &arg1, &arg2);
 */

static void eval_args_rest(char *name, obj_t env, obj_t op_env,
                           obj_t operands, obj_t *restp, unsigned n, ...)
{
  va_list args;
  va_start(args, n);
  operands = eval_args1(name, env, op_env, operands, n, args);
  va_end(args);
  *restp = eval_list(env, op_env, operands, "eval: badly formed argument list");
}


/* eval_tail -- return an object that will cause eval to loop
 *
 * Rather than calling `eval` an operator can return a special object that
 * causes a calling `eval` to loop, avoiding using up a C stack frame.
 * This implements tail recursion (in a simple way).
 */

static obj_t eval_tail(obj_t env, obj_t op_env, obj_t exp)
{
  return make_pair(obj_tail,
                   make_pair(env,
                             make_pair(op_env,
                                       make_pair(exp,
                                                 obj_empty))));
}


/* eval_body -- evaluate a list of expressions, returning last result
 *
 * This is used for the bodies of forms such as let, begin, etc. where
 * a list of expressions is allowed.
 */

static obj_t eval_body(obj_t env, obj_t op_env, obj_t operator, obj_t body)
{
  for (;;) {
    if (TYPE(body) != TYPE_PAIR)
      error("%s: illegal expression list", coperator(operator)->name);
    if (cdr(body) == obj_empty)
      return eval_tail(env, op_env, car(body));
    (void)eval(env, op_env, car(body));
    body = cdr(body);
  }
}


/* BUILT-IN OPERATORS */


/* entry_interpret -- interpreted function entry point
 *
 * When a function is made using lambda (see entry_lambda) an operator
 * is created with entry_interpret as its entry point, and the arguments
 * and body of the function.  The entry_interpret function evaluates
 * the operands of the function and binds them to the argument names
 * in a new frame added to the lambda's closure environment.   It then
 * evaluates the body in that environment, executing the function.
 */

static obj_t entry_interpret(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arguments, fun_env, fun_op_env;

  assert(TYPE(operator) == TYPE_OPERATOR);

  /* Make a new frame so that bindings are local to the function. */
  /* Arguments will be bound in this new frame. */
  fun_env = make_pair(obj_empty, coperator(operator)->env);
  fun_op_env = make_pair(obj_empty, coperator(operator)->op_env);

  arguments = coperator(operator)->arguments;
  while(operands != obj_empty) {
    if(arguments == obj_empty)
      error("eval: function applied to too many arguments");
    if(TYPE(arguments) == TYPE_SYMBOL) {
      define(fun_env, arguments,
             eval_list(env, op_env, operands, "eval: badly formed argument list"));
      operands = obj_empty;
      arguments = obj_empty;
    } else {
      assert(TYPE(arguments) == TYPE_PAIR &&
             TYPE(car(arguments)) == TYPE_SYMBOL);
      define(fun_env,
             car(arguments),
             eval(env, op_env, car(operands)));
      operands = cdr(operands);
      arguments = cdr(arguments);
    }
  }
  if(arguments != obj_empty)
    error("eval: function applied to too few arguments");

  return eval_tail(fun_env, fun_op_env, coperator(operator)->body);
}


/* entry_quote -- return operands unevaluated
 *
 * In Scheme, (quote foo) evaluates to foo (i.e. foo is not evaluated).
 * See R4RS 4.1.2.  The reader expands "'x" to "(quote x)".
 */

static obj_t entry_quote(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  unless(TYPE(operands) == TYPE_PAIR &&
         cdr(operands) == obj_empty)
    error("%s: illegal syntax", coperator(operator)->name);
  return car(operands);
}


/* entry_define -- bind a symbol in the top frame of the environment
 *
 * In Scheme, "(define <symbol> <expression>)" evaluates expressions
 * and binds it to symbol in the top frame of the environment (see
 * R4RS 5.2).  This code also allows the non-essential syntax for
 * define, "(define (<symbol> <formals>) <body>)" as a short-hand for
 * "(define <symbol> (lambda (<formals>) <body>))".
 */

static obj_t entry_define(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t symbol = NULL, value = NULL;
  unless(TYPE(operands) == TYPE_PAIR &&
         TYPE(cdr(operands)) == TYPE_PAIR)
    error("%s: illegal syntax", coperator(operator)->name);
  if(TYPE(car(operands)) == TYPE_SYMBOL) {
    unless(cddr(operands) == obj_empty)
      error("%s: too many arguments", coperator(operator)->name);
    symbol = car(operands);
    value = eval(env, op_env, cadr(operands));
  } else if(TYPE(car(operands)) == TYPE_PAIR &&
            TYPE(caar(operands)) == TYPE_SYMBOL) {
    symbol = caar(operands);
    value = eval(env, op_env,
                 make_pair(obj_lambda,
                           make_pair(cdar(operands), cdr(operands))));
  } else
    error("%s: applied to binder", coperator(operator)->name);
  define(env, symbol, value);
  return symbol;
}


/* entry_if -- one- or two-armed conditional
 *
 * "(if <test> <consequent> <alternate>)" and "(if <test> <consequent>)".
 * See R4RS 4.1.5.
 */

static obj_t entry_if(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t test;
  unless(TYPE(operands) == TYPE_PAIR &&
         TYPE(cdr(operands)) == TYPE_PAIR &&
         (cddr(operands) == obj_empty ||
          (TYPE(cddr(operands)) == TYPE_PAIR &&
           cdddr(operands) == obj_empty)))
    error("%s: illegal syntax", coperator(operator)->name);
  test = eval(env, op_env, car(operands));
  /* Anything which is not #f counts as true [R4RS 6.1]. */
  if(test != obj_false)
    return eval_tail(env, op_env, cadr(operands));
  if(TYPE(cddr(operands)) == TYPE_PAIR)
    return eval_tail(env, op_env, caddr(operands));
  return obj_undefined;
}


/* entry_cond -- general conditional
 *
 * "(cond (<test1> <exp1.1> ...) (<test2> <exp2.1> ...) ... [(else <expe.1> ...)])"
 */

static obj_t entry_cond(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  unless(TYPE(operands) == TYPE_PAIR)
    error("%s: illegal syntax", coperator(operator)->name);
  while(TYPE(operands) == TYPE_PAIR) {
    obj_t clause = car(operands);
    obj_t result;
    unless(TYPE(clause) == TYPE_PAIR &&
           TYPE(cdr(clause)) == TYPE_PAIR)
      error("%s: illegal clause syntax", coperator(operator)->name);
    if(car(clause) == obj_else) {
      unless(cdr(operands) == obj_empty)
        error("%s: else clause must come last", coperator(operator)->name);
      result = obj_true;
    } else
      result = eval(env, op_env, car(clause));
    if(result != obj_false) {
      if (cdr(clause) == obj_empty)
        return result;
      return eval_body(env, op_env, operator, cdr(clause));
    }
    operands = cdr(operands);
  }
  return obj_undefined;
}


/* entry_and -- (and <test1> ...) */

static obj_t entry_and(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t test;
  if (operands == obj_empty)
    return obj_true;
  do {
    if (TYPE(operands) != TYPE_PAIR)
      error("%s: illegal syntax", coperator(operator)->name);
    if (cdr(operands) == obj_empty)
      return eval_tail(env, op_env, car(operands));
    test = eval(env, op_env, car(operands));
    operands = cdr(operands);
  } while (test != obj_false);
  return test;
}


/* entry_or -- (or <test1> ...) */

static obj_t entry_or(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t test;
  if (operands == obj_empty)
    return obj_false;
  do {
    if (TYPE(operands) != TYPE_PAIR)
      error("%s: illegal syntax", coperator(operator)->name);
    if (cdr(operands) == obj_empty)
      return eval_tail(env, op_env, car(operands));
    test = eval(env, op_env, car(operands));
    operands = cdr(operands);
  } while (test == obj_false);
  return test;
}


/* entry_let -- (let <bindings> <body>) */
/* TODO: Too much common code with let* */

static obj_t entry_let(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t inner_env, bindings;
  unless(TYPE(operands) == TYPE_PAIR &&
         TYPE(cdr(operands)) == TYPE_PAIR)
    error("%s: illegal syntax", coperator(operator)->name);
  inner_env = make_pair(obj_empty, env);        /* TODO: common with interpret */
  bindings = car(operands);
  while(TYPE(bindings) == TYPE_PAIR) {
    obj_t binding = car(bindings);
    unless(TYPE(binding) == TYPE_PAIR &&
           TYPE(car(binding)) == TYPE_SYMBOL &&
           TYPE(cdr(binding)) == TYPE_PAIR &&
           cddr(binding) == obj_empty)
      error("%s: illegal binding", coperator(operator)->name);
    define(inner_env, car(binding), eval(env, op_env, cadr(binding)));
    bindings = cdr(bindings);
  }
  if(bindings != obj_empty)
    error("%s: illegal bindings list", coperator(operator)->name);
  return eval_body(inner_env, op_env, operator, cdr(operands));
}


/* entry_let_star -- (let* <bindings> <body>) */
/* TODO: Too much common code with let */

static obj_t entry_let_star(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t inner_env, bindings;
  unless(TYPE(operands) == TYPE_PAIR &&
         TYPE(cdr(operands)) == TYPE_PAIR)
    error("%s: illegal syntax", coperator(operator)->name);
  inner_env = make_pair(obj_empty, env);        /* TODO: common with interpret */
  bindings = car(operands);
  while(TYPE(bindings) == TYPE_PAIR) {
    obj_t binding = car(bindings);
    unless(TYPE(binding) == TYPE_PAIR &&
           TYPE(car(binding)) == TYPE_SYMBOL &&
           TYPE(cdr(binding)) == TYPE_PAIR &&
           cddr(binding) == obj_empty)
      error("%s: illegal binding", coperator(operator)->name);
    define(inner_env, car(binding), eval(inner_env, op_env, cadr(binding)));
    bindings = cdr(bindings);
  }
  if(bindings != obj_empty)
    error("%s: illegal bindings list", coperator(operator)->name);
  return eval_body(inner_env, op_env, operator, cdr(operands));
}


/* entry_letrec -- (letrec <bindings> <body>) */
/* TODO: Too much common code with let and let* */

static obj_t entry_letrec(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t inner_env, bindings;
  unless(TYPE(operands) == TYPE_PAIR &&
         TYPE(cdr(operands)) == TYPE_PAIR)
    error("%s: illegal syntax", coperator(operator)->name);
  inner_env = make_pair(obj_empty, env);        /* TODO: common with interpret */
  bindings = car(operands);
  while(TYPE(bindings) == TYPE_PAIR) {
    obj_t binding = car(bindings);
    unless(TYPE(binding) == TYPE_PAIR &&
           TYPE(car(binding)) == TYPE_SYMBOL &&
           TYPE(cdr(binding)) == TYPE_PAIR &&
           cddr(binding) == obj_empty)
      error("%s: illegal binding", coperator(operator)->name);
    define(inner_env, car(binding), obj_undefined);
    bindings = cdr(bindings);
  }
  if(bindings != obj_empty)
    error("%s: illegal bindings list", coperator(operator)->name);
  bindings = car(operands);
  while(TYPE(bindings) == TYPE_PAIR) {
    obj_t binding = car(bindings);
    define(inner_env, car(binding), eval(inner_env, op_env, cadr(binding)));
    bindings = cdr(bindings);
  }
  return eval_body(inner_env, op_env, operator, cdr(operands));
}


/* entry_do -- (do ((<var> <init> <step1>) ...) (<test> <exp> ...) <command> ...)
 * Do is an iteration construct. It specifies a set of variables to be
 * bound, how they are to be initialized at the start, and how they
 * are to be updated on each iteration. When a termination condition
 * is met, the loop exits with a specified result value.
 * See R4RS 4.2.4.
 */
static obj_t entry_do(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t inner_env, next_env, bindings;
  unless(TYPE(operands) == TYPE_PAIR &&
         TYPE(cdr(operands)) == TYPE_PAIR &&
         TYPE(cadr(operands)) == TYPE_PAIR)
    error("%s: illegal syntax", coperator(operator)->name);
  inner_env = make_pair(obj_empty, env);

  /* Do expressions are evaluated as follows: The <init> expressions
     are evaluated (in some unspecified order), the <variable>s are
     bound to fresh locations, the results of the <init> expressions
     are stored in the bindings of the <variable>s, and then the
     iteration phase begins. */
  bindings = car(operands);
  while(TYPE(bindings) == TYPE_PAIR) {
    obj_t binding = car(bindings);
    unless(TYPE(binding) == TYPE_PAIR &&
           TYPE(car(binding)) == TYPE_SYMBOL &&
           TYPE(cdr(binding)) == TYPE_PAIR &&
           (cddr(binding) == obj_empty ||
            (TYPE(cddr(binding)) == TYPE_PAIR &&
             cdddr(binding) == obj_empty)))
      error("%s: illegal binding", coperator(operator)->name);
    define(inner_env, car(binding), eval(env, op_env, cadr(binding)));
    bindings = cdr(bindings);
  }
  for(;;) {
    /* Each iteration begins by evaluating <test>; */
    obj_t test = cadr(operands);
    if(eval(inner_env, op_env, car(test)) == obj_false) {
      /* if the result is false (see section see section 6.1
         Booleans), then the <command> expressions are evaluated in
         order for effect, */
      obj_t commands = cddr(operands);
      while(TYPE(commands) == TYPE_PAIR) {
        eval(inner_env, op_env, car(commands));
        commands = cdr(commands);
      }
      unless(commands == obj_empty)
        error("%s: illegal syntax", coperator(operator)->name);

      /* the <step> expressions are evaluated in some unspecified
         order, the <variable>s are bound to fresh locations, the
         results of the <step>s are stored in the bindings of the
         <variable>s, and the next iteration begins. */
      bindings = car(operands);
      next_env = make_pair(obj_empty, inner_env);
      while(TYPE(bindings) == TYPE_PAIR) {
        obj_t binding = car(bindings);
        unless(cddr(binding) == obj_empty)
          define(next_env, car(binding), eval(inner_env, op_env, caddr(binding)));
        bindings = cdr(bindings);
      }
      inner_env = next_env;
    } else {
      /* If <test> evaluates to a true value, then the <expression>s
         are evaluated from left to right and the value of the last
         <expression> is returned as the value of the do expression.
         If no <expression>s are present, then the value of the do
         expression is unspecified. */
      obj_t result = obj_undefined;
      test = cdr(test);
      while(TYPE(test) == TYPE_PAIR) {
        result = eval(inner_env, op_env, car(test));
        test = cdr(test);
      }
      unless(test == obj_empty)
        error("%s: illegal syntax", coperator(operator)->name);
      return result;
    }
  }
}


/* entry_delay -- (delay <exp>) */

static obj_t entry_delay(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  unless(TYPE(operands) == TYPE_PAIR &&
         cdr(operands) == obj_empty)
    error("%s: illegal syntax", coperator(operator)->name);
  return make_promise(make_operator("anonymous promise",
                                    entry_interpret, obj_empty,
                                    car(operands), env, op_env));
}


static obj_t quasiquote(obj_t env, obj_t op_env, obj_t operator, obj_t arg)
{
  obj_t result = obj_empty, end = NULL, insert;
  unless(TYPE(arg) == TYPE_PAIR)
    return arg;
  while(TYPE(arg) == TYPE_PAIR) {
    if(TYPE(car(arg)) == TYPE_PAIR &&
       TYPE(caar(arg)) == TYPE_SYMBOL &&
       (caar(arg) == obj_unquote ||
        caar(arg) == obj_unquote_splic)) {
      unless(TYPE(cdar(arg)) == TYPE_PAIR &&
             cddar(arg) == obj_empty)
        error("%s: illegal %s syntax", coperator(operator)->name,
              csymbol(caar(arg))->string);
      insert = eval(env, op_env, cadar(arg));
      if(caar(arg) == obj_unquote) {
        obj_t pair = make_pair(insert, obj_empty);
        if(result == obj_empty)
          result = pair;
        if(end)
          set_cdr(end, pair);
        end = pair;
      } else if(caar(arg) == obj_unquote_splic) {
        while(TYPE(insert) == TYPE_PAIR) {
          obj_t pair = make_pair(car(insert), obj_empty);
          if(result == obj_empty)
            result = pair;
          if(end)
            set_cdr(end, pair);
          end = pair;
          insert = cdr(insert);
        }
        if(insert != obj_empty)
          error("%s: %s expression must return list",
                coperator(operator)->name, csymbol(caar(arg))->string);
      }
    } else {
      obj_t pair = make_pair(quasiquote(env, op_env, operator, car(arg)), obj_empty);
      if(result == obj_empty)
        result = pair;
      if(end)
        set_cdr(end, pair);
      end = pair;
    }
    arg = cdr(arg);
  }
  return result;
}


/* entry_quasiquote -- (quasiquote <template>) or `<template> */

static obj_t entry_quasiquote(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  unless(TYPE(operands) == TYPE_PAIR &&
         cdr(operands) == obj_empty)
    error("%s: illegal syntax", coperator(operator)->name);
  return quasiquote(env, op_env, operator, car(operands));
}


/* entry_set -- assignment
 *
 * (set! <variable> <expression>)
 * See R4RS 4.1.6.
 */

static obj_t entry_set(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t symbol, binding, value;
  unless(TYPE(operands) == TYPE_PAIR &&
         TYPE(cdr(operands)) == TYPE_PAIR &&
         cddr(operands) == obj_empty)
    error("%s: illegal syntax", coperator(operator)->name);
  unless(TYPE(car(operands)) == TYPE_SYMBOL)
    error("%s: applied to non-symbol", coperator(operator)->name);
  symbol = car(operands);
  binding = lookup(env, symbol);
  if(binding == obj_undefined)
    error("%s: applied to unbound symbol \"%s\"",
          coperator(operator)->name, csymbol(symbol)->string);
  value = eval(env, op_env, cadr(operands));
  set_cdr(binding, value);
  return value;
}


/* entry_lambda -- lambda expressions
 *
 * (lambda <formals> <body>)
 * See R4RS 4.1.4.
 *
 * The entry_lambda function creates a new object of TYPE_OPERATOR
 * which captures the current environments, and contains the lambda
 * formals and body.  This operator has an entry point at
 * entry_interpret, which will evaluate and bind the arguments when
 * the operator is applied.
 *
 * [Capturing the whole environment is bad for GC because it means
 *  that everything defined when the lambda is evaluated will survive
 *  for as long as the operator survives.  It would be better to
 *  examine the lambda body and determine which variables it references,
 *  and either create a new environment or build a new body with just
 *  those variables bound.]
 */

static obj_t entry_lambda(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t list;
  unless(TYPE(operands) == TYPE_PAIR &&
         TYPE(cdr(operands)) == TYPE_PAIR)
    error("%s: illegal syntax", coperator(operator)->name);
  /* check syntax of argument list to save time in apply */
  list = car(operands);
  while(list != obj_empty && TYPE(list) != TYPE_SYMBOL) {
    unless(TYPE(list) == TYPE_PAIR &&
           TYPE(car(list)) == TYPE_SYMBOL)
      error("%s: illegal argument list", coperator(operator)->name);
    list = cdr(list);
  }
  return make_operator("anonymous function",
                       entry_interpret, car(operands),
                       make_pair(obj_begin, cdr(operands)),
                       env, op_env);
}


/* entry_begin -- sequencing
 *
 * (begin <expression1> <expression2> ...)
 * See R4RS 4.2.3.
 */

static obj_t entry_begin(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  return eval_body(env, op_env, operator, operands);
}


/* BUILT-IN FUNCTIONS */


/* (not <obj>)
 * Not returns #t if obj is false, and return #f otherwise.
 * See R4RS 6.1.
 */
static obj_t entry_not(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_bool(arg == obj_false);
}


/* (boolean? <obj>)
 * Boolean? return #t if obj is either #t or #f, and #f otherwise.
 * See R4RS 6.1.
 */
static obj_t entry_booleanp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_bool(arg == obj_true || arg == obj_false);
}


/* (eqv? <obj1> <obj2>)
 * The eqv? procedure defines a useful equivalence relation on
 * objects.
 * See R4RS 6.2.
 */
static obj_t entry_eqvp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg1, arg2;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &arg1, &arg2);
  return make_bool(eqvp(arg1, arg2));
}


/* (eq? <obj1> <obj2>)
 * Eq? is similar to eqv? except that in some cases it is capable of
 * discerning distinctions finer than those detectable by eqv?.
 * See R4RS 6.2.
 */
static obj_t entry_eqp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg1, arg2;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &arg1, &arg2);
  return make_bool(arg1 == arg2);
}


static int equalp(obj_t obj1, obj_t obj2)
{
  size_t i;
  if(TYPE(obj1) != TYPE(obj2))
    return 0;
  switch(TYPE(obj1)) {
  case TYPE_PAIR:
    return equalp(car(obj1), car(obj2)) && equalp(cdr(obj1), cdr(obj2));
  case TYPE_VECTOR:
    if(cvector(obj1)->length != cvector(obj2)->length)
      return 0;
    for(i = 0; i < cvector(obj1)->length; ++i) {
      if(!equalp(vref(obj1, i), vref(obj2, i)))
        return 0;
    }
    return 1;
  case TYPE_STRING:
    return cstring(obj1)->length == cstring(obj2)->length
      && 0 == strcmp(cstring(obj1)->string, cstring(obj2)->string);
  default:
    return eqvp(obj1, obj2);
  }
}

/* (equal? <obj1> <obj2>)
 * Equal? recursively compares the contents of pairs, vectors, and
 * strings, applying eqv? on other objects such as numbers and
 * symbols. A rule of thumb is that objects are generally equal? if
 * they print the same. Equal? may fail to terminate if its arguments
 * are circular data structures.
 * See R4RS 6.2.
 */
static obj_t entry_equalp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg1, arg2;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &arg1, &arg2);
  return make_bool(equalp(arg1, arg2));
}


/* (pair? <obj>)
 * Pair? returns #t if obj is a pair, and otherwise returns #f.
 * See R4RS 6.3.
 */
static obj_t entry_pairp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_bool(TYPE(arg) == TYPE_PAIR);
}


/* (cons obj1 obj2)
 * Returns a newly allocated pair whose car is obj1 and whose cdr is
 * obj2. The pair is guaranteed to be different (in the sense of eqv?)
 * from every existing object.
 * See R4RS 6.3.
 */
static obj_t entry_cons(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t car, cdr;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &car, &cdr);
  return make_pair(car, cdr);
}


/* (car pair)
 * Returns the contents of the car field of pair. Note that it is an
 * error to take the car of the empty list.
 * See R4RS 6.3.
 */
static obj_t entry_car(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t pair;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &pair);
  unless(TYPE(pair) == TYPE_PAIR)
    error("%s: argument must be a pair", coperator(operator)->name);
  return car(pair);
}

/* (cdr pair)
 * Returns the contents of the cdr field of pair. Note that it is an
 * error to take the cdr of the empty list.
 * See R4RS 6.3.
 */
static obj_t entry_cdr(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t pair;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &pair);
  unless(TYPE(pair) == TYPE_PAIR)
    error("%s: argument must be a pair", coperator(operator)->name);
  return cdr(pair);
}


/* (set-car! pair obj)
 * Stores obj in the car field of pair. The value returned by set-car!
 * is unspecified.
 * See R4RS 6.3.
 */
static obj_t entry_setcar(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t pair, value;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &pair, &value);
  unless(TYPE(pair) == TYPE_PAIR)
    error("%s: first argument must be a pair", coperator(operator)->name);
  set_car(pair, value);
  return obj_undefined;
}


/* (set-cdr! pair obj)
 * Stores obj in the cdr field of pair. The value returned by set-cdr!
 * is unspecified.
 * See R4RS 6.3.
 */
static obj_t entry_setcdr(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t pair, value;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &pair, &value);
  unless(TYPE(pair) == TYPE_PAIR)
    error("%s: first argument must be a pair", coperator(operator)->name);
  set_cdr(pair, value);
  return obj_undefined;
}


/* (null? obj)
 * Returns #t if obj is the empty list, otherwise returns #f.
 * See R4RS 6.3.
 */
static obj_t entry_nullp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_bool(arg == obj_empty);
}


/* (list? obj)
 * Returns #t if obj is a list, otherwise returns #f. By definition,
 * all lists have finite length and are terminated by the empty list.
 * See R4RS 6.3.
 */
static obj_t entry_listp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  while(TYPE(arg) == TYPE_PAIR)
    arg = cdr(arg);
  return make_bool(arg == obj_empty);
}


/* (list obj ...)
 * Returns a newly allocated list of its arguments.
 * See R4RS 6.3.
 */
static obj_t entry_list(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t rest;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &rest, 0);
  return rest;
}


/* (length list)
 * Returns the length of list.
 * See R4RS 6.3.
 */
static obj_t entry_length(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  long length;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  length = 0;
  while(TYPE(arg) == TYPE_PAIR) {
    ++length;
    arg = cdr(arg);
  }
  if(arg != obj_empty)
    error("%s: applied to non-list", coperator(operator)->name);
  return make_integer(length);
}


/* (append list ...)
 * Returns a list consisting of the elements of the first list
 * followed by the elements of the other lists.
 * See R4RS 6.3.
 */
static obj_t entry_append(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg1, arg2, result, pair, end;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &arg1, &arg2);
  result = obj_empty;
  end = NULL;                   /* suppress "uninitialized" warning in GCC */
  while(TYPE(arg1) == TYPE_PAIR) {
    pair = make_pair(car(arg1), obj_empty);
    if(result == obj_empty)
      result = pair;
    else
      set_cdr(end, pair);
    end = pair;
    arg1 = cdr(arg1);
  }
  if(arg1 != obj_empty)
    error("%s: applied to non-list", coperator(operator)->name);
  if(result == obj_empty)
    return arg2;
  set_cdr(end, arg2);
  return result;
}


/* (integer? obj)
 * These numerical type predicates can be applied to any kind of
 * argument, including non-numbers. They return #t if the object is of
 * the named type, and otherwise they return #f.
 * See R4RS 6.5.5.
 */
static obj_t entry_integerp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_bool(TYPE(arg) == TYPE_INTEGER);
}


/* (zero? z)
 * (positive? x)
 * (negative? x)
 * These numerical predicates test a number for a particular property,
 * returning #t or #f.
 * See R4RS 6.5.5.
 */
static obj_t entry_zerop(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  unless(TYPE(arg) == TYPE_INTEGER)
    error("%s: argument must be an integer", coperator(operator)->name);
  return make_bool(cinteger(arg)->integer == 0);
}


static obj_t entry_positivep(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  unless(TYPE(arg) == TYPE_INTEGER)
    error("%s: argument must be an integer", coperator(operator)->name);
  return make_bool(cinteger(arg)->integer > 0);
}


static obj_t entry_negativep(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  unless(TYPE(arg) == TYPE_INTEGER)
    error("%s: argument must be an integer", coperator(operator)->name);
  return make_bool(cinteger(arg)->integer < 0);
}


/* (symbol? obj)
 * Returns #t if obj is a symbol, otherwise returns #f.
 * See R4RS 6.4.
 */
static obj_t entry_symbolp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_bool(TYPE(arg) == TYPE_SYMBOL);
}


/* (procedure? obj)
 * Returns #t if obj is a procedure, otherwise returns #f.
 * See R4RS 6.9.
 */
static obj_t entry_procedurep(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_bool(TYPE(arg) == TYPE_OPERATOR);
}


/* (apply proc args)
 * Proc must be a procedure and args must be a list. Calls proc with
 * the elements of args as the actual arguments.
 * See R4RS 6.9.
 */
static obj_t entry_apply(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t proc, args, qargs = obj_empty, end = NULL, quote;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &proc, &args);
  unless(TYPE(proc) == TYPE_OPERATOR)
    error("%s: first argument must be a procedure", coperator(operator)->name);
  quote = make_operator("quote", entry_quote, obj_empty, obj_empty, obj_empty, obj_empty);
  while(args != obj_empty) {
    obj_t a;
    assert(TYPE(args) == TYPE_PAIR);
    a = make_pair(make_pair(quote, make_pair(car(args), obj_empty)), obj_empty);
    if(end != NULL)
      set_cdr(end, a);
    else
      qargs = a;
    end = a;
    args = cdr(args);
  }
  return (*coperator(proc)->entry)(env, op_env, proc, qargs);
}


/* (+ z1 ...)
 * This procedure returns the sum of its arguments.
 * See R4RS 6.5.5.
 */
static obj_t entry_add(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t args;
  long result;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &args, 0);
  result = 0;
  while(TYPE(args) == TYPE_PAIR) {
    unless(TYPE(car(args)) == TYPE_INTEGER)
      error("%s: arguments must be integers", coperator(operator)->name);
    result += cinteger(car(args))->integer;
    args = cdr(args);
  }
  assert(args == obj_empty); /* eval_args_rest always returns a list */
  return make_integer(result);
}


/* (* z1 ...)
 * This procedure returns the product of its arguments.
 * See R4RS 6.5.5.
 */
static obj_t entry_multiply(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t args;
  long result;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &args, 0);
  result = 1;
  while(TYPE(args) == TYPE_PAIR) {
    unless(TYPE(car(args)) == TYPE_INTEGER)
      error("%s: arguments must be integers", coperator(operator)->name);
    result *= cinteger(car(args))->integer;
    args = cdr(args);
  }
  assert(args == obj_empty); /* eval_args_rest always returns a list */
  return make_integer(result);
}


/* (- z)
 * (- z1 z2)
 * (- z1 z2 ...)
 * With two or more arguments, this procedure returns the difference
 * of its arguments, associating to the left. With one argument,
 * however, it returns the additive inverse of its argument.
 * See R4RS 6.5.5.
 */
static obj_t entry_subtract(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg, args;
  long result;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &args, 1, &arg);
  unless(TYPE(arg) == TYPE_INTEGER)
    error("%s: first argument must be an integer", coperator(operator)->name);
  result = cinteger(arg)->integer;
  if(args == obj_empty)
    result = -result;
  else {
    while(TYPE(args) == TYPE_PAIR) {
      unless(TYPE(car(args)) == TYPE_INTEGER)
        error("%s: arguments must be integers", coperator(operator)->name);
      result -= cinteger(car(args))->integer;
      args = cdr(args);
    }
    assert(args == obj_empty); /* eval_args_rest always returns a list */
  }
  return make_integer(result);
}


/* (/ z)
 * (/ z1 z2)
 * (/ z1 z2 ...)
 * With two or more arguments, this procedure returns the quotient
 * of its arguments, associating to the left. With one argument,
 * however, it returns the multiplicative inverse of its argument.
 * See R4RS 6.5.5.
 */
static obj_t entry_divide(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg, args;
  long result;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &args, 1, &arg);
  unless(TYPE(arg) == TYPE_INTEGER)
    error("%s: first argument must be an integer", coperator(operator)->name);
  result = cinteger(arg)->integer;
  if(args == obj_empty) {
    if(result == 0)
      error("%s: reciprocal of zero", coperator(operator)->name);
    result = 1/result;  /* TODO: pretty meaningless for integers */
  } else {
    while(TYPE(args) == TYPE_PAIR) {
      unless(TYPE(car(args)) == TYPE_INTEGER)
        error("%s: arguments must be integers", coperator(operator)->name);
      if(cinteger(car(args))->integer == 0)
        error("%s: divide by zero", coperator(operator)->name);
      result /= cinteger(car(args))->integer;
      args = cdr(args);
    }
    assert(args == obj_empty); /* eval_args_rest always returns a list */
  }
  return make_integer(result);
}


/* (< x1 x2 x3 ...)
 * This procedure returns #t if its arguments are monotonically
 * increasing.
 * See R4RS 6.5.5.
 */
static obj_t entry_lessthan(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg, args;
  long last;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &args, 1, &arg);
  unless(TYPE(arg) == TYPE_INTEGER)
    error("%s: first argument must be an integer", coperator(operator)->name);
  last = cinteger(arg)->integer;
  while(TYPE(args) == TYPE_PAIR) {
    unless(TYPE(car(args)) == TYPE_INTEGER)
      error("%s: arguments must be integers", coperator(operator)->name);
    if (last >= cinteger(car(args))->integer)
      return obj_false;
    last = cinteger(car(args))->integer;
    args = cdr(args);
  }
  assert(args == obj_empty); /* eval_args_rest always returns a list */
  return obj_true;
}


/* (> x1 x2 x3 ...)
 * This procedure returns #t if its arguments are monotonically
 * decreasing.
 * See R4RS 6.5.5.
 */
static obj_t entry_greaterthan(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg, args;
  long last;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &args, 1, &arg);
  unless(TYPE(arg) == TYPE_INTEGER)
    error("%s: first argument must be an integer", coperator(operator)->name);
  last = cinteger(arg)->integer;
  while(TYPE(args) == TYPE_PAIR) {
    unless(TYPE(car(args)) == TYPE_INTEGER)
      error("%s: arguments must be integers", coperator(operator)->name);
    if (last <= cinteger(car(args))->integer)
      return obj_false;
    last = cinteger(car(args))->integer;
    args = cdr(args);
  }
  assert(args == obj_empty); /* eval_args_rest always returns a list */
  return obj_true;
}


/* (reverse list)
 * Returns a newly allocated list consisting of the elements of list
 * in reverse order.
 * See R4RS 6.3.
 */
static obj_t entry_reverse(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg, result;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  result = obj_empty;
  while(arg != obj_empty) {
    unless(TYPE(arg) == TYPE_PAIR)
      error("%s: argument must be a list", coperator(operator)->name);
    result = make_pair(car(arg), result);
    arg = cdr(arg);
  }
  return result;
}


/* (list-tail list k)
 * Returns the sublist of list obtained by omitting the first k
 * elements.
 */
static obj_t entry_list_tail(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg, k;
  int i;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &arg, &k);
  unless(TYPE(k) == TYPE_INTEGER)
    error("%s: second argument must be an integer", coperator(operator)->name);
  i = cinteger(k)->integer;
  unless(i >= 0)
    error("%s: second argument must be non-negative", coperator(operator)->name);
  while(i-- > 0) {
    unless(TYPE(arg) == TYPE_PAIR)
      error("%s: first argument must be a list", coperator(operator)->name);
    arg = cdr(arg);
  }
  return arg;
}


/* (list-ref list k)
 * Returns the kth element of list.
 * See R4RS 6.3.
 */
static obj_t entry_list_ref(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg, k, result;
  int i;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &arg, &k);
  unless(TYPE(k) == TYPE_INTEGER)
    error("%s: second argument must be an integer", coperator(operator)->name);
  i = cinteger(k)->integer;
  unless(i >= 0)
    error("%s: second argument must be non-negative", coperator(operator)->name);
  do {
    if(arg == obj_empty)
      error("%s: index %ld out of bounds", coperator(operator)->name, cinteger(k)->integer);
    unless(TYPE(arg) == TYPE_PAIR)
      error("%s: first argument must be a list", coperator(operator)->name);
    result = car(arg);
    arg = cdr(arg);
  } while(i-- > 0);
  return result;
}


static obj_t entry_environment(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  eval_args(coperator(operator)->name, env, op_env, operands, 0);
  return env;
}


/* (open-input-file filename)
 * Takes a string naming an existing file and returns an input port
 * capable of delivering characters from the file. If the file cannot
 * be opened, an error is signalled.
 * See R4RS 6.10.1
 */
static obj_t entry_open_input_file(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t filename;
  FILE *stream;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &filename);
  unless(TYPE(filename) == TYPE_STRING)
    error("%s: argument must be a string", coperator(operator)->name);
  stream = fopen(cstring(filename)->string, "r");
  if(stream == NULL)
    error("%s: cannot open input file", coperator(operator)->name);
  return make_port(filename, stream);
}


/* (open-output-file filename)
 * Takes a string naming an output file to be created and returns an
 * output port capable of writing characters to a new file by that
 * name. If the file cannot be opened, an error is signalled. If a
 * file with the given name already exists, the effect is unspecified.
 * See R4RS 6.10.1
 */
static obj_t entry_open_output_file(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t filename;
  FILE *stream;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &filename);
  unless(TYPE(filename) == TYPE_STRING)
    error("%s: argument must be a string", coperator(operator)->name);
  stream = fopen(cstring(filename)->string, "w");
  if(stream == NULL)
    error("%s: cannot open output file", coperator(operator)->name);
  return make_port(filename, stream);
}


/* (close-input-port port)
 * (close-output-port port)
 * Closes the file associated with port, rendering the port incapable
 * of delivering or accepting characters. These routines have no
 * effect if the file has already been closed. The value returned is
 * unspecified.
 * See R4RS 6.10.1.
 */
static obj_t entry_close_port(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t port;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &port);
  unless(TYPE(port) == TYPE_PORT)
    error("%s: argument must be a port", coperator(operator)->name);
  if(cport(port)->stream != NULL) {
    fclose(cport(port)->stream);
    cport(port)->stream = NULL;
  }
  return obj_undefined;
}


static FILE *rest_port_stream(obj_t operator, obj_t rest, const char *argnumber, FILE *default_stream) {
  FILE *stream = default_stream;
  unless(rest == obj_empty) {
    unless(cdr(rest) == obj_empty)
      error("%s: too many arguments", coperator(operator)->name);
    unless(TYPE(car(rest)) == TYPE_PORT)
      error("%s: %s argument must be a port", coperator(operator)->name, argnumber);
    stream = cport(car(rest))->stream;
    unless(stream)
      error("%s: port is closed", coperator(operator)->name);
  }
  return stream;
}


/* (write obj)
 * (write obj port)
 * Writes a written representation of obj to the given port. Strings
 * that appear in the written representation are enclosed in
 * doublequotes, and within those strings backslash and doublequote
 * characters are escaped by backslashes. Write returns an unspecified
 * value. The port argument may be omitted, in which case it defaults
 * to the value returned by current-output-port.
 * See R4RS 6.10.3.
 */
static obj_t entry_write(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg, rest;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &rest, 1, &arg);
  /* TODO: default to current-output-port */
  print(arg, -1, rest_port_stream(operator, rest, "second", stdout));
  return obj_undefined;
}


static obj_t entry_write_string(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg, rest;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &rest, 1, &arg);
  unless(TYPE(arg) == TYPE_STRING)
    error("%s: first argument must be a string", coperator(operator)->name);
  /* TODO: default to current-output-port */
  fputs(cstring(arg)->string, rest_port_stream(operator, rest, "second", stdout));
  return obj_undefined;
}


/* (newline)
 * (newline port)
 * Writes an end of line to port. Exactly how this is done differs
 * from one operating system to another. Returns an unspecified value.
 * The port argument may be omitted, in which case it defaults to the
 * value returned by current-output-port.
 */
static obj_t entry_newline(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t rest;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &rest, 0);
  /* TODO: default to current-output-port */
  putc('\n', rest_port_stream(operator, rest, "first", stdout));
  return obj_undefined;
}


/* (load filename)
 * Filename should be a string naming an existing file containing
 * Scheme source code. The load procedure reads expressions and
 * definitions from the file and evaluates them sequentially. It is
 * unspecified whether the results of the expressions are printed. The
 * load procedure does not affect the values returned by
 * current-input-port and current-output-port. Load returns an
 * unspecified value.
 * See R4RS 6.10.4.
 */
static obj_t entry_load(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t filename;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &filename);
  unless(TYPE(filename) == TYPE_STRING)
    error("%s: argument must be a string", coperator(operator)->name);
  return load(env, op_env, cstring(filename)->string);
}


/* (force promise)
 * Forces the value of promise. If no value has been computed for the
 * promise, then a value is computed and returned. The value of the
 * promise is cached (or "memoized") so that if it is forced a second
 * time, the previously computed value is returned.
 * See R4RS 6.9.
 *
 * TODO: This doesn't work if the promise refers to its own value.
 */
static obj_t entry_force(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t promise;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &promise);
  unless(TYPE(promise) == TYPE_PROMISE)
    error("%s: argument must be a promise", coperator(operator)->name);
  /* If the promise is unevaluated then apply the CDR. */
  if (!cpromise(promise)->fulfilledp) {
    obj_t closure = cpromise(promise)->fulfiller;
    assert(TYPE(closure) == TYPE_OPERATOR);
    assert(coperator(closure)->arguments == obj_empty);
    obj_t value = (*coperator(closure)->entry)(env, op_env, closure, obj_empty);
    gc_write_barrier(gc_ref_from_heap_object(promise), sizeof(promise_s),
                     gc_edge(&cpromise(promise)->fulfiller),
                     gc_ref_from_heap_object(value));
    cpromise(promise)->fulfiller = value;
    cpromise(promise)->fulfilledp = true;
  }
  return cpromise(promise)->fulfiller;
}


/* (char? obj)
 * Returns #t if obj is a character, otherwise returns #f.
 * See R4RS 6.6.
 */
static obj_t entry_charp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_bool(TYPE(arg) == TYPE_CHARACTER);
}


/* (char->integer char)
 * Given a character, char->integer returns its Unicode scalar value
 * as an exact integer object.
 * See R4RS 6.6.
 */
static obj_t entry_char_to_integer(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  unless(TYPE(arg) == TYPE_CHARACTER)
    error("%s: first argument must be a character", coperator(operator)->name);
  return make_integer(ccharacter(arg)->c);
}


/* (integer->char sv)
 * For a Unicode scalar value sv, integer->char returns its associated
 * character.
 * See R4RS 6.6.
 */
static obj_t entry_integer_to_char(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  unless(TYPE(arg) == TYPE_INTEGER)
    error("%s: first argument must be an integer", coperator(operator)->name);
  unless(0 <= cinteger(arg)->integer)
    error("%s: first argument is out of range", coperator(operator)->name);
  return make_character(cinteger(arg)->integer);
}


/* (vector? obj)
 * Returns #t if obj is a vector, otherwise returns #f.
 * See R4RS 6.8.
 */
static obj_t entry_vectorp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_bool(TYPE(arg) == TYPE_VECTOR);
}


/* (make-vector k)
 * (make-vector k fill)
 * Returns a newly allocated vector of k elements. If a second
 * argument is given, then each element is initialized to fill.
 * Otherwise the initial contents of each element is unspecified.
 * See R4RS 6.8.
 */
static obj_t entry_make_vector(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t length, rest, fill = obj_undefined;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &rest, 1, &length);
  unless(TYPE(length) == TYPE_INTEGER)
    error("%s: first argument must be an integer", coperator(operator)->name);
  unless(rest == obj_empty) {
    unless(cdr(rest) == obj_empty)
      error("%s: too many arguments", coperator(operator)->name);
    fill = car(rest);
  }
  return make_vector(cinteger(length)->integer, fill);
}


/* (vector obj ...)
 * Returns a newly allocated vector whose elements contain the given
 * arguments. Analogous to list.
 * See R4RS 6.8.
 */
static obj_t entry_vector(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t rest, vector;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &rest, 0);
  vector = list_to_vector(rest);
  assert(vector != obj_error);
  return vector;
}


/* (vector-length vector)
 * Returns the number of elements in vector.
 * See R4RS 6.8.
 */
static obj_t entry_vector_length(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t vector;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &vector);
  unless(TYPE(vector) == TYPE_VECTOR)
    error("%s: argument must be a vector", coperator(operator)->name);
  return make_integer(cvector(vector)->length);
}


/* (vector-ref vector k)
 * k must be a valid index of vector. Vector-ref returns the contents
 * of element k of vector.
 * See R4RS 6.8.
 */
static obj_t entry_vector_ref(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t vector, index;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &vector, &index);
  unless(TYPE(vector) == TYPE_VECTOR)
    error("%s: first argument must be a vector", coperator(operator)->name);
  unless(TYPE(index) == TYPE_INTEGER)
    error("%s: second argument must be an integer", coperator(operator)->name);
  unless(0 <= cinteger(index)->integer && cinteger(index)->integer < cvector(vector)->length)
    error("%s: index %ld out of bounds of vector length %ld",
          coperator(operator)->name, cinteger(index)->integer, cvector(vector)->length);
  return vref(vector, cinteger(index)->integer);
}


/* (vector-set! vector k obj
 * k must be a valid index of vector. Vector-set! stores obj in
 * element k of vector. The value returned by vector-set! is
 * unspecified.
 * See R4RS 6.8.
 */
static obj_t entry_vector_set(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t vector, index, obj;
  eval_args(coperator(operator)->name, env, op_env, operands, 3, &vector, &index, &obj);
  unless(TYPE(vector) == TYPE_VECTOR)
    error("%s: first argument must be a vector", coperator(operator)->name);
  unless(TYPE(index) == TYPE_INTEGER)
    error("%s: second argument must be an integer", coperator(operator)->name);
  unless(0 <= cinteger(index)->integer && cinteger(index)->integer < cvector(vector)->length)
    error("%s: index %ld out of bounds of vector length %ld",
          coperator(operator)->name, cinteger(index)->integer, cvector(vector)->length);
  vset(vector, cinteger(index)->integer, obj);
  return obj_undefined;
}


/* (vector->list vector)
 * Vector->list returns a newly allocated list of the objects
 * contained in the elements of vector.
 * See R4RS 6.8.
 */
static obj_t entry_vector_to_list(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t vector, list;
  size_t i;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &vector);
  unless(TYPE(vector) == TYPE_VECTOR)
    error("%s: argument must be a vector", coperator(operator)->name);
  list = obj_empty;
  i = cvector(vector)->length;
  while(i > 0) {
    --i;
    list = make_pair(vref(vector, i), list);
  }
  return list;
}


/* (list->vector list)
 * List->vector returns a newly created vector initialized to the
 * elements of the list list.
 * See R4RS 6.8.
 */
static obj_t entry_list_to_vector(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t list, vector;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &list);
  vector = list_to_vector(list);
  if(vector == obj_error)
    error("%s: argument must be a list", coperator(operator)->name);
  return vector;
}


/* (vector-fill! vector fill)
 * Stores fill in every element of vector. The value returned by
 * vector-fill! is unspecified.
 * See R4RS 6.8.
 */
static obj_t entry_vector_fill(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t vector, obj;
  size_t i;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &vector, &obj);
  unless(TYPE(vector) == TYPE_VECTOR)
    error("%s: first argument must be a vector", coperator(operator)->name);
  for(i = 0; i < cvector(vector)->length; ++i)
    vset(vector, i, obj);
  return obj_undefined;
}


static obj_t entry_eval(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t exp;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &exp);
  return eval(env, op_env, exp);
}


static obj_t entry_error(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t msg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &msg);
  unless(TYPE(msg) == TYPE_STRING)
    error("%s: argument must be a string", coperator(operator)->name);
  error(cstring(msg)->string);
  return obj_undefined;
}


/* (symbol->string symbol)
 * Returns the name of symbol as a string.
 * See R4RS 6.4.
 */
static obj_t entry_symbol_to_string(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t symbol;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &symbol);
  unless(TYPE(symbol) == TYPE_SYMBOL)
    error("%s: argument must be a symbol", coperator(operator)->name);
  return make_string(csymbol(symbol)->length, csymbol(symbol)->string);
}


/* (string->symbol symbol)
 * Returns the symbol whose name is string.
 * See R4RS 6.4.
 */
static obj_t entry_string_to_symbol(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t string;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &string);
  unless(TYPE(string) == TYPE_STRING)
    error("%s: argument must be a string", coperator(operator)->name);
  /* TODO: Should pass length to intern to avoid problems with NUL termination. */
  return intern(cstring(string)->string);
}


/* (string? obj)
 * Returns #t if obj is a string, otherwise returns #f.
 * See R4RS 6.7.
 */
static obj_t entry_stringp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_bool(TYPE(arg) == TYPE_STRING);
}


/* (make-string k)
 * (make-string k char)
 * Make-string returns a newly allocated string of length k. If char
 * is given, then all elements of the string are initialized to char,
 * otherwise the contents of the string are unspecified.
 * See R4RS 6.7.
 */
static obj_t entry_make_string(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t obj, k, args;
  char c = '\0';
  int i;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &args, 1, &k);
  unless(TYPE(k) == TYPE_INTEGER)
    error("%s: first argument must be an integer", coperator(operator)->name);
  unless(cinteger(k)->integer >= 0)
    error("%s: first argument must be non-negative", coperator(operator)->name);
  if (TYPE(args) == TYPE_PAIR) {
    unless(TYPE(car(args)) == TYPE_CHARACTER)
      error("%s: second argument must be a character", coperator(operator)->name);
    unless(cdr(args) == obj_empty)
      error("%s: too many arguments", coperator(operator)->name);
    c = ccharacter(car(args))->c;
  }
  obj = make_string(cinteger(k)->integer, NULL);
  for (i = 0; i < cinteger(k)->integer; ++i) {
    cstring(obj)->string[i] = c;
  }
  return obj;
}


/* (string char ...)
 * Returns a newly allocated string composed of the arguments.
 * See R4RS 6.7.
 */
static obj_t entry_string(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t args, obj, o;
  size_t length;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &args, 0);
  o = args;
  length = 0;
  while(TYPE(o) == TYPE_PAIR) {
    unless(TYPE(car(o)) == TYPE_CHARACTER)
      error("%s: arguments must be strings", coperator(operator)->name);
    ++ length;
    o = cdr(o);
  }
  obj = make_string(length, NULL);
  o = args;
  length = 0;
  while(TYPE(o) == TYPE_PAIR) {
    assert(TYPE(car(o)) == TYPE_CHARACTER);
    cstring(obj)->string[length] = ccharacter(car(o))->c;
    ++ length;
    o = cdr(o);
  }
  assert(length == cstring(obj)->length);
  return obj;
}


/* (string-length string)
 * Returns the number of characters in the given string.
 * See R4RS 6.7.
 */
static obj_t entry_string_length(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  unless(TYPE(arg) == TYPE_STRING)
    error("%s: argument must be a string", coperator(operator)->name);
  return make_integer(cstring(arg)->length);
}


/* (string-ref string k)
 * k must be a valid index of string. String-ref returns character k
 * of string using zero-origin indexing.
 * See R4RS 6.7.
 */
static obj_t entry_string_ref(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg, k;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &arg, &k);
  unless(TYPE(arg) == TYPE_STRING)
    error("%s: first argument must be a string", coperator(operator)->name);
  unless(TYPE(k) == TYPE_INTEGER)
    error("%s: second argument must be an integer", coperator(operator)->name);
  unless(0 <= cinteger(k)->integer && cinteger(k)->integer < cstring(arg)->length)
    error("%s: second argument is out of range", coperator(operator)->name);
  return make_character(cstring(arg)->string[cinteger(k)->integer]);
}

/* (string=? string1 string2)
 * Returns #t if the two strings are the same length and contain the
 * same characters in the same positions, otherwise returns #f.
 * See R4RS 6.7.
 */
static obj_t entry_string_equalp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg1, arg2;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &arg1, &arg2);
  unless(TYPE(arg1) == TYPE_STRING)
    error("%s: first argument must be a string", coperator(operator)->name);
  unless(TYPE(arg2) == TYPE_STRING)
    error("%s: second argument must be a string", coperator(operator)->name);
  return make_bool(string_equalp(arg1, arg2));
}


/* (substring string start end)
 * String must be a string, and start and end must be exact integers
 * satisfying
 *     0 <= start <= end <= (string-length string).
 * Substring returns a newly allocated string formed from the
 * characters of string beginning with index start (inclusive) and
 * ending with index end (exclusive).
 * See R4RS 6.7.
 */
static obj_t entry_substring(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t obj, arg, start, end;
  size_t length;
  eval_args(coperator(operator)->name, env, op_env, operands, 3, &arg, &start, &end);
  unless(TYPE(arg) == TYPE_STRING)
    error("%s: first argument must be a string", coperator(operator)->name);
  unless(TYPE(start) == TYPE_INTEGER)
    error("%s: second argument must be an integer", coperator(operator)->name);
  unless(TYPE(end) == TYPE_INTEGER)
    error("%s: third argument must be an integer", coperator(operator)->name);
  unless(0 <= cinteger(start)->integer
         && cinteger(start)->integer <= cinteger(end)->integer
         && cinteger(end)->integer <= cstring(arg)->length)
    error("%s: arguments out of range", coperator(operator)->name);
  length = cinteger(end)->integer - cinteger(start)->integer;
  obj = make_string(length, NULL);
  strncpy(cstring(obj)->string, &cstring(arg)->string[cinteger(start)->integer], length);
  return obj;
}

/* (string-append string ...)
 * Returns a newly allocated string whose characters form the
 * concatenation of the given strings.
 * See R4RS 6.7.
 */
static obj_t entry_string_append(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t args, obj, o;
  size_t length;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &args, 0);
  o = args;
  length = 0;
  while(TYPE(o) == TYPE_PAIR) {
    unless(TYPE(car(o)) == TYPE_STRING)
      error("%s: arguments must be strings", coperator(operator)->name);
    length += cstring(car(o))->length;
    o = cdr(o);
  }
  obj = make_string(length, NULL);
  o = args;
  length = 0;
  while(TYPE(o) == TYPE_PAIR) {
    string_s *s = cstring(car(o));
    assert(TYPE(car(o)) == TYPE_STRING);
    memcpy(cstring(obj)->string + length, s->string, s->length + 1);
    length += s->length;
    o = cdr(o);
  }
  assert(length == cstring(obj)->length);
  return obj;
}


/* (string->list string)
 * The string->list procedure returns a newly allocated list of the
 * characters that make up the given string.
 * See R4RS 6.7.
 */
static obj_t entry_string_to_list(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t string, list;
  size_t i;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &string);
  unless(TYPE(string) == TYPE_STRING)
    error("%s: argument must be a string", coperator(operator)->name);
  list = obj_empty;
  i = cstring(string)->length;
  while(i > 0) {
    --i;
    list = make_pair(make_character(cstring(string)->string[i]), list);
  }
  return list;
}


/* (list->string list)
 * List must be a list of characters. The list->string procedure
 * returns a newly allocated string formed from the characters in
 * list.
 * See R4RS 6.7.
 */
static obj_t entry_list_to_string(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t l, list, string;
  size_t i, length = 0;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &list);
  l = list;
  while(l != obj_empty) {
    unless(TYPE(l) == TYPE_PAIR)
      error("%s: argument must be a list", coperator(operator)->name);
    unless(TYPE(car(l)) == TYPE_CHARACTER)
      error("%s: argument must be a list of characters", coperator(operator)->name);
    ++ length;
    l = cdr(l);
  }
  string = make_string(length, NULL);
  l = list;
  for(i = 0; i < length; ++i) {
    assert(TYPE(l) == TYPE_PAIR);
    assert(TYPE(car(l)) == TYPE_CHARACTER);
    cstring(string)->string[i] = ccharacter(car(l))->c;
    l = cdr(l);
  }
  return string;
}


/* (string-copy string)
 * Returns a newly allocated copy of the given string.
 * See R4RS 6.7.
 */
static obj_t entry_string_copy(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  unless(TYPE(arg) == TYPE_STRING)
    error("%s: argument must be a string", coperator(operator)->name);
  return make_string(cstring(arg)->length, cstring(arg)->string);
}


/* (string-hash string)
 * Returns an integer hash value for string, based on its current
 * contents. This hash function is suitable for use with string=? as
 * an equivalence function.
 * See R6RS Library 13.2.
 */
static obj_t entry_string_hash(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  unless(TYPE(arg) == TYPE_STRING)
    error("%s: argument must be a string", coperator(operator)->name);
  return make_integer(string_hash(arg));
}


static obj_t entry_eq_hash(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_integer(eq_hash(arg));
}


static obj_t entry_eqv_hash(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_integer(eqv_hash(arg));
}


static obj_t make_hashtable(obj_t operator, obj_t rest, hash_t hashf, cmp_t cmpf)
{
  size_t length = 0;
  if (rest == obj_empty)
    length = 8;
  else unless(cdr(rest) == obj_empty)
    error("%s: too many arguments", coperator(operator)->name);
  else {
    obj_t arg = car(rest);
    unless(TYPE(arg) == TYPE_INTEGER)
      error("%s: first argument must be an integer", coperator(operator)->name);
    unless(cinteger(arg)->integer > 0)
      error("%s: first argument must be positive", coperator(operator)->name);
    length = cinteger(arg)->integer;
  }
  return make_table(length, hashf, cmpf);
}


/* (make-eq-hashtable)
 * (make-eq-hashtable k)
 * Returns a newly allocated mutable hashtable that accepts arbitrary
 * objects as keys, and compares those keys with eq?. If an argument
 * is given, the initial capacity of the hashtable is set to
 * approximately k elements.
 * See R6RS Library 13.1.
 */
static obj_t entry_make_eq_hashtable(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t rest;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &rest, 0);
  return make_hashtable(operator, rest, eq_hash, eqp);
}


/* (make-eqv-hashtable)
 * (make-eqv-hashtable k)
 * Returns a newly allocated mutable hashtable that accepts arbitrary
 * objects as keys, and compares those keys with eqv?. If an argument
 * is given, the initial capacity of the hashtable is set to
 * approximately k elements.
 * See R6RS Library 13.1.
 */
static obj_t entry_make_eqv_hashtable(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t rest;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &rest, 0);
  return make_hashtable(operator, rest, eqv_hash, eqvp);
}


/* (make-hashtable hash-function equiv)
 * (make-hashtable hash-function equiv k)
 * Hash-function and equiv must be procedures. Hash-function should
 * accept a key as an argument and should return a non-negative exact
 * integer object. Equiv should accept two keys as arguments and
 * return a single value. Neither procedure should mutate the
 * hashtable returned by make-hashtable. The make-hashtable procedure
 * returns a newly allocated mutable hashtable using hash-function as
 * the hash function and equiv as the equivalence function used to
 * compare keys. If a third argument is given, the initial capacity of
 * the hashtable is set to approximately k elements.
 * See R6RS Library 13.1.
 */
static obj_t entry_make_hashtable(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t hashf, cmpf, rest;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &rest, 2, &hashf, &cmpf);
  unless(TYPE(hashf) == TYPE_OPERATOR)
    error("%s: first argument must be a procedure", coperator(operator)->name);
  unless(TYPE(cmpf) == TYPE_OPERATOR)
    error("%s: first argument must be a procedure", coperator(operator)->name);
  if (coperator(hashf)->entry == entry_eq_hash
      && coperator(cmpf)->entry == entry_eqp)
    return make_hashtable(operator, rest, eq_hash, eqp);
  if (coperator(hashf)->entry == entry_eqv_hash
      && coperator(cmpf)->entry == entry_eqvp)
    return make_hashtable(operator, rest, eqv_hash, eqvp);
  if (coperator(hashf)->entry == entry_string_hash
      && coperator(cmpf)->entry == entry_string_equalp)
    return make_hashtable(operator, rest, string_hash, string_equalp);
  error("%s: arguments not supported", coperator(operator)->name);
  return obj_undefined;
}


/* (hashtable? hashtable)
 * Returns #t if hashtable is a hashtable, #f otherwise.
 * See R6RS Library 13.2.
 */
static obj_t entry_hashtablep(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  return make_bool(TYPE(arg) == TYPE_TABLE);
}

/* (hashtable-size hashtable)
 * Returns the number of keys contained in hashtable as an exact
 * integer object.
 * See R6RS Library 13.2.
 */
static obj_t entry_hashtable_size(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t arg;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &arg);
  unless(TYPE(arg) == TYPE_TABLE)
    error("%s: argument must be a hash table", coperator(operator)->name);
  return make_integer(table_size(arg));
}


/* (hashtable-ref hashtable key default)
 * Returns the value in hashtable associated with key. If hashtable
 * does not contain an association for key, default is returned.
 * See R6RS Library 13.2.
 */
static obj_t entry_hashtable_ref(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t tbl, key, def, value;
  eval_args(coperator(operator)->name, env, op_env, operands, 3, &tbl, &key, &def);
  unless(TYPE(tbl) == TYPE_TABLE)
    error("%s: first argument must be a hash table", coperator(operator)->name);
  value = table_ref(tbl, key);
  if (value) return value;
  return def;
}


/* (hashtable-set! hashtable key value)
 * Changes hashtable to associate key with obj, adding a new
 * association or replacing any existing association for key, and
 * returns unspecified values.
 * See R6RS Library 13.2.
 */
static obj_t entry_hashtable_set(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t tbl, key, value;
  eval_args(coperator(operator)->name, env, op_env, operands, 3, &tbl, &key, &value);
  unless(TYPE(tbl) == TYPE_TABLE)
    error("%s: first argument must be a hash table", coperator(operator)->name);
  table_set(tbl, key, value);
  return obj_undefined;
}


/* (hashtable-delete! hashtable key)
 * Removes any association for key within hashtable and returns
 * unspecified values.
 * See R6RS Library 13.2.
 */
static obj_t entry_hashtable_delete(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t tbl, key;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &tbl, &key);
  unless(TYPE(tbl) == TYPE_TABLE)
    error("%s: first argument must be a hash table", coperator(operator)->name);
  table_delete(tbl, key);
  return obj_undefined;
}


/* (hashtable-contains? hashtable key)
 * Returns #t if hashtable contains an association for key, #f otherwise.
 * See R6RS Library 13.2.
 */
static obj_t entry_hashtable_containsp(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  obj_t tbl, key;
  eval_args(coperator(operator)->name, env, op_env, operands, 2, &tbl, &key);
  unless(TYPE(tbl) == TYPE_TABLE)
    error("%s: first argument must be a hash table", coperator(operator)->name);
  return make_bool(table_ref(tbl, key) != NULL);
}


/* (hashtable-keys hashtable)
 * Returns a vector of all keys in hashtable. The order of the vector
 * is unspecified.
 * See R6RS Library 13.2.
 */
static obj_t entry_hashtable_keys(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  size_t i, j = 0;
  obj_t tbl, vector;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &tbl);
  unless(TYPE(tbl) == TYPE_TABLE)
    error("%s: argument must be a hash table", coperator(operator)->name);
  vector = make_vector(table_size(tbl), obj_undefined);
  for(i = 0; i < cbuckets(ctable(tbl)->buckets)->length; ++i) {
    struct bucket_s *b = &cbuckets(ctable(tbl)->buckets)->bucket[i];
    if(b->key != NULL && b->key != obj_deleted)
      vset(vector, j++, b->value);
  }
  assert(j == cvector(vector)->length);
  return vector;
}

/* Weak pointers */

static obj_t entry_make_weak_box(obj_t env, obj_t op_env, obj_t operator, obj_t operands) {
  obj_t obj;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &obj);
  return make_weak_box(obj);
}

static obj_t entry_weak_box_value(obj_t env, obj_t op_env, obj_t operator, obj_t operands) {
  obj_t box, rest, defact = obj_false;
  eval_args_rest(coperator(operator)->name, env, op_env, operands, &rest, 1, &box);
  unless(TYPE(box) == TYPE_WEAK_BOX)
    error("%s: first argument must be a weak box", coperator(operator)->name);
  unless(rest == obj_empty) {
    unless(cdr(rest) == obj_empty)
      error("%s: too many arguments", coperator(operator)->name);
    defact = car(rest);
  }
  return weak_box_value(box, defact);
}

static obj_t entry_weak_box_p(obj_t env, obj_t op_env, obj_t operator, obj_t operands) {
  obj_t box;
  eval_args(coperator(operator)->name, env, op_env, operands, 1, &box);
  return TYPE(box) == TYPE_WEAK_BOX ? obj_true : obj_false;
}

/* (gc)
 * Run a full garbage collection now.
 */
static obj_t entry_gc(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  eval_args(coperator(operator)->name, env, op_env, operands, 0);
  gc_collect(mutator, GC_COLLECTION_ANY);
  return obj_undefined;
}

// Print statistics since the last GC.
static obj_t entry_room(obj_t env, obj_t op_env, obj_t operator, obj_t operands)
{
  eval_args(coperator(operator)->name, env, op_env, operands, 0);
  gc_basic_stats_finish(&gcstats);
  gc_basic_stats_print(&gcstats, stdout);
  return obj_undefined;
}


/* INITIALIZATION */


/* special table */

static struct {char *name; obj_t *varp;} sptab[] = {
  {"()", &obj_empty},
  {"#[eof]", &obj_eof},
  {"#[error]", &obj_error},
  {"#t", &obj_true},
  {"#f", &obj_false},
  {"#[undefined]", &obj_undefined},
  {"#[tail]", &obj_tail},
  {"#[deleted]", &obj_deleted}
};


/* initial symbol table */

static struct {char *name; obj_t *varp;} isymtab[] = {
  {"quote", &obj_quote},
  {"lambda", &obj_lambda},
  {"begin", &obj_begin},
  {"else", &obj_else},
  {"quasiquote", &obj_quasiquote},
  {"unquote", &obj_unquote},
  {"unquote-splicing", &obj_unquote_splic}
};


/* operator table */

static struct {char *name; entry_t entry;} optab[] = {
  {"quote", entry_quote},
  {"define", entry_define},
  {"set!", entry_set},
  {"lambda", entry_lambda},
  {"begin", entry_begin},
  {"cond", entry_cond},
  {"if", entry_if},
  {"and", entry_and},
  {"or", entry_or},
  {"let", entry_let},
  {"let*", entry_let_star},
  {"letrec", entry_letrec},
  {"do", entry_do},
  {"delay", entry_delay},
  {"quasiquote", entry_quasiquote}
};


/* function table */

static struct {char *name; entry_t entry;} funtab[] = {
  {"not", entry_not},
  {"boolean?", entry_booleanp},
  {"eqv?", entry_eqvp},
  {"eq?", entry_eqp},
  {"equal?", entry_equalp},
  {"pair?", entry_pairp},
  {"cons", entry_cons},
  {"car", entry_car},
  {"cdr", entry_cdr},
  {"set-car!", entry_setcar},
  {"set-cdr!", entry_setcdr},
  {"null?", entry_nullp},
  {"list?", entry_listp},
  {"list", entry_list},
  {"length", entry_length},
  {"append", entry_append},
  {"integer?", entry_integerp},
  {"zero?", entry_zerop},
  {"positive?", entry_positivep},
  {"negative?", entry_negativep},
  {"symbol?", entry_symbolp},
  {"procedure?", entry_procedurep},
  {"apply", entry_apply},
  {"+", entry_add},
  {"-", entry_subtract},
  {"*", entry_multiply},
  {"/", entry_divide},
  {"<", entry_lessthan},
  {">", entry_greaterthan},
  {"reverse", entry_reverse},
  {"list-tail", entry_list_tail},
  {"list-ref", entry_list_ref},
  {"the-environment", entry_environment},
  {"open-input-file", entry_open_input_file},
  {"open-output-file", entry_open_output_file},
  {"close-input-port", entry_close_port},
  {"close-output-port", entry_close_port},
  {"write", entry_write},
  {"write-string", entry_write_string},
  {"newline", entry_newline},
  {"load", entry_load},
  {"force", entry_force},
  {"char?", entry_charp},
  {"char->integer", entry_char_to_integer},
  {"integer->char", entry_integer_to_char},
  {"vector?", entry_vectorp},
  {"make-vector", entry_make_vector},
  {"vector", entry_vector},
  {"vector-length", entry_vector_length},
  {"vector-ref", entry_vector_ref},
  {"vector-set!", entry_vector_set},
  {"vector->list", entry_vector_to_list},
  {"list->vector", entry_list_to_vector},
  {"vector-fill!", entry_vector_fill},
  {"eval", entry_eval},
  {"error", entry_error},
  {"symbol->string", entry_symbol_to_string},
  {"string->symbol", entry_string_to_symbol},
  {"string?", entry_stringp},
  {"make-string", entry_make_string},
  {"string", entry_string},
  {"string-length", entry_string_length},
  {"string-ref", entry_string_ref},
  {"string=?", entry_string_equalp},
  {"substring", entry_substring},
  {"string-append", entry_string_append},
  {"string->list", entry_string_to_list},
  {"list->string", entry_list_to_string},
  {"string-copy", entry_string_copy},
  {"make-eq-hashtable", entry_make_eq_hashtable},
  {"make-eqv-hashtable", entry_make_eqv_hashtable},
  {"make-hashtable", entry_make_hashtable},
  {"hashtable?", entry_hashtablep},
  {"hashtable-size", entry_hashtable_size},
  {"hashtable-ref", entry_hashtable_ref},
  {"hashtable-set!", entry_hashtable_set},
  {"hashtable-delete!", entry_hashtable_delete},
  {"hashtable-contains?", entry_hashtable_containsp},
  {"hashtable-keys", entry_hashtable_keys},
  {"string-hash", entry_string_hash},
  {"eq-hash", entry_eq_hash},
  {"eqv-hash", entry_eqv_hash},
  {"gc", entry_gc},
  {"room", entry_room},
  {"make-weak-box", entry_make_weak_box},
  {"weak-box-value", entry_weak_box_value},
  {"weak-box?", entry_weak_box_p},
};

/* more GC interactions */

struct handle* add_heap_root(void **ptrs, size_t nptrs) {
  struct handle *old_roots = global_roots.roots;
  struct handle *n = malloc(sizeof(struct handle));
  n->nptrs = nptrs; n->v = ptrs;
  n->next = old_roots;
  global_roots.roots = n;
  return n;
}
// return true if the root was actually present
// dunno that anything needs to know but w/e
// anyway this is a basic linked list delete.
bool remove_heap_root(struct handle *old) {
  struct handle *cur = global_roots.roots;
  if (cur == old) {
    global_roots.roots = old->next;
    free(old);
    return true;
  } else {
    while (cur) {
      if (cur->next == old) {
        cur->next = old->next;
        free(old);
        return true;
      } else cur = cur->next;
    }
    return false;
  }
}

/* MAIN PROGRAM */


int main(int argc, char *argv[])
{
  // GC initialization
  char* optstr = getenv("GC_OPTIONS");
  struct gc_options *options = gc_allocate_options();
  gc_options_set_int(options, GC_OPTION_HEAP_SIZE_POLICY, GC_HEAP_SIZE_FIXED);
  if (optstr && !gc_options_parse_and_set_many(options, optstr))
    error("Failed to set GC options: '%s'\n", optstr);

  struct gc_heap *heap;
  if (!gc_init(options, NULL, &heap, &mutator, GC_BASIC_STATS, &gcstats))
    error("Failed to initialize GC");

  gc_heap_set_roots(heap, &global_roots);
  
  // Scheme
  FILE *input = stdin;
  size_t i;
  volatile obj_t env, op_env, obj;
  jmp_buf jb;

  symtab_size = 16;
  symtab = malloc(sizeof(obj_t) * symtab_size);
  if(symtab == NULL) error("out of memory");
  for(i = 0; i < symtab_size; ++i)
    symtab[i] = NULL;

  // Register symtab root
  symtab_root = add_heap_root((void**)symtab, symtab_size);

  error_handler = &jb;

  if(!setjmp(*error_handler)) {
    for(i = 0; i < LENGTH(sptab); ++i)
      *sptab[i].varp = make_special(sptab[i].name);
    
    for(i = 0; i < LENGTH(isymtab); ++i)
      *isymtab[i].varp = intern(isymtab[i].name);
    env = make_pair(obj_empty, obj_empty);
    op_env = make_pair(obj_empty, obj_empty);
    for(i = 0; i < LENGTH(funtab); ++i)
      define(env,
             intern(funtab[i].name),
             make_operator(funtab[i].name, funtab[i].entry,
                           obj_empty, obj_empty, env, op_env));
    for(i = 0; i < LENGTH(optab); ++i)
      define(op_env,
             intern(optab[i].name),
             make_operator(optab[i].name, optab[i].entry,
                           obj_empty, obj_empty, env, op_env));
  } else {
    fflush(stdout);
    fprintf(stderr,
            "Fatal error during initialization: %s\n",
            error_message);
    abort();
  }

  if(argc >= 2) {
    /* Non-interactive file execution */
    if(setjmp(*error_handler) != 0) {
      fflush(stdout);
      fprintf(stderr, "%s\n", error_message);
      return EXIT_FAILURE;
    }
    for (i = 1; i < argc; ++i)
      load(env, op_env, argv[i]);
    return EXIT_SUCCESS;
  } else {
    /* Interactive read-eval-print loop */
    puts("Scheme Test Harness");
    for(;;) {
      if(setjmp(*error_handler) != 0) {
        fflush(stdout);
        fprintf(stderr, "%s\n", error_message);
        fflush(stderr);
      }
      printf("> ");
      fflush(stdout);
      obj = read_(input);
      if(obj == obj_eof) break;
      obj = eval(env, op_env, obj);
      if(obj != obj_undefined) {
        print(obj, 6, stdout);
        putc('\n', stdout);
      }
    }
    puts("Bye.");
    return EXIT_SUCCESS;
  }
}


/* C. COPYRIGHT AND LICENSE
 *
 * Copyright (C) 2001-2020 Ravenbrook Limited <https://www.ravenbrook.com/>.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
