#pragma once

#include <stdatomic.h>
#include "gc-embedder-api.h"
#include "roots.h"
#include "object.h"

#define GC_EMBEDDER_EPHEMERON_HEADER struct gc_header header;
#define GC_EMBEDDER_FINALIZER_HEADER struct gc_header header;

static inline size_t gc_finalizer_priority_count() { return 2; }

static inline int
gc_is_valid_conservative_ref_displacement(uintptr_t displacement) {
#if GC_CONSERVATIVE_ROOTS || GC_CONSERVATIVE_TRACE
  // Here is where you would allow tagged heap object references.
  return displacement == 0;
#else
  // Shouldn't get here.
  GC_CRASH();
#endif
}

// No external objects.
static inline int gc_extern_space_visit(struct gc_extern_space *space,
                                        struct gc_edge edge,
                                        struct gc_ref ref) {
  GC_CRASH();
}
static inline void gc_extern_space_start_gc(struct gc_extern_space *space,
                                            int is_minor_gc) {
}
static inline void gc_extern_space_finish_gc(struct gc_extern_space *space,
                                             int is_minor_gc) {
}

/* GC visiting */

typedef void (*visitor)(struct gc_edge edge, struct gc_heap *heap,
                        void *visit_data);

#define DEFINE_FIELDLESS(name)                                          \
  static inline void                                                    \
  visit_##name##_fields(name##_s *o, visitor visit,                     \
                        struct gc_heap *heap, void *visit_data) {       \
  }

static inline void
visit_pair_fields(pair_s *pair, visitor visit,
                  struct gc_heap *heap, void *visit_data) {
  visit(gc_edge(&pair->car), heap, visit_data);
  visit(gc_edge(&pair->cdr), heap, visit_data);
}

static inline void
visit_promise_fields(promise_s *promise, visitor visit,
                     struct gc_heap *heap, void *visit_data) {
  visit(gc_edge(&promise->fulfiller), heap, visit_data);
}

DEFINE_FIELDLESS(symbol);
DEFINE_FIELDLESS(integer);
DEFINE_FIELDLESS(special);

static inline void
visit_operator_fields(operator_s* op, visitor visit,
                      struct gc_heap *heap, void *visit_data) {
  visit(gc_edge(&op->arguments), heap, visit_data);
  visit(gc_edge(&op->body), heap, visit_data);
  visit(gc_edge(&op->env), heap, visit_data);
  visit(gc_edge(&op->op_env), heap, visit_data);
}

DEFINE_FIELDLESS(string);

static inline void
visit_port_fields(port_s* port, visitor visit,
                  struct gc_heap *heap, void *visit_data) {
  visit(gc_edge(&port->name), heap, visit_data);
}

DEFINE_FIELDLESS(character);

static inline void
visit_vector_fields(vector_s* vec, visitor visit,
                    struct gc_heap *heap, void *visit_data) {
  for (size_t i = 0; i < vec->length; ++i)
    visit(gc_edge(&vec->vector[i]), heap, visit_data);
}

static inline void
visit_table_fields(table_s* table, visitor visit,
                   struct gc_heap *heap, void *visit_data) {
  visit(gc_edge(&table->buckets), heap, visit_data);
}

static inline void
visit_buckets_fields(buckets_s* buckets, visitor visit,
                     struct gc_heap *heap, void *visit_data) {
  for (size_t i = 0; i < buckets->length; ++i) {
    visit(gc_edge(&buckets->bucket[i].key), heap, visit_data);
    visit(gc_edge(&buckets->bucket[i].value), heap, visit_data);
  }
}

static inline void
visit_thread_fields(thread_s* thread, visitor visit,
                    struct gc_heap *heap, void *visit_data) {
  visit(gc_edge(&thread->thunk), heap, visit_data);
}

static inline void
visit_weak_box_fields(weak_box_s* weak_box, visitor visit,
                      struct gc_heap *heap, void *visit_data) {
  gc_trace_ephemeron(weak_box, visit, heap, visit_data);
}

static inline void
visit_ephemeron_fields(ephemeron_s* ephemeron, visitor visit,
                       struct gc_heap *heap, void *visit_data) {
  gc_trace_ephemeron(ephemeron, visit, heap, visit_data);
}

#undef DEFINE_FIELDLESS

/* GC trace */

static inline uintptr_t* header_word(struct gc_ref ref) {
  struct gc_header *header = gc_ref_heap_object(ref);
  return &header->header;
}

static inline void gc_trace_object(struct gc_ref ref,
                                   visitor trace_edge,
                                   struct gc_heap *heap,
                                   void *trace_data,
                                   size_t *size) {
  // the test code in whippet does this multiple gc_ref_heap_object
  // rather than just keeping an object. not sure if that's required.
  switch(header_live_alloc_kind(*header_word(ref))) {
#define SCAN_OBJECT(name, Name, NAME)                                   \
    case TYPE_##NAME:                                                   \
      if (trace_edge)                                                   \
        visit_##name##_fields(gc_ref_heap_object(ref), trace_edge,      \
                              heap, trace_data);                        \
      if (size)                                                         \
        *size = name##_osize(gc_ref_heap_object(ref));                  \
      break;
    FOR_EACH_HEAP_OBJECT_KIND(SCAN_OBJECT)
#undef SCAN_OBJECT
  default:
    GC_CRASH();
  }
}

/* roots */

static inline void visit_roots(struct handle *roots,
                               void (*trace_edge)(struct gc_edge edge,
                                                  struct gc_heap *heap,
                                                  void *trace_data),
                               struct gc_heap *heap,
                               void *trace_data) {
  for (struct handle *h = roots; h; h = h->next)
    for (size_t i = 0; i < h->nptrs; ++i)
      if (h->v[i])
        trace_edge(gc_edge(&h->v[i]), heap, trace_data);
}

static inline void gc_trace_mutator_roots(struct gc_mutator_roots *roots,
                                          void (*trace_edge)(struct gc_edge edge,
                                                             struct gc_heap *heap,
                                                             void *trace_data),
                                          struct gc_heap *heap,
                                          void *trace_data) {
  if (roots)
    visit_roots(roots->roots, trace_edge, heap, trace_data);
}

static inline void gc_trace_heap_roots(struct gc_heap_roots *roots,
                                       void (*trace_edge)(struct gc_edge edge,
                                                          struct gc_heap *heap,
                                                          void *trace_data),
                                       struct gc_heap *heap,
                                       void *trace_data) {
  if (roots)
    visit_roots(roots->roots, trace_edge, heap, trace_data);
}

static inline uintptr_t gc_object_forwarded_nonatomic(struct gc_ref ref) {
  uintptr_t tag = *header_word(ref);
  return (tag & gcobj_not_forwarded_bit) ? 0 : tag;
}

static inline void gc_object_forward_nonatomic(struct gc_ref ref,
                                               struct gc_ref new_ref) {
  *header_word(ref) = gc_ref_value(new_ref);
}

static inline void gc_object_set_remembered(struct gc_ref ref) {
  uintptr_t *loc = header_word(ref);
  atomic_fetch_or(loc, gcobj_remembered_bit);
}

static inline int gc_object_is_remembered_nonatomic(struct gc_ref ref) {
  uintptr_t *loc = header_word(ref);
  uintptr_t tag = *loc;
  return tag & gcobj_remembered_bit;
}

static inline void gc_object_clear_remembered_nonatomic(struct gc_ref ref) {
  uintptr_t *loc = header_word(ref);
  uintptr_t tag = *loc;
  *loc = tag & ~(uintptr_t)gcobj_remembered_bit;
}

static inline struct gc_atomic_forward
gc_atomic_forward_begin(struct gc_ref ref) {
  uintptr_t tag = atomic_load_explicit(header_word(ref), memory_order_acquire);
  enum gc_forwarding_state state;
  if (tag == gcobj_busy)
    state = GC_FORWARDING_STATE_BUSY;
  else if (tag & gcobj_not_forwarded_bit)
    state = GC_FORWARDING_STATE_NOT_FORWARDED;
  else
    state = GC_FORWARDING_STATE_FORWARDED;
  return (struct gc_atomic_forward){ ref, tag, state };
}

static inline int
gc_atomic_forward_retry_busy(struct gc_atomic_forward *fwd) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_BUSY);
  uintptr_t tag = atomic_load_explicit(header_word(fwd->ref),
                                       memory_order_acquire);
  if (tag == gcobj_busy)
    return 0;
  if (tag & gcobj_not_forwarded_bit)
    fwd->state = GC_FORWARDING_STATE_ABORTED;
  else {
    fwd->state = GC_FORWARDING_STATE_FORWARDED;
    fwd->data = tag;
  }
  return 1;
}

static inline void
gc_atomic_forward_acquire(struct gc_atomic_forward *fwd) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_NOT_FORWARDED);
  // should this have explicit ordering? acq rel?
  if (atomic_compare_exchange_strong(header_word(fwd->ref), &fwd->data,
                                     gcobj_busy))
    fwd->state = GC_FORWARDING_STATE_ACQUIRED;
  else if (fwd->data == gcobj_busy)
    fwd->state = GC_FORWARDING_STATE_BUSY;
  else {
    GC_ASSERT((fwd->data & gcobj_not_forwarded_bit) == 0);
    fwd->state = GC_FORWARDING_STATE_FORWARDED;
  }
}

static inline void
gc_atomic_forward_abort(struct gc_atomic_forward *fwd) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_ACQUIRED);
  atomic_store_explicit(header_word(fwd->ref), fwd->data, memory_order_release);
  fwd->state = GC_FORWARDING_STATE_ABORTED;
}

static inline size_t
gc_atomic_forward_object_size(struct gc_atomic_forward *fwd) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_ACQUIRED);
  switch (header_live_alloc_kind(fwd->data)) {
#define OBJECT_SIZE(name, Name, NAME)                                   \
    case TYPE_##NAME:                                                   \
      return name##_osize(gc_ref_heap_object(fwd->ref));
    FOR_EACH_HEAP_OBJECT_KIND(OBJECT_SIZE)
#undef OBJECT_SIZE
  default:
    GC_CRASH();
  }
}

static inline void
gc_atomic_forward_commit(struct gc_atomic_forward *fwd, struct gc_ref new_ref) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_ACQUIRED);
  *header_word(new_ref) = fwd->data;
  atomic_store_explicit(header_word(fwd->ref), gc_ref_value(new_ref),
                        memory_order_release);
  fwd->state = GC_FORWARDING_STATE_FORWARDED;
}

static inline uintptr_t
gc_atomic_forward_address(struct gc_atomic_forward *fwd) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_FORWARDED);
  return fwd->data;
}
