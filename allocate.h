#pragma once

#include "header.h"
#include "gc-api.h"

static inline void*
gc_allocate_with_type(struct gc_mutator *mut, type_t type, size_t bytes) {
  void *obj = gc_allocate(mut, bytes);
  // The benchmark code does essentially
  // ref-heap-object(ref-from-heap-object obj)
  // which I'm pretty sure are inverses, looking at gc-ref.h. So, no thanks.
  // Also, what happens if we gc_allocate but then a collection starts before
  // we initialize? I guess that means the header is gcobj_busy so it's okay?
  struct gc_header *header = obj;
  header->header = header_live(type);
  return obj;
}
