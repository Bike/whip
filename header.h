#pragma once

#include <stdint.h>

struct gc_header {
  uintptr_t header;
};

// Alloc kind is in bits 2-7, for live objects.
static const uintptr_t gcobj_alloc_kind_mask = 0x3f;
static const uintptr_t gcobj_alloc_kind_shift = 2;
static const uintptr_t gcobj_remembered_mask = 0x2;
static const uintptr_t gcobj_remembered_bit = 0x2;
static const uintptr_t gcobj_forwarded_mask = 0x1;
static const uintptr_t gcobj_not_forwarded_bit = 0x1;
static const uintptr_t gcobj_busy = 0;

static inline uint8_t header_live_alloc_kind(uintptr_t header) {
  return (header >> gcobj_alloc_kind_shift) & gcobj_alloc_kind_mask;
}
static inline uintptr_t header_live(uint8_t alloc_kind) {
  return ((uintptr_t)alloc_kind << gcobj_alloc_kind_shift)
    | gcobj_not_forwarded_bit;
}
