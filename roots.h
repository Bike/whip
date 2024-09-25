#pragma once

struct handle {
  size_t nptrs;
  void **v;
  struct handle *next;
};

struct gc_heap_roots {
  struct handle *roots;
};

struct gc_mutator_roots {
  struct handle *roots;
};
