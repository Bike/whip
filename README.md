This is a simple pseudo-R4RS Scheme using the [Whippet](https://github.com/wingo/whippet/) garbage collector. It is an adaptation of the [Memory Pool System](https://github.com/Ravenbrook/mps)'s example Scheme.

# Setup

Clone Whippet into the main directory. I don't want to bother with the subtree merge or submodules or whatever. Then `make`. This will produce a `scheme` binary.

# Running

With no arguments, `scheme` pops up a REPL. You have access to basic operators and procedures like `letrec`, list procedures, arithmetic, vectors, hash tables, yada yada.

With arguments, `scheme` will treat each argument as a file and load them in order, and then quit.

# Extensions

Stuff I've implemented to see how it works with whippet, that wasn't in the original MPS version:

* Threads. Use `(thread thunk)` to start a thread.
* Weak boxes and ephemerons. `make-weak-box`, `weak-box-value`, `make-ephemeron`, `ephemeron-value`, etc.

Syntax and semantics for these is mostly copied from Racket.
