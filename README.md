# A demo of some source-to-source optimizations (et hooked into byte compiler) 

Type-aware source-to-source optimizations for the Emacs Lisp byte compiler,
packaged as a global minor mode. Should work with Emacs 28.1+ but only tested on
Emacs 32 (master). It is just a brief LLM:ed demo to illustrate the idea.

```elisp
(require 'elisp-optimizer)
(elisp-optimizer-byte-compile-file "foo.el")   ; mode on only for this call
```

Batch: `emacs -Q --batch -l elisp-optimizer.el -f elisp-optimizer-batch-byte-compile foo.el`

Or wrap your own build in `(elisp-optimizer-mode 1)` ... `(elisp-optimizer-mode -1)`.
The mode is a `:filter-args` advice on `cconv-closure-convert`, i.e. the point
between `macroexpand-all` and closure conversion in `byte-compile-preprocess`
(where bytecomp.el has a FIXME about running `byte-optimize-form` before
closure conversion). Disabling the mode
removes the advice; compiled output has no runtime dependency on this library.

Implemented (see the Commentary in `elisp-optimizer.el`): branch/`cond`/`and`/
`or`/`while` folding from inferred types, type-predicate folding, removal of
redundant `cl-check-type`/`cl-assert` guards, `equal`/`eql`→`eq`, fixnum `=`→`eq`,
`member`/`assoc`/`delete`→`memq`/`assq`/`delq`, disjoint-type equality folding,
dropping identity operands on integers (`(+ x 0)`, `(* x 1)`, `(logand x -1)`,
`(logior x 0)`), and `mapcar`/`mapc` inlining (see `elisp-optimizer-inline-mapping`).
Emacs byte compiler never does this because they are C subrs that call back into Lisp per
element. The inlined loop copies `mapcar1`'s semantics (length first, same errors
on dotted/circular lists); with unknown argument types it is guarded by `listp`
and falls back to the real call for vectors and strings. It trades code size
for speed (about 5 bytes becomes about 47) and is mainly faster for short lists
and lambdas that capture variables; otherwise the gain is a few percent.
`(mapc #'identity xs)` keeps only the length check and the list walk.

Types also come from `(declare (type T var...))`, `(declare (type (function
...)))` and `(declare (et ...))` on `defun`/`lambda` (Emacs itself warns
"Unknown defun property" for `type`; this is harmless), and the return types
of `defun`s earlier in the same file are inferred.

Types of variables are tracked only for lexical variables that are never
`setq`'d, so no call can invalidate them. Not implemented on purpose: typed `plist-get`→`nth`
(unsound because `plist-put` prepends keys) and float unboxing (the bytecode
VM cannot). External type sources (e.g. `et`) can plug in through
`elisp-optimizer-type-functions` / `elisp-optimizer-function-types`; those are
trusted, and the `et` hookup is untested.

Demo: `emacs -Q --batch -L . -l demo.el` compiles sample functions with the mode
off and on and compares size, result and time.

Tests: `emacs -Q --batch -L . -l elisp-optimizer-tests.el -f ert-run-tests-batch-and-exit`
