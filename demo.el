;;; demo.el --- Demonstrate elisp-optimizer  -*- lexical-binding: t; -*-
;; Run:  emacs -Q --batch -L . -l demo.el
;; Each case is compiled with the mode off and on.  We print the bytecode
;; size (bytes of bytecode; inlined loops are bigger but faster), check that
;; both versions give the same result, and time 1000000 calls.  Small timing
;; differences are noise; equal->eq and member->memq keep the size because
;; both opcodes are one byte.

(require 'elisp-optimizer)
(require 'bytecomp)

(defvar demo-cases
  '(("dead branch after type test"
     (lambda (x) (declare (type string x)) (if (stringp x) 'string 'other))
     ("abc"))
    ("redundant check after guard"
     (lambda (x) (if (consp x) (if (listp x) (car x) 'never) 'no))
     ((1 2)))
    ("identity operand on integer"
     (lambda (x) (declare (type fixnum x)) (+ (* x 1) 0))
     (41))
    ("equal -> eq on symbols"
     (lambda (x) (declare (type symbol x)) (equal x 'foo))
     (foo))
    ("member -> memq"
     (lambda (x l) (declare (type symbol x)) (member x l))
     (b (a b c)))
    ("mapcar, lambda captures a variable"
     (lambda (l k) (mapcar (lambda (x) (+ x k)) l))
     ((1 2 3) 10))
    ("mapcar, plain lambda"
     (lambda (l) (mapcar (lambda (x) (* x 2)) l))
     ((1 2 3)))
    ("mapc with identity (walk only)"
     (lambda (l) (mapc #'identity l))
     ((1 2 3)))
    ("mapcar on non-list still works"
     (lambda (v) (mapcar (lambda (x) (1+ x)) v))
     ([1 2 3]))))

(setq byte-compile-warnings nil)

(defun demo--compile (form on)
  (elisp-optimizer-mode (if on 1 -1))
  (unwind-protect (byte-compile form)
    (elisp-optimizer-mode -1)))

(defun demo--time (fn args)
  (let ((t0 (float-time)))
    (dotimes (_ 1000000) (apply fn args))
    (- (float-time) t0)))

(dolist (c demo-cases)
  (pcase-let* ((`(,name ,form ,args) c)
               (off (demo--compile form nil))
               (on (demo--compile form t))
               (r-off (apply off args))
               (r-on (apply on args)))
    (princ (format "%-34s size %3d -> %3d  same result: %-3s  time %.3fs -> %.3fs\n"
                   name (length (aref off 1)) (length (aref on 1))
                   (if (equal r-off r-on) "yes" "NO!")
                   (demo--time off args) (demo--time on args)))))

;; Real defun in a file, through the file compiler.
(princ "\nOptimizer decisions for a small file:\n")
(let ((file (make-temp-file "demo" nil ".el")))
  (with-temp-file file
    (insert ";;; -*- lexical-binding: t -*-\n"
            "(defun demo-f (x) (declare (type string x))\n"
            "  (if (stringp x) (mapcar (lambda (c) (1+ c)) x) 'dead))\n"
            "(defun demo-g (l) (mapc #'identity l))\n"))
  (elisp-optimizer-mode 1)
  (let ((byte-compile-warnings nil)) (byte-compile-file file))
  (elisp-optimizer-report)
  (elisp-optimizer-mode -1)
  (delete-file file) (delete-file (byte-compile-dest-file file)))
