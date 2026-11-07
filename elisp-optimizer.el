;;; elisp-optimizer.el --- Type-aware optimizations for the byte compiler -*- lexical-binding: t; -*-

;; Copyright (C) 2026  Arthur Miller

;; Author: Arthur Miller <arthur.miller@live.com>
;; Version: 0.1.0
;; Package-Requires: ((emacs "28.1"))
;; Keywords: lisp, tools, internal
;; License: GPL-3.0-or-later

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; `elisp-optimizer-mode' is a global minor mode that teaches the
;; Emacs Lisp byte compiler a handful of optimizations that depend on
;; knowing the *type* of an expression.  It only has an effect while
;; code is being byte-compiled; the code it produces is ordinary
;; bytecode that has no dependency on this library.
;;
;; How it hooks in
;; ---------------
;;
;; `byte-compile-preprocess' runs `macroexpand-all' and then
;; `cconv-closure-convert'.  A FIXME in that function says an
;; optimizer should live between the two steps.  The mode installs a
;; `:filter-args' advice on `cconv-closure-convert', so our pass sees
;; the fully macroexpanded form and hands a rewritten form to the
;; closure converter.  Disabling the mode removes the advice, so
;; nothing is left behind after the compilation is finished.
;;
;; What it does
;; ------------
;;
;; The pass is a code walker that infers a small set-of-primitive-types
;; for each expression (nil, t, keyword, symbol, fixnum, bignum, float,
;; string, cons, vector, other) and tracks facts about lexical variables
;; that are never assigned.  Facts come from literals, from the known
;; result types of primitives, from `let' initializers, and from type
;; tests that dominate the code (`if', `cond', `and', `or', `when',
;; `unless', and guards such as `cl-check-type' / `cl-assert').
;; With that it can:
;;
;;  - fold branches whose test has a known truth value (`if', `cond',
;;    `and', `or', `while'), removing dead code;
;;  - fold type predicates whose answer is known;
;;  - drop `cl-check-type' style guards that are proven redundant;
;;  - turn `equal'/`eql' into `eq', `=' into `eq' for fixnums, `member'
;;    into `memq', `assoc' into `assq', `delete' into `delq';
;;  - fold `eq'/`equal'/`eql' to nil when the operand types are disjoint;
;;  - inline `mapcar'/`mapc' with a literal one-argument lambda (or a
;;    primitive such as `car') into a `while' loop.  The byte compiler
;;    does not do this because both are C functions that call back into
;;    Lisp for every element.  See `elisp-optimizer-inline-mapping'.
;;
;; Every rewrite is meant to be semantics preserving.  Facts about
;; variables are only used for lexical variables that are never the
;; target of `setq', so they cannot be invalidated by a call.
;;
;; Usage
;; -----
;;
;;   (require 'elisp-optimizer)
;;   (elisp-optimizer-byte-compile-file "foo.el")
;;
;; or, for batch use,
;;
;;   emacs -Q --batch -l elisp-optimizer.el \
;;         -f elisp-optimizer-batch-byte-compile foo.el bar.el
;;
;; or enable the mode around your own build:
;;
;;   (elisp-optimizer-mode 1)
;;   (byte-recompile-directory "~/.emacs.d/my-package" 0)
;;   (elisp-optimizer-mode -1)
;;
;; External type information (for example from the `et' type checker)
;; can be supplied through `elisp-optimizer-type-functions' and
;; `elisp-optimizer-function-types'.  Such information is trusted:
;; if it is wrong, the compiled code is wrong.
;;
;; Not done on purpose
;; -------------------
;;
;; Rewriting `plist-get' on a typed plist into `nth' is unsound in
;; Emacs Lisp because `plist-put' may prepend keys, so it is not
;; implemented. The bytecode VM has no unboxed floats, so we can't
;; do some transforms that we can in SBCL.

;;; Code:

(eval-when-compile (require 'subr-x))
(require 'cl-lib)

(defgroup elisp-optimizer nil
  "Type-aware optimizations for the Emacs Lisp byte compiler."
  :group 'lisp
  :prefix "elisp-optimizer-")

(defcustom elisp-optimizer-verbose nil
  "When non-nil, log each rewrite with `message'."
  :type 'boolean)

(defcustom elisp-optimizer-inline-mapping 'guarded
  "Whether to inline `mapcar' and `mapc' into `while' loops.
The byte compiler never does this: both are C functions that call back
into Lisp once per element.  Inlining avoids the closure and the call.

nil          never inline.
`known-lists' inline only when the sequence is known to be a list.
`guarded'     also inline when the type is unknown, by testing `listp'
              at run time and falling back to the original call for
              vectors, strings and bool-vectors.  The lambda body is
              duplicated, so it is limited by
              `elisp-optimizer-inline-size-limit'.

The loop behaves like the C code: the length is taken first, so dotted
and circular lists signal the same errors."
  :type '(choice (const :tag "Never" nil)
                 (const :tag "Known lists only" known-lists)
                 (const :tag "Also unknown types, guarded" guarded)))

(defcustom elisp-optimizer-inline-size-limit 40
  "Largest lambda body, in conses, duplicated by guarded mapping inlining."
  :type 'natnum)

(defcustom elisp-optimizer-function-types nil
  "Alist of (FUNCTION . TYPE-SPEC) giving trusted result types.
TYPE-SPEC is a list of type names, the result being one of them.
Known names: null t keyword symbol fixnum bignum integer float
number string cons list vector boolean atom other.
Example: ((my-name . (string)) (my-count . (fixnum)))."
  :type '(alist :key-type symbol :value-type (repeat symbol)))

(defcustom elisp-optimizer-type-functions nil
  "Abnormal hook used to ask external tools for expression types.
Each function is called with a call form (FUNCTION ARG...), where the
arguments are already optimized, and returns a type spec (see
`elisp-optimizer-function-types') or nil if it knows nothing.  The
answer is trusted."
  :type 'hook)

(defvar byte-compile-delete-errors)
(defvar byte-compile-bound-variables)
(defvar byte-compile--known-dynamic-vars)
(defvar byte-optimize)
(defvar elisp-optimizer--handlers)

;;;; Types
;;
;; A type is a bit mask; an expression has one of the primitive types
;; whose bit is set.

(defconst elisp-optimizer--empty 0)
(defconst elisp-optimizer--null 1)
(defconst elisp-optimizer--true 2)
(defconst elisp-optimizer--boolean 3)
(defconst elisp-optimizer--keyword 4)
(defconst elisp-optimizer--symbol 8)
(defconst elisp-optimizer--fixnum 16)
(defconst elisp-optimizer--bignum 32)
(defconst elisp-optimizer--float 64)
(defconst elisp-optimizer--string 128)
(defconst elisp-optimizer--cons 256)
(defconst elisp-optimizer--vector 512)
(defconst elisp-optimizer--other 1024)
(defconst elisp-optimizer--top 2047)
(defconst elisp-optimizer--list 257)
(defconst elisp-optimizer--eq-safe 31
  "Types for which `equal' and `eql' are the same as `eq'.")

(defconst elisp-optimizer--type-table
  `((null       ,elisp-optimizer--null    (null not) . ,elisp-optimizer--null)
    (t          ,elisp-optimizer--true    nil        . ,elisp-optimizer--true)
    (keyword    ,elisp-optimizer--keyword keywordp   . ,elisp-optimizer--keyword)
    (symbol     15                        symbolp    . 15)
    (fixnum     ,elisp-optimizer--fixnum  fixnump    . ,elisp-optimizer--fixnum)
    (bignum     ,elisp-optimizer--bignum  bignump    . ,elisp-optimizer--bignum)
    (integer    48                        integerp   . 48)
    (float      ,elisp-optimizer--float   floatp     . ,elisp-optimizer--float)
    (number     112                       numberp    . 112)
    (string     ,elisp-optimizer--string  stringp    . ,elisp-optimizer--string)
    (cons       ,elisp-optimizer--cons    consp      . ,elisp-optimizer--cons)
    (list       ,elisp-optimizer--list    listp      . ,elisp-optimizer--list)
    (vector     ,elisp-optimizer--vector  vectorp    . ,elisp-optimizer--vector)
    (boolean    ,elisp-optimizer--boolean booleanp   . ,elisp-optimizer--boolean)
    (other      ,elisp-optimizer--other   nil        . ,elisp-optimizer--empty)
    (atom       1791                      atom       . 1791)
    (nil        48                        natnump        . ,elisp-optimizer--empty)
    (nil        ,elisp-optimizer--fixnum  characterp     . ,elisp-optimizer--empty)
    (nil        1921                      sequencep      . ,elisp-optimizer--empty)
    (nil        1664                      arrayp         . ,elisp-optimizer--empty)
    (nil        ,elisp-optimizer--other   bufferp        . ,elisp-optimizer--empty)
    (nil        ,elisp-optimizer--other   markerp        . ,elisp-optimizer--empty)
    (nil        ,elisp-optimizer--other   hash-table-p   . ,elisp-optimizer--empty)
    (nil        ,elisp-optimizer--other   char-table-p   . ,elisp-optimizer--empty)
    (nil        ,elisp-optimizer--other   bool-vector-p  . ,elisp-optimizer--empty)
    (nil        ,elisp-optimizer--other   recordp        . ,elisp-optimizer--empty))
  "Table of (NAME MASK PREDICATE . EXACT) rows.
NAME is accepted in type specs, or nil for predicate-only entries.
MASK is the type mask.
PREDICATE is a predicate symbol, list of symbols, or nil.
EXACT is the mask when the predicate is exact, or `elisp-optimizer--empty'.")

(defconst elisp-optimizer--type-names
  (let (names)
    (dolist (row elisp-optimizer--type-table (nreverse names))
      (when (car row)
        (push (cons (car row) (cadr row)) names))))
  "Names accepted in type specs, with their masks.")

(defconst elisp-optimizer--predicates
  (let (preds)
    (dolist (row elisp-optimizer--type-table (nreverse preds))
      (let ((pred (caddr row))
            (mask (cadr row))
            (exact (cdddr row)))
        (when pred
          (if (consp pred)
              (dolist (p pred)
                (push (cons p (cons mask exact)) preds))
            (push (cons pred (cons mask exact)) preds))))))
  "Type predicates: (NAME IMPLIED . EXACT).
If (NAME X) is true, the type of X is within the mask IMPLIED.  If the
type of X is within EXACT, the predicate is true, and it is false when X's
type is disjoint from IMPLIED.  EXACT is 0 when no type is sufficient.")

(cl-defsubst elisp-optimizer--spec-mask (spec)
  "Return the type mask for the type SPEC (a list of type names)."
  (let ((mask elisp-optimizer--empty))
    (dolist (name spec)
      (setq mask (logior mask (or (cdr (assq name elisp-optimizer--type-names))
                                  elisp-optimizer--top))))
    (if (eql mask elisp-optimizer--empty) elisp-optimizer--top mask)))

;; The walker carries type masks, not values; this is the boundary where a literal becomes a type.
(defun elisp-optimizer--const-type (value)
  "Return the type mask of the constant VALUE."
  (cond ((null value) elisp-optimizer--null)
        ((eq value t) elisp-optimizer--true)
        ((keywordp value) elisp-optimizer--keyword)
        ((symbolp value) elisp-optimizer--symbol)
        ((fixnump value) elisp-optimizer--fixnum)
        ((bignump value) elisp-optimizer--bignum)
        ((floatp value) elisp-optimizer--float)
        ((stringp value) elisp-optimizer--string)
        ((consp value) elisp-optimizer--cons)
        ((vectorp value) elisp-optimizer--vector)
        (t elisp-optimizer--other)))

(defconst elisp-optimizer--result-types
  (let (alist)
    (dolist (spec '((3 eq equal eql = < > <= >= /= string= string-equal
                       string< string-lessp bobp eobp bolp eolp)
                    (257 memq member assq assoc mapcar)
                    (16 length point point-min point-max line-number-at-pos)
                    (112 1+ 1- + - * / mod abs min max string-to-number)
                    (48 % ash logand logior logxor lognot truncate floor
                        ceiling round)
                    (64 float)
                    (128 concat format format-message symbol-name
                         number-to-string make-string string buffer-string
                         buffer-substring buffer-substring-no-properties
                         propertize prin1-to-string mapconcat string-trim)
                    (256 cons)
                    (512 vector make-vector)
                    (8 make-symbol gensym)
                    (15 intern)
                    (17 char-after char-before)
                    (1024 current-buffer)))
      (dolist (fn (cdr spec)) (push (cons fn (car spec)) alist)))
    alist)
  "Alist (FUNCTION . MASK) of result types of well-known primitives.")

;;;; State and statistics

(defvar elisp-optimizer--setqs nil
  "Hash table of symbols that are the target of a `setq' in the form.")

(defvar elisp-optimizer--dynbound nil
  "Variables the compiler considers dynamically bound.")

(defvar elisp-optimizer--stats nil
  "Alist (KIND . COUNT) of rewrites performed since the mode was enabled.")

(defvar elisp-optimizer--inferred-types nil
  "Hash table mapping function symbols to their inferred return type masks.")

(defun elisp-optimizer--note (kind &optional detail)
  "Record a rewrite of KIND (a symbol), logging DETAIL when verbose."
  (let ((cell (assq kind elisp-optimizer--stats)))
    (if cell (setcdr cell (1+ (cdr cell)))
      (push (cons kind 1) elisp-optimizer--stats)))
  (when elisp-optimizer-verbose
    (message "[elisp-optimizer] %s%s" kind
             (if detail (format ": %S" detail) ""))))

;;;; Helpers

(cl-defsubst elisp-optimizer--truth (type)
  "Return `true' if TYPE excludes nil, `false' if it is only nil, else nil."
  (cond ((eql type elisp-optimizer--empty) nil)
        ((eql type elisp-optimizer--null) 'false)
        ((eql (logand type elisp-optimizer--null) elisp-optimizer--empty) 'true)))

(defun elisp-optimizer--trackable-p (var)
  "Non-nil if facts about the lexical variable VAR may be recorded."
  (and lexical-binding var (symbolp var) (not (eq var t)) (not (keywordp var))
       (not (special-variable-p var))
       (not (memq var elisp-optimizer--dynbound))
       (not (and (boundp 'byte-compile--known-dynamic-vars)
                 (memq var byte-compile--known-dynamic-vars)))
       (not (gethash var elisp-optimizer--setqs))))

(cl-defsubst elisp-optimizer--var-type (var env)
  "Return the type mask of the variable reference VAR in ENV."
  (cond ((null var) elisp-optimizer--null)
        ((eq var t) elisp-optimizer--true)
        ((keywordp var) elisp-optimizer--keyword)
        (t (or (cdr (assq var env)) elisp-optimizer--top))))

(cl-defsubst elisp-optimizer--bind (var type env)
  "Return ENV extended with a binding of VAR with TYPE."
  (cons (cons var (and (elisp-optimizer--trackable-p var)
                       (if (eql type elisp-optimizer--empty)
                           elisp-optimizer--top
                         type)))
        env))

(defun elisp-optimizer--all-discardable (forms)
  "Non-nil if all of FORMS can be dropped when their value is unused."
  (cl-every #'elisp-optimizer--discardable-p forms))

(cl-defsubst elisp-optimizer--discardable-p (form)
  "Non-nil if FORM has no side effects and cannot signal an error."
  (if (atom form) t
    (let ((head (car form)))
      (cond ((memq head '(quote function)) t)
            ((not (symbolp head)) nil)
            ((memq head '(progn and or if))
             (elisp-optimizer--all-discardable (cdr form)))
            ((eq head 'cond)
             (let ((ok t))
               (dolist (clause (cdr form))
                 (unless (and (listp clause)
                              (elisp-optimizer--all-discardable clause))
                   (setq ok nil)))
               ok))
            ((special-form-p head) nil)
            (t (let ((p (function-get head 'side-effect-free)))
                 (and p
                      (or (eq p 'error-free) byte-compile-delete-errors)
                      (proper-list-p (cdr form))
                      (elisp-optimizer--all-discardable (cdr form)))))))))

(defun elisp-optimizer--progn (forms)
  "Return a single form evaluating FORMS in sequence."
  (cond ((null forms) nil)
        ((null (cdr forms)) (car forms))
        (t (cons 'progn forms))))

(defun elisp-optimizer--seq (effect forms)
  "Return a form evaluating EFFECT (for side effects only) and then FORMS."
  (let ((eff (reverse (if (eq (car-safe effect) 'progn)
                          (cdr effect)
                        (list effect)))))
    (while (and eff (elisp-optimizer--discardable-p (car eff)))
      (pop eff))
    (elisp-optimizer--progn (append (nreverse eff) forms))))

(defun elisp-optimizer--diverges-p (form)
  "Non-nil if evaluating FORM never returns normally."
  (and (consp form)
       (cl-case (car form)
         ((signal error user-error throw cl--assertion-failed)
          t)
         (progn
          (and (consp (cdr form))
               (elisp-optimizer--diverges-p (car (last form))))))))

(cl-defsubst elisp-optimizer--constant (form)
  "If FORM is a constant, return (VALUE), else nil."
  (cond ((or (null form) (eq form t) (keywordp form)
             (numberp form) (stringp form))
         (list form))
        ((and (consp form) (eq (car form) 'quote)) (list (cadr form)))))

;;;; Narrowing

(defun elisp-optimizer--narrow-var (var env keep)
  "Restrict the type of VAR in ENV to its intersection with mask KEEP."
  (let ((ty (and (symbolp var) (cdr (assq var env)))))
    (if ty
        (cons (cons var (logand ty keep)) env)
      env)))

(defun elisp-optimizer--narrow (test env truthy)
  "Return ENV refined by the knowledge that TEST is TRUTHY (non-nil) or not."
  (cond
   ((symbolp test)
    (if (or (null test) (eq test t) (keywordp test)) env
      (elisp-optimizer--narrow-var
       test env (if truthy
                    (lognot elisp-optimizer--null)
                  elisp-optimizer--null))))
   ((not (and (consp test) (proper-list-p test))) env)
   (t
    (let ((head (car test)) (args (cdr test)))
      (cond
       ((and (memq head '(not null)) (= (length args) 1))
        (elisp-optimizer--narrow (car args) env (not truthy)))
       ((eq head 'and)
        (when truthy
          (dolist (a args) (setq env (elisp-optimizer--narrow a env t))))
        env)
       ((eq head 'or)
        (unless truthy
          (dolist (a args) (setq env (elisp-optimizer--narrow a env nil))))
        env)
       ((and (= (length args) 1) (symbolp (car args))
             (assq head elisp-optimizer--predicates))
        (let ((p (cdr (assq head elisp-optimizer--predicates))))
          (elisp-optimizer--narrow-var
           (car args) env (if truthy (car p) (lognot (cdr p))))))
       ((and (memq head '(eq eql equal)) (= (length args) 2))
        (let* ((a (car args)) (b (cadr args))
               (var (cond ((and (symbolp a) (elisp-optimizer--constant b)) a)
                          ((and (symbolp b) (elisp-optimizer--constant a)) b)))
               (const (and var (elisp-optimizer--constant (if (eq var a) b a)))))
          (cond
           ((null var) env)
           (truthy (elisp-optimizer--narrow-var
                    var env (elisp-optimizer--const-type (car const))))
           ((null (car const))
            (elisp-optimizer--narrow-var var env (lognot elisp-optimizer--null)))
           ((eq (car const) t)
            (elisp-optimizer--narrow-var var env (lognot elisp-optimizer--true)))
           (t env))))
       (t env))))))

(defun elisp-optimizer--after (env form)
  "Return ENV refined by what is known once FORM has completed normally."
  (if (not (consp form)) env
    (let ((head (car form)))
      (cond
       ((eq head 'progn)
        (dolist (x (cdr form)) (setq env (elisp-optimizer--after env x)))
        env)
       ((and (eq head 'if) (proper-list-p form) (cddr form))
        (cond ((elisp-optimizer--diverges-p (nth 2 form))
               (elisp-optimizer--narrow (nth 1 form) env nil))
              ((and (nthcdr 3 form)
                    (elisp-optimizer--diverges-p (car (last form))))
               (elisp-optimizer--narrow (nth 1 form) env t))
              (t env)))
       ((and (eq head 'or) (proper-list-p form) (= (length form) 3)
             (elisp-optimizer--diverges-p (nth 2 form)))
        (elisp-optimizer--narrow (nth 1 form) env t))
       (t env)))))

;;;; The walker
;;
;; `elisp-optimizer--walk' returns (NEW-FORM . TYPE-MASK).

(defun elisp-optimizer--walk (form env)
  "Optimize FORM in the type environment ENV.  Return (FORM . TYPE)."
  (cond
   ((symbolp form) (cons form (elisp-optimizer--var-type form env)))
   ((not (consp form)) (cons form (elisp-optimizer--const-type form)))
   ((not (and (symbolp (car form)) (proper-list-p form)))
    (cons form elisp-optimizer--top))
   (t
    (let* ((head (car form))
           (handler (cdr (assq head elisp-optimizer--handlers))))
      (cond
       (handler (funcall handler form env))
       ((special-form-p head) (cons form elisp-optimizer--top))
       (t (elisp-optimizer--walk-call form env)))))))

(defun elisp-optimizer--walk-body (forms env)
  "Optimize the implicit progn FORMS.  Return (FORM-LIST . TYPE)."
  (let ((out nil) (type elisp-optimizer--null))
    (while forms
      (let* ((r (elisp-optimizer--walk (car forms) env))
             (f (car r))
             (last (null (cdr forms))))
        (setq type (cdr r))
        (cond ((and (not last) (elisp-optimizer--discardable-p f))
               (unless (atom f) (elisp-optimizer--note 'dead-statement f)))
              (t (push f out)))
        (unless last (setq env (elisp-optimizer--after env f)))
        (setq forms (cdr forms))))
    (cons (nreverse out) type)))

(defun elisp-optimizer--walk-quote (form _env)
  (cons form (elisp-optimizer--const-type (cadr form))))

(defun elisp-optimizer--type-decl-mask (type-spec)
  "Return the type mask for TYPE-SPEC in a declaration."
  (cond
   ((symbolp type-spec)
    (let ((sym (intern (downcase (symbol-name type-spec)))))
      (or (cdr (assq sym elisp-optimizer--type-names))
          elisp-optimizer--top)))
   ((consp type-spec)
    (elisp-optimizer--spec-mask
     (mapcar (lambda (s) (if (symbolp s) (intern (downcase (symbol-name s))) s))
             type-spec)))
   (t elisp-optimizer--top)))

(defun elisp-optimizer--parse-declares (prefix params)
  "Extract (PARAM-TYPES . RETURN-TYPE) from declare forms in PREFIX for PARAMS."
  (let (param-types ret-type)
    (dolist (item prefix)
      (let ((decl (cond ((eq (car-safe item) 'declare) item)
                        ((and (eq (car-safe item) 'progn)
                              (eq (car-safe (cadr item)) 'quote)
                              (eq (car-safe (cadr (cadr item))) 'declare))
                         (cadr (cadr item))))))
        (when decl
          (dolist (clause (cdr decl))
            (when (consp clause)
              (let ((head (car clause)))
                (cond
                 ;; (type (function (ARG-TYPES...) [RET-TYPE])) or (ftype ...)
                 ((and (memq head '(type ftype))
                       (consp (cadr clause))
                       (eq (car (cadr clause)) 'function))
                  (let ((sig (cadr clause)))
                    (when (nth 2 sig)
                      (setq ret-type (elisp-optimizer--type-decl-mask (nth 2 sig))))
                    (let ((arg-types (cadr sig))
                          (plist params))
                      (while (and arg-types plist)
                        (let ((p (pop plist)))
                          (unless (memq p '(&optional &rest))
                            (let ((ty (pop arg-types)))
                              (when (and p ty)
                                (push (cons p (elisp-optimizer--type-decl-mask ty))
                                      param-types)))))))))
                 ;; (type TYPE-SPEC VAR...)
                 ((and (eq head 'type) (cddr clause))
                  (let ((mask (elisp-optimizer--type-decl-mask (cadr clause))))
                    (dolist (var (cddr clause))
                      (when (symbolp var)
                        (push (cons var mask) param-types)))))
                 ;; (et (VAR TYPE-SPEC)...)
                 ((eq head 'et)
                  (dolist (entry (cdr clause))
                    (when (consp entry)
                      (if (eq (car entry) '@return)
                          (setq ret-type (elisp-optimizer--type-decl-mask (cadr entry)))
                        (when (symbolp (car entry))
                          (push (cons (car entry)
                                      (elisp-optimizer--type-decl-mask (cadr entry)))
                                param-types)))))))))))))
    (cons param-types ret-type)))

(defun elisp-optimizer--walk-lambda (lam env &optional name)
  "Optimize the lambda expression LAM."
  (let ((params (cadr lam)) (body (cddr lam)) prefix env2)
    (while (and (cdr body)
                (or (stringp (car body))
                    (memq (car-safe (car body)) '(interactive declare))
                    (and (eq (car-safe (car body)) 'progn)
                         (eq (car-safe (cadr (car body))) 'quote)
                         (eq (car-safe (cadr (cadr (car body)))) 'declare))))
      (push (pop body) prefix))
    (let* ((parsed (elisp-optimizer--parse-declares prefix params))
           (declared (car parsed))
           (declared-ret (cdr parsed)))
      (dolist (p params)
        (unless (memq p '(&optional &rest))
          (let ((init-type (or (cdr (assq p declared)) elisp-optimizer--top)))
            (push (cons p (and (elisp-optimizer--trackable-p p) init-type))
                  env2))))
      (setq env2 (nconc env2 env))
      (let* ((walked-body (elisp-optimizer--walk-body body env2))
             (ret-type (if declared-ret
                           (if (eql (cdr walked-body) elisp-optimizer--empty)
                               declared-ret
                             (let ((m (logand (cdr walked-body) declared-ret)))
                               (if (eql m elisp-optimizer--empty)
                                   (cdr walked-body)
                                 m)))
                         (cdr walked-body))))
        (when (and name elisp-optimizer--inferred-types)
          (puthash name ret-type elisp-optimizer--inferred-types)
          (elisp-optimizer--note 'inferred-return-type (cons name ret-type)))
        (cons `(lambda ,params ,@(nreverse prefix) ,@(car walked-body))
              elisp-optimizer--other)))))

(defun elisp-optimizer--walk-function (form env)
  (let ((arg (cadr form)))
    (if (and (consp arg) (eq (car arg) 'lambda) (proper-list-p arg))
        (cons (list 'function (car (elisp-optimizer--walk-lambda arg env)))
              elisp-optimizer--other)
      (cons form elisp-optimizer--other))))

(defun elisp-optimizer--walk-progn (form env)
  (let ((r (elisp-optimizer--walk-body (cdr form) env)))
    (cons (if (and (car r) (null (cdr (car r)))) (car (car r))
            (cons 'progn (car r)))
          (cdr r))))

(defun elisp-optimizer--walk-prog1 (form env)
  (let* ((first (elisp-optimizer--walk (cadr form) env))
         (rest (car (elisp-optimizer--walk-body (cddr form) env))))
    ;; Note: Dropping discardable forms in REST and unwrapping (prog1 X) -> X
    ;; are already performed by `byte-optimize-form-code-walker' for `prog1'
    ;; in byte-opt.el (evaluating body for-effect).
    ;;
    ;; (let (keep)
    ;;   (dolist (f rest)
    ;;     (unless (elisp-optimizer--discardable-p f)
    ;;       (push f keep)))
    ;;   (setq rest (nreverse keep)))
    ;; (cons (if rest `(prog1 ,(car first) ,@rest) (car first))
    ;;       (cdr first))
    (cons `(prog1 ,(car first) ,@rest)
          (cdr first))))

(defun elisp-optimizer--walk-if (form env)
  (let* ((test (elisp-optimizer--walk (nth 1 form) env))
         (tform (car test))
         (truth (elisp-optimizer--truth (cdr test))))
    (cond
     ((eq truth 'true)
      (let ((then (elisp-optimizer--walk
                   (nth 2 form) (elisp-optimizer--narrow tform env t))))
        (elisp-optimizer--note 'dead-else-branch (nth 1 form))
        (cons (elisp-optimizer--seq tform (list (car then))) (cdr then))))
     ((eq truth 'false)
      (let ((else (elisp-optimizer--walk-body
                   (nthcdr 3 form) (elisp-optimizer--narrow tform env nil))))
        (elisp-optimizer--note 'dead-then-branch (nth 1 form))
        (cons (elisp-optimizer--seq tform (or (car else) (list nil)))
              (cdr else))))
     (t
      (let ((then (elisp-optimizer--walk
                   (nth 2 form) (elisp-optimizer--narrow tform env t)))
            (else (elisp-optimizer--walk-body
                   (nthcdr 3 form) (elisp-optimizer--narrow tform env nil))))
        (cons `(if ,tform ,(car then) ,@(car else))
              (logior (cdr then) (cdr else))))))))

(defun elisp-optimizer--walk-cond (form env)
  (let ((clauses (cdr form)) out (type elisp-optimizer--empty) exhaustive)
    (while (and clauses (not exhaustive))
      (let* ((clause (car clauses))
             (test (elisp-optimizer--walk (car clause) env))
             (tform (car test))
             (truth (elisp-optimizer--truth (cdr test))))
        (setq clauses (cdr clauses))
        (cond
         ((and (eq truth 'false) (elisp-optimizer--discardable-p tform))
          (elisp-optimizer--note 'dead-cond-clause (car clause)))
         ((eq truth 'false)
          (push (list tform) out)
          (setq env (elisp-optimizer--narrow tform env nil)))
         (t
          (let ((body (elisp-optimizer--walk-body
                       (cdr clause) (elisp-optimizer--narrow tform env t))))
            (push (cons tform (car body)) out)
            (setq type (logior type (if (cdr clause) (cdr body)
                                      (logand (cdr test)
                                              (lognot elisp-optimizer--null)))))
            (when (eq truth 'true) (setq exhaustive t))
            (setq env (elisp-optimizer--narrow tform env nil)))))))
    (when (and clauses exhaustive)
      (elisp-optimizer--note 'dead-cond-clause (caar clauses)))
    (unless exhaustive (setq type (logior type elisp-optimizer--null)))
    (setq out (nreverse out))
    (cond
     ((null out) (cons nil elisp-optimizer--null))
     ((and exhaustive (null (cdr out)) (cdr (car out))
           (elisp-optimizer--discardable-p (car (car out))))
      (cons (elisp-optimizer--progn (cdr (car out))) type))
     (t (cons (cons 'cond out) type)))))

(defun elisp-optimizer--walk-and (form env)
  (let ((args (cdr form)) out (type elisp-optimizer--empty) done)
    (if (null args) (cons t elisp-optimizer--true)
      (while (and args (not done))
        (let* ((r (elisp-optimizer--walk (car args) env))
               (f (car r)) (ty (cdr r))
               (truth (elisp-optimizer--truth ty))
               (last (null (cdr args))))
          (setq args (cdr args))
          (cond
           ((and (not last) (eq truth 'true)
                 (elisp-optimizer--discardable-p f))
            (elisp-optimizer--note 'redundant-and-test f))
           (t (push f out)
              (if last (setq type (logior type ty))
                (setq type (logior type (logand ty elisp-optimizer--null))
                      env (elisp-optimizer--narrow f env t)))
              (when (eq truth 'false) (setq done t))))))
      (setq out (nreverse out))
      (cons (if (cdr out) (cons 'and out) (car out)) type))))

(defun elisp-optimizer--walk-or (form env)
  (let ((args (cdr form)) out (type elisp-optimizer--empty) done)
    (if (null args) (cons nil elisp-optimizer--null)
      (while (and args (not done))
        (let* ((r (elisp-optimizer--walk (car args) env))
               (f (car r)) (ty (cdr r))
               (truth (elisp-optimizer--truth ty))
               (last (null (cdr args))))
          (setq args (cdr args))
          (cond
           ((and (not last) (eq truth 'false)
                 (elisp-optimizer--discardable-p f))
            (elisp-optimizer--note 'redundant-or-test f))
           (t (push f out)
              (if last (setq type (logior type ty))
                (setq type (logior type (logand ty (lognot elisp-optimizer--null)))
                      env (elisp-optimizer--narrow f env nil)))
              (when (eq truth 'true) (setq done t))))))
      (setq out (nreverse out))
      (cons (if (cdr out) (cons 'or out) (car out)) type))))

(defun elisp-optimizer--walk-while (form env)
  (let* ((test (elisp-optimizer--walk (nth 1 form) env))
         (tform (car test)))
    (if (and (eq (elisp-optimizer--truth (cdr test)) 'false)
             (elisp-optimizer--discardable-p tform))
        (progn (elisp-optimizer--note 'dead-loop (nth 1 form))
               (cons nil elisp-optimizer--null))
      (cons `(while ,tform
               ,@(car (elisp-optimizer--walk-body
                       (nthcdr 2 form) (elisp-optimizer--narrow tform env t))))
            elisp-optimizer--null))))

(defun elisp-optimizer--walk-let (form env)
  (let* ((star (eq (car form) 'let*))
         (benv env) pending newb)
    (dolist (b (cadr form))
      (let* ((var (if (consp b) (car b) b))
             (has-init (and (consp b) (cdr b)))
             (r (if has-init
                    (elisp-optimizer--walk (cadr b) (if star benv env))
                  (cons nil elisp-optimizer--null))))
        (push (if has-init (list var (car r)) b) newb)
        (if star
            (setq benv (elisp-optimizer--bind var (cdr r) benv))
          (push (cons var (cdr r)) pending))))
    (unless star
      (dolist (p (nreverse pending))
        (setq benv (elisp-optimizer--bind (car p) (cdr p) benv))))
    (let ((body (elisp-optimizer--walk-body (cddr form) benv)))
      (cons `(,(car form) ,(nreverse newb) ,@(car body)) (cdr body)))))

(defun elisp-optimizer--walk-setq (form env)
  (let ((p (cdr form)) out (type elisp-optimizer--null))
    (while p
      (let ((r (elisp-optimizer--walk (cadr p) env)))
        (push (car p) out)
        (push (car r) out)
        (setq type (cdr r)
              p (cddr p))))
    (cons (cons 'setq (nreverse out)) type)))

(defun elisp-optimizer--walk-condition-case (form env)
  (let* ((var (nth 1 form))
         (body (elisp-optimizer--walk (nth 2 form) env))
         (henv (if var (cons (cons var nil) env) env))
         (handlers
          (mapcar (lambda (h)
                    (if (consp h)
                        (cons (car h)
                              (car (elisp-optimizer--walk-body (cdr h) henv)))
                      h))
                  (nthcdr 3 form))))
    (cons `(condition-case ,var ,(car body) ,@handlers) elisp-optimizer--top)))

(defun elisp-optimizer--walk-catch (form env)
  (let ((tag (elisp-optimizer--walk (nth 1 form) env)))
    (cons `(catch ,(car tag)
             ,@(car (elisp-optimizer--walk-body (nthcdr 2 form) env)))
          elisp-optimizer--top)))

(defun elisp-optimizer--walk-unwind-protect (form env)
  (let ((body (elisp-optimizer--walk (nth 1 form) env)))
    (cons `(unwind-protect ,(car body)
             ,@(car (elisp-optimizer--walk-body (nthcdr 2 form) env)))
          (cdr body))))

(defun elisp-optimizer--walk-save (form env)
  (let ((body (elisp-optimizer--walk-body (cdr form) env)))
    (cons (cons (car form) (car body)) (cdr body))))

(defun elisp-optimizer--walk-defvar (form env)
  (if (cddr form)
      (cons `(,(car form) ,(cadr form)
              ,(car (elisp-optimizer--walk (nth 2 form) env))
              ,@(nthcdr 3 form))
            elisp-optimizer--top)
    (cons form elisp-optimizer--top)))

(defun elisp-optimizer--walk-untouched (form _env)
  (cons form elisp-optimizer--top))

(defun elisp-optimizer--walk-defalias (form env)
  "Optimize a `defalias' form, inferring the function's return type."
  (let* ((name-form (cadr form))
         (name (and (consp name-form) (eq (car name-form) 'quote) (cadr name-form)))
         (val (nth 2 form))
         (is-func (and (consp val) (eq (car val) 'function)))
         (target (if is-func (cadr val) val))
         (is-lambda (and (consp target) (eq (car target) 'lambda))))
    (if (and (symbolp name) is-lambda)
        (let* ((lam-res (elisp-optimizer--walk-lambda target env name))
               (new-val (if is-func (list 'function (car lam-res)) (car lam-res))))
          (cons `(defalias ,name-form ,new-val ,@(nthcdr 3 form))
                elisp-optimizer--top))
      (elisp-optimizer--walk-call form env))))

(defconst elisp-optimizer--handlers
  '((quote . elisp-optimizer--walk-quote)
    (function . elisp-optimizer--walk-function)
    (progn . elisp-optimizer--walk-progn)
    (prog1 . elisp-optimizer--walk-prog1)
    (if . elisp-optimizer--walk-if)
    (cond . elisp-optimizer--walk-cond)
    (and . elisp-optimizer--walk-and)
    (or . elisp-optimizer--walk-or)
    (while . elisp-optimizer--walk-while)
    (let . elisp-optimizer--walk-let)
    (let* . elisp-optimizer--walk-let)
    (setq . elisp-optimizer--walk-setq)
    (condition-case . elisp-optimizer--walk-condition-case)
    (catch . elisp-optimizer--walk-catch)
    (unwind-protect . elisp-optimizer--walk-unwind-protect)
    (save-excursion . elisp-optimizer--walk-save)
    (save-restriction . elisp-optimizer--walk-save)
    (save-current-buffer . elisp-optimizer--walk-save)
    (defalias . elisp-optimizer--walk-defalias)
    (defvar . elisp-optimizer--walk-defvar)
    (defconst . elisp-optimizer--walk-defvar)
    (interactive . elisp-optimizer--walk-untouched)
    (declare . elisp-optimizer--walk-untouched))
  "Alist mapping special forms to the function that optimizes them.")

;;;; Function calls

(defun elisp-optimizer--fold (forms value)
  "Return (FORM . TYPE) for a call over FORMS known to yield VALUE (t or nil)."
  (cons (if (elisp-optimizer--all-discardable forms) value
          `(progn ,@forms ,value))
        (if value elisp-optimizer--true elisp-optimizer--null)))

(cl-defsubst elisp-optimizer--subtype-p (type mask)
  "Non-nil if the non-empty TYPE is within MASK."
  (and (not (eql type elisp-optimizer--empty))
       (eql (logand type (lognot mask)) elisp-optimizer--empty)))

(defun elisp-optimizer--tree-size (tree)
  "Return the number of conses in TREE, stopping early above 1000."
  (let ((n 0) (stack (list tree)))
    (while (and stack (< n 1000))
      (let ((x (pop stack)))
        (when (consp x)
          (setq n (1+ n))
          (push (car x) stack)
          (push (cdr x) stack))))
    n))

(defun elisp-optimizer--element-call (fun)
  "Return a function building the call of FUN on an element form, or nil.
FUN is the already optimized first argument of a mapping function."
  (let ((target (and (memq (car-safe fun) '(function quote)) (cadr fun))))
    (cond
     ((and lexical-binding
           (eq (car-safe target) 'lambda) (proper-list-p target)
           (let ((params (cadr target)))
             (and (consp params) (null (cdr params)) (car params)
                  (symbolp (car params))
                  (not (memq (car params) '(&optional &rest)))))
           (not (memq 'interactive (mapcar #'car-safe (cddr target)))))
      (let ((var (car (cadr target))) (body (cddr target)))
        (lambda (elt) `(let ((,var ,elt)) ,@body))))
     ;; A primitive: call it directly, so that `car', `1+' etc. become
     ;; opcodes.  Not for special forms or macros.
     ((and target (symbolp target) (fboundp target)
           (subrp (indirect-function target))
           (not (special-form-p target)) (not (macrop target)))
      (lambda (elt) (list target elt))))))

(defun elisp-optimizer--mapping-loop (fn fun seq)
  "Return a loop applying FUN over the list in variable SEQ, like FN.
FN is `mapcar' or `mapc'.  Return nil if FUN is not suitable.  The
loop mirrors `mapcar1' in fns.c: the length is computed first."
  (let ((call (elisp-optimizer--element-call fun))
        (tail (make-symbol "tail")) (n (make-symbol "n"))
        (acc (make-symbol "acc")) (elt (make-symbol "elt")))
    (when call
      (if (eq fn 'mapcar)
          `(let ((,tail ,seq) (,n (length ,seq)) (,acc nil))
             (while (and (> ,n 0) (consp ,tail))
               (setq ,n (1- ,n))
               (let ((,elt (car ,tail)))
                 (setq ,acc (cons ,(funcall call elt) ,acc)))
               (setq ,tail (cdr ,tail)))
             (nreverse ,acc))
        `(let ((,tail ,seq) (,n (length ,seq)))
           (while (and (> ,n 0) (consp ,tail))
             (setq ,n (1- ,n))
             ,@(let ((form (funcall call elt)))
                 ;; A discardable call (e.g. `identity') needs no element.
                 (unless (elisp-optimizer--all-discardable
                          (list form))
                   `((let ((,elt (car ,tail))) ,form))))
             (setq ,tail (cdr ,tail)))
           ,seq)))))

(defun elisp-optimizer--inline-mapping (fn forms known-list)
  "Inline (FN FUN SEQ) given as FORMS.  Return a form or nil.
KNOWN-LIST non-nil means SEQ is known to evaluate to a list."
  (let* ((fun (car forms))
         (seq (make-symbol "seq"))
         (loop (elisp-optimizer--mapping-loop fn fun seq))
         (target (and (eq (car-safe fun) 'function) (cadr fun)))
         (body (and (consp target) (eq (car target) 'lambda) (cddr target)))
         (body-size (if body (elisp-optimizer--tree-size body) 0)))
    (cond
     ((null loop) nil)
     (known-list `(let ((,seq ,(cadr forms))) ,loop))
     ((and (eq elisp-optimizer-inline-mapping 'guarded)
           (<= body-size elisp-optimizer-inline-size-limit))
      ;; The fallback needs its own copy: cconv keys on the identity of
      ;; lambda forms, so they must not be shared.
      `(let ((,seq ,(cadr forms)))
         (if (listp ,seq) ,loop (,fn ,(copy-tree fun) ,seq)))))))

(defun elisp-optimizer--simplify-call (fn forms types)
  "Try to rewrite the call (FN . FORMS) whose argument types are TYPES.
Return (FORM . TYPE) or nil."
  (let ((n (length forms))
        (a (car forms)) (b (cadr forms))
        (ta (car types)) (tb (cadr types)))
    (cl-case fn
      ((eq equal eql)
       (when (and (= n 2)
                  (not (eql ta elisp-optimizer--empty))
                  (not (eql tb elisp-optimizer--empty)))
         (cond
          ;; Disjoint-type equality folding is absent from byte-opt.el
          ;; (byte-optimize-binary-predicate only evaluates when both
          ;; operands are literal constants, not inferred types).
          ((eql (logand ta tb) elisp-optimizer--empty)
           (elisp-optimizer--note 'fold-disjoint-equality (cons fn forms))
           (elisp-optimizer--fold forms nil))
          ;; Note: byte-opt.el (byte-optimize-equal) already rewrites
          ;; equal/eql -> eq when an operand is a literal constant symbol
          ;; or fixnum. We keep this rewrite because it also applies when an
          ;; operand is an inferred eq-safe variable or declaration.
          ((and (not (eq fn 'eq))
                (or (elisp-optimizer--subtype-p ta elisp-optimizer--eq-safe)
                    (elisp-optimizer--subtype-p tb elisp-optimizer--eq-safe)))
           (elisp-optimizer--note 'equal-to-eq (cons fn forms))
           (cons `(eq ,a ,b) elisp-optimizer--boolean)))))
      (=
       ;; Fixnum = -> eq is absent from byte-opt.el (byte compiler emits byte-eql).
       (when (and (= n 2)
                  (elisp-optimizer--subtype-p ta elisp-optimizer--fixnum)
                  (elisp-optimizer--subtype-p tb elisp-optimizer--fixnum))
         (elisp-optimizer--note 'fixnum-compare (cons fn forms))
         (cons `(eq ,a ,b) elisp-optimizer--boolean)))
      (zerop
       ;; zerop compiler-macro expands to (= 0 x); byte-opt.el does not turn (= 0 x) to eq.
       (when (and (= n 1)
                  (elisp-optimizer--subtype-p ta elisp-optimizer--fixnum))
         (elisp-optimizer--note 'fixnum-compare (cons fn forms))
         (cons `(eq ,a 0) elisp-optimizer--boolean)))
      ((+ * - logand logior)
       ;; byte-opt.el does not drop identity operands (it must keep the
       ;; type error for non-numbers); with an integer operand we can.
       (let ((int (logior elisp-optimizer--fixnum elisp-optimizer--bignum))
             (id (cl-case fn ((+ - logior) 0) (* 1) (logand -1))))
         (cond
          ((and (= n 2) (eql b id)
                (elisp-optimizer--subtype-p ta int))
           (elisp-optimizer--note 'identity-operand (cons fn forms))
           (cons a ta))
          ((and (= n 2) (eql a id) (memq fn '(+ * logand logior))
                (elisp-optimizer--subtype-p tb int))
           (elisp-optimizer--note 'identity-operand (cons fn forms))
           (cons b tb)))))
      ((member assoc)
       ;; Note: byte-opt.el already rewrites member/assoc -> memq/assq when
       ;; the key is a literal constant symbol or fixnum. This pass also
       ;; optimizes inferred eq-safe variables and parameters.
       (when (and (= n 2)
                  (elisp-optimizer--subtype-p ta elisp-optimizer--eq-safe))
         (elisp-optimizer--note 'search-to-eq (cons fn forms))
         (cons (list (if (eq fn 'member) 'memq 'assq) a b) elisp-optimizer--list)))
      (delete
       ;; delete -> delq is completely absent from byte-opt.el (even for literals).
       (when (and (= n 2)
                  (elisp-optimizer--subtype-p ta elisp-optimizer--eq-safe)
                  (elisp-optimizer--subtype-p tb elisp-optimizer--list))
         (elisp-optimizer--note 'search-to-eq (cons fn forms))
         (cons `(delq ,a ,b) elisp-optimizer--list)))
      ((mapcar mapc)
       (when (and elisp-optimizer-inline-mapping
                  (= n 2) (not (eql tb elisp-optimizer--empty)))
         (let ((new (elisp-optimizer--inline-mapping
                     fn forms (elisp-optimizer--subtype-p
                               tb elisp-optimizer--list))))
           (when new
             (elisp-optimizer--note 'inline-mapping (cons fn forms))
             (cons new (if (eq fn 'mapcar) elisp-optimizer--list
                         elisp-optimizer--top))))))
      (t
       ;; Type predicates with a known answer.
       (let ((pred (cdr (assq fn elisp-optimizer--predicates))))
         (when (and pred (= n 1) (not (eql ta elisp-optimizer--empty)))
           (cond ((and (/= (cdr pred) elisp-optimizer--empty)
                       (eql (logand ta (lognot (cdr pred))) elisp-optimizer--empty))
                  (elisp-optimizer--note 'fold-predicate (cons fn forms))
                  (elisp-optimizer--fold forms t))
                 ((eql (logand ta (car pred)) elisp-optimizer--empty)
                  (elisp-optimizer--note 'fold-predicate (cons fn forms))
                  (elisp-optimizer--fold forms nil)))))))))

(defun elisp-optimizer--call-type (fn forms)
  "Return the result type mask of the call (FN . FORMS)."
  (let* ((user (assq fn elisp-optimizer-function-types))
         (inferred (and elisp-optimizer--inferred-types
                        (gethash fn elisp-optimizer--inferred-types)))
         (base (cond (user (elisp-optimizer--spec-mask (cdr user)))
                     (inferred inferred)
                     ((eq fn 'list)
                      (if forms elisp-optimizer--cons elisp-optimizer--null))
                     ((assq fn elisp-optimizer--result-types)
                      (cdr (assq fn elisp-optimizer--result-types)))
                     ((assq fn elisp-optimizer--predicates)
                      elisp-optimizer--boolean)
                     (t elisp-optimizer--top))))
    (when elisp-optimizer-type-functions
      (dolist (f elisp-optimizer-type-functions)
        (let ((spec (funcall f (cons fn forms))))
          (when spec
            (let ((m (logand base (elisp-optimizer--spec-mask spec))))
              (unless (eql m elisp-optimizer--empty) (setq base m)))))))
    base))

(defun elisp-optimizer--walk-call (form env)
  (let* ((fn (car form))
         (rs (mapcar (lambda (a) (elisp-optimizer--walk a env)) (cdr form)))
         (forms (mapcar #'car rs))
         (types (mapcar #'cdr rs)))
    (or (elisp-optimizer--simplify-call fn forms types)
        (cons (cons fn forms) (elisp-optimizer--call-type fn forms)))))

;;;; Entry points

(defun elisp-optimizer--collect-setqs (form)
  "Return a hash table of the symbols assigned by `setq' anywhere in FORM."
  (let ((tbl (make-hash-table :test #'eq))
        (seen (make-hash-table :test #'eq))
        (stack (list form)))
    (while stack
      (let ((x (pop stack)))
        (when (and (consp x) (not (gethash x seen)))
          (puthash x t seen)
          (when (eq (car x) 'setq)
            (let ((p (cdr x)))
              (while (consp p)
                (when (symbolp (car p)) (puthash (car p) t tbl))
                (setq p (and (consp (cdr p)) (cddr p))))))
          (push (car x) stack)
          (push (cdr x) stack))))
    tbl))

(defun elisp-optimizer-optimize-form (form &optional dynbound-vars)
  "Return the optimized version of the macroexpanded FORM.
DYNBOUND-VARS are variables to be treated as dynamically bound."
  (let ((elisp-optimizer--setqs (elisp-optimizer--collect-setqs form))
        (elisp-optimizer--dynbound dynbound-vars)
        (elisp-optimizer--inferred-types (or elisp-optimizer--inferred-types
                                            (make-hash-table :test #'eq))))
    (car (elisp-optimizer--walk form nil))))

(defvar elisp-optimizer--failed nil
  "Non-nil once an internal error has been reported.")

(defun elisp-optimizer--filter-args (args)
  "Advice for `cconv-closure-convert': optimize its FORM argument."
  (if (not (and byte-optimize (consp (car args))))
      args
    (condition-case err
        (cons (elisp-optimizer-optimize-form (car args) (cadr args))
              (cdr args))
      (error
       (unless elisp-optimizer--failed
         (setq elisp-optimizer--failed t)
         (message "elisp-optimizer: internal error, form left alone: %S" err))
       args))))

;;;###autoload
(define-minor-mode elisp-optimizer-mode
  "Toggle type-aware optimizations in the Emacs Lisp byte compiler.

While enabled, every form the byte compiler processes is first run
through `elisp-optimizer-optimize-form'.  Turn the mode off after the
compilation; it leaves nothing behind in the compiled files."
  :global t
  :group 'elisp-optimizer
  (if elisp-optimizer-mode
      (progn
        (setq elisp-optimizer--stats nil
              elisp-optimizer--failed nil
              elisp-optimizer--inferred-types (make-hash-table :test #'eq))
        (advice-add 'cconv-closure-convert :filter-args
                    #'elisp-optimizer--filter-args))
    (setq elisp-optimizer--inferred-types nil)
    (advice-remove 'cconv-closure-convert #'elisp-optimizer--filter-args)))

(defun elisp-optimizer-call-with-mode (thunk)
  "Call THUNK with `elisp-optimizer-mode' enabled, then restore the mode."
  (let ((was elisp-optimizer-mode))
    (unwind-protect
        (progn (elisp-optimizer-mode 1) (funcall thunk))
      (elisp-optimizer-mode (if was 1 -1)))))

(defmacro elisp-optimizer-with-optimizations (&rest body)
  "Evaluate BODY with `elisp-optimizer-mode' temporarily enabled."
  (declare (indent 0))
  `(elisp-optimizer-call-with-mode (lambda () ,@body)))

;;;###autoload
(defun elisp-optimizer-byte-compile-file (file &optional load)
  "Byte compile FILE with the optimizer enabled.  Optionally LOAD it."
  (interactive "fByte compile file: ")
  (require 'bytecomp)
  (let ((ok (elisp-optimizer-with-optimizations (byte-compile-file file))))
    (when (and ok load)
      (load (byte-compile-dest-file file) nil nil t))
    (when (called-interactively-p 'any) (elisp-optimizer-report))
    ok))

;;;###autoload
(defun elisp-optimizer-batch-byte-compile ()
  "Like `batch-byte-compile' but with the optimizer enabled."
  (require 'bytecomp)
  (elisp-optimizer-with-optimizations
    (unwind-protect (batch-byte-compile)
      (elisp-optimizer-report))))

(defun elisp-optimizer-report ()
  "Show how many rewrites of each kind were done by the optimizer."
  (interactive)
  (let ((text (if elisp-optimizer--stats
                  (mapconcat (lambda (c) (format "%s: %d" (car c) (cdr c)))
                             (sort (copy-sequence elisp-optimizer--stats)
                                   (lambda (x y) (string< (car x) (car y))))
                             ", ")
                "no rewrites")))
    (message "elisp-optimizer: %s" text)))

(defun elisp-optimizer-unload-function ()
  "Remove the advice when the feature is unloaded."
  (advice-remove 'cconv-closure-convert #'elisp-optimizer--filter-args)
  nil)

(provide 'elisp-optimizer)
;;; elisp-optimizer.el ends here
