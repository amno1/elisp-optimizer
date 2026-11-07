;;; elisp-optimizer-tests.el --- Tests for elisp-optimizer  -*- lexical-binding: t; -*-

;;; Code:

(require 'ert)
(require 'cl-lib)
(require 'bytecomp)
(require 'elisp-optimizer)

(defun eo-test--opt (form)
  "Macroexpand and optimize FORM."
  (elisp-optimizer-optimize-form (macroexpand-all form)))

(defmacro eo-test--should-opt (form expected)
  `(should (equal (eo-test--opt ',form) (macroexpand-all ',expected))))

(ert-deftest eo-fold-if-literals ()
  (eo-test--should-opt (lambda () (if 1 'a 'b)) (lambda () 'a))
  (eo-test--should-opt (lambda () (if nil 'a 'b)) (lambda () 'b)))

(ert-deftest eo-fold-known-types ()
  (eo-test--should-opt (lambda () (let ((x 5)) (if (stringp x) 'a 'b)))
                       (lambda () (let ((x 5)) 'b)))
  (eo-test--should-opt (lambda () (let ((x (length "abc"))) (integerp x)))
                       (lambda () (let ((x (length "abc"))) t))))

(ert-deftest eo-narrowing-and-redundant-checks ()
  (eo-test--should-opt
   (lambda (x) (when (consp x) (if (consp x) 1 2)))
   (lambda (x) (if (consp x) 1)))
  (eo-test--should-opt
   (lambda (x) (cl-check-type x integer) (when (integerp x) 'yes))
   (lambda (x) (progn (or (integerp x) (signal 'wrong-type-argument
                                               (list 'integer x 'x)))
                      nil)
     'yes)))

(ert-deftest eo-setq-blocks-narrowing ()
  (let ((form '(lambda (x) (when (consp x) (setq x 1) (if (consp x) 1 2)))))
    (should (equal (eo-test--opt form) (macroexpand-all form)))))

(ert-deftest eo-equal-to-eq ()
  (eo-test--should-opt (lambda (x) (when (symbolp x) (equal x 'foo)))
                       (lambda (x) (if (symbolp x) (eq x 'foo))))
  (eo-test--should-opt (lambda (a b) (equal a b)) (lambda (a b) (equal a b)))
  (eo-test--should-opt (lambda (s) (when (stringp s) (equal s 'foo)))
                       (lambda (s) (if (stringp s) nil))))

(ert-deftest eo-search-to-eq ()
  (eo-test--should-opt (lambda (l) (member 'a l)) (lambda (l) (memq 'a l)))
  (eo-test--should-opt (lambda (l) (assoc 3 l)) (lambda (l) (assq 3 l)))
  (eo-test--should-opt (lambda (l) (when (listp l) (delete :k l)))
                       (lambda (l) (if (listp l) (delq :k l))))
  (eo-test--should-opt (lambda (l) (member "a" l)) (lambda (l) (member "a" l))))

(ert-deftest eo-fixnum-comparisons ()
  (should (equal (elisp-optimizer--simplify-call 'zerop '(x) (list elisp-optimizer--fixnum))
                 (cons '(eq x 0) elisp-optimizer--boolean)))
  (eo-test--should-opt (lambda () (let ((x (length "a"))) (= x 0)))
                       (lambda () (let ((x (length "a"))) (eq x 0))))
  (eo-test--should-opt (lambda () (let ((x (length "a")) (y (length "b"))) (= x y)))
                       (lambda () (let ((x (length "a")) (y (length "b"))) (eq x y)))))

(ert-deftest eo-constants-and-accessors ()
  (should (= elisp-optimizer--empty 0))
  (should (eq (elisp-optimizer--truth elisp-optimizer--empty) nil))
  (should (eq (elisp-optimizer--truth elisp-optimizer--null) 'false))
  (should (eq (elisp-optimizer--truth elisp-optimizer--true) 'true))
  (should (eq (elisp-optimizer--truth elisp-optimizer--fixnum) 'true))
  (should (elisp-optimizer--subtype-p elisp-optimizer--fixnum elisp-optimizer--top))
  (should-not (elisp-optimizer--subtype-p elisp-optimizer--empty elisp-optimizer--top)))

(ert-deftest eo-inline-mapping ()
  ;; Known list: no call to mapcar and no guard.
  (let ((out (eo-test--opt '(lambda () (mapcar (lambda (x) (1+ x)) (list 1 2))))))
    (should-not (string-match-p "mapcar\\|listp" (prin1-to-string out)))
    (should (equal (funcall (byte-compile out)) '(2 3))))
  ;; Unknown type: guarded, with the original call as the fallback.
  (let ((out (eo-test--opt '(lambda (s) (mapcar (lambda (x) x) s)))))
    (should (string-match-p "listp" (prin1-to-string out)))
    (should (string-match-p "mapcar" (prin1-to-string out)))))

(ert-deftest eo-inline-mapping-hardening ()
  ;; Lexical binding nil: primitives still inline, lambdas do not.
  (let ((lexical-binding nil))
    (let ((out-subr (eo-test--opt '(lambda (s) (mapcar #'car s))))
          (out-quote (eo-test--opt '(lambda (s) (mapcar 'car s))))
          (out-lam (eo-test--opt '(lambda (s) (mapcar (lambda (x) x) s)))))
      (should (string-match-p "while" (prin1-to-string out-subr)))
      (should (string-match-p "while" (prin1-to-string out-quote)))
      (should-not (string-match-p "while" (prin1-to-string out-lam)))))
  ;; Size limit boundary: at limit 0, lambda body not duplicated, primitive still inlined.
  (let ((elisp-optimizer-inline-size-limit 0))
    (let ((out-lam (eo-test--opt '(lambda (s) (mapcar (lambda (x) (1+ x)) s))))
          (out-subr (eo-test--opt '(lambda (s) (mapcar #'car s)))))
      (should-not (string-match-p "while" (prin1-to-string out-lam)))
      (should (string-match-p "while" (prin1-to-string out-subr))))))

(ert-deftest eo-inline-mapping-semantics ()
  (elisp-optimizer-with-optimizations
    (let ((f (byte-compile (lambda (s k) (mapcar (lambda (x) (+ x k)) s))))
          (g (byte-compile (lambda (s) (let (acc) (mapc (lambda (x) (push x acc)) s)
                                            acc))))
          (h (byte-compile (lambda (s) (mapcar #'car s)))))
      (should (equal (funcall f '(1 2 3) 10) '(11 12 13)))
      (should (equal (funcall f [1 2 3] 10) '(11 12 13)))
      (should (equal (funcall f nil 10) nil))
      (should (equal (funcall g '(1 2 3)) '(3 2 1)))
      (should (equal (funcall g "ab") '(?b ?a)))
      (should (equal (funcall h '((1) (2))) '(1 2)))
      ;; Same errors as the C implementation.
      (should (equal (should-error (funcall f '(1 2 . 3) 0))
                     (should-error (mapcar (lambda (x) x) '(1 2 . 3)))))
      (let ((l (list 1 2)))
        (setcdr (cdr l) l)
        (should (eq (car (should-error (funcall f l 0))) 'circular-list)))
      ;; The length is fixed up front, as in `mapcar'.
      (let* ((l (list 1 2 3)) (n 0))
        (funcall (byte-compile (lambda (l) (mapc (lambda (x) (when (= x 1) (nconc l (list 9)))) l))) l)
        (should (equal l '(1 2 3 9)))
        (setq n (length (funcall f l 0)))
        (should (= n 4))))))

(ert-deftest eo-side-effects-kept ()
  (eo-test--should-opt (lambda () (if (progn (message "hi") t) 'a 'b))
                       (lambda () (progn (message "hi") 'a))))

(ert-deftest eo-declare-parameter-types ()
  (eo-test--should-opt
   (lambda (x) (declare (type integer x)) (if (integerp x) 1 2))
   (lambda (x) (declare (type integer x)) 1))
  (eo-test--should-opt
   (lambda (x y) (declare (type (function (integer string) boolean))) (if (stringp y) x 999))
   (lambda (x y) (declare (type (function (integer string) boolean))) x))
  (eo-test--should-opt
   (lambda (x) (declare (et (x Integer))) (if (integerp x) 'yes 'no))
   (lambda (x) (declare (et (x Integer))) 'yes))
  (eo-test--should-opt
   (lambda (x) (declare (type integer x)) (cl-the integer x) 'ok)
   (lambda (x) (declare (type integer x)) 'ok)))

(ert-deftest eo-infer-defun-result-types ()
  (let ((out (eo-test--opt
              '(progn
                 (defun my-len (x) (length x))
                 (defun check (x) (if (stringp (my-len x)) "string" "not-string"))))))
    (should-not (string-match-p "\"string\"" (prin1-to-string (caddr out))))
    (should (string-match-p "\"not-string\"" (prin1-to-string (caddr out))))))

(ert-deftest eo-mode-installs-and-removes-advice ()
  (should-not (advice-member-p #'elisp-optimizer--filter-args
                               'cconv-closure-convert))
  (elisp-optimizer-with-optimizations
    (should (advice-member-p #'elisp-optimizer--filter-args
                             'cconv-closure-convert)))
  (should-not (advice-member-p #'elisp-optimizer--filter-args
                               'cconv-closure-convert)))

(ert-deftest eo-compiled-behaviour ()
  (elisp-optimizer-with-optimizations
    (let ((f (byte-compile
              (lambda (x)
                (cond ((stringp x) (concat "s" x))
                      ((integerp x) (if (stringp x) 'never (1+ x)))
                      ((memq x '(a b)) (if (equal x 'a) 'is-a 'is-b))
                      (t (mapcar (lambda (y) (* y 2)) (if (listp x) x nil))))))))
      (should (equal (funcall f "a") "sa"))
      (should (equal (funcall f 4) 5))
      (should (eq (funcall f 'a) 'is-a))
      (should (eq (funcall f 'b) 'is-b)))))

(provide 'elisp-optimizer-tests)
;;; elisp-optimizer-tests.el ends here

(ert-deftest eo-defun-and-mapc-identity ()
  "Real `defun's are optimized; `mapc' of `identity' keeps only the walk."
  (let* ((form '(defun eo-test--mi (xs) (mapc #'identity xs)))
         (out (eo-test--opt form))
         (str (prin1-to-string out)))
    (should-not (string-match-p "(car " (replace-regexp-in-string "(consp" "" str)))
    (should (string-match-p "length" str))
    (should (string-match-p "(consp" str))))

(ert-deftest eo-identity-operands ()
  (eo-test--should-opt (lambda (x) (declare (type fixnum x)) (+ x 0))
                       (lambda (x) (declare (type fixnum x)) x))
  (eo-test--should-opt (lambda (x) (declare (type integer x)) (* 1 x))
                       (lambda (x) (declare (type integer x)) x))
  ;; Unknown or float operands must keep the operation.
  (eo-test--should-opt (lambda (x) (+ x 0)) (lambda (x) (+ x 0)))
  (eo-test--should-opt (lambda (x) (declare (type float x)) (* x 1))
                       (lambda (x) (declare (type float x)) (* x 1))))
