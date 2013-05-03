;-*- Mode: LISP; Package: AP5; Base:10.; Syntax: Common-lisp -*-
(in-package "AP5")

#|
A binary relation (or description) R is called a partial-order if it
satisfies the following axioms:
   non-reflexive -- (not (E (x) (R x x)))
   transitive -- (A (x y z) (implies (and (R x y) (R y z)) (R x z)))

The macros documented below provide an expression language, within AP5,
for defining partial orders out of other partial orders.

Inverse-Order[ordering-expression]
Priority-Order[ordering-expression+]
Image-Order[ordering-expression image-relation]
Lexicographic-Order[ordering-expression]
Order-By-Class[class-expression &optional ordering-expression]
Literal-Order[equivalence &rest values]

Description[description]

Partial-Order-Sort[list ordering-relation]
Partial-Order-Merge[result-type list1 list2 ordering-relation]
|#

(defmacro description (d &environment e)
  `(quote ,(macroexpand d e)))

;; the inverse of an order
(defmacro INVERSE-ORDER (O &environment e)
  (let ((x '|x|) (y '|y|))
    `((,x ,y) s.t. (,(macroexpand O e) ,y ,x))))

;; a "priority" ordering (O1 ... On) Oi is used be break ties
;; for O1 ...Oi-1
(defmacro PRIORITY-ORDER (F1 &rest FR &environment e)
  (let ((ef1 (macroexpand F1 e)))
    (if FR
	(let ((x '|x|) (y '|y|))
	  `((,x ,y) s.t. (or (,ef1 ,x ,y)
			     (and (not (,ef1 ,y ,x))
				  (,(macroexpand-1 `(PRIORITY-ORDER ,. FR) e)
				   ,x ,y)))))
      ef1)))

;; derive an ordering from another ordering on an image
(defmacro IMAGE-ORDER (O image-rel &environment e)
  (let ((x '|x|) (y '|y|) (xi '|xi|) (yi '|yi|) oo)
    (setf oo (macroexpand O e))
    `((,x ,y) s.t. (E (,xi ,yi) (and (,image-rel ,x ,xi)
				     (,image-rel ,y ,yi)
				     (,oo ,xi ,yi))))))

;; for orderings on sets whose elements are SEQUENCES,
;; order 2 members by lexicographic ordering of their elements
(defmacro Lexicographic-Order (O &environment e)
  (let ((x '|x|) (y '|y|))
    `((,X ,Y) s.t. (LEX*FN ,X ,Y (description ,(macroexpand O e))))))

(defun LEX*FN (seq1 seq2 ORDERING)
  (map nil  #'(lambda (e1 e2)
		(when (testrel ORDERING e1 e2)
		  (return-from LEX*FN t))
		(when (testrel ORDERING e2 e1)
		  (return-from LEX*FN nil)))
	  seq1 seq2)
    ; elements are pairwise equal through shorter list -- return the shorter
    (< (length seq1) (length seq2)))

(defrelation LEX*FN :arity 3  :computation (lisp-predicate LEX*FN)
	     :equivs (equal equal :default)
	     :types (sequence sequence))

;; order by a unary relation
(defmacro order-by-class (C &optional tiebreaker &environment e)
  (let ((x '|x|) (y '|y|))
    `((,x ,y) s.t. (and (,c ,x)
			(or (not (,c ,y))
			    ,(if tiebreaker
				 `(,(macroexpand tiebreaker e) ,x ,y)
			       'false))))))

(defmacro Literal-Order (equiv &rest values &aux (x '|x|) (y '|y|))
  `((,x ,y) s.t. (precedes-in-sequence ,x ,y ',(copy-list values)
				   (description ,equiv))))

(defun precedes-in-sequence (x y l equiv-rel)
  (map nil #'(lambda (item)
	       (cond ((testrel equiv-rel x item) 
		      (return-from precedes-in-sequence (not (testrel equiv-rel y item))))
		     ((testrel equiv-rel y item) 
		      (return-from precedes-in-sequence nil))))
       l)
  nil)

(defrelation precedes-in-sequence :arity 4
	     :computation (lisp-predicate precedes-in-sequence)
	     :types (entity entity sequence relation)
	     :equivs (:default :default equal :default)
	     )

;;; as with MEMBER, we can't really express a correct equivalence signature
;;; for slots 0 and 1

(defun partial-order-sort (L  ORDERING &rest keys &key key)
  (declare (ignore key))
  (apply #'SORT L #'(LAMBDA (X Y) (?? funcall ordering x y)) keys))

(defun partial-order-stable-sort  (L  ORDERING &rest keys &key key)
  (declare (ignore key))
  (apply #'STABLE-SORT L #'(LAMBDA (X Y) (?? funcall ordering x y)) keys))

(defun partial-order-merge  (result-type L1 L2 ORDERING &rest keys &key key)
  (declare (ignore key))
  (apply #'MERGE result-type L1 L2
	 #'(LAMBDA (X Y) (?? funcall ordering x y))
	 keys))

(defrelation arbitrary< :arity 2
	     :computation (lisp-predicate arbitrary-compare))


;;; NIL < other symbols < strings  < numbers < dbobjects < atom < cons
;;; strings and symbols ordered by string< on print name
;;; numbers ordered by <
;;; dbobjects ordered by their unique-id property
;;; conses ordered recursively by car then cdr

#|(defrelation unordered :inline t
	     :definition ((x y) s.t. (ignore-vars (x y) false)))|#
(defrelation false :arity 0)
(defrelation unordered :inline t
	     :definition ((x y) s.t. (ignore-vars (x y) (false))))



