;;; -*- Mode: Lisp; Package:AP5; Syntax:COMMON-LISP; Base:10 -*-

(in-package "AP5")
;;----------------  INSTANCE SLOTS ----------------

(defun slot (name keys slot-name)
  (warn-ignored-keys name keys (:arity :adder :deleter :tester)
    `(:representation stored-in-place :arity 2
         :alsofns
         ,(cons `(lambda (rel) (++ Stored-where rel
				   ,(stored-in-slot-placer slot-name nil)))
		(getf keys :alsofns))
	 ,.keys)))

(defun slot-single (name keys slot-name)
  (warn-ignored-keys name keys (:arity :adder :deleter :tester)
    `(:representation stored-in-place-single :arity 2
	    :alsofns
	    ,(cons `(lambda (rel) (++ Stored-where rel
				      ,(stored-in-slot-placer slot-name t)))
		   (getf keys :alsofns))
	    :size ,(cons '(input output) (cons 1 (getf keys :size)))
	    ,.keys)))

(defun stored-in-slot-placer (slot-name missing-is-unbound)
  `(FUNCTIONAL-EQUIVALENCE-TESTABLE
    ,(cond (missing-is-unbound
	    `#'(lambda (obj equiv) (declare (ignore equiv))
		       `(slot-value-check-bound ,obj ',',slot-name )))
	  (t `#'(lambda (obj equiv) (declare (ignore equiv))
		       `(slot-value ,obj ',',slot-name ))))
  '(stored-in-slot-placer ,slot-name ,missing-is-unbound)))


(defmethod slot-value-check-bound (obj slot-name)
  (if (slot-boundp obj slot-name)
      (slot-value obj slot-name)
      *no-single-value-stored*))

(defmethod (setf slot-value-check-bound) (new obj slot-name)
  (if (eq new *no-single-value-stored*)
      (slot-makunbound obj slot-name)
      (setf (slot-value obj slot-name) new)))

