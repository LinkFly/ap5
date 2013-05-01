;-*- Mode:LISP; Package:AP5; Base:10.; Syntax:Common-Lisp -*-
(in-package "AP5")
;
; commonlisp compatible approximations of try and fail
;
;; used to catch and throw multiple values

(defvar *failure* nil)
; We record the last failure because the commonlisp manual does not
; require that values of uncaught throws be accessible.

(declaim (special trystack))
(setq trystack nil)

(defun throw1 (x y) ;; something to appear on the stack and be traceable 2012/03/11
  (throw x y))

(defmacro-displace fail (tag &rest values)
  (cond ((symbolp tag) (setq tag (kwote tag)))
	((and (listp tag)
	      (eq (car tag) 'quote)
	      (symbolp (cadr tag))))
	(t (error "bad throw tag ~A" tag)))
  `(progn (setq *failure* (list 'fail-marker ,@values))
	  (if (member ,tag trystack :test #'equal)
	      (throw1 ,tag *failure*)
	      (error "uncaught failure of type ~A:~&~A" ,tag (cdr *failure*)))))

#+ignore  ;; doesn't handle multiple-valued forms
(defmacro-displace try (form tag &rest code)
  (setq tag
	(cond ((symbolp tag) (kwote tag))
	      ((and (listp tag)
		    (eq (car tag) 'quote)
		    (symbolp (cadr tag)))
	       tag)			; allow either foo or 'foo why why why????
	      (t (Error "bad catch tag ~A" tag))))
  `(let* ((trystack (cons ,tag trystack))
	  (tryvalue
	   (catch ,tag ,form)))
     (cond ((eq (car (ilistp tryvalue)) 'fail-marker)
	    ;; you really want one protocol for direct THROWs and
            ;; something else for throws expressed through FAIL?
	    (setq tryvalue (cdr tryvalue))
	    ,@code)
	   (t tryvalue))))
(defun catch1 (tag form) ;; to be able to trace and see on stack 2012/03/11
  (catch tag (funcall form)))
(defmacro try (form tag &rest code)
  (setf tag
	(cond ((symbolp tag) (kwote tag))
	      ((and (listp tag)
		    (eq (car tag) 'quote)
		    (symbolp (second tag)))
	       tag) ; allow either foo or 'foo why why why????
              ;; so you can write (try (foo) tag (code)) instead of 'tag
              ;; this is a macro, after all
	      (t (Error "bad catch tag ~A" tag))))
  `(multiple-value-call
    #'(lambda (&rest tryvalue)
        (cond ((eq (car (ilistp (first tryvalue))) 'fail-marker)
               ;; you really want one protocol for direct THROWs and
               ;; something else for throws expressed through FAIL?
               (setf tryvalue (rest (first tryvalue)))
               ,@code)
              (t (values-list tryvalue))))
    ;; 2012/03/11
    ;; trystack must NOT be bound during code since that can do another fail
    (let ((trystack (cons ,tag trystack)))
      (catch1 ,tag (lambda (),form)))))

; this seems related ...
(Defvar-resettable goals nil)
(defmacro with-goal (goal &rest body)
  `(let ((goals (cons ,goal goals))) ,.body))
