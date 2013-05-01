;-*- Mode:LISP; Package:AP5; Base:10.; Syntax:Common-Lisp -*-
;
; Here's our collection of wff macros...
(in-package "AP5")

(defmacro implies (x y) `(or (not ,x) ,y))

(defmacro equiv (x y) `(and (implies ,x ,y) (implies ,y ,x)))

; xor is (evidently) about to become part of commonlisp
(defmacro nequiv (x y) `(not (equiv ,x ,y)))

(defmacro all (vars wff) `(A ,vars ,wff))

(defmacro exists (vars wff) `(E ,vars ,wff))

(defmacro ~ (wff) (list 'not wff))

(defmacro If-Then-Else (if then else)
  `(or (and ,if ,then) (and (not ,if) ,else)))

(defmacro multiple (Avars Evars wff)
  (unless Evars
    (error "MULTIPLE must have a non-empty set of existential variables~%~s"
	   (list 'multiple Avars Evars wff)))
  `(A ,Avars (E ,Evars ,wff)))

(defmacro OPTIONAL (Avars Evars1 wff &optional canonical-order)
  (unless (and Evars1 (listp evars1))
    (error "OPTIONAL must have a non-empty set of existential variables~%~s"
	   (list 'optional Avars Evars1 wff)))
  (let ((Evars2
	  (mapcar #'(lambda (v)
		       (let ((type (VariableTypeName v)))
			 ; symbolics compiler bug prevents this from being &aux
			 (if type
			     (MakeTypedVariable type nil (symbol-package v))
			     (gentemp (string v) (symbol-package v)))))
		  Evars1)))
    `(A (,@ Avars ,@ Evars1 ,. Evars2)
	(IMPLIES
	  (AND ,wff ,(subst-free-in-wff
		       (pairlis Evars1 (vars-to-names Evars2)) wff)
	       ,.(when canonical-order
		   (loop for v1 in Evars1 as v2 in Evars2 collect
			 `(arbitrary-order ,(variablename v1) ,(variablename v2)))))
	  ,(let ((equalities
		   (loop with wff-equality = (Equality-relations Evars1 wff)
			 for ev1 in Evars1 as ev2 in Evars2
			 collect (list (which-equality (variablename ev1) wff-equality)
				       (variablename ev1) (variablename ev2)))))
	     (if (cdr equalities) (cons 'AND equalities) (car equalities)))))))


(defun which-equality (var table &aux entry)
  (or (setq entry (car (member var table :test #'(lambda (x y) (eql x (varname y))))))
      (error "~s not in the variable table" var))
  (cond ((not (listp (setq entry (varcompare entry)))) (relationnamep entry))
	((null entry) (error "~s has no comparison relation in table" var))
	((cdr entry) (error "~s has multiple comparison relations" var ))
	(t (relationnamep (car entry)))))

(defun Equality-relations (vars1 wff) ;;vars1 wff nil) ;*** to be expanded
  (first (expanddescription `(,vars1 s.t. ,wff)
		       :allowevalargs t
		       :keepstarts t))) ; just get the digested vars

(defun MakeTypedVariable (TypeName &optional varname
			                     (pkg (symbol-package TypeName)))
  (if varname
      (intern (concatenate 'string (string TypeName) "#" (string varname)) pkg)
    (gentemp (concatenate 'string (string TypeName) "#G") pkg)))

(defmacro change (vars w &aux tname)
  ; translates into (E vars' (or (start w') (start (not w'))))
  ; where vars' and w' account for typed entries in vars
  (cond ((loop for v in vars thereis (variabletypename v))
	 (setq w `(and ,.(loop for v in vars
			       when (setq tname (variabletypename v))
			       collect (list tname (variablename v)))
		       ,w)
	       vars (loop for v in vars collect (variablename v)))))
  (if vars
      `(E ,vars (or (start ,w) (start (not ,w))))
      `(or (start ,w) (start (not ,w)))))

; We avoid calling expand... so as to make this relation independent of other data
; such as the defns of the rels involved or even whether they're defined.
; unfortunately(?), this fn can map two inputs to the same output.

; this is a sort of anti-wff macro - makes previously available to non-wffs
(defmacro previously (&rest forms)
  `(let (delta) (check2states 'previous-macro) ,@forms))