;;;-*- Mode: LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-
;
; --------------- Type Constraints ----------------
(in-package "AP5")

#+symbolics
(eval-when (:compile-toplevel)
  (or (equal (si:undigest (theonly x s.t. (reladder (relationp 'subtype) x)))
	     '(lambda (&rest ignore) (declare (ignore ignore)) 'subtype-adder-temp))
      (error "this file has to be compiled before loading subtyperules")))


(Defun TypeConstraintTrigger (rel arity pos type &aux args)
  (and (integerp arity) (integerp pos) (< -1 pos arity) ;=> (< 0 arity)
       (not (consp rel)) #+ignore (not (consp type))  ; see comments in subrel constraints
       (list 'E
	     (setq args
		   (loop for i below arity collect (pack* 'v i)))
	     `(and ,(cons rel args) (not ,(list type (nth pos args)))))))

(Defun TypeConstraintTriggerP (trigger &aux rel arity pos w args
				       #+ignore type)
  (and (listp trigger) ; absurd to do (?? closed-wff trigger)
       (eq 'E (first trigger))
       (eq-length trigger 3) ; (e vars (and ...))
       (eq-length (setq w (third trigger)) 3) ; (and (r x y) (not (t ..)))
       (eq 'AND (first w))
       (nlistp (setq rel (car (ilistp (second w)))))
       ;; (E vars (and (R . args) ..)
       ;; quantified vars must be some permutation of the args
       ;; ASSUMPTION -- vars does not include any TYPED variables foo#x
       (setq arity (length (setq args (cdr (ilistp (second w))))))
       (eq-length (second trigger) arity)
       (subsetp (second trigger) args)
       (subsetp args (second trigger))
       ;; end of permutation test
       (eq-length (setq w (third w)) 2)  ; (not (t x))
       (eq 'not (first w))
       (eq-length (setq w (second w)) 2)  ; (t vi)
       #+ignore(symbolp (cadr w))
       #+ignore (integerp (setq pos (global:ignore-errors
			     (read-from-string
			       (subseq (symbol-name (cadr w)) 1)))))
       #+ignore(equal trigger
		      (TypeConstraintTrigger rel arity pos (setq type (car w))))
       (setq pos (position (second w) args :test #'eq))
       (list rel (length args) pos (first w))))

(atomic
 (++ codedrelname 'TypeConstraintTrigger
    '((rel arity pos type trigger) s.t.
      (and trigger (equal (TypeConstraintTrigger rel arity pos type) trigger))))
 reveal
 (++ compare-relation (relationp 'typeconstrainttrigger) 4 (relationp 'equal))
 (++ compare-relation (relationp 'typeconstrainttrigger) 1 (dbo relation =))
 (++ compare-relation (relationp 'typeconstrainttrigger) 2 (dbo relation =)))

(simplegenerator '(typeconstrainttrigger rel arity pos type output)
   '(let ((result (typeconstrainttrigger rel arity pos type)))
      (and result (list result))))
(SimpleMultipleGenerator
  '(typeconstrainttrigger output output output output trigger)
  '(let ((result (typeconstrainttriggerp trigger)))
     (and result (list result))))

(++ RelSize (relationp 'TypeConstrainttrigger)
    '(input input input input output)
    1)
(++ RelSize (relationp 'TypeConstrainttrigger)
    '(output output output output input)
    1)


(++ TreePropRelName 'RelationTypeConstraint)
(++ RelSize (relationp 'RelationTypeConstraint) '(input output) 3)
(++ RelSize (relationp 'RelationTypeConstraint) '(output input) 1)

(++ no-trigger
    (canonicalize-trigger
      '((rel rule) s.t.
	(E (TRIGGER ARITY POS TYPE)
	   (AND (PREVIOUSLY (NOT (RELATIONTYPECONSTRAINT REL RULE)))
		(START (RELATIONARITY REL ARITY))
		(CONSISTENCYRULE RULE)
		(RULETRIGGER RULE TRIGGER)
		(TYPECONSTRAINTTRIGGER REL ARITY POS TYPE TRIGGER)
		;(RELATION-IN-DEFN REL RULE)
		;(RELATION-IN-DEFN TYPE RULE)
		)))))
#+ignore ; previous version
(++ No-Trigger
    (canonicalize-trigger
      '((RULE REL TRIGGER ARITY POS TYPE)
	S.T.
	(AND (START (RELATIONARITY REL ARITY))
	     (RULETRIGGER RULE TRIGGER)
	     (TYPECONSTRAINTTRIGGER REL ARITY POS TYPE TRIGGER)
	     (relation-in-defn rel rule)
	     (relation-in-defn type rule)))))
; tell the rule compiler not
; to worry about the previous rules that turn out to be constraints when 
; a new rel is declared

(++ no-trigger
    (canonicalize-trigger
      '((REL RULE)
	S.T.
	(AND (E (TRIGGER ARITY POS TYPE)
		(AND (RELATIONARITY REL ARITY)
		     (RULETRIGGER RULE TRIGGER)
		     (TYPECONSTRAINTTRIGGER REL ARITY POS TYPE TRIGGER)))
	     (PREVIOUSLY (NOT (RELATIONTYPECONSTRAINT REL RULE)))
	     (START (CONSISTENCYRULE RULE))))))
; better to start from ruletrigger

; now get it coordinated with the following defn
;(let ((triggereffortwarning 999999)
;      (triggersizewarning 9999))  ; avoid warnings in loading the system
(++ WffDefn (relationp 'RelationTypeConstraint)
      '((rel rule) s.t.
	(and (ConsistencyRule rule)
	     (E (trigger arity pos type)
		(and (RuleTrigger rule trigger)
		     (relationarity rel arity)
		     (TypeConstraintTrigger rel arity pos type trigger)
		     ; disgusting optimization no longer needed!
		     ; (cause maintaining is now done via the maintainedrel)
		     ;(relation-in-defn rel rule)
		     ;(relation-in-defn type rule)
		     )))));)

(setq TypeConstraintEnforcement :incremental)

(++ definedrelname 'typename
  '((x) s.t. (E (r) (and (relationname r x) (type r)))))
(++ subtype (relationp 'typename) (relationp 'symbol))
(++ reldeleter (dbo relation TYPENAME) 'namedrel-deleter)
(defun typenamep (x) (?? typename x))

(++ definedrelname 'binary-relationname
  '((x) s.t. (E (r) (and (relationname r x) (relationarity r 2)))))
(++ subtype  (relationp 'binary-relationname) (relationp 'symbol))
(++ reldeleter (dbo relation BINARY-RELATIONNAME) 'namedrel-deleter)

(++ codedrelname 'countspec   ;; would like MEMBER as a testable relation
  '((x) s.t. (member x '(:any :multiple :unique :optional :none))))
(simplegenerator '(countspec output) ''(:any :multiple :unique :optional :none))
(++ subtype (relationp 'countspec) (relationp 'symbol))

(++ codedrelname 'enforcement
  '((x) s.t. (member x '(:incremental :total :none))))
(simplegenerator '(Enforcement output) ''(:incremental :total :none))
(++ subtype (relationp 'enforcement) (relationp 'symbol))


(Defun DefTypeConstraint (relation position type
			     &key (enforcement TypeConstraintEnforcement)
			          (repair :remove)
				  (environment *empty-env*)
			     &aux name  code relname)
  (setq relname (cond ((symbolp relation) relation)
		      (t (relationnamep relation)))
	relation (relationp relation)
	type (or (relationp type) type))
  (declare-type  (relation relation) #+ignore(type type) (integer position)
		 (enforcement enforcement))
  (unless (or (?? type type) (cl-type-name type environment)
	      (and (descriptionp type) (eq-length (car type) 1)))
    (fail parameter-type-fault 'type 'type type))
  (unless (<= 0 position (1- (arity* relation)))
    (error "~&constrained position not legitimate~%~
            position ~d of relation ~a"  position relation))
  (setq name (pack* "Typeconstraint-" relname '- position))
  ; *** this is an odd dependence on the relname - if we change the name we lose
  (when (eq type (relationp 'entity))
    (atomic (loop for rule s.t. (rulename rule name) do (-- rule rule)))
    (return-from DefTypeConstraint nil))
  ; the replacing property of the constraints
  (setq code (cond ((or (eq repair :norepair)(eq enforcement :none)) 'ignored)
		   ((eq repair :remove )
		    (FUNCTIONAL-EQUIVALENCE-TESTABLE
		      #'(lambda (&rest args)
			  (common-tc-remove-enforcement relname args))
		      (list :typeconstraint-remove relation)
		      (format nil "typeconstraint-remove-~a-tuple" relname)))
		   (t repair)))
  (atomic
    (apply 'neverpermit 
	     name
	     (TypeConstraintTrigger relation (arity* relation) position type)
	     code Enforcement
	     (when (relationnamep type)
	       (list :reporter
		     (FUNCTIONAL-EQUIVALENCE-TESTABLE
		       (coerce ; not worth compiling
			`(lambda (&rest args)
			    (report-typeconstraint-violation
			     ',relname ,position ',(relationnamep type) args))
			'function)
		       (list :typeconstraint-reporter position relation type)
		       (format nil "report-typeconstraint-violation-~a-~a-~d"
			       relname position (relationnamep type))))))))
; should I perhaps delete any rule that is a typeconstraint for the slot?
; how about subtype constraints?

(defun common-tc-remove-enforcement (relname args)
  (unless (?? start (apply relname args))
    (-- apply relname args)))

(defun report-typeconstraint-violation (rel pos type args)
  (declare (special default-tuple-printer))
  (write-string "Type constraint violation:" *error-output*)
  (terpri *error-output*)
  (apply default-tuple-printer *error-output* rel args)
  (format *error-output* "~& Position ~d is supposed to have type ~A"
	  pos (relationp type)))


(defun find-cached-code-for-rule (rule &aux queue ans next)
  ; returns a list of canon-desc's used by the matchnode of rule
  ; in a bottom up order in which they can be compiled so that
  ; they use the ones earlier defined
  (loop for x s.t. (or (matchconsistency x rule) (matchmaintain x rule) (matchautomation x rule))
	do (pushnew x queue))
  (loop while (setq next (pop queue)) do ;(print (matchcode next))
	(when (symbolp (matchcode next))
	  (loop for x in (get (matchcode next) 'uses-generator) do
		; if it's already there, remove it - we want this to be earlier
		(setq ans (delete x ans :test #'equal))
		(push x ans)))
	(loop for x in (matchpredecessors next) do (pushnew x queue)))
  ans)

(defun make-multiple-type-constraints (relname &rest args)
  (mapc #'(lambda (l) (apply #'deftypeconstraint relname l)) args)
  ; removed atomic - optimization only works outside atomic
  relname)

(atomic
 (++ fullindexrelname 'TypeConstraint-Stored 3)
 reveal
 (++ compare-relation (relationp 'typeconstraint-stored) 1 (dbo relation =)))
(++ relsize (relationp 'typeconstraint-stored) '(input input output) 1)
(++ relsize (relationp 'typeconstraint-stored) '(input output output) 3)
(++ relsize (relationp 'typeconstraint-stored) '(output output output) 1000)

(++ no-trigger
    (canonicalize-trigger
      '((RELATION POSITION TYPE) S.T.
	(E (D TR ARITY)
	   (AND (PREVIOUSLY (NOT (TYPECONSTRAINT-STORED RELATION POSITION TYPE)))
		(START (RELATIONARITY RELATION ARITY))
		(RULETRIGGER D TR)
		(TYPECONSTRAINTTRIGGER RELATION ARITY POSITION TYPE TR)
		(RELATIONTYPECONSTRAINT RELATION D))))))
#+ignore ;old version
(++ no-trigger
    (canonicalize-trigger
      '((RELATION POSITION TYPE D TR ARITY)
	S.T.
	(AND (START (RELATIONARITY RELATION ARITY))
	     (RELATIONTYPECONSTRAINT RELATION D)
	     (RULETRIGGER D TR)
	     (TYPECONSTRAINTTRIGGER RELATION ARITY POSITION TYPE TR)))))

(++ no-trigger
    (canonicalize-trigger
      '((RELATION POSITION TYPE)
	S.T.
	(E (D TR ARITY)
	   (AND (PREVIOUSLY (NOT (TYPECONSTRAINT-STORED RELATION POSITION TYPE)))
		(START (RULETRIGGER D TR))
		(RELATIONARITY RELATION ARITY)
		(TYPECONSTRAINTTRIGGER RELATION ARITY POSITION TYPE TR)
		(RELATIONTYPECONSTRAINT RELATION D))))))
; better to start from relationtypeconstraint

(++ wffdefn (relationp 'typeconstraint-stored)
    '((relation position type) s.t.
      (E (d tr arity) (and (RelationTypeConstraint relation d)
			   (RuleTrigger d tr)
			   (typeconstrainttrigger relation arity position type tr)
			   (relationarity relation arity)))))

(++ DefinedRelName 'TypeConstraint
    '((rel pos type) s.t. (typeconstraint-stored rel pos type)))
#+ignore ; no longer compatible with adder
 (++ inlinerel (relationp 'TypeConstraint))

(++ RelAdder (relationp 'TypeConstraint)
   '(lambda (ignore relation position type) (declare (ignore ignore))
      (typeconstraint-adder relation position type)))
(defun typeconstraint-adder (&rest ignore) (declare (ignore ignore))
  '(lambda (ignore relation position type) (declare (ignore ignore))
     (cond ((?? TypeConstraint relation position type)
	    (Insist "supposed to add it" TypeConstraint relation position type))
	   (t (deftypeconstraint relation position type)))))
;; we give up any hope of compiling it all in because the args are to be eval'd
; (well, actually, I could compile the test)
(++ RelDeleter (relationp 'TypeConstraint)
   '(lambda (ignore relation position type) (declare (ignore ignore))
      (typeconstraint-deleter relation position type)))
(defun typeconstraint-deleter (&rest ignore) (declare (ignore ignore))
  '(lambda (ignore relation position type) (declare (ignore ignore))
     (cond ((?? not (TypeConstraint relation position type))
	    (Insist "supposed to add it" not (TypeConstraint relation position type)))
	   (t (loop for (d tr arity) s.t.
		    (and (RelationTypeConstraint relation d)
			 (RuleTrigger d tr)
			 (typeconstrainttrigger relation arity position type tr)
			 (relationarity relation arity))
		    do (-- consistencyrule d))))))

(Defmacro DefTypeConstraints (;; &environment env
			      &rest args &aux call
		   arg (enforcement TypeConstraintEnforcement) relname #+ignore code-done
		   (pos 0) (repair :remove)
		   passed-args)
  ;args are enforcement keywords interleaved with a list of relname &rest typenames
  ;where :ignore is a special case of a typename meaning no change
  ;also, the keywords :remove, :norepair control the value of the :repair keyword
  ;passed to deftypeconstraint
  (setf passed-args
	(loop while (setf arg (pop args)) nconc
	         (cond ((?? enforcement arg) (setf enforcement arg) nil)
		       ((member arg '(:remove :norepair))
			(setf repair arg)
			nil)
		       ((eq (car (ilistp arg)) :repair)
			(setf repair (cadr arg))
			nil)
		       ((not relname) (setf relname arg) nil)
		       ((eq arg :ignore) (incf pos) nil)
		       (t (setf call
				(list
				  (kwote (list pos arg
					       :enforcement enforcement :repair repair))))
			  ; ** undo history would benefit from (++ typeconstraint ..)
			  ; but that leads us into problems of binding enforcement at
			  ; expand ++ time.
			  #+ignore(cond
			    ((eq enforcement :none))
			    (code-done)
			    (t (push
				 `(compute-typeconstraint-code
				    ,relname
				    ,(loop for i from 0 below
					   (arity* (relationp relname))
					   collect (pack* 'v i))
				    t)
				 call)
			       (setf code-done t)))
			  (incf pos)
			  call))))
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     ,@(let (rule rel type rules)
	 (setf rules (listof x s.t. (relationtypeconstraint
				      (setf rel (relationp relname)) x)))
	 (loop for arglist in passed-args when
	       (and rel (setf arglist (cadr arglist))	; remove quote
		    (setf type (relationp (cadr arglist)))
		    (not (eq (fourth arglist) :none))
		    (?? typeconstraint rel (car arglist) type)
		    (setf rule
			  (loop for r in rules thereis
				(and (?? typeconstrainttrigger
					 rel (arity* rel) (car arglist) type
					 (any x s.t. (ruletrigger r x) ifnone nil))
				     r))))
	       nconc (loop for desc in (find-cached-code-for-rule rule)
			   collect (compile-code-for-desc desc))))
	  (make-multiple-type-constraints
	   ',relname ,.passed-args
	   ;;,.
	   #+ignore
	   (dolist (al passed-args passed-args)
	     ;; al = (quote (...))
	     ;; Rene De Visser claims that nconc here smashes env?
	     #| I don't believe that, but then I also don't see why we
	        need to pass the environment here.  Compiling this macro
	        to file would then require environment objects to be stored
	        in the compiled file. |#
	     (nconc (second al) (list :environment env))))))
