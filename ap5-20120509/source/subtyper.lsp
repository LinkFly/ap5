;;;-*- Mode: LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-
;
; ---------------- SubRel ----------------
(in-package "AP5")

(Defun SubRelTrigger (SubRel SuperRel arity &aux vars)
  (setq vars (loop for i below arity collect (pack* 'v i)))
  `(E ,vars (and ,(cons SubRel vars) (not ,(cons SuperRel vars)))))

(Defun SubRelTriggerP (trigger &aux part sub super arity)
  (and (eq-length trigger 3)  ; (E vars (and ...))
       (eq-length (setq part (third trigger)) 3) ; (and (r1 ...) (not (r2 ...)))
       (nlistp (setq sub (car (ilistp (cadr part))))) ; r1
       (eq-length (setq part (third part)) 2) ; (not (r2 ...))
       (nlistp (setq super (car (setq part (ilistp (second part))))))
       (< 0 (setq arity (length (cdr part))))
       (equal trigger (SubRelTrigger sub super arity))
       (list sub super arity)))

(atomic
 (++ CodedRelName 'SubRelTrigger
    '((sub super arity trigger) s.t.
      (and (nlistp sub) (nlistp super) (integerp arity) (< 0 arity)
	   (equal trigger (subreltrigger sub super arity)))))
 reveal
 (++ compare-relation (relationp 'subreltrigger) 2 (dbo relation =)))

; need nlistp's so that we can leave the comparison relation at eql
; if it were equal we wouldn't be able to use variables for relation objects
; (since most other places that use them expect to compare with eql)
; without nlistp, we couldn't generate the sub,super,arity from trigger

(++ compare-relation (relationp 'subreltrigger) 3 (relationp 'equal))

; probably could have used lisp-function implementation for this ...
(SimpleGenerator '(SubRelTrigger sub super arity output)
  '(and (nlistp sub) (nlistp super) (nlistp arity)
	(list (subreltrigger sub super arity))))
(SimpleMultipleGenerator
  '(SubRelTrigger output output output trigger)
  '(let ((result (SubRelTriggerP trigger)))
     (and result (list result))))

(++ RelSize (relationp 'SubRelTrigger) '(output output output input) 1)
(++ RelSize (relationp 'SubRelTrigger) '(input input input output) 1)


(++ FullIndexRelname 'SubRelationConstraint 3)

(++ no-trigger
    (canonicalize-trigger
      '((RULE SUB SUPER) S.T.
	(E (TRIGGER ARITY)
	   (AND (NOT (PREVIOUSLY (SUBRELATIONCONSTRAINT RULE SUB SUPER)))
		(START (RELATIONARITY SUB ARITY))
		(RELATIONARITY SUPER ARITY)
		(RULETRIGGER RULE TRIGGER)
		;(RELATION-IN-DEFN SUB RULE)
		;(RELATION-IN-DEFN SUPER RULE)
		(SUBRELTRIGGER SUB SUPER ARITY TRIGGER))))))
(++ no-trigger
    (canonicalize-trigger
      '((RULE SUB SUPER) S.T.
	(E (TRIGGER ARITY)
	   (AND (PREVIOUSLY (NOT (SUBRELATIONCONSTRAINT RULE SUB SUPER)))
		(START (RELATIONARITY SUPER ARITY))
		(RELATIONARITY SUB ARITY)
		(RULETRIGGER RULE TRIGGER)
		;(RELATION-IN-DEFN SUB RULE)
		;(RELATION-IN-DEFN SUPER RULE)
		(SUBRELTRIGGER SUB SUPER ARITY TRIGGER))))))
#+ignore ; an old version
(++ no-trigger
    (canonicalize-trigger
      '((RULE SUB SUPER TRIGGER ARITY)
	S.T.
	(AND (START (RELATIONARITY SUPER ARITY))
	     (RELATIONARITY SUB ARITY)
	     (RULETRIGGER RULE TRIGGER)
	     (SUBRELTRIGGER SUB SUPER ARITY TRIGGER)
	     (relation-in-defn sub rule)
	     (relation-in-defn super rule)))))
; tell the rule compiler not
; to worry about the previous rules that turn out to be constraints when 
; a new rel is declared

(++ wffdefn (relationp 'SubRelationConstraint)
  '((rule sub super) s.t.
    (E (trigger arity) (and (RuleTrigger rule trigger)
			    (relationarity sub arity)
			    (relationarity super arity)
			    (SubRelTrigger sub super arity trigger)
			    ; more optimization no longer needed
			    ;(relation-in-defn sub rule)
			    ;(relation-in-defn super rule)
			    ))))

(setq SubRelEnforcement :none)

(defun subrel-adder (ignore sub super &aux arity) (declare (ignore ignore))
  (cond #+ignore
	 ((?? Subrel sub super)
	  ; this screws up if you atomically delete a subtype and
	  ; add one that it implied
	  (insist "supposed to add it" Subrel sub super))
	((setq arity
	       (any a s.t. (and (relationarity sub a) (relationarity super a))
		    :ifnone
		    (abort 'bad-subrel
			   "Trying to assert subrel of non relations" sub super)))
	 (neverpermit
	   (let ((subn (relationnamep sub))
		 (supn (relationnamep super)))
	     (pack* "SubRelation-" subn "--"
		    (cond ((eq (symbol-package subn) (symbol-package supn)) "")
			  (t (concatenate 'string
					   (package-name (symbol-package supn))
					   ":")))
		    supn))
	     ; *** another strange use of names
	   (SubRelTrigger sub super arity)
	   'ignored
	   SubRelEnforcement
	   :reporter
	   (FUNCTIONAL-EQUIVALENCE-TESTABLE
	     (coerce ; not worth compiling
	      `(lambda (&rest args)
		  (report-subtype-violation
		   ',(relationnamep sub) ',(relationnamep super) args))
	      'function)
	     (list :subtype-violation-reporter sub super)
	     (format nil "report-subrel-violation-~a-~a"
		     (relationnamep sub) (relationnamep super)))))))

(defun report-subtype-violation (sub super args)
  (declare (special default-tuple-printer))
  (format *error-output* "~%SubRelation constraint violation:~%")
  (apply default-tuple-printer *error-output* sub args)
  (format *error-output* "~% but not~%")
  (apply default-tuple-printer *error-output* super args))

(defun subrel-deleter (ignore sub super) (declare (ignore ignore))
  (cond ((?? ISubrel sub super)
	 ; get the effect of (-- ISubrel sub super) from
	 (forany rule s.t. (SubRelationConstraint rule sub super)
		 (-- ConsistencyRule rule)
		 ifnone (error "shouldn't happen! - Subrel-Deleter"))))
	; if not isubrel then I don't know what to do
  (insist "supposed to delete it" not (Subrel sub super)))

(++ reladder (relationp 'subrel) '(lambda (&rest ignore) (declare (ignore ignore))
					  'subrel-adder))
(++ reldeleter (relationp 'subrel) '(lambda (&rest ignore) (declare (ignore ignore))
					    'subrel-deleter))

; now replace the Subtype update macros ...

;; avoid weird warning msgs
(let ((old (theonly x s.t. (RelAdder Rel-Subtype x))))
  (-- RelAdder Rel-Subtype old))
;decache the adder
(rem-structure-property rel-subtype 'adder)

(defun subtype-adder (rel sub super)
  ; unnecessary (insist "supposed to add it" subtype sub super)
  (subrel-adder rel sub super))

(defun subtype-deleter (rel sub super)
  ; not needed - done in subre-deleter
  ; (insist "supposed to delete it" not (Subrel sub super))
  (subrel-deleter rel sub super))

(++ RelAdder Rel-SubType '(lambda (&rest ignore) (declare (ignore ignore)) 'subtype-adder))

(++ RelDeleter Rel-SubType '(lambda (&rest wff) 'subtype-deleter))

; now get ISubrel coordinated with the following defn
(++ WffDefn (relationp 'ISubRel)
  '((sub super) s.t.
    (E (rule) (SubRelationConstraint rule sub super))))

(loop for z in subtypetuples do (++ subtype (car z) (cadr z)))


