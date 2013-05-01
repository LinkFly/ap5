;;;-*- Mode: LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-
;
(in-package "AP5")

(defrelation Names-not-allowed-for-relations  :representation base
	     ;;:equivs (string-equal)
	     :types (symbol))

(atomic
 (loop for name in
      '(a e and or not implies equiv incx previously start start* nil
	  all exists xor change OPTIONAL multiple If-Then-Else
	  s.t. inline notinline output)
      do (++ Names-not-allowed-for-relations name)))


(neverpermitted relation-with-illegal-name
  (E (name)
    (and (relationname $ name)
	 (Names-not-allowed-for-relations name)
	 #+ignore(string-equal name badname)
	 )))

(neverpermitted anycomparison-for-stored-rel
	     (E (rel pos imp)
		 (and (anycomparison rel pos)
		      (relationimplementation rel imp)
		      (not (derived imp))))
	     :repair ignored
	     :enforcement-level :incremental)

(neverpermitted Non-Coded-Rel-with-CodeDefn
  (E (rel) (and (E (def) (CodeDefn rel def))
		 (not (relationimplementation rel 'coded))))
  :repair (lambda (rel) (set-listof def s.t. (CodeDefn rel def) nil))
  ; for when you change implementation from coded to other
  :enforcement-level :incremental
  :reporter
  (lambda (rel)
     (format *error-output*
	     "~%Relation ~A has a CodeDefn but is not a coded relation" rel)))

(alwaysrequired codedrel-has-codedefn
  (A (rel) (implies (relationimplementation rel 'coded)
		     (E (def) (codedefn rel def))))
  :repair ignored :enforcement-level :incremental
  :reporter
  (lambda (rel)
     (format *error-output*
	     "~%Relation ~A is coded but has no definition" rel)))

; change to codedefn => change to tester
(defun tester-for-codedefn (codedefn)
  `(lambda (&rest ignore)
     (declare (ignore ignore))
     '(LAMBDA (ignore ,@(car codedefn)) (declare (ignore ignore))
	      ,(caddr codedefn))))

#|  The following was relying on the reltester function being
a LIST, whereas it really should be a FUNCTION. I have
replaced it with a weaker consistency, just below.
(defrelation tester-for-codedefn :equivs (equal equal)
	     :computation (lisp-function tester-for-codedefn 1 1)
	     :define-macro-accessors nil)

(alwaysrequired codedefn->tester
   (A (rel code tester)
       (implies (and (codedefn rel code) (tester-for-codedefn code tester))
		(reltester rel tester)))
   :repair (lambda (rel code tester) (declare (ignore code))
	     (++ reltester rel tester))
   :enforcement-level :incremental)
; count constraint will remove old ones; also codedrel has 1 codedefn ...
|#

(alwaysrequired codedefn->tester
   (A (rel code)
       (implies (codedefn rel code)
		(exists (tester) (reltester rel tester))))
   :repair (lambda (rel code)
	     (++ reltester rel (coerce (tester-for-codedefn code) 'function)))
   :enforcement-level :incremental)


(alwaysrequired definededrel-has-wffdefn
  (A (rel) (implies (relationimplementation rel 'defined)
		     (E (def) (wffdefn rel def))))
  :repair ignored :enforcement-level :incremental
  :reporter
  (lambda (rel)
     (format *error-output*
	     "~%Relation ~A is defined but has no definition" rel)))

#+ignore  ; this can now be done by a count constraint
(neverpermit 'multiple-rels-per-name
   '(E (name rel1 rel2)
       (and (not (eql rel1 rel2))
	    (relationname rel1 name)
	    (relationname rel2 name)))
   'ignored
   :incremental
  :reporter
  #'(lambda (name &rest ignore)
     (declare (ignore ignore))
     (format *error-output* "~%Not allowed to have two relations named ~A" name)))

(neverpermitted Two-Rules-with-same-name
  (E (x y name) ; waste of time to make x and y typed vars!!
      (and (rulename x name) (rulename y name) (not (eql x y))))
  :repair
  (lambda (x y name)
     (cond ((?? start (rulename x name))
	    (-- rule y))))
  :enforcement-level :incremental
  :reporter
  (lambda (ignore ignore2 name)
     (declare (ignore ignore ignore2))
     (format *error-output* "~%Not allowed to have two rules named ~A" name)))
; no two rules with same name
;; this seems like special case of countconstraint, but the response does
;  not (yet) fall into a standard category

; this can't be done via consistency
; (useful) legal transitions.
;; The real spec is that we should delete isubrel links if doing so will
; leave the subrel link in place.  However this is complicated by transitions
; in which there may be a choice of which isubrels to delete.  We can just
; let rule exection order decide for us.
(defautomation Minimize-ISubrel
   ((sub sup extra) s.t.
     (start (and (Subrel sub extra) (Subrel extra sup) (ISubrel sub sup)
		 (not (subrel extra sub)) (not (subrel sup extra)))))
   (lambda (sub sup extra)
       (withwriteaccess ; check that it's still true
	 (when (?? and (Subrel sub extra) (Subrel extra sup) (ISubrel sub sup)
		       (not (subrel extra sub)) (not (subrel sup extra)))
	   (loop for rule1 s.t. (subrelationconstraint rule1 sub sup) do
		 (-- consistencyrule rule1))))))

#+ignore ; no longer prohibited, in particular if we define T2(x) as T1(x),
; the classifier will deduce that they are mutual subtypes.  Considering all
; the problems with names, this is probably better than adding names.
 (neverpermit 'subtype-cycles
  '(e (x y) (and (subrel x y) (subrel y x) (not (eql x y))))
  #'ignored
  :incremental
  :reporter
  #'(lambda (x y)
     (format *error-output*
	     "Types ~A and ~A are subtypes of each other?  In that case they're~
              the same type.  You should simply declare one type to have both names."
	     x y)))

(defautomation Minimize-Classification
   ((dbo sub sup) s.t.
     (start (and (classification dbo sub) (classification dbo sup)
		 (Subrel sub sup) (not (eql sub sup)))))
   (lambda (dbo sub sup) ; make sure it's still true
      (and (?? classification dbo sub) (-- classification dbo sup))))

#+ignore ; no longer true, since classification is treeprop+
(AlwaysRequire 'basetypes-are-subtype-of-DBO
  '(A (basetype#tp) (subtype tp (theap5relation dbobject)))
  #'(lambda (tp) (++ subtype tp (theap5relation dbobject)))
  :incremental)

(loop for type# s.t. (not (subtype type (relationp 'entity)))
      collect (progn (++ subtype type (relationp 'entity)) type))
(alwaysrequired all-types-subtype-of-entity
  (A (type#) (subtype type (constant type-entity)))
  :repair
  (lambda (tp); (or (?? basetype tp) ; in which case the previous rule applies
		     (++ subtype tp type-entity));)
  :enforcement-level :incremental)

; prevent triggers of rules from changing
; this should suffice in combintation with a uniqueness constraint
(neverpermitted rule-trigger-update
   (E (rule trigger)
       (and (previously (rule rule))
	    (start (ruletrigger rule trigger))))
   :repair
   (lambda (&rest ignore)
      (declare (ignore ignore))
      (abort 'change-rule-trigger
	     "see the manual for an explanation of why this is prohibited"))
   :enforcement-level :incremental)

; prevent enforcement from changing
; this should suffice in combintation with a uniqueness constraint
(neverpermitted enforcement-update
   (E (rule enforcement)
       (and (previously (consistencyrule rule))
	    (start (Constraint-Enforcement-Level rule enforcement))))
   :repair
   (lambda (&rest ignore)
      (declare (ignore ignore))
      (abort 'change-rule-enforcement
	     "see the manual for an explanation of why this is prohibited"))
   :enforcement-level :incremental)

;; here's a bunch of stuff for tclosures

(alwaysrequired tclosure-has-right-implementation
   (A (rel*) (equiv (E (rel) (tclosure rel rel*))
		     (relationimplementation rel* 'tclosure)))
   ; if it has no imp then a typeconstraint will remove tclosure
   ; it could have another implementation in which case remove the tclosure
   ; it could no longer be the tclosure of anything in which case kill it
   :repair fix-tclosure-imp :enforcement-level :incremental
   :reporter
   (lambda (r) (format *error-output*
			"~%The RelationImplementation and TClosure relations~
                         ~% seem to disagree on whether ~A is a transitive closure" r)))
                        
(defun fix-tclosure-imp (rel*)
  (forany rel s.t. (tclosure rel rel*)
	  (warn "~A will no longer be the transitive closure of ~A" rel* rel)
	  (-- tclosure rel rel*)
	  ifnone (when (relationp rel*) ; don't warn the 2nd time
		   ; after relarity removed but before relimp
		   (warn "discarding the relation ~A" rel*)
		   (-- relation rel*))))

(defun fix-tclosure-comparisons (irel crel compare)
  (cond ((?? start (compare-relation irel 0 compare))
	 (++ compare-relation irel 1 compare)
	 (++ compare-relation crel 0 compare)
	 (++ compare-relation crel 1 compare))
	((?? start (not (compare-relation irel 0 compare)))
	 (-- compare-relation irel 1 compare)
	 (-- compare-relation crel 0 compare)
	 (-- compare-relation crel 1 compare))
	((?? and (start (tclosure irel crel))
	         (compare-relation irel 0 compare))
	 (++ compare-relation irel 1 compare)
	 (++ compare-relation crel 0 compare)
	 (++ compare-relation crel 1 compare))))
; have to define the function before its use - due to typeconstraint

; no longer needed with new trigger compiler? (let ((dnf-ify t))  
(alwaysrequired tclosures-have-consistent-comparisons
   (A (rel rel* crel)
       (implies
	 (tclosure rel rel*)
	 (and
	   (equiv (compare-relation rel 0 crel) (compare-relation rel 1 crel))
	   (equiv (compare-relation rel 0 crel) (compare-relation rel* 0 crel))
	   (equiv (compare-relation rel 0 crel) (compare-relation rel* 1 crel)))))
   :repair fix-tclosure-comparisons
   :enforcement-level :incremental
   :reporter
   (lambda (r r* crel)
      (format *error-output*
	      "~%The fact that ~A and ~A are related by transitive-closure~
                ~% requires that they have consistent comparison relations.
                ~% There's some disagreement about ~A."
	      r r* crel)));)

(alwaysrequired tclosures-have-consistent-typeconstraints
   (A (rel rel* pos tc)
       (implies
	 (tclosure rel rel*)
	 (equiv (typeconstraint rel pos tc)
		(typeconstraint rel* pos tc))))
   :repair fix-tclosure-typeconstraints :enforcement-level :incremental
   :reporter
   (lambda (r r* pos tc)
      (format *error-output*
	      "~%The fact that ~A and ~A are related by transitive-closure~
                ~% requires that they have consistent typeconstraints.
                ~% There's some disagreement about ~A in position ~A."
	      r r* tc pos)))

(defun fix-tclosure-typeconstraints (rel rel* pos tc)
  (cond ((?? start (typeconstraint-stored rel pos tc))
	   (deftypeconstraint rel* pos tc :enforcement :none))
	((?? start (not (typeconstraint-stored rel pos tc)))
	 (-- typeconstraint rel* pos tc))
	((?? and (start (tclosure rel rel*))
	         (typeconstraint-stored rel pos tc))
	   (deftypeconstraint rel* pos tc :enforcement :none))))

;; This could cause some problems if you go around declaring multiple typeconstraints
; with nonstandard-names - you'll have to do the same thing for the tclosures.


#+ignore  ; this stuff doesn't work yet ...
(
 ;; can't afford to make real-reladder trigger from adder and real-possibletoadd
 ; trigger from it - that gives us demons that fight each other (and thus abort)
 ; --- that's why we invented maintainrules ---
 (++ proprelname 'real-reladder)
 (++ compare-relation (relationp 'real-reladder) 1 (relationp 'equal))
 (compiled
   (forany d s.t. (wffdefn (relationp 'real-reladder) d) ifnone
	   (loop for relation#r s.t. true do
	     (forany x s.t. (reladder r x) (++ real-reladder r x)
		     ifnone (forany imp x s.t. (and (relationimplementation r imp)
						    (reladder imp x))
				    (++ real-reladder r x)
				    ifnone nil)))))
 (++ wffdefn (relationp 'real-reladder)
     '((relation#rel adder) s.t.
       #+ignore  ; simplifier isn't smart enough to do this
       (if-then-else (E (x) (reladder rel x))
		     (reladder rel adder)
		     (E (imp) (and (relationimplementation rel imp)
				   (reladder imp adder))))
       (or (reladder rel adder)
	   (and (not (E (x) (reladder rel x)))
		(E (imp) (and (relationimplementation rel imp)
			      (reladder imp adder)))))))
 
 (++ help (relationp 'real-reladder)
 "(Real-RelAdder relation addmacro) is true if addmacro would be used to 
 compile an addition of a tuple of relation: either addmacro is actually 
 the RelAdder of relation, or relation has no RelAdder, and addmacro is
 the reladder of its implememtation.")
 (deftypeconstraints :none real-reladder relation function)
 
 (++ proprelname 'real-reldeleter)
 (++ compare-relation (relationp 'real-reldeleter) 1 (relationp 'equal))
 (compiled
   (forany d s.t. (wffdefn (relationp 'real-reldeleter) d) ifnone
	   (loop for relation#r s.t. true do
	     (forany x s.t. (reldeleter r x) (++ real-reldeleter r x)
		     ifnone (forany imp x s.t. (and (relationimplementation r imp)
						    (reldeleter imp x))
				    (++ real-reldeleter r x)
				    ifnone nil)))))
 (++ wffdefn (relationp 'real-reldeleter)
     '((relation#rel deleter) s.t.
       #+ignore  ; same thing
       (if-then-else (E (x) (reldeleter rel x))
		     (reldeleter rel deleter)
		     (E (imp) (and (relationimplementation rel imp)
				   (reldeleter imp deleter))))
       (or (reldeleter rel deleter)
	   (and (not (E (x) (reldeleter rel x)))
		(E (imp) (and (relationimplementation rel imp)
			      (reldeleter imp deleter)))))))
 (++ help (relationp 'real-reldeleter)
 "(Real-RelDeleter relation deletemacro) is true if deletemacro would be used
 to compile a deletion of a tuple of relation: either deletemacro is actually 
 the RelDeleter of relation, or relation has no RelDeleter, and deletemacro is
 the reldeleter of its implememtation.")
 (deftypeconstraints :none real-reldeleter relation function)

 ;; Problem: rule below requires tclosures have add/del triggers.
 ;; This makes it appear that they can be added/deleted even if irel is static.
 ;; This must be fixed if we wish to enforce constraints below that irel and crel
 ;; are equally possible to update.

 (++ proprelname 'real-possibletoadd)
 (deftypeconstraints :none real-possibletoadd relation t-or-nil)
 (compiled
   (forany d s.t. (wffdefn (relationp 'real-possibletoadd) d) ifnone
	   (loop for relation#r s.t. true do
	     (forany pta s.t. (possibletoadd r pta) (++ real-possibletoadd r pta)
		     ifnone (forany x s.t. (real-reladder r x)
				    (++ real-possibletoadd r t)
				    ifnone (++ real-possibletoadd r nil))))))
 ; *** that's wrong - defined rels are possible to add if the rels in the defn
 ; can be changed appropriately
 (++ wffdefn (relationp 'real-possibletoadd)
     '((rel ans) s.t.
       #+ignore  ; again
       (if-then-else (E (x) (possibletoadd rel x))
		     (possibletoadd rel ans)
		     (if-then-else (E (x) (real-reladder rel x))
				   (eql ans t)
				   (eql ans nil)))
       (or (possibletoadd rel ans)
	   (and (not (E (x) (possibletoadd rel x)))
		(if-then-else (E (x) (real-reladder rel x))
			      (eql ans t)
			      (eql ans nil))))))
 
 (++ help (relationp 'real-possibletoadd)
 "(Real-PossibleToAdd relation T-OR-NIL) tells whether (ap thinks) relation can
 ever become true (T if so, NIL if not): if the relation is in a PossibleToAdd
 tuple, that provides the answer, otherwise the answer is determined by the
 presence or absence of a Real-RelAdder for the relation.  This turns out to
 be wrong for defined relations, but our applications are not interested in them.")
 (++ subrel (relationp 'possibletoadd) (relationp 'real-possibletoadd))
 
 (++ proprelname 'real-possibletodelete)
 (deftypeconstraints :none real-possibletodelete relation t-or-nil)
 (compiled
   (forany d s.t. (wffdefn (relationp 'real-possibletodelete) d) ifnone
	   (loop for relation#r s.t. true do
	     (forany pta s.t. (possibletodelete r pta) (++ real-possibletodelete r pta)
		     ifnone (forany x s.t. (real-reldeleter r x)
				    (++ real-possibletodelete r t)
				    ifnone (++ real-possibletodelete r nil))))))
 (++ wffdefn (relationp 'real-possibletodelete)
     '((rel ans) s.t.
       #+ignore  ; again
       (if-then-else (E (x) (possibletodelete rel x))
		     (possibletodelete rel ans)
		     (if-then-else (E (x) (real-reldeleter rel x))
				   (eql ans t)
				   (eql ans nil)))
       (or (possibletodelete rel ans)
	   (and (not (E (x) (possibletodelete rel x)))
		(if-then-else (E (x) (real-reldeleter rel x))
			      (eql ans t)
			      (eql ans nil))))))
 (++ help (relationp 'real-possibletodelete)
 "(Real-PossibleToDelete relation T-OR-NIL) tells whether (ap thinks) relation 
 can ever become false (T if so, NIL if not): if the relation is in a 
 PossibleToDelete tuple, that provides the answer, otherwise the answer is
 determined by the presence or absence of a Real-RelDeleter for the relation.
 This turns out to be wrong for defined relations, but our applications are not 
 interested in them.")
 (++ subrel (relationp 'possibletodelete) (relationp 'real-possibletodelete))
 
 (alwaysrequire 'tclosures-have-right-possibletoadd
    '(A (rel crel pta)
	(implies (and (tclosure rel crel) (real-possibletoadd rel pta))
		 (possibletoadd crel pta)))
    (compile-ap '(lambda (rel crel pta) rel (++ possibletoadd crel pta)))
    :incremental
    :reporter
    '(lambda (r r*)
       (format *error-output*
	       "~%The fact that ~A and ~A are related by transitive-closure~
		 ~% requires that if one can be added then so can the other.~
		 ~% The PossibleToAdd relation could not be adjusted to achieve this."
	       r r*)))
 
 (alwaysrequire 'tclosures-have-right-possibletodelete
    '(A (rel crel pta)
	(implies (and (tclosure rel crel) (real-possibletodelete rel pta))
		 (possibletodelete crel pta)))
    (compile-ap '(lambda (rel crel pta) rel (++ possibletodelete crel pta)))
    :incremental
    :reporter
    '(lambda (r r*)
       (format *error-output*
	       "~%The fact that ~A and ~A are related by transitive-closure~
		 ~% requires that if one can be deleted then so can the other.~
		 ~% The PossibleToDelete relation could not be adjusted to achieve this."
	       r r*)))
)

(alwaysrequired tclosure-trigger
   (A (rel crel)
      (and (equiv (tclosure rel crel) (trigger rel t 'trigger++tclosures crel t))
	   (equiv (tclosure rel crel) (trigger rel nil 'trigger--tclosures crel nil))))
   :repair
   (lambda (rel crel)
     (cond ((?? tclosure rel crel)
	    (++ trigger rel t 'trigger++tclosures crel t)
	    (++ trigger rel nil 'trigger--tclosures crel nil))
	   (t (-- trigger rel t 'trigger++tclosures crel t)
	      (-- trigger rel nil 'trigger--tclosures crel nil))))
   :enforcement-level :incremental)


(alwaysrequired subrelations-have-same-arity
  (A (rel1 rel2)
     (implies (isubrel rel1 rel2)
	      (E (arity) (and (relationarity rel1 arity)
			      (relationarity rel2 arity)
			      #+ignore(isubrel rel1 rel2)))))
  ;; the extra isubrel in the RHS is an efficiency hack (no longer needed - new rule compiler)
  :repair ignored
  ; one case that we can take care of is when one of the relations was deleted
  ; that's now subsumed - all rules are deleted when they contain non-relations
  :enforcement-level :incremental
  :reporter
  (lambda (r1 r2)
    (format *error-output*
	    "~%The SubRelation relation cannot hold between ~A and ~A ~
              ~% because they don't have the same arity" r1 r2))) 

(defun report-position-violation (rel pos argrel arity &rest tuple)
  (format *error-output* "~%Position argument out of range:~%")
  (apply default-tuple-printer *error-output* rel tuple)
  (format *error-output*
	  "~% ~A is used as a position of relation ~A, with arity ~A.~
           ~% It should be the case that 0 <= position < arity."
	  pos argrel arity))

#+ignore  ; this can't happen ...
(++ no-trigger
    '((REL POS TYPE ARITY)
      S.T.
      (AND (START (RELATIONARITY REL ARITY))
	   (OR (NOT (< POS ARITY)) (NOT (<= 0 POS)))
	   (TYPECONSTRAINT-STORED REL POS TYPE))))
#+ignore 
(AlwaysRequire 'typeconstraint-has-legal-position
  '(A (rel pos type arity)
      (implies (and (typeconstraint rel pos type) (relationarity rel arity))
	       (and (<= 0 pos) (< pos arity))))
  'ignored
  :none ; can't happen
  ;:reporter
  #+ignore '(lambda (rel pos type arity)
     (report-position-violation 'TypeConstraint pos rel arity rel pos type arity)))

(++ no-trigger
    (canonicalize-trigger
      '((REL POS COMPARE ARITY) s.t.
	(AND (A (POSN ARITYN)
		(OR (NOT (<= 0 POSN))
		    (NOT (< POSN ARITYN))
		    (NOT (= POS POSN))
		    (NOT (= ARITY ARITYN))))
	     (start (RELATIONARITY REL ARITY))
	     (COMPARE-RELATION REL POS COMPARE)))))

(AlwaysRequired compare-relation-has-legal-position
  (A (rel pos compare arity)
      (implies (and (compare-relation rel pos compare)
		    (relationarity rel arity))
	       (E (posn arityn) (and (= pos posn) (= arity arityn)
				     (<= 0 posn) (< posn arityn)))))
  :repair ignored :enforcement-level :incremental
  :reporter
  (lambda (rel pos cmp arity)
     (report-position-violation 'Compare-Relation pos rel arity rel pos cmp arity)))

(++ no-trigger
    (canonicalize-trigger
      '((REL POS ARITY)
	S.T.
	(AND (START (RELATIONARITY REL ARITY))
	     (ANYCOMPARISON REL POS)
	     (a (posn arityn)
		(OR (not (= posn pos)) (not (= arityn arity))
		    (NOT (< POSn ARITYn)) (NOT (<= 0 POSn))))))))
(AlwaysRequired anycomparison-has-legal-position
  (A (rel pos arity)
      (implies (and (anycomparison rel pos) (relationarity rel arity))
	       (e (posn arityn)
		  (and (= posn pos) (= arityn arity)
		       (<= 0 posn) (< posn arityn)))))
  :repair ignored :enforcement-level :incremental
  :reporter
  (lambda (rel pos arity)
     (report-position-violation 'AnyComparison pos rel arity rel pos arity)))

#+ignore
(++ no-trigger
    (canonicalize-trigger
      '((REL POS FN ARITY)
	S.T.
	(AND (START (RELATIONARITY REL ARITY))
	     (OR (NOT (< POS ARITY)) (NOT (<= 0 POS)))
	     (TELL-ME-ABOUT-FNS REL POS FN)))))
#+ignore
(AlwaysRequire 'tell-me-about-fns-has-legal-position
  '(A (rel pos fn arity)
      (implies (and (tell-me-about-fns rel pos fn) (relationarity rel arity))
	       (and (<= 0 pos) (< pos arity))))
  'ignored
  :incremental
  :reporter
  #'(lambda (rel pos fn arity)
     (report-position-violation 'Tell-Me-About-Fns pos rel arity rel pos fn arity)))

#+ignore ;; have to wait for member to be defined (in fsd)
; of course, we really want this to apply to all infinite sets, not just entity
; note this is not strictly true - I could have a "stored" rel that assigns a
; default value to every element of an infinite set.  (Like the documentation fn.)
(neverpermitted stored-rel-multiple-for-entity
  (e (rel pat imp) (and (start (multiple-for rel pat))
			(member-eql 'entity pat)
			(relationimplementation rel imp)
			(not (derived imp))))
  :repair ignored :enforcement-level :incremental
  :reporter
  (lambda (rel pat imp) (declare (ignore pat imp))
     (format *error-output* "~%It's impossible to store a tuple of ~A for every ENTITY!~%"
	     rel)))

; There's really something wrong with having a rule with an invalid trigger...
(neverpermitted throw-out-invalid-defns
  (E (rel rel-or-rule def)
     (and (or (e (x)(start (not (relationarity rel x))))
	      (e (x)(start (not (relationname rel x))))
	      (e (x y)(start (not (compare-relation rel x y))))
	      (e (x y)(start (compare-relation rel x y))))
	  (relation-in-defn rel rel-or-rule)
	  (or (ruletrigger rel-or-rule def) (wffdefn rel-or-rule def))
	  (not (description def))
	  (not (closed-wff def))))
  :repair
  (lambda (rel bad def)
      (declare (ignore def rel))
      (when (?? or (rule bad) (relation bad))
	(warn "~&discarding ~A which now has a bad definition" bad)
	(-- relation bad)(-- rule bad)))
  :enforcement-level :incremental)
; This is not quite enough, e.g., I could swap the names of two rels
; resulting in a valid wff which is still not the one actually being used.
; See below.

; rules to decache relation data

;; Whenever the expanded-defn changes w.r.t. EQUAL, the relation has changed
; in ways that should be reflected by decaching.  Also it needs new 
; known-match-predecessor's.
; What can change the expanded-defn?
; - changes to inlinerel
; - changes to wffdefn
; - changes to relationname (see above)
; - changes to macros, but we cannot detect these

;; decaching seems about right when done by automationgenerators - 
;  automation is clearly too late since other stuff can run first
;  consistency may be too early - who knows what we want in inconsistent state?

(defautomationgenerator notice-changed-expanded-defn
    ((rel) s.t. (E (changerel)
		    (and (previously (relation-in-defn* changerel rel))
			 (relation rel)
			 (or (change (x) (wffdefn changerel x))
			     (change (x) (relationname changerel x))
			     (change nil (inlinerel changerel))))))
    check-expanded-defn)

(defun check-expanded-defn (rel &aux old new)
  (when (setq old (get-structure-property rel 'expanded-defn))
    (rem-structure-property rel 'expanded-defn)
    (setq new (expanded-defn rel))
    (unless (equal old new)
      (warn "The meaning of the definition of ~A has changed" rel)
      (enqueue-automation ;;too bad this has to wait for an automation ***
	(atomic (loop for (x y z) s.t. (known-match-predecessor rel x y z) do
		      (-- known-match-predecessor rel x y z))))
      ; that's supposed to get them recomputed if necessary (possible)
      (decache-rel rel :all))))

(defautomationgenerator decache-reltester
    ((x) s.t. (change (y) (reltester x y)))
    ; we worry about addition in case the tester was previously inherited from imp
    (lambda (rel)
       (cond ((relationp rel)
	      (decache-rel rel :tester t))
	     (t ; it's an implementation or a FORMER rel, in which case this is a noop
	      (loop for x s.t. (relationimplementation x rel) do
		    ; waste a little effort for rels with their own testers ...
		    (decache-rel x :tester t))))))
(defautomationgenerator decache-reladder
    ((x) s.t. (or (change (y) (reladder x y)) (change (y) (checker x y))))
    (lambda (rel)
       (cond ((relationp rel)
	      (decache-rel rel :adder t))
	     (t ; it's an implementation or FORMER rel
	      (loop for x s.t. (relationimplementation x rel) do
		    (decache-rel x :adder t))))))
(defautomationgenerator decache-reldeleter
    ((x) s.t. (or (change (y) (reldeleter x y)) (change (y) (checker x y))))
    (lambda (rel)
       (cond ((relationp rel)
	      (decache-rel rel :deleter t))
	     (t ; it's an implementation or FORMER rel
	      (loop for x s.t. (relationimplementation x rel) do
		    (decache-rel x :deleter t))))))
(defautomationgenerator decache-relupdater
    ((x) s.t. (change (y) (relupdater x y)))
    (lambda (rel)
       (cond ((relationp rel)
	      (decache-rel rel :adder :deleter))
	     (t ; it's an implementation or FORMER rel
	      (loop for x s.t. (relationimplementation x rel) do
		    (decache-rel x :adder :deleter))))))
#+ignore 
(defautomationgenerator decache-relinheriter
    ((x) s.t. (change (y) (relinheriter x y)))
    (lambda (rel)
       (cond ((relationp rel)
	      (decache-rel rel :inheriter t))
	     (t ; it's an implementation or FORMER rel
	      (loop for x s.t. (relationimplementation x rel) do
		    (decache-rel x :inheriter t))))))
(defautomationgenerator decache-generator
    ((x) s.t. (e (y) (start (not (relgenerator x y)))))
    (lambda (rel)
       (cond ((relationp rel)
	      (decache-rel rel :generator t))
	     (t ; it's an implementation or FORMER rel
	      (loop for x s.t. (relationimplementation x rel) do
		    (decache-rel x :generator t))))))

(defautomationgenerator decache-cannot-generator
    ((x) s.t. (e (y) (and (not (start (relation x)))
			   (start (relgenerator x y)))))
    (lambda (x)
      (loop for (rel rel*) s.t.
	    (and (or (eql rel x) (relationimplementation rel x))
		 (or (eql rel rel*) (relation-in-defn* rel rel*)))
	    ; compiles the wrong way if I combine the two (worst case is wrong!)
	    do (loop for (y z) s.t. (generator-cache rel* y z)
		     when (eq (cadr (assoc 'initialstate z)) :cannot-generate)
		     do (gendeleter y z)))))

;; implementation-parameter-relations

(defautomationgenerator decache-codedefn
    ((x y) s.t.
      (start (not (codedefn x y))))
    (lambda (rel olddef) (declare (ignore olddef))
	     (when (relationp rel)
	       (decache-rel rel :tester t))))

#+ignore
(defautomationgenerator decache-relation-lispfn
    ((x y) s.t.
      (start (not (relation-lispfn x y))))
    (lambda (rel olddef) (declare (ignore olddef))
	     (when (relationp rel)
	       (decache-rel rel :tester :generator))))

(defautomationgenerator decache-from-stored-where
    ((x y) s.t.
      (start (not (stored-where x y))))
    (lambda (rel old) (declare (ignore old))
	     (when (relationp rel)
	       (decache-rel rel :all))))

;; Both stored-in-place and store-in-place-single share the stored-where
;; relation, so we better not have one relation with both of those imp's.
(neverpermitted implementation-both-stored-where-and-single
   (E (rel)(and (relationimplementation rel 'stored-in-place-single)
		(relationimplementation rel 'stored-in-place)))
   :repair ignored
   :enforcement-level :incremental)

#+ignore
(defautomationgenerator decache-sip-generator
    ((x) s.t. (or (change (y) (GLOBALVAR-PLACER x y))
		  (change (y z) (structfield-placer x y z))
		  (change (y) (symbolprop-placer x y))
		  (change (y) (hash-table-placer x y))
		  (change (y) (alist-placer x y))
		  (change (y) (array-placer x y))))
    (lambda (x)
	(loop for rel s.t. (stored-where rel x) do
	      (decache-rel rel :all))))
; has to be maintained as new virtual implementations are invented ***
; since it's really a second order relation
;; evidently we don't need to worry about changing from array to alist
;  since there's only one placer - no problem if X-placer relates something
;  that's no longer the placer for any relation


(defautomationgenerator decache-from-tclosure
    ((x y) s.t.
      (start (not (tclosure x y))))
    (lambda (irel crel) (declare (ignore irel))
	     (when (relationp crel)
	       (decache-rel crel :all))))

(defconsistencychecker decache-matchrels
  ((rel) s.t. (change (x) (wffdefn rel x)))
  (lambda (rel &aux newrels oldrels)
    (loop for node in (matchnodes-> (list rel)) do
	  (try (progn
		 (setq newrels (changerels-in-wff (matchwff node)))
		 (setq oldrels (matchrels node))
		 (unless (?? matchrels node newrels)
		   (++ matchrels node newrels)
		   (-- matchrels node oldrels)))
	       ; in case it contains a defunct relation
	       ;; what if we make it a relation again?
	       ;;; (Only a problem if not via undo)
	       expanddescription nil))))
; matchrels is a relation so this can be undone

(defautomationgenerator decache-defn
    ((x y) s.t. (start (not (wffdefn x y))))
    (lambda (rel ignore) (declare (ignore ignore))
        (when (relationp rel) ; other rules apply if rel was deleted 
	  (decache-rel rel :all)
	  ; compound not possible under the current implementation
	  (loop for x s.t. (relation-in-defn* rel x) do
		;(warn "~A uses ~A, which has lost a definition" x rel)
		; Neil argues we don't want to see that warning
		(when (?? relation x) (decache-rel x :all))))))

; Now try to maintain comparisons for rels with defns (even maintained)
; *** it would be nice to do this via consistency, but for now...
(defautomation defined-comparisons
    ((rel) s.t.
      (or (E (def) (start (wffdefn rel def)))
	  (E (pos cmp) (or (start (compare-relation rel pos cmp))
			   (start (not (compare-relation rel pos cmp)))))))
    ;; anything that could cause a comparison to change above
    derive-comparisons)
(defun derive-comparisons (rel)
  (loop for r s.t. (or (eql rel r) (relation-in-defn* rel r))
	when (?? E (def) (wffdefn r def)) do
	(decache-rel r :expanded-defn)
	(atomic ; is it better with or without?
	  ; An advantage is only one decache-rel/relation
	  (loop for v in (expanded-defn-vars r) as i from 0 do
		(let ((old (any x s.t. (compare-relation r i x) ifnone rel-eql))
		      (new (varcompare v)))
		  (unless (or (eql old new)
			      (and (consp old) (consp new) (feqset old new)))
		    (warn "Definition of ~A makes the comparison of ~A in ~
                           position ~A ~A~
                           ~:[~& which will force it to be used InLine~;~]"
			  rel r i (or (relationp new) "ambiguous") (relationp new))
		    (-- compare-relation rel i old)
		    (unless (eq new rel-eql)
		      (when (relationp new) (++ compare-relation r i new)))))))))

;; get these installed without triggering rules to decache everything ...
;(with-dormant-rules (change-comparison) ; not needed yet
(loop for (relation#x y) s.t. (wffdefn x y) do (derive-comparisons x))

; Currently the previously compiled code that refers to the rel will not
; be changed to use the new defn.
; Removing a defn cannot change comparisons.  Adding one can cause previous
; code to not (re)compile due to changed comparisons.
(defautomationgenerator change-comparison
    ((x n equiv) s.t. 
      (and (previously (relation x))
	   (relation x)
	   (or (start (compare-relation x n equiv))
	       (start (not (compare-relation x n equiv))))))
    (lambda (rel n equiv) ; see remark below
	(unless (eql equiv (dbo relation eql))
	  (unless (?? relationimplementation rel 'defined)
	    ; assume it's from the rule above
	    (warn "~&Changing comparison for slot ~d of ~A~
                   ~&AP5 will not re-represent the tuples" n rel))
	  (decache-rel rel :all t))))

(defautomationgenerator change-implementation-or-arity
    ((rel) s.t.
     (and (previously (E (pl) (parameter-list rel pl)))
	  ; meaning that it was previously defined via defrelation
	  ;(previously (relationimplementation rel $))
	  (relation rel)
	  (or (change (imp) (relationimplementation rel imp))
	      (CHANGE (A) (RELATIONARITY REL A))
	      (change (parms) (parameter-list rel parms)))))
    (lambda (rel)
      (when (derivedrel rel)
	(if (previously (derivedrel rel))
	    (warn "Changing derivation of ~A~
                   ~&AP5 will not trigger rules on any changes to it" rel)
	    (warn "Changing ~A to a derived relation~
                   ~&AP5 will ignore any previous tuples and ~
                   ~&will not trigger rules on any changes to it" rel)))
      (decache-rel rel :all t)))


; used for translation of updates
(defun simple-update-p (rel tv)
  (declare (ignore tv))
  ; too bad - ought to be able to see which rules are
  ; sensitive to additions, which to deletions.
  (and (not (derivedrel rel)) ; no adder/deleter translation
       (not (getdefn rel)) ; also not maintained (updates normally disallowed)
       ; no rules can trigger
       (?? not (e (rule#r)
		  (and (derived-from* r rel)
		       (not (Constraint-Enforcement-Level r :none)))))))

(loop for relation#r s.t. true when (simple-update-p r t) do
      (decache-rel r :adder :deleter))

(defautomationgenerator decache-simple-updaters
   ; other rules take care of this for most changes:
   ;  notice-changed-expanded-defn for wffdefn
   ;  change-implementation for implementation (don't worry about changing derived?)
   ((x) s.t. (change nil (e (rule#r)
			    (and (derived-from* r x)
				 (not (Constraint-Enforcement-Level r :none))))))
   (lambda (rel)
     (let ((fn (get-structure-property rel 'adder)))
       (if (fboundp (pack* "Normal-" fn))
	   (setf (symbol-function fn)
		 (symbol-function
		  (if (simple-update-p rel t)
		      (pack* "Simple-" fn) (pack* "Normal-" fn))))))
     (let ((fn (get-structure-property rel 'deleter)))
       (if (fboundp (pack* "Normal-" fn))
	   (setf (symbol-function fn)
		 (symbol-function
		  (if (simple-update-p rel nil)
		      (pack* "Simple-" fn) (pack* "Normal-" fn))))))))
; This is cheap enough that it's ok for defrel to install the wrong one
; and a later rule to change it.

#+ignore ; old version
(defautomationgenerator decache-simple-updaters
   ; other rules take care of this for most changes:
   ;  notice-changed-expanded-defn for wffdefn
   ;  change-implementation for implementation (don't worry about changing derived?)
   ((x) s.t. (change nil (e (rule#r)
			    (and (derived-from* r x)
				 (not (Constraint-Enforcement-Level r :none))))))
   (lambda (rel) (decache-rel rel :adder :deleter)))

(defautomationgenerator decache-relevant-updates
   ; similarly ...
   ((x) s.t. (change (rule#r)
		     (and (derived-from* r x)
			  (not (Constraint-Enforcement-Level r :none)))))
   (lambda (rel) (decache-rel rel :relevant-updates)))
;; Again, some backward UNDO's ought to trigger this rule but don't.
; *** (could be fixed by changing to a consistency and modelling
; relevant-updates explicitly as a relation)

(setq maintaining-relevant-updates t)

(defautomationgenerator change-nonatomic
  ((rel) s.t.
   (and (previously (relation rel))
	(relation rel)
	(or (change nil (nonatomic-relation rel))
	    (change (x) (idempotent rel x))
	    (change (x) (allow-interrupts rel x)))))
  (lambda (rel) (decache-rel rel :adder :deleter)))

(defautomation change-wffdefn
	       ((rel old new) s.t. (and (previously (wffdefn rel old))
					(start (wffdefn rel new))))
  (lambda (rel old new)
    (declare (ignore old new))
    (when (derived-from* rule#$ rel)
      (warn "The definition of ~A is changing.~
                  ~&AP5 assumes its tuples are unchanged!~
                  ~&(no rules will trigger on the changes)" rel))))

(defautomation warn-nonatomic-relation-in-trigger
   ((rel rule) s.t.
    (start (and (rule rule)
		(not (constraint-enforcement-level rule :none))
		(derived-from* rule rel)
		(nonatomic-relation rel))))
  (lambda (rel rule)
    (warn "Rule ~A uses the nonatomic relation ~A.~
          ~&AP5 can only assume this makes sense." rule rel)))
   
#||
(listof (rel rule) s.t. (and (rule rule)
			     (not (constraint-enforcement-level rule :none))
			     (derived-from* rule rel)
			     (nonatomic-relation rel)))
((DESCRIPTION THROW-OUT-INVALID-DEFNS)
 (CLOSED-WFF THROW-OUT-INVALID-DEFNS)
 (ADDMATCHER ADD-PREDECESSORS-WITH-DEFN)
 (DELETEMATCHER ADD-PREDECESSORS-WITH-DEFN))
;; THROW-OUT-INVALID-DEFNS really checks all those after start of other stuff
;; ADD-PREDECESSORS-WITH-DEFN uses start of other stuff & checks add/delmatcher
||#

#+ignore ; this becomes part of defrelation
(defautomation add-wff-typeconstraints
    ((rel def) s.t. (and (start (wffdefn rel def))
			  (not (E (pos type)
				  (and (typeconstraint rel pos type)
				       (not (eql type (constant type-entity))))))))
    add-wff-typeconstraints)

(flet
    ((add-wff-typeconstraints (rel def &aux *used-equiv* result varnames)
       (declare (special *used-equiv*))
       (setf def (copy-tree def))
       (setf varnames (mapcar #'variablename (car def))
	     result (defined-typeconstraints def))
       (setq result (loop for r in result collect
			  (cons (car r) (delete rel (cdr r)))))
					; we don't want x-or-y to be isubrel of itself
       (loop with pos for r in result do
	     (unless (setq pos (position (car r) varnames))
	       (error "cannot find the variable ~A in ~A" (car r) (car def)))
	
	     (loop for type in (cdr r)
		 unless (eq type type-entity) do
		   (deftypeconstraint rel pos type :enforcement :none)))
       (when (setq result (delete-if #'(lambda (l)
					 (or (null (cdr l))
					     (eq (cadr l) type-entity)))
				     result))
	 (warn "~&Type constraints derived from definition of ~A : ~
         ~%~A ~
         ~@[~%(please check this to be sure it's what you want)~]"
	       rel result *used-equiv*))))
  (loop for (relation#r d) s.t.
      (and (wffdefn r d) (not (e (x) (typeconstraint r 0 x))))
      do (add-wff-typeconstraints r (copy-tree d)))

  (loop for (type#r d) s.t.
      (and (wffdefn r d) (isubrel r (dbo type entity)))
      do (add-wff-typeconstraints r (copy-tree d))))

#+ignore ; subsumed by defined-comparisons
(++ automation 'warn-defn-must-be-inline
    '((x y) s.t. (start (definedrelname x y)))
    #'(lambda (x y) (declare (ignore y))
	(when (some #'(lambda (x) (listp (varcompare x)))
		    ;; can be nil for only anycomparisons
		    (expanded-defn-vars (relationp x)))
	  (warn "The definition of ~A will force it to be used InLine" x))))

(loop for (r def) s.t. (and (wffdefn r def) (relationimplementation r 'defined))
      unless (compoundwffp (third def))
      unless (?? E (x) (or (reladder r x) (reldeleter r x)))
      do (++ inlinerel r))
; we know that compoundwffp never smashes its argument

#+ignore ; this is now the default for defrelation
(defautomation make-trivial-defns-inline
    ((rel def) s.t. (start (and (relationimplementation rel 'defined)
				 (wffdefn rel def))))
    maybe-make-inline)
#+ignore 
(defun maybe-make-inline (rel def)
  (declare (ignore def))
  (unless (compoundwffp (third (expanded-defn rel))) (++ inlinerel rel)))
; we know that compoundwffp never smashes its argument

(defautomation copy-relsize-tuples
    ((x) s.t. (and (start (relsize x $ $)) (inlinerel x)))
    (lambda (r) (warn "The size annotation for ~s will be ignored; it is inline"
		      (relationnamep r))))

;; What we want is that for every definedrel, every matchnode for that rel
;; has a predecessor that matches the definition.  (The definition actually
;; ought to mean the expanded-defn, so that even if the defn of a rel used in
;; the defn changes - or even if a MACRO used in the defn changes! - we notice.)
;; We settle for a close approximation since some of those rels are nontriggerable.
;; When a defrel gets a defn or a rel with a defn becomes defined, we give its
;; matchnodes predecessors.
;; When a node is created for a defrel, detectinput will give it predecessors.
;; Predecessors for old defns are removed by the rule below.
;;; Problem: what if detectinput builds the matchnode for the defrel, gives it
;;  predcessors and the atomic aborts?  Then the node does have predecessors
;;  even though K-M-P is not recorded! - wrong - pred's are part of asserting KMP.
;; We still have to worry about how changes of defns affect KMP's of other rels
;; that use the defn inline - doesn't rel-in-defn still record this?
(alwaysrequired add-predecessors-with-defn
   (a (rel def)
       (implies (start (and (wffdefn rel def)
			    (relationimplementation rel 'defined)))
		(a (node)
		   (implies (or (addmatcher rel node) (deletematcher rel node))
			    (E (pred) (known-match-predecessor rel def node pred))))))
   :repair add-predecessors-for-defn :enforcement-level :incremental)

(defun add-predecessors-for-defn (rel def)
  (setq def (copy-tree def))
  (loop for x s.t. (addmatcher rel x) do
	(add-defn-predecessor rel x def nil))
  (loop for x s.t. (deletematcher rel x) do
	(add-defn-predecessor rel x def t)))

(alwaysrequired known-match-predecessor-matches-defn
	       (A (rel def x y)
		   (implies (known-match-predecessor rel def x y)
			    (and (wffdefn rel def)
				 (relationimplementation rel 'defined))))
	       :repair
	       (lambda (rel def x y) (-- known-match-predecessor rel def x y))
	       :enforcement-level :incremental)

; Nothing to fix up here since all matchnodes for def. rels were built after
; they were defined.


;; I originally thought addcheckers were needed to ensure the relation can be detected.
; However, trying to detect in a checker meant asserting known-match-pred in a check,
; which is not allowed.  Instead we want to do it in a consistency rule, so we do
; the "check" as part of these rules:

; This will just get an error if it can't, so the user can abort or whatever.
(defun check-matchnode-for-rel (addp rel defn &aux desc node)
  (setf desc (loop for i below (arity* rel) collect (gensym "V")))
  (setf desc (expanddescription (list desc 's.t.
				      (cond (addp `(notinline (,rel ,.desc)))
					    (t `(not (notinline (,rel ,.desc))))))))
  (when (and (compoundwffp (third desc)) (not (eq 'NOT (first(third desc)))))
    (error "Since ~A has a definition that forces it to be used INLINE~
            ~&you will not be able to derive other relations from it.~
            ~&You might try redefining it with explicit comparisons" rel))
  (unless (setf node (detectinput (first desc) (third desc)))
    (error "Can't claim a relation knows how to be triggered if its
dependents can't be triggered."))      
  (put-structure-property rel (cons defn node)
			  (if addp 'add-matchnode 'del-matchnode)))

(alwaysrequired addtriggers-have-matchnodes
  (a (rel defn)
      (implies (and (relationimplementation rel 'defined)
		    (wffdefn rel defn)
		    (e (x y z) (trigger rel t x y z)))
	       (definedrel-with-known++maintain rel defn)))
  :repair
  (lambda (rel defn)
    (setf defn (copy-tree defn))
     (check-matchnode-for-rel t rel defn)
     (++ definedrel-with-known++maintain rel defn))
  :enforcement-level :incremental)

(alwaysrequired deltriggers-have-matchnodes
  (a (rel defn)
      (implies (and (relationimplementation rel 'defined)
		    (wffdefn rel defn)
		    (e (x y z) (trigger rel nil x y z)))
	       (definedrel-with-known--maintain rel defn)))
  :repair
  (lambda (rel defn)
    (setq defn (copy-tree defn))
     (check-matchnode-for-rel nil rel defn)
     (++ definedrel-with-known--maintain rel defn))
  :enforcement-level :incremental)

(alwaysrequired nonaddtriggers-may-have-nomatchnodes
  (a (rel defn)
      (implies (not (and (relationimplementation rel 'defined)
			 (wffdefn rel defn)
			 (e (x y z) (trigger rel t x y z))))
	       (not (definedrel-with-known++maintain rel defn))))
  :repair (lambda (rel defn) (-- definedrel-with-known++maintain rel defn))
  :enforcement-level :incremental)

(alwaysrequired nondeltriggers-may-have-nomatchnodes
  (a (rel defn)
      (implies (not (and (relationimplementation rel 'defined)
			 (wffdefn rel defn)
			 (e (x y z) (trigger rel nil x y z))))
	       (not (definedrel-with-known--maintain rel defn))))
  :repair (lambda (rel defn) (-- definedrel-with-known--maintain rel defn))
  :enforcement-level :incremental)

(neverpermitted circular-definitions
	     (e (rel) (derived-from* rel rel))
	     :repair ignored :enforcement-level :incremental)

; as per Neil's suggestion, change definedrelname so it does not
; necessarily mean that the implementation is 'defined

(++ wffdefn (dbo relation definedrelname)
  '((RELNAME DEF) S.T.
    (E (REL)
       (AND (RELATIONNAME REL RELNAME)
	    (WFFDEFN REL DEF)))))
; warns 3 rules use it & it lost defn

(neverpermitted unimplemented-defined-relation  
  (E (r) (and (E (d) (wffdefn r d))
	       (not (E (i) (relationimplementation r i)))))
  :repair (lambda (r) (++ relationimplementation r 'defined))
  :enforcement-level :incremental)

; the reason we have to treat this as a patch (change it at the end
; rather than where it's first defined) is that in building ap5
; all my definedrelnames would need implementations attached to them.
;; adder uses ...
(defun DefRel1 (RelName Args Defn &aux rel)
  (try (ExpandDescription (list args 's.t. defn))
    'ExpandDescription
    (abort 'bad-definition
	   "bad definition for ~S~%~S~%~S"
	   RelName (list Args 's.t. Defn) tryvalue))
  (setq rel (or (relationp RelName) (make-dbobject)))
  ; try to use old one ...
  #+ignore (Add-imparityname rel 'Defined (LENGTH Args) RelName)
  (++ relationarity rel (length args))
  (++ relationname rel relname)
  ; no longer add implementation
  (++ WffDefn rel (list Args 's.t. Defn))
  Defn)

(setf (symbol-function 'defrel) (symbol-function 'defrel1))

(loop with lisp = (find-package "LISP")
      for (r n) s.t. (relationname r n) unless (or (fboundp n) (eq (symbol-package n) lisp))
      do (setf (macro-function n)
	       #+(or ti symbolics) 'standard-relation-macro
	       #-(or ti symbolics) #'standard-relation-macro))