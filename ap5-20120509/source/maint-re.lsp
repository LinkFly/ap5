;;;-*- Mode: LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-
;
; ---------------- Maintained Relations ----------------

(in-package "AP5")

; Guaranteed to terminate
(defun eq-length (list length)
  (loop while (and (> length 0) (consp list)) do
	(setq list (cdr list))
	(setq length (- length 1)))
  (and (= 0 length) (null list)))

(defmacro need-update (def rel)
  `(or (and (start* ,def) (previously (not ,rel)))
       (and (start* (not ,def)) (previously ,rel))))

(defun maintainreltrigger (def mrel)
  (and (listp def) (eq-length def 3) (listp (car def))
       #+ignore
       `(,(car def) s.t.
	 (need-update ,(caddr def) ,(cons mrel (mapcar #'variablename (car def)))))
       (let ((names-types
	       (loop for v in (car def) collect
		     (multiple-value-list (VariableNameandType v)))))
	 `(E ,(loop for var in (car def) collect
		    (if (variabletypename var)
			(intern (subseq (symbol-name var)
					(1+ (position #\# (symbol-name var))))
				(symbol-package var))
			var))
	     ;(mapcar #'car names-types)
	     (need-update ,(cond ((loop for x in names-types always (eq (cadr x) 'entity))
				  (caddr def))
				 (t `(and ,@(loop for x in names-types
						  unless (eq (cadr x) 'entity)
						  collect (reverse x))
					  ,(caddr def))))
			  ,(cons mrel (mapcar #'car names-types)))))))
#+ignore ;previous version failed for @equiv
(defun maintainreltrigger (def mrel)
  (and (listp def) (eq-length def 3) (listp (car def))
       (let ((names-types
	       (loop for v in (car def) collect
		     (multiple-value-list (VariableNameandType v)))))
	 `(E ,(mapcar #'car names-types)
	     (need-update ,(cond ((loop for x in names-types always (eq (cadr x) 'entity))
				  (caddr def))
				 (t `(and ,@(loop for x in names-types
						  unless (eq (cadr x) 'entity)
						  collect (reverse x))
					  ,(caddr def))))
			  ,(cons mrel (mapcar #'car names-types)))))))
#+ignore ; previous previous version failed for type#
(defun maintainreltrigger (def mrel)
  (and (listp def) (eq-length def 3) (listp (car def))
       `(E ,(car def) (need-update ,(caddr def) ,(cons mrel (car def))))))

; This seems like a good place to put some commentary on what other things were
; tried and why this was chosen.
;- Maintaining rules were originally just consistency rules.  This was bad cause
; it yields maintained relation with different semantics from defined relations.
;- I consider it unfortunate that in trying to make a single maintaining rule
; I had to combine two triggers into one (defn becomes true or false).  It would
; be cleaner to have separate triggers and reactions.  In the consistency rule
; version you always knew that the change would be correct, whereas in this version
; if you manage to get off somehow the rule just keeps the data wrong.
;- I originally tried to use relation names in the trigger and code.  This is bad
; because the coded relations that generate them are really dependent on data,
; e.g., what things are relations and what their names are.  It's much cleaner
; to let the relations (like maintainingtrigger, below) deal with any objects, 
; whether or not they're relations or relation names.
;- The "change" macro, in addition to being generally useful, has the nice property
; that we can deduce the original definition from it, whereas we cannot deduce the
; original definition from its expansion.  This is because of typed variables.
; I tried to get around this by allowing MaintainingTrigger to relate any version
; of a definition to the trigger.  This turned out to be wrong because the rule
; Maintain-Rels-With-WffDefn would then object that the alternate definition was
; true for MaintainedRel but not for WffDefn.

(atomic
 (++ CodedRelName 'MaintainingTrigger
    '((def mrel trigger) s.t.
      (and trigger (equal trigger (maintainreltrigger def mrel)))))
 reveal
 (++ compare-relation (relationp 'maintainingtrigger) 0 (relationp 'equal))
 (++ compare-relation (relationp 'maintainingtrigger) 2 (relationp 'equal)))

(SimpleGenerator
  '(MaintainingTrigger def mrel output)
  '(let ((trigger (maintainreltrigger def mrel)))
     (and trigger (list trigger))))

(defun def-from-trigger (trigger &aux wff temp)
  (and (eq-length trigger 3) ; (e (vars) (need-update ...))
       (eq-length (setq temp (caddr trigger)) 3)
       (eq (car temp) 'need-update)
       (setq wff (cadr temp))
       (listp (setq temp (caddr temp)))
       (equal trigger
	      (maintainreltrigger
		(list (cadr trigger) 's.t. wff)
		(car temp)))
       (list (list (list (cadr trigger) 's.t. wff) (car temp)))))

#+ignore ; not possible with new defn
(simplemultiplegenerator
  '(maintainingtrigger output output trigger)
  '(def-from-trigger trigger))

(++ RelSize (relationp 'MaintainingTrigger)  '(output output input) 1)
(++ RelSize (relationp 'MaintainingTrigger) '(input input output) 1)

(defun maintainrelcode (rel arity &aux vars)
  ; have to make arity an argument since otherwise this rel would depend on the DB
  ; e.g., things could become rels and thus obtain arities
  (and (integerp arity) (>= arity 0)
       `(lambda ,(setq vars (loop for i below arity collect (pack* 'v i)))
	  (cond ((?? previously (,rel ,@vars))
		 (-- ,rel ,@vars))
		(t (++ ,rel ,@vars))))))

(atomic
 (++ CodedRelName 'MaintainingCode
    '((rel arity code) s.t.
      (and (symbolp code)
	   (equal (get code :FUNCTIONAL-CHARACTERIZATION)
		  (list :maintain rel arity))
	   #+ignore ; obsolete
	   (setq code (get code :previous-definition)) ; has to be non-nil
	   #+ignore ; obsolete
	   (equal code (maintainrelcode rel arity)))))
 reveal
 (++ compare-relation (relationp 'maintainingcode) 1 (dbo relation =)))

; Of course, we are now assuming that this never changes - if you start monkeying
; with the previous definition or making the function not equivalent to it then
; things won't work.
(++ compare-relation (relationp 'maintainingcode) 2
    (relationp 'symbol-functional-equivalentp))

; there is no longer any way to get from the trigger to the rel
; however we can get from the maintaining code to the rel
(defun rel-arity-from-code (fnname)
  (and (symbolp fnname)
       (setq fnname (get fnname :functional-characterization))
       (listp fnname)
       (eq (car fnname) :maintain)
       (list (cdr fnname)))
  #+ignore ; obsolete
  (let (rel arity code)
     (setq code (and (symbolp fnname) (get fnname :previous-definition)))
     (and (eq-length code 3) ;(lambda vars cond)
	  (setq arity (length (cadr code)))
	  (eq-length (setq rel (caddr code)) 3) ; (cond (?? --)(t ++))
	  (eq-length (setq rel (caddr rel)) 2) ; (t (++ rel ...))
	  (listp (setq rel (ilistp (cadr rel)))) ; (++ rel ...)
           ;*** this listp seems to return nil on hplisp when this function
           ; is compiled to a file (evidence from compiling with PRINT's)
	  (setq rel (cadr rel))
	  (equal code (maintainrelcode rel arity))
	  (list (list rel arity)))))


(SimpleMultipleGenerator
  '(MaintainingCode output output fnname)
  '(rel-arity-from-code fnname))


(++ RelSize (relationp 'MaintainingCode) '(output output input) 1)

#+ignore ; needed earlier (relations)
(++ TreeRelName 'MaintainedRel 3)
#+ignore ; also in relations
(++ compare-relation (relationp 'maintainedrel) 1 (relationp 'equal))

; for some reason (compiled <this>) compiles into something that uses the same
; property names for subrel-stored as for isubrel+, resulting in two identical
; facts for isubrel+ and none for subrel-stored.  (Why? ***)
; - Answer appears to be related to bug in put-structure-property inherited
; from bug in setf of getf - at least on HP

; - nmg 7/2/90 -- with LUCID's implementation of memo (since fixed)
; the two uses of MEMO in two-way-structprop functions, WHEN COMPILED
; TO CORE RATHER THAN TO A FILE, were merging the memo cells. 

#+ignore
(cerror "ready to do ++ isubrel r r if isubrel not yet defined" "")
(eval '(or (any x s.t. (wffdefn (relationp 'isubrel+) x) :ifnone nil)
    (loop for r s.t. (relation r) do (++ isubrel+ r r) (++ subrel-stored r r))))

#+ignore (cerror "done" "")
; there are no isubrels yet - this has to be done before the first ++wffdefn
; so that maintainrule will be true of things that are classified as maintainrules
; Also, this enables rules to be recognized and thus print out right.

(compiled
 (alwaysrequire 'Maintain-Rels-with-WffDefn
  '(A (rel def)
    (implies (and (relation rel) ; needed for (-- relation ..) - see below
		  (wffdefn rel def)
		  (E (imp) (and (not (eql imp 'defined))
				(relationimplementation rel imp))))
	     (E (rule) (maintainedrel rel def rule))))
  ;;(compile-ap*
    (lambda (rel def)
      (setq def (copy-tree def))
      (expanddescription
	`(,(car def) s.t.
	  (or (,rel ,@(mapcar 'variablename (car def))) ,(caddr def))))
      ; just to generate an error if the comparerels disagree
      (make-maintain
	(pack* "Maintain-" (relationnamep rel))
	; *** again a strange use of the name
	(maintainreltrigger def rel)
	(functional-equivalence-testable
	  (compile-ap (maintainrelcode rel (arity* rel)))
	  (list :maintain rel (arity* rel))
	  (format nil "Maintain-~A" (relationnamep rel)))))
    ;; )
  :incremental)
)

; The (relation rel) is needed cause if we try to delete a maintained rel
; the wffdefn is not removed until the first consistency cycle, and also
; on the first cycle this rule will notice that rel needs a maintainrule
; and try to build one.  (Because maintainedrel is maintained it appears
; deleted at the start of the first consistency cycle!)

; note that in this version maintainingtrigger relates several defs to the trigger
; and we don't want to require that all those be wffdefns of rel
(alwaysrequire 'unmaintain-non-defined-rels
  '(A (rel def rule)
      (implies (maintainedrel rel def rule)
	       (E (imp); trigger)
		  (and ; implied by defn of maintainedrel (wffdefn rel def)
		       (relationimplementation rel imp)
		       (not (eql imp 'defined))
		       ; also in defn of maintrel (ruletrigger rule trigger)
		       ; also in defn (maintainingtrigger def rel trigger)
		       ))))
  (compile-ap '(lambda (rel def rule) (declare (ignore rel def))
		       (-- maintainrule rule)))
  :incremental)

; However, that only requires that, IF there's a wffdefn, then 
; a maintaining rule is present iff there's a non-DEFINED implementation
; Next, when the Maintainedrel tuple goes, remove the rule
(alwaysrequire 'maintainrules-must-maintain-defn
  '(A (maintainrule#rule) (E (rel def) (maintainedrel rel def rule)))
  (compile-ap '(lambda (rule) (-- maintainrule rule)))
  :incremental)

; Now we have rules that create/remove maintainrules when appropriate.
; We just have to keep MAINTAINEDREL coordinated.
; I claim that it's ok (and a lot easier) for MAINTAINEDREL to be defined in
; terms of wffdefn.

#+ignore ; thought I needed this for symbolics compiler bug - let's see
(global:undefun (LOOKUP-GENERATOR  (RELATIONp 'MAINTAINEDREL) '(INPUT INPUT OUTPUT)))

(++ no-trigger
    (canonicalize-trigger
      '((rel def rule) s.t.
	(e (trigger code arity)
	   (and (PREVIOUSLY (not (maintainedrel rel def rule)))
		(start (relationarity rel arity))
		(maintainrule rule)
		(ruletrigger rule trigger)
		(rulecode rule code)
		(wffdefn rel def)
		(maintainingtrigger def rel trigger)
		(maintainingcode rel arity code))))))
; tell the rule compiler not
; to worry about the previous rules that turn out to be constraints when 
; a new rel is declared

(++ no-trigger
    (canonicalize-trigger
      '((REL DEF RULE)
	S.T.
	(E (TRIGGER CODE ARITY)
	   (AND (PREVIOUSLY (NOT (MAINTAINEDREL REL DEF RULE)))
		(START (WFFDEFN REL DEF))
		(RELATIONARITY REL ARITY)
		(MAINTAINRULE RULE)
		(RULETRIGGER RULE TRIGGER)
		(RULECODE RULE CODE)
		(MAINTAININGTRIGGER DEF REL TRIGGER)
		(MAINTAININGCODE REL ARITY CODE))))))
(++ no-trigger
    (canonicalize-trigger
      '((REL DEF RULE)
	S.T.
	(E (TRIGGER CODE ARITY)
	   (AND (PREVIOUSLY (NOT (MAINTAINEDREL REL DEF RULE)))
		(START (RULETRIGGER RULE TRIGGER))
		(RELATIONARITY REL ARITY)
		(WFFDEFN REL DEF)
		(MAINTAINRULE RULE)
		(RULECODE RULE CODE)
		(MAINTAININGTRIGGER DEF REL TRIGGER)
		(MAINTAININGCODE REL ARITY CODE))))))
(++ no-trigger
    (canonicalize-trigger
      '((REL DEF RULE)
	S.T.
	(E (TRIGGER CODE ARITY)
	   (AND (PREVIOUSLY (NOT (MAINTAINEDREL REL DEF RULE)))
		(START (RULECODE RULE CODE))
		(RELATIONARITY REL ARITY)
		(WFFDEFN REL DEF)
		(MAINTAINRULE RULE)
		(RULETRIGGER RULE TRIGGER)
		(MAINTAININGTRIGGER DEF REL TRIGGER)
		(MAINTAININGCODE REL ARITY CODE))))))
; the argument is that maintainrule should be enough

; since the maintaining rule does not yet exist, the code of the previous
; rule will not restore consistency (since that rule expects MaintainedRel
; to become true).  Therefore we have to explicitly add the MaintainedRel
; tuple this one time.  However in order to do that we need the rule.
; This we do the body of the previous rule, which conveniently returns
; the rule that it creates, and assert MaintainedRel of the result - which
; also prevents the previous rule from firing.
(compiled
  (let (;(triggereffortwarning 9999)
	;(triggersizewarning 999)  ; avoid warnings in loading the system
	(rel (relationp 'MaintainedRel))
	(def '((rel def rule) s.t.
	       (E (trigger code arity)
		  (and (maintainrule rule)                ; needn't be in E
		       (RuleTrigger rule trigger)
		       (wffdefn rel def)                  ; ditto
		       (MaintainingTrigger def rel trigger)
		       (RuleCode rule code)
		       (RelationArity rel arity)
		       (MaintainingCode rel arity code))))))
    (or (?? wffdefn rel def)  ; can't do it if already done - cause maintained
	(atomic (++ WffDefn rel def)
		(++ maintainedrel rel def
		    (make-maintain
		      (pack* "Maintain-" (relationnamep rel))
		      (maintainreltrigger def rel)
		      (functional-equivalence-testable
			(compile-ap (maintainrelcode rel (arity* rel)))
			(list :maintain rel (arity* rel))
			(format nil "Maintain-~A" (relationnamep rel)))))))))

; now as promised we maintain isubrel+ and subrel

(compiled
  (++ wffdefn (relationp 'isubrel+)
      '((subrel superrel) s.t.
	(or (isubrel subrel superrel)
	    (and (relation subrel) (eql subrel superrel))))))

(compiled
  (++ wffdefn (relationp 'subrel-stored)
      '((r1 r2) s.t. (isubrel+* r1 r2))))

(compiled
  (do-s.t. ((rel rule def mnode)
	    (and (maintainedrel rel def rule) (matchmaintain mnode rule)))
       (declare (ignorable rule def))
       (++ maintain-mnode rel mnode)))

(compiled
  (++ wffdefn (relationp 'maintain-mnode)
      '((rel mnode) s.t.
	(E (rule def) (and (maintainedrel rel def rule) (matchmaintain mnode rule))))))

(setq maintaining-mnodes t)

;; ---- relation-in-defn ----
(tuple-comparison rel-implementation)
; bootstrapping problem - have to cache comparetuple to avoid infinite recursion
(++ definedrelname 'rule-or-relation
    '((x) s.t. (or (rule x) (relation x))))
(++ subtype (dbo type relation) (dbo type rule-or-relation))
(++ subtype (dbo type rule) (dbo type rule-or-relation))
(++ subtype (dbo type rule-or-relation) (dbo type dbobject))

; expanddesc (or something similar) needed for cases like (R1 (R2 x =))
; 7/93 - DonC
(defun rels-in-wff (wff &aux ans)
  ; a list of relations used in wff
  (declare (special ans))
  (try (progn
	 (map-wff (third (expanddescription
			  (cond ((and (listp wff) (listp (car wff))
				      (listp (cdr wff))
				      (symbolp (cadr wff))
				      (string-equal (symbol-name (cadr wff))
						    "s.t."))
				 wff)
				(t (list nil 's.t. wff)))
			  :AllowEvalArgs t :KeepStarts t))
	   :primitive-wff	  
	   #'(lambda (rel &rest ignore) (declare (ignore ignore))
		     (pushnew rel ans)))
	 ans)
       'expanddescription nil))
#+ignore ; previous defn takes a long time cause of expanddesc. - not needed
(defun rels-in-wff (wff &aux ans)
  ; a list of relations used in wff
  (declare (special ans))
  (map-wff (cond ((?? closed-wff wff) wff) ((?? description wff) (caddr wff)) (t 'true))
	   :primitive-wff	  
	   #'(lambda (rel &rest ignore) (declare (ignore ignore))
		     (pushnew rel ans)))
  ans)

(++ codedrelname 'relation-in-wff
    '((rel wff) s.t. (member rel (rels-in-wff wff))))

(++ possibletoadd (relationp 'relation-in-wff) t)
(++ possibletodelete (relationp 'relation-in-wff) t)
(++ nontriggerable (relationp 'relation-in-wff))

(simplegenerator '(relation-in-wff output trigger) '(rels-in-wff trigger))
(++ compare-relation (dbo relation relation-in-wff) 1 (dbo relation equal)) 
(++ doubleproprelname 'relation-in-defn)
(++ relsize (relationp 'relation-in-defn) '(output output) 5000)
(++ relsize (relationp 'relation-in-defn) '(input output) 50)
(++ relsize (relationp 'relation-in-defn) '(output input) 10)

; ---- relations includes primitive versions of these
(defun maintainedrels-affected-by-node (mnode)
  (when (matchnode-p mnode)
    (let ((queue (list mnode)) nodes ans next)
      (loop while (setq next (pop queue))
	    unless (member next nodes)
	    when (member :maintain (matchactive next)) do
	    (push next nodes) (setq queue (append (matchsuccessors next) queue)))
      (loop for n in nodes do
	    (loop for rel s.t. (maintain-mnode rel n) do (pushnew rel ans)))
      ans)))
(defun maintainedrels-affected-by-rel (rel)       
  (listof x s.t. (and (relation-in-defn rel x)
		      (E (imp) (and (relationimplementation x imp)
				    (not (eql imp 'defined)))))))

(atomic
  (loop for (rel rule-or-rel) s.t.
	(E (trigger-or-def) (and (or (and (rule rule-or-rel)
					  (ruletrigger rule-or-rel trigger-or-def))
				     (and (relation rule-or-rel)
					  (wffdefn rule-or-rel trigger-or-def)))
				 (relation-in-wff rel trigger-or-def)))
	do (++ relation-in-defn rel rule-or-rel)))


; * * * potential source of error (how should this be documented?) * * *
; We assume in this relation (more precisely in the implementation of the
; rule to maintain it) that macros used in wffs do not change in such a way
; that existing definitions (wffdefns/ruletriggers) expand into a different
; set of relations.
;
; These enable the rule to compile - now we attempt to justify them:
; We intend that the relations used by a relation or rule always exist.
; Thus, we have no fear that the introduction of a relation will make
; a rel-or-rule use it, since in that case the rel-or-rule should not 
; have been allowed to exist before.
; In the case where the removal of a rel would cause it not to be used
; by the rel-or-rule, that makes the rel-or-rule invalid, and this is
; detected by the removal of the rel.  This causes the rule-or-rel to
; be removed which in turn allows us to notice that the use ceases.
(++ no-trigger
    (canonicalize-trigger
      '((rel trigger-or-def) s.t.
	(start (NOT (RELATION-IN-WFF REL TRIGGER-OR-DEF))))))

(++ no-trigger
    (canonicalize-trigger
      '((rel trigger-or-def) s.t.
	(start (RELATION-IN-WFF REL TRIGGER-OR-DEF)))))

(++ wffdefn (relationp 'relation-in-defn)
    '((rel rule-or-rel) s.t.
      (E (trigger-or-def) (or (and ; not needed (rule rule-or-rel)
				   (ruletrigger rule-or-rel trigger-or-def)
				   (relation-in-wff rel trigger-or-def))
			      (and ; not needed (relation rule-or-rel)
				   (wffdefn rule-or-rel trigger-or-def)
				   (relation-in-wff rel trigger-or-def))))))

; however that did not maintain itself (!) so, ...
(let ((fix-maintained-relation t))
  (loop for rule-or-rel in
	(cons (dbo relation relation-in-defn)
	      (loop for (x y) s.t.
		    (maintainedrel (dbo relation relation-in-defn) x y)
		    collect y))
	do (atomic
	     (loop for (rel) s.t.
		   (E (trigger-or-def)
		      (and (or (and (rule rule-or-rel)
				    (ruletrigger rule-or-rel trigger-or-def))
			       (and (relation rule-or-rel)
				    (wffdefn rule-or-rel trigger-or-def)))
			   (relation-in-wff rel trigger-or-def)))
		   do (++ relation-in-defn rel rule-or-rel)))))


(++ transitive-closure 'relation-in-defn 'relation-in-defn*)
(++ relsize (relationp 'relation-in-defn*) '(output input) 20)
(++ relsize (relationp 'relation-in-defn*) '(output output) 9000)

; these have to be added since they are not yet maintained
(++ Possibletoadd (relationp 'relation-in-defn*) t)
(++ Possibletodelete (relationp 'relation-in-defn*) t)
(++ trigger (relationp 'relation-in-defn) nil
    'trigger--tclosures (relationp 'relation-in-defn*) nil)
(++ trigger (relationp 'relation-in-defn) t
    'trigger++tclosures (relationp 'relation-in-defn*) t)
(++ relsize (dbo relation relation-in-defn*) '(input output) 100)
; The main idea here is to test the closure by generating the rels-in
; something rather than generating the things that use the other one
; The example of classification shows why we don't want to go the other way.
