;-*- Mode:LISP; Package:AP5; Base:10.; Syntax:Common-Lisp -*-

(in-package "AP5")
; declaration and compilation of rules, etc.
#|
   RULE-HANDLER-BIND ({(rulename responsefn)}* {form}+)
the macro RULE-HANDLER-BIND provides for dynamically scoped "reactions" to
globally scoped database conditions.  The globally scoped conditions are 
specified as always with AP5 named "rule"s: consistency rules, 
automation rules, consistency checkers, automation generators.  Each kind of
rule provides its own protocol for a function that responds to the condition
defined by the rule's "trigger" -- e.g., automation generator responses
execute in a 2-state environment and may use ENQUEUE-AUTOMATION to 
add entries to the automation queue.  

RULE-HANDLER-BIND allows the programmer to dynamically scope an
alternative responder for a rule.  When a rule is triggered, the dynamic
responder with the smallest scope is selected.  Its <resonsefn> is
applied to the same arguments as a global reaction for the rule.
The responsefn is responsible for determining whether this dynamic responder
is appropriate for the triggering and, if so, for providing (but not running)
a suitable response.
If the value returned by <responsefn> is  NIL, the dynamically scoped responder
is ignored and the search for a responder continues -- a dynamic
responder with larger scope may be found, or the global responder,
provided with the rule definition, may be used.  A <responsefn>
returning a non-NIL value MUST return a value that is a function
obeying the same calling conventions and semantic requirements imposed
on a global responder for the named rule.

Each <rulename> and <responsefn> provides a single dynamically scoped
responder.  <rulename> is not evaluated, <responsefn> is.  
The forms are executed as on implicit
PROGN.  Their execution is the scope of the responders.  A <responsefn>
is given read access to two database states.  It is not permitted
to write into the database.

==============================================================
CLF>(defrelation abc :arity 1)
[defrel ABC]
ABC
CLF>(defautomation abcrule
       ((x) s.t. (start (abc x)))
       (lambda (x) (print "global response")))
ABCRULE
CLF>(++ abc 0)

"global response" 
NIL
CLF>(rule-handler-bind ((abcrule #'(lambda (x)
				     #'(lambda (x) (print "local response")))))
      (++ abc 1))

"local response" 
NIL
=======================================================
RULE-HANDLER-CASE (expression {(rulename lambda-list {declaration}* {form}+)}*)

is a simplified version of RULE-HANDLER-BIND for use when the
dynamically scoped responder is unconditionally suitable for all
triggerings of the named rules.  In this case, the lambda-list,
declarations and forms associated with the rulename provide the
response -- a function obeying the same calling conventions and
semantic requirements imposed on a global responder for the named
rule.

=========================================================
CLF>(rule-handler-case (++ abc 2)
	     ((abcrule  (x) (print "local response"))))

"local response" 
NIL
=========================================================

No relational access is provided to dynamically scoped responders
(although non-triggerable access could be provided at low overhead.)
The relation RULECODE provides access to the global responder only.

|#

(define-condition rule-triggered (#-clisp condition)
  ; subclass of condition is implied?  In lucid/allegro it's needed,
  ; in clisp it actually hurts, Harlequin ok either way
  ((rule #-lucid :accessor #-lucid rule-triggered-rule
	#-lucid :initarg #-lucid :rule)
   
   (bindings #-lucid :initform #-lucid nil
	     #-lucid :accessor #-lucid rule-triggered-bindings
	     #-lucid :initarg #-lucid :bindings))
  (:documentation "signalled to find dynamically scoped rule reactions"))

(defvar-resettable *dynamic-responders-available*
  #+no-conditions nil 
  #-no-conditions t)

(defmacro rule-handler-bind (handlers &body body
				      &aux (g (gensym)) (response (gensym)))
  ;; handlers is a list, each element being  (rulename responsefn)
  ;; Responsefn should be a piece of code whose VALUE is NIL or
  ;; a function with the
  ;; correct protocol for the rule named Rulename
  ;; If it returns NIL, responsefn will not be evaluated and
  ;; the search for a rule response will continue.
  (if handlers
    `(let ((*dynamic-responders-available* t))
       #+no-conditions (error "need condition system for dynamic responders")
       #-no-conditions
       (handler-bind
         ((rule-triggered
	   #'(lambda (,g)
	       (case (rule-triggered-rule ,g)
		     ,. (loop for e in handlers collect
			      `(,(first e)
				(let ((,response
				       (apply ,(second e)
					      (rule-triggered-bindings ,g))))
				  (when ,response
					(invoke-restart 'use-rule-response
							 ,response)))))))))
    ,. body))
    `(progn ,. body)))

(defmacro rule-handler-case (expression handlers &aux (g (gensym)))
  ;; handlers is a list, each element being  
  ;; (rulename lambda-list {declaration}* {form}+)

  (if handlers
    `(let ((*dynamic-responders-available* t))
       #+no-conditions (error "need condition system for dynamic responders")
       #-no-conditions
       (handler-bind
         ((rule-triggered
	   #'(lambda (,g)
	       (case (rule-triggered-rule ,g)
		     ,. (loop for e in handlers collect
			      `(,(first e)
				(invoke-restart 'use-rule-response
				    (function (lambda ,.(cdr e))))))))))
    ,expression))
    expression))

(defvar *rule-signal* (make-condition 'rule-triggered))

(defun effective-rule-code (rule inputs)
  ;; THIS IMPLEMENTATION ASSUMES ONLY ONE PROCESS MAY BE DOING THIS AT A TIME!!
  ;; IT USES A GLOBAL RESOURCE *rule-signal*
  (if *dynamic-responders-available*
      #+no-conditions (error "need condition system for dynamic responders")
      #-no-conditions
      (unwind-protect
	  (progn (setf (rule-triggered-bindings *rule-signal*) inputs
		       (rule-triggered-rule *rule-signal*) (rulename rule))
		 (restart-case
		  (let ((|UpdateStatus | 'responder-search))
		    (signal *rule-signal*)
		    ;; if there is no handler, use the "global" code
		    (rulecode rule))
		  (use-rule-response (fn) fn)))
	(setf (rule-triggered-bindings *rule-signal*) nil))
    (rulecode rule)))

#+ignore  ; put in utilities just to avoid that silly redefining warning
(defstruct (matchnode (:include DBObject) (:conc-name nil) :named)
  matchvars matchwff matchcode matchcompare
  matchsuccessors matchpredecessors matchrels matchactive)
; moved to properties (rels): matchconsistencies matchautomations

#|
 matchcode accepts the same fixed number of arguments of the same meanings from
 each of the predecessor nodes, and uses them to generate a list of instantiations
 of matchvars s.t. matchwff.  This can be used to trigger the rules and also as
 input to the successor nodes.  There are some nodes with no predecessors which
 are triggered directly by atomicupdate - these always accept inputs of the form
 (x y z) s.t. Start (Rel x y z) or (x y z) s.t. Start ~(Rel x y z)
 Matchcompare decides whether two instantiations of matchvars are really the same,
 which depends on the comparison relations for the variables involved.
 MatchRels contains a list of relations that must change in order to affect the
 output of this node.  This is used to avoid redoing work from one consistency
 cycle to the next.
 MatchActive is a list of the types of rules connected to (any successor of)
 the node.  When we delete a rule, this can be turned off so as to not waste
 (much) time in matching, yet stick around in case it's needed again later.
|#
(defun NodeMatches (node vars wff &aux (keepstarts t))
  (declare (special keepstarts))
  ; if this node returns right vals in right order, return it
  ; if it returns right vals in wrong order, see if it has a successor that
  ; orders them right - if so return that, if not build one
  ; if this node returns the wrong vals, return nil
  (and (eq (length vars) (length (matchvars node)))
       (loop for v1 in vars as v2 in (matchvars node) always
	     (equal (varcompare v1) (varcompare v2)))
       (same-wff (matchwff node) wff (mapcar #'cons (matchvars node) vars) t)))

; note: there was code that had to change when we started matching non-equal
; nodes - all the places where (matchvars x) is replaced by the vars of the
; wff being triggered (since the vars of the node may be a renamed version).
;; It seems to be a waste of time to consider permutations.
;  In loading the system, of 456 tries, 122 were equal, 49 were simple renaming
;  (caught by current code), 5 were permutations, others were different.
#+ignore 
(defun permutations (l)
  (cond ((null (cdr l)) (list l))
	(t (loop for x in l nconc
		 (loop for rest in (permutations (remove x l))
		       collect (cons x rest))))))
#+ignore  ; Of 280 that were different, 58 had different number of vars. Of the others, only
   ; 14 had same set of rels (these all had different constants - for classification)
(defun rels-in (wff &aux ans)
    (declare (special ans))
    (map-wff wff
      :primitive-wff
       #'(lambda (rel &rest ignore) (declare (ignore ignore))
	   (pushnew (or (relationp rel) (error "non-relation?")) ans)))
    ans)

#+ignore  ;previous dumber one
(defun NodeMatches (node vars wff)
  ; if this node returns right vals in right order, return it
  ; if it returns right vals in wrong order, see if it has a successor that
  ; orders them right - if so return that, if not build one
  ; if this node returns the wrong vals, return nil
  (and (equal vars (matchvars node))
       (equal wff (matchwff node))))
; summary of experiment:
;  61% really different, 39% equivalent
;  27% are equal, 11% renamings, 1% permutations 
;  (permutations would still require more work - and new matchnodes)

(defun MatchActivate (node inputs class-to-activate &aux tmp tmptree)
  (declare (special |Activations | activationtrees))
  (or (setq tmp (assoc node |Activations |))
      (push (setq tmp (list node)) |Activations |))
  (or (setq tmptree (cdr (assoc node Activationtrees)))
      (push (cons node (setq tmptree (createtree))) Activationtrees))
  ; activations is alist of (node outputs1 outputs2 ...) where outputs are lists of
  ; objects s.t. (apply '(lambda <node.vars>(?? . <node.wff>)) output) => T
  (loop for output in (do-matchcode node inputs) do
	(cond ((not (do-matchcompare node (or output '(t)) tmptree))
	       (treeadder (or output '(t)) tmptree
			  (or (matchcompare node) '(eq)))
	       (push output (cdr tmp)) ;add it
	       (loop for s in (matchsuccessors node)
		     when (member class-to-activate (matchactive s))
		     unless
		     #+ignore (member s (assoc class-to-activate suspended-matchnodes))
		     (eql generation# (get-structure-property s class-to-activate))
		     do (MatchActivate s output class-to-activate))))))

; separated this to time it
(defun do-matchcode (node inputs)
  (apply (matchcode node) inputs))

; separated this to time it
(defun do-matchcompare (node tuple tree)
  (treetester tuple tree (or (matchcompare node) '(eq))))

(defun DoConsistencyRules (activations &aux lastupdate done)
  (loop for a in (cons (list true-matchnode nil) Activations)
        ;; why the cons above when it's going to be filtered by next line?
	when (cdr a) do ; non-negligible optimization
	(loop for d in (matchconsistencies (car a))
	      unless (member d suspended-rules) do ; the matchnode
	      (if (ConsistencyChecker-P d)
		  (loop for inputs in (cdr a) do
			(setq lastupdate (car |Updates |))
			(when (or (DoConsistencyRule d inputs)
				  (not (eq lastupdate (car |Updates |))))
			  (push (cons d inputs) done))
			(loop for u in |Updates | until (eql u lastupdate) do
			      (setf (updreason u) (list :consistency d inputs
							(updreason u)))))
		  ; normal consistencyrule
		  (loop for inputs in (cdr a) do
			(push (cons d inputs) done)
			(setq lastupdate (car |Updates |))
			(DoConsistencyRule d inputs)
			(loop for u in |Updates | until (eql u lastupdate) do
			      (setf (updreason u) (list :consistency d inputs
							(updreason u))))))))
  done) ; return list of activations that were violated

(defun DoConsistencyRule (*current-rule* inputs)
  (apply (effective-rule-code *current-rule* inputs) inputs))

; while we're at it, a copy for maintains
(defun DoMaintainRule (*current-rule* inputs)
  (apply (rulecode *current-rule*) inputs))

; Perhaps it would be worth trying to record the history that triggered
; again to aid debugging

(defun DoAutomationRulesNew (&aux inv)
  (when *automation-queue*
    (let (|Updates | |Requirements | EXPLICIT-MI ORIGINALUPDATES DELTA
	  |Again | AGAINTREES |Maintain | |Direct | DIRECTTREES OLD-DIRECT
	  INDEXDELTA)
      (declare (special |Updates | |Requirements | EXPLICIT-MI ORIGINALUPDATES DELTA
	  |Again | AGAINTREES |Maintain | |Direct | DIRECTTREES OLD-DIRECT
	  INDEXDELTA))
      ;;; the let bindings are just to compensate for the bindings still
      ;;; visible from atomics compiled when the *outer-atomic-state-vars*
      ;;; were scoped to widely.
    (tagbody
      retry
      (unwind-protect
	  (with-whostate "Run Automations"
	    (loop while *automation-queue* do
		  (apply #'doautomationrule (setq inv (pop *automation-queue*)))))
	(when *automation-queue*
	  (cerror "Abort this automation, then decide whether to let the rest execute."
		  "A throw or error is propogating out of the automation rule ~a.~
                   ~&If this occurs, ~d pending rule invocations will be lost."
		  (car inv) (length *automation-queue*))
	  ;; if user aborts he gets complaint about aborting from cleanup form
	  (when (y-or-n-p "Execute the remaining automations?") (go retry))))))))

#+ignore ;; this was the version when automation rules still executed inside
        ;; atomic's withwriteaccess
(defun DoAutomationRules (activations)
  (loop for a in Activations do
	(loop for d in (matchautomations (car a)) do ; the matchnode
	      (loop for inputs in (cdr a) do
		    (DoAutomationRule d inputs)))))

(defun DoAutomationRule (*current-rule* function inputs)
  (apply function inputs))
; This is broken out to help users debug their rules

(Defun Ident(&rest args) (list (copy-seq args))) ;used for collection matchnodes

(defun get-match-compare (vars)
  (loop for v in vars collect
	(let ((c (varcompare v)))
	  (when (listp c)
	    (cond ((not (cdr (setq c (remove-duplicates c))))
		   (setq c (car c)))
		  ((not (cdr (setq c (most-specific-types-of c))))
		   ; expect this not to be needed until defined (if ever)
		   (setq c (car c)))
		  (t (error "multiple equivalence relations for matchvar~
                             - show this to DonC"))))
	  (setq c (c-and-c c))
	  (cond ((listp c) (car c)) (t c)))))
#+ignore ; former version
(defun get-match-compare (vars)
  (compile-ap
    `(lambda (tup1 tup2)
       #-ti(equal2 tup1 tup2 ,(loop for v in vars collect (varcompare v)))
       #+ti ; avoid extra macroexpansions until rel. 3
       (progn nil (equal2 tup1 tup2 ,(loop for v in vars collect (varcompare v)))))))

(defun union* (lists &aux ans)
  (loop while lists do (setq ans (union ans (pop lists))))
  ans)
	       

(defun changerels-in-wff (wff &aux ans in-start)
  ; a list of relations used in wff outside PREVIOUSLY
  (declare (special ans in-start))
  (map-wff wff
	   :primitive-wff
	   #'(lambda (rel &rest ignore) (declare (ignore ignore))
	       (loop for (x y z w) in (get-triggers-of rel)
		 ;; evidently have to change vars to NIL to avoid warnings
		 do (progn (pushnew x ans) y z w)) ;; doesn't avoid warnings
	       (pushnew (or (relationp rel) (error "non relation?")) ans))
	   :defined-wff
	   #'(lambda (wff defn)
	       (pushnew (or (relationp (car wff)) (error "non relation?")) ans)
	       (map-wff-internal defn))		     
	   :temporal-op
	   #'(lambda (op wff)
	       (unless (eq op 'previously)
		 (map-wff-internal wff))))
  ans)

;; let's try out the new version ...
#-old-rule-compiler
(defun detect (vars wff) (detect-or-* vars wff))
#-old-rule-compiler
(defun detect* (vars wff) (detect-or-* vars wff t))
#-old-rule-compiler
(defun find-triggers (vars wff type &optional stack
		      &aux result (currentvars vars))
  ; type is one of start, start*, start+
  (declare (special stack currentvars type))
  (flet ((get-trigger (w herevars &aux mnode matchwff genvars alist
			 (newwff 'true) (keepstarts t))
	  (declare (special currentvars stack keepstarts))
	  (when (and (not (no-trigger herevars (list 'start w)))
		     (setf mnode (detectinput herevars w))
		     )	; if nil don't push anything above 
	    (loop for wff in stack when (consp wff) do
		  ; weird interpretation of subst
		  (setf newwff (subst newwff '* wff)))
	    (setf matchwff
		  ;;vars-to-names-wff ;; not needed -
		  ;;decache-rel expects matchvars/matchwff to be a description (args to detect)
		  (simplify
		    `(E ,(fldifference currentvars vars) (and (start ,w) ,newwff))))
	    (unless (no-trigger vars matchwff)      
	      (setf newwff
		    (simplify
		      `(E ,(fldifference (fldifference currentvars vars) herevars) ,newwff))
		    genvars (fldifference vars herevars))
	      (let ((n 0) vars-used)
		(map-wff newwff :primitive-wff
			 #'(lambda (rel &rest args) (declare (ignore rel))
				   (loop for a in args when (variable-p a) do
					 (pushnew (varname a) vars-used))))
		(setf alist (loop for var in (append herevars genvars) collect
				  (cons var (let (name)
					      (loop while (member (setf name (pack* 'x (incf n)))
								  vars-used)
						    do nil)
					      name)))))
						; a lot of trouble to make sure it all works out
	      (list mnode newwff
		    `(lambda ,(loop for v in herevars collect (cdr (assoc v alist)))
		       ,@(loop for v in herevars collect (cdr (assoc v alist)))
						; avoid compiler warnings
		       (loop for ,(loop for v in genvars collect (cdr (assoc v alist))) s.t.
			     ,(map-copy-wff newwff
					    :primitive-wff
					    #'(lambda (rel &rest args)
						(cons rel
						      (loop for a in args collect
							    (cond ((variable-p a)
								   (or (cdr (assoc a alist))
								       (varname a)))
								  (t a)))))
					    :quantified-wff
					    #'(lambda (q v w)
						(list q (loop for a in v collect
							      (cond ((variable-p a)
								     (or (cdr (assoc a alist))
									 (varname a)))
								    (t a)))
						      (map-wff-internal w))))
			     collect (list ,@(loop for v in vars collect (cdr (assoc v alist)))))
		       #+ignore
; which is better?  I choose this cause the
; loop for nil generator can at least be saved to the .bin file
		       (cond (genvars
			      `(loop for ,(vars-to-names genvars) s.t. ,newwff
				     collect (list ,@(vars-to-names vars))))
			     (t `(when (?? . ,newwff) (list (list ,@(vars-to-names vars)))))))
		    matchwff)))))
  (map-wff wff
     :quantified-wff
     #'(lambda (q v w)
	 (case q
	   (a (case type
		(start (let ((stack (cons `(and * (A ,v ,w)) stack))
			     (currentvars (append v currentvars)))
			 (declare (special stack currentvars))
			 (map-wff-internal w)))
		(start* (let ((stack (cons `(and * (A ,v ,w)) stack))
			      (currentvars (append v currentvars))
			      (type 'start)) ; could have been (and was) start+
			  (declare (special stack currentvars type))
			  (map-wff-internal w)))
		(start+ (let ((currentvars (append v currentvars)))
			  (declare (special currentvars))
			  (map-wff-internal w)))))
	   (e (case type
		(start (let ((stack (cons `(and * (not (previously (E ,v ,w)))) stack))
			     (currentvars (append v currentvars)))
			 (declare (special stack currentvars))
			 (map-wff-internal w)))
		(start* (let ((stack (cons '* stack))
			      (currentvars (append v currentvars)))
			  (declare (special stack currentvars))
			  (map-wff-internal w)))
		(start+ (let ((currentvars (append v currentvars)))
			  (declare (special currentvars))
			  (map-wff-internal w)))))))
     :boolean-op
     #'(lambda (op &rest wffs)
	 (cond
	   ((eq op 'not)
	    (let ((herevars (remove-if-not #'variable-p
					   (remove-duplicates (cdar wffs))))
		  res)
	      (when (setf res (get-trigger (cons op wffs) herevars))
		(push res result))))
	   ((eq type 'start+)
	    (loop for w in wffs do (map-wff-internal w)))
	   ((eq op 'and)
	    (loop for w in wffs do
		  (let ((stack (cons `(and * ,@(remove w wffs)) stack)))
		    (declare (special stack))
		    (map-wff-internal w))))
	   ((eq op 'or)
	    (loop for w in wffs do
		  (let ((stack (cons (cond ((eq type 'start*) '*)
					   (t `(and * (not (previously
							     (or ,@(remove w wffs)))))))
				     stack)))
		    (declare (special stack))
		    (map-wff-internal w))))
	   (t (error "unknown connective"))))
     #+ignore :temporal-op
     #+ignore #'(lambda (op w)
	 (case op
	   (start (let (*-p (in-start t)) (declare (special *-p in-start))
		       (map-wff-internal w)))
	   (start* (let ((*-p t) (in-start t)) (declare (special *-p in-start))
			(map-wff-internal w)))
	   (previously (map-wff-internal w))
	   (t (error "impossible"))))
     :primitive-wff
     #'(lambda (&rest w)
	 (let ((herevars (remove-if-not #'variable-p (remove-duplicates (cdr w))))
	       res)
	   (when (setf res (get-trigger w herevars)) (push res result))))))
  result)



#+ignore ; previous version
(defun get-trigger (w herevars &aux mnode matchwff (newwff 'true) (keepstarts t))
  (declare (special currentvars stack))
  (when (and (not (no-trigger herevars (list 'start w)))
	     (setq mnode (detectinput herevars w))) ; if nil don't push anything above 
    (loop for wff in stack do
	  (setq newwff (subst newwff '* wff)))
    (setq matchwff
	  ;;vars-to-names-wff ;; not needed -
	  ;decache-rel expects matchvars/matchwff to be a description (args to detect)
	    (simplify
	      `(E ,(fldifference currentvars vars) (and (start ,w) ,newwff))))
    (unless (no-trigger vars matchwff)      
      (setq newwff
	    (vars-to-names-wff
	      (simplify
		`(E ,(fldifference (fldifference currentvars vars) herevars) ,newwff))))
      (list mnode newwff
	    `(lambda ,(vars-to-names herevars)
	       ,@(vars-to-names herevars) ; avoid compiler warnings
	       ,(let ((genvars (fldifference vars herevars)))
		  `(loop for ,(vars-to-names genvars) s.t. ,newwff
			 collect (list ,@(vars-to-names vars)))
		  #+ignore ; which is better?  I choose this cause the
		  ; loop for nil generator can at least be saved to the .bin file
		  (cond (genvars `(loop for ,(vars-to-names genvars) s.t. ,newwff
					collect (list ,@(vars-to-names vars))))
			(t `(when (?? . ,newwff) (list (list ,@(vars-to-names vars))))))))
	    matchwff))))

(defvar matchcode-fn-cache)
(DEFUN TOP-SUBLIS (ALIST LIST &AUX ENTRY)
  (LOOP FOR X IN LIST COLLECT
	(COND ((SETQ ENTRY (ASSOC X ALIST)) (CDR ENTRY)) (T X))))
#+ignore ; previous version
; This weird function is reasonable only because we know so much
; about the lists to which it will be applied
(defun top-sublis (alist list &optional (levels 1) &aux entry)
  (loop for x in list collect
	(cond ((setq entry (assoc x alist)) (cdr entry))
	      ((= levels 1) x)
	      ((not (listp x)) x)
	      (t (top-sublis alist x (1- levels))))))

(defun compile-matchcode (loop-spec &aux body cdesc evlvars evlrels inputs outputs desc
			  fn-arg table-fn (*fn-being-compiled* (gentemp "F" ap-compiled)))
  ; loop-spec is what comes out of get-trigger
  ; this is supposed to be equivalent to that function but faster to compute
  ; *fn-being-compiled* used in order to get generators recorded before compiling the fn
  (unless (eq (caar (last loop-spec)) 'loop)
    (return-from compile-matchcode (compile-ap loop-spec)))
  (setf inputs (cadr loop-spec)
	desc (car (last loop-spec))
	outputs (car (last desc)))
  (setf desc (list (third desc) (fourth desc) (fifth desc)))
  (multiple-value-setq (body evlvars evlrels)
    (ExpandDescription desc :allowevalargs t :keepstarts t))
  (multiple-value-setq (body cdesc) (get-generator body evlvars evlrels))
  (setf fn-arg (kwote (lookup-gen cdesc)))
  ; next two lines - very poor protocol
  (setf body (third body)) ;; part of patch to generators for aclpc bug
  (setf (second body) '|GenFn|)
  (dolist (x evlvars) (rplacd x (second x)))
  (setf body (top-sublis evlvars body) ; we know that the args are only vars
	table-fn
	`(lambda (|GenFn| ,@inputs &aux |GenFun | |Exhausted | ,@(car desc))
	   #+lucid (declare (ignore |Exhausted |))
	   ;; Monday 2010/10/11	following declare was under #+allegro
	   (declare (ignorable |Exhausted |))
	     ,@inputs
	     (setq |GenFun | ,body)
	     (loop until (MULTIPLE-VALUE-SETQ (|Exhausted | ,@(car desc))
			   (FUNCALL |GenFun |))
		   collect ,outputs)))
  #+ignore ; now canonicalize it - moved back into get-trigger
  (setq table-fn (top-sublis (loop for var in (append inputs (car desc))
				   as num from 1 collect (cons var (pack* 'x num)))
			     table-fn 3))
  ; don't replace args like (dbo type entity) with (dbo x1 entity)
  (setf table-fn
	(or (gethash table-fn matchcode-fn-cache)
	    (setf (gethash table-fn matchcode-fn-cache) (compile-ap table-fn))))
  ; now this is supposed to compile fast
  (compile-ap `(lambda (&rest args) (apply ',table-fn ,fn-arg args)) *fn-being-compiled*))

(Defun Detect-or-* (vars wff &optional *-p stack &aux newwff inputs)
 (with-goal (list "detect" vars "s.t." (list (cond (*-p 'start*) (t 'start)) wff))
  ; build the stuff that will recognize when any instantiation of vars starts
  ; to satisfy wff.  Sharing of this structure is desirable.
  ; return a match node whose outputs are {vars s.t. (start wff)}.
  ; return nil if it cannot become true
  (cond ((no-trigger vars (list (cond (*-p 'start*) (t 'start)) wff)) nil)
	((member wff '(true false)) nil)
	; even in this case we have to deal with the stack
	((and (null stack)
	      (or (not (compoundwffp wff)) ; positive input node
		  (eql (car wff) 'not))) ;negative input node
	 (DetectInput vars wff))
	((null (setq inputs (find-triggers vars wff
					   (cond (*-p 'start*) (t 'start)) stack)))
	 nil)
	((let ((keepstarts t)) (declare (special keepstarts))
	   (setq newwff `(,(cond ((and *-p (compoundwffp wff) (not (eq (car wff) 'not)))
				  'start*)
				 (t 'start))
			  ,wff))
	   (loop for s in stack when (consp s) ; see previous comment
		 do (setq newwff (subst newwff '* s)))
	   (setq newwff (simplify newwff))
	   nil)) ;; keep going
	((loop for mn in (matchsuccessors (caar inputs)) thereis
	       ; we now always build one or two levels ...
	       (or (and (nodematches mn vars newwff) mn)
		   (loop for mn2 in (matchsuccessors mn) thereis
			 (and (nodematches mn2 vars newwff) mn2)))))
	; if there's only 1 input then we won't build a node for newwff ...
	((and (null (cdr inputs))
	      (loop for mn in (matchsuccessors (caar inputs)) thereis
		    (and (nodematches mn vars (fourth (car inputs))) mn))))
	(t (let (mnode subnodes result)
	     (setq subnodes
		   (loop for input in inputs collect
		       (progn
			 (setq mnode
			       (make-matchnode
				 :matchvars vars
				 :matchcompare (get-match-compare vars)
				 :matchwff (fourth input)
				 :matchpredecessors (list (car input))
				 :matchrels (changerels-in-wff (fourth input))
				 :matchcode
				 (with-goal (list "react to" (car input))
				   (compile-matchcode (caddr input)))))
			 (push mnode (matchsuccessors (car input)))
			 mnode)))
	     (cond
	       ; checked above ((null subnodes) nil)
	       ((null (cdr subnodes)) (car subnodes))
	       (t (setq result
			(make-matchnode
			    :matchvars vars :matchcompare (get-match-compare vars)
			    :matchwff newwff :matchpredecessors subnodes
			    :matchrels (changerels-in-wff newwff)
			    :matchcode 'ident))
		  (loop for m in subnodes do (push result (matchsuccessors m)))
		  result)))))))

; used below for Exist
(defvar first-n-fn-table nil)
(defun get-first-n-fn (n)
  (or (cdr (assoc n first-n-fn-table))
      (let (fn (vars (loop for i below n collect (gensym "V"))))
	(setq fn (compile-ap `(lambda (,@vars &rest Evars)
				(declare (ignore evars))
				(list (list ,@vars)))))
	(push (cons n fn) first-n-fn-table)
	fn)))

#-old-rule-compiler
(Defun Detect+ (vars wff &optional stack &aux subnodes subnode result)
 (with-goal (list "detect" vars "s.t." wff)
  ; like Detect, but for arbitrary transition wffs
  ; W is a transition wff iff there is no to-(from-)state such that wff is true
  ; for any from-(to-)state.
  ; generates an error for non-transition wffs, otherwise either a node or nil
  (cond
    ((no-trigger vars wff) nil)
    (t
     (Case (car (ilistp wff))
       (Start (Detect-or-* vars (cadr wff) nil stack))
       (Start* (Detect-or-* vars (cadr wff) t stack))
       (and
	 ; find any triggerable conjunct that can trigger the entire wff
	 ; really ought to be looking for the cheapest ***
	 ; note this is is a global optimization problem - rules interact
	 ;; if recursive detect+ returns nil for some conjunct then 
	 ;; detect+ should return nil for the whole conjunction
	 ;; Below we don't actually search exhaustively for a nil...
	 ;; We must still treat nil different from cannot-detect since 
	 ;; all other conjuncts are likely cannot-detect's.
	 (cond ((loop for j in (cdr wff) thereis
		      (try (or
			     (setq subnode
				   (detect+ vars j
					    (cons `(and * ,@(remove j (cdr wff)))
						  stack)))
			     (return-from Detect+ nil))
			   ap5-cannot-generate nil))
		subnode) ; even if the result is nil
	       (t (fail ap5-cannot-generate (list vars 's.t. wff)))))
       (or #+ignore ; not required in new version - might be in stack also
	   (when (loop for junct in (cdr wff) thereis
		       (not (fsubset vars (varsfreein junct vars))))
	     (fail ap5-cannot-generate (list vars 's.t. wff)))
	   (setq subnodes 
		 (loop for junct in (cdr wff) 
		       when (setq subnode (Detect+ vars junct stack))
		       unless (when (eq t subnode) (error junct))
		       collect subnode))
	   (cond ((null subnodes) nil)
		 ((null (cdr subnodes)) (car subnodes))
		 ((let ((keepstarts t)) (declare (special keepstarts))
		    (loop for w in stack when (consp w) do ; see prev. comment
			  (setq wff (subst wff '* w)))
		    (setq wff (simplify wff))
		    nil)) ; keep going
		 ((loop for sn in subnodes thereis
			(when (matchnode-p sn)
			  (loop for s in (matchsuccessors sn) thereis
				(and (nodematches s vars wff) s)))))
		 (t (setq result
			  (make-matchnode
			    :matchvars vars :matchwff wff
			    :matchrels (union* (loop for n in subnodes
						     when (matchnode-p n) collect
						     (matchrels n)))
			    :matchcompare (get-match-compare vars)
			    :matchcode 'Ident :matchpredecessors subnodes))
		    (loop for sn in subnodes do
			  (push result (matchsuccessors sn)))
		    result)))
       (E #+ignore ; not required in new version - as above
	  (unless (fsubset vars (varsfreein wff vars))
	    (fail ap5-cannot-generate (list vars 's.t. wff)))
	  (setq subnode (Detect+ (append vars (cadr wff)) (caddr wff) stack))
	  (cond ((null subnode) nil)
		((let ((keepstarts t)) (declare (special keepstarts))
		   (loop for w in stack when (consp w) do ; see prev. comment
			 (setq wff (subst wff '* w)))
		   (setq wff (simplify wff))
		   nil)) ; keep going
		((loop for s in (matchsuccessors subnode) thereis
		       (and (matchnode-p s) (nodematches s vars wff) s)))
		(t (setq result
			 (make-matchnode
			   :matchvars vars :matchcompare (get-match-compare vars)
			   :matchwff wff :matchrels (changerels-in-wff wff)
			   :matchcode (get-first-n-fn (length vars))
			   :matchpredecessors (list subnode)))
		   ;alter-matchnode
		   (push result  (matchsuccessors subnode))
		   result)))
       ; InCx ???
       (t (fail ap5-cannot-generate (list vars 's.t. wff)))
       ; includes the cases of primtive, not, previous, A
       )))))

#+old-rule-compiler
(Defun Detect+ (vars wff &optional stack &aux subnodes subnode result oldwff)
  ; like Detect, but for arbitrary transition wffs
  ; W is a transition wff iff there is no to-(from-)state such that wff is true
  ; for any from-(to-)state.
  ; generates an error for non-transition wffs, otherwise either a node or nil
  (cond
    ((no-trigger vars wff) nil)
    (t
     (Case (car (ilistp wff))
       (Start (Detect-or-* vars (cadr wff) nil stack))
       (Start* (Detect-or-* vars (cadr wff) t stack))
       (and
	 ; find any triggerable conjunct that can trigger the entire wff
	 ; really ought to be looking for the cheapest ***
	 ; note this is is a global optimization problem - rules interact
	 (cond ((loop for j in (cdr wff) thereis
		      (try (setq subnode
				 (list (detect+ vars j
						(cons `(and * ,@(remove j (cdr wff)))
						      stack))))
			   ap5-cannot-generate nil))
		(car subnode)) ; even if the result is nil
	       (t (fail ap5-cannot-generate (list vars 's.t. wff)))))	 
       (or #+ignore ; not required in new version - might be in stack also
	   (when (loop for junct in (cdr wff) thereis
		       (not (fsubset vars (varsfreein junct vars))))
	     (fail ap5-cannot-generate (list vars 's.t. wff)))
	   (setq subnodes 
		 (loop for junct in (cdr wff) 
		       when (setq subnode (Detect+ vars junct stack))
		       collect subnode))
	   (cond ((null subnodes) nil)
		 ((null (cdr subnodes)) (car subnodes))
		 ((loop for sn in subnodes thereis
			(loop for s in (matchsuccessors sn) thereis
			      (and (nodematches s vars wff) s))))
		 (t (loop for w in stack do
			  (setq wff (subst wff '* w)))
		    (setq result
			  (make-matchnode
			    :matchvars vars :matchwff wff
			    :matchrels (union* (loop for n in subnodes collect
						     (matchrels n)))
			    :matchcompare (get-match-compare vars)
			    :matchcode 'Ident :matchpredecessors subnodes))
		    (loop for sn in subnodes do
			  (push result (matchsuccessors sn)))
		    result)))
       (E #+ignore ; not required in new version - as above
	  (unless (fsubset vars (varsfreein wff vars))
	    (fail ap5-cannot-generate (list vars 's.t. wff)))
	  (setq subnode (Detect+ (append vars (cadr wff)) (caddr wff) stack))
	  (cond ((null subnode) nil)
		((loop for s in (matchsuccessors subnode) thereis
		       (and (nodematches s vars wff) s)))
		(t (setq oldwff wff)
		   (loop for w in stack do
			 (setq wff (subst wff '* w)))
		   (setq result
			 (make-matchnode
			   :matchvars vars :matchcompare (get-match-compare vars)
			   :matchwff wff :matchrels (changerels-in-wff wff)
			   :matchcode
			   (compile-ap
			     `(lambda ,(vars-to-names (append vars (cadr oldwff)))
				,@(vars-to-names (cadr oldwff))  ; not used
				(list (list ,@(vars-to-names vars)))))
			   :matchpredecessors (list subnode)))
		   ;alter-matchnode
		   (push result  (matchsuccessors subnode))
		   result)))
       ; InCx ???
       (t (fail ap5-cannot-generate (list vars 's.t. wff)))
       ; includes the cases of primtive, not, previous, A
       ))))

#+old-rule-compiler
(Defun Detect* (vars wff &aux subnodes result newvars)
  ; Like Detect, but rather than Start wff we detect Start* wff, which means
  ; that wff is assumed to have been false before (this is not allowed in
  ; any source code - it just allows optimizing out the checking).
  (cond ((no-trigger vars (list 'start* wff)) nil)
	((not (member (car (ilistp wff)) '(or e))) (detect vars wff))
        ((eql (car wff) 'e)
	 (setq subnodes (detect* (setq newvars (append (cadr wff) vars))
				 (caddr wff)))
	 (cond
	   ((loop for successor in (matchsuccessors subnodes) thereis
		  (and (nodematches successor vars wff) successor)))
	   (t (setq result
		    (make-matchnode
		      :matchvars vars
		      :matchcompare (get-match-compare vars)
		      :matchwff (list 'start* wff)
		      :matchpredecessors (list subnodes)
		      :matchrels (matchrels subnodes)
		      :matchcode
		      (compile-ap
			`(lambda ,(vars-to-names newvars)
			   ,@(vars-to-names (cadr wff))
			   ;just to avoid warnings
			   (list (list ,@(vars-to-names vars)))))))
	      ;alter-matchnode
	      (push result  (matchsuccessors subnodes))
	      result)))
	(t (setq subnodes ; if not all juncts have vars it's too bad
		 (loop for junct in (cdr wff) collect
		       (detect* vars junct)))
	   (cond 
	     ((loop for successor in (matchsuccessors (car subnodes)) thereis
		    (and (nodematches successor vars wff) successor)))
	     (t (setq result (make-matchnode
			       :matchvars vars
			       :matchcompare (get-match-compare vars)
			       :matchwff (list 'start* wff)
			       :matchrels (union* (loop for n in subnodes collect
							(matchrels n)))
			       :matchcode 'Ident
			       :matchpredecessors subnodes))
		(loop for sn in subnodes do
		      ;alter-matchnode
		      (push result  (matchsuccessors sn)))
		result)))))

#+old-rule-compiler
(Defun Detect (vars wff)
  ; build the stuff that will recognize when any instantiation of vars starts
  ; to satisfy wff.  Sharing of this structure is desirable.
  ; return a match node whose outputs are {vars s.t. (start wff)}.
  ; return nil if it cannot become true
  (cond ((no-trigger vars (list 'start wff)) nil)
	((member wff '(true false)) nil)
	((or (not (compoundwffp wff)) ; positive input node
	     (eql (car wff) 'not)) ;negative input node
	 (DetectInput vars wff))
	((member (car wff) '(and or)) (DetectAndOr vars wff))
	((member (car wff) '(a e)) (DetectAE vars wff))
	(t (error "~S unknown type of triggering wff" wff))))


(Defun DetectInput (vars wff &aux oldnode wff2 prop inputs result ans
			 rel samevars)
  (setf wff2 (copy-seq (if (eql (car wff) 'not) (cadr wff) wff)))
  ; if vars are repeated we'll smash wff2
  (setq prop (cond ((not (eql (car wff) 'not)) 'addmatchers) (t 'deletematchers)))
  (setq oldnode (car (get-structure-property (setq rel (relationp (car wff2))) prop)))
  (setq ans
     (cond
        ((eq 'start (car wff2)) t) ; should never happen?
	((and oldnode (nodematches oldnode vars (list 'start wff))) oldnode)
	((and oldnode
	      (loop for n in (matchsuccessors oldnode) thereis
		    (and (nodematches n vars (list 'start wff))
			 n))))
	((really-not-possible-to-update rel (equal wff wff2)) nil)
	((nontriggerablep rel)
	 (fail ap5-cannot-generate (list vars 's.t. (list 'start wff))))
	((and (not (PossibleToUpdate rel (equal wff wff2))) (not (getdefn rel)))
	 nil)
	((and (derivedrel rel) (not (getdefn rel)) (PossibleToUpdate rel (equal wff wff2))
	      (not (something-triggers? rel (equal wff wff2)))
	      (cerror "You'll supply the triggering data later"
		      "Trying to trigger on the derived relation ~A~
                      ~& which evidently can be updated, but no trigger~
                      ~& claims to cause it to change!" rel)))
	(t (loop for argtail on (cdr wff2) do
		 (let ((nexttail argtail) copies)
		   (loop while (and (variable-p (car argtail))
				    (setq nexttail (member (car argtail) (cdr argtail))))
			 do
			 (push (setf (car nexttail)
				     (make-variable :varname (gensym "V")
					      :vartype (vartype (car argtail))
					      :varcompare (varcompare (car argtail))))
			       copies))
		   (and copies (push (cons (car argtail) copies) samevars))))
	   (setf result (make-matchnode :matchvars vars
					:matchrels (changerels-in-wff wff2)
					:matchcompare (get-match-compare vars)
					:matchwff (list 'start wff))
		  inputs (loop for arg in (cdr wff2) collect
			      (cond ((or (member arg vars)
					 (loop for s in samevars thereis
					       (member arg (cdr s))))
				     (name-of-var arg))
				    (t (gensym "V")))))
	   ;alter-matchnode
	   (setf (matchcode result)
		 (cond ((not (equal vars (cdr wff2)))
			; includes samevars, permutation
			(compile-ap
			  `(lambda ,inputs
			     (cond
			       ((and
				  ,@(loop for arg in (cdr wff2)
					  as i in inputs as pos from 0
					  unless (or (member arg vars)
						     (loop for s in samevars thereis
							   (member arg (cdr s))))
					  collect
					  (get-test-function (get-comparison rel pos t)
							     arg i))
				  ,@(loop for s in samevars nconc
					  (loop for v in (cdr s) collect
						(get-test-function (varcompare v)
						   (varname v) (varname (car s))))))
				(list (list ,@(vars-to-names vars))))))))
		       (t 'ident)))
	   ; do this AFTER the matchcode is entered so if compilation breaks we don't end
	   ; up trying to execute matchnodes with null rulecodes
	   (cond ((not (equal vars (cdr wff2))) 
		  ; let this be a successor to the generic node
		  (let ((args (loop for a below (length (cdr wff2))
				collect (gensym "V"))) w)
		    (setq w (cons (car wff2) args))
		    (when (eq (car wff) 'not) (setq w (list 'not w)))
		    (setq w (expanddescription (list args 's.t. w)))
		    (detectinput (car w) (caddr w))
		    ; builds node but returns nil if it can never match
		    (setq oldnode (car (get-structure-property rel prop)))
		    (unless oldnode (error "Failed to find matchnode - see DonC")))
		  (push oldnode (matchpredecessors result))
		  (push result (matchsuccessors oldnode)))
		 (t (add-structure-property rel result prop)))
	   ; there should be only one on proplist, but keep it a list for compatibility
	   result)))
  ;; this has to be done even if the node already existed in case the predecessor
  ;; was removed earlier, e.g., in response to the need for it disappearing
  (when (matchnode-p ans)
    (let ((def (getdefn rel)))
      (when (and def
		 (defined-p rel)
		 (null (matchpredecessors ans)))
	; if already has predecessors it could be one of those just above,
	; a successor to the real input node
	(unless (add-defn-predecessor rel ans (car def) (eq (car wff) 'not))
	  (return-from detectinput nil)))))
  ans)

(defun add-defn-predecessor (rel oldnode def negated &aux desc newnode)
  (setf desc (expanddescription `(,(car def) s.t. ,(caddr def))))
  (when negated (setf (third desc) (simplify1 (list 'not (third desc)))))
  ; have to negate the whole thing, inc. stuff from type#name@equiv !!
  (setf newnode (with-goal (list "detect" 'start
				 (cond (negated (list 'not rel)) (t rel)))
			   (detect (car desc) (caddr desc))))
  (when newnode (assert-known-matchpred rel def oldnode newnode) t))

#+old-rule-compiler
(Defun DetectAndOr (vars wff &aux subnodes result firstreal)
  (setq subnodes (loop for junct in (cdr wff) collect
		       (detect (varsfreein junct vars) junct)))
  (cond ((not (setq firstreal (loop for sn in subnodes thereis sn)))
	 nil) ; cannot become true
	((loop for s1 in (matchsuccessors firstreal) thereis
	       (loop for s2 in (matchsuccessors s1) thereis
		     (and (nodematches s2 vars (list 'start wff))
			  s2))))
	; already had the node we wanted
	(t (setq subnodes
	     (loop for sn in subnodes as junct in (cdr wff)
		with w and junctvars when sn
		unless
		(no-trigger
		  vars
		  (setq w
			(cond ((eq (car wff) 'and)
			       (cons (car wff) (cons (list 'start junct)
						    (remove junct (cdr wff)))))
			      (t (cons 'and
				       (cons (list 'start junct)
					     (loop for j in (remove junct (cdr wff))
						   collect
						   (simplify1
						     (list 'previously
							   (list 'not j))))))))))
		collect
		(let (newnode
		      (newvars
			(fldifference vars (setq junctvars (varsfreein junct vars)))))
		  (setq newnode
			(cond
			  ((eq (car wff) 'and)
			   (make-matchnode
			     :matchvars vars
			     :matchcompare (get-match-compare vars)
			     :matchwff w
			     :matchrels (changerels-in-wff wff)
			     :matchcode
			     (compile-ap
			       (cond
				 ((null newvars)
				  `(lambda ,(vars-to-names junctvars) ;(matchvars sn)
				     (and ,(cons '?? (vars-to-names-wff
						       (remove junct wff)))
					  (list (list ,@(vars-to-names vars))))))
				 (t
				  `(lambda ,(vars-to-names junctvars)  ;(matchvars sn)
				     #-ti(loop for ,(vars-to-names newvars) s.t.
					   ,(vars-to-names-wff (remove junct wff))
					   collect (list ,@(vars-to-names vars)))
				     #+ti ; avoid extra macroexpansions until rel. 3
				     (progn nil
					    (loop for ,(vars-to-names newvars) s.t.
					   ,(vars-to-names-wff (remove junct wff))
					   collect (list ,@(vars-to-names vars))))))))
			     :matchpredecessors (list sn)))
			  (t ;car wff = or
			   (make-matchnode
			     :matchvars vars
			     :matchcompare (get-match-compare vars)
			     :matchrels (matchrels sn)
			     :matchwff w
			     :matchcode
			     (compile-ap
			       (cond
				 ((null newvars)
				  `(lambda ,(vars-to-names junctvars) ;(matchvars sn)
				     (and (?? not (previously ,
						    (vars-to-names-wff
						      (remove junct wff))))
					  (list (list ,@(vars-to-names vars))))))
				 (t `(lambda ,(vars-to-names junctvars) ;(matchvars sn)
				       #-ti(loop for ,(vars-to-names newvars) s.t.
					     (previously
					       (not ,(vars-to-names-wff
						       (remove junct wff))))
					     collect (list ,@(vars-to-names vars)))
				       #+ti ; avoid extra macroexpansions until rel. 3
				       (progn nil
					      (loop for ,(vars-to-names newvars) s.t.
					     (previously
					       (not ,(vars-to-names-wff
						       (remove junct wff))))
					     collect (list ,@(vars-to-names vars))))))))
			     :matchpredecessors (list sn)))))
		  ;alter-matchnode
		  (push newnode (matchsuccessors sn))
		  newnode)))
	   (setq result (make-matchnode 
			  :matchvars vars
			  :matchcompare (get-match-compare vars)
			  :matchwff (list 'start wff)
			  :matchrels (union* (loop for n in subnodes collect
						   (matchrels n)))
			  :matchcode 'Ident
			  :matchpredecessors subnodes))
	   (loop for sn in subnodes do
		 ;alter-matchnode
		 (push result  (matchsuccessors sn)))
	   result)))

#+old-rule-compiler
(Defun DetectAE (vars wff &aux subnode result subvars)
  (setq subnode (Detect (setq subvars (append vars (cadr wff))) (caddr wff)))
  (cond ((null subnode) nil) ; can never become true
	((loop for s in (matchsuccessors subnode) thereis
	       (and (nodematches s vars (list 'start wff)) s))) ; already existed
	(t (setq result
		 (make-matchnode
		   :matchvars vars
		   :matchrels (matchrels subnode)
		   :matchcompare (get-match-compare vars)
		   :matchwff (list 'start wff)
		   :matchpredecessors (list subnode)
		   :matchcode
		   (compile-ap
		     (cond ((eql (car wff) 'a)
			    `(lambda ,(vars-to-names subvars) ;(matchvars subnode)
			       ,@(vars-to-names (cadr wff)) ; just to avoid warnings
			       (cond (,(cons '?? (vars-to-names-wff wff))
				      (list (list ,@(vars-to-names vars)))))))
			   ; forall was false before - true now?
			   (t ;  Exists is now true, but was it before?
			    `(lambda ,(vars-to-names subvars) ;(matchvars subnode)
			       ,@(vars-to-names (cadr wff)) ; just to avoid warnings
			       (cond ((?? not (previously ,(vars-to-names-wff wff)))
				      (list (list ,@(vars-to-names vars)))))))))))
	   ;alter-matchnode
	   (push result  (matchsuccessors subnode))
	   result)))

;; This is apparently needed only for push-in-start:
; The only other place where we copy pieces of wffs that result in the same 
; variable-object being bound twice is above in find-triggers, but that is
; never compiled - find-triggers creates its own piece of code in which the
; vars are changed back into names so that when the code is compiled they
; become separate structures again.
(defun separate-vars (wff &aux alist)
  (declare (special alist))
  (map-copy-wff wff
      :quantified-wff
      #'(lambda (q v w)
	  (let ((alist
		  (append
		    (loop for var in v collect
			  (cons var
				(if (variable-p var)
				    (let ((new (copy-variable var)))
				      (setf (varname new) (gensym "V"))
				      new)
				    ;; used from testeffort on undigested wffs
				    (gensym "V"))))
		    alist)))
	    (declare (special alist))
	    (list q (loop for var in v collect (cdr (assoc var alist)))
		  (map-wff-internal w))))
      :primitive-wff
      #'(lambda (rel &rest args)
	  (cons rel (loop for a in args collect (or (cdr (assoc a alist)) a))))))

;; stuff for compiling start in other contexts ...

(defun push-in-start (vars wff type &aux result stack (currentvars vars))
  (declare (special stack currentvars type result))
  (flet ((get-inside (w herevars &aux matchwff genvars ;; wff2
			(newwff 'true) (keepstarts t))
	   (declare (special currentvars stack keepstarts))
	   ;; (setf wff2 (if (eq (car w) 'not) (cadr w) w))
	   (when (and (not (no-trigger herevars (list 'start w)))
		      (wff-needs-trigger w t))
		; if nil don't push anything above 
	     (loop for wff in stack when (consp wff) do	; weird interpretation of subst
		   (setq newwff (subst newwff '* wff)))
	     (setf matchwff
		   ;;vars-to-names-wff ;; not needed -
		   ;;decache-rel expects matchvars/matchwff to be a description (args to detect)
		   (simplify
		     `(E ,(fldifference currentvars vars) (and (start ,w) ,newwff))))
	     (unless (no-trigger vars matchwff)      
	       (setf newwff
		     (simplify
		       `(E ,(fldifference (fldifference currentvars vars) herevars) ,newwff))
		     genvars (fldifference vars herevars))
	       (let ((n 0) vars-used)
		 (map-wff newwff :primitive-wff
			  #'(lambda (rel &rest args) (declare (ignore rel))
				    (loop for a in args when (variable-p a) do
					  (pushnew (varname a) vars-used))))
		 (loop for var in (append herevars genvars) collect
		       (cons var (let (name)
				   (loop while (member (setq name (pack* 'x (incf n)))
						       vars-used)
					 do nil)
				   name))))
	       matchwff))))
    (map-wff wff
     :quantified-wff
     #'(lambda (q v w)
	 (case q
	   (a (case type
		(start (let ((stack (cons `(and * ,(separate-vars (list 'A v w))) stack))
			     (currentvars (append v currentvars)))
			 (declare (special stack currentvars))
			 (map-wff-internal w)))
		(start* (let ((stack (cons `(and * ,(separate-vars (list 'A v w))) stack))
			      (currentvars (append v currentvars))
			      (type 'start)) ; could have been (and was) start+
			  (declare (special stack currentvars type))
			  (map-wff-internal w)))
		(start+ (let ((currentvars (append v currentvars)))
			  (declare (special currentvars))
			  (map-wff-internal w)))))
	   (e (case type
		(start (let ((stack (cons `(and * (not (previously
							 ,(separate-vars (list 'E v w)))))
					  stack))
			     (currentvars (append v currentvars)))
			 (declare (special stack currentvars))
			 (map-wff-internal w)))
		(start* (let ((stack (cons '* stack))
			      (currentvars (append v currentvars)))
			  (declare (special stack currentvars))
			  (map-wff-internal w)))
		(start+ (let ((currentvars (append v currentvars)))
			  (declare (special currentvars))
			  (map-wff-internal w)))))))
     :boolean-op
     #'(lambda (op &rest wffs)
	 (cond
	   ((eq op 'not)
	    (let ((herevars (remove-if-not #'variable-p
					   (remove-duplicates (cdar wffs))))
		  res)
	      (when (setq res (get-inside (cons op wffs) herevars))
		(push res result))))
	   ((eq type 'start+)
	    (loop for w in wffs do (map-wff-internal w)))
	   ((eq op 'and)
	    (loop for w in wffs do
		  (let ((stack (cons `(and * ,@(remove w wffs)) stack)))
		    (declare (special stack))
		    (map-wff-internal w))))
	   ((eq op 'or)
	    (loop for w in wffs do
		  ; that simplify seems necessary to ensure that all prev's
		  ; end up around literals - (prev (and (p x))) violates that
		  ; assumption and so ends up assigning to vars it shouldn't
		  (let ((stack (cons (cond ((eq type 'start*) '*)
					   (t `(and * (not (previously
							     ,(simplify
							       `(or ,@(remove w wffs))))))))
				     stack)))
		    (declare (special stack))
		    (map-wff-internal w))))
	   (t (error "unknown connective"))))
     :primitive-wff
     #'(lambda (&rest w)
	 (let ((herevars (remove-if-not #'variable-p (remove-duplicates (cdr w))))
	       res)
	   (when (setq res (get-inside w herevars)) (push res result))))))
  (cond ((null result) 'false)
	((cdr result) (cons 'or result))
	(t (car result))))

(defun wff-needs-trigger (wff addp)
  (map-wff wff
	   :primitive-wff
	   #'(lambda (rel &rest args)
	       (declare (ignore args))
	       (if (rel-needs-trigger rel addp)
		   (return-from wff-needs-trigger t)))
	   :boolean-op
	   #'(lambda (op &rest wffs)
	       (if (eq op 'not)
		   (when (wff-needs-trigger (car wffs) (not addp))
			 (return-from wff-needs-trigger t))
		 (mapc #'map-wff-internal wffs)))))

(defun rel-needs-trigger (rel addp &aux defn)
  (cond ((really-not-possible-to-update rel addp) nil)
	((PossibleToUpdate rel addp) t)
	((and (setq defn (getdefn rel))
	      (wff-needs-trigger (third (car defn)) addp))
	 t)))

(defun mark-active (matchnode class)
  ; as part of asserting the relation between a node and a rule
  ; note that these and mark-inactive's can be done in any order with
  ; the same net effect
  (cond ((not (member class (matchactive matchnode)))
	 (push class (matchactive matchnode))
	 (loop for sn in (matchpredecessors matchnode) do
	       (mark-active sn class)))))

(defun maybe-mark-inactive (matchnode class &aux delta)
  ; delta is nil for matchXs in case stmt
  ; - shouldn't access DB during primitive update - here we're trying to
  ; read the actually stored data, just using DB operations to do it.
  ; maybe is because we call this when we remove one link
  ; (either to a rule or another matchnode)
  (or (loop for suc in (matchsuccessors matchnode) thereis
	    (member class (matchactive suc)))
      (case class
	(:consistency (matchconsistencies matchnode))
	(:automation (matchautomations matchnode))
	(:maintain (matchmaintains matchnode))
	(t nil))
      (progn (setf (matchactive matchnode) (delete class (matchactive matchnode)))
	     (loop for pre in (matchpredecessors matchnode) do
		   (maybe-mark-inactive pre class)))))

; for runtime compilation - the only advantage of this over the one below is
; that you can cons up something at run time.  It is also used by functions
; that cache code (so we don't have to compile many versions of the same thing).
;
; I've inserted copy-tree's around the stuff to be compiled so as to prevent 
; the compiler from smashing the lambda expression.  This is important because
; sometimes that code is examined to see if it matches some known form.
;
(setq prototype-mode nil)

#- buggy-compiler
(defun compile-ap (lambda-exp &optional (symbol (gentemp "F" ap-compiled))
			      &aux #+symbolics(si::FDEFINE-FILE-DEFINITIONS nil)
			      #+symbolics (si::inhibit-fdefine-warnings t))
  (unless symbol (error "trying to compile-ap NIL!!"))
  (if prototype-mode 
      (setf (symbol-function symbol) (mexpand-all (copy-tree lambda-exp)))
    (with-whostate compile-msg (mycompile symbol (copy-tree lambda-exp))))
  (setf (get symbol :previous-definition) lambda-exp)	; for debugging
  symbol)					;return the compiled thing!

#+ buggy-compiler
(defun compile-ap (lambda-exp &aux  (symbol (gentemp "F" ap-compiled)))
  (multiple-value-bind (ignore error-flag) 
      (ignore-errors (with-whostate compile-msg (mycompile symbol (copy-tree lambda-exp))))
    (declare (ignore ignore))
    (when error-flag (setf (symbol-function symbol)  (mexpand-all (copy-tree lambda-exp)))))
  (setf (get symbol :previous-definition) lambda-exp) ; for debugging
  symbol) ;return the compiled thing!

; for compile-time compilation
#+ignore ;; (or ti symbolics)
(defmacro-displace compile-ap* (lambda-exp &aux (symbol (gensym "F")))
  ; avoid gentemp due to possible conflicts at load time
  ; perhaps we should collect all such symbols into a list??
  (mycompile symbol (copy-tree lambda-exp))
  `(progn (setf (get ',symbol :previous-definition) ',lambda-exp)
	  (setf (symbol-function ',symbol) ',(symbol-function symbol))
	  ',symbol))

#-ignore ;;(or ti symbolics)
(defmacro-displace compile-ap* (lambda-exp)
		   `',lambda-exp)

#+ignore ;; buggy-compiler
(defmacro-displace compile-ap* (lambda-exp &aux (symbol (gensym "F")))
  `(progn (setf (get ',symbol :previous-definition) ',lambda-exp)
	  (setf (symbol-function ',symbol) ',(mexpand-all (copy-tree lambda-exp)))
	  ',symbol))

#+(or symbolics) ;; ti compiles forms in release 6
(defmacro-displace compiled (&rest forms &aux (symbol (gensym "F")))
  ; it seems that the top level forms of compiled files are not really compiled
  ; this can be wrapped around such forms to make sure they get compiled all the
  ; way at compile time and then just executed at load time
  `(progn (defun ,symbol () ,@forms)
	  (,symbol)
	  (fmakunbound ',symbol)))

#-(or symbolics)
(defmacro-displace compiled (&rest forms)
  `(progn ,@forms))

(defun dump-symbol (symbol)
  (unless symbol (error "trying to dump-symbol NIL!!"))
  `(progn (setf (get ',symbol :previous-definition) ',(get symbol :previous-definition))
	  (setf (symbol-function ',symbol) ',(symbol-function symbol))
	  ',symbol))
; this variant for when you already have the compiled symbol
