;;;-*- Mode: LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-
(in-package "AP5")

; ---------------- temporarily turning off rules ----------------

(defmacro-displace with-dormant-rules (rules &body forms
    &aux (classes+ '(:consistency :maintain :automation))
    (classes '(:consistency :automation))
    rulenames  to-append)
  (cond ((member rules classes) (setq rules (list rules))))
  `(let* ((suspended-rule-classes
	    ,(cond ((eq rules t) (kwote classes+))
		   ((setq to-append (intersection classes rules))
		     `(append suspended-rule-classes
				',to-append))
		   (t 'suspended-rule-classes)))
	  ,@(and (eq rules t) '((Fix-Maintained-Relation t)))
	  (suspended-rules
	    ,(cond ((eq rules t) 'suspended-rules)
		   ((setq rulenames (set-difference rules classes))
		    `(append suspended-rules
			     (list ,. (loop for n in rulenames collect
					    `(any r s.t. (rulename r ',n)
						  ifnone ',n))))))))
     ; if not a rule name, it might be a fn name in advice-for-every-transition
     (when (inatomic) (error "trying to do with-dormant-rules in an atomic"))
     ,@ forms))

(defun zap-olddata-and-save (name rel)
  (try (let* ((prevdata (eval `(listof ,name)))
	      (l (length prevdata)))
	 (warn "~A tuple~P saved for rerepresentation of ~A"
	       l l name)
	 (unless (derivedrel rel)
	   (with-dormant-rules t (eval `(set-listof ,name nil))))
	 prevdata)
       ap5-cannot-generate
       (warn "~A is changing representation but cannot be generated.~
              ~&It is your responsibility to restore the data" name)
       :cannot-generate))

(defun restore-zapped-data (name rel arity prevdata)
  (with-dormant-rules t
    (try (eval `(set-listof ,name nil))
       ap5-cannot-generate
       (warn "Since new representation is not totally generable ~
             ~&ap5 cannot check that ~A contains only old tuples" name))
    (atomic (loop for tuple in prevdata do
		  (if (= arity 1) (++ funcall rel tuple) (++ apply rel tuple))))))

(defun cache-data (rel relname defn &aux newtuples)
  (with-dormant-rules t
    (try (eval `(set-listof ,relname nil))
	 ap5-cannot-generate
	 (warn "unable to remove any old tuples of ~A" relname))
    (try (progn (setq newtuples (eval `(listof ,.defn)))
		(warn "~A tuples to be stored in ~A" (length newtuples) relname)
		(atomic (loop for tuple in newtuples do
			      (if (= (length (car defn)) 1)
				  (++ funcall rel tuple)
				  (++ apply rel tuple)))))
	 ap5-cannot-generate
	 (warn "unable to generate new tuples of ~A" relname))))

; a version for when you know how to compute the list of rules
; no classes allowed
(defmacro-displace with-dormant-rules* (rulesform fix-maintained &body forms)
  `(let* (,@(and fix-maintained '((Fix-Maintained-Relation t)))
	  (suspended-rules (append suspended-rules ,rulesform)))
     ,@ forms))

; this is better than the previous defn (from types) because it uses the 
; cached subtype data
(defun most-specific-types-of (types &key typeaccessor)
  ;; elements of types that are not supertypes of other elements
  (cond
    (typeaccessor
     (cond ((null types) nil)
	   ((cdr types)
	    (flet ((superceded-in (node nodelist)
		     (some #'(lambda (n2)
			       (or (eq n2 node) 
				   ;; not needed if types has no duplications
				   (?? subrel
				       (funcall typeaccessor n2)
				       (funcall typeaccessor node))))
			   nodelist)))
	      (loop for tail on types
		    unless (or (superceded-in (car tail) final)
			       (superceded-in (car tail) (cdr tail)))
		    collect (car tail) into final
		    finally (return final))))
	   (t (list (car types)))))
    (t
     (cond ((null types) nil)
	   ((cdr types)
	    (flet ((superceded-in (type l)
		     (some #'(lambda (t2)
			       (or (eq t2 type) 
				   ;; not needed if types has no duplications
				   (?? subtype t2 type)))
			   l)))
	      (loop for tail on types
		    unless (or (superceded-in (car tail) final)
			       (superceded-in (car tail) (cdr tail)))
		    collect (car tail) into final
		    finally (return final))))
	   (t (list (car types)))))))

(defrelation derived-from :definition
   ((x y) s.t. (or (E (tv1 fn tv2) (trigger y tv1 fn x tv2)) (relation-in-defn y x))))

(defrelation derived-from* :derivation (tclosure derived-from)
	     :size ((output input) 100 (input output) 10))
; The main idea here is to test the closure by generating the rels-in
; something rather than generating the things that use the other one
; The example of classification shows why we don't want to go the other way.
; these have to be added since they are not yet maintained
(++ Possibletoadd (relationp 'derived-from*) t)
(++ Possibletodelete (relationp 'derived-from*) t)

(defun derived-nonatomic-rel (rel)
  (?? E (r) (and (derived-from* rel r) (nonatomic-relation r))))
; used by defrel

(defrelation
  transition-derived-from
  :definition
  ((relation#derived transition) s.t.
   (and (derived-from* derived transition)
	(not (E (derived#implementation)
		(relationimplementation transition implementation)))
	(not (E (rel)
		(derived-from transition rel)))))
  :representation two-way-structprop
  :documentation
  "Efficient access from derived relations to the non-derived relations they depend on.")

; still have to initialize it ...
(with-dormant-rules t
  (atomic
    (loop for (relation#x y) s.t. (inline (transition-derived-from x y)) do
	  (++ transition-derived-from x y))))

; used for generating starts, map-updates
(defun might-have-changed (r)
  (or (?? nontriggerable r)
      (loop for x s.t. (derived-from* r x) thereis
	    (or (assoc x delta) (?? nontriggerable x)))))


(defun unchanged (rel) ; only differences are parity and this handles stored rels
  (cond ((not (derivedrel rel)) (not (assoc rel delta)))
	(t (not (might-have-changed rel)))))



; ---------------- DescribeRel ----------------
; provide information to the user about a relation

(defun DescribeRel (rel-or-name &optional (stream *standard-output*) extra-printer
				&aux (rel (relationp rel-or-name))
				imp arity temp *print-pretty*)
  (unless (or rel
	      (setf rel (relationp (check-relation-package-error rel-or-name))))
    (error "~s is not a relation or the name of one" rel-or-name))
  (setq imp (implementations-of rel)) 
  (format stream "~%~A  implementation: ~S" (relationnamep rel)
	  (or (any x s.t. (parameter-list rel x) ifnone nil)
	      (if (cdr imp) imp (car imp)))) 
  (format stream "~%arity: ~S"
	  (setf arity (any x s.t. (relationarity rel x))))
  (cond ;((eq imp 'defined))
	((?? equivalence-relation rel)
	 (format stream "~%~A is an equivalence relation" (relationnamep rel)))
	(t (format stream "~%Compare Relations: ~A"
		   (loop for pos below arity collect
			 (cond ((eq t (setf temp (get-comparison rel pos nil)))
				'any)
			       ((listp temp) '<indeterminate>)
			       (t (relationnamep temp)))))))
  (or #+ignore (eq imp 'defined) (?? equivalence-relation rel) (?? type rel)
      (format stream "~%arguments: ~A" (typeconstraints rel)))
     ;; count constraints
  
  (cond ((member 'coded imp) 
	 (format stream "~%Definition:~%")
	 (write (any x s.t. (codedefn rel x)) :stream stream :pretty t
		:length 9 :level 5))		; protect against infinite loops
	((and (?? derived (car imp)) (not (member 'defined imp))) 
	 ;; was (?? and (derived imp) (not (eql imp 'defined)))
	 (format stream "~%Derived (but not from wff or code)")))
  (describerel2 rel stream extra-printer))

(defun describerel2 (rel stream extra-printer &aux temp)
  (loop for x s.t. (wffdefn rel x) do
	(format stream "~%Definition:~%")
	(write x :stream stream :pretty t)) ; :length 9 :level 5 (always want to see it)
  #-lucid
  (loop for name s.t. (relationname rel name) do
	(let ((doc (documentation name 'relation)))
	  (when doc (terpri stream) (princ doc stream))))
  #+ignore (loop for h s.t. (help rel h) do (terpri stream) (princ h stream))
  (cond ((context-sensitive rel)
	 (format stream "~%Context Sensitive")))
  (let (in-def)
    (when (setq in-def (loop for x s.t. (derived-from* x rel) as i below 11 collect x))
      (when (= 11 (length in-def)) (rplaca (last in-def) "..."))
      (format stream "~&Appears in the definition of: ~&~A" in-def)))
  #+ignore (forany x s.t. (possibleupdates rel x)
		   (format stream "~%Possible Updates: ~S" x)
		   ifnone nil)
  (and (setq temp (listof x s.t. (E (r) (and (ISubrel rel r) (relationname r x)))))
       (format stream "~%Immediate superrelations: ~S" temp))
  (and (setq temp (listof x s.t. (E (r) (and (ISubrel r rel) (relationname r x)))))
       (format stream "~%Immediate subrelations: ~S" temp))
  (let ((sizes (listof x y s.t. (relsize rel x y))))
    (when sizes (format stream "~&Size annotations: ~S" sizes)))
  (when extra-printer (funcall extra-printer rel stream))
  (values-list nil))

(defun DescribeRule (rule-or-name &optional (stream *standard-output*)
		     &aux rule code)
  (setq rule (cond ((?? rule rule-or-name) rule-or-name)
		   (t (any x s.t. (rulename x rule-or-name)
			   ifnone (error "no such rule")))))
  (format stream "~%~A  (~A)"
	  (any x s.t. (rulename rule x) ifnone '<unnamed-rule>)
	  (aptypecase rule
		      (consistencyrule 'consistency)
		      (automationrule 'automation)
		      (maintainrule 'maintain)
		      (consistencychecker 'consistencychecker)
		      (automationgenerator 'automationgenerator)
		      (t 'unknown-rule-type)))
  #-lucid
  (loop for name s.t. (rulename rule name) do
	(let ((doc (documentation name 'rule)))
	  (when doc (terpri stream) (princ doc stream))))
  (format stream "~%Trigger: ~S"
	  (any x s.t. (ruletrigger rule x) ifnone '<none>))
  (format stream "~%Code: ~S"
	  (setq code (any x s.t. (rulecode rule x) ifnone '<none>)))
  (when (and (symbolp code) (eql (symbol-package code) (find-package 'ap-compiled))
	     (setq code (prevdef code)))
    (format stream "~% which is a compiled version of~%~S" code))
  (when (?? consistencyrule rule)
    (format stream "~%Enforcement: ~A"
	    (any x s.t. (constraint-enforcement-level rule x) ifnone '<none>))))

; ---------------- match network access ----------------

(defun RuleMatchTree (Rule &aux queue seen m)
     (setq queue (list (cond ((?? or (ConsistencyRule Rule) (ConsistencyChecker Rule))
			      (theonly m s.t. (MatchConsistency m Rule)))
			     ((?? or (AutomationRule Rule) (AutomationGenerator Rule))
			      (theonly m s.t. (MatchAutomation m Rule)))
			     ((?? MaintainRule Rule)
			      (theonly m s.t. (MatchMaintain m Rule)))
			     (t (error "~S not a rule" Rule)))))
     (loop while (setq m (pop queue)) collect
	   (progn (push m seen)
		  (loop for p in (matchpredecessors m) unless (member p seen) do
			(push p queue))
		  (list m (matchvars m) (matchwff m)
			(or (get (matchcode m) :previous-definition) (matchcode m))
			(matchpredecessors m)))))


(defun MatchNodes-< (rules &aux queue result n nextqueue)
     (and (eq rules t) (setq rules (listof rule)))
     (loop for y in rules do
	   (loop for x s.t. (or (matchconsistency x y)
				(matchautomation x y)
				(matchMaintain x y)) do
		 (push x queue)))
     ; altered to return in more breadth first order
     (loop while (setq n (progn (cond ((null queue)
				       (setq queue nextqueue) (setq nextqueue nil)))
				(pop queue)))
	   do
	   (or (member n result)
	       (progn (push n result)
		      (loop for p in (matchpredecessors n)
			    unless (member p queue)
			    unless (member p result)
			    do (pushnew p nextqueue)))))
     (nreverse result))


(defun MatchNodes-> (rels &optional (changetypes '(:add :delete)) &aux queue result n)
     (and (eq rels t) (setq rels (listof relation)))
     (loop for x in rels do
	   (and (member :delete changetypes)
		(loop for y in (get-structure-property x 'deletematchers) do
		      (push y queue)))
	   (and (member :add changetypes)
		(loop for y in (get-structure-property x 'addmatchers) do
		      (push y queue))))
     (loop while (setq n (pop queue)) do
	   (or (member n result)
	       (progn (push n result)
		      (loop for p in (matchsuccessors n)
			    unless (member p queue)
			    unless (member p result)
			    do (push p queue)))))
     result)

(defun rules-sensitive-to (rels &optional (changetypes '(:add :delete)) &aux mnodes result)
  (setq mnodes (matchnodes-> rels changetypes))
  (loop for m in mnodes do
	(progn
	  (loop for r s.t. (matchconsistency m r) do (push r result))
	  (loop for r s.t. (matchautomation m r) do (push r result))
	  (loop for r s.t. (matchmaintain m r) do (push r result))))
  result)

(defun MNodeTriggers (mnodes)
  (loop for x in mnodes collect (list (vars-to-names (matchvars x)) 's.t.
				      (vars-to-names-wff (matchwff x)))))
	
; Note - undoing past a remove-inactive-matchnodes may be hazardous
;
(defun remove-inactive-matchnodes (&rest rels)
  ; this could possibly save some space, but it's really needed in order
  ; to avoid using matchnodes that contain bad compiled code (cause you
  ; were debugging your relations when they were compiled)
  (or rels (setq rels (listof relation)))
  (loop for m in (matchnodes-> rels) unless (matchactive m) do
	(warn "~&remove matchnode ~A" m)
	(setf (matchsuccessors m) nil)
	(setf (matchpredecessors m) nil))
  (loop for r in rels do
	(put-structure-property
	  r
	  (loop for m in (get-structure-property r 'deletematchers)
		when (matchactive m) collect m)
	  'deletematchers)
	(put-structure-property
	  r
	  (loop for m in (get-structure-property r 'addmatchers)
		when (matchactive m) collect m)
	  'addmatchers)))

(defun DeActivate-MatchNode (matchnode &optional (classes (matchactive matchnode)))
  (loop for class in classes do
	(and (case class
	       (:consistency (matchconsistencies matchnode))
	       (:automation (matchautomations matchnode))
	       (:maintain (matchmaintains matchnode))
	       (t nil))
	     (error "MatchNode ~S directly triggers rules of class ~S" matchnode class))
	(setf (matchactive matchnode) (delete class (matchactive matchnode)))
	(loop for pre in (matchpredecessors matchnode) do
	      (maybe-mark-inactive pre class))))

(defun active-rule-p (rule &aux (mnode (get-structure-property rule 'former-mnode)))
     (if mnode
	 nil
	 (aptypecase rule
		 ((consistencyrule ConsistencyChecker)
		   (?? E (x) (matchconsistency x rule)))
		 (maintainrule
		   (?? E (x) (matchmaintain x rule)))
		 ((automationrule automationgenerator)
		   (?? E (x) (matchautomation x rule))))))

(defun DeActivate-Rule (rule &optional nowarn)
  (flet ((warn1 () (unless nowarn (warn "~A was not active" rule))))
     (aptypecase rule
		 ((consistencyrule ConsistencyChecker)
		   (forany m s.t. (matchconsistency m rule)
			   (put-structure-property rule m 'former-mnode)
			   (-- matchconsistency m rule) t
			   ifnone (warn1)))
		 (maintainrule
		   (forany m s.t. (matchmaintain m rule)
			   (put-structure-property rule m 'former-mnode)
			   (-- matchmaintain m rule) t
			   ifnone (warn1)))
		 ((automationrule automationgenerator)
		   (forany m s.t. (matchautomation m rule)
			   (put-structure-property rule m 'former-mnode)
			   (-- matchautomation m rule) t
			   ifnone (warn1)))
		 (t (error "~A is not a rule" rule)))))

(defun ReActivate-Rule (rule &optional nowarn &aux m)
  (cond ((setq m (get-structure-property rule 'former-mnode))
	 (aptypecase rule
	      ((consistencyrule ConsistencyChecker) (++ matchconsistency m rule))
	      (maintainrule (++ matchmaintain m rule))
	      ((automationrule automationgenerator) (++ matchautomation m rule))
	      (t (warn "~A is not a rule" rule)))
	 (rem-structure-property rule 'former-mnode)
	 t)
	((not nowarn) (warn "~A was never deactivated"))))



(defun suspend-matchnodes-for-rules (rules &aux crules mrules arules delta)
  (declare (special delta)) ; do it as of previous DB
  (loop for r in rules do
	(aptypecase r
		    ((consistencyrule ConsistencyChecker) (push r crules))
		    (maintainrule (push r mrules))
		    ((automationrule automationgenerator) (push r arules))
		    (t (warn "~A is not a rule" r))))
  (flet ((sm-internal (name rules)
	      (let (#+ignore in out queue next)
		(labels ((accept (node)
			   #+ignore (pushnew node in) ; new way of suspending
			   (put-structure-property node generation# name)
			   (loop for p in (matchpredecessors node) do
				 (cond ((not (cdr (matchsuccessors p)))
					#+debug (princ "a")
					(accept p))
				       (t #+debug (princ "q")
					  (pushnew p queue)))))
			 (reject (node) (pushnew node out) #+debug (princ "r")
				 ;(loop for n in (matchpredecessors node) do (reject n))
				 ))
		  (loop for r in rules do
			(let ((node (case name
				      (:consistency (any x s.t. (matchconsistency x r)))
				      (:automation (any x s.t. (matchautomation x r)))
				      (:maintain (any x s.t. (matchmaintain x r)))
				      (t (error "")))))
			  (cond ((matchsuccessors node) (pushnew node queue)
				 #+debug (princ "q"))
				(t #+debug (princ "A")
				  (accept node)))))
		  (loop while (setq next (pop queue)) do
			(cond ((eql generation# (get-structure-property next name))
			       #+ignore (member next in) #+debug (princ "i"))
			      ((member next out) #+debug (princ "o"))
			      ((every #'(lambda (n)
					  (or (not (member name (matchactive n)))
					      #+ignore (member n in)
					      (eql generation#
						   (get-structure-property n name))))
				      (matchsuccessors next))
			       (when (member name (matchactive next))
				 #+debug (princ "B")
				 (accept next)))
			      ((some #'(lambda (n) (and (member name (matchactive n))
							(member n out)))
				     (matchsuccessors next))
			       (when (member name (matchactive next)) #+debug (princ "R")
				 (reject next)))
			      ; otherwise have to check the hard way ...
			      ((let ((q2 (list next)) #+ignore seen nn)
				 (loop while (setq nn (pop q2)) do
				       (cond ((eql generation#
						   (get-structure-property nn name)))
 ;; It seems that once we get here, odds are very good that we'll reject.  
 ;; Since this takes a significant portion of the time when it's used,
 ;; and we assume that it does no harm for the suspended rules to trigger,
 ;; we try optimizing it out ...
					     (t (return t))
					     #+ignore((member nn out) (return t))
					     #+ignore
					     ((some #'(lambda (r) (not (member r rules)))
						    (case name
						      (:consistency (matchconsistencies nn))
						      (:maintain (matchmaintains nn))
						      (:automation (matchautomations nn))))
					      #+debug (princ "X")
					      (return t))
					     #+ignore
					     (t #+debug (princ ".")
						(push nn seen)
						(loop for x in (matchsuccessors nn)
						      unless (member x in)
						      unless (member x seen)
						      when (member name (matchactive x))
						      do (pushnew x q2))))))
			       (reject next))
			      (t #+debug (princ "C")
			       (accept next)))))
		#+ignore ; get the minimal list of matchnodes to make searching easier
		(loop for m in in unless
		      (and (matchpredecessors m)
			   (every #'(lambda (x) (member x in)) (matchpredecessors m)))
		      collect m))))
  (sm-internal :consistency crules)
  (sm-internal :maintain mrules)
  (sm-internal :automation arules)))

;; for possible future debugging
#+ignore ; check to be sure that no other vars free in result
(global:advise make-matchnode :after :no-free-vars nil
  (expanddescription
    (list (matchvars (car global:values)) 's.t. (matchwff (car global:values)))))
; notice how expanddescription can be used to find the free vars of a wff



; ---------------- Undo mechanism ----------------
; This history undoing mechanism is imperfect in the following ways:
; - it does not handle contexts quite right - in particular it's not quite obvious
;   whether a ++ should be undone via a -- or an inherit
; - it depends on all relations with adders or deleters to have both
; - it can fail due to constraints like (prohibit (start ...))
; - it can fail due to transactions that change the adders/deleters of 
;   relations that are also being changed in the same transition

;(defvar history-labels nil) ; not used in new format

;; history-label needed with defrel ...

(defun new-history () nil)
(defun reset-history ()
  (withwriteaccess
    (if (intransaction)
	(warn "not allowed to reset-history while in a transaction")
	(setq global-history (new-history)))))

(defmacro-displace without-recording-history (&body forms)
  `(withwriteaccess ; careful not to turn off anyon else's recording
     (progv (when (consp global-history) '(last-recorded-transition))
	    (when (consp global-history) (list (car global-history)))
	(let ((global-history
		(if (intransaction)
		    (progn (warn "have to record history while in a transaction")
			   global-history)
		    t)))
	  ,. forms))))
#+ignore ; old version
 (defmacro-displace without-recording-history (&body forms)
  `(let ((global-history t)) ,. forms))

;kevin's patch, previous version below
(defun undo-to (label &optional query &aux stop n otherlabels)
  (when (inatomic) (error "cannot undo history while in an atomic"))
  ; if not inatomic above then we still won't be inside the withwriteaccess
  (withwriteaccess
    (loop for h in global-history as i from 1
	  do
	  (cond ((member label (get-structure-property h 'history-label))
		 (setq stop h n i)
		 (return))
		('else
		 (when (get-structure-property h 'history-label)
		   (setq otherlabels
			 (append (get-structure-property h 'history-label) otherlabels)))
		 (when (get-structure-property h 'unrecorded-history-follows)
		   (error "unrecorded history encountered before label ~A" label))
		 (when (get-structure-property h 'block-undo)
		   (error "undoable event encountered before label ~A" label))
		 (when (get-structure-property h 'transaction-in-progress)
		   (error "start of transaction in progress encountered before label ~A"
			  label))))
	  finally (setq stop nil n i))
    (unless stop (error "history label ~A not found" label))
    (when (and query otherlabels)
      (warn "undoing past the following labels: ~A" otherlabels))
    (when (or (not query) (y-or-n-p "Undo ~A event~p?" n n))
      (loop for e on global-history until (eq (car e) stop) do
	    (undo-updates (car e) t)
	    finally (setq global-history (cdr e))))
  label))


#+ignore (defun undo-to (label &optional query &aux stop n otherlabels)
  (when (inatomic) (error "cannot undo history while in an atomic"))
  ; if not inatomic above then we still won't be inside the withwriteaccess
  (withwriteaccess
    (loop for h in global-history as i from 1 until
	  (member label (get-structure-property h 'history-label))
	  do
	  (when (get-structure-property h 'history-label)
	    (setq otherlabels
		  (append (get-structure-property h 'history-label) otherlabels)))
	  (when (get-structure-property h 'unrecorded-history-follows)
	    (error "unrecorded history encountered before label ~A" label))
	  (when (get-structure-property h 'block-undo)
	    (error "undoable event encountered before label ~A" label))
	  (when (get-structure-property h 'transaction-in-progress)
	    (error "start of transaction in progress encountered before label ~A"
		   label))
	  finally (setq stop h n i))
    (unless stop (error "history label ~A not found" label))
    (when (and query otherlabels)
      (warn "undoing past the following labels: ~A" otherlabels))
    (when (or (not query) (y-or-n-p "Undo ~A event~p?" n n))
      (loop for e on global-history until (eq (car e) stop) do
	    (undo-updates (car e) t)
	    finally (setq global-history (cdr e))))
  label))
#+ignore ; previous version
(defun undo-to (&optional label (noquery t) &aux stop events)
  (withwriteaccess
    (cond (label)
	  ((eq (cdar history-labels) global-history)
	   (or (cdr history-labels) (error "no previous history labels"))
	   (setq label (caadr history-labels)))
	  (t (or history-labels (error "no previous history labels"))
	     (setq label (caar history-labels))))
    (setq stop (cdr (or (assoc label history-labels)
			(error "no such history label as ~A" label))))
    (setq events (loop for h on global-history until (eq h stop) collect
		       (progn (cond ((eq h (cdar history-labels))
				     (warn "Undoing past ~A" (caar history-labels))))
			      (car h))))
    (when (or noquery (null events) (y-or-n-p "Undo ~A events?" (length events)))
      (loop for e in events do (undo-updates e))
      (setq history-labels (member (assoc label history-labels) history-labels))
      (setq global-history stop)))
  label)


(defvar history-help
 "You are in the AP5 database history browser.
Starting from the last event (atomic update) you can see various
information about an event, move to another event, or undo an event.
There are two kinds of undoing - \"backward\" undoing means going
backward in time - only the last event may be undone.  It is undone
without any rules and then removed from the history.
Undoing \"forward\" means doing a new atomic update with the opposite 
effect of the current event: delete all the stored tuples added and
add all the stored tuples deleted.
Forward undo's are done with rules in effect.  Any event may be 
undone forward (and in fact the undo may later be undone).
Note, however, that forward undo's may abort or trigger automations.
The following commands are currently supported:
q quit
<space> show the previous event
p change printing parameters
j jump to an arbitrary event
b undo backward (only allowed from the end) then show previous event
f undo the current event forward then show previous event
s search for an event
x exit with this event as the value of HISTORY (for further processing)
<otherwise> print this message [the value of ap5::history-help]")

; *** how about event descriptors, grouping, ...

(declaim (special history-print-length history-print-level
		    history-ask-more? history-decide-per-relation?
		    history-max#updates history-field))
#-aclpc1
(setf history-print-length 5 history-print-level 4
      history-ask-more? nil history-decide-per-relation? nil
      history-max#updates 9 history-field 'direct)

#+aclpc1 ; compiler bug
(eval '
 (setf history-print-length 5 history-print-level 4
       history-ask-more? nil history-decide-per-relation? nil
       history-max#updates 9 history-field 'direct))

#+(or ti symbolics)
(declaim (inline read-char*))

(defun read-char* (stream)
  #+(or ti symbolics)
  (read-char stream)
  #-(or ti symbolics)   ; same as read-char but ignores nl's - for hp
    (loop with ans unless (char= #\newline (setf ans (read-char stream)))
	  do (return ans)))

(defun history (&key (print-length history-print-length)
		     (print-level history-print-level)
		     (ask-more? history-ask-more?)
		     (decide-per-relation? history-decide-per-relation?)
		     (max#updates history-max#updates)
		     (field history-field) search-key
		     &aux (history global-history) (pos 0))
  (flet ((newline (s)
	  (fresh-line *query-io*)
	  (write-string s *query-io*)))
    (unless history
      (newline  "There is no history.")
      (return-from history nil))
    (withwriteaccess
      (loop
	(unless history
	  (newline "end of history.")
	  (return-from history nil))
	(show-event (first history) :max#updates max#updates
		    :print-length print-length :print-level print-level
		    :field field :ask-more? ask-more?
		    :decide-per-relation? decide-per-relation?)
	(loop do
	      (newline "q, <space>, p, j, b, f, s, x, ? ")
	      until
	      (case (read-char* *query-io*)
		(#\x (return-from history (first history)))
		(#\q (return-from history nil))
		(#\j (let ((lgh (+ pos (length history))) to)
		       (format *query-io*
			       "~&current position is ~A ~
                         (latest event = 0, earliest recorded = ~A)~
                         ~&jump to (number) : " pos lgh)
		       (setf to (read *query-io*))
		       (cond ((not (and (integerp to) (<= 0 to lgh)))
			      (newline "illegal position"))
			     ((>= to pos)
			      (setf history (nthcdr (- to pos) history)
				    pos to))
			     (t (setf history (nthcdr to global-history)
				      pos to))))
		     t)
		(#\space (pop history) (incf pos) t)
		(#\p
		 (format *query-io*
			 "~&Change what: l (printLength = ~A), d (printDepth = ~A), ~
                    n (Number of updates to show = ~A), ~
                  ~&m (More mode = ~A), r (ask for each Relation = ~A) or ~
                    w (Which updates to show = ~A) ? "
			 print-length print-level max#updates ask-more?
			 decide-per-relation?
			 (case field (delta "end result") (direct "stored updates")
			       (otherwise "originally requested updates")))
		 (case (read-char* *query-io*)
		   (#\l (newline "new value: ")
			(setf print-length (read *query-io*)))
		   (#\d (newline "new value: ")
			(setf print-level (read *query-io*)))
		   (#\n (newline "new value (nil means all): ")
			(setf max#updates (read *query-io*)))
		   (#\m (setf ask-more? (not ask-more?)))
		   (#\r (setf decide-per-relation? (not decide-per-relation?)))
		   (#\w (format *query-io*
				"~&Show e (End result), s (Stored updates) or ~
                           i (Initially requested updates) ? ")
			(setf field (case (read-char* *query-io*)
				      (#\e 'delta)
				      (#\s 'direct)
				      (#\i 'originalupdates)
				      (otherwise
				       (newline "illegal response ignored")
				       field))))
		   (otherwise (newline "illegal response ignored")))
		 t)
		(#\b
		 (cond
		   ((not (eq history global-history))
		    (newline "Backward undo allowed only from end of history")
		    nil)
		   ((get-structure-property (first global-history)
					    'unrecorded-history-follows)
		    (newline "Backward undo disallowed due to unrecorded transitions")
		    nil)
		   ((get-structure-property (car global-history)
					    'block-undo)
		    (newline "Backward undo blocked for this event")
		    nil)
		   (t (undo-updates (car global-history) t)
		      (setf history (cdr history)	; pos remains 0
			    global-history history)
						; NOT cddr (global-history) -
						;undoing noop does not change global-history
		      t)))
		(#\f (undo-updates (first history) nil)
		     (pop history) (incf pos 2) t)
		(#\s (format *query-io*
			     "~&Search for ~@[<space> ~A, ~]r (change to a Relation), ~
                        p (a Process) or s (event Satisfying a predicate) "
			     search-key)
		     (case (read-char* *query-io*)
		       (#\space nil)
		       (#\r (newline "search for relation: ")
			    (setf search-key (relationp (check-relation-package-error
							  (read *query-io*)))))
		       (#\p (format *query-io*
				    "~& search for process (name or <space> for ~A): "
				    (current-process-name))
			    (setf search-key
				  (cond ((eql #\space (peek-char nil *query-io*))
					 (read-char* *query-io*)
					 (current-process-name))
					(t (string (read *query-io*))))))
		       (#\s (newline "search for event satisfying predicate named: ")
			    (setf search-key (read *query-io*)))
		       (otherwise (setf search-key nil)))
		     (cond ((null search-key)
			    (newline *query-io*))
			   (t (let (new-h (new-pos (1+ pos)))
				(loop for h on (cdr history) until
				      (cond ((relationp search-key)
					     (assoc search-key
						    (delta (car (consistency-cycles
								  (car h))))))
					    ((stringp search-key)
					     (string-equal search-key
							   (get-structure-property (car h)
										   'process)))
					    (t (funcall search-key (car h))))
				      do (write-char #\. *query-io*) (incf new-pos)
				      finally (setq new-h h))
				(cond (new-h (setf history new-h pos new-pos))
				      (t (newline "not found"))))))
		     t)
		(otherwise (newline history-help) nil)))))))

(defun ask-undo ()
  (warn "ask-undo is obsolete - calling (history) instead")
  (history))

(defun show-history ()
  (warn "show-history is obsolete - calling (history) instead")
  (history))


(defun show-event (event &key (stream *query-io*) (max#updates 10)
			 (print-length 5) (print-level 4)
			 (field 'originalupdates) ask-more? decide-per-relation?
			 &aux updates nupdates norig ndelta nstored
			 (*print-length* print-length)
			 (*print-level* print-level))
  (when (get-structure-property event 'history-label)
    (format stream "~&history label ~A"
	    (get-structure-property event 'history-label))
    (return-from show-event nil))
  (setq norig (length (originalupdates event))
	ndelta (loop for u in (delta (car (consistency-cycles event)))
		     sum (length (cdr u)))
	nstored (loop for u in (direct (car (consistency-cycles event)))
		      sum (length (cdr u))))
  (cond ((eq field 'originalupdates)
	 ;; sort them by relation
	 (setq updates nil nupdates norig)
	 (when (< 100 nupdates)
	   (format stream "~&sorting ~A updates ..." nupdates))
	 (loop for u in (originalupdates event) do
	       (let (entry (rel (tuprel (updtuple u))))
		 (setq entry (assoc rel updates))
		 (unless entry (push (setq entry (list rel)) updates))
		 (push u (cdr entry)))))
	(t (setq event (car (consistency-cycles event)))))
  (when (and (consistency-cycle-record-p event)
	     (member field '(direct directdelta indirect maintain
				   again delta #+ignore activations)))
    (setq updates (funcall field event)
	  nupdates (loop for u in updates sum (length (cdr u)))))
  (unless nupdates (error "bad event/field arguments to show-event"))
  (format stream "~&~A original update~P, ~A stored update~P, ~A update~P in delta"
	  norig norig nstored nstored ndelta ndelta)
  (cond (decide-per-relation?
	 (let (*print-length*)
	   (format *query-io* "~&relations updated: ~A" (mapcar 'car updates)))
	 (loop for u in updates when
	       (progn (format *query-io* "~&show updates to ~A ? ~
                                         (q = quit, n = no, otherwise = yes "
			      (car u))
		      (case (read-char* *query-io*)
			(#\q (return-from show-event nil))
			(#\n nil)
			(t t)))
	       do
	       (let ((ul (cdr u)))
		 (cond (max#updates 
			(loop do
			      (loop for i below max#updates while ul
				    do (format stream "~&~A" (pop ul)))
			      while (and ul
					 (cond (ask-more? (y-or-n-p "~& more? "))
					       (t (format stream
					           "~&more updates not displayed")
						  nil)))))
		       (t (loop while ul do (format stream "~&~A" (pop ul))))))))
	(t (let ((nleft max#updates))
	     (loop for u in updates do
		   (loop for ul in (cdr u) do
			 (when (and nleft
				    (>= 0 nleft)
				    (or (when (not ask-more?)
					  (format stream
					     "~&more updates not displayed")
					  t)
					(not (when (y-or-n-p "~& more? ")
					       (setq nleft max#updates)))))
			   (return-from show-event nil))
			 (when nleft (setq nleft (1- nleft)))
			 (format stream "~&~A" ul)))))))
						
(defun undo-updates (history-event dormant-rules-p)
  (when (inatomic) (error "cannot undo history while in an atomic"))
  ; expansion of with-dormant-rules 
  (LET* ((SUSPENDED-RULE-CLASSES
	   (cond (dormant-rules-p '(:CONSISTENCY :MAINTAIN :AUTOMATION))
		 (t SUSPENDED-RULE-CLASSES)))
	 (FIX-MAINTAINED-RELATION (or dormant-rules-p FIX-MAINTAINED-RELATION)))
     ; we'll include maintain(1) and direct (4), just like dodbupdates
     (atomic
       (loop for class in
	     (list (direct (first (consistency-cycles history-event)))
		   (when dormant-rules-p
		     (maintain (first (consistency-cycles history-event)))))
	     do
	     (loop for entry in class do
		   (loop for u in (cdr entry) do
			 (let ((tuple (updtuple u)))
			   (apply 'do-update
				  (ecase (tuptv tuple)
				    ((t) nil)
				    ((nil) t)
				    #+ignore
				    (otherwise
				      (error "Inherit's can't (yet) be undone.~
                                              ~% Make DonC fix it.")))
				  (tuprel tuple)
				  (tupargs tuple)))))))))

; at end of load do (history-label 'beginning)

; ---------------- recovering from atomics ----------------

(defmacro retract-update (&rest update)
  `(retract-update-internal ',(car update) ',(cadr update) ,@(cddr update)))

(defun retract-update-internal (tv rel &rest tuple &aux (origrel rel) tup (n 0))
  (unless (boundp 'in-recover-atomic)
    (error "Retract-Update is only to be used for recovering from failed atomics"))
  (setq tv (case tv (++ t) (-- nil)
		 (otherwise (error "updates must start with ++ or --"))))
  (unless (setq rel (relationp rel))
      (error "~A is an unknown relation" origrel))
  (unless (inatomic) (error "Retract-Update can only be done in an atomic"))
  (setq |Updates |
	(loop with compfn for u in |Updates | unless
	      (and (eq tv (tuptv (setq tup (updtuple u))))
		   (eq rel (tuprel tup))
		   (funcall (or compfn (setf compfn (tuple-comparison rel)))
			    tuple (tupargs tup))
		   (incf n))
	      collect u))
  n)

(defvar browse-atomic-help 
 "You are in the AP5 atomic browser.  You can see the proposed updates
(NOT including any that have been REVEALed!).
Updates may be added to this set via ++ and -- and may be removed from
the set via (Retract-Update ++ rel . args) or (Retract-Update -- rel . args)

The top level commands are:
q Quit (done editing)
<space> show the next update
p change Printing parameters
j jump to some particular update indexed by number
n move to the first update of the next relation
r move to the first update of a given relation
s search for the next update of a given object
a show All updates
<otherwise> print this message [the value of ap5::edit-atomic-help")

(defun browse-atomic (&aux (*print-length* history-print-length)
			 (*print-level* history-print-level)
			 updates nupdates rels cur-tail pos)
  (unless (eq (inatomic) 'atomic)
    (error "browse-atomic called in the wrong context"))
  (format *query-io* "~&Entering the atomic browser")
  (setq nupdates (length |Updates |))
  (when (< 100 nupdates)
    (format *query-io* "~&sorting updates ..."))
  (loop for u in |Updates | do
	(let (entry (rel (tuprel (updtuple u))))
	  (setq entry (assoc rel updates))
	  (unless entry (push (setq entry (list rel)) updates))
	  (push u (cdr entry))))
  (setq rels (mapcar 'car updates))
  (setq updates (apply 'nconc (mapcar 'cdr updates)))
  (format *query-io* "~&updates to ~A relation~P: ~A"
	  (length rels) (length rels) rels)
  (setq cur-tail updates pos 0)
  (loop
    (if (car cur-tail) (format *query-io* "~&~A" (car cur-tail))
	(format *query-io* "~&no more updates"))
    (format *query-io* "~&q, <space>, p, j, n, r, s, a, ? ")
    (case (read-char* *query-io*)
      (#\q (return nil)) ; from loop
      (#\space (when cur-tail (pop cur-tail) (incf pos)))
      (#\p
       (format *query-io*
	       "~&Change what: l (printLength = ~A), d (printDepth = ~A) ? "
	       *print-length* *print-level*)
       (case (read-char* *query-io*)
	 (#\l (format *query-io* "~&new value: ")
	  (setq *print-length* (read *query-io*)))
	 (#\d (format *query-io* "~&new value: ")
	  (setq *print-level* (read *query-io*)))
	 (otherwise (format *query-io* "~& illegal response ignored"))))
      (#\j (let (to)
	     (format *query-io*
		     "~&current position is ~A ~
                       (first update = 0, last = ~A)~
                      ~&jump to (number) : " pos nupdates)
	     (setq to (read *query-io*))
	     (cond ((not (and (integerp to) (<= 0 to nupdates)))
		    (format *query-io* "~&illegal position"))
		   ((>= to pos)
		    (setq cur-tail (nthcdr (- to pos) cur-tail) pos to))
		   (t (setq cur-tail (nthcdr to updates) pos to)))))
      (#\n (let ((rel (and cur-tail (tuprel (updtuple (pop cur-tail))))))
	     (loop while (and cur-tail (eq rel (tuprel (updtuple (car cur-tail)))))
		   do (pop cur-tail) (incf pos))))
      (#\r (let (rel)
	     (format *query-io* "~&move to relation: ")
	     (setq rel (read *query-io*))
	     (unless (setq rel (relationp rel))
	       (format *query-io* "~& not a relation name"))
	     (setq cur-tail updates pos 0)
	     (loop while (and cur-tail
			      (not (eq rel (tuprel (updtuple (car cur-tail))))))
		   do (pop cur-tail) (incf pos))))
      (#\a (when (or (< nupdates 20)
		     (y-or-n-p
		       "~&There are ~A updates - do you really want to see them all? "
		       nupdates))
	     (loop for u in updates do (format *query-io* "~&~A" u)))
           (format *query-io* "~%~%"))
      (#\s (let (ob rel equivs)
	     (format *query-io*
		     "~&search for what object (enter a form to evaluate): ")
	     (setq ob (eval (read *query-io*)))
	     (loop while
		   (and cur-tail
			(progn
			  (unless (eq rel (tuprel (updtuple (car cur-tail))))
			    (setq rel (tuprel (updtuple (car cur-tail))))
			    (setq equivs (loop for p below (arity* rel)
					       collect (get-comparison rel p))))
			  (loop for x in (tupargs (updtuple (car cur-tail)))
				as eqv in equivs never
				(testrel eqv x ob))))
		   do (princ "." *query-io*) (pop cur-tail) (incf pos))))
      (otherwise (format *query-io* "~&~a" browse-atomic-help) nil))))

(defmacro from-abort ((&key (abortdata '(when (boundp 'abortdata) abortdata) abd-p)
			    ((:delta use-delta)
			     '(when abortdata
				(delta (car (consistency-cycles
					      (car (last abortdata))))))
			     del-p)
			    ((:updatestatus use-updatestatus) ''report-inconsistency))
		      &rest body)
  (or body (setq body '((break))))
  (when (and del-p (not abd-p)) (setq abortdata nil))
  `(let* ((abortdata ,abortdata)
	  (delta ,use-delta)
	  (|UpdateStatus | ,use-updatestatus)
	  |Direct | |Maintain |)
     (declare (special |Direct | |Maintain |))
     (loop for d in delta unless (derivedrel (car d)) do
	   (if (?? E (x y) (maintainedrel (car d) x y))
	       (push d |Maintain |)
	       (push d |Direct |)))
     (withwriteaccess
       (check-generation# (car (last abortdata)))
       ,@body)))


; ---------------- generator-cache as a relation ----------------

; really ought to convert the rest to defrelation...
(defrelation generator-cache :arity 3 :representation tree :nonatomic t
	     :equivs (eql equal equal))
(put-structure-property (relationp 'generator-cache) generator-cache 'treedata)
(deftypeconstraints :none generator-cache ((x) s.t. (or (symbol x)(relation x)))
		    description list)
(++ relsize (relationp 'generator-cache) '(output output output) 20000)
(++ relsize (relationp 'generator-cache) '(input output output) 50)
(++ relsize (relationp 'generator-cache) '(output input output) 1)
(++ relsize (relationp 'generator-cache) '(output output input) 1)

#+ignore 
(++ reldeleter (dbo relation generator-cache)
    '(lambda (&rest ignore) (declare (ignore ignore))
	     'delete-generator-from-cache))
#+ignore 
(defun delete-generator-from-cache (ignorerel ignorecar desc gen)
  (declare (ignore ignorerel ignorecar))
  ; delete all of the copies
  (gendeleter desc gen))

(defun find-gen-fn (fn rel-or-name &optional decache?)
   (when (keywordp fn) (setq fn (intern (symbol-name fn) (find-package "AP-COMPILED"))))
   (loop for (y z) s.t. (generator-cache (relationp rel-or-name) y z) do
	 (cond ((eq fn (cadr (assoc 'initialstate z)))
		(when decache? (gendeleter y z))
		(return-from find-gen-fn y))
	       ((eq fn (cadr (assoc :previous-fn z)))
		(return-from find-gen-fn y))))
   :not-found)

; ---------------- tell-me-about ----------------

(defvar default-tuple-printer 'print-tuple)

(defun print-tuple (stream rel &rest args)
  (fresh-line stream)
  (write (relationnamep rel) :stream stream)
  (write args :stream stream :pretty t :length 5 :level 2))
; not only protect against infinite loops, but also keep is fairly small

(defvar *tell-me-about-tuple-limit* 5)


(defun tell-me-about (object &key (stream *standard-output*) verbose
			     (rels (default-tell-me-about-rels))
			     (more *tell-me-about-tuple-limit*)
			     (printer default-tuple-printer)
			     &aux types)
  ; verbosity means mentioning the things that can't be generated and 
  ; telling the user when attempting to compile a new generator
  ; that belongs in the arg list but compiler bug prevents it ...
  (loop for tp in (setq types (all-types-of object))
	when (member tp rels) do (funcall printer stream tp object))
  (loop for rel in rels do
	(when verbose (format stream "...~A" (relationnamep rel)))
	(loop for arity s.t.
	      (and (relationarity rel arity) (not (= arity 1))) ; already did types
	      do
	      (loop for pos below arity
		    unless (type-incompatible rel pos types)
		    do (ShowTuplesOf rel pos object arity stream verbose more printer)))))

(defvar tma-template-table nil)
(defun tma-desc (rel pos arity &aux entry)
  (or (setq entry (assoc arity tma-template-table))
      (push (setq entry
		  (cons arity
			(loop for p below arity collect
			      (let ((args
				      (loop for i below arity collect
					    (cond ((= p i) 'c0)
						  ((> p i) (pack* 'x i))
						  (t (pack* 'x (1- i)))))))
				(list args (remove 'c0 args))))))
            tma-template-table))
  (setq entry (nth pos (cdr entry)))
  (list (cadr entry) 's.t. (cons rel (car entry))))

(defun showtuplesof (rel pos object arity stream verbose more printer &aux gen)
  (cond ((?? equivalence-relation rel)
	 (when verbose (format stream t-m-a-f1 (relationnamep rel))))
	((and (defined-p rel)
	      (eq (setq gen (lookup-gen+ (tma-desc rel pos arity)))
		  :cannot-generate))
	 (when verbose (format stream t-m-a-f2 (relationnamep rel) pos)))
	((and (not (defined-p rel))
	      (eq (setq gen (lookup-gen (tma-desc rel pos arity) t)) :cannot-generate))
	 (when verbose (format stream t-m-a-f2 (relationnamep rel) pos)))
	(t (cond ((= arity 1)
		  (when (testrel rel object) (funcall printer stream rel object)))
		 (t (setq gen (funcall gen object))
		    (loop with i = 0 and values
		       do (when (car (setq values (multiple-value-list (funcall gen))))
			    (return nil))
		          (unless (or (null more) (< i (abs more))
				      (and (> more 0) (setq i 0) (y-or-n-p "more?")))
			    (return nil))			  
			  (let ((tail (nthcdr pos values))) ; insert object
			    (push object (cdr tail)))
			  (apply printer stream rel (cdr values))
			  (incf i)))))))

; how about a fn that takes a canondesc which is allowed to contain defined rels,
; does a gen-cache-i-i-o, if not there does expanddesc, findgen, caches result under
; original desc 
(defun lookup-gen+ (canondesc) ; always does the noerror thing
 (let ((wff (caddr canondesc)))
    #+ignore
    (unless (or (compoundwffp wff) (dbobject-p (car wff)))
      (break "adding generator cache entry for non relation ~A" wff))
  (cond
    ((cadr (assoc 'initialstate (gen-cache-i-i-o canondesc))))
    ((and (relationp (car wff))
	  (?? relationimplementation (relationp (car wff)) 'defined))
      (let (ans realdesc evlvars evlrels)
	(multiple-value-setq (realdesc evlvars evlrels)
	  (expanddescription canondesc
			     :allowevalargs t :keepstarts t))
	(and evlrels (error "funcall/apply not allowed in lookup-gen+"))
	(setq ans (try (get-generator realdesc)
		       'ap5-cannot-generate :cannot-generate))
	(or (cadr (assoc 'initialstate (gen-cache-i-i-o canondesc)))
	    ; this had to be added for funcalls when get-gen creates it
	    (progn
	      (cond ((eq ans :cannot-generate)
		     (setq ans `((initialstate :cannot-generate))))
		    (t (setq ans `((initialstate
				     ,(compile-ap
					`(lambda ,(mapcar #'cadr evlvars)
					   (let ,evlvars ,ans))))
				   (template
				     ,(loop for arg in (cdr (third canondesc))
					    collect
					    (cond ((member arg (car canondesc))
						   'output)
						  (t 'input))))))))
	      (genadder canondesc ans)
	      (cadar ans)))))
    (t (lookup-gen canondesc t)))))

(defrelation dont-tell-me-about :types (relation))

(defun default-tell-me-about-rels ()
  (listof relation#relation s.t. (not (dont-tell-me-about relation))))

(defun all-rels ()
  (listof relation#relation s.t. true))

(defun rels-without-wffdefn ()
  (listof relation#relation s.t. (not (E (def) (wffdefn relation def)))))

(defun rels-without-defn ()
  (listof relation#relation s.t. (not (or (E (def) (wffdefn relation def))
				  (E (def) (codedefn relation def))))))

(defun type-incompatible (rel pos types)
  ; return t if an object of the given types cannot be in any tuple of rel at pos
  ; = if there's a type constraint that's not one of the types -
  ; this relies on the fact that types contains ALL types of the object,
  ; not just the most specific ones!
  (loop for type s.t. (typeconstraint-stored rel pos type) thereis
	(and (not (listp type)) ; descriptions don't count here
	     (not (member type types)))))

(loop for x in
      '(SUBREL-STORED ISUBREL+ ISUBREL+* MAINTAININGTRIGGER MAINTAININGCODE
		      TYPECONSTRAINT-STORED SUBRELTRIGGER ;TELL-ME-ABOUT-FNS
		      ;LISP-FUNCTION-INPUT-ARITY LISP-FUNCTION-OUTPUT-ARITY 
		      SUBTYPE ANY-FOR)
      do (++ dont-tell-me-about (relationp x)))

(defvar t-m-a-f1 "~%... don't bother to generate equivalence relation ~A")
(defvar t-m-a-f2 "~%...cannot generate ~A in position ~A")

; ---------------- dumping compiled code ----------------
; let's try to get the compilation done at compile-time for a change ...
#+ignore
(defmacro-displace load-tma-table ()
  `(progn ,.
     (loop for (rel arity) s.t. (relationarity rel arity)
	   unless (eq arity 1)
	   unless (?? dont-tell-me-about rel)
	   nconc
	   (loop for pos below arity do (princ "." *trace-output*)
		 nconc 
		 `((++ tell-me-about-fns ',rel ,pos
		       ,(dump-copy-symbol
			  (any x s.t. (tell-me-about-fns rel pos x)
			       :ifnone
			       (tell-me-about-compile rel pos arity nil nil))))
		   ; now try to recover the cached generator too
		   ,.(let ((temp (loop for i below arity collect
				       (cond ((= i pos) 'input) (t 'output))))
			   entry)
		       (when (setq entry (assoc temp (get-structure-property
						      rel 'generator-cache)
					       :test #'equal))
			    `((or (assoc ',temp (get-structure-property
						 ',rel 'generator-cache)
					:test #'equal)
				  (add-structure-property
				    ',rel
				    (list ',temp
					  (cons (list 'initialstate ; the compiled fn
						      ,(dump-copy-symbol
							 (cadr (assoc 'initialstate
								      (cadr entry)))))
						',(remove (assoc 'initialstate
								 (cadr entry))
							  (cadr entry))))
				    'generator-cache))))))))))

(defun dump-copy-symbol (symbol)
  `(let ((s (gentemp "F" "AP-COMPILED")))
     (setf (get s :previous-definition) ',(get symbol :previous-definition))
     ,.(and (fboundp symbol)
	    `((setf (symbol-function s) ',(symbol-function symbol))))
     s))
#+ignore
(load-tma-table)

; build up the tester cache
(progn (loop for type# s.t. true do (checktype type nil)))

; function to precompile everything for tell-me-about
(defun prepare-tma ()
  (loop for (rel arity) s.t. (relationarity rel arity) do
	(princ ".")
	(cond ((= arity 1) (get-tester rel))
	      ((defined-p rel)
	       (loop for pos below arity do (lookup-gen+ (tma-desc rel pos arity))))
	      (t (loop for pos below arity do (lookup-gen (tma-desc rel pos arity) t))))))

; insert (recompile-decached-generators) in a file and compile it ...
; we purposely leave the var bound so you can continue after it breaks
(defmacro recompile-decached-generators (&optional (new-set t) ;&aux (prototype-mode t)
					 )
  (declare (special gens-to-recompile))
  (when new-set
    (setq gens-to-recompile
	(loop for (x y z) s.t. (generator-cache x y z)
	      unless (eq (car (third y)) 'subset-gen)
	      when (eq x (car (ilistp (third y))))
	      when (eq :recompile (cadr (assoc 'initialstate z)))
	      collect y)))
  (warn "starting to recompile ~A generators ~
        ~& x = cannot generate, . = recompiled, ? = invalid description"
	(length gens-to-recompile))
  (loop for n in gens-to-recompile do
	(try (try (progn (lookup-gen+ n) (princ "."))
		  ap5-cannot-generate
		  (princ "x")
		  (setq gens-to-recompile (delete n gens-to-recompile)))
	     expanddescription
	     (princ "?")
	     (setq gens-to-recompile (delete n gens-to-recompile))))
  `(progn
     ,.(loop for n in gens-to-recompile collect (compile-code-for-desc n))))


; ---------------- decache-rel ----------------
; This still does not do all that throwing out and redeclaring the relation would.
; For instance, the internal data is not changed.
; This is thus not sufficient for changing implementations or equivalence relations
; (at least not after data has been stored)
; Also, undoing past a decache-rel may be hazardous.
;

(defrelation decache-rel-keyword-fn :arity 2)

(defun decache-rel (origrel &rest decache-rel-args
		    ;&key &allow-other-keys
		    &aux rel decache-rel-all)
  (unless decache-rel-args (error "decache-rel called without arguments"))
  ;(when (inatomic) (error "Decache-Rel should be done outside an atomic"))
  (flet ((lookup-keyword (kwd &aux tail)
	   (and (setf tail (member kwd decache-rel-args))
		(not (and (cdr tail) (null (cadr tail)))))))
    (when (setq rel (relationp origrel))
      (setq decache-rel-all (lookup-keyword :all))
      (loop for (kwd fn) s.t. (decache-rel-keyword-fn kwd fn)
	  when (or decache-rel-all
		   (when (lookup-keyword kwd)
		     (setf decache-rel-args (remove kwd decache-rel-args))
		     t))
	  do (funcall fn rel))
      (when (find-if #'(lambda (x) (and (keywordp x) (not (eq x :all))))
		     decache-rel-args)
	#+ignore (setq decache-rel-args
	      (remove :all (remove-if-not 'keywordp decache-rel-args)))
	;; a RUN-TIME warning!! VERY strange.
	(warn "extraneous args to decache-rel ~A" decache-rel-args)))))

#|
At one time I tried to recompile testers/adders/deleters on decache.
This leads to waste in the common cases of defrel.  Instead I want to
cause recompilation on next use.  There are two possible paths of next
reuse, however.  If I simply remove the property of the relation then
the code will be recompiled on next macroexpansion, but already compiled
code will continue to use the obsolete definition.   I both remove the
property and replace the current definition with one that will cause
the macro expansion and then execute it.
|#

(++ decache-rel-keyword-fn :tester
    #'(lambda (rel)
	(let ((sym (get-structure-property rel 'tester)))
	  (when sym
		(setf (symbol-function sym)
		      #'(lambda (&rest args) (?? apply rel args)))))
	(rem-structure-property rel 'tester)))
(++ decache-rel-keyword-fn :adder
    #'(lambda (rel)
	(let ((sym (get-structure-property rel 'adder)))
	  (when sym
		(setf (symbol-function sym)
		      #'(lambda (&rest args) (++ apply rel args)))))
	(rem-structure-property rel 'adder)))
(++ decache-rel-keyword-fn :deleter
    #'(lambda (rel)
	(let ((sym (get-structure-property rel 'deleter)))
	  (when sym
		(setf (symbol-function sym)
		      #'(lambda (&rest args) (-- apply rel args)))))
	(rem-structure-property rel 'deleter)))

(++ decache-rel-keyword-fn :relevant-updates
    #'(lambda (rel) (rem-structure-property rel 'relevant-updates)))
(++ decache-rel-keyword-fn :comparetuple
    #'(lambda (rel)
	(rem-structure-property rel 'comparetuple)
	(rem-structure-property rel 'comparecanontuple)
	(rem-structure-property rel 'canonicalizetuple)
	(rem-structure-property rel 'rel-comparerels)
	#+ignore ; this is already done when comparisons are changed by rule
	; THROW-OUT-INVALID-DEFNS - also this is wrong for automation triggers
	(loop for r s.t. (relation-in-defn rel r) do
	      (try (expanddescription
		     (copy-tree
		       (any d s.t. (wffdefn r d) ifnone
			  (forany d s.t. (ruletrigger r d) (list nil 's.t. d)))))
		   expanddescription
		   (warn "deleting ~A which now has an invalid definition~
                          ~& reason: ~A" r tryvalue)
		   (-- relation r) (-- rule r)))))

(++ decache-rel-keyword-fn :expanded-defn
    #'(lambda (rel)
	(rem-structure-property rel 'expanded-defn)
	(rem-structure-property rel 'expanded-defn-vars)))
(++ decache-rel-keyword-fn :place-check-fn
    #'(lambda (rel) (rem-structure-property rel 'place-check-fn)))
(++ decache-rel-keyword-fn :cached-trigger-fn
    #'(lambda (rel) (rem-structure-property rel 'cached-trigger-fn)))
(defun decache-generator (rel)
  ;; don't do (-- gen-cache ..) - DB update does more harm than good
  (loop for (x y z) s.t. (and (generator-cache x y z)
			      (or (eql x rel)
				  #+ignore (relation-in-defn* rel x)
				  (derived-from* x rel)))
	do (gendeleter y z))
  (setf findgens-cache nil))
(++ decache-rel-keyword-fn :generator #'decache-generator)

(++ decache-rel-keyword-fn :relsize
    #'(lambda (rel) (rem-structure-property rel 'relsize-cache)))

(++ decache-rel-keyword-fn :worldspat
    #'(lambda (rel) (rem-structure-property rel :worldspat-alist)))

;; this seems unnecessary - all the matchnodes do is run generators and these are
;; already decached
(++ decache-rel-keyword-fn :recompile-rules 'recompile-rules)
;; since it's currently documented, keep it but don't let it do anything
(defun recompile-rules (rel) rel)

(let ((tups (listof x y z u v s.t. (trigger x y z u v)))
      (old (symbol-function 'possibletoupdate)))
  ;; Unfortunately, this is one of those relations needed in bootstrapping ...
  (setf (symbol-function 'possibletoupdate)
	#'(lambda (ignore ignore2) (declare (ignore ignore ignore2)) t))
  (atomic (++ relationimplementation (dbo relation trigger) 'full-index)
	  (-- relationimplementation (dbo relation trigger) 'base))
  (decache-rel 'trigger :all)
  (any x y z u v s.t. (trigger x y z u v) ifnone nil)
  (any x y z s.t. (trigger x y z nil nil) ifnone nil)
  (loop for x in tups do (++ apply (dbo relation trigger) x))
  (setf (symbol-function 'possibletoupdate) old))

#+ignore ; this also contains some bug that leaves you with only the top of a matchnetwork
(defun recompile-rules (rel)
  (rem-structure-property rel 'addmatchers)
  (rem-structure-property rel 'deletematchers)
  (let ((mnodes (matchnodes-< (listof rule#rule s.t. (relation-in-defn* rel rule)))) m a c)
    (loop for mn in mnodes
	  when (rel-in rel (matchwff mn)) do
	  (loop for pred in (matchpredecessors mn) do
		(setf (matchsuccessors pred) (delete mn (matchsuccessors pred))))
	  (setf (matchpredecessors mn) nil)
	  (setq c (matchconsistencies mn))
	  (setq a (matchautomations mn))
	  (setq m (matchmaintains mn))
	  when (or c a m)
	  do (let ((new (ignore-errors (detect+ (matchvars mn) (matchwff mn))
			  #+ignore
			  (cond ((eq (car (matchwff mn)) 'start*)
				 (detect* (matchvars mn) (cadr (matchwff mn))))
				(t (detect+ (matchvars mn) (matchwff mn)))))))
	       (unless (eq new mn)
		 (atomic
		   (loop for r in c do
			 (-- matchconsistency mn r)
			 (cond (new (++ matchconsistency new r))
			       (t (warn "no longer able to trigger ~A" r))))
		   (loop for r in a do
			 (-- matchautomation mn r)
			 (cond (new (++ matchautomation new r))
			       (t (warn "no longer able to trigger ~A" r))))
		   (loop for r in m do
			 (-- matchmaintain mn r)
			 (cond (new (++ matchmaintain new r))
			       (t (warn "no longer able to trigger ~A" r))))))))))

#+ignore ; hold on to old defn for now
(defun decache-rel (rel &key all tester adder deleter inheriter
		    comparetuple expanded-defn
		    generator non-compound-gen fix-existing-generator
		    recompile-rules)
  ; all means other keys should be assumed t
 (when (inatomic) (error "Decache-Rel should be done outside an atomic"))
 (when (setq rel (relationp rel))
  (when (or all tester) (rem-structure-property rel 'tester))
  (when (or all adder) (rem-structure-property rel 'adder))
  (when (or all deleter) (rem-structure-property rel 'deleter))
  (when (or all inheriter) (rem-structure-property rel 'inheriter))
  (when (or all comparetuple)
    (rem-structure-property rel 'comparetuple)
    (rem-structure-property rel 'canonicalizetuple)
    (rem-structure-property rel 'rel-comparerels))
  (when (or all expanded-defn) (rem-structure-property rel 'expanded-defn))
  (when (and (or all non-compound-gen generator)
	     (any y z s.t. (generator-cache rel y z) ifnone nil))
    ; assume that if there are no gens for rel then it's not used in any compound ones
    ; atomic ;; why clutter up history ?
    ; one current answer is that the -- below has to be done before the
    ; next lookup-gen
    (loop for (y z) s.t. (generator-cache rel y z) do
	  (let ((old (lookup-gen y t)) new)
	    (-- generator-cache rel y z)
	    (when (or all fix-existing-generator)
	      (setq new (lookup-gen y t))
	      (cond ((and (eq new :CANNOT-GENERATE)
			  (not (eq old :CANNOT-GENERATE)))
		     (warn "~A~%can no longer be generated~%~
                            Previously compiled code to do so calls ~A~%~
                            which will now generate an error" y old)
		     (setf (symbol-function old)
			   (symbol-function 'can-no-longer-generate))
		     (setf (get old :previous-definition) nil))
		    ((and (eq old :CANNOT-GENERATE) (eq new :CANNOT-GENERATE)))
		    ((eq old :cannot-generate))
		    (t (setf (symbol-function old) (symbol-function new))
		       (setf (get old :previous-definition)
			     (get new :previous-definition))))))))
  (when (or all recompile-rules)
    (rem-structure-property rel 'addmatchers)
    (rem-structure-property rel 'deletematchers)
    (let ((mnodes (matchnodes-< (listof rule#rule s.t. (relation-in-defn* rel rule)))) m a c)
      (loop for mn in mnodes
	    when (rel-in rel (matchwff mn)) do
	    (loop for pred in (matchpredecessors mn) do
		  (setf (matchsuccessors pred) (delete mn (matchsuccessors pred))))
	    (setf (matchpredecessors mn) nil)
	    when (or (setq c (matchconsistencies mn))
		     (setq a (matchautomations mn))
		     (setq m (matchmaintains mn)))
	    do (let ((new (ignore-errors
			    (cond ((eq (car (matchwff mn)) 'start*)
				   (detect* (matchvars mn) (cadr (matchwff mn))))
				  (t (detect+ (matchvars mn) (matchwff mn)))))))
		 (unless (eq new mn)
		   (atomic
		     (loop for r in c do
			 (-- matchconsistency mn r)
			 (cond (new (++ matchconsistency new r))
			       (t (warn "no longer able to trigger ~A" r))))
		     (loop for r in a do
			 (-- matchautomation mn r)
			 (cond (new (++ matchautomation new r))
			       (t (warn "no longer able to trigger ~A" r))))
		     (loop for r in m do
			 (-- matchmaintain mn r)
			 (cond (new (++ matchmaintain new r))
			       (t (warn "no longer able to trigger ~A" r))))))))))))

#+ignore
(let (props)
  (loop for relation#r s.t. true do
      (princ "." *debug-io*)
      (loop for p in (properties r)
	    when (and (symbolp p)
		      (eq (symbol-package p) *package*)
		      (not (member p props)))
	    do (princ "*" *debug-io*) (push p props)))
  props)
#+ignore
(|Add-ISUBREL+*|
   |Del-ISUBREL+*| TEST-MACRO BASEDATA TREEDATA
   TYPECONSTRAINT-CODE EXPANDED-DEFN BACKWARD-NAME
   REL-COMPARERELS FORWARD-NAME
   |Add-RELATION-IN-DEFN*| |Del-RELATION-IN-DEFN*|
   DELETEMATCHERS RELATIONIMPLEMENTATION
   RELATIONNAME RELATIONARITY UNIQUE-ID TESTER ADDER
   COMPARETUPLE CANONICALIZETUPLE ADDMATCHERS
   INHERITER)

; these are here because this calls decache-rel ...
(++ NOT-ALLOWED-TO-UPDATE (relationp 'generator-cache) t)
(++ NOT-ALLOWED-TO-UPDATE (relationp 'generator-cache) nil)

(++ compare-relation (dbo relation proper-name) 1 (dbo relation string-equal))
(decache-rel 'proper-name :all)

(defun can-no-longer-generate (&rest ignore)
  (declare (ignore ignore))
  (error "attempt to generate a pattern that can no longer be generated"))

(defun rel-in (rel wff)
  (try
    (catch :found
      (map-wff wff
	  :primitive-wff
	  #'(lambda (r &rest ignore) (declare (ignore ignore))
		    (when (eq rel r) (throw :found t)))))
    expanddescription nil))

(defmacro cache-generators (&rest descs-or-rels &aux (fname (gensym "F")) defrels rel)
  (let ((*fn-being-compiled* fname))
    (loop for d in descs-or-rels do
	  (cond ((listp d)
		 (try (macroexpand-1 `(generator ,@d))
		    'ap5-cannot-generate (warn "~a not cached -- non-generable." d)))
		((setf rel (relationp d))
		 (when (defined-p rel)
		   (let* ((args (loop for i below (arity* rel) collect (pack* 'x i)))
			  (desc (expanddescription (list args 's.t. (cons rel args)))))
		     (unless (compoundwffp (third desc))
		       (apply 'definedrelgenerator t (car desc) (caddr desc))
		       ; so as to compute it all first
		       (push rel defrels))))
		 (doxproduct (args (loop for p below (arity* rel) collect
				       (list 'input (gensym "X"))))
		   (when (member-if-not #'(lambda (x) (eq x 'input)) args)
			(let ((arglist (copy-list args)));; doxproduct shares tails
			  (try (macroexpand-1
				`(generator ,(remove 'input arglist) s.t.
					    ,(cons d arglist)))
				'ap5-cannot-generate nil)))))
		(t (warn "~A is neither a relation nor description - cache-generators"
			 d))))
    `(progn ,.(mapcar #'compile-code-for-desc (get fname 'uses-generator))
	    ,.(mapcan #'cache-definedrel defrels))))

(defun compile-starts1 (r &aux (arglist (loop for i below (arity* r)
					      collect (pack* 'x i))))
  (get-generator (expanddescription
		  `(,arglist s.t. (start (,r ,.arglist)))
		  :keepstarts t)
		 nil nil)
  (get-generator (expanddescription
		  `(,arglist s.t. (start (not (,r ,.arglist))))
		  :keepstarts t)
		 nil nil)
  `(progn ,(compile-code-for-desc
	    `(,arglist s.t. (start (,r ,.arglist))))
	  ,(compile-code-for-desc
	    `(,arglist s.t. (start (not (,r ,.arglist)))))))

(defmacro compile-starts (rname &aux (rel (relationp rname)))
  (if rel
    `(progn
       ,.(loop for r s.t. (derived-from* rel r) collect (compile-starts1 r))
       ,(compile-starts1 rel))
    (progn (warn "~A not a relation name" rname) nil)))

(defun cache-definedrel (rel &aux entry args)
  (setq args (loop for i below (arity* rel) collect (pack* 'x i)))
  (when (setq entry (gen-cache-i-i-o `(,args s.t. (subset-gen (,rel ,@args)))))
    (cons `(let ((f (gensym "F")))
	     (genadder (list ',args 's.t.
			     (list 'subset-gen
				   (cons (relationp ',(relationnamep rel))
					 ',args)))
		       (list (list 'initialstate f)
			     (cons 'answer ',(cdr (assoc 'answer entry)))
			     #+ignore  ;from experimental definedrelgenerator?
			     (list 'uses-gen f)))
	     (setf (get f 'uses-generator)
		   (list ,.(loop for g in (get (cadr (assoc 'initialstate entry))
					       'uses-generator)
				 collect
				 `(list ',(car g) 's.t.
					(map-copy-wff ',(vars&rels-to-names-wff (caddr g))))))))
	  (loop for desc in (get (cadr (assoc 'initialstate entry)) 'uses-generator)
		collect (compile-code-for-desc desc)))))

(defun typeconstraints (rel-or-name &aux rel argnames)
  ; version by donc taken from describerel
  (unless (setq rel (relationp rel-or-name)) (error "no such relation as ~A" rel-or-name))
  (setq argnames (any x s.t. (relationargnames  rel x) ifnone nil))
  (loop for pos below (arity* rel) collect
	(or (pop argnames)
	    (let ((types (listof ty s.t. (typeconstraint-stored rel pos ty))))
	      (cond ((null types) 'entity)
		    ((null (cdr types)) (or (relationnamep (car types)) (car types)))
		    (t (loop for x in types collect (or (relationnamep x) x))))))))

(defrelation equivalence-for-ignored-vars
    :derivation (coded ((x y) s.t.  (declare (ignore x y)) t)))

(++ equivalence-relation (relationp 'equivalence-for-ignored-vars))
(defun constant-supposed-to-be-ignored (x)
  (declare (ignore x)) 'supposed-to-be-ignored)
(++ canonicalizer (relationp 'equivalence-for-ignored-vars) (relationp 'eq)
    'constant-supposed-to-be-ignored)
(++ subrel (relationp 'equal) (relationp 'equivalence-for-ignored-vars))

(defrelation ignored-var :derivation (coded ((x) s.t. (progn x t)))
	     :equivs (equivalence-for-ignored-vars))

(++ relsize (relationp 'ignored-var) '(output) 1)
(simplegenerator '(ignored-var output) 'supposed-to-be-ignored)
(defvar supposed-to-be-ignored 'supposed-to-be-ignored)

; It would be nice if we could detect that this macro was being used
; in the wrong context, i.e., that the vars had not "just" been introduced.
(defmacro ignore-vars (varlist wff)
  (when (and varlist (symbolp varlist)) (setq varlist (list varlist)))
  `(and ,.(loop for v in varlist collect (list 'ignored-var v)) ,wff))


#+ignore
(defun typeconstraints (rel-or-name)  ;dga8III86  ;dga 19VI87
  "Returns a list of type constraints for all slots of the relation.
The type constraints for each slot is a joint constraint list (JCL),
which is a list where no type in the list is a supertype of any
other type in the list.  If the JCL for a slot has only one member,
just that member is returned for that slot."
  (let* ((rel (relationp rel-or-name))
	 (arity (and rel (theonly arity s.t. (relationarity rel arity)))))
    (cond (rel
	   (loop for pos below arity collect
		 (or (inside (listof tp s.t. (typeconstraint rel pos tp)))
		     ;;Neil will hate the following conjunct
		     #+ignore ; string-equal is not yet defined
		     (let
		       ((possiblerulename
			  (pack* "Typeconstraint-" (relationnamep rel) "-" pos)))
		       (fourth
			 (typeconstrainttriggerp
			   (any trigger s.t.
				(ruletrigger
				  (any Consistencyrule#rule s.t.
				       (and (relation-in-defn* rel rule)
					    (E (symbol)
					       (and (rulename rule symbol)
						    (string-equal
						      symbol
						      possiblerulename))))
				       ifnone NIL)
				  trigger)
				ifnone NIL))))
		     type-entity))) ;;  #!entity.type is not defined here, Dennis.
	  (t " not a relation"))))

(defun inside (L)  ;dga8III86
  "if L has only one member, that member, else L itself"
  ; not a macro so as to not reevaluate args
  (if (cdr L) L (car L)))

#+ignore
(defun repeat-abort-msg (abortdata)
  (cond ((member (car abortdata) '(rules-do-only-noops unfixed-consistency-violation))
	 (let ((delta (delta (car (consistency-cycles (fourth abortdata))))))
	   (report-consistency-violations (third abortdata))))
	(t "<not the right kind of abort>")))
(defun abort-delta (abortdata)
  (car (consistency-cycles (fourth abortdata))))

; *** function describe-type - 
; in what positions of what relations can it appear
; countspecs for those not inherited, ...

; *** something like get-attributes-of-type (called by describe-type)

; *** describerel - tell about count constraints?  


; Common lisp Documentation is not quite the same as help, since it's only for
; names (not general objects), it's optional (can't have two) and it has an
; extra argument.

#+ignore 
(defrelation doc
  :types (symbol symbol ((x) s.t. (or (string x) (equal x nil))))
  :equivs (:default :default equal)
  :size ((input input output) 1)
  :nontriggerable t :possibletoadd t :possibletodelete t
  :derivation (lisp-function documentation 2 1))
; why equal: (1) doc is case sensitive and (2) NIL is not the same as "NIL"
; I tried it as stored-in-place-single but it got upset when trying to
; do setf of the non-string ("none stored") when delete done before add

; changed this in order to not count NIL as a documentation string

(defrelation doc
  :arity 3 :types (symbol symbol string)
  :equivs (:default :default string=)
  :size ((input input output) 1)
  :nontriggerable t :possibletoadd t :possibletodelete t
  :derivation (lisp-predicate (lambda (x y z) (and z (string= z (documentation x y)))))
  :generator
  (simplegenerator
    (x y output)
    (when (and (symbolp x) (symbolp y))
      (let ((z (documentation x y)))
	(when z (list z))))))

#| these aren't ever linked up to the relation!!
(defun add-documentation (rel sym type string) (declare (ignore rel))
       (setf (documentation sym type) string))
(defun delete-documentation (rel sym type string) (declare (ignore rel))
       (when (equal string (documentation sym type))
	 (setf (documentation sym type) nil)))
|#

;;(loop for (relation#r h) s.t. (help r h) do (++ doc (relationnamep r) 'relation h))
;; eventually I should get rid of the help relation and replace all the documentation
; in earlier files - maybe collect it into one file so it can be maintained? ***

(defun do-documentation (rel doc
			 &aux #-lucid(relname (relationnamep rel)))
  #+lucid (declare (ignore rel doc))
  #-lucid
  (progn (setf (documentation relname 'relation) doc)
	 (loop for (n) s.t. (relationname rel n) unless (eq relname n) do
	       (setf (documentation n 'relation) nil)))
  #+lucid nil)

;; for function/relation analogy

(defun RBOUNDP (symbol) (?? relationname $ symbol))

(defun SYMBOL-RELATION (symbol)
  (any r s.t. (relationname r symbol)
       ifnone (error "~s has no relation binding" symbol)))

(defun RMAKUNBOUND (symbol) (-- relationname $ symbol))
