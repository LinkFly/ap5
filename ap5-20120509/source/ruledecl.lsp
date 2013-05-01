;;;-*- Mode:LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-
;
(in-package "AP5")

(eval-when (:compile-toplevel :load-toplevel :execute) (setq bootstrapping t))

; *** should these rule making functions first check that no such rule exists?

(Defun make-automation (name originaltrigger action &optional generator-p
		 &aux trigger matchnode params wff
		 (GenEffortWarning TriggerEffortWarning)
		 (GenSizeWarning TriggerSizeWarning))
  (setf trigger (expanddescription originaltrigger :keepstarts t)
	params (car trigger) wff (caddr trigger))
  (cond ((loop for a in params thereis (not (freein a wff)))
	 (error "not all of these vars are free in trigger ~S" (list params wff))))
  (cond ((and (eq wff 'true) (null params) generator-p)
	 (setq matchnode true-matchnode))
	(t (setq matchnode (Detect+ params wff))))
  (unless matchnode (warn "The trigger for ~A can apparently never be satisfied!" name))
  (case matchnode
    ((nil) (warn "~A is being ignored cause it could never trigger" name))
    ((t) (abort 'cannot-trigger
		"trigger is not appropriate for an automation - ~A" name))
    (otherwise
      (forany rule s.t. (and  (or (automationrule rule) (automationgenerator rule))
			      (ruletrigger rule originaltrigger)
			      (RuleName rule name))
	      (++ rulecode rule action)
	      (++ MatchAutomation matchnode rule)
	      (if generator-p
		  (progn (++ automationgenerator rule) (-- automationrule rule))
		  (progn (-- automationgenerator rule) (++ automationrule rule)))
	      ifnone
	      (atomic
		(let ((rule (make-dbobject)))
		  (if generator-p (++ automationgenerator rule) (++ automationrule rule))
		  (++ RuleName rule name)
		  (++ rulecode rule action)
		  (++ ruletrigger rule originaltrigger)
		  (++ MatchAutomation matchnode rule))))
       name)))

(Defun make-maintain (name originalwff repair
			 &aux matchnode params trigger rule wff
			 (GenEffortWarning TriggerEffortWarning)
			 (GenSizeWarning TriggerSizeWarning))
  (setf rule (make-dbobject)
	wff (macroexpand-to-wff originalwff)
	trigger
	(expanddescription
	  (if (eq (car (ilistp wff)) 'E)
	      (list (cadr wff) 's.t. (caddr wff))
	    (list nil 's.t. wff))
	  :keepstarts t)
	params (car trigger))
  (setf wff (caddr trigger))
  (cond ((loop for a in params thereis (not (freein a wff)))
	 (error "not all of ~S are free in ~S" params wff)))
  (setq matchnode (Detect+ params wff))
  (unless matchnode (warn "The trigger for ~A can apparently never be satisfied!" name))
  #+ignore ; again
  (try (setq matchnode (Detect+ params wff)) ; triggers now detect change in defn
       ap5-cannot-generate
       (abort 'cannot-trigger
	      "Cannot trigger consistency rule ~A~%due to inability to generate~%~A"
	      name tryvalue))
  (atomic (++ maintainrule rule)
	  (++ Rulename rule name)
	  (++ rulecode rule repair)
	  (++ ruletrigger rule originalwff)
	  (and matchnode (++ Matchmaintain matchnode rule)))
  rule)

; Declare a prohibition consistency rule named <name> which prohibits that
; there exist <params> s.t. <wff> by doing repair.  Enforcement-Level is
; (currently) one of {total, incremental, none}, indicating whether the
; constraint is to be checked at creation time (y,n,n) and whether it is
; to be compiled into a rule to notice incremental violations (y,y,n).
; None is useful for declaring intent when the enforcement is not possible,
; not necessary or not worth the effort.
(defun make-Consistency (name originalwff repair Enforcement-Level
			      &key reporter
			      &aux matchnode params trigger rule wff originaltrigger
			      (GenEffortWarning TriggerEffortWarning)
			      (GenSizeWarning TriggerSizeWarning))
     (unless (member Enforcement-Level '(:total :incremental :none))
       (abort 'bad-enforcement-level
	      "illegal constraint enforcement level - ~A" Enforcement-Level))
     (atomic
       (forany rule#old s.t. (and (consistencyrule old)
				  (Rulename old name)
				  (ruletrigger old originalwff)
				  (Constraint-Enforcement-Level old Enforcement-Level))
	       (++ rulecode old repair)
	       (when  reporter (++ inconsistency-reporter old reporter))
	       old
	       ifnone
	       (setf wff (macroexpand-to-wff originalwff)
		     trigger
		     (try (expanddescription
			    (setf originaltrigger
				  (cond ((eq (car (ilistp wff)) 'E)
					 (unless (eq-length wff 3)
					   (fail expanddescription "wrong length" wff))
					 (list (cadr wff) 's.t. (caddr wff)))
					(t (list nil 's.t. wff))))
			    :keepstarts t :dont-warn-for-false t)
			  expanddescription
			  (cond ((and (equal (car tryvalue) "not all vars are free in wff")
				      (eq (caddr tryvalue) 'false))
				 #+ignore(cond ((not (eql Enforcement-level :none))
					  #+ignore(warn name "can never trigger - "
						  "setting enforcement to :none")
					  #+ignore(setq enforcement-level :none)))
				 originaltrigger)
				(t (fail bad-rule-trigger originaltrigger tryvalue))))
		     params (car trigger) wff (caddr trigger))
	       
	       (try
		 (or (not (eql Enforcement-level :total))
		     (eval `(insist "check-consistency-condition"
				    not ,originalwff)))
		 ap5-cannot-generate
		 (abort 'cannot-trigger
		   "cannot compile code to test consistency condition ~A~
               ~%due to inability to generate~%~A"
		   name tryvalue))
	       (cond ((not (eql Enforcement-Level :none))
		      (setq matchnode
			    (cond ((temporalp wff) (detect+ params wff))
				  (t (Detect* params wff)))
			    #+ignore			; again
			    (try (cond ((temporalp wff) (detect+ params wff))
				       (t (Detect* params wff)))
				 ap5-cannot-generate
				 (abort 'cannot-trigger
					"Cannot trigger consistency rule ~A~
                                    ~%due to inability to generate~%~A"
					name tryvalue)))
		      (unless matchnode
			(warn "The trigger for ~A can apparently never be satisfied!"
			      name))))
	       (setq rule (make-dbobject))
	       (++ consistencyrule rule)
	       (++ Rulename rule name)
	       (++ rulecode rule repair)
	       (++ ruletrigger rule originalwff)
	       (++ Constraint-Enforcement-Level rule Enforcement-Level)
	       (and matchnode (++ MatchConsistency matchnode rule))
	       (and reporter (++ inconsistency-reporter rule reporter))
	       name)))

(defun make-ConsistencyChecker (name originaltrigger repair ; Enforcement-Level
				     &key reporter
				     &aux matchnode params trigger rule wff
				     (GenEffortWarning TriggerEffortWarning)
				     (GenSizeWarning TriggerSizeWarning))
     (atomic
       (forany rule#old s.t. (and (consistencychecker old)
				  (Rulename old name)
				  (ruletrigger old originaltrigger))
	       (++ rulecode old repair)
	       (when  reporter (++ inconsistency-reporter old reporter))
	       old
	       ifnone
	       (setq trigger (expanddescription originaltrigger
						:keepstarts t))
	       (setq params (car trigger) wff (caddr trigger))
	       (cond ((loop for a in params thereis (not (freein a wff)))
		      (error "not all of these vars are free in trigger ~S"
			     (list params wff))))
	       (cond ((and (eq wff 'true) (null params))
		      (setq matchnode true-matchnode))
		     (t (setq matchnode (detect+ params wff))))
	       (setq rule (make-dbobject))
	       (++ consistencychecker rule)
	       (++ Rulename rule name)
	       (++ rulecode rule repair)
	       (++ ruletrigger rule originaltrigger)
	       (++ MatchConsistency matchnode rule)
	       (when reporter (++ inconsistency-reporter rule reporter))
	       name)))

(Defun AlwaysRequire (name wff repair Enforcement-Level
			   &key reporter documentation &aux wff2)
  #+lucid (declare (ignore documentation))
  (setf wff2 (macroexpand-to-wff wff))
  ; don't macroexpand if it's a relname (?)
  (make-Consistency name
    (cond ((eq (car (ilistp wff2)) 'A)
	   (list 'E (cadr wff2) (list 'not (caddr wff2))))
	  ((eql wff2 'true) wff)
	  (t (list 'E nil (list 'not wff))))
    repair Enforcement-Level :reporter reporter)
  #-lucid(setf (documentation name 'rule) documentation)
  name)

(Defun NeverPermit (name wff repair Enforcement-Level &key reporter documentation)
  #+lucid (declare (ignore documentation))
  (make-Consistency name wff repair Enforcement-Level :reporter reporter)
  #-lucid(setf (documentation name 'rule) documentation)
  name)

(defun check-atomic-rulename (name macro)
  (unless (symbolp name)
    (error "~a is a macro; its arguments are not evaluated.~%The rule name must be a symbol.  ~
            ~s is unacceptable." macro name)))


(Defmacro NeverPermitted (name wff &environment env &rest keys
			  &key (repair 'ignored) (enforcement-level :incremental)
			       reporter documentation
			       &allow-other-keys  ;; only for compatibility with old calls
			       &aux rule fn1 fn2 (*in-anon-rel-context* t))
  (declare (ignore env #+lucid documentation))
  (check-atomic-rulename name 'neverpermitted)
  ;; handle old style uses -- detected by (first keys) not being a keyword
  (when (and (first keys) (not (keywordp (first keys))))
    (setf repair (first keys) enforcement-level (second keys)))
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     ,.(anon-rels-in-wff wff #+ignore env *empty-env*)
    ,(when (and (listp repair) (eq (car repair) 'lambda))
       `(defun ,(setf fn1 (pack* "REPAIR-FOR-" name)) ,@(cdr repair)))
    ,(when (and (listp reporter) (eq (car reporter) 'lambda))
       `(defun ,(setf fn2 (pack* "REPORTER-FOR-" name)) ,@(cdr reporter)))
    ,@(when (and (setf rule (any x s.t. (rulename x name) ifnone nil))
		 (?? ruletrigger rule wff))
	    (loop for desc in (find-cached-code-for-rule rule)
		  when (compoundwffp (third desc))
		  collect (compile-code-for-desc desc)))
    #+symbolics(global::record-source-file-name ',name 'rule)
    #+ti(system::record-source-file-name ',name 'rule)
    (make-Consistency ',name ',wff ',(or fn1 repair)
		      ',Enforcement-Level :reporter ',(or fn2 reporter))
    #-lucid(setf (documentation ',name 'rule) ',documentation)
    ',name))

(Defmacro AlwaysRequired
    (name wff &rest keys
   &key (repair 'ignored) (enforcement-level :incremental)
        reporter documentation
   &allow-other-keys  ;; only for compatibility with old calls
   &environment env)
  (declare (ignore env #+lucid documentation))
  (let (wff2 rule fn1 fn2 (*in-anon-rel-context* t))
    (check-atomic-rulename name 'neverpermitted)
    (setf wff2 (macroexpand-to-wff wff #+ignore env *empty-env*))
    ; don't macroexpand if it's a relname (?)
    (setf wff2 (cond ((eq (car (ilistp wff2)) 'A)
		      `(E ,(second wff2) (not ,(third wff2))))
		     ((eql wff2 'true) wff)
		     (t `(E () (not ,wff)))))

    ;; handle old style uses -- detected by (first keys) not being a keyword
    (when (and (first keys) (not (keywordp (first keys))))
      (setf repair (first keys) enforcement-level (second keys)))
    `(eval-when (:compile-toplevel :load-toplevel :execute)
       ,.(anon-rels-in-wff wff2 #+ignore env *empty-env*)
       ,(when (and (listp repair) (eq (car repair) 'lambda))
	  `(defun ,(setf fn1 (pack* "REPAIR-FOR-" name)) ,@(cdr repair)))
       ,(when (and (listp reporter) (eq (car reporter) 'lambda))
	  `(defun ,(setf fn2 (pack* "REPORTER-FOR-" name)) ,@(cdr reporter)))
       ,@(when (and (setf rule (any x s.t. (rulename x name) ifnone nil))
		    (?? ruletrigger rule wff))
	       (loop for desc in (find-cached-code-for-rule rule)
		     when (compoundwffp (third desc))
		     collect (compile-code-for-desc desc)))
       (make-Consistency ',name ',wff2 ',(or fn1 repair)
			 ',Enforcement-Level :reporter ',(or fn2 reporter))
       #-lucid(setf (documentation ',name 'rule) ',documentation)
       ',name)))

(Defmacro defconsistencychecker (name desc response &key reporter documentation
				      &environment env &aux rule fn rfn (*in-anon-rel-context* t)) 
   (declare (ignore env #+lucid documentation))
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     ,.(anon-rels-in-wff (third desc) #+ignore env *empty-env*)
    ,(when (and (listp response) (eq (car response) 'lambda))
       `(defun ,(setq fn (#+(or clisp ti) progn
			  #-(or clisp ti) copy-symbol
			  (pack* "RESPONSE-FOR-" name)))
	       ; copy so we don't think the next call is a noop
	       ,@(cdr response)))
    ,(when (and (listp reporter) (eq (car reporter) 'lambda))
       `(defun ,(setq rfn (#+(or clisp ti) progn
			   #-(or clisp ti) copy-symbol
			   (pack* "REPORTER-FOR-" name)))
	       ,@(cdr reporter)))
    ,@(when (and (setq rule (any x s.t. (rulename x name) ifnone nil))
		 (?? ruletrigger rule desc))
	    (loop for desc in (find-cached-code-for-rule rule)
		  when (compoundwffp (third desc))
		  collect (compile-code-for-desc desc)))
    #+symbolics(global::record-source-file-name ',name 'rule)
    #+ti(system::record-source-file-name ',name 'rule)
    (make-ConsistencyChecker ',name ',desc ',(or fn response)
			     :reporter ',(or rfn reporter))
    #-lucid(setf (documentation ',name 'rule) ',documentation)
    ',name))

(Defmacro defautomation (name desc response &key documentation &aux rule fn
			      (*in-anon-rel-context* t)
			      &environment env)
   (declare (ignore env #+lucid documentation))
  (check-atomic-rulename name 'defautomation)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     ,.(anon-rels-in-wff (third desc) #+ignore env *empty-env*)
    ,(when (and (consp response) (eq (car response) 'lambda))
       `(defun ,(setq fn (pack* "RESPONSE-FOR-" name)) ,@(cdr response)))
    ,@(when (and (setq rule (any x s.t. (rulename x name) ifnone nil))
		 (?? ruletrigger rule desc))
	    (loop for desc in (find-cached-code-for-rule rule)
		  when (compoundwffp (third desc))
		  collect (compile-code-for-desc desc)))
    #+symbolics(global::record-source-file-name ',name 'rule)
    #+ti(system::record-source-file-name ',name 'rule)
    (make-automation ',name ',desc ',(or fn response))
    #-lucid(setf (documentation ',name 'rule) ',documentation)
    ',name))

(Defmacro defautomationGenerator
   (name desc response &key documentation &aux rule fn
	 (*in-anon-rel-context* t) &environment env)
  (declare (ignore env #+lucid documentation))
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     ,.(anon-rels-in-wff (third desc) #+ignore env *empty-env*)
    ,(when (and (listp response) (eq (car response) 'lambda))
       `(defun ,(setq fn (#+(or clisp ti) progn
			  #-(or clisp ti) copy-symbol
			  (pack* "RESPONSE-FOR-" name)))
	       ; copy needed so we don't think the next call is a noop
	       ,@(cdr response)))
    ,@(when (and (setq rule (any x s.t. (rulename x name) ifnone nil))
		 (?? ruletrigger rule desc))
	    (loop for desc in (find-cached-code-for-rule rule)
		  when (compoundwffp (third desc))
		  collect (compile-code-for-desc desc)))
    #+symbolics(global::record-source-file-name ',name 'rule)
    #+ti(system::record-source-file-name ',name 'rule)
    (make-automation ',name ',desc ',(or fn response) t)
    #-lucid(setf (documentation ',name 'rule) ',documentation)
    ',name))

(Defun RuleCode (rule)
  (any x s.t. (RuleCode rule x)))

(Defun RuleName (rule)
  (any x s.t. (RuleName rule x)))

(Defun MatchConsistencies (matchnode)
  ;; should we be rebinding delta to NIL here?
  ; so we don't see the rules that are added in this transition?
  (loop for x s.t. (MatchConsistency matchnode x) collect x))

(Defun MatchAutomations (matchnode)
  (loop for x s.t. (MatchAutomation matchnode x) collect x))

(Defun Matchmaintains (matchnode)
  (loop for x s.t. (MatchMaintain matchnode x) collect x))

(++ DefinedRelName 'Automation
    '((name trigger action) s.t.
       (E (d) (and (AutomationRule d)
		   (RuleName d name)
		   (RuleTrigger d trigger)
		   (RuleCode d action)))))
(++ RelAdder (relationp 'automation) '(lambda (&rest ignore)
					(declare (ignore ignore))
					'automation-adder))

(defun automation-adder (ignore name trigger action)
  (declare (ignore ignore))
  (make-automation name trigger action))
; notice that a new trigger causes the rule to be replaced
; The user should understand that the trigger is only for his convenience and
; that changing it has no effect - the system uses the matchnode
; how about a rule that prevents changes to a trigger of an existing rule?

(++ RelDeleter (relationp 'automation)
    '(lambda (&rest ignore) (declare (ignore ignore)) 'automation-deleter))
(defun automation-deleter (ignore name ignore2 ignore3)
  (declare (ignore ignore ignore2 ignore3))
  (forany rule s.t. (RuleName rule name)
	  (-- automationrule rule)
	  :ifnone nil))


(++ DefinedRelName 'Prohibited
    '((name trigger repair enforcement) s.t.
       (E (d) (and (ConsistencyRule d)
		   (RuleName d name)
		   (Constraint-Enforcement-Level d enforcement)
		   (RuleTrigger d trigger)
		   (RuleCode d repair)))))

(++ RelAdder (relationp 'Prohibited)
    '(lambda (&rest ignore) (declare (ignore ignore)) 'consistency-adder))
(defun consistency-adder (ignore name trigger repair enforcement)
  (declare (ignore ignore))
  (neverpermit name trigger repair enforcement))

(++ RelDeleter (relationp 'Prohibited)
    '(lambda (&rest ignore) (declare (ignore ignore)) 'consistency-deleter))
(defun consistency-deleter (ignore name ignore2 ignore3 ignore4)
  (declare (ignore ignore ignore2 ignore3 ignore4))
  (forany rule s.t. (RuleName rule name)
	  (-- consistencyrule rule)
	  :ifnone nil))
