;;;-*- Mode:LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-

(in-package "AP5")

(eval-when (:compile-toplevel :load-toplevel :execute) (setq bootstrapping t))
; These used to be basetypes, but that looks like a mere pessimization
(++ treerelName 'ConsistencyRule 1)
(++ treerelName 'AutomationRule 1)
; Until I fix testwff to do con/disjunct ordering, put consistency first
; here - influences unique-id which determines order for testing type RULE.
(dbobject-order (relationp 'consistencyrule)(relationp 'automationrule))
(++ treerelName 'ConsistencyChecker 1)
(++ treerelName 'AutomationGenerator 1)
(++ treerelName 'MaintainRule 1)
(++ relsize (relationp 'ConsistencyRule) '(output) 2000)
(++ relsize (relationp 'AutomationRule) '(output) 50)
(++ relsize (relationp 'MaintainRule) '(output) 20)
(++ relsize (relationp 'ConsistencyChecker) '(output) 20)
(++ relsize (relationp 'AutomationGenerator) '(output) 20)

; used by trigger-automations
(defun automationgenerator-P (rule)
  (?? automationgenerator rule))
(defun ConsistencyChecker-P (rule)
  (?? ConsistencyChecker rule))

;; define the attributes of rules
(++ TreePropRelName 'RuleName)  

(++ TreePropRelName 'rulecode)
;(++ compare-relation (relationp 'rulecode) 1 (relationp 'equal))
; at end it's made functional-equivalent

(++ TreePropRelName 'ruletrigger)
(++ compare-relation (relationp 'ruletrigger) 1 (relationp 'equal))
; turns out to be real handy to get the rule from the trigger

; connection between rules and matchnodes
(++ TreePropRelName 'MatchConsistency)
(++ TreePropRelName 'MatchAutomation)
#+ignore  ; declared earlier (in relations) cause it was needed earlier
(++ TreePropRelName 'MatchMaintain)

; since matchadder is called during dodbupdates, avoid any db access
(declaim (special rel-matchconsistency rel-matchmaintain rel-matchautomation))
(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; eval-when for aclpc - maybe buffer break?
  (setf rel-matchconsistency (relationp 'matchconsistency))
  (setf rel-matchmaintain (relationp 'matchmaintain))
  (setf rel-matchautomation (relationp 'matchautomation)))

; these are slightly altered versions of the defaults
(Defun matchadder (rel &rest ignore &aux
			 (compare (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel x y)
     (put-structure-property x (cons y (get-structure-property x rel)) rel)
     (TreeAdder
       ,(cond ((some #'listp compare)
		`(loop for x in (list y x) as cmp in ',(reverse compare) collect
		       (cond ((listp cmp) (funcall (cadr cmp) x))
			     (t x))))
	       (t '(list y x)))
       (GETTreeData rel)
       ',(mapcar #'(lambda (x) (cond ((listp x) (car x)) (t x)))
		 (reverse compare)))
     (mark-active x (cond ((eq rel rel-matchconsistency) :consistency)
			  ((eq rel rel-matchmaintain) :maintain)
			  ((eq rel rel-matchautomation) :automation)
			  (t (error "strange type of rule"))))))

(Defun matchdeleter (rel &rest ignore &aux
			    (compare (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel x y)
      (put-structure-property x
	  (delete y (get-structure-property x rel)
		  :test ,(get-test-function (get-comparison rel 1 t))
		  :count 1)
	rel)
      (TreeDeleter
	,(cond ((some #'listp compare)
	        `(loop for x in (list y x) as cmp in ',(reverse compare) collect
		       (cond ((listp cmp) (funcall (cadr cmp) x))
			     (t x))))
	       (t '(list y x)))
	(GETTreeData rel)
	',(mapcar #'(lambda (x) (cond ((listp x) (car x)) (t x)))
		  (reverse compare)))
      (maybe-mark-inactive x
	(cond ((eq rel rel-matchconsistency) :consistency)
	      ((eq rel rel-matchmaintain) :maintain)
	      ((eq rel rel-matchautomation) :automation)
	      (t (error "strange type of rule"))))))

(++ reladder (relationp 'matchconsistency) 'matchadder)
(++ reladder (relationp 'matchautomation) 'matchadder)
(++ reladder (relationp 'matchmaintain) 'matchadder)
(++ reldeleter (relationp 'matchconsistency) 'matchdeleter)
(++ reldeleter (relationp 'matchautomation) 'matchdeleter)
(++ reldeleter (relationp 'matchmaintain) 'matchdeleter)

(++ PropRelName 'Constraint-Enforcement-Level)
; :total, :incremental, or :none
(++ proprelname 'inconsistency-reporter)
;(++ compare-relation (relationp 'inconsistency-reporter) 1 (relationp 'equal))
; at end it's made functional-equivalent

(++ RelSize (relationp 'rulecode) '(Input Output) 1)
(++ RelSize (relationp 'ruletrigger) '(Input Output) 1)
(++ RelSize (relationp 'Constraint-Enforcement-Level) '(Input Output) 1)
(++ RelSize (relationp 'inconsistency-reporter) '(Input Output) 1)
(++ RelSize (relationp 'MatchConsistency) '(Input Output) 1)
(++ RelSize (relationp 'MatchConsistency) '(Output Input) 1)
(++ RelSize (relationp 'MatchAutomation) '(Input Output) 1)
(++ RelSize (relationp 'MatchAutomation) '(Output Input) 1)
(++ RelSize (relationp 'MatchMaintain) '(Input Output) 1)
(++ RelSize (relationp 'MatchMaintain) '(Output Input) 1)
(++ RelSize (relationp 'RuleName) '(Input Output) 1)
(++ RelSize (relationp 'RuleName) '(Output Input) 1)
(++ relsize (relationp 'ruletrigger) '(output output) 2000)
(++ relsize (relationp 'rulecode) '(output output) 2000)
(++ relsize (relationp 'rulename) '(output output) 2000)
(++ relsize (relationp 'inconsistency-reporter) '(output output) 2000)
(++ relsize (relationp 'Constraint-Enforcement-Level) '(output output) 2000)


;(setq *default-atomic-abort-code* '((report-abort abortdata)))

(defun report-consistency-violations (triggers STREAM)
  (dolist (trigger triggers)
    (fresh-line STREAM)
    (forany reporter s.t. (inconsistency-reporter (first trigger) reporter)
	    (let (#-clisp *print-pretty*) ;; reporters can turn it on if they need it.
	      (format STREAM 
		      "~&Violation reported by ~s:~%" (first trigger))
	      (let ((*error-output* stream)) ;; stream should be a parmeter to
		;; the reporters!!
		(apply reporter (rest trigger))))
	    ifnone (default-inconsistency-report trigger STREAM)
	    (fresh-line STREAM))))

(defun default-inconsistency-report (trigger STREAM)
  (forany wff s.t. (ruletrigger (first trigger) wff)
	  ;; list#wff broke in bootstrapping -- incompatible equivs
	  (when (listp wff)
		(format STREAM 
			"The following situation is prohibited by ~s:~%"
			(first trigger))
		(write
		 (cond ((or (eq 'e (car wff)) (eq 'exists (car wff)))
                        ;;; could a macro appear? YES!
			(subst-free-in-wff (pairlis
					    (mapcar 'variablename (second wff))
					    (rest trigger))
					   (third wff)))
		       (t wff))
		 :stream STREAM :pretty t :level 8 :length 10))
	  ifnone nil))


(++ DefinedRelName 'Rule
    '((x) s.t. (or (ConsistencyRule x) (AutomationRule x) (MaintainRule x)
		   (ConsistencyChecker x) (AutomationGenerator x))))


(++ reldeleter (relationp 'rule)
    '(lambda (&rest ignore) (declare (ignore ignore)) 'deleterule))
(defun deleterule (ignore rule)
  (declare (ignore ignore))
  (-- consistencyrule rule)
  (-- automationrule rule)
  (-- maintainrule rule)
  (-- ConsistencyChecker rule)
  (-- AutomationGenerator rule))

(++ Printer (relationp 'Rule) 'PrintRule)
(Defun PrintRule (d)
  (PrintDBO 'Rule (theonly name s.t. (RuleName d name))))
(++ Reader (relationp 'Rule) 'ReadRule)
(Defun ReadRule (&rest x)
  (theonly rule s.t. (RuleName rule (cadr x))))

;(++ SubType (RelationP 'Rule) (RelationP 'DBObject))
; will be under rule-or-relation
(++ SubType (relationp 'ConsistencyRule) (relationp 'Rule))
(++ SubType (relationp 'AutomationRule) (relationp 'Rule))
(++ SubType (relationp 'MaintainRule) (relationp 'Rule))
(++ SubType (relationp 'ConsistencyChecker) (relationp 'Rule))
(++ SubType (relationp 'AutomationGenerator) (relationp 'Rule))
(++ Printer (relationp 'Rule) 'PrintRule)

(++ baserelname 'No-Trigger 1)
(++ compare-relation (relationp 'no-trigger) 0 (relationp 'equal))

(defun no-trigger (vars wff &aux (keepstarts t) ans simpwff)
  (declare (special keepstarts))
  (setq ans (?? no-trigger (setq simpwff (list (vars-to-names vars) 's.t.
					       (vars-to-names-wff (simplify2 wff))))))
  (when ans (warn "~&No matchnode is being built to detect~%~A"
		  simpwff))
  ans)

(progn
(tuple-comparison (relationp 'relationimplementation))
(tuple-comparison (relationp 'relationarity))
(tuple-comparison (relationp 'relationname))
)
; bootstrapping problem - have to cache comparetuple to avoid infinite recursion
(atomic (++ treerelname 'known-match-predecessor 4)
	reveal
	(++ compare-relation (dbo relation known-match-predecessor) 1 (dbo relation equal)))

;; KMP(definedrel defn defrelmatchnode pred-matchnode)

(++ reladder (dbo relation known-match-predecessor) 'addknown-match-predecessor)
(++ reldeleter (dbo relation known-match-predecessor) 'delknown-match-predecessor)

(Defun addknown-match-predecessor (rel &rest ignore &aux
			 (compare (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel &rest tuple)
     (when (matchnode-p (fourth tuple) #+ignore newnode) ; might be nil (t?)
       (push (fourth tuple) (matchpredecessors (third tuple)))
       (push (third tuple) (matchsuccessors (fourth tuple)))
       (loop for x in (matchactive (third tuple)) do (mark-active (fourth tuple) x)))
      (TreeAdder
	,(cond ((some #'listp compare)
		`(list ,.(loop for cmp in compare collect
			       (cond ((listp cmp) (list (cadr cmp) '(pop tuple)))
				     (t '(pop tuple))))))
	       (t 'tuple))
	(GETTreeData rel)
	,(constant-equality-sig
	  (mapcar #'(lambda (x)(if (listp x) (car x) x))
		  compare)))))

(defun assert-known-matchpred (rel def oldnode newnode)
  (++ known-match-predecessor rel def oldnode newnode))

(Defun delknown-match-predecessor (rel &rest ignore &aux
			    (compare (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel &rest tuple)
     (when (matchnode-p (fourth tuple) #+ignore newnode) ; might be nil (t?)
       (setf (matchpredecessors (third tuple))
	     (delete (fourth tuple) (matchpredecessors (third tuple))))
       (setf (matchsuccessors (fourth tuple))
	     (delete (third tuple) (matchsuccessors (fourth tuple))))
       (loop for x in (matchactive (third tuple)) do
	     (maybe-mark-inactive (fourth tuple) x)))
      (TreeDeleter
	,(cond ((some #'listp compare)
		`(list ,.(loop for cmp in compare collect
			       (cond ((listp cmp) (list (cadr cmp) '(pop tuple)))
				     (t '(pop tuple))))))
	       (t 'tuple))
	(GETTreeData rel)
	,(constant-equality-sig
	   (mapcar #'(lambda (x)(if (listp x) (car x) x))
		  compare)))))

;; from (former source file) fequiv
#|
It is often desirable to store FUNCTIONS in the database.  
(Particularly) when the function is just a function object, 
as created by #'(lambda ...), there is no satisfactory
means to test EQUIVALENCE of functions.  While it MAY be acceptable
for two functionally equivalent functions to appear non-equivalent
to the database, it is usually undesirable. In the past, we have seen,
and written, code that goes out of its way to generate and
intern a "canonical" name for such functions so that the database could
use EQ on symbols as a comparison.

Here is an alternative facility.  It is based on the ability to
CHARACTERIZE a function's functionality by some lisp value
(typically, though not necessarily, a symbol or list of symbols),
where EQUAL serves as a suitable equivalence test over the characterizations.
The facility has two parts:

1) a new equivalence relation,  SYMBOL-FUNCTIONAL-EQUIVALENTP,
which holds for two symbols iff they are EQ or they have
EQUAL values for their :FUNCTIONAL-CHARACTERIZATION property
(and both have a value stored for the property.)  This is the
equivalence relation to use for FUNCTION valued slots in the database.
Obviously this does not meet the technical requirements for being
an equivalence relation in AP5, since it is possible to change
property values of symbols.  BUT, if the facility is used solely
through the advertised function below, it will meet the requirements.
Note that symbols are NOT claimed to be equivalent even if they are
both (currently) FBOUNDP to EQ values!


2) a function FUNCTIONAL-EQUIVALENCE-TESTABLE [funarg
equivalence-property &optional preferred-name]
The FUNARG should evaluate to something of which FUNCTIONP is true.
The EQUIVALENCE-PROPERTY is the characterization described above.
A new symbol is generated (interned in an isolated package).  The new
symbol is globally fbound to the funarg, and its :FUNCTIONAL-CHARACTERIZATION
property is set to EQUIVALENCE-PROPERTY.  The symbol is returned.

The optional name (a string) will be used (as a prefix of) the name for
the generated symbol.  If a symbol with the preferred name already exists,
AND is already globally fbound to a funarg, AND has its 
:FUNCTIONAL-CHARACTERIZATION property EQUAL to EQUIVALENCE-PROPERTY,
that symbol is the value returned.
|#

(declaim (special *no-fc*))
(setq *no-fc* (list "not characterized"))
; (defparameter *no-fc* '#,(list "not characterized"))
; I know this is "semantically" a defconstant, but compilers do weird things
; with that - in particular, the build process tries to load the bin file on
; top of the lisp file and that gives redefinition warnings/queries.
; (In one case below it's important to redefine!)
; Now I've even given up on defparameter ...

; In order to get this in before adding tuples of relations that use it,
; we'll define the relation as a codedrel rather than lisp-pred-equiv-rel.
(defun symbol-functional-equivalentp (s1 s2 &aux s1pval)
  (or (equal s1 s2)
      (and (symbolp s2) (symbolp s1)
	   (not (eq *no-fc* (setq s1pval
				  (get s1 :functional-characterization *no-fc*))))
	   (equal s1pval (get s2 :functional-characterization *no-fc*)))))

(declaim (special *cfn-package*))
#-clisp
(setq *cfn-package* ; formerly defparameter
      (or (find-package "Canonical Functions")
	  (make-package "Canonical Functions" :use nil)))
#+clisp ; compiler likes to eval that make-package 
(eval '(setq *cfn-package* ; formerly defparameter
	     (or (find-package "Canonical Functions")
		 (make-package "Canonical Functions" :use nil))))
; see comment above about defconstant
(declaim (special *cfn-table*))
(setq *cfn-table* (make-hash-table :test #'equal :size 255)) ; formerly defparameter
;;; hash table from characterizations to "canonical" symbols

(defun make-canonical-function-name
       (sym &aux pval new-sym-name existing-sym new-sym)
  (unless (and (symbolp sym)
	       (not (eq *no-fc* (setq pval (get sym :functional-characterization
						*no-fc*)))))
    (return-from make-canonical-function-name sym))
  
  (when (setq existing-sym (gethash pval *cfn-table*))
    (return-from make-canonical-function-name existing-sym))
  ;; that was the normal exit
  
  ;; no canonical symbol for PVAL is yet interned
  (setq new-sym-name (let ((*package* (find-package "LISP")))
		       (write-to-string pval :readably t)))
  ;; Neil thinks the f.c. will be a more understandable name than sym
  ;; However, note that FUNCTIONAL-EQUIVALENCE-TESTABLE makes the
  ;; created function canonical
  (setq new-sym
	(cond ((find-symbol new-sym-name *cfn-package*)
	       ;;; can't make the symbol have this name, because that
	       ;;; symbol already exists with a different characterization
	       (gentemp new-sym-name *cfn-package*))
	      (t (intern new-sym-name *cfn-package*))))
  (setf (gethash pval *cfn-table*) new-sym)
  new-sym)

#+ignore
(lisp-predicate-equivalence-relation
  symbol-functional-equivalentp EQUAL EQUAL make-canonical-function-name)

(++ codedrelname 'SYMBOL-FUNCTIONAL-EQUIVALENTP
    '((x y) s.t. (SYMBOL-FUNCTIONAL-EQUIVALENTP X Y)))

(++ EQUIVALENCE-RELATION (DBO RELATION SYMBOL-FUNCTIONAL-EQUIVALENTP))

(++ CANONICALIZER (DBO RELATION SYMBOL-FUNCTIONAL-EQUIVALENTP)
    (DBO RELATION EQUAL) 'MAKE-CANONICAL-FUNCTION-NAME)

(++ SUBtype (DBO RELATION EQUAL) (DBO RELATION SYMBOL-FUNCTIONAL-EQUIVALENTP))
; subrel will not yet cause the rule to be made

; see comment above about defconstant
(declaim (special *rel-symbol-functional-equivalentp*))
(setq *rel-symbol-functional-equivalentp* ; formerly defparameter
	     (relationp 'symbol-functional-equivalentp))

(defun FUNCTIONAL-EQUIVALENCE-TESTABLE
	  (funarg equivalence-property-value &optional preferred-name)
  (unless (or (symbolp funarg) (functionp funarg))
    (warn "~a does not appear to be a legitimate functional value" funarg))
  (when (symbolp funarg) (setq funarg (symbol-function funarg)))
  (let* ((sym (and preferred-name (find-symbol (string preferred-name)
						 *cfn-package*)))
	 (sym-pval (get sym :functional-characterization *no-fc*)))
    (cond ((and (null sym) preferred-name)
	   (setq sym (intern (string preferred-name) *cfn-package*)))
	  ((or (null sym)
	       (eq sym-pval *no-fc*) ;; should never happen
	       (not  (equal sym-pval equivalence-property-value)))
	   ;;; must gen a new symbol
	   (setq sym (gentemp (cond (preferred-name (string preferred-name))
			       (t "F"))
			 *cfn-package*))))
    (unless (fboundp sym) (setf (symbol-function sym) funarg))
    (setf (get sym :functional-characterization) equivalence-property-value)
    (unless (gethash equivalence-property-value *cfn-table*)
      ;; make sym the canonical representative
      (setf (gethash equivalence-property-value *cfn-table*) sym))
    sym))

(++ compare-relation (relationp 'rulecode) 1
    *rel-symbol-functional-equivalentp*)
(++ compare-relation (relationp 'inconsistency-reporter) 1
    *rel-symbol-functional-equivalentp*)

; ---------------- special matching for basetypes ----------------


(declaim (special *add-class-node* *add-subrel-node*
		    *del-class-node* *del-subrel-node*))

; Figure out which nodes to activate and activate them.  Return nil so the
; normal activation mechanism does NOT activate them.  We use the successor
; relation here to check that the node really expects activation of this sort.
(defun trigger-basetypes-on-add-classification (object class)
  (declare (special |MIQueue |))
  (loop for sup s.t. (subrel class sup) do
	(loop for node in (get-structure-property sup 'addmatchers)
	      when (member class-to-activate (matchactive node))
	      ; probably almost all will satisfy this test
	      when (member *add-class-node* (matchpredecessors node))
	      unless (previously (testrel sup object))
	      ; this seems the most expensive test - assume only one such node
	      do
	      (if (eq class-to-activate :maintain) ; different protocol
		  (push (cons node (list object)) |MIQueue |)
		(matchactivate node (list object) class-to-activate)))))


(let ((desc (expanddescription '((x y) s.t. (classification x y)))))
  (let ((add-class (detectinput (car desc) (third desc))))
    (setq *add-class-node*
	  (make-matchnode :matchwff '(funcall *add-class-node*)
			  :matchrels (list (relationp 'classification)
					   (relationp 'subrel-stored))
			  ; need no compare since there are no "outputs"
			  :matchcode 'trigger-basetypes-on-add-classification
			  ;; unnecessary - it'll be maintained by its successors
			  ;:matchactive '(:maintain :consistency :automation)
			  :matchpredecessors (list add-class)))
    (setf (matchactive add-class) '(:maintain :consistency :automation))
    (push *add-class-node* (matchsuccessors add-class))
    *add-class-node*))

(defun trigger-basetypes-on-del-classification (object class)
  (declare (special |MIQueue |))
  (loop for sup s.t. (subrel class sup) do
	(loop for node in (get-structure-property sup 'deletematchers)
	      when (member class-to-activate (matchactive node))
	      when (member *del-class-node* (matchpredecessors node))
	      unless (testrel sup object)
	      do
	      (if (eq class-to-activate :maintain)
		  (push (cons node (list object)) |MIQueue |)
		(matchactivate node (list object) class-to-activate)))))

(let ((desc (expanddescription '((x y) s.t. (not (classification x y))))))
  (let ((del-class (detectinput (car desc) (third desc))))
    (setq *del-class-node*
	  (make-matchnode :matchwff '(funcall *del-class-node*)
			  :matchrels (list (relationp 'classification)
					   (relationp 'subrel-stored))
			  ; need no compare since there are no "outputs"
			  :matchcode 'trigger-basetypes-on-del-classification
			  ;:matchactive '(:maintain :consistency :automation)
			  :matchpredecessors (list del-class)))
    (setf (matchactive del-class) '(:maintain :consistency :automation))
    (push *del-class-node* (matchsuccessors del-class))
    *del-class-node*))

(defun trigger-basetypes-on-add-subrel (sub super)
  (declare (special |MIQueue |))
  (when (?? and (basetype sub) (basetype super))
    (loop for node in (get-structure-property super 'addmatchers)
	  when (member class-to-activate (matchactive node))
	  when (member *add-subrel-node* (matchpredecessors node)) do
	  (loop for obj s.t. (funcall sub obj)
		unless (previously (testrel super obj)) do
		(if (eq class-to-activate :maintain)
		    (push (cons node (list obj)) |MIQueue |)
		  (matchactivate node (list obj) class-to-activate))))))

(let ((desc (expanddescription '((x y) s.t. (subrel-stored x y)))))
  (let ((add-subrel (detectinput (car desc) (third desc))))
    (setq *add-subrel-node*
	  (make-matchnode :matchwff '(funcall *add-subrel-node*)
			  :matchrels (list (relationp 'classification)
					   (relationp 'subrel-stored))
			  ; need no compare since there are no "outputs"
			  :matchcode 'trigger-basetypes-on-add-subrel
			  ;:matchactive '(:maintain :consistency :automation)
			  :matchpredecessors (list add-subrel)))
    (setf (matchactive add-subrel) '(:maintain :consistency :automation))
    (push *add-subrel-node* (matchsuccessors add-subrel))
    *add-subrel-node*))

(defun trigger-basetypes-on-del-subrel (sub super)
  (declare (special |MIQueue |))
  (when (?? and (basetype sub) (basetype super))
    (loop for node in (get-structure-property super 'deletematchers)
	  when (member class-to-activate (matchactive node))
	  when (member *del-subrel-node* (matchpredecessors node)) do
	  (loop for obj s.t. (funcall sub obj)
		unless (testrel super obj) do
		(if (eq class-to-activate :maintain)
		    (push (cons node (list obj)) |MIQueue |)
		  (matchactivate node (list obj) class-to-activate))))))

(let ((desc (expanddescription '((x y) s.t. (not (subrel-stored x y))))))
  (let ((del-subrel (detectinput (car desc) (third desc))))
    (setq *del-subrel-node*
	  (make-matchnode :matchwff '(funcall *del-subrel-node*)
			  :matchrels (list (relationp 'classification)
					   (relationp 'subrel-stored))
			  ; need no compare since there are no "outputs"
			  :matchcode 'trigger-basetypes-on-del-subrel
			  ;:matchactive '(:maintain :consistency :automation)
			  :matchpredecessors (list del-subrel)))
    (setf (matchactive del-subrel) '(:maintain :consistency :automation))
    (push *del-subrel-node* (matchsuccessors del-subrel))
    *del-subrel-node*))

(defvar *var-x* (make-variable :varname 'x :varcompare (dbo type eql)))
(defun add-matchnodes-for-basetype (b def &aux desc addnode delnode)
  (setq desc `((,*var-x*) s.t. (,b ,*var-x*)))
  (unless (get-structure-property b 'addmatchers)
    (setf addnode (make-matchnode :matchvars (car desc)
				  :matchwff (list 'start (caddr desc))
				  :matchcode 'ident
				  :matchrels (list b (relationp 'classification)
						   (relationp 'subrel-stored))
				  :matchcompare '(eql)))
    (add-structure-property b addnode 'addmatchers))
  (loop for n in (get-structure-property b 'addmatchers) do
	;; could there be more than one?
	;; if so, better connect them all - have to trigger all their successors
	(loop for pred s.t. (known-match-predecessor b def n pred)
	      unless (or (eql pred *add-class-node*) (eql pred *add-subrel-node*))
	      do (-- known-match-predecessor b def n pred))
	(++ known-match-predecessor b def n *add-class-node*)
	(++ known-match-predecessor b def n *add-subrel-node*))
  (unless (get-structure-property b 'deletematchers)
    (setq delnode
	  (make-matchnode :matchvars (car desc)
			  :matchwff (list 'start (list 'not (caddr desc)))
			  :matchcode 'ident
			  :matchrels (list b (relationp 'classification)
					   (relationp 'subrel-stored))
			  :matchcompare '(eql)))
    (add-structure-property b delnode 'deletematchers))
  (loop for n in (get-structure-property b 'deletematchers) do
	(loop for pred s.t. (known-match-predecessor b def n pred)
	      unless (or (eql pred *del-class-node*) (eql pred *del-subrel-node*))
	      do (-- known-match-predecessor b def n pred))
	(++ known-match-predecessor b def n *del-class-node*)
	(++ known-match-predecessor b def n *del-subrel-node*)))

(defun basetypename-adder (ignore name &aux def rel) (declare (ignore ignore))
  (cond ((?? BaseTypeName name)
	 (Insist "supposed to add it" BaseTypeName name))
	(t (atomic
	     (add-imparityname (setq rel (make-dbobject)) 'Defined 1 name)
	     (++ WffDefn rel (setq def (BaseTypeDef name)))
	     ; (++ SubType rel (relationp 'DBObject))
	     ; this cannot be done here because the arity isn't known yet
	     ; instead it will be done by a rule
	     (++ reladder rel 'basetype-adder)
	     (++ reldeleter rel 'basetype-deleter)
	     (add-matchnodes-for-basetype rel def)))))


;; In order to derive a relation from a defined relation, there must be a matchnode
; for the defined rel which is active during maintain/indirect computations.
; The defined rel is treated like a derived rel (which it is, after all).
;; These have to be consistencies since the node may be required for the next update.
;; We have to connect these nodes to a permanent maintain node so if some other
; node is connected to them and then disconnected, they won't go away!

(declaim (special *permanent-maintain-matchnode*))
(unless (boundp '*permanent-maintain-matchnode*)
  (setq *permanent-maintain-matchnode*
	(make-matchnode :matchwff '(funcall *permanent-maintain-matchnode*)
			:matchcode 'ignored :matchactive '(:maintain))))

; This relation relates defined rels to their defns if they 
; have a ++ matchnode activated during maintain/indirect with 
; *permanent-maintain-matchnode* as a successor.
; Of course, this node will have a known-match-predecessor...
;
(++ baserelname 'definedrel-with-known++maintain 2)
(++ compare-relation (dbo relation definedrel-with-known++maintain)
    1 (dbo relation equal))
(++ reladder (dbo relation definedrel-with-known++maintain)
    'add-definedrel-with-known++maintain)
(defun add-definedrel-with-known++maintain (rel &rest ignore)
  (declare (ignore rel ignore))
  `(lambda (rel rel2 defn)
     (add-maintain-node rel2 defn t)
     (PutBaseData rel (CONS (list rel2 defn) (GETBaseData rel)))))
(++ reldeleter (dbo relation definedrel-with-known++maintain)
    'del-definedrel-with-known++maintain)
(defun del-definedrel-with-known++maintain (rel &rest ignore)
  (declare (ignore ignore))
  `(lambda (rel &rest tuple)
     (del-maintain-node (car tuple) t)
     (let (memb) ; symbolics compiler bug
       (cond ((setq memb (car (fmemb3 tuple (getbasedata rel) ,rel)))
	      (putbasedata rel (delete memb (getbasedata rel))))))))
(++ baserelname 'definedrel-with-known--maintain 2)
(++ compare-relation (dbo relation definedrel-with-known--maintain)
    1 (dbo relation equal))
(++ reladder (dbo relation definedrel-with-known--maintain)
    'add-definedrel-with-known--maintain)
(defun add-definedrel-with-known--maintain (rel &rest ignore)
  (declare (ignore ignore rel))
  `(lambda (rel rel2 defn)
     (add-maintain-node rel2 defn nil)
     (PutBaseData rel (CONS (list rel2 defn) (GETBaseData rel)))))
(++ reldeleter (dbo relation definedrel-with-known--maintain)
    'del-definedrel-with-known--maintain)


(defun del-definedrel-with-known--maintain (rel &rest ignore)
  (declare (ignore ignore))
  `(lambda (rel &rest tuple)
     (del-maintain-node (car tuple) nil)
     (let (memb) ; symbolics compiler bug
       (cond ((setq memb (car (fmemb3 tuple (getbasedata rel) ,rel)))
	      (putbasedata rel (delete memb (getbasedata rel))))))))

(defun add-maintain-node (rel defn addp &aux node)
  (setq node (get-structure-property rel (if addp 'add-matchnode 'del-matchnode)))
  ; supposed to have been left there by a consistency rule
  (unless (eq (car node) defn)
    (error "cannot find the matchnode for ~A" rel))
  (setq node (cdr node))
  ;; this was not just optimization but also needed to avoid reading the DB
  ;; during primitive update code
  #+ignore (
  (setq desc (loop for i below (arity* rel) collect (gensym "V")))
  (setq desc (expanddescription
	       (list desc 's.t.
		     (cond (addp `(notinline (,rel ,.desc)))
			   (t `(not (notinline (,rel ,.desc))))))))
  (setq node (detectinput (car desc) (caddr desc)))
  )
  (mark-active node :maintain)
  (push node (matchpredecessors *permanent-maintain-matchnode*))
  (push *permanent-maintain-matchnode* (matchsuccessors node)))

(defun del-maintain-node (rel addp)
  (loop for s in (get-structure-property rel
		     (cond (addp 'addmatchers) (t 'deletematchers)))
	when (member *permanent-maintain-matchnode* (matchsuccessors s)) do
	(setf (matchsuccessors s)
	      (delete *permanent-maintain-matchnode* (matchsuccessors s))
	      (matchpredecessors *permanent-maintain-matchnode*)
	      (delete s (matchpredecessors *permanent-maintain-matchnode*)))
	(maybe-mark-inactive s :maintain)))
