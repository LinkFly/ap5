;-*- Mode:LISP; Package:AP5; Base:10.; Syntax:Common-Lisp -*-
;
; Generators

(in-package "AP5")

#+ignore
(defun deferredconstantp (x)
    ; have to recognize the case where it's been expanded.
    (or (eq (car (ilistp x)) 'deferredconstant)
	(and (eq (car (ilistp x)) 'si:displaced)
	     (eq (caadr x) 'deferredconstant))))

(defun UnEval(rel-exp)
  ; try to produce something that, when loaded into another environment,
  ; will give back the same relation
  (cond ;((deferredconstantp rel-exp) rel-exp)
	((relationnamep rel-exp)
	 #|
	  formerly (kwote (relationp rel-exp))
	  before that (list 'deferredconstant
	                 (list 'relationp (kwote (relationnamep rel-exp))))|#
	 #+ignore`(memo (relationp ',(relationnamep rel-exp)))
	 `(theap5relation ,(relationnamep rel-exp)))
	(t (error "unable to compile a reference to ~s" rel-exp))))

#+ignore(defun handle-variable-relation (op rel-exp tuple &optional evalflg &aux rel code)
    ; what to do (at run time) about (+/-/? (expression) . args)
    ;should be equivalent to
    ;(eval (TranslateDBOp (list op (cons (eval Rel-Exp) Tuple))))
    (cond
     ((not (setq rel (relationp (cond (evalflg
				       (eval rel-exp))
				      (t rel-exp)))))
      (error "~s is not a relation" rel-exp))
     ((not (= (length tuple) (arity* rel)))
      (error "wrong arity for ~s" (cons op (cons rel-exp tuple))))
     ((not (setq code (get-structure-property rel op)))
      ; I tried once to cache code on the basis of
      ; {operation, implementation, arity}.  It doesn't work.
      ; The problem is that there are implementations that compile
      ; the same operation of the same arity differently for
      ; different relations, e.g. defined (which depends on the defn)
      ; this will cache code for future.
      (put-structure-property
       rel
       (setq code (translatedbop (list op
				       (cons rel
					     (loop for ignore in tuple
						   collect (gensym "A"))))))
       op)
      (or code (error "no translation for ~S" (cons op (cons rel-exp tuple))))))
    (cond (evalflg
	   (setq tuple (loop for x in tuple
			     collect (eval x)))))
    (cond ((eq op 'test)
	   (not (not (lexpr-funcall code rel tuple))))
	  (t (lexpr-funcall code rel tuple))))


(defstruct (subsetgen ;:named
	     :copier
	     (:conc-name nil))
  effort sinput soutput size sgen wff genprops)

(Defun IfEffort (x) (and x (Effort x)))

; loop extension stuff now in sys-depend

; Here's the zetalisp version of s.t.
;  alter the data used by the loop macro
#+ignore ;; #+(or symbolics ti allegro)
(progn
 (pushnew '(s.t. loop-for-s.t.) loop-for-keyword-alist :test #'equal)

 (defun loop-for-s.t. (originalvars originalbody datatypes
		      &aux outputs pulser)
    (when (or (and (symbolp wff) (not (member wff '(true false))))
	      (descriptionp wff t))
	   (setf wff (cons wff (copy-list variables))))
    (multiple-value-bind (varnames evlvars initializer temporal)
	(analyze-desc originalvars originalbody)
    (loop-make-iteration-variable  varnames nil datatypes)
    (loop-make-iteration-variable '|Exhausted | nil nil)
    (loop-make-iteration-variable '|GenFun | `(let ,evlvars ,initializer) nil)
    ; do init without IV's bound, e.g. *package* might affect the computation
    (setq outputs (cons '|Exhausted | varnames))
    (setq pulser `(multiple-value-setq ,outputs (do-pulse |GenFun |)))
    ; eachtime {pretest steps posttest pseudo} firsttime {pretest ...}
    (list nil nil pulser nil
	  (cond (temporal #+ignore (temporalp (caddr body))
		 `(check2states
		    (mmemo (generate ,.(rels-to-names
					 (list originalvars 's.t.
					       originalbody)))))))
	  ; not actually used as a test
	  nil pulser nil)))
)
#+ignore ;; #+lucid
(progn
 (loop::define-loop-method (tuple tuples) tuples-path (of))

 (defun tuples-path (path-name variables data-types prep-phrases inclusive?
			      allowed-preps data &aux outputs pulser
			      (wff (cadar prep-phrases)))
  (declare (ignore path-name allowed-preps data data-types))
  (when inclusive? (error "inclusive syntax not supported by tuples keyword"))
  (when (or (and (symbolp wff) (not (member wff '(true false))))
		 (descriptionp wff t))
	   (setf wff (cons wff (copy-list variables))))
  (multiple-value-bind (varnames evlvars initializer temporal)
	(analyze-desc variables wff)
    ; do init without IV's bound, e.g. *package* might affect the computation
    (setq outputs (cons '|Exhausted | varnames))
    (setq pulser `(multiple-value-setq ,outputs (do-pulse |GenFun |)))
    ; bindings prolog eachtime:{pretest steps posttest pseudo} firsttime:{pretest ...}
    (list (list* '(|Exhausted | nil #+ignore (member t nil))
		 `(|GenFun | (let ,evlvars ,initializer)
				  #+ignore function t)
		 (loop for v in varnames ; as d in data-types
			    ;; data types cannot be useful, because this
                            ;; xlation initializes all the vars to NIL
			    collect (list v nil #+ignore d)))
	  (list '|Exhausted |) nil nil pulser nil
	  (cond (temporal
		 `(check2states
		    (mmemo (generate ,.(rels-to-names
					 (list variables 's.t.
					       (cadar prep-phrases))))))))
	  ; not actually used as a test
	  nil pulser nil)))
)

(defun analyze-desc (originalvars wff &optional (environment *empty-env*)
				  &aux body evlvars evlrels vars2)
    (cond ((null (setf vars2 originalvars)))
	  ((listp vars2))
	  (t (setf vars2 (list vars2))))
    (try (multiple-value-setq (body evlvars evlrels)
	   (ExpandDescription (list vars2 's.t. wff)
			      :allowevalargs t
			      :keepstarts t
			      :environment environment))
	 expanddescription
	 (fail expanddescription ;;ap5-cannot-generate
	       (list vars2 's.t. wff)
	       "not a valid description" tryvalue))
    ;; formerly:
    ; If expanddescription fails we Fail ap5-cannot-generate so that
    ; outer Try's need not catch both failures
    ;; The trouble is that this gives you no clue that the reason
    ;; you can't generate R2 is that its generator uses R1 which is not
    ;; yet defined.
    (multiple-value-bind (code cdesc) (get-generator body evlvars evlrels)
      (values (vars-to-names (car body))
	      evlvars
	      code
	      (temporalp (third body))
	      cdesc)))


;; These are meant to allow more lazy evaluation -
; rather than passing a list of generated objects to a function
; one passes a generator.
; instead of doing (f (listof x s.t. (P x))) and
; (defun f(l) ... (loop for x in l ...) ...)
; one now does (f (relation ((x) s.t. (P x)))) and
; (defun f(r) ... (loop for x s.t.* (r x) ...) ...)

;; this is a lower level facility also thought to be useful
;; it provides a generator that can be pulsed (via do-pulse)
;; to provide the next tuple.  
(defmacro generator (vars st wff &environment env)
  (declare (ignore st))
  (unless (listp vars) (setf vars (list vars)))
  (multiple-value-bind
    (varnames evlvars initializer temporal)
      (analyze-desc vars wff env)
    (declare (ignore varnames))
    `(progn
       ,(when temporal
	  `(check2states
	     (mmemo (generate ,vars s.t. ,wff))))
       (let ,evlvars ,initializer))))

(defun do-pulse (fn) ;; what's the tradeoff of putting this inline?
  (withreadaccess (funcall fn)))

(defun canonicalize-trigger (desc &aux expanded)
  (setf expanded (expanddescription desc
		    :allowevalargs t :keepstarts t))
  (list (vars-to-names (car expanded)) 's.t. (vars-to-names-wff (caddr expanded))))

(defun canonicalize-description (desc &aux vars subst (v# -1) (c# -1))
  ; This expects an input that could be produced by expanddescription.
  ; [actually works ok with symbols rather than variables]
  ; Replace all vars with canonical var names and all other args with 
  ; canonical constant names.  Return the new description along with
  ; an ORDERED list of constant and variable bindings.
  ; I know this is not perfect, since the simplifer uses arbitrary-order,
  ; but it ought to do a lot of good, i.e., map equivalent wffs to the same
  ; thing most of the time.
  (declare (special vars))
  (mapc #'(lambda (v) (push (cons v (pack* 'x (incf v#))) subst))
		      (first desc))
  (setf vars (first desc))
  (values
    (list (mapcar #'cdr (reverse subst)) 's.t.
	  (flet ((canonicalize-arg (a)
		   (cond ((member a vars) (cdr (assoc a subst)))
			 (t (let ((entry (pack* 'c (incf c#))))
			      (push (cons a entry) subst)
			      entry)))))
	    (map-copy-wff (third desc)
	      :quantified-wff
	      #'(lambda (quant varlist qwff)
		  (list quant
			(mapcar #'(lambda (v &aux (canon (pack* 'x (incf v#))))
				    (push (cons v canon) subst)
				    canon)
				varlist)
			(let ((vars (append varlist vars)))
			  (declare (special vars))
			  (map-wff-internal qwff))))
	      :primitive-wff
	      #'(lambda (rel &rest args)
		  (cons rel (mapcar #'canonicalize-arg args)))
	      :incx
	      #'(lambda (cx cxwff)
		  (list 'INCX (canonicalize-arg cx) (map-wff-internal cxwff)))
	      :funcall-wff
	      #'(lambda (&rest args)
		  (cons 'FUNCALL (mapcar #'canonicalize-arg args)))
	      :apply-wff
	      #'(lambda (&rest args) (cons 'APPLY (mapcar #'canonicalize-arg args))))))
    (reverse subst)))


; We store the generators in a three level tree.  The first is the car of the
; wff, a relation for primitive wffs, a connective or quantifier for compound wffs.
; This extra level enables us to easily enumerate all generators for a particular
; relation.  Next is a description, conanicalized and compared by EQUAL, and finally
; the actual generator (compared by equal, if that matters).
;
#+ignore
(defun gen-cache-i-i-o (desc &optional even-if-recompile
			     &aux (car (first (ilistp (third desc)))))
  (PROG ((STATE (LIST NIL NIL NIL (LIST (CONS NIL generator-cache)))))
     (TREE-CONSTANT-NON-LAST (CDR (CDR STATE)) car #'eq)
     (AND (TREE-EXHAUSTED (CDR (CDR STATE))) (return nil))
     (TREE-CONSTANT-NON-LAST (CDR STATE) desc #'equal)
     (AND (TREE-EXHAUSTED (CDR STATE)) (return nil))
     (TREE-VARIABLE-LAST STATE)
     (AND (TREE-EXHAUSTED STATE) (return nil))
     (when (or (not (eq (cadr (assoc 'initialstate (setq state (caar state)))) :recompile))
	       even-if-recompile)
       (RETURN STATE))))

#+(and clisp mt)
(defvar cache-mutex (mt:make-mutex :name "cache-mutex"))
(defmacro with-cache-lock (&body body)
  `(flet ((body () ,.body))
    #+(and clisp mt)
    (if (eq (mt:current-thread) (mt:mutex-owner cache-mutex))
        (progn (body))
      (mt:with-mutex-lock (cache-mutex) (body)))
    #-(and clisp mt) (body)))

(defun gen-cache-i-i-o (desc &optional even-if-recompile
			 &aux (tree (purify-tree generator-cache)))
 (with-cache-lock
  (when (and tree ;; may be NIL early in bootstrapping
	  (setf tree (nexttree tree nil (first (ilistp (third desc))) #'eq))
	  (setf tree (nexttree tree nil desc #'equal)))
    ;; final level is never a hash table, because there is always just one value
     (when (or (not (eq (cadr (assoc 'initialstate (first tree))) :recompile))
	       even-if-recompile)
       (first tree)))))

(defun gendeleter (desc gen &aux (wff (third desc)) oldfn)
 (with-cache-lock
  (treedeleter (list (car wff) desc gen) generator-cache
	       (list #'eq #'equal #'equal))
  (when (or (setq oldfn (cadr (assoc :previous-fn gen)))
	    (not (eq :cannot-generate
		     (setq oldfn (cadr (assoc 'initialstate gen))))))
    (unless oldfn (error "internal error - See Donc.  Try to recompile nil!!"))
    (genadder desc `((initialstate :recompile)(:previous-fn ,oldfn)))
    ; should we remove pointers TO this gen? no, they still use it.
    (loop for d in (get oldfn 'uses-generator) do
	  (let ((fn (cadr (assoc 'initialstate (gen-cache-i-i-o d)))))
	    (setf (get fn 'generator-used-by) (remove oldfn (get fn 'generator-used-by)))))
    (setf (get oldfn 'uses-generator) nil)
    (unless (eq oldfn 'never-called)
      (setf (symbol-function oldfn)
	    (coerce
	     `(lambda (&rest args)
		(recompile-gen ',oldfn ',desc) (apply ',oldfn args))
	     'function))))
  (unless (dbobject-p (car wff))
    (try (map-wff wff
	     :primitive-wff
	     #'(lambda (rel &rest ignore) (declare (ignore ignore))
		       (treedeleter (list rel desc gen) generator-cache
				    (list #'eq #'equal #'equal))))
	 expanddescription nil))))
;; if map-wff gives errors cause things are no longer rels just don't decache

(pushnew :can-no-longer-generate *warning-flags*)

(defvar-resettable *in-relationsize* nil)

(defun genadder (desc gen &aux (wff (third desc)) prevgen previous newfn)
 (with-cache-lock
  (when *in-relationsize*
    (cerror "don't cache" "genadder called from in relationsize - show DonC")
    (return-from genadder nil))
  (setq gen (copy-list gen)) ; to avoid those read-only cells from "constants" ...
  (setq prevgen (gen-cache-i-i-o desc t))
  (unless (equal prevgen gen)
    (when (setq previous (cadr (assoc :previous-fn prevgen)))
      (cond ((eq (cadr (setq newfn (assoc 'initialstate gen)))
		 :cannot-generate)
	     (when (member :can-no-longer-generate *warning-flags*)
	       (warn "~A~%can no longer be generated~%~
                      Previously compiled code to do so ~
                      now generates an error" desc))
	     (push (list :previous-fn previous) gen)
	     (unless (eq previous 'never-called)
	       (setf (symbol-function previous)
		     #+ignore 'can-no-longer-generate
		     (coerce
		      `(lambda (&rest args &aux (desc ',desc) gen)
			(cerror "try to recompile"
				"can no longer generate ~A" desc)
			(when (setq gen (gen-cache-i-i-o desc))
			  (gendeleter desc gen))
			(recompile-gen ',previous desc)
			(apply ',previous args))
		      'function)))
	     (setf (get previous :previous-definition) nil))
	    ((eq (cadr newfn) :recompile)) ; gendeleter will take care of it
	    ((eq previous 'never-called))
	    ((eq (car (ilistp wff)) 'SUBSET-GEN))
	    (t (setf (symbol-function previous)
		     (symbol-function (cadr newfn)))
	       (setf (get previous :previous-definition)
		     (get (cadr newfn) :previous-definition))
	       (setf (cadr newfn) previous)))) ; keep old fnname
    (when prevgen (treedeleter (list (car (ilistp wff)) desc prevgen)
			       generator-cache (list #'eq #'equal #'equal)))
    (treeadder (list (car (ilistp wff)) desc gen)
	       generator-cache (list #'eq #'equal #'equal))
    (unless (dbobject-p (car (ilistp wff)) )
      (try (map-wff wff
	       :primitive-wff
	       #'(lambda (rel &rest ignore) (declare (ignore ignore))
			 (when prevgen
			   (treedeleter (list rel desc prevgen)
					generator-cache (list #'eq #'equal #'equal)))
			 (treeadder (list rel desc gen) generator-cache
				    (list #'eq #'equal #'equal))))
	   expanddescription nil)))))

(defun compile-gen-error (&rest ignore)
  (declare (ignore ignore))
  (error "still being compiled"))

#+lispworks(defvar *compile-gen-calls* nil)

(defun compile-gen (desc code rest &aux (sym (gentemp "F" ap-compiled)) finished)
  #+lispworks(push (list desc code rest sym) *compile-gen-calls*)
  (setf (symbol-function sym) (symbol-function 'compile-gen-error))
  (unwind-protect
      (progn
	(genadder desc (setq rest (cons (list 'initialstate sym) rest)))
	(let ((fn (cadr (assoc 'initialstate (gen-cache-i-i-o desc)))))
	  (if fn (compile-ap code fn)
	    (error "trying to compile nil!")))
	; use initialstate fn instead of sym since that's the permanent 
	; symbol - sym's function cell is just copied into that one
	(setq finished t))
    (unless finished (gendeleter desc rest))
    #+lispworks
    (when (eq (symbol-function sym) (symbol-function 'compile-gen-error))
	  (warn "~&~A still defined to call error - ~A" sym desc)))
  rest)

; this is needed in case the desc doesn't simplify to itself
(defun recompile-gen (fn desc &aux newdesc newfn)
  (unless fn (error "internal error: See Donc.  Can't recompile NIL!!"))
  (when (eq fn 'never-called) (return-from recompile-gen nil))
  (lookup-gen desc)
  (cond ((setq newfn (gen-cache-i-i-o desc))
	 ; normally ought to be a noop
	 (setf (symbol-function fn)
	       (cond ((eq (cadr (assoc 'initialstate newfn)) :cannot-generate)
		      #+ignore 'can-no-longer-generate
		      `(lambda (&rest args &aux (desc ',desc) gen)
			 (cerror "try to recompile"
				 "can no longer generate ~A" desc)
			 (when (setq gen (gen-cache-i-i-o desc))
			   (gendeleter desc gen))
			 (recompile-gen ',fn desc)
			 (apply ',fn args)))
		     (t (symbol-function (cadr (assoc 'initialstate newfn)))))))
	(t (setf newdesc (canonicalize-description
			   (expanddescription desc
					      :allowevalargs t
					      :keepstarts t)))
	   (unless (setq newfn (cadr (assoc 'initialstate (gen-cache-i-i-o newdesc))))
	     (error "cannot find the generator for ~A" desc))
	   (cond ((eq newfn :cannot-generate)
		  (when (member :can-no-longer-generate *warning-flags*)
		    (warn "~A~%can no longer be generated~%~
                           Previously compiled code to do so ~
                           now generates an error" desc))
		  (setf (symbol-function fn) ;; will fn track newfn?  should it??
			#+ignore 'can-no-longer-generate
			`(lambda (&rest args &aux (desc ',desc) gen)
			   (cerror "try to recompile"
				   "can no longer generate ~A" desc)
			   (when (setq gen (gen-cache-i-i-o desc))
			     (gendeleter desc gen))
			   (recompile-gen ',fn desc)
			   (apply ',fn args)))
		  (setf (get fn :previous-definition) nil))
		 (t (setf (symbol-function fn)
			  (symbol-function newfn))
		    (setf (get fn :previous-definition)
			  (get newfn :previous-definition)))))))

(defmacro lookup-this-generator (gen)
  ;; this is provided so that the (1-level) macroexpansion of 
  ;; (loop for vars s.t. wff ...) does not end up with the
  ;; description inside quote (that is ugly for code walkers)
  `(lookup-gen (mmemo ,gen)))


#+ignore ;;replaced by Don's proposed workaround
(defun get-generator (description &optional evlvars evalrels-p
		       &aux generator subgen entry canon sub rel
		       (*in-relationsize* nil))
  ; return a form that computes a pulser
  (multiple-value-setq (canon sub) (canonicalize-description description))
  (setf rel (car (ilistp (third canon))))
  ; since description is assumed to be the output of expanddescription,
  ; rel is either a relation, connective, quantifier or nil (for true/false)
  (cond
    (evalrels-p
     (labels
       ((get-funcall-generator (description)
          `(get-funcall-gen
	     ',(list (vars-to-names (car description)) 's.t.
		     (vars&rels-to-names-wff (caddr description)))
	     ',(mapcar #'car evlvars) ,.(mapcar #'car evlvars)))
	(get-special-funcall-gen (description &aux canon)
		; for this special case we use lookup-gen+, defined in tools
	      (setf canon
		    (canonicalize-description
		      (list (car description) 's.t.
			    (cons (car (caddr description)) (cddr (caddr description))))))
	      (cond ((eq (caaddr canon) 'funcall)
		     `(or
			(funcall
			  (lookup-gen++ (list ',(car canon) 's.t.
					      (cons ,(cadr (caddr description))
						    ',(cdr (caddr canon)))))
			  ,.(loop for arg in (cddr (caddr description))
				  unless (member arg (car description))
				  collect arg))
			,(get-funcall-generator description)))
		    (t `(or (apply (lookup-gen++ (list ',(car canon) 's.t.
						       (finish-canon-apply
							 ,(cadr (caddr description))
							 ',(cdr (caddr canon)))))
				   ,.(loop for arg in (cddr (caddr description))
					   unless (member arg (car description))
					   collect arg))
			    ,(get-funcall-generator description))))))
       (values
	 (cond ((member (car (third description)) '(apply funcall))
		(get-special-funcall-gen description))
	       (t (get-funcall-generator description)))
	 description)))
    ((setf entry (gen-cache-i-i-o canon))
     (record-use-of-generator canon entry)
     (note-generator-found entry)
     (and (eq (cadr (assoc 'initialstate entry)) :cannot-generate)
	  (fail ap5-cannot-generate description))
     (let ((cdesc (rels-to-names canon)))
       (values
	 `(funcall (load-memo (lookup-this-generator ,cdesc))
		   ,.(cond ((symbolp rel)	; compound
			    (loop for s in sub
				  unless (variable-p (car s))
			    ; probably shouldn't rely on variable-p
			    ; though perhaps get-gen won't be passed any desc
			    ; with (type var) objects unbound (???) ***
				  collect (car s)))
			   (t (loop for a in (cdaddr description)
				    as temp in (cadr (assoc 'template entry))
				    when (eq temp 'input) collect a))))
	 cdesc)))
    ((prog1 nil ; always return nil to go on to next clause
	   (try (progn
		  (setf subgen
			(with-whostate expand-msg
			  (findgenerator (first description)
			    (cond ((consp (third canon))
				   (sublis (loop for s in sub
					       when (variable-p (car s))
						 ; *** see above
						 collect (cons (cdr s) (car s)))
					   (third canon)))
				  (t (third canon))))))
		  ; work backward in case of (and (p x 1) (r 1)):
		  ; the two occurrences of 1 should be treated as different constants
		  (record-generator (first canon) (third canon) (size subgen) (effort subgen))
		  (setf generator (sgen subgen)))
		'ap5-cannot-generate
		;; TI likes to write protect constants -> copy-tree
		(genadder canon (copy-tree '((initialstate :cannot-generate))))
		(fail ap5-cannot-generate description tryvalue))))
    ; always return nil so as to go on to next clause
    ((or (compoundwffp (wff subgen)) (member (wff subgen) '(true false)))
     ; compound, T/F, {x s.t. (R x x)}
     ; (symbolp (car (ilistp (wff subgen)))) no longer works since
     ; make-test-gen now translates rel into symbol for dumping
     (setf generator
	   (compile-gen canon
		`(lambda (,.(loop for s in sub
				  unless (variable-p (car s))	;***
					 collect (cdr s))
				 &aux	;,.(vars-to-names (car description))
				 ,@ (car canon))
	          (declare (optimize (speed 3)(safety 1)(compilation-speed 0)))
		   ;,.(vars-to-names (car description))
		   ,@ (car canon)
		   (withreadaccess ,(cadr (assoc 'initialstate generator))))
		; this copy-list is supposed to protect against generators
		; built with `( ... (effort 20)) which might end up sharing cells
		(copy-list (remove 'initialstate generator :key #'car))))
    (record-use-of-generator canon generator)
     (let ((cdesc (rels-to-names canon)))
       (values
	 `(funcall (load-memo (lookup-this-generator ,cdesc))
		   ,.(loop for s in sub unless (variable-p (car s) ) collect (car s)))
	 cdesc)))
    ;***
    ((or (when (setf entry (gen-cache-i-i-o canon))
	   (record-use-of-generator canon entry)
	   t)
	 (progn (setf (sgen subgen) (cache-gen-if-needed subgen)
		      entry (gen-cache-i-i-o canon))
		(record-use-of-generator canon entry)
		entry))
     (let ((cdesc (rels-to-names canon)))
       (values
	 `(funcall (load-memo (lookup-this-generator ,cdesc))
		   ,.(loop for a in (cdaddr description)
			   as temp in (cadr (assoc 'template entry))
			   when (eq temp 'input) collect a))
	 cdesc)))
    (t (error "internal ap5 error - show DonC - failure to canonicalize ~A" canon))))

(defun get-generator (description &optional evlvars evalrels-p
		       &aux generator subgen entry canon sub rel
		       (*in-relationsize* nil))
  ; return a form that computes a pulser
  (multiple-value-setq (canon sub) (canonicalize-description description))
  (setf rel (car (ilistp (third canon))))
  ; since description is assumed to be the output of expanddescription,
  ; rel is either a relation, connective, quantifier or nil (for true/false)
  (cond
    (evalrels-p
     (labels
       ((get-funcall-generator (description)
          `(get-funcall-gen
	     ',(list (vars-to-names (car description)) 's.t.
		     (vars&rels-to-names-wff (caddr description)))
	     ',(mapcar #'car evlvars) ,.(mapcar #'car evlvars)))
	(get-special-funcall-gen (description &aux canon)
		; for this special case we use lookup-gen+, defined in tools
	      (setf canon
		    (canonicalize-description
		      (list (car description) 's.t.
			    (cons (car (caddr description)) (cddr (caddr description))))))
	      (cond ((eq (caaddr canon) 'funcall)
		     `(or
			(funcall
			  (lookup-gen++ (list ',(car canon) 's.t.
					      (cons ,(cadr (caddr description))
						    ',(cdr (caddr canon)))))
			  ,.(loop for arg in (cddr (caddr description))
				  unless (member arg (car description))
				  collect arg))
			,(get-funcall-generator description)))
		    (t `(or (apply (lookup-gen++ (list ',(car canon) 's.t.
						       (finish-canon-apply
							 ,(cadr (caddr description))
							 ',(cdr (caddr canon)))))
				   ,.(loop for arg in (cddr (caddr description))
					   unless (member arg (car description))
					   collect arg))
			    ,(get-funcall-generator description))))))
       (values
	 (cond ((member (car (third description)) '(apply funcall))
		(get-special-funcall-gen description))
	       (t (get-funcall-generator description)))
	 description)))
    ((setf entry (gen-cache-i-i-o canon))
     (record-use-of-generator canon entry)
     (note-generator-found entry)
     (and (eq (cadr (assoc 'initialstate entry)) :cannot-generate)
	  (fail ap5-cannot-generate description))
     (let ((cdesc (rels-to-names canon)))
       (values
	 #+ignore 
	 `(funcall (load-memo (lookup-this-generator ,cdesc))
		   ,.(cond ((symbolp rel)	; compound
			    (loop for s in sub
				  unless (variable-p (car s))
			    ; probably shouldn't rely on variable-p
			    ; though perhaps get-gen won't be passed any desc
			    ; with (type var) objects unbound (???) ***
				  collect (car s)))
			   (t (loop for a in (cdaddr description)
				    as temp in (cadr (assoc 'template entry))
				    when (eq temp 'input) collect a))))
	 `(let ((FOO (load-memo (lookup-this-generator ,cdesc))))
	     (funcall FOO
		   ,.(cond ((symbolp rel)	; compound
			    (loop for s in sub
				  unless (variable-p (car s))
			    ; probably shouldn't rely on variable-p
			    ; though perhaps get-gen won't be passed any desc
			    ; with (type var) objects unbound (???) ***
				  collect (car s)))
			   (t (loop for a in (cdaddr description)
				    as temp in (cadr (assoc 'template entry))
				    when (eq temp 'input) collect a)))))
	 cdesc)))
    ((prog1 nil ; always return nil to go on to next clause
	   (try (progn
		  (setf subgen
			(with-whostate expand-msg
			  (findgenerator (first description)
			    (cond ((consp (third canon))
				   (sublis (loop for s in sub
					       when (variable-p (car s))
						 ; *** see above
						 collect (cons (cdr s) (car s)))
					   (third canon)))
				  (t (third canon))))))
		  ; work backward in case of (and (p x 1) (r 1)):
		  ; the two occurrences of 1 should be treated as different constants
		  (record-generator (first canon) (third canon) (size subgen) (effort subgen))
		  (setf generator (sgen subgen)))
		'ap5-cannot-generate
		;; TI likes to write protect constants -> copy-tree
		(genadder canon (copy-tree '((initialstate :cannot-generate))))
		(fail ap5-cannot-generate description tryvalue))))
    ; always return nil so as to go on to next clause
    ((or (compoundwffp (wff subgen)) (member (wff subgen) '(true false)))
     ; compound, T/F, {x s.t. (R x x)}
     ; (symbolp (car (ilistp (wff subgen)))) no longer works since
     ; make-test-gen now translates rel into symbol for dumping
     (setf generator
	   (compile-gen canon
		`(lambda (,.(loop for s in sub
				  unless (variable-p (car s))	;***
					 collect (cdr s))
				 &aux	;,.(vars-to-names (car description))
				 ,@ (car canon))
		  (declare (optimize (speed 3)(safety 1)(compilation-speed 0)))
		   ;,.(vars-to-names (car description))
		   ,@ (car canon)
		   (withreadaccess ,(cadr (assoc 'initialstate generator))))
		; this copy-list is supposed to protect against generators
		; built with `( ... (effort 20)) which might end up sharing cells
		(copy-list (remove 'initialstate generator :key #'car))))
    (record-use-of-generator canon generator)
     (let ((cdesc (rels-to-names canon)))
       (values
         #+ignore 
	 `(funcall (load-memo (lookup-this-generator ,cdesc))
		   ,.(loop for s in sub unless (variable-p (car s) ) collect (car s)))
	 `(let ((FOO (load-memo (lookup-this-generator ,cdesc))))
             (funcall FOO
		   ,.(loop for s in sub unless (variable-p (car s) ) collect (car s))))
	 cdesc)))
    ;***
    ((or (when (setf entry (gen-cache-i-i-o canon))
	   (record-use-of-generator canon entry)
	   t)
	 (progn (setf (sgen subgen) (cache-gen-if-needed subgen)
		      entry (gen-cache-i-i-o canon))
		(record-use-of-generator canon entry)
		entry))
     (let ((cdesc (rels-to-names canon)))
       (values
         #+ignore 
	 `(funcall (load-memo (lookup-this-generator ,cdesc))
		   ,.(loop for a in (cdaddr description)
			   as temp in (cadr (assoc 'template entry))
			   when (eq temp 'input) collect a))
	 `(let ((FOO (load-memo (lookup-this-generator ,cdesc))))
            (funcall FOO
		   ,.(loop for a in (cdaddr description)
			   as temp in (cadr (assoc 'template entry))
			   when (eq temp 'input) collect a)))
	 cdesc)))
    (t (error "internal ap5 error - show DonC - failure to canonicalize ~A" canon))))

; this used for compiling to files (see compile-code-for-desc)
(defun get-generator-source (canon &aux gen)
  (setf (third canon) (map-copy-wff (third canon)))
  (when (setq gen (gen-cache-i-i-o canon))
    (gendeleter canon gen))
  (prevdef (lookup-gen canon t)))

(defun record-use-of-generator (canon &optional gen &aux fn)
  ;(print (list *fn-being-compiled* canon gen))
  (unless gen (setq gen (gen-cache-i-i-o canon)))
  (when (and *fn-being-compiled* 
	     (not (eq :cannot-generate (setq fn (cadr (assoc 'initialstate gen))))))
    (when (symbolp *fn-being-compiled*)
      (pushnew canon (get *fn-being-compiled* 'uses-generator) :test #'equal))
    ; might as well try to go backward too ...
    ; since it's easier to get from canon to initialstate fn than back, we record on fn
    (when (symbolp fn) (pushnew *fn-being-compiled* (get fn 'generator-used-by)))))

(defun note-generator-found (entry)
  (incf (cdr (or (assoc 'ntimesfound entry)
		 (let ((zilch (cons 'ntimesfound 0)))
		   (nconc entry (list zilch))
		   zilch)))))

(defun finish-canon-apply (rel args &aux arity)
  (unless (setq rel (relationp rel)) (return-from finish-canon-apply (list (list nil))))
  ; to look like a description to lookup-gen++
  (When (> (setq arity (arity* rel)) 10)
    (error "DonC didn't expect that many arguments"))
  (cons rel
	(nconc (butlast args)
		(loop for extra in
		      (member (car (last args))
			      '(c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10))
		      as pos below (- arity (length (cdr args)))
		      collect extra))))

(defun lookup-gen++ (desc+ &aux result)
  ; where desc+ is allowed to contain as caaddr a rel, relname or desc
  (cond ((dbobject-p (caaddr desc+))
	 (if (eq (setq result (lookup-gen+ desc+)) :cannot-generate)
	     (fail ap5-cannot-generate desc+)
	     result))
	((symbolp (caaddr desc+))
	 (if (eq (setq result
		       (lookup-gen+ (list (car desc+) 's.t.
					  (cons (relationp (caaddr desc+))
						(cdaddr desc+)))))
		 :cannot-generate)
	     (fail ap5-cannot-generate desc+)
	     result))
	((consp (caaddr desc+)) ; description
	 'ignored)
	(t (error "trying to generate ~A which does not look like a description" desc+))))

(defun get-funcall-gen (description vars &rest vals &aux alist newwff)
  (setq alist (loop for var in vars as val in vals collect (cons var val)))
  (setq newwff
	(map-copy-wff (caddr description)
	    :funcall-wff
	    #'(lambda (rel &rest args)
		(cons (or (cdr (assoc rel alist))
			  (error "internal ap5 error - see DonC - ~
				  strange funcall rel ~A" rel))
		      args))
	    :apply-wff
	    #'(lambda (rel &rest args)
		`(,(or (cdr (assoc rel alist))
		       (error "internal ap5 error - see DonC - ~
			       strange funcall rel ~A" rel))
		  ,.(loop for argtail on args while (cdr argtail)
			  collect (car argtail))
		  ,.(mapcar #'kwote
			    (cond ((cdr (assoc (car (last args)) alist)))
				  ((constantp* (car (last args))) (eval (car (last args))))
				  (t (error "internal ap5 error - see DonC - ~
					strange apply arg ~A" (car (last args))))))))))
  ; reasons to redo expanddescription: check comparisons on vars, resimplify
  ; problems: new names for evlvars
  (multiple-value-bind (newdes evlvars evlrels)
      (expanddescription (list (car description) 's.t. newwff)
			 :allowevalargs t :keepstarts t)
    (and evlrels (error "funcall/apply wff evaluates to another funcall/apply wff"))
    (progv (mapcar #'car evlvars)
	   (mapcar #'(lambda (x) (cdr (assoc (cadr x) alist))) evlvars)
	   (eval (subst 'identity 'load-memo (get-generator newdes))))))

(defun compile-primitive-gen (subgen canon &aux (generator (sgen subgen)) inputs)
  (setq inputs (loop for a in (cdr (wff subgen))
		     as temp in (cadr (assoc 'template generator))
		     when (eq temp 'input) collect a))
  (compile-gen canon
	`(lambda ,(vars-to-names inputs)
	   (declare (optimize (speed 3)(safety 1)(compilation-speed 0)))
	   (withreadaccess
	     (,(cadr (assoc 'initialstate generator))
	      (theap5relation ,(relationnamep (caaddr canon)))
	      ,.(vars-to-names inputs))))
	(remove 'initialstate generator :key #'car)))

(defun cache-gen-if-needed (subgen &aux canon old (wff (wff subgen))
				   (temp (cadr (assoc 'template (sgen subgen)))))
  ; only done for primitive wffs from get-generators and findgens - return new sgen
  ; (setq canon (canonicalize-description (list (soutput subgen) 's.t. (wff subgen))))
  ; this is not right when subgen is really only a subset generator, e.g.,
  ; soutput may be nil and the wff may still contain vars
  (setq canon
	(let ((v# -1) (c# -1) args vars)
	  (loop for ;arg in (cdr wff) as
		tem in temp do
		(cond ((eq tem 'input) (push (pack* 'c (incf c#)) args))
		      (t (push (pack* 'x (incf v#)) args) (push (car args) vars)))
		finally (return (list (reverse vars) 's.t.
				      ; this relationp needed cause make-test-gen ...
				      (cons (relationp (car wff)) (reverse args)))))))
  ; have to recanonicalize since wff may be part of a larger one
  (cond ((loop for arg in (cdr wff)
	       as tem in temp
	       thereis (and (eq 'output tem) (not (member arg (soutput subgen)))))
	 (adjust-generator subgen canon))
	((and (setq old (gen-cache-i-i-o canon))
	      (ifleq (cadr (assoc 'effort old))
		     (cadr (assoc 'effort (sgen subgen)))))
	 old)
	((null old) (compile-primitive-gen subgen canon))
	(t ;(gendeleter canon old)  seems to be taken care of by compile-primitive-gen,
           ;; and avoids a bootstrapping problem in which the deleted (although correct)
           ;; generator is needed to COMPILE the new generator
	   (compile-primitive-gen subgen canon))))

(defun adjust-generator (sgen canon &aux newgen old newcanon
			      check inputs outputs vars args
			      (wff (wff sgen))
			      (temp (cadr (assoc 'template (sgen sgen)))))
  ; sgen is too general for canon (which is non-compound)
  (let ((v# -1) (c# -1))
    (loop for arg in (cdr wff) as tem in temp
	as arg# below (length temp)
	when (eq tem 'input) do (let ((c (pack* 'c (incf c#))))
				  (push c args) (push c inputs))
	when (eq tem 'output) do (let ((v (pack* 'x (incf v#))))
				   (push v args) (push v vars)
				   (cond ((member arg (soutput sgen))
					  ; previously (variable-p arg)
					  (push v outputs))
					 (t (push (list v (gensym "V") arg#) check))))
	;finally
	;(setq newcanon (list (reverse vars) 's.t. (cons (car wff) (reverse args))))
	))
  (setq newcanon ; get the canonical form of the version with inputs
	(let ((v# -1) (c# -1) args vars)
	  (loop for arg in (cdr wff) as tem in temp do
		(cond ((and (eq tem 'output)
			    (member arg (soutput sgen))#+ignore(variable-p arg))
		       (push (pack* 'x (incf v#)) args)
		       (push (car args) vars))
		      (t (push (pack* 'c (incf c#)) args)))
		finally (return (list (reverse vars) 's.t.
				      (cons (car wff) (reverse args)))))))
  (cond ((and (setq old (gen-cache-i-i-o newcanon))
	      (ifleq (cadr (assoc 'effort old))
		     (cadr (assoc 'effort (sgen sgen)))))
	 old)
	(t (setq newgen
		 `(lambda ,(loop for arg in (reverse args)
				 unless (member arg outputs) collect
				 (or (cadr (assoc arg check)) arg))
		  (declare (optimize (speed 3)(safety 1)(compilation-speed 0)))
		    (let ((unchecked
			    (funcall (load-memo (lookup-gen (mmemo ,(rels-to-names canon))))
				     ,.(reverse inputs))))
		      #'(lambda nil
			  (prog (exhausted ,.(reverse vars))
			    #+lucid (declare (ignore exhausted))
			    ;; Monday 2010/10/11 ignorable was under #+allegro
			    (declare (ignorable exhausted))
			     next
				(when (multiple-value-setq (exhausted ,.(reverse vars))
					(funcall unchecked))
				  (return t)) ; exhausted
				(unless (and ,.(loop for c in check collect
						     (get-test-function
						       (get-comparison (car wff) (caddr c) t)
						       (car c) (cadr c))))
				  (go next))
				; if we didn't want to share this code we could
				; just fall thru with vars bound
				(return (values nil ,.(reverse outputs))))))))
	   (compile-gen newcanon newgen
	       (cons (list 'template
			   (loop for arg in (cdr wff)
				 as tem in temp collect
				 (cond ((and (eq tem 'output)
					     (member arg (soutput sgen))
					     #+ignore(variable-p arg))
					'output)
				       (t 'input))))
		     (remove 'initialstate
			     (remove 'template (sgen sgen) :key #'car)
			     :key #'car))))))

(defun lookup-gen (canondesc &optional no-error &aux lookup)
  (setf canondesc (names-to-rels canondesc)
	lookup (cadr (assoc 'initialstate
			    (gen-cache-i-i-o canondesc))))
  (and (eq lookup :cannot-generate) (not no-error)
       (fail ap5-cannot-generate canondesc))
  (or lookup
      ; if not in cache we compile it - it supposedly worked before
      (let ((desc (expanddescription canondesc
		     :allowevalargs t :keepstarts t :sort-juncts nil)))
	; we avoid sorting juncts since that may require arguments
	; in a different order, e.g., ((x0) s.t. (and (P x0 c0) (Q x0 c1)))
	; may canonicalize to ((x0) s.t. (and (Q x0 c0) (P x0 c1)))
	; which requires switching order of c0, c1
	(try (get-generator desc) ap5-cannot-generate nil)
	(setq lookup (cadr (assoc 'initialstate (gen-cache-i-i-o canondesc))))
	(and (eq lookup :cannot-generate) (not no-error)
	     (if (member 'ap5-cannot-generate trystack)
		 (fail ap5-cannot-generate canondesc)
	       (progn
		 (cerror "try to recompile it"
			 "cannot generate ~A" canondesc)
		 (gendeleter desc (gen-cache-i-i-o canondesc))
		 (return-from lookup-gen
		   (lookup-gen canondesc no-error)))))
	lookup)
      (error "internal ap5 error - show DonC - failure to canonicalize ~A" canondesc)))

(defun canonical-rel-template (rel template &aux args vars (v# -1) (c# -1))
  (setq args (loop for temp in template collect
		   (cond ((eq temp 'input) (pack* 'c (incf c#)))
			 (t (car (push (pack* 'x (incf v#)) vars))))))
  (list (reverse vars) 's.t. (cons rel args)))

(defun lookup-generator (rel template)
  ; purely for compatibility with code compiled for intermediate caching scheme
  (lookup-gen (canonical-rel-template rel template)))

(pushnew :generate-cost *warning-flags*)
(pushnew :generate-size *warning-flags*)

(defun record-generator (vars wff size effort)
  (when (listp generator-cost-record)
    (push (list vars wff size effort) generator-cost-record))
  (when (and (ifleq geneffortwarning effort) (member :generate-cost *warning-flags*))
	 (warn1 "Estimated cost to generate ~S s.t. ~S is ~d"
	         vars wff (if effort (round effort) "infinity")))
  (when (and (ifleq gensizewarning size) (member :generate-size *warning-flags*))
	 (warn1 "Estimated size of ~S s.t. ~S is ~d"
	         vars wff (if size (round size) "infinity"))))
 
(defun check-equivalence (check-pair)
  (get-test-function (evalvarcompare (car check-pair))
		     (evalvarname (car check-pair))
		     ; caddr is a new var if supplied
		     (name-of-var (or (caddr check-pair) (cadr check-pair)))))

(defun bindandcheck (gen vars wff &aux newvars testvars)
    ; we want to use the generator Gen (not subgen!) to get Vars s.t. Wff
    ;This function computes a list of variables to bind (after exhausted and
    ; newstate) and a list of pairs to check for equivalence afterward
    (cond ((compoundwffp wff)
	   (cadr (assoc 'output gen)))  ; nothing to check
          (t (setq newvars
		   (loop for p in (cadr (assoc 'template gen))
			 as b in (cdr (ilistp wff))
			 as pos from 0
			 when (eq p 'output) collect
			 (cond ((member b vars) b)
			       ((variable-p b)
				(caar (push (list (make-evalvar
						    :evalvarname (gensym "EV")
						    :evalvarcompare (varcompare b))
						  b)
					    testvars)))
			       ; I claim next clause should never happen ...
			       (t (caar (push (list (make-evalvar
						      :evalvarname (gensym "EV")
						      :evalvarcompare
						      (get-comparison (car wff) pos t))
						    b)
					      testvars))))))
	     (values newvars testvars))))


;---- Conventions for using Generators ----
; if wff is compound
; - the initializer is just eval'd, returning a closure (of no args) as a pulser
; - the pulser returns exhausted and the values of the variables to ge generated
;   in the order of the Output property of Gen
; if wff is not compound:
; - the initializer accepts as input the relation object and the values
;   of the objects identified as Input's in the template (in that order)
;   an returns a closure (of no args) as a pulser
; - the pulser returns exhausted and the values that correspond
;   to the Output's in the template (in that order)
;   If those places in the wff were not variables to be bound, the values
;   have to be tested for agreement with whatever was there.
; note that these are likely to change at the same time as DefRelGenerator -
; namely whenever the calling sequence of generators changes.
;
(defun expand-initializer (gen wff &optional inputs)
  ; Gen is a real Gen, not subgen
  (cond ((compoundwffp wff) (cadr (assoc 'initialstate gen)))
	((not (zlistp wff)) (list (cadr (assoc 'initialstate gen))))
	(inputs (cons (cadr (assoc 'initialstate gen)) inputs))
	((eq (caar gen) 'test) 'this-should-never-be-used)
	(t `(funcall (load-memo (lookup-gen
			     (mmemo ,(rels-to-names
				       (canonical-rel-template 
					 (car wff) (cadr (assoc 'template gen)))))))
		     ,.(loop for x in (cadr (assoc 'template gen))
			     as arg in (cdr wff) when (eq x 'input)
			     collect (name-of-var arg))))))

(defun matchtemplate (template vars pat)
    ; does the IO template of a generator indicate that it's general enough to
    ; generate all the vars in Pat
    (and (zlistp template)
	 (zlistp pat)
	 (= (length template) (length pat))
	 (loop for x in template as y in pat
	       always (or (eq x 'output)
			  (not (member y vars))))))

#+ignore
(defun variablep (x) (member x vars))
;formerly 
#+ignore(cond ((symbolp x)
	 (setq x (variablename x))
	 (loop for v in vars thereis
	       (and (symbolp v)
		    (eql (setq x (variablename x)) (variablename v))
		    x)))
	(t (member x vars)))

;Find the best way to generate {<vars> s.t. <Wff>}
; The answer is a SubsetGen of the form (E I O S G W)
; meaning that for each set of bindings for vars in I,
; generator G will generate (approx S sets of) {<O> s.t. <W>}
; with effort approx E.  (W is Wff.)
; As special cases of G: 
;   - ((Test <Wff>)) means given all bindings, test the Wff
;     [this is ok since assoc of normal proerties => nil]
;   - if Wff is (And/Or ...), G = list of subgens for the -juncts
;     [- *** get rid of this ***]
;The normal representation of G is an alist with fields:
;- Effort - estimate of number instructions to do whose generation,
;- InitialState - if generating a compound wff then just a form, otherwise
;  a function of the relation and non-vars (in argument order) - returns
;  a closure object that will be called as the pulser.  This takes no arguments
;  (but may alter the state over which it's closed), and returns an exhausted
;  flag and the values of the variables it is supposed to generate.
;  Order of output vars is argument order for non-compound wffs, and order
;  in Output property otherwise,
;- Template - if not for a compound wff, there is a template that is a list
;  of Input/Output - corresponding to the arguments of the relation
;- Output - see above
;- Size - if for a compound (or defined) wff throw in size (same as for subsetgens)
;

(defun findgenerator (vars wff &optional noerrors &aux generators equiv-failure)
  (declare (special equiv-failure))
  (cond ((and (null (setq generators (findgenerators vars wff nil)))
	      (not noerrors))
	 (fail ap5-cannot-generate (list vars 's.t. wff)
	       (when equiv-failure
		 (cons
		   "NOTE: could not generate a finer equivalence class from a coarser one"
		   equiv-failure))))
	((null (cdr generators)) (car generators))
	(t (loop for gen in generators with result
		 when (iflessp (effort gen) (and result (effort result)))
		 do (setq result gen)
		 finally (return result)))))


; Find some set of subsetgens (I hope including the best) for {vars | Wff}
; In this file Subsetflg is either a list of variables that may be available 
; as inputs (so we want the result to include the best algorithm for every 
; subset of those variables being supplied) or, as a special case, T, meaning that
; the list of such variables is empty but that canonicalization is not needed.
; (That's pretty close to what canonical also means inside findgenerators.)
; In relgenerators, however, subsetflg is still either nil or T, where T means
; that we want all subsets, which is what we would mean here if we made it the 
; same as the vars argument.
; Do not include any items that are dominated by others (see DominateEIO)
; Assume that equal vars already processed

(defvar findgens-cache nil)

; these are now treated like compound wffs resulting in different protocol ...
(defvar NullSetGenerator '((InitialState (let nil #'(lambda nil t)))
			   (Template NIL)
			   (Effort 1)))
(defvar TSetGenerator '((InitialState (let (done)
					#'(lambda nil
					    (cond (done)
						  (t (setq done t) nil)))))
			(Template NIL)
			(Effort 1)))

(defun findgenerators (vars wff subsetflg &optional canonical
			    &aux ans badvar
			    (rel (relationp (car (ilistp wff))))
			    canon canonsub entry)
  (declare (special findgens-cache))
  (when (and (not subsetflg) (not canonical) (not *in-relationsize*)
	     (compoundwffp wff) (not (eq 'not (car wff))))
    (multiple-value-setq (canon canonsub)
      (canonicalize-description (list vars 's.t. wff)))
    (cond ((setf entry (assoc canon findgens-cache :test 'equal))
	   (setf findgens-cache (cons entry (remove entry findgens-cache))))
	  (t (let ((expanded (expandcanondesc canon vars wff)))
	       (findgenerators (car expanded) (caddr expanded) nil t))
	     ;(push canon stat4)
	     (unless (setf entry (assoc canon findgens-cache :test 'equal))
	       (error "failure to canonicalize?"))))
    (return-from findgenerators (subst-findgens (cdr entry) canonsub)))
  (setf ans
	(cond
	  ((setf badvar (loop for v in vars thereis (null (varcompare v))))
	   (fail ap5-cannot-generate "var has no compare relation"
		 badvar vars wff))
	  ((eq wff 'false)
	   (list (make-subsetgen :effort 1. :size 0. :wff wff
				 :sgen nullsetgenerator)))
	  ((and (eq wff 'true) (null vars))
						; sure, we can generate that
	   (list (make-subsetgen :effort 1. :size 1. :wff wff
				 :sgen Tsetgenerator)))
	  ((not (zlistp wff))
	   (or subsetflg (fail ap5-cannot-generate (list vars 's.t. wff)))
	   nil)
	  ((null vars) nil)
	  ;(list (make-Test-Generator wff)) ; handle this below as in subsetgen
	  ((compoundwffp wff) (findwffgenerators vars wff subsetflg))
	  ((not rel) (error "~s not a relation" (car wff)))
	  ((and (loop for v in vars thereis (not (member v wff)))
		(not subsetflg))
	   #+ignore(help "not all vars are bound in " (list vars 's.t. wff))
	   ; this may actually be all right when calling fingenerator with noerror
	   nil)
	  ((loop for v in vars thereis (member v (cdr (member v (cdr wff)))))
	   (generatorswitheq vars wff subsetflg))
	  ((equivalence-relp rel)
	   (equivalencegenerators vars wff rel subsetflg))
	  #+ignore  ; for bottom of compound wff - need a way to find it and apply args
	  ((and (not subsetflg)
		(setf ans (assoc (loop for arg in (cdr wff) collect
				       (cond ((variablep arg) 'output) (t 'input)))
				 (get-structure-property rel 'generator-cache)
				 :test #'equal)))
	   ; check the cache - we ought to have some way to avoid recomputing
	   ; the same gens when subsetflg=t ***
	   (list (subfromgenerator (cadr ans) vars wff)))
	  (t					; down to the primitives
	   (let ((gens (loop for gen in
			     (if (and *in-relationsize*
				      (or (null (getdefn rel))
					  ; if it has size estimates use them
					  (rel-sizes rel)))
				 '(fake-generator)
				 (nconc (all-generators-for rel)
					;; see all-gens-for below
					(when (and (getdefn rel)
						   (not (defined-p rel)))
					      '(definedrelgenerator))))
			     append ;nconc
			     ;MULTIPLE-VALUE-LIST can produce shared list structure on TIs
			     (multiple-value-list
			       (apply gen subsetflg vars rel (cdr wff))))))
		  ; first compute all of them so we can discard those that are subsumed
	     (setf gens (delete nil gens)) ; old protocol returned a list
	     (loop for g in gens unless
		   (and (assoc 'template g)
			(assoc 'initialstate g))
		   do (error "implemementation bug~
                                   - generator needs initialstate and template~%~s" g)
		   unless (= (length (cadr (assoc 'template g))) (arity* rel))
		   do (error "implemementation bug~
                                   - wrong length template~%~s" g))
	     (setf gens (loop for g in gens collect (subfromgenerator g vars wff)))
	     #+ignore ; old version
	     (unless subsetflg
	       (setf gens (loop for e in gens when (fsubset vars (soutput e))
				collect e)))
	     ; new version
	     (unless (eq t subsetflg)
	       (setf gens
		   (delete-if-not
		    #'(lambda (g) (fsubset (sinput g) subsetflg))
		    gens)))
	     (setf gens (sort gens #'ifleq :key #'effort))
	     ;; tester is expected to be first
	     (setf gens (loop for g1 in gens unless
			      (and ;(not (eq (caar (sgen g1)) 'test))
				   (loop for g2 in gens until (eq g1 g2)
					 thereis (dominateeio g2 g1)))
			      collect g1))
	     ; only those of less effort can dominate
	     ; now the value
	     (loop for gen in gens collect
		   (progn (when (and (soutput gen) ; not for tests
				     (not (context-sensitive rel))
				     (not (derivedrel rel))
				     (not (nonatomic-relation rel))
				     (or (possibletoupdate rel nil)
					 (possibletoupdate rel t)))
			    (setf gen (cxsensitize gen rel)))
			  ; make compound gens use cache entries for primitives
			  (or subsetflg *in-relationsize*
			      (setf (sgen gen) (cache-gen-if-needed gen)))
			  (or subsetflg *in-relationsize*
			      (adjust-permutation-if-needed vars gen))
			  gen))))))
  (if *in-relationsize*
      ; even if not ... when (and rel (null (getdefn rel)))
      (when subsetflg 
	(push (make-subsetgen :effort 1 :sinput (varsfreein wff vars)
			      :sgen (list (list 'test wff)) :size 1. :wff wff)
	      ans))
      (when (and (not (member wff '(true false)))
		 (or (eq t subsetflg) (fsubset vars subsetflg)))
	(let ((tester (make-Test-Generator wff)))
	  (unless (loop for x in ans thereis (dominateeio x tester))
	    (push tester ans)))))
  (when (and canonical (not *in-relationsize*))
    (push (cons (list (vars-to-names vars) 's.t. (vars-to-names-wff wff)) ans)
	  findgens-cache)
    (let ((tail (nthcdr 29 findgens-cache)))
      (when tail (setf (cdr tail) nil))))
    ans)

(defun fake-generator (ignore vars rel &rest args)
  (declare (ignore ignore vars))
  (apply #'values
	 `((INITIALSTATE
	     (LAMBDA (&REST IGNORE)
	       (DECLARE (IGNORE IGNORE))
	       (error "calling fake generator!?")))
	   (template ;,(loop for v in args collect 'output)
		     ,(make-list (length args) :initial-element 'output))
	   (effort ,(relationsize args (cons rel args))))
	 (loop for size in (rel-sizes rel)
	       when (member 'input (car size)) collect
	       `((INITIALSTATE
		   (LAMBDA (&REST IGNORE)
		     (DECLARE (IGNORE IGNORE))
		     (error "calling fake generator!?")))
		 (template ,(car size))
		 (effort ,(cadr size))))))

(defun subst-findgens (ans canonsub)
  (setq ans (mapcar #'copy-subsetgen ans)
	;canonsub (loop for x in canonsub collect (cons (cdr x) (car x)))
	;; use RASSOC
	)
  (loop for a in ans do
	(setf (soutput a)
	      (loop for x in (soutput a) collect (car (rassoc (varname x) canonsub)))
	      (wff a)
	      (map-copy-wff (wff a) 
	        :primitive-wff
		#'(lambda (rel &rest args)
		    (cons rel (loop for a in args collect
				    (or (car (rassoc (name-of-var a) canonsub)) a))))
		:quantified-wff
		#'(lambda (q qvars w)
		    (list q (loop for a in qvars collect
				  (car (rassoc (name-of-var a) canonsub)))
			  (map-wff-internal w))))
	      (sgen a)
	      (cons (list 'output (soutput a))
		       (cons
			  (list 'initialstate
				(list 'let
				      (loop for s in canonsub
					    when (eql (aref (symbol-name (cdr s)) 0) #\C)
					    unless (eq (car s) (cdr s)) ; minor opt.
					    collect
					    (if (member (car s) (soutput a)) (car s)
						(list (cdr s) (name-of-var (car s)))))
				      (cadr (assoc 'initialstate (sgen a)))))
			  (loop for x in (sgen a)
				unless (member (car x) '(output initialstate))
				collect x)))))
  ans)

(defun expandcanondesc (canon v w &aux sub)
  ; return something like canon but with real variables having same compares
  ; as in original (v s.t. w)
  (loop for cvar in (car canon) as var in v do
	(push (cons cvar (copy-variable var)) sub)
	(setf (varname (cdar sub)) cvar))
  (labels ((convert-wff (canon orig)
	   (cond ((relationp (car canon))
		  (cons (car canon) (loop for x in (cdr canon) collect
					(or (cdr (assoc x sub)) x))))
		 ((member (car canon) '(a e))
		  (list (car canon)
			(loop for x in (cadr canon) as y in (cadr orig) collect
			      (progn (push (cons x (copy-variable y)) sub)
				     (setf (varname (cdar sub)) x)
				     (cdar sub)))
			(convert-wff (third canon) (third orig))))
		 ((member (car canon) '(and or start previously start* start+ not))
		  (cons (car canon) (loop for x in (cdr canon) as y in (cdr orig)
					  collect (convert-wff x y))))
		 (t (error "shouldn't see this type of wff here")))))
    (list (mapcar #'cdr (reverse sub)) 's.t. (convert-wff (third canon) w))))

(defun adjust-permutation-if-needed (vars gen &aux (wff (wff gen)) wffvars ;template
					  )
  ;(setq template (cadr (assoc 'template (sgen gen))))
  (setf wffvars (loop for v in (cdr wff) when (member v vars) collect v))
  (or (equal vars wffvars)
      (let ((unpermuted (canonical-rel-template (car wff)
			   (loop for v in (cdr wff) collect
				 (cond ((member v vars) 'output) (t 'input)))))
	    (permuted (canonicalize-description (list vars 's.t. wff)))
	    newgen (oldgen (sgen gen)) cached)
	(setq cached (gen-cache-i-i-o permuted))
	(cond
	  ((and cached (ifleq (cadr (assoc 'effort cached))
			      (cadr (assoc 'effort oldgen)))))
	  ; strange that this should be called to get a better one than before?
	  (t
	   (when cached (gendeleter permuted cached))
	   ; evidently to ensure that old users get the new defn
	   (setq newgen
		 `(lambda (&rest inputs)
                   (declare (optimize (speed 3)(safety 1)(compilation-speed 0)))		    
		    (let (original) ; not taking any chances with compiler bugs
		      (setf original
			    (apply (load-memo (lookup-gen
						(mmemo ,(rels-to-names unpermuted))))
				   inputs))
		      #'(lambda (&aux exhausted ,.(vars-to-names wffvars))
			  (multiple-value-setq (exhausted ,.(vars-to-names wffvars))
			    (funcall original))
			  (values exhausted ,.(vars-to-names vars))))))
	   (compile-gen permuted newgen
			`((effort ,(cadr (assoc 'effort oldgen)))
			  (template ,(cadr (assoc 'template oldgen)))
			  (permutation ,permuted))))))))

(defun make-test-generator (origwff &aux wff args effort)
  (setq wff (vars&rels-to-names-wff origwff))
  ; relation names to compile to file
  (setq effort (testeffort wff))
  (cond ((compoundwffp wff)
	 (when (try (macroexpand (cons '?? wff))
		    :cannot-generate nil)
	   (make-subsetgen
	     :effort effort :size 1 :wff wff
	     :sinput (varsfreein origwff (all-vars-in-wff origwff))
	     :sgen
	     `((effort ,effort)
	       (initialstate
		 (let ((testvalue (?? ,.wff)))
		   #'(lambda nil
		       (cond (testvalue (setq testvalue nil) nil)
			     (t)))))))))
	(t ; cache-gen-if-needed
	 (dolist (arg (rest wff))
	   (declare (ignorable arg))
	   (push (gensym "A") args))
	 (when (try (macroexpand (cons '?? (cons (car wff) args)))
		    :cannot-generate nil)
	    (make-subsetgen
	     :effort effort :size 1 :wff wff
	     :sinput (remove-duplicates (remove-if-not #'variable-p (cdr origwff)))
	     :sgen
	     `((effort ,effort)
	       (template ;,(loop for arg in (cdr wff) collect 'input)
		          ,(make-list (length (rest wff)) :initial-element 'input))
	       (initialstate
		 (lambda (ignore ,@args &aux testvalue)
		   (declare (optimize (speed 3)(safety 1)(compilation-speed 0))
			    (ignore ignore))
		   (setq testvalue (?? ,@(cons (car wff) args)))
		   #'(lambda nil
		       (cond (testvalue (setq testvalue nil) nil)
			     (t)))))))))))

(declaim (special equivgen0 equivgen1))

(setq Equivgen1
      '((EFFORT 15)
	(TEMPLATE (INPUT OUTPUT))
	(INITIALSTATE
	  (LAMBDA (IGNORE A &aux state done)
	    (declare (optimize (speed 3)(safety 1)(compilation-speed 0))
		     (ignore ignore))
	    (setq state A)
	    #'(LAMBDA nil
		(COND (done) ;exhausted
		      (t (setq done t)
			 (VALUES NIL STATE))))))))

(setq Equivgen0
      '((EFFORT 15)
	(TEMPLATE (OUTPUT INPUT))
	(INITIALSTATE
	  (LAMBDA (IGNORE A &aux state done)
	    (declare (optimize (speed 3)(safety 1)(compilation-speed 0))
		     (ignore ignore))
	    (setq state A)
	    #'(LAMBDA nil
		(COND (done)
		      (t (setq done t)
			 (VALUES NIL STATE))))))))

(defun equivalencegenerators (vars wff rel subsetflg)
  (declare (special equiv-failure))
  ; we can generate x equivalent (by rel) to y if x is a variable whose
  ; compare relation is rel - either just the relation or a list of relations
  ; that are all superrels of rel (rel is guaranteed to be in the list due to
  ; this occurrence)
  (when (and (member (second wff) vars)
	     (member (third wff) vars)
	     (not subsetflg))
    (return-from equivalencegenerators nil))
  (loop for var in (cdr wff) as gen in (list equivgen0 equivgen1) 
	when (and (member var vars) #+ignore(variable-p var)
		  (or (eq rel (varcompare var))
		      bootstrapping ; can't do allsupertypes yet
		      (and (listp (varcompare var))
			   (fsubset (varcompare var) (allsupertypes rel)))
		      (null (pushnew rel equiv-failure)))) ; set it for failure msg
	collect (subfromgenerator gen vars wff)))

; translate x s.t. (p x x) into x y s.t. (and (p x y) (eq x y))
(defun generatorswitheq (vars wff subsetflg &aux newvars)
  ; transform {x s.t. (R x x)} to {x,y s.t. (and (R x y) (= x y))}
  ; not for compound wffs
  ; y should in principle be existential but it's a gensym
  (setq wff
	(cons (car wff)
	      (loop for tail on
		    (cdr wff)
		    collect
		    (cond ((not (member (car tail) vars)) (car tail))
			  ((not (member (car tail) (cdr tail))) (car tail))
			  (t (push (cons (make-variable :varname (gensym "V")
						:vartype (vartype (car tail))
						:varcompare (varcompare (car tail)))
					 (car tail))
				   newvars)
			     (caar newvars))))))
  (findgenerators
     vars
     (simplify
       `(e ,(mapcar #'car newvars)
	   (and ,wff
		,@(loop for v in newvars collect 
			(list (relationnamep (varcompare (car v))) (car v) (cdr v))))))
     subsetflg))

(defun findwffgenerators (vars wff subsetflg) ; only for compound wffs
    (cond 
      (subsetflg (subsetwffgens vars wff subsetflg))
      (t (loop for g in
	       (case
		 (car wff)
		 (not ; nots are already on the inside so give up
		  nil)
		 (or (list (orgenerator vars wff
					(loop for w in (cdr wff)
					      collect (findgenerator vars w t)))))
		 (e (cond ((null (intersection vars (cadr wff)))
			   (list (egenerator vars wff
					     (findgenerator (append vars (cadr wff))
							    (caddr wff) t))))
			  (t (fail ap5-cannot-generate
				   (list (intersection vars (cadr wff))
					 's.t. wff)))))
		 (a nil)   ; formerly a HELP
		 (and (loop for gen in (subsetwffgens vars wff nil)
			    with result
			    when (and (null (sinput gen))
				      (fsubset vars (soutput gen)))
			    when (iflessp (effort gen)
					  (and result (effort result)))
			    do (setq result gen)
			    finally (return (and result (list result)))))
		 #+ignore
		 (incx
		  (let ((g (findgenerator vars (caddr wff) t)))
		    (and g (list (make-incx-gen g (cadr wff) vars)))))
		 ; incx/prev use shortcuts that could prevent generating something
		 ; if they are not pushed inside and/or/quantifiers
		 (previously
		  (let ((g (findgenerator vars (cadr wff) t)))
		    (and g (list (make-prev-gen g vars)))))
		 ((start* start+ start) (start-generators vars wff subsetflg))
		 (t (error "~s -- bad wff syntax" wff)))
	       when g
	       collect (subfromgenerator g vars wff)))))

(defun subst-args (wff alist)
  (map-copy-wff wff
     :primitive-wff
     #'(lambda (rel &rest args)
	 (cons rel (mapcar #'(lambda (a) (or (cdr (assoc a alist)) a)) args)))))

#+ignore
(defun make-incx-gen (gen cx vars &aux (ans (copy-subsetgen gen)))
  ; *** if we ever revive this, make sure to provide an explanation with the generator
  (setf (wff ans) (list 'incx cx (wff ans)))
  (cond ((eq (caar (sgen ans)) 'test)
	 (setf (sgen ans) `((test (incx ,cx ,(cadar (sgen ans))))))
	 ans)
	((and (not (compoundwffp (wff gen)))
	      (/= (length (soutput gen))
		      (loop for x in (cadr (assoc 'template (sgen gen)))
			    count (eq x 'output)))
		  ; it's really a subset gen - we have to check some supposed outputs
	      (let ((w (wff gen)) (tem (cadr (assoc 'template (sgen gen)))) outv)
		(setq outv (loop for arg in (cdr w) as x in tem
				 when (and (member arg (soutput gen)) (eq x 'output))
				 collect arg))
		(setq gen (subfromgenerator (findgenerator outv w) outv w)))
	      nil))
	(t (setf (sgen ans) (copy-tree (remove 'output (sgen ans) :key #'car)))
	   (push (list 'output (soutput gen)) (sgen ans))
	   (let ((init (assoc 'initialstate (sgen ans))))
	     (setf (cadr init)
		   `(let ((closure (incx ,cx ,(expand-initializer1
						(soutput gen) (sgen gen) (wff gen)))))
		      #'(lambda nil (incx ,cx (funcall closure))))))
	   ans)))

(defun expand-initializer1 (vars gen wff)
  ; Gen is a real Gen, not subgen
  (cond ((compoundwffp wff) (cadr (assoc 'initialstate gen)))
	((not (zlistp wff)) (list (cadr (assoc 'initialstate gen))))
	(t `(funcall (load-memo (lookup-gen
			     (mmemo ,(rels-to-names
				       (canonicalize-description
					 (list (loop for v in vars
						     when (member v (cdr wff)) collect v)
					       's.t. wff))))))
		     ; subsetwffgen may pass more vars than appear in the wff -
		     ; in what order should they appear? - I think any order is ok as
		     ; long as it's consistent across disjuncts
		     ,.(loop for x in (cadr (assoc 'template gen))
			     as arg in (cdr wff) when (eq x 'input)
			     collect (name-of-var arg))))))

; somehow it seems this shouldn't be so hard - someday I should reexamine this
; and see if it can't be simplified

(defun make-prev-gen (gen vars &aux (ans (copy-subsetgen gen)) expl)
  (declare (ignore vars))
  (setf (wff ans) (list 'previously (wff ans)))
  ; this is not really necessary - should be obvious ...
  (if (setq expl (assoc 'explanation (sgen ans)))
      ; (explanation ((vars s.t. wff) = prog)) =>
      ; (explanation ((vars s.t. (PREVIOUSLY wff)) = (LET (DELTA) prog)))
      (setf (third (car (cadr expl))) (list 'previously (third (car (cadr expl))))
	    (third (cadr expl)) (list 'let '(delta) (third (cadr expl))))
      #+ignore ; not safe in case of (test ...)
      ; also not necessary
      (push `(explanation ((,(vars-to-names vars) s.t.
			    ,(vars&rels-to-names-wff (wff ans)))
			   = (let (delta)
			       (listof ,(vars-to-names vars) s.t.
				       ,(cadr (vars&rels-to-names-wff (wff ans)))))))
	    (sgen ans)))
  (cond ((eq (caar (sgen ans)) 'test)
	 (setf (sgen ans) `((test (previously ,(cadar (sgen ans))))))
	 ans)
	((and (not (compoundwffp (wff gen)))
	      (/= (length (soutput gen))
		  (loop for x in (cadr (assoc 'template (sgen gen))) count (eq x 'output)))
	      ; it's really a subset gen - we have to check some supposed outputs
	      (let ((w (wff gen)) (tem (cadr (assoc 'template (sgen gen)))) outv)
		(setq outv (loop for arg in (cdr w) as x in tem
				 when (and (member arg (soutput gen)) (eq x 'output))
				 collect arg))
		(setq gen (subfromgenerator (findgenerator outv w) outv w)))
	      nil)) ; continue
	(t (setf (sgen ans) (copy-tree (remove 'output (sgen ans) :key #'car)))
	   (push (list 'output (soutput gen)) (sgen ans))
	   ; don't map to name - this field is used
	   (let ((init (assoc 'initialstate (sgen ans))))
	     (setf (cadr init)
		   `(let ((closure (let (delta)
				     ,(expand-initializer1 (soutput gen)
							   (sgen gen) (wff gen)))))
		      #'(lambda nil (let (delta) (funcall closure))))))
	   ans)))

(defun start-generators (vars wff subsetflg)
  (cond
    ((or (eq (caadr wff) 'not) (relationp (caadr wff)))
     (let (tv rel args)
       (if (eq (caadr wff) 'not)
	   (setq tv nil rel (caadr (cadr wff)) args (cdadr (cadr wff)))
	   (setq tv t rel (caadr wff) args (cdadr wff)))
       (cond ((defined-p rel)
	      (let (code (def (expanded-defn rel) #+ignore (car (getdefn rel))))
		; expanded-defn does the right thing for stuff like foo#x s.t.
		(setq code
		      (try (macroexpand
			     `(loop for ,(car def) s.t.
				    (start ,(if tv (caddr def) (list 'not (caddr def))))
				    do (add-derived-to-delta
					 (theap5relation ,(relationnamep rel))
					 ,tv ,@(mapcar #'variablename (car def)))))
			   ap5-cannot-generate nil))
	     ; doesn't really use subsetflg - always computes entire thing
		(when code
		  (cache-in-delta code vars tv rel args wff subsetflg))))
	     ((nontriggerablep rel)
	      ; don't try to cache it cause it's quite likely that it can only
	      ; be partially generated!
	      (findgenerators vars
			      (simplify `(and ,(cadr wff)
					      (not (previously ,(cadr wff)))))
			      subsetflg))
	     ((derivedrel rel)
	      (cache-in-delta
		`(compute-from-triggers (theap5relation ,(relationnamep rel)) ,tv)
		vars tv rel args wff subsetflg))
	     (t (make-start-gen vars tv rel args wff subsetflg)))))
    (t (findgenerators vars (push-in-start vars (cadr wff) (car wff)) subsetflg))))

(defun cache-in-delta (code vars tv rel args wff subsetflg &aux start-gens init)
  ; code must generate ALL changes to rel (of one parity) and store them in delta 
  (declare (ignore subsetflg))
  (setq start-gens (make-start-gen vars tv rel args wff #+ignore subsetflg))
  (loop for g in start-gens do
	(setf (effort g) (+ (effort g) (effort g)))
	; worst case (first time) is probably typical
	(setq init (assoc 'initialstate (sgen g)))
	(setf (cadr init)
	      `(progn
		 (let ((entry (or (assoc (theap5relation ,(relationnamep rel))
					 indirect-computed)
				  (car (push (list (theap5relation ,(relationnamep rel))
						   nil nil)
					     indirect-computed)))))
		   (unless (,(if tv 'second 'third) entry)
		     (unless
		       (loop for upd in
			     (cdr (assoc (theap5relation ,(relationnamep rel)) delta))
			     thereis (eq ,tv (tuptv (updtuple upd))))
		       ,code)
		     (setf (,(if tv 'second 'third) entry) t)))
		 ,(cadr init))))
  start-gens)

(defun make-start-gen (vars tv rel args wff &optional subsetflg &aux g ans ;comp
			    )
  ;; how to estimate sizes??  All we can do is estimate that there
  ;; will be fewer indexed tuples than total tuples
  (when (loop for a in args always (member a vars))
    (setq g ; all tuples generator
      `((output ,args)
	(initialstate
	  (let ((updates (cdr (assoc (theap5relation ,(relationnamep rel))
				     #+ignore (memo (relationp ',(relationnamep rel)))
				     delta))))
	    #'(lambda nil
		(prog (tup)
		   loop (unless updates (return t))
		      (when (eq ,tv (tuptv (setq tup (updtuple (pop updates)))))
			(return (apply 'values nil (tupargs tup))))
		      (go loop)))))
	,(list 'effort 20))) ; trying to prevent certain list cells being read only
    (push (make-subsetgen :sgen g :soutput args
			  :effort 20 :size 10 :wff wff)
	  ans))
  (loop for a in args as i from 0 as cnc in (get-comparisons-and-canonicalizers rel)
	unless (and (member a vars) (not subsetflg))
	do
	(setq g ; gen given a
	      `((output ,(loop for a in args as j from 0 unless (= i j)
			       when (member a vars) collect a))
		(effort 10)
		(initialstate
		  (let (updates canon indexentry)
		    (when delta
		      (cond ((setq indexentry
				   (assoc (theap5relation ,(relationnamep rel))
					  #+ignore (memo (relationp ',(relationnamep rel)))
					  indexdelta))
			     (setq canon ,(cond ((listp cnc)
						 (list (cadr cnc) (name-of-var a)))
						(t (name-of-var a))))
			     (let ((hash (nth ,i (cdr indexentry))))
			       (setq updates (cdr (gethash canon hash)))))
			    (t (setq updates
				     (cdr (assoc (theap5relation ,(relationnamep rel))
						 #+ignore
						 (memo (relationp ',(relationnamep rel)))
						 delta))))))
		    #'(lambda nil
			(prog (tup)
			   loop (unless updates (return t))
			      (unless (eq ,tv (tuptv (setq tup (updtuple (pop updates)))))
				(go loop))
			      (unless (and ,.(loop for b in args ;as c in comp
						   as j from 0
						   unless (and (member b vars) (not (= i j)))
						   ; need to compare on i=j if not indexed
						   collect
						   (get-test-function
						     (get-comparison rel j t)
						     (name-of-var (nth j args))
						     `(nth ,j (tupargs tup)))))
				(go loop))
			      (return
				(values nil
				   ,. (loop for a in args as j from 0 unless (= i j)
					    when (member a vars) collect
					    `(nth ,j (tupargs tup)))))))))))
	(push (make-subsetgen :effort 10 :sinput (when (member a vars) (list a))
			      :soutput (cadar g) :size 5 :sgen g :wff wff)
	      ans))
  ans)

(defun optimize-for-no-change (subsetgen rel stored-gen &aux form tv)
  (setq form (assoc 'initialstate (sgen subsetgen))
	tv (not (eq 'not (car (cadr (wff stored-gen))))))
  (setf (cadr form)
	`(if (loop for x in (,(if tv 'car 'cdr)
			     (relevant-updates (theap5relation ,(relationnamep rel))
				       #+ignore (memo (relationp ',(relationnamep rel)))))
		   thereis (not (member x suspended-rule-classes)))
	     #+ignore ;formerly
	     (assoc (memo (relationp ',(relationnamep rel))) delta)
	     ,(cadr (assoc 'initialstate (sgen stored-gen)))
	     (if
		 (might-have-changed (theap5relation ,(relationnamep rel))
			 #+ignore (memo (relationp ',(relationnamep rel))))
		 ,(cadr form)
	       'constant-t)))
  subsetgen)

; unchanged reads the database ... in tools

(defun geneffort (gen vars body)
  (declare (ignore vars))
  ;how hard is it to generate vars s.t. body using gen (NOT Subgen!)
  (cond ((null gen) nil)			; special case
	((assoc 'effort gen) (cadr (assoc 'effort gen)))	; normal case
	; Claim: only user-supplied gens will lack an effort.  
	; Assume in this case that the whole relation can be generated
	; in 50 instructions/tuple (as stated in doc)
	(t (* 50. (relationsize (cdr body) body)))))

;; It saves a lot of work to cache relation sizes for defined relations
;; We'll have to decache these when definitions change...
(defun relsize-cache (vars wff &aux iopat)
  (setq iopat (loop for arg in (cdr wff) collect (and (member arg vars) t)))
  (cdr (assoc iopat (get-structure-property (relationp (car wff))
					    'relsize-cache)
	      :test #'equal)))

(defun add-relsize-cache (vars wff size &aux iopat)
  (setq iopat (loop for arg in (cdr wff) collect (and (member arg vars) t)))
  (push (cons iopat size)
	(get-structure-property (relationp (car wff)) 'relsize-cache))
  size)

(pushnew '(:defaultrelsize) *warning-flags*)

; Allow constants in relsize tuples; only use most specific matches.
; This should allow us to leave rels like type as notinline.
; Of course, if you want to use it both ways you should have both relsize tuples.

(defun relationsize (vars wff &aux ans size rel pat equiv-failure *fn-being-compiled*)
  (declare (special findgens-cache equiv-failure))
    ; estimate (for <Vars> s.t. <Wff> count T)
    ; (DECLARE (GLOBALVARS DefaultRelSize DefaultRelSizePats))
    (cond
      ((null vars) 1)
      ((not (listp wff)) 1)
      ((fldifference vars (varsfreein wff vars)) nil)
      ((and (setq rel (relationp (car (ilistp wff))))
	    (or (eql (length (cdr wff)) (arity* rel))
		(error "bad wff (wrong arity) - ~A" wff))
	    (loop for x in (most-specific-matches (rel-sizes rel) vars wff) with $$val
		  do ; if any rel-size tuples exist, only use rel-size
		  (progn
		    (setq $$val t)
		    (cond
		      ((iflessp
			 (setq size
			       ;(ifix ;; now allow floating size estimates ...
				 (ifexpt
				   (cadr x)
				   (/ (loop for xx in wff count (member xx vars))
				      (loop for xx in (car x)
					    count (eq 'output xx)))));)
			 ans)
		       (setq ans size))))
		  finally (return $$val)))
       ans)
      ((and rel (relsize-cache vars wff)))
      ((getdefn rel)
       (add-relsize-cache vars wff
         (relationsize (vars-to-names vars) (expanddefn wff (expanded-defn rel)))))
      ((compoundwffp wff) (compoundrelsize vars wff)
       #+ignore ; depend on FindGenerators to estimate it

       ; this stuff is not obsolete, and thus so is *in-relationsize*

       (let (v w canon)
	 (cond ((variable-p (car vars)) (setq v vars) (setq w wff))
	       (t (setq v (expanddescription (list vars 's.t. wff)
				    :allowevalargs t :keepstarts t))
		  (setq w (caddr v))
		  (setq v (car v))))
	 (setq canon (canonicalize-description (list vars 's.t. wff)))
	 ;; the following should be written with REDUCE
	 (loop for g in (let ((*in-relationsize* t)) (findgenerators v w nil))
	       #+ignore
	       (let ((entry (assoc canon findgens-cache :test 'equal)))
		 (if entry
		     (progn (setf findgens-cache (cons entry (delete entry findgens-cache)))
			    (cdr entry))
		     (findgenerators v w nil)))
	       ;usually 0 or 1, but see start...
	       with result 
	       when (iflessp (size g) result)
	       do (setq result (size g))
	       finally (return result))))  ;no expt needed - no extra vars generated
      ((not rel) (error "~s~%unknown relation for RelationSize" wff))
      (t
       (and (member :defaultrelsize *warning-flags*)
	    (not (member (setq pat (cons (car wff)
					 (loop for w in (cdr wff) collect
					       (cond ((member w vars) 'output)
						     (t 'input)))))
			 defaultrelsizepats
			 :test #'equal))
	    (push pat defaultrelsizepats)
	    (warn "No estimate for size of ~A" pat))
       (round (expt defaultrelsize
		  (/ (loop for x in (cdr wff) count (member x vars))
		     (length (cdr wff))))))))

#| This is still not fast, but a lot better than the alternative.
The problem of estimating wff sizes is still open.  This version
fails to adequately take into account the various declared sizes
of the lower level relations, e.g., asking the size of x, y s.t.
Px and Qxy where P is declared to have 20 elements and Q(in out)
declared to have 1 ought to be 20, whereas this version gives 100:
choosing the Qxy first is preferred since that gives a factor of
10 per variable rather than 20 for Px.
The other version gives 20 since the reasoning corresponds to an
algorithm.
However, not all size arguments correspond to algorithms.
Suppose the problem is x, y s.t. Pxy and Qxy, where both have
100 tuples, but P(in out) has size 1 while Q is a 10 x 10 square.  
Then the intersection could have only 10 tuples.  However, either
algorithm would generate and test 100 tuples, giving an estimated
size of (about) 100.
In summary, I now choose to settle for cheap and perhaps less
accurate estimates for the cases where none are provided.
I think it's justifiable to interpret the lack of sizes in relations
without definitions as meaning that the user doesn't really care
which algorithm is used.  This is not so clear in the case of
defined relations, where one might expect the definition to give
meaningful results.
|#

(defun compoundrelsize (vars wff)
  (ecase (car wff)
    ((start start* start+) 5)
    ((incx previously) (relationsize vars (cadr wff)))
    (or (loop for w in (cdr wff) sum (let ((x (relationsize vars w)))
				       (unless x (return nil))
				       x)))
    (e (ifquotient (relationsize (append (cadr wff) vars) (caddr wff))
		   (relationsize (cadr wff) (caddr wff))))
    (not nil)
    (a nil)
    (and (let (best-junct best-size best-vars best-exp jsize jvars exp)
	   (loop for j in (cdr wff)
		 when (setq jvars (varsfreein j vars))
		 when (setq jsize (RelationSize jvars j))
		 when (iflessp (setq exp
				     (if (<= jsize 1) jsize
					 (expt jsize (/ 1.0 (length jvars)))))
			       best-exp)
		 do (setq best-junct j best-size jsize
			  best-exp exp best-vars jvars))
	   (if (and best-vars (fldifference vars best-vars))
	       (iftimes best-size
			(compoundrelsize (fldifference vars best-vars)
					 (remove best-junct wff)))
	       best-size)))
    #+ignore
    (and (let (juncts v jsize int (n 1))
	   (loop for w in (cdr wff) do
		 (setq v (varsfreein w vars) jsize (relationsize v w))
		 (when (and jsize v)
		   (push (list (expt jsize (/ 1.0 (length v))) v jsize w) juncts)))
	   (setq juncts (sort juncts '< :key 'car))
	   (setq v vars)
	   (loop for j in juncts while v
		 when (setq int (intersection v (cadr j))) do
		 (setq n (* n (third j)))
		 (unless (= (length (cadr j)) (length int))
		   (setq n (/ n (relationsize (fldifference (cadr j) int) (fourth j)))))
		 (setq v (fldifference v (cadr j))))
	   n))))

; *** note there's NO WAY to specify a size for the constant symbols INPUT, OUTPUT
(defun most-specific-matches (templates vars pat &aux rel equivs matches)
  ; templates may now contain constants as well as the symbols input/output
  (setq equivs (loop for i below (arity* (setq rel (relationp (pop pat))))
		     collect (get-comparison rel i)))
  (loop for x in templates when
	(let ((template (car x)))
	  (and (zlistp template)
	       (zlistp pat)
	       (= (length template) (length pat))
	       (loop for x in template as y in pat as eqv in equivs
		     always (or (eq x 'output)
				(and (eq x 'input) (not (member y vars)))
				(and (not (member x '(input output)))
				     (relationp eqv)
        ;; for lists of equiv.rels perhaps we should test them all
				     (testrel eqv x y))))))
	do (push x matches))
  (loop for x in matches when ; now remove any subsumed by more specific matches
	(loop for y in matches always
	      (or (equal (car x) (car y)) ; another equal is ok
		  (not (loop for xx in (car x) as yy in (car y) always
			     ;; yy is at least as specific - const>input>output
			     (or (eq xx 'output)
				 (and (eq xx 'input) (not (eq yy 'output)))
				 (not (member yy '(input output))))))))
	collect x))


(defun testeffort (wff &aux *fn-being-compiled*)
  ; estimate effort to test Wff
  (let ((computed
	  (macrolet
	   ((error-default (real-form &rest error-forms)
	     ;;if real-form gets an error return the value of error-form
	     `(multiple-value-bind (ans err) (ignore-errors ,real-form)
				   (cond (err ,@error-forms) (t ans)))))
	    (cond
	      ((not (zlistp wff)) 1.)
	      ((compoundwffp wff)
	       (case (car wff)
		 ((not incx previously) (testeffort (cadr wff)))
		 ((start start* start+)
		  (cond
		   ((or (eq (caadr wff) 'not) (relationp (caadr wff)))
		    (let (tv rel #+ignore args)
		      (if (eq (caadr wff) 'not)
			  (setf tv nil rel (relationp (caadr (cadr wff)))
				;args (cdadr (cadr wff))
				)
			(setf tv t rel (relationp (caadr wff))
			      ;args (cdadr wff)
			      ))
		      (cond ((AND REL (defined-p rel))
			     (let ((newwff (third (car (getdefn rel)))))
			       (when (not tv)
				     (setf newwff (simplify (list 'not newwff))))
			       (testeffort (list 'start newwff))))
			    ((and REL (derivedrel rel))	; optimize this later ***
			     (* 2. (testeffort (cadr wff))))
			    (t 10))))	; look in delta
		   (t (testeffort (push-in-start nil (simplify (cadr wff))
						 (car wff))))))
		 ((or and) (loop with $$val = 0. for p in (cdr wff)
				 do (setf $$val (ifplus $$val (testeffort p)))
				 finally (return $$val)))
		 ((a e)
		  (let ((w (vars-to-names-wff (caddr wff)))
			(v (vars-to-names (cadr wff))))
		    (flet
		     ((f (v w &aux desc gen effort)
			 (#+clisp block #+clisp f #-clisp progn
			   (try (multiple-value-bind (a b c d cdesc)
						     (analyze-desc v w)
						     (declare (ignore a b c d))
						     (setf desc cdesc))
				ap5-cannot-generate (return-from f nil))
			   (if (setf effort
				     (cadr
				      (assoc 'effort
					     (setf gen
						   (gen-cache-i-i-o
						    (list (car desc) 's.t.
							  (map-copy-wff
							   (third desc))))))))
			       (ifquotient
				; pretty optimistic - imagine that first of n
				; tuples appears in 1/n'th the total time ...
				effort
				; No size stored for noncompound wffs ...
				(max 1 (or (cadr (assoc 'size gen))
					   (relationsize v w))))))))
		      ; don't divide by less than one - the fact that there are
		      ; expected to be .01 tuples does not make it cheaper
		      ; to test	whether there are any 
		      (if (eq (car wff) 'e) (f v w)
			(f v (simplify (list 'not w))))))
		  #+ignore 
		  (let ((w (caddr wff)) (v (cadr wff)))
		    (cond ((variable-p (car v)) nil)	; already expanded
			  (t (setf v (expanddescription (list v 's.t. w)
					:allowevalargs t :keepstarts t)
				   w (caddr v))
			     (setf v (car v))))
		    (let ((e1 (ifeffort (ignore-errors (findgenerator v w t))))
			  (e2 (ifeffort
			       (ignore-errors
				(findgenerator v (simplify (list 'not w)) t)))))
		      ; can generate either positive or negative
		      (cond ((iflessp e1 e2) e1) (t e2)))))
		 (t (error "~s -- bad wff syntax" wff))))
	      (t (let ((rel (relationp (car (ilistp wff)))) etuple) ;defn imp
		   (cond ((not rel)
			  (error "~A is not a wff starting with a relation ~
 			          - testeffort" wff))
			 ((setf etuple (get-testeffort rel))
			  ;; look for rel before imp
			  (error-default (apply etuple wff)
			   (warn "error computing effort for ~A ~
				  testeffort ~A - assuming 1000"
				 rel etuple) 1000))
			 ;;  minimize over all imps with testeffort
			 ((let (min effort)
			   (loop for imp in (implementations-of rel) 
				 when (setf etuple (get-testeffort imp)) do
				 (setf effort
				   (error-default (apply etuple wff)
				     (warn "error computing effort for ~A ~
					    testeffort ~A ~
					    - assuming 1000"
					   imp etuple) 1000))
				 (when (iflessp effort min)
				       (setf min effort)))
			    min))
			 #+ignore ;; single imp version
			 ((setf etuple 
				(get-testeffort
				 (or imp (setf imp (implementationof rel)))))
			  (error-default (apply etuple wff)
			   (warn "error computing effort for ~A - assuming 1000"
				 imp) 1000))
			 ((expanded-defn rel) ;(setf defn (expanded-defn rel))
			  #+ignore (testeffort (expanddefn wff defn))
			  ; changed to use the definedrel generator cache
			  (loop for g in
				(multiple-value-list
				 (apply #'definedrelgenerator nil nil rel
					(rest wff)))
				minimize (cadr (assoc 'effort g))))
			 (t ; assume we just have to generate the entire relation
			  ; perhaps we ought to find the cheapest generator
			  ; but we have to do it without calling testeffort!
			  ; I now just consider it a requirement that every rel
			  ; have a testeffort which is cheaper than any generator
			  (iftimes 50. (relationsize (cdr wff) wff))))))))))

    (if (ifleq computed 1) 1 computed)
    ;; TI has compiler bug (4/3/90 release 6) when the code reads
    ; (max 1 COMPUTED)
    ))

#| Experiment to measure the effect of different duplicate rels:
The original solution was tree-rels.
If #+nohash-dups then we arrange to never hash duplicate removal.
This is done by rebinding *MaxTreeList* to a large number, only
during duplicate relation adding.  (I don't want to change the 
other tree-rels in the system, such as generator-cache.)
|#

(defmacro create-duprel () '(createtree))

(defmacro duptester (tup rel comparisons)
  (list 'treetester tup rel comparisons))

(defmacro dupadder (tup rel comparisons)
  (list #-nohash-dups 'treeadder #+nohash-dups 'no-hash-treeadder
	tup rel comparisons))
#+nohash-dups
(defun no-hash-treeadder (tup rel comparisons &aux (*MaxTreeList* 999999))
  (treeadder tup rel comparisons))


; The object is to find <vars> s.t. Wff, where Wff is (E <vars'> <wff'>),
; Gen is generator for <append <vars> <vars'>> s.t. <wff'>
;
(defun egenerator (vars wff subgen &aux
			(compare (get-comparison-and-canonicalizer vars))
			(gen (and subgen (sgen subgen)))
			bind check)
    ; we use wff of subgen rather than caddr wff in case it was defined - then
    ; the generator expects to be used as a generator for the expanded form.
    ; keep order of vars but only those that occur
    (setq vars (loop for v in vars when (freein v wff) collect v))
    (when gen (multiple-value-setq (bind check)
	       (bindandcheck gen (append vars (cadr wff)) (wff subgen))))
    (when
     gen
      `((effort ,(effort subgen))
	(size ,(ifquotient (size subgen)  ; found in subsetwffgen
			   (relationsize (cadr wff) (wff subgen))))
	(output ,vars)
	(explanation
	  ((,(vars-to-names vars) s.t. ,(vars&rels-to-names-wff wff)) =
	   (remove-duplicates
	     (loop for ,(vars-to-names (soutput subgen)) s.t.
		   ,(vars&rels-to-names-wff (wff subgen))
		   ,@(if (assoc 'explanation gen) 
			 `((comment ,@(cadr (assoc 'explanation gen)))))
		   collect (list ,@(vars-to-names vars))))))
	(initialstate
	  (let ((filter-tree (create-duprel))
		innerpulse ,@(vars-to-names (cadr wff)))
	    (declare (ignorable ,@(vars-to-names (cadr wff))))
	    (setq innerpulse ,(expand-initializer gen (wff subgen)))
	    #'(lambda nil
		(prog (|Exhausted | |This |
		       ,@(loop for c in check collect (evalvarname (car c)))
		       . ,(vars-to-names vars))
		      (declare (ignorable . ,(vars-to-names vars)))
		 l (multiple-value-setq
		     (|Exhausted | . ,(vars-to-names bind))
		     (funcall innerpulse))
		   (cond
		     (|Exhausted | (return t))
		     ((not (and .,(loop for ch in check collect
					(check-equivalence ch))))
		      (go l))
		     ((duptester
			(setq |This |
			      (list .,(loop for v in vars as c in compare collect
					    (cond ((listp c)
						   (list (cadr c) (varname v)))
						  (t (varname v))))))
			filter-tree
			,(constant-equality-sig
			  (mapcar #'(lambda (x)(if (listp x) (car x) x))
				  compare)))
		      (go l))
		     (t (dupadder |This | filter-tree
			   ,(constant-equality-sig
			     (mapcar #'(lambda (x)(if (listp x) (car x) x))
				     compare)))
			(return (values nil . ,(vars-to-names vars))))))))))))

#+ignore ;newer version that fails due to (lisp) compiler bug
(defun orgenerator (vars wff subgens &aux
			 (compare (get-comparison-and-canonicalizer vars)) gens)
    ; find vars s.t. wff where wff is (or w1 w2 ...) and SubGens is a list of
    ; subsetgenerators (g1 g2 ...) matching the w's
    ; keep order of vars but only those that occur
    (setq vars (loop for v in vars when (freein v wff) collect v))
    (and
      (not (member nil subgens))
      (setq gens (sort (loop for w in (cdr wff) as gen in subgens
			     collect (list (effort gen) (sgen gen) w
					   (multiple-value-list
					     (bindandcheck (sgen gen) vars w))))
		       #'(lambda (x y)(iflessp (car x)(car y)))))
      ;relies on gens in same order as disjuncts
       `((effort ,(loop for g in gens sum (car g)))
	 (size ,(loop for g in subgens sum (size g)))
	 (output ,vars)
	 (initialstate
	   (let ((filter-tree (create-duprel))
		 (junct# 1)
		 (current-gen ,(expand-initializer (cadr (car gens)) (caddr (car gens))))
		 #+ignore(junct-gens (list ,@(loop for g in gens collect
					   (expand-initializer (cadr g) (caddr g))))))
	     #'(lambda nil
		 (prog (|Next | |Exhausted |
			.,(prog ((bind vars))    ; gather all the vars to bind
				(loop for g in gens
				      do (loop for b in (car (cadddr g))
					       do (pushnew b bind)))
				(return (vars-to-names bind))))
		    l  (case junct# ; branch to current disjunct
		         ,@(loop for case from 1. as g on gens collect
			         `(,case  ; get next set of values into vars
			  	   (multiple-value-setq 
				     (|Exhausted | .,(vars-to-names (car (cadddr (car g)))))
				     (funcall current-gen))
				   (cond
				     (|Exhausted |
				      ,.(when (cdr g)
					     `((setq current-gen
						     ,(expand-initializer
							(cadadr g) (caddr (cadr g)))))))
				     ((not (and .,(loop for ch in (cadr (cadddr (car g)))
							collect (check-equivalence ch))))
				      (go l))))) ;new vals exist but don't check out
		         (t (return t)))  ; if out of selectq cases, we're exhausted
	    (cond (|Exhausted | ; this disjunct done - go to next
		   (incf junct#)
		   (go l))
		  ((and (progn
			  (setq |Next |
				(list .,(loop for v in vars as c in compare collect
					      (cond ((listp c) (list (cadr c) (varname v)))
						    (t (varname v))))))
			  t) ; just an assignment
			(/= junct# 1) ;another optimization
			(duptester next filter-tree
			  ,(constant-equality-sig
			     (mapcar #'(lambda (x)(if (listp x) (car x) x))
				     compare))))
		   (go l))  ; seen it before
		  (t (or (= junct# ,(length gens))
			 ; slight optimization - don't store results of last disjunct
			 (dupadder |Next | filter-tree
			    ,(constant-equality-sig
			      (mapcar #'(lambda (x)(if (listp x) (car x) x))
				      compare))))
                     (return (values nil . ,(vars-to-names vars))))))))))))

;previous version - for use until a bug is fixed by symbolics
#+ignore
(defun orgenerator (vars wff subgens &aux
			 (compare (get-comparison-and-canonicalizer vars)) gens)
    ; find vars s.t. wff where wff is (or w1 w2 ...) and SubGens is a list of
    ; subsetgenerators (g1 g2 ...) matching the w's
    ; keep order of vars but only those that occur
    (setq vars (loop for v in vars when (freein v wff) collect v))
    (and
      (not (member nil subgens))
      (setq gens (sort (loop for w in (cdr wff) as gen in subgens
			     collect (list (effort gen) (sgen gen) (wff gen)
        ;; ** use (wff gen) instead of w because (r x x) => (e (y) (and ...))
	;; and the gen is in compound format!
					   (multiple-value-list
					     (bindandcheck (sgen gen) vars w))))
		       #'(lambda (x y)(iflessp (car x)(car y)))))
      ;relies on gens in same order as disjuncts
       `((effort ,#+ignore(loop for g in gens sum (car g))
		 (reduce #'(lambda (sum y) (ifplus sum (car y))) gens
			 :initial-value 0))
	 (size ,#+ignore(loop for g in subgens sum (size g))
	       (reduce #'(lambda (sum y) (ifplus sum (size y))) subgens
			 :initial-value 0))
	 (output ,vars)
	 (explanation
	   ((,(vars-to-names vars) s.t. ,(vars&rels-to-names-wff wff)) =
	    (union-without-duplicates
	      ,@(loop for g in gens collect
		      `(loop for ,(vars-to-names vars) s.t.
			     ,(vars&rels-to-names-wff (third g))
			     ,@(if (assoc 'explanation (cadr g))
				   `((comment ,@(cadr (assoc 'explanation (cadr g))))))
			     collect (list ,@(vars-to-names vars)))))))
	 (initialstate
	   (let ((filter-tree (create-duprel))
		 (junct# 1)
		 junct-gens) ; don't initialize it here - symbolics compiler bug ***
		 (setq junct-gens (list ,@(loop for g in gens collect
					   (expand-initializer (cadr g) (caddr g)))))
	     #'(lambda nil
		 (prog (|Next | |Exhausted |
			.,(prog ((bind vars))    ; gather all the vars to bind
				(loop for g in gens
				      do (loop for b in (car (cadddr g))
					       do (or (member b bind)
						      (push b bind))))
				(return (vars-to-names bind))))
		    l  (case junct# ; branch to current disjunct
		         ,@(loop for case from 1. as g in gens collect
			         `(,case  ; get next set of values into vars
			  	   (multiple-value-setq 
				     (|Exhausted | .,(vars-to-names (car (cadddr g))))
				     (funcall (car junct-gens)))
				   (or |Exhausted |
				       (and .,(loop for ch in (cadr (cadddr g)) collect
						    (check-equivalence ch)))
				       (go l)))) ;new vals exist but don't check out
		         (t (return t)))  ; if out of selectq cases, we're exhausted
	    (cond (|Exhausted | ; this disjunct done - go to next
		   (pop junct-gens)
		   (setq junct# (1+ junct#))
		   (go l))
		  ((duptester
		     (setq |Next |
			   (list .,(loop for v in vars as c in compare collect
					 (cond ((listp c) (list (cadr c) (varname v)))
					       (t (varname v))))))
		     filter-tree
		     ,(constant-equality-sig
			      (mapcar #'(lambda (x)(if (listp x) (car x) x))
				      compare)))
		   (go l))  ; seen it before
		  (t (or (= junct# ,(length gens))
			 ; slight optimization - don't store results of last disjunct
			 (dupadder |Next | filter-tree
			    ,(constant-equality-sig
			      (mapcar #'(lambda (x)(if (listp x) (car x) x))
				      compare))))
                     (return (values nil . ,(vars-to-names vars))))))))))))

;; this version uses CHARs rather than INTEGERS as case keys, due
;; to problems in LUCID compiler
(defun orgenerator (vars wff subgens &aux
			 (compare (get-comparison-and-canonicalizer vars)) gens)
    ; find vars s.t. wff where wff is (or w1 w2 ...) and SubGens is a list of
    ; subsetgenerators (g1 g2 ...) matching the w's
    ; keep order of vars but only those that occur
    (setq vars (loop for v in vars when (freein v wff) collect v))
    (and
      (not (member nil subgens))
      (setq gens (sort (loop for w in (cdr wff) as gen in subgens
			     collect (list (effort gen) (sgen gen) (wff gen)
        ;; ** use (wff gen) instead of w because (r x x) => (e (y) (and ...))
	;; and the gen is in compound format!
					   (multiple-value-list
					     (bindandcheck (sgen gen) vars w))))
		       #'(lambda (x y)(iflessp (car x)(car y)))))
      ;relies on gens in same order as disjuncts
       `((effort ,#+ignore(loop for g in gens sum (car g))
		 (reduce #'(lambda (sum y) (ifplus sum (car y))) gens
			 :initial-value 0))
	 (size ,#+ignore(loop for g in subgens sum (size g))
	       (reduce #'(lambda (sum y) (ifplus sum (size y))) subgens
			 :initial-value 0))
	 (output ,vars)
	 (explanation
	   ((,(vars-to-names vars) s.t. ,(vars&rels-to-names-wff wff)) =
	    (union-without-duplicates
	      ,@(loop for g in gens collect
		      `(loop for ,(vars-to-names vars) s.t.
			     ,(vars&rels-to-names-wff (third g))
			     ,@(if (assoc 'explanation (cadr g))
				   `((comment ,@(cadr (assoc 'explanation (cadr g))))))
			     collect (list ,@(vars-to-names vars)))))))
	 (initialstate
	   (let ((filter-tree (create-duprel))
		 (junct# 1)
		 junct-gens) ; don't initialize it here - symbolics compiler bug ***
		 (setq junct-gens (list ,@(loop for g in gens collect
					   (expand-initializer (cadr g) (caddr g)))))
	     #'(lambda nil
		 (prog (|Next | |Exhausted |
			.,(prog ((bind vars))    ; gather all the vars to bind
				(loop for g in gens
				      do (loop for b in (car (cadddr g))
					       do (or (member b bind)
						      (push b bind))))
				(return (vars-to-names bind))))
		    l  (case #+lucid (code-char junct#)
			     ; *** work around lucid compiler bug
			     #-lucid junct#	; branch to current disjunct
		         ,@(loop for case from 1. as g in gens collect
			         `(,#+lucid(code-char case)
				    #-lucid case ; get next set of values into vars
			  	   (multiple-value-setq 
				     (|Exhausted | .,(vars-to-names (car (cadddr g))))
				     (funcall (car junct-gens)))
				   (or |Exhausted |
				       (and .,(loop for ch in (cadr (cadddr g)) collect
						    (check-equivalence ch)))
				       (go l)))) ;new vals exist but don't check out
		         (t (return t)))  ; if out of selectq cases, we're exhausted
	    (cond (|Exhausted | ; this disjunct done - go to next
		   (pop junct-gens)
		   (setq junct# (1+ junct#))
		   (go l))
		  ((duptester
		     (setq |Next |
			   (list .,(loop for v in vars as c in compare collect
					 (cond ((listp c) (list (cadr c) (varname v)))
					       (t (varname v))))))
		     filter-tree
		     ,(constant-equality-sig
			      (mapcar #'(lambda (x)(if (listp x) (car x) x))
				      compare)))
		   (go l))  ; seen it before
		  (t (or (= junct# ,(length gens))
			 ; slight optimization - don't store results of last disjunct
			 (dupadder |Next | filter-tree
			    ,(constant-equality-sig
			      (mapcar #'(lambda (x)(if (listp x) (car x) x))
				      compare))))
                     (return (values nil . ,(vars-to-names vars))))))))))))

; this can be discarded in the near future unless we find some problems
(defvar extra-bindings nil)

(defun andgenerator (vars wff gen &aux (gens (and gen (reverse (sgen gen)))) 
		     (saved (loop for g in gens
				  when (assoc 'save (genprops g))
				  collect (cons g (gensym "GEN"))))
		     (remainingvars (soutput gen)) (label 0.) bind statevars)
  ; actually Gen is a SubsetGen, supposed to generate all vars s.t. wff
  ; since wff is conjunctive, (fetch SGen of gen) is a list of subgens.
  wff ; no longer used - get it out of generator
  ; keep order of vars but only those that occur
  (setq vars (loop for v in vars when (freein v wff) collect v))
  (setf (soutput gen) (loop for v in vars when (member v (soutput gen)) collect v))
  ; put them in the desired order!
  (and
    gen
    `((effort , (effort gen))
      (size ,(size gen))
      (initialstate
	,(unless *in-relationsize*
	 `(let (,.(setq statevars
		      (loop for g in gens unless (assoc 'test (genprops g))
			    collect (gensym "ST")))
	      (start-flg t) ,@(when saved '(saved-tables))) ,@(when saved '(saved-tables))
	  #'(lambda nil
	      (prog ,  ; (append  Vars *) is now thought to be a mistake 
		(setq bind (list '|Exhausted |))
		;; the LIST above will be nconc'd - don't replace it with a quote !
		(cond (start-flg (setq start-flg nil) (go start))
		      (t (go cont)))
		GEN0CONT
		(return t)  ;exhausted
		start
		,@(let (ans check gen1 wff1)
		    (loop for g on gens do
		      (cond
			((not (assoc 'test (genprops (car g))))
			 (setq gen1 (sgen (car g)) wff1 (wff (car g)))
			 #+ignore(push (pack* 'gen (incf label) 'start) ans)
			 (push `(setq ,(car statevars)
				      ,(let ((exp (expand-initializer gen1 wff1))
					     (v (loop for x in (cadr (assoc 'output gen1))
						      ;when (member x vars)
						      unless (member x remainingvars)
						      collect x)))
  ; *** unless some useful bindings are found this can be discarded
  ; question is whether we need (let <(vars-to-names v)> exp)
					 (cond (v (push (list vars wff v) extra-bindings)
						  exp)
					       (t exp))))
			       ans)
			 (or ;find tables that can now be saved
			   (loop for tester in (cdr g) do
			     (cond
			       ((not (assoc 'test (genprops tester))) (return t))
			       ;; that return returns from loop, not outer prog!
			       ; others to come - no cont
			       ((assoc 'save (genprops tester))
				(push
				  `(setq saved-tables
					 (cons (cons ',(cdr (assoc tester saved)) 'regenerate)
					       (delete ',(cdr (assoc tester saved))
						       saved-tables :key #'car)))
				  ans))))
			   (push 'cont ans))
			 (setq check nil)
			 (let ((lab  (pack* 'gen (incf label) 'cont)))
			   ;; while I'm here, try to avoid annoying warnings 
			   ;; about unused labels  ;; 2/2000 - DonC 
			   (push (list 'go lab) ans)
			   (push lab ans))
			 (push
			   `(multiple-value-setq
			      (|Exhausted |
			       ,@(cond
				   ((compoundwffp wff1)
				    (loop for var in (cadr (assoc 'output gen1)) collect
					  (cond ((member var remainingvars) (varname var))
						(t (push (list (make-evalvar
								 :evalvarname (gensym "CHK")
								 :evalvarcompare
								 (varcompare var))
							       (varname var))
							 check)
						   ; - - - -
						   (nconc bind
							  (list (evalvarname (caar check))))
						   ; sneaky way to get it prog bound !!!
						   (evalvarname (caar check))))))
				   (t
				    (loop for var in (cdr wff1) as pos from 0
					  as temp in (cadr (assoc 'template gen1))
					  when (eq temp 'output) collect
					  ; similar to BindAndCheck
					  (cond ((member var remainingvars) (varname var))
						((variable-p var)
						 (push (list (make-evalvar
							       :evalvarname (gensym "CHK")
							       :evalvarcompare
							       (varcompare var))
							     (name-of-var var))
						       check)
						; - - - -
						 (nconc bind
							(list (evalvarname (caar check))))
						 ; sneaky way to get it prog bound !!!
						 (evalvarname (caar check)))
						; claim next clause never happens
						(t 
						 (push (list (make-evalvar
							       :evalvarname (gensym "CHK")
							       :evalvarcompare
							       (get-comparison
								 (relationp (car wff1))
								 pos t))
							     (name-of-var var))
						       check)
						 ; - - - -
						 (nconc bind
							(list (evalvarname (caar check))))
						 ; sneaky way to get it prog bound !!!
						 (evalvarname (caar check))))))))
			      (funcall ,(pop statevars)))
			   ans)
			 (push `(cond (|Exhausted |
				       ;(pop AndState)
				       (go ,(pack* 'gen (- label 1) 'cont))))
			       ans)
			 (and check
			      (push `(or (and ,@ (loop for c in check collect
						       (check-equivalence c)))
					 (go , (pack* 'gen label 'cont)))
				    ans))
			 (setq remainingvars (fldifference remainingvars
							   (soutput (car g)))))
			((assoc 'save ; case of test and save
				(genprops (car g)))
			 (prog
			   ((s (cdr (assoc (car g) saved)))
			    (v (soutput (car g)))
			    (compare (get-comparison-and-canonicalizer
				       (soutput (car g)))))
			   (push
			     `(cond
				((eq (cdr (assoc ,(kwote s) saved-tables))
				      'regenerate)
				 (prog (tree)
				       (push (cons ,(kwote s) (setq tree (createtree)))
					     saved-tables)
				       (loop for ,(vars-to-names v) s.t.
						 ,(vars&rels-to-names-wff (wff (car g))) do
					 (treeadder
					   (list
					     ,@(loop for var in v
						     as c in compare collect
							(cond ((listp c)
							       (list (cadr c) (varname var)))
							      (t (varname var)))))
					   tree
					   ,(constant-equality-sig
					     (mapcar #'(lambda (x)(if (listp x) (car x) x))
						     compare)))))))
			     ans)
			   (push
			     `(or
				(treetester
				  (list
				    ,@(loop for var in v
					    as c in compare collect
					    (cond ((listp c)
						   (list (cadr c) (varname var)))
						  (t (varname var)))))
				  (cdr (assoc , (kwote s) saved-tables))
				  ,(constant-equality-sig
				    (mapcar #'(lambda (x)(if (listp x) (car x) x))
					    compare)))
				(go , (pack* 'gen label 'cont)))
			     ans)))
			(t  ; case of test and not save
			 (push `(cond ((?? ,.(vars&rels-to-names-wff (wff (car g)))) nil)
				      ;; rels to names for compiling to file
				      (t (go ,(pack* 'gen label 'cont))))
			       ans))))
		    (reverse ans))
                (return (values nil ,@(vars-to-names ;; remainingvars = nil now
					(soutput gen)
					#+ignore ; previously
					(fldifference vars remainingvars)))))))))
      (output ,(soutput gen) ; previously
	      #+ignore (fldifference vars remainingvars)) ; remainingvars = nil now
      (explanation
	((,(vars-to-names (soutput gen)) ; NOT vars - that includes all to be output
	  s.t. ,(vars&rels-to-names-wff wff)) =
	 ,(explain-ands vars gens (soutput gen) (soutput gen)))))))

(defun explain-ands (vars gens to-be-bound collectvars)
  (cond ((null gens) `(list ,@(vars-to-names collectvars)))
	((assoc 'test (genprops (car gens)))
	 `(when (?? ,@(vars&rels-to-names-wff (wff (car gens))))
	    ,(explain-ands vars (cdr gens) to-be-bound collectvars)))
	(t ; find all tests following this first generate
	 (let ((tail (cdr gens)) tests test-vars)
	   (loop while (and tail (assoc 'test (genprops (car tail))))
		 do (push (pop tail) tests))
	   `(loop for
	       ,(loop for out in (soutput (car gens)) collect
		      (if (member out to-be-bound)
			  (name-of-var out)
			  (cdar (push (cons (name-of-var out)
					    (pack* (name-of-var out) "-NEW"))
				       test-vars))))
	       s.t.
	       ,(sublis test-vars (vars&rels-to-names-wff (wff (car gens))))
	       ,@(if (assoc 'explanation (sgen (car gens)))
		     `((comment ,@(cadr (assoc 'explanation (sgen (car gens)))))))
	       ,@(loop for v in test-vars nconc
		       `(when (equiv ,(car v) ,(cdr v))))
	       ,@(loop for tst in (reverse tests) nconc
		       `(when (?? ,@ (vars&rels-to-names-wff (wff tst)))))
	       ,@(if tail
		     `(nconc ,(explain-ands vars tail
					    (fldifference to-be-bound
							  (soutput (car gens)))
					    collectvars))
		     `(collect (list ,@(vars-to-names collectvars)))))))))

(defun subfromgenerator (gen vars wff &aux template outvars)
  (cond ((subsetgen-p gen) gen)
        ((compoundwffp wff)
	   (make-subsetgen
	      :effort (geneffort gen vars wff)
	      :soutput (cadr (assoc 'output gen))
	      :sgen gen :size (cadr (assoc 'size gen))
	      :wff wff))
        (t (setq template (cadr (assoc 'template gen)))
	   (setq outvars
		 (loop for arg in (cdr wff)
		       as x in template when (eq x 'output)
		       when (member arg vars) collect arg))
	   (make-subsetgen
	      :effort (geneffort gen vars wff)
	      :sinput
	      (loop for arg in (cdr wff)
		    as x in template when (eq x 'input)
		    when (member arg vars) collect arg)
	      :soutput outvars :sgen gen :size
	      (or (cadr (assoc 'size gen)) (relationsize outvars wff))
	      :wff wff))))


(defvar warn-function 'warn)
(defun warn1 (&rest args)
  (apply warn-function args))
(defvar and-time-threshold 10) ; seconds 
(pushnew :compile-cost *warning-flags*)

(defvar record-and-costs nil)
(defvar record-expensive-and-costs nil)
(defvar and-cost-threshold 500)

(defun subsetandgens (vars wff subsetflg &aux
			   (possible-sub-inputs subsetflg) junct-free-vars
			   choices nodes node result (cost 0)
			   realvars  time1 time-diff shrink vs)
  (setf junct-free-vars (loop for j in (cdr wff) collect (varsfreein j vars)))
  ; if a var is in more than one junct then it can be used as input for
  ; any junct in which it appears
  (unless (eq t subsetflg)
	  (loop for j in (cdr wff) as free in junct-free-vars
		with used-once unless (eql (car j) 'not) do
		(loop for v in free do
		      (if (member v used-once) (pushnew v possible-sub-inputs)
			(push v used-once)))))
  (setf choices (loop for w in (cdr wff) as free in junct-free-vars collect
		      (cons w (findgenerators
			       (loop for v in vars when (member v free) collect v)
				; could be free but I order it as in vars to get the
				; same answers as before (for purpose of comparison)
			       w
			       (if (or (eql 'not (car w))
				       (null possible-sub-inputs))
				   t
				 possible-sub-inputs)))))
  (if (member nil choices :key #'cdr) ; no generator for some conjunct
      (return-from subsetandgens nil))

  (setq realvars (varsfreein wff vars))
  (labels ((fact (n) (cond ((= n 0) 1)(t (* n (fact (1- n))))))
	   (f (nvars nconj)
	      ; most of the cost is where the vars are split evenly among conjuncts
	      ; the order of the conjuncts is nv!, there are nc/nv choices for each
	      (cond ((= 0 nvars) 1)
		    ((= 1 nconj) 1)
		    (t (* (fact (min nvars nconj))
			  (expt (max 1 (float (/ nconj nvars))) nvars))))))
    (cond (subsetflg
	   (loop for x in (xproduct (loop for v in #+ignore realvars ; change to:
					  (if (eq subsetflg t) nil
					    (intersection realvars subsetflg))
					  collect (list nil v))) do
		 (push (make-subsetgen :sgen (cons nil choices)
				       :sinput (setq vs
						     ; (loop for y in x when y collect y) =>
						     (remove nil x)))
		       nodes)
		 (setq cost (+ cost (f (length vs) (length (cdr wff)))))))
	  (t (setq nodes (list (make-subsetgen :sgen (cons nil choices))))
	     (setq cost (f (length realvars) (length (cdr wff)))))))
  (record-and-cost cost vars wff subsetflg)
  (setq time1 (get-universal-time))
  ; sgen will be cons of actual choices and choices remaining to be made
  ; the tester was always first, this seems to make maintenance hard
  ; now we take any tester or gen with output <= 1
  (loop while (setq node (pop nodes)) do
	(setq shrink (loop for con in (cdr (sgen node)) thereis
			   (loop for g in (cdr con) thereis (iflessp (size g) 1))))
	(loop for con in (cdr (sgen node)) do
	      ;; we should really order any such shrinking gens by cost-effectiveness
	      (let (best)
		(loop for g in (cdr con) when
		      (loop for v in (sinput g) always
			    (or (member v (sinput node))
				(member v (soutput node)))) ; gen now applies
		      when (ifleq (size g) 1.0)
		      when (or (null best) (ifleq (size g) (size best)))
		      do (setq best g))
		(when best
		  (push best (car (sgen node)))
		  (setf (cdr (sgen node)) (remove con (cdr (sgen node))))
		  (setf (soutput node)
			(union (soutput node)
			       (fldifference (soutput best) (sinput node)))))))
	; note that we no longer throw in any "testers" just because all vars
	; are bound - this would make the algorithm search faster but sometimes
	; fail to find the best algorithms - note that it may be expensive to do 
	; such a test (generate a lot of stuff) whereas after later shrinking the
	; expense will diminish.
	; The argument above holds only if some generator still to be chosen has size<1
	; in many cases this is a very significant optimization
	(unless shrink
	    (loop for con in (cdr (sgen node)) with cheapest with mineffort
		  ; since all have the same union of input&output, use the first
		  when (fsubset (sinput (cadr con)) (soutput node))
		  when (fsubset (soutput (cadr con)) (soutput node))
		  do
		  (setq mineffort nil)
		  (loop for g in (cdr con) when (effort g)
			when (ifleq (effort g) mineffort)
			;; ifleq instead of iflessp in case all are nil (?)
			do (setq mineffort (effort g) cheapest g))
		  (push cheapest (car (sgen node)))
		  (setf (cdr (sgen node)) (remove con (cdr (sgen node))))))
	(cond ((null (cdr (sgen node)))
	       ;if that was all the conjuncts then save it (do subsumption)
	       (setf (wff node) wff (sgen node) (car (sgen node))
		     node (optimizeandgen node))
	       (unless (loop for a in result thereis (dominateeio a node))
		 (setf (sgen node) (andgenerator vars wff node)
		       result (cons node (delete-if #'(lambda (a) (dominateeio node a))
						    result)))))
	      (t ; try all possible next conjuncts (branch)
	       (loop for con in (cdr (sgen node)) do
		     ; find the cheapest (if any) way to generate each conjunct
		     (let (best)
		       (loop for gen in (cdr con) when
			     (loop for z in (sinput gen)
				   always (or (member z (sinput node))
					      (member z (soutput node))))
						; have enough inputs
			     when (or (null best) (ifleq (effort gen) (effort best)))
			     do (setq best gen))
		       (when best
			 (push (make-subsetgen
				 :sinput (sinput node)
				 :soutput (union (and best
						      (fldifference (soutput best)
								    (sinput node)))
						 (soutput node))
				 :sgen (cons (cons best (car (sgen node)))
					     (remove con (cdr (sgen node)))))
			       nodes)))))))
  (cond ((> (setq time-diff (- (get-universal-time) time1)) and-time-threshold)
	 (when (member :compile-cost *warning-flags*)
	   (warn1 "A conjunction took ~A seconds to compile. ~
                   See ap5::record-expensive-and-costs." time-diff))
	 (push (list time-diff vars wff subsetflg) record-expensive-and-costs))
	#+ignore
	((> cost and-cost-threshold)
	 (when (member :compile-cost *warning-flags*)
	   (warn1 " - not so bad - took ~A seconds." time-diff))))
  result)

#+ignore ; previous version
(defun subsetandgens (vars wff subsetflg)
 (let ((choices (loop for w in (cdr wff) collect (cons w (findgenerators vars w t))))
      nodes node result (cost 0) realvars vs time1 time-diff)
  (setq realvars (varsfreein wff vars))
  (labels ((fact (n) (cond ((= n 0) 1)(t (* n (fact (1- n))))))
	   (f (nvars nconj)
	      ; most of the cost is where the vars are split evenly among conjuncts
	      ; the order of the conjuncts is nv!, there are nc/nv choices for each
	      (cond ((= 0 nvars) 1)
		    ((= 1 nconj) 1)
		    (t (* (fact (min nvars nconj))
			  (expt (max 1 (float (/ nconj nvars))) nvars))))))
    (cond (subsetflg
	   (loop for x in (xproduct (loop for v in realvars collect (list nil v))) do
		 (push (make-subsetgen :sgen (cons nil choices)
				       :sinput (setq vs (loop for y in x when y collect y)))
		       nodes)
		 (setq cost (+ cost (f (length vs) (length (cdr wff)))))))
	  (t (setq nodes (list (make-subsetgen :sgen (cons nil choices))))
	     (setq cost (f (length realvars) (length (cdr wff)))))))
  (record-and-cost cost vars wff subsetflg)
  (setq time1 (get-universal-time))
  ; sgen will be cons of actual choices and choices remaining to be made
  (loop while (setq node (pop nodes)) do
	(loop for con in (cdr (sgen node))	; first take the testers
	      when (loop for v in (varsfreein (car con) vars)
			 always (or (member v (sinput node))
				    (member v (soutput node))))
	      do (push (cadr con)		; the tester is always first
		       (car (sgen node)))
	      (setf (cdr (sgen node)) (remove con (cdr (sgen node)))))
	(cond ((null (cdr (sgen node)))
	       ;if that was all the conjuncts then save it (do subsumption)
	       (setf (wff node) wff (sgen node) (car (sgen node))
		     node (optimizeandgen node))
	       (unless (loop for a in result thereis (dominateeio a node))
		 (setf (sgen node) (andgenerator vars wff node)
		       result (cons node (delete-if #'(lambda (a) (dominateeio node a))
						    result)))))
	      (t ; try all possible next conjuncts (branch)
	       (loop for con in (cdr (sgen node)) do
		     ; find the cheapest (if any) way to generate each conjunct
		     (let (best)
		       (loop for gen in (cdr con) when
			     (loop for z in (sinput gen)
				   always (or (member z (sinput node))
					      (member z (soutput node))))
						; have enough inputs
			     when (or (null best) (ifleq (effort gen) (effort best)))
			     do (setq best gen))
		       (when best
			 (push (make-subsetgen
				 :sinput (sinput node)
				 :soutput (union (and best
						      (fldifference (soutput best)
								    (sinput node)))
						 (soutput node))
				 :sgen (cons (cons best (car (sgen node)))
					     (remove con (cdr (sgen node)))))
			       nodes)))))))
  (cond ((> (setq time-diff (- (get-universal-time) time1)) and-time-threshold)
	 (warn1 "A conjunction took ~A seconds to compile." time-diff)
	 (push (list time-diff vars wff subsetflg) record-expensive-and-costs))
	((> cost and-cost-threshold)
	 (warn1 " - not so bad - took ~A seconds." time-diff)))
  result))

#+ignore ; previous previous version
(defun subsetandgens (vars wff subsetflg)
 (let ((choices (loop for w in (cdr wff) collect (cons w (findgenerators vars w t))))
      nodes node result (oldcost 1) (newcost 0) realvars vs time1 time-diff)
  (setq realvars (varsfreein wff vars))
  (loop for c in choices do (setq oldcost (* oldcost (length c))))
  (labels ((fact (n) (cond ((= n 0) 1)(t (* n (fact (1- n))))))
	   (f (nvars nconj)
	      ; most of the cost is where the vars are split evenly among conjuncts
	      ; the order of the conjuncts is nv!, there are nc/nv choices for each
	      (cond ((= 0 nvars) 1)
		    ((= 1 nconj) 1)
		    (t (* (fact (min nvars nconj))
			  (expt (max 1 (float (/ nconj nvars))) nvars))))))
    (cond (subsetflg
	   (loop for x in (xproduct (loop for v in realvars collect (list nil v))) do
		 (push (make-subsetgen :sgen (cons nil choices)
				       :sinput (setq vs (loop for y in x when y collect y)))
		       nodes)
		 (setq newcost (+ newcost (f (length vs) (length (cdr wff)))))))
	  (t (setq nodes (list (make-subsetgen :sgen (cons nil choices))))
	     (setq newcost (f (length realvars) (length (cdr wff)))))))
  (record-and-cost newcost oldcost vars wff subsetflg)
  (setq time1 (get-universal-time))
  (cond ((ifleq newcost oldcost)
	 ; sgen will be cons of actual choices and choices remaining to be made
	 (loop while (setq node (pop nodes)) do
	       (loop for con in (cdr (sgen node))  ; first take the testers
		     when (loop for v in (varsfreein (car con) vars)
				always (or (member v (sinput node))
					   (member v (soutput node))))
		     do (push (cadr con) ; the tester is always first
			      (car (sgen node)))
		     (setf (cdr (sgen node)) (remove con (cdr (sgen node)))))
	       (cond ((null (cdr (sgen node)))
		      ;if that was all the conjuncts then save it (do subsumption)
		      (setf (wff node) wff (sgen node) (car (sgen node))
			    node (optimizeandgen node))
		      (unless (loop for a in result thereis (dominateeio a node))
			(setf (sgen node) (andgenerator vars wff node)
			      result (cons node (delete-if #'(lambda (a) (dominateeio node a))
							   result)))))
		     (t ; try all possible next conjuncts (branch)
		      (loop for con in (cdr (sgen node)) do
			    ; find the cheapest (if any) way to generate each conjunct
			    (let (best)
			      (loop for gen in (cdr con) when
				    (loop for z in (sinput gen)
					  always (or (member z (sinput node))
						     (member z (soutput node))))
				    ; have enough inputs
				    when (or (null best) (ifleq (effort gen) (effort best)))
				    do (setq best gen))
			      (when best
				(push (make-subsetgen
					:sinput (sinput node)
					:soutput (union (and best
							     (fldifference (soutput best)
									   (sinput node)))
							(soutput node))
					:sgen (cons (cons best (car (sgen node)))
						    (remove con (cdr (sgen node)))))
				      nodes))))))))
	(t ; old algorithm
	 (doxproduct (choice (mapcar #'cdr choices))
	   (let (this new queue remaining easy)
	     (setq queue (list (make-subsetgen)))
	     (loop while (setq this (pop queue)) do
		   (setq remaining (fldifference choice (sgen this)))
		   (loop while
			 (setq easy
			       (loop for r in remaining thereis
				     (and	;another thereis conversion
				       (loop for z in (sinput r)
					    unless (member z (sinput this))
					    always (member z (soutput this)))
				       r)))
			 do (setf (sgen this) (cons easy (sgen this))
				  remaining (delete easy remaining)
						;alter-subsetgen
				  (soutput this) (union (soutput this)
							(fldifference (soutput easy)
								      (sinput this)))))
		   (unless remaining		;alter-subsetgen
		     (setf (wff this) wff this (optimizeandgen this))
		     (unless (loop for a in result thereis (dominateeio a this))
		       (setf (sgen this) (andgenerator vars wff this)
			     result (cons this (delete-if #'(lambda (a) (dominateeio this a))
						       result)))))
		   (when subsetflg
		     (loop for r in remaining
			   do (setq new
				    (make-subsetgen
				      :sinput
				      (nunion (copy-list (sinput this))
					      (fldifference (sinput r) (soutput this)))
				      :soutput
				      (nunion (copy-list (soutput this))
					      (fldifference (soutput r) (sinput this)))
				      :sgen (sgen this)))
			   unless (loop for q in queue
					thereis (and (feqset (sinput new) (sinput q))
						     (feqset (soutput q) (soutput new))))
			   do (push new queue))))))))
  (cond ((> (setq time-diff (- (get-universal-time) time1)) and-time-threshold)
	 (warn1 "A conjunction took ~A seconds to compile." time-diff)
	 (push (list time-diff vars wff subsetflg) record-expensive-and-costs))
	((> (cond ((ifleq oldcost newcost) oldcost)(t newcost)) and-cost-threshold)
	 (warn1 " - not so bad - took ~A seconds." time-diff)))
  result))

; G1 subsumes g2 if it covers the same conjuncts (and thus generates the same vars)
; at less cost.
; We are still not doing that much subsumption - that involves keeping old partial
; solutions (and searching thru them).
; For any given conjunct in a given situation (previously bound vars) there's
; at most one best algorithm.  This is done and cuts down the search a lot.
; A further refinement to subsetflg is that sometimes we know that certain vars
; will not be available for input - avoid asking for solutions to nonproblems.
; Example, (E (x) ...) - on the inside you HAVE to generate x.

; Full subsumption as described above gives us total work on the order of
; 2**nvars * nconj/2 - which is much less than fact(nconj) because we collapse
; ordered subsets of vars to unordered sets. For each subset of vars we have to
; generate the set of next conjuncts that could be used (and compare the costs
; of the ways to generate that subset). [e.g. 10,10 => 5K]
; Notice that this version does not even need the optimize pass since all orders
; are considered as separate algorithms.


(defun record-and-cost (cost vars wff flg)
  (setq cost (floor cost))
  (when (and (> cost and-cost-threshold) (member :compile-cost *warning-flags*))
    #+ignore (warn1 "A conjunction looks expensive to compile. ~
                 See ap5::record-expensive-and-costs.")
    (push (list (list cost) vars wff flg) record-expensive-and-costs))
  (when record-and-costs (push cost record-and-costs)))

(defun ordered-intersection (l1 l2)
  (loop for x in l1 when (member x l2) collect x))


(defun subsetorgens (vars wff subsetflg &aux disjgens ans cost1 cost2)
  (setq disjgens (loop for w in (cdr wff) collect (findgenerators vars w subsetflg)))
  (setq cost1 (apply #'* (mapcar #'length disjgens))
	cost2 (expt 2 (length vars)))
  (when (and (< and-cost-threshold (min cost1 cost2))
	     (member :compile-cost *warning-flags*))
    #+ignore
    (warn1 "A DISjunction looks expensive to compile. ~
            See ap5::record-expensive-and-costs.")
    (push (list (list cost1 cost2) vars wff) record-expensive-and-costs))
  (if (< cost1 cost2)
      (doxproduct
	(choice disjgens)
	; this algorithm might be improved some, e.g., 
	; if g1 gets x given y cheaper than g2 gets (x,y), don't combine 
	; g2 with another gen that only gets x given y.  Unfortunately,
	; that's not a large improvement and I don't think there is one.  
	; Keep in mind that intersections are necessary, 
	; e.g., x->y,z and y->x,z combine to form x,y->z.
	(let ((e 0.) (o vars) this (size 0.))
	  (loop for g in choice
		do (setq e (ifplus e (effort g))
			 o (ordered-intersection o (soutput g))
			 size (ifplus size (size g))))
	  (setq this (make-subsetgen
		       :effort e :soutput o
		       :sinput (fldifference (varsfreein wff vars) o)
		       :sgen (orgenerator o wff choice)
		       :size size :wff wff))
	  (unless (loop for a in ans thereis (dominateeio a this))
	    (setq ans (cons this (delete-if #'(lambda (a) (dominateeio this a))
					    ans))))))
      (doxproduct
	(varlist (loop for v in vars collect (list nil v)))
	(setq varlist (remove nil varlist))
	(block varlist
	  (let (choice (e 0) (o vars) (size 0))
	    (setq choice
		  (loop for d in disjgens collect
			(let (best)
			  (loop for gen in d when (fsubset varlist (soutput gen))
				when (fsubset (sinput gen) vars)
				;; possible to have an existential var here
				when (or (null best) (ifleq (effort gen) (effort best)))
				do (setq best gen))
			  (unless best (return-from varlist nil))
			  best)))
	    (loop for g in choice
		  do (setq e (ifplus e (effort g))
			   o (ordered-intersection o (soutput g))
			   size (ifplus size (size g))))
	    (unless (fsubset o varlist) (return-from varlist nil))
	    ; will be found on a more general varlist
	    (push (make-subsetgen
		    :effort e :soutput varlist
		    :sinput (fldifference (varsfreein wff vars) o)
		    :sgen (orgenerator o wff choice)
		    :size size :wff wff)
		  ans)))))
  ans)

(defun subsetwffgens (vars wff subsetflg)
  ; only for compound wffs
  ; and-all means that this is being called to do the gens for an AND where subsetflg
  ; is really nil - the algorithm is so similar that it shouldn't be duplicated
  (case
    (car wff)
    (not nil) ; nots are already on inside so give up
    (or (subsetorgens vars wff subsetflg))
    (and (subsetandgens vars wff subsetflg))
    (e (loop for subgen in
	     (findgenerators (append vars (cadr wff)) (caddr wff) subsetflg)
	     ; t => subsetflg - have to generate all the new ones
	     when (fsubset (cadr wff) (soutput subgen))
	     unless (eq (caar (sgen subgen)) 'test)
	     collect
	     (let ((out (loop for v in vars when (member v (soutput subgen)) collect v)
			; try to retain vars order for defined rels of form
			; ((y) s.t. (E (x) (R x y)))
			#+ignore (fldifference (soutput subgen) (cadr wff))) 
		   (foo (copy-subsetgen subgen))) ;from create using
	       ;alter-subsetgen
	       (setf (soutput foo) out
		     (sgen foo) (egenerator out wff subgen)
		     (size foo) (cadr (assoc 'size (sgen foo)))
		     ; since we already did it...
		     (wff foo) wff)
	       foo)))
    (a nil)    ; formerly a help
    #+ignore
    (incx 
      (loop for g in (findgenerators vars (caddr wff) subsetflg) collect
	    (make-incx-gen g (cadr wff)
			   (loop for v in vars when (member v (soutput g)) collect v))))
    (previously
      (loop for g in (findgenerators vars (cadr wff) subsetflg) collect
	    (make-prev-gen g (loop for v in vars when (member v (soutput g)) collect v))))
    ((start* start+ start) (start-generators vars wff t))
    (t (error "~s --strange Wff to generate" wff))))

#+ignore ; old version
(defun subsetwffgens (vars wff &optional and-all &aux ans)
  ; only for compound wffs
  ; and-all means that this is being called to do the gens for an AND where subsetflg
  ; is really nil - the algorithm is so similar that it shouldn't be duplicated
  (case
    (car wff)
    (not nil) ; nots are already on inside so give up
    (or (doxproduct (choice (loop for w in (cdr wff) collect (findgenerators vars w t)))
	      ; this algorithm might be improved some, e.g., 
	      ; if g1 gets x given y cheaper than g2 gets (x,y), don't combine 
	      ; g2 with another gen that only gets x given y.  Unfortunately,
	      ; that's not a large improvement and I don't think there is one.  
	      ; Keep in mind that intersections are necessary, 
	      ; e.g., x->y,z and y->x,z combine to form x,y->z.
	      
	       (let ((e 0.) (o vars) this (size 0.))
		   (loop for g in choice
			 do (setq e (ifplus e (effort g))
				  o (intersection o (soutput g))
				  size (ifplus size (size g))))
		   (setq this (make-subsetgen
				:effort e :soutput o
				:sinput (fldifference (varsfreein wff vars) o)
				:sgen (orgenerator o wff choice)
				:size size :wff wff))
		   (unless (loop for a in ans thereis (dominateeio a this))
		     (setq ans (cons this (delete-if #'(lambda (a) (dominateeio this a))
						  ans))))))
	ans)
    (and (doxproduct (choice (loop for w in (cdr wff) collect (findgenerators vars w t)))
	   (let (this new queue remaining easy)
	     (setq queue (list (make-subsetgen)))
	     (loop while (setq this (pop queue)) do
		   (setq remaining (fldifference choice (sgen this)))
		   (loop while
			 (setq easy
			       (loop for r in remaining thereis
				     (and	;another thereis conversion
				       (loop for z in (sinput r)
					    unless (member z (sinput this))
					    always (member z (soutput this)))
				       r)))
			 do (setf (sgen this) (cons easy (sgen this))
				  remaining (delete easy remaining)
						;alter-subsetgen
				  (soutput this) (union (soutput this)
							(fldifference (soutput easy)
								      (sinput this)))))
		   (unless remaining		;alter-subsetgen
		     (setf (wff this) wff this (optimizeandgen this))
		     (unless (loop for a in ans thereis (dominateeio a this))
		       (setf (sgen this) (andgenerator vars wff this)
			     ans (cons this (delete-if #'(lambda (a) (dominateeio this a))
						       ans)))))
		   (unless and-all
		     (loop for r in remaining
			   do (setq new
				    (make-subsetgen
				      :sinput
				      (nunion (copy-list (sinput this))
					      (fldifference (sinput r) (soutput this)))
				      :soutput
				      (nunion (copy-list (soutput this))
					      (fldifference (soutput r) (sinput this)))
				      :sgen (sgen this)))
			   unless (loop for q in queue
					thereis (and (feqset (sinput new) (sinput q))
						     (feqset (soutput q) (soutput new))))
			   do (push new queue))))))
	 ans)
    (e (loop for subgen in
	     (findgenerators (append vars (cadr wff)) (caddr wff) t)
	     when (fsubset (cadr wff) (soutput subgen))
	     unless (eq (caar (sgen subgen)) 'test)
	     collect
	     (let ((out (fldifference (soutput subgen) (cadr wff))) 
		   (foo (copy-subsetgen subgen))) ;from create using
	       ;alter-subsetgen
	       (setf (soutput foo) out
		     (size foo) (ifquotient (size subgen)
					    (relationsize (cadr wff) (caddr wff)))
		     (sgen foo) (egenerator out wff subgen)
		     (wff foo) wff)
	       foo)))
    (a nil)    ; formerly a help
    (incx 
      (loop for g in (findgenerators vars (caddr wff) t) collect
	    (make-incx-gen g (cadr wff)
			   (loop for v in vars when (member v (soutput g)) collect v))))
    (previously
      (loop for g in (findgenerators vars (cadr wff) t) collect
	    (make-prev-gen g (loop for v in vars when (member v (soutput g)) collect v))))
    (start ; come back and optimize this later ***
      (findgenerators vars (simplify
			     `(and ,(cadr wff)
				   (not (previously , (cadr wff)))))
		      t))
    (t (error "~s --strange Wff to generate" wff))))

(defun dominateeio (x y)
    ;subset generator X dominates Y if it takes less effort to 
    ;generate more outputs from fewer inputs
    (and (ifleq (effort x) (effort y))
	 (fsubset (sinput x) (sinput y))
         (fsubset (soutput y) (soutput x))))

(defun genwffsize (bound subgen)   ;used only in OptimizeAndGen
    ; estimate (for <Output of SubGen - bound> s.t. <Wff of SubGen> count t)
    ; i.e., if some of vars are already bound, how many tuples are expected?
    (cond ((not (loop for b in (soutput subgen) thereis (member b bound)))
	   (size subgen))
	  (t  ; oh well - tried to optimize
           (relationsize (fldifference (soutput subgen) bound) (wff subgen)))))

#| 
remaining problem:
suppose size of P(o,o)=1000, size of Q(o,o)=10
even though relationsize of the conjunction is now 10,
if Q cannot be generated, the algorithm for the conjunction
will return size 1000 - it does not notice that the test 
cannot succeed very often (test size assumed to be 1).
On the other hand, we can't very well assign test sizes
(=probabilities) independent of the domains of the inputs.
|#
(defun optimizeandgen (subgen &aux (size 1.) ans testans totalsize testg nextg g 
		       testsize testsizes (bound (sinput subgen)) (effort 0.) 
		       (remaining (reverse (sgen subgen))))
  ; subgen has as its gen a list of the gens for the conjuncts
  (setq testans (optimizetesters remaining size bound))
  (setq ans (sgen testans))
  (setq remaining (fldifference remaining ans))
  (setq effort (effort testans))
  (setq totalsize 1) ; not (size testans)
  (loop while remaining do
	(setq nextg (setq g (pop remaining)))
	(setq testg
	      (optimizetesters remaining
			       (setq testsize (genwffsize bound g))
			       (setq bound (union bound (soutput nextg)))))
	(setq testsizes
	      (sort (cons testsize
			  (loop for subgen in (sgen testg)
				when (fsubset bound (varsfreein (wff subgen) bound))
				collect (relationsize bound (wff subgen))))
		    (function iflessp)))
	(loop while (and (car testsizes) (numberp (cadr testsizes))) do
	      (rplaca testsizes     ; remember cadr > car
		      (- (car testsizes)
			 (* (car testsizes) 0.2
			    (/ (+ 0.0 (car testsizes))
			       (cadr testsizes)))))
	      (rplacd testsizes (cddr testsizes)))
	;; note this is all very weak - need extra testers for all bound
	;; ** don't rely on sizes of gen's, but on relationsize
	(setq testsize (car testsizes))
	(setq testans testg)
	(setq size testsize) ; not (size testans)
	(setq effort (ifplus effort (iftimes totalsize (effort nextg))))
	(setq totalsize (iftimes size totalsize))
	;alter-subsetgen
	(setf (genprops nextg) nil)
	(push nextg ans)
	(setq remaining (delete nextg remaining)) ;from dremove
	(setq ans (append (sgen testans) ans))
	(setq remaining (fldifference remaining (sgen testans)))
	(setq effort (ifplus effort (effort testans))))
  (make-subsetgen :effort effort :size totalsize :sgen
		  (loop for g in ans collect (copy-subsetgen g))
		  ; other attempts tend to smash the propertylist of these sgens
		  :wff (wff subgen)
		  :sinput (sinput subgen) :soutput (soutput subgen)))

#+ignore ; old version
(defun optimizeandgen (subgen &aux (size 1.) ans testans totalsize testg nextg 
		       testsize testsizes (bound (sinput subgen)) (effort 0.) 
		       (remaining (sgen subgen)))
  ;if size is given [it never is!!] it is the number of input tuples
  ; subgen has as its gen a list of the gens for the conjuncts
  (setq testans (optimizetesters remaining size bound))
  (setq ans (sgen testans))
  (setq remaining (fldifference remaining ans))
  (setq effort (effort testans))
  (setq totalsize (size testans))
  (loop while remaining do
    (progn
      (setq nextg nil)
      (loop for g in remaining
	    when (fsubset (sinput g) bound) do
	    (progn
	      (setq testg
		    (optimizetesters (remove g remaining)
				     (setq testsize (genwffsize bound g))
				     (union bound (soutput g))))
	      (setq testsizes (sort (loop for subgen in (sgen testg)
					  collect (size subgen))
				    (function iflessp)))
	      (loop while (and (car testsizes) (cdr testsizes)) do
		    (progn
		      (rplaca testsizes
			      (and (numberp (cadr testsizes))
				   (- (car testsizes)
				      (* (car testsizes) 0.2
					 (/ (+ 0.0 (car testsizes))
					    (cadr testsizes))))))
		      (rplacd testsizes (cddr testsizes))))
	      (cond ((or (null nextg)
			 (iflessp (car testsizes) testsize))
		     (setq nextg g)
		     (setq testsize (car testsizes))
		     (setq testans testg)))))
      (setq size (size testans))
      (setq effort (ifplus effort (iftimes totalsize (effort nextg))))
      (setq totalsize (iftimes size totalsize))
      ;alter-subsetgen
      (setf (genprops nextg) nil)
      (push nextg ans)
      (setq remaining (delete nextg remaining)) ;from dremove
      (setq bound (union bound (soutput nextg)))
      (setq ans (append (sgen testans) ans))
      (setq remaining (fldifference remaining (sgen testans)))
      (setq effort (ifplus effort (effort testans)))))
  (make-subsetgen :effort effort :size totalsize :sgen
		  (loop for g in ans collect (copy-subsetgen g))
		  ; other attempts tend to smash the propertylist of these sgens
		  :wff (wff subgen)
		  :sinput (sinput subgen) :soutput (soutput subgen)))

(defun optimizetesters (subgens size bound)
  (let ((testers (loop for g in subgens
			when (fsubset (sinput g) bound)
			when (fsubset (soutput g) bound)
			collect g))
	 (effort 0.) ans next)
	(loop for x in testers do (testconjunct x size))
	(loop while testers
	      ;(* find the tester with least cost/benefit where 
	      ;  benefit is reduction factor based on estimate of 
	      ; size of the expanded relation)
	      do (progn
		   (setq next
			 (loop for x in testers
			       with result with temp1 with temp2
			       when
			       (iflessp
				 (setq temp1
				       (iftimes
					 (cdr (assoc 'effort (genprops x)))
					 (cond ((fsubset bound (soutput x))
						#+ignore (min (size x) size)
						; nil possible (infinite gens)
						(if (ifleq (size x) size) (size x) size)
						#+ignore
						(round (expt (size x)
							     (/ (+ 0.0 (length bound))
								(length (soutput x))))))
					       (t size))))
				 temp2)
			       do (setq result x temp2 temp1)
			       finally (return result)))
		   (push next ans)
		   (setq testers (delete next testers))
		   (setq effort (ifplus effort
					(cdr (assoc 'effort
						    (genprops next)))))
		   (cond ((and (iflessp (size next) size)
			       (fsubset bound (soutput next))
			       #+ignore
			       (= (length bound)
				    (+ (length (sinput next))
				       (length (soutput next)))))
			  (setq size (size next))
			  (loop for x in testers do (testconjunct x size))
			  nil ;RECONSIDER ON BASIS OF NEW SIZE
			  ))))
	; just a convenient form to return - not really used as a subgen
	(make-subsetgen :effort effort :size size :sgen ans)))

(defun storecost (tuplesize)
    ; estimate cost (instructions) for store or lookup in TreeRel
    (* 50. tuplesize))

(defun testconjunct (subgen size &aux savecost
			    (regencost (iftimes size (effort subgen))))
  (declare (ignore savecost)) ; until this is fixed ...
  ;alter-subsetgen
  (setf (genprops subgen) (list '(test)))
  (cond #+ignore ;; this is buggy - can save the table one loop too soon
	;; fix it ***
    ((and
       (soutput subgen)
       (iflessp
	 (setq savecost (ifplus (effort subgen)
				(iftimes (ifplus (size subgen) size)
					 (storecost (length (soutput subgen))))))
	 regencost))
     (push (cons 'effort savecost) (genprops subgen))
     ;alter-subsetgen
     (setf (genprops subgen) (cons '(save) (genprops subgen))))
    (t (push (cons 'effort regencost) (genprops subgen)))))


(defmacro subset-gen (x) x)
;(defmacro not-subset-gen (x) x)

(defun definedrelgenerator (subsetflg origvars &rest origwff &aux vars wff2 fn
			     wff generators sub2 canon2
			    equiv-failure desc canon sub evlvars cache canonw)
  (declare (special equiv-failure) (ignore origvars subsetflg)) ; set below
  ;; only compute one pattern for everything
  (setq wff2 (cons (car origwff)
		   (loop for i below (length (rest origwff))
			 collect (pack* 'x i))))
  (setq canonw (list (cdr wff2) 's.t. (list 'subset-gen wff2)))
  (unless (setq cache (gen-cache-i-i-o canonw))
    (setq fn (or (cadr (assoc :previous-fn (gen-cache-i-i-o canonw t))) (gensym "F")))
    (setf (symbol-function fn) (symbol-function 'never-called))
    ;; since what we return has no references to the objects in vars, we can rename them.
    ; this turns out to be useful, e.g., for ((var-x) s.t. (relation var-x))
    ;; unfortunately, we don't want to keep computing for different wffs ...
    (multiple-value-setq (canon2 sub2)
      (canonicalize-description ; at least gets rid of constants
	(list (car canonw) 's.t.
	      (ExpandDefn wff2 (expanded-defn (car origwff))))))
    (multiple-value-setq (desc evlvars) 
      (expanddescription canon2
	 :allowevalargs t :keepstarts t))
    (setf vars (car desc) wff (caddr desc))
    ; don't have to worry about mismatching equivalences - such defrels are always
    ; expanded - even if in a NOTINLINE.
    (setq generators (findgenerators vars wff vars)) ;; all !! (since it's being cached)
    (setq cache
	  (loop for g in generators collect
		(let (template inputs2 args) ; gen canonc canonx
		  (setq template
			(loop for a in (car desc) collect
			      (cond ((member a (soutput g) :test
					     #'(lambda (x y)
						 (and (variable-p x)
						      (eq (varname x) (varname y)))))
				     'output)
				    (t 'input))))
		  (cond ((compoundwffp (wff g))
			 (setq inputs2 (loop for a in (cdr wff2) as b in template
					     when (eq b 'input) collect (name-of-var a)))
			 (multiple-value-setq (canon sub)
			   (canonicalize-description (list (soutput g) 's.t. wff)))
			 ;; now a bunch of stuff copied from get-generator
			 (setq args
			       (loop for s in sub when
				     (eql #\C (aref (symbol-name (cdr s)) 0))
				     collect
				     (cond ((member (car s) vars)
					    (name-of-var (car s)))
					   ((constantp* (car s)) (car s))
					   ; constantp for (listof basetype)
					   (t (caar (member
						      (cadr (assoc (car s) evlvars))
						      sub2 :key #'cdr))))))
			 ; Too bad we can't compute the generator for the wff from g -
			 ; The problem is that if any of the variables of wff2 are bound
			 ; and used more than once, the code in g just reuses them.
			 ; What we want is more general code that accepts different
			 ; arguments for which we'll just pass the same values.
			 (let ((*fn-being-compiled* fn))
			   (lookup-gen canon t)
			   (record-use-of-generator canon)) ; in case previously compiled
			 (list (list 'effort (effort g)) ; sgen won't have it if a tester
			       #+ignore ; see below
			       (list 'size (size g))
			       ;; no sense computing it over again ...
			       ;; - wrong - first, this could be the wrong estimate
			       ;; since the relation might have its own size estimates
			       ;; second, when size is computed, if this data is to be
			       ;; used it will be found in the cache
			       (list 'template template)
			       (list 'initialstate
				     `(lambda (rel ,@inputs2)
					(declare (ignore rel))
					(funcall
					  (load-memo (lookup-gen
						  (mmemo ,(rels-to-names canon))))
					  ,@args)))))
			(t (setq inputs2 (loop for a in (cdr wff2) as b in template
					       when (eq b 'input) collect (name-of-var a)))
			   (multiple-value-setq (canon sub)
			     (canonicalize-description
			       (list ;(soutput g)
				 (loop for v in vars as x in template
				       when (eq x 'output) collect v)
				 's.t. (wff g))))
			   (list
			     (list 'effort (effort g))
			     (list 'template template)
			     (list 'initialstate
				   `(lambda (rel ,@inputs2)
				      (declare (optimize (speed 3)(safety 1)(compilation-speed 0))
					       (ignore rel))
				      ;,@(mapcar #'cdr inputs2) ; in case they're not used
				      (funcall
					(load-memo (lookup-gen (mmemo ,(rels-to-names canon))))
					,.(loop for s in sub when
						(eql #\C (aref (symbol-name (cdr s)) 0))
						collect
						(if (member (car s) vars)
						    (name-of-var (car s))
						    (caar (member (cadr (assoc (car s)
									       evlvars))
								  sub2 :key #'cdr)))))))))))))
    (when *in-relationsize* (return-from definedrelgenerator (values-list cache)))
    (genadder canonw (list (list 'initialstate fn) (cons 'answer cache))))
  (values-list (cdr (assoc 'answer (gen-cache-i-i-o canonw)))))

#| ; extracted from where "too bad" comment now is above
   ; it looks like we could still save some time by doing this stuff when the problems
   ; do not arise ...
 (setq canonc (loop for s in sub when
		    (eql #\C (aref (symbol-name (cdr s)) 0))
		    collect (name-of-var (car s)))
       canonx (vars-to-names (soutput g)))
 (record-generator (car canon) (caddr canon) (size g) (effort g))
 (setq gen (gen-cache-i-i-o canon t))
 (let ((genf (cond ((null gen) (gentemp "F" ap-compiled))
		   ((eq (cadr (assoc 'initialstate gen))
			:recompile)
		    (cadr (assoc :previous-fn gen))))))
   (when genf
     (setq gen
	   (cons (list 'initialstate
		       (compile-ap
			 `(lambda (,@canonc &aux ,@canonx)
                           (declare (optimize (speed 3)(safety 1)
                                    (compilation-speed 0)))
			    ,@canonx		; see (x s.t. (relation x))
			    ,(cadr (assoc 'initialstate
					  (sgen g))))
			 genf))
		 (copy-list (remove 'initialstate gen :key #'car))))))
 (genadder canon gen))
|#

#+ignore ; old version
(defun definedrelgenerator (subsetflg origvars &rest origwff &aux vars
			    (defn (expanded-defn (car origwff))) wff generators
			    equiv-failure desc canon sub evalvars cache canonw)
  (declare (special equiv-failure)) ; set below
  (setq vars (loop for v in origvars when (member v origwff) collect v))
  (setq canonw (canonicalize-description (list vars 's.t. origwff)))
  (setq canonw (list (car canonw) (cadr canonw)
		     (list (cond (subsetflg 'subset-gen) (t 'not-subset-gen))
			   (caddr canonw))))
  (when (and (setq cache (gen-cache-i-i-o canonw))
	     ; not decached
	     (not (eq (assoc 'initialstate cache) ':recompile)))
    (return-from definedrelgenerator (values-list (cdr (assoc 'answer cache)))))
  ;; since what we return has no references to the objects in vars, we can rename them.
  ; this turns out to be useful, e.g., for ((var-x) s.t. (relation var-x))
  ;; unfortunately, we don't want to keep computing for different wffs ...
  (setq wff (vars-to-names-wff origwff))
  (multiple-value-setq (desc evalvars)
    (expanddescription
      (list (loop for v in (vars-to-names vars) when (freein v wff) collect v)
	    's.t. (ExpandDefn wff defn))
      :allowevalargs t :keepstarts t))
  (setq vars (car desc) wff (caddr desc))
  (when (and (loop for v in vars as pos in
		   (loop for y in origvars when (member y (cdr origwff))
			 collect (position y (cdr origwff)))
		   thereis
		   (not (eq (varcompare v) (get-comparison (car origwff) pos))))
	     (not (testrel rel-equivalence (car origwff))))
    ; let defined equiv-rels generate although the signature disaggrees with defn
    (return-from definedrelgenerator nil)) ; cannot generate!
  (setq generators (findgenerators vars wff subsetflg))
  (setq cache
    (loop for g in generators collect
      (let (template inputs2 vars2)
	(setq template
	      (loop for a in (cdr origwff) collect
		    (cond ((member a (soutput g)
				   :test #'(lambda (x y)
					     (and (variable-p x)
						  (eq (varname x) (varname y)))))				   
			   'output)
			  (t 'input))))
	(cond ((compoundwffp (wff g))
	       (setq inputs2 (loop for a in (cdr origwff) as b in template
				   when (eq b 'input) collect (name-of-var a)))
	       (setq vars2 (loop for v in vars as tem in
				 (loop for x in template as a in (cdr origwff)
				       when (variable-p a) collect x)
				 when (eq tem 'output) collect v))
	       (multiple-value-setq (canon sub)
		 (canonicalize-description (list vars2 's.t. wff)))
	       (list (list 'effort (effort g)) ; sgen won't have it if a tester
		     (list 'size (size g)) ;; no sense computing it over again ...
		     (list 'template template)
		     (list 'initialstate
		       `(lambda (rel ,.inputs2)
			  (declare (optimize (speed 3)(safety 1)(compilation-speed 0))
				   (ignore rel))
			  ,@inputs2 ; in case they're not used
			  (funcall (memo (lookup-gen (mmemo ,(rels-to-names canon))))
			     ,.(loop for s in sub
				 unless (variable-p (car s)) collect ;***
				 (cond ((or (constantp* (car s))
					    (member (car s) (cdr origwff)))
					(car s))
				       ((cadr (assoc (car s) evalvars)))
				       (t (error "unrecognized input ~A" (car s))))))))))
	      (t (setq inputs2 (loop for x in (cdr origwff) as z in template
				     when (eq z 'input) collect
				     (cons (name-of-var x) (gensym "G"))))
		 (multiple-value-setq (canon sub)
		   (canonicalize-description (list (soutput g) 's.t. (wff g))))
		 (list
		  (list 'effort (effort g))
		  (list 'template template)
		  (list 'initialstate
	           `(lambda (rel ,.(mapcar #'cdr inputs2))
		      (declare (optimize (speed 3)(safety 1)(compilation-speed 0))
			       (ignore rel))
		      ,@(mapcar #'cdr inputs2) ; in case they're not used
		      (funcall (memo (lookup-gen (mmemo ,(rels-to-names canon))))
			,.(vars-to-names
			    (loop for s in sub when ; constant
				  (eql (elt (symbol-name (cdr s)) 0) #\C) collect
				  (cond ((constantp* (car s)) (car s))
					((let ((temp (car s))) ; if non var
					   (and (setq temp (cadr (assoc (car s) evalvars)))
						(cdr (assoc temp inputs2)))))
					((and (variablep (car s)) 
					      (cdr (assoc (name-of-var (car s)) inputs2))))
					(t (error "~A not an input" (car s)))))))))))))))
  (genadder canonw (list (list 'initialstate 'never-called) (cons 'answer cache)))
  ;; note the cache entry is not large - the algorithm is not saved
  (values-list cache))

(defun never-called (&rest args)
  (declare (ignore args))
  (error "should never be called!"))

(defmacro do-s.t. ((vars wff &optional result-form) &body body
		   &environment env)
  (let ((do-s.t.-block (gensym "DO-ST"))
	(do-s.t.-do (gensym "DO-ST"))
	(do-s.t.-result (gensym "DO-ST")))
    (when (and vars (symbolp vars)) (setf vars (list vars))) ;; allow a symbol for unary rels
    (when (or (and (symbolp wff) (not (member wff '(true false))))
	      (descriptionp wff t))
	   (setf wff (cons wff (copy-list vars))))
    (multiple-value-bind (varnames evlvars initializer temporal)
	(analyze-desc vars wff env)
      `(block ,do-s.t.-block
	 ,(when temporal
	    `(check2states
	       (mmemo (generate ,.(list vars 's.t. wff)))))
	 (,@ (if result-form
		 `(tagbody
		    (go ,do-s.t.-do) ;; skip over result-form
		    ,do-s.t.-result
		    (return-from ,do-s.t.-block
		      ,result-form);; outside lexical scope of vars
		    ,do-s.t.-do)
		 '(progn))
	  (return-from ,do-s.t.-block
	    (do ((|Exhausted | nil)
		 (|GenFun | (let ,evlvars ,initializer))
		 ,@(mapcar #'(lambda (x) (list x nil)) varnames))
		((multiple-value-setq (|Exhausted | ,@varnames)
		   (do-pulse |GenFun |))
		 |Exhausted | ;; avoid unused variable warnings - 2/2000 DonC 
		 ,(when result-form `(go ,do-s.t.-result)))
	      (declare (ignorable |Exhausted |))
	      ,.body)))))))

#+ignore 
(defmacro do-s.t.+ (vars-wffs-result &body body  &environment env)
  (let ((do-s.t.-block (gensym "DO-ST"))
	(do-s.t.-do (gensym "DO-ST"))
	(do-s.t.-result (gensym "DO-ST"))
	exhausted genfuns
	generators
	result-form)
    (do ((tail vars-wffs-result (cddr tail)))
	((null (rest tail))
	 (when tail (setf result-form (first tail))))
      (push (gensym) exhausted)
      (push (gensym) genfuns)
      (let ((vars (first tail)) (wff (second tail)))
	(when (and vars (symbolp vars)) (setf vars (list vars)));; allow a symbol for unary rels
	(when (or (and (symbolp wff) (not (member wff '(true false))))
		  (descriptionp wff t))
	  (setf wff (cons wff (copy-list vars))))
	(push (multiple-value-list (analyze-desc vars wff env)) generators)))
      `(block ,do-s.t.-block
	 ,(when  (loop for (nil nil nil temporal) in generators
		       thereis temporal)
	    '(check2states 'do-s.t.+))
	 (,@ (if result-form
		 `(tagbody
		    (go ,do-s.t.-do) ;; skip over result-form
		    ,do-s.t.-result
		    (return-from ,do-s.t.-block
		      ,result-form);; outside lexical scope of vars
		    ,do-s.t.-do)
		 '(progn))
	  (return-from ,do-s.t.-block
	    (do (,@ (mapcar #'(lambda (v) `(,v nil)) exhausted)
	         ,@ (loop for gf in genfuns
			  as  (varnames evlvars initializer temporal)
			  in generators collect
		     `(,gf (let ,evlvars ,initializer)))
		 ,@(loop for (nil varnames) in generators nconc
			 (mapcar #'(lambda (x) (list x nil)) varnames)))
		((or
		   ,.(loop for gf in genfuns as exh in exhausted
			 as (varnames) in generators collect
			 `(multiple-value-setq (,exh ,@varnames)
			      (do-pulse ,gf)))
		   (or ,.exhausted))
		 ,(when result-form `(go ,do-s.t.-result)))
	      #+lucid (declare (ignore ,@exhausted))
	      ,.body))))))

#+ignore ;; don't bind the vars to NIL
(defmacro do-s.t. ((vars wff &optional result-form) &body body
		   &environment env)
  (let ((do-s.t.-block (gensym "DO-ST"))
	(do-s.t.-do (gensym "DO-ST"))
	(do-s.t.-result (gensym "DO-ST")))
    (when (and vars (symbolp vars)) (setf vars (list vars))) ;; allow a symbol for unary rels
    (when (or (symbolp wff) (descriptionp wff t))
	   (setf wff (cons wff (copy-list vars))))
    (multiple-value-bind (varnames evlvars initializer temporal)
	(analyze-desc vars wff env)
      `(block ,do-s.t.-block
	 ,(when temporal
	    `(check2states
	       (mmemo (generate ,.(list vars 's.t. wff)))))
	 (,@ (if result-form
		 `(tagbody
		    (go ,do-s.t.-do) ;; skip over result-form
		    ,do-s.t.-result
		    (return-from ,do-s.t.-block
		      ,result-form);; outside lexical scope of vars
		    ,do-s.t.-do)
		 '(progn))
	  (return-from ,do-s.t.-block
	    (let ((|GenFun | (let ,evlvars ,initializer)))
	      (loop 
		(multiple-value-bind (|Exhausted | ,@varnames)
		   (do-pulse |GenFun |)
		  ;; declarations fit here
		  (when |Exhausted |
		    ,(if result-form
			 `(go ,do-s.t.-result)
			 (return nil)))
		  ,.body ; with decl's stripped off
		  )))))))))

(defun decache (desc)
  (let ((d (list (car desc) (cadr desc)
		 (map-copy-wff (caddr desc))))
	g)
    (if (setq g (gen-cache-i-i-o d))
	(gendeleter d g)
	(warn "no generator for ~A cached" d))))

(defun describe-algorithm (desc &aux rel)
  (when (and (setq rel (relationp (car (third desc))))
	     (defined-p rel))
    (setf (third desc) (list 'inline (third desc))))
  (multiple-value-bind (varsx a b c cdesc)
      (analyze-desc (first desc) (third desc))
    (declare (ignore a b c varsx))
    (let ((desc cdesc) alg cache)
      (setf desc (list (first desc) (second desc) (map-copy-wff (third desc))))
      #+ignore
      (when (or (null (first desc)) (relationp (car (third desc))))
	(return-from describe-algorithm nil))
      (cond ((setf alg (cadr (assoc 'explanation (setq cache (gen-cache-i-i-o desc))))))
	    ((not (relationp (car (third desc))))
	     (decache desc)
	     (lookup-gen desc)
	     (setf alg (cadr (assoc 'explanation (setf cache (gen-cache-i-i-o desc)))))))
      (when (assoc 'effort cache)
	(setf alg (append alg (list :cost (cadr (assoc 'effort cache))))))
      (if (assoc 'size cache)
	  (setf alg (append alg (list :size (cadr (assoc 'size cache)))))
	  (setf alg (append alg (list :size (relationsize (car desc) (third desc))))))
      alg)))

;; useful lower level function - for server ...
(defun generator-init-fn (rel-or-desc template &aux args desc)
  ;; return a string in the case of an error, a fn otherwise
  (setf args (loop for temp in template collect
		    (if (eq temp 'output) (gensym "X") 'input))
	desc (list (remove 'input args) 's.t. (cons rel-or-desc args)))
  (try (multiple-value-bind
	 (varnames evlvars initializer temporal cdesc)
	   (analyze-desc (car desc) (third desc))
	 (declare (ignore varnames evlvars initializer temporal))
	 (lookup-gen cdesc))
       ap5-cannot-generate ;; expanddescriptions translate into cannot-gen's
       (return-from generator-init-fn
	 (format nil "Cannot generate ~A" tryvalue))))


(defstruct (rel (:conc-name nil)
		(:constructor make-rel (tester generators defn))
		(:print-function printrel))
	   tester generators defn)

(defun printrel (relation stream depth)
  (declare (ignore depth))
  (format stream "#<relation ~A>" (defn relation)))

(defun pat-to-int (pat)
  (if (integerp pat)
      pat
      (let ((p 0))
	(loop for x in pat as n from 0
	  when (eq x 'input)
	  do (setf p (dpb 1 (byte 1 n) p)))
	p)))

(defmacro relation (definition &key test
		    (generate nil gen-s)
		    &environment environment
		    &aux arity)
  (unless (or test generate (null gen-s))
    (error "the relation ~A will be entirely useless ~
	    unless some keyword arguments are provided" definition))

  (multiple-value-bind (body evlvars evlrels)
      (unless (relationp definition)
	(ExpandDescription definition
			   :allowevalargs t
			   :keepstarts t :environment environment))
    (setf arity (if (consp definition)
		    (length (first definition))
		    (arity* (relationp definition))))
    (when evlrels (error "funcall/apply not allowed in (relation ...)"))
    `(progn
       ,(when (and body (temporalp (third body)))
	  `(check2states (mmemo (relationp ,definition))))
       (make-rel
	 ,(when test (if body
			 `(let ,evlvars
			    #'(lambda ,(mapcar #'varname (first body))
				(?? ,.(vars&rels-to-names-wff (third body)))))
			 `#',(get-tester (relationp definition))))
	 (list ,.(loop for pat in (or generate (unless gen-s '(0)))
		       nconc
		       (let ((p (pat-to-int pat)))
			 (list p
			     (if body
				 (multiple-value-bind (varnames evlvars2 initializer)
				     (analyze-desc
				       #+ignore
				       (loop for p in pat as a in (car body)
					     when (eq p 'output) collect (varname a))
				       (loop for i below arity as a in (car body)
					     unless (logbitp i p)
					     collect (varname a))
				       (vars-to-names-wff (third body)))
				   (declare (ignore varnames))
				   `(let ,evlvars
				      #'(lambda ,#+ignore
					         (loop for p in pat as a in (first body)
						       unless (eq p 'output)
						       collect (varname a))
						 (loop for i below arity as a in (first body)
						       when (logbitp i p)
						       collect (varname a))
					  (let ,evlvars2 ,initializer))))
				 (loop with bit and var for i below arity
				       do (setf bit (logbitp i p)
						var (gensym))
				       collect var into args
				       when bit
				       collect var into inputs
				       else collect var into outputs
				       finally (return `#'(lambda ,inputs
							    ,(get-generator `(,outputs s.t. (,definition ,. args)))))))))))
	 ',definition))))

(defun initialize-generator (rel pat &rest inputs)
  (apply (or (getf (generators rel) pat)
	     (error "~A does not support ~A generation" rel pat))
	 inputs))

#+ignore ; #+(or symbolics ti allegro)
(pushnew '(s.t.* loop-for-s.t.*) loop-for-keyword-alist :test #'equal)

#+ignore ; #+(or symbolics ti allegro)
(defun loop-for-s.t.* (vars rel&args datatypes &aux pulser pat)
  (unless (listp vars) (setf vars (list vars)))
  (loop for v in vars unless (eq v (variablename v)) do
	(warn "no types/equivalences allowed for s.t.* variables"))
  (setq pat (loop for arg in (cdr rel&args) collect
		  (if (member arg vars) 'output 'input)))
  (when (loop for v on vars thereis (member (car v) (cdr v)))
    (error "s.t.* variables must be distinct"))
  (unless (= (length vars) (count 'output pat))
    (error "every s.t.* variable must occur once as an argument"))
  (loop-make-iteration-variable  vars nil datatypes)
  (loop-make-iteration-variable '|Exhausted | nil nil)
  (loop-make-iteration-variable '|GenFun |
        `(initialize-generator ,(car rel&args) ,(pat-to-int pat)
	       ,.(loop for arg in (cdr rel&args) as p in pat
			  when (eq p 'input) collect arg))
	nil)
  (setq pulser `(multiple-value-setq
		  ,(cons '|Exhausted |
			 ; not vars in case they're in another order
			 (loop for arg in (cdr rel&args) as p in pat
			       when (eq p 'output) collect arg))
		  (do-pulse |GenFun |)))
  ; eachtime {pretest steps posttest pseudo} firsttime {pretest ...}
  (list nil nil pulser nil nil nil pulser nil))

(defun test (rel &rest args)
  (apply (or (tester rel)
	     (error "~A does not support testing" rel))
	 args))
