;-*- Mode:LISP; Package:AP5; Base:10.; Syntax:Common-Lisp -*-

(in-package "AP5")

#| added 1/97: anonymous relations
 Just as a desc is allowed in place of a relation (but only in a wff),
 we now allow (anon-rel . def) as a relation, both in wffs and in
 the derivation idioms that accept relation names as arguments
 (tclosure, sum, cardinality, extreme)
 where def could be the cddr of a defrelation form (after a name).
|#

;; we try to share anon rels with equal descriptions
(defvar *anon-rel-table* (make-hash-table :test #'equal))

;; moved to first use in sys-depend: (defvar *in-anon-rel-context* nil)
;; we have to be prepared to define the relation in a compile-file,
;; and this can be done only in certain contexts ...

;; (defmacro anon-rel ...) moved to much later (defrel)
;; it uses ?? maintainedrel, never used in ap5

(defun make-rel-anonymous (rel def)
  (put-structure-property rel def :anonymous-def)
  (setf (gethash def *anon-rel-table*) rel))

;; allow any macros, not just non-rel, as long as they expand to rels
(defun relationp+ (x)
  ;; maybe even remove listp and allow symbol-macros?
  (when (listp x) (setf x (macroexpand x)))
  (relationp x))

;; ==== 

(defstruct (variable ; :named
		     (:conc-name nil)
		     (:print-function print-variable))
	   varname vartype varcompare varcompare-P)

(defun print-variable (variable stream depth)
   (declare (ignore depth))
   (format stream "Var-~A" (varname variable)))

(defmethod #+lucid clos::make-load-form #-lucid make-load-form
  ;;#-(or lispworks allegro) ((var variable))
  ;;#+(or lispworks allegro) ((var variable) &optional env)
  ;;#+(or lispworks allegro) (declare (ignore env))
  ((var variable) &optional env) (declare (ignore env))
  ;`(make-variable :varname ',(varname var))
  (error "should never write VARIABLE to compiled file"))

(defstruct (evalvar ; :named
	     (:conc-name nil)
	     (:print-function print-evalvar))
  evalvarname evalvarcompare)

(defun print-evalvar (evalvar stream depth)
   (declare (ignore depth))
   (format stream "EvalVar-~A" (evalvarname evalvar)))

;; (constant x) is just like x, but declares that the value computed by x will
;; be EQ constant over all executions
(defmacro constant (form) form)

(defun constantp* (x &key (equiv 'eql) (env *empty-env*))
  ;;; really want EQUIV to be an equivalence relation, but I don't know enough
  ;;; about the bootstrapping to know what is safe to put here as the default
  ;;; What AP5 needs to be asking is whether an expression is guaranteed to evaluate to
  ;;; a "representive" of the SAME equivalence class the one for the slot of the relation
  ;;; in which it appears.  My concern is that the CL spec says that
  ;;; a compiler is only required to preserve EQLness (not EQness) on constants.
  ;;; Of course, this also opens up the possibility of a subtle dependency of
  ;;; a rule getting asserted using a constant in the trigger, and LATER the
  ;;; equivalence class for that slot changes so that, in effect, the constant-hood
  ;;; no longer holds.  We can probably live without catching this, or maybe
  ;;; our current decaching on EQUIV class changes is course enough that it gets
  ;;; rechecked anyway?? (I doubt it).
  ;;; N.G. 7/9/87

  (declare (ignore equiv))
  ; the commonlisp version is almost but not quite what I want ...
  (or #+ignore ;;; taken care of by first macroexpansion
      (let ((unmx (labels ((unmacroexpand (form)
 			     (if (and (consp form)
				      (eq (car form) *displaced-macro-marker*))
				 (unmacroexpand (cadr form))
				 form))))
			(unmacroexpand x)))
	(and (consp unmx) (member (car unmx) '(memo load-memo))))
      (and (consp x) (member (car x) '(quote memo load-memo theap5relation)))
       ;; THEAP5RELATION has to be known because in some cases
       ;; this function is applied to (theap5relation foo) BEFORE
       ;; foo is really a relation (in the definition of a basetype, at least)
  
      (and (constantp x)
	   (not (variable-p x))
	   (not (evalvar-p x)))
      (and (consp x) (or (eq (first x) 'constant)
			 ;(eq (first x) 'quote-smashable)
			 ))
      (and (consp x)
	   (multiple-value-bind (expanded err) (ignore-errors (macroexpand-1 x env))
	     (unless (or err (eq x expanded)) (constantp* expanded :env env))))))

#+ignore 
(defun alphalessp (x y)
  (string-lessp (princ-to-string x)
		(princ-to-string y)))

(defun arbitrary-compare (x y)
  (eq :less (arbitrary-order x y)))

(defun arbitrary-order (x y)
;;; NIL < other symbols < strings  < numbers < dbobjects
  ; < vars <evalvars < other atoms < lists
  (cond ((eql x y) :equal)
	((null x) :less)
	((null y) :greater)
	((symbolp x)
	 (if (symbolp y) (string-or-symbol-order x y) :less))
	((symbolp y) :greater)
	((stringp x)
	 (if (stringp y) (string-or-symbol-order x y) :less))
	((stringp y) :greater)
	((numberp x)
	 (if (numberp y)
	     (if (= x y) :equal (if (< x y) :less :greater))
	   :less))
	((numberp y) :greater)
	((dbobject-p x)
	 (if (dbobject-p y) (dbobject-order x y)))
	((dbobject-p y) :greater)
	((variable-p x)
	 (if (variable-p y) (string-or-symbol-order (varname x) (varname y))
	   :less))
	((variable-p y) :greater)
	((evalvar-p x)
	 (if (evalvar-p x) (string-or-symbol-order
			    (evalvarname x) (evalvarname y))
	   :less))
	((evalvar-p y) :greater)
	((atom x) (if (atom y) :equal :less))
	((atom y) :greater) ;; else x and y are both cons cells
	(t (let ((car-o (arbitrary-order (car x) (car y))))
	     (if (eq :equal car-o) (arbitrary-order (cdr x) (cdr y)) car-o)))))

(defvar dbobject-id 0)

(defun dbobject-order (x y)
  (declare (special dbobject-id))
  (let ((xx (or (get-structure-property x 'unique-id)
		(put-structure-property x (incf dbobject-id) 'unique-id)))
	(yy (or (get-structure-property y 'unique-id)
		(put-structure-property y (incf dbobject-id) 'unique-id))))
    (if (< xx yy) :less
      (if (> xx yy) :greater :equal))))

(defun string-or-symbol-order (xx yy &aux 
				  (x (string xx)) (y (string yy))
				  (where (string/= x y)))
  (if where 
      (cond ((= where (length x)) :less)
	    ((= where (length y)) :greater)
	    ((char< (char (string x) where) (char (string y) where)) :less)
	    (t :greater))
    :equal))

(defun boundsymbollist (varlist)
    (cond ((null varlist) t)
	  ((or (not (zlistp varlist))
	       (loop for a in varlist thereis (not (symbolp a)))
	       (loop for a on varlist thereis (member (car a) (cdr a))))
	   nil)
          (t t)))


; names are of the form type#name@equiv (any # must come before any @)
; if there's no # then there's no type (== type=entity)
; if there's # is at the end or just before @ then name=type
; if there's no @ then there's no equiv
; any combination is possible except none and only an equivalence, i.e.,
;  either type or name must be supplied
(Defun parse-var (symbol &aux (name (symbol-name symbol)) index tname ename
		  (pkg (symbol-package symbol)))
  (when (setq index (position #\# name))
    (setq tname (intern (subseq name 0 index) pkg)
	  name (subseq name (1+ index))))
  (when (setq index (position #\@ name))
    (setq ename (intern (subseq name (1+ index)) pkg)
	  name (subseq name 0 index)))
  (cond ((= (length name) 0) (setq name tname))
	((or ename tname) (setq name (intern name pkg)))
	(t (setq name symbol))) ; if we get a gensym don't make a copy!!
  (values name tname ename))

; The variable registry records the declared type of a variable and its comparison
; relation - if the variable is only used in equivalence relations, this is a list
; of the comparison relations (meaning intersection of the rels).  
; If referencevar
; is called, the var is not just being introduced, but used, in which case we
; have to check any new info against the old (and add it).  Comparison will be
; either an equivalence relation (relation object) or a list of such (nil in the
; case of a variable introduction).
;
; perhaps we have to make this accept (already digested) variables?
; for the cases where relations are to be eval'd at runtime
; instead we will just translate the vars back into names.

; - when a var is introduced, its comparison is not yet known - establishvar is called
(Defun EstablishVar (origvar &aux var type tname eqv ename)
  (unless (symbolp origvar) ; such as ((1) s.t. (R 1))
      (error "attempt to use a non-symbol ~s as a variable" origvar))
  (multiple-value-setq  (var tname ename) (parse-var origvar))
  (unless (or (null tname) (eq 'entity tname)
	      (setf type (relationp tname))
	      (when (cl-type-name tname) (setf type tname)))
    (let ((r (check-relation-package-error tname 1)))
      (when (eq r tname) ;; no alternative
	(error "~S is not the name of a type" tname))
      (setf tname r type (relationp r))))
  (unless (or (null ename) (setf eqv (relationp ename)))
    (let ((r (check-relation-package-error ename 2)))
      (when (eq r ename) ;; no alternative
	(error "~S is not the name of a binary relation" ename))
      (setf ename r eqv (relationp r)))
    (unless (equivalence-relp eqv) (error "~A is not an equivalence relation" eqv)))
  (when (constantp var) 
    (error "~A is used as a variable but is a constant!" var))
  (make-variable :varname var :vartype type
		 :varcompare eqv :varcompare-P (when eqv t)))

; - when an occurrence of var does not constrain the equivalence relation used
;   - either due to an AnyComparison declaration or the occurrence is in a defined
;   rel, we want to translate the name into the
;   already existing var, but add no new comparison info - comparison is T
; - when a var is used in a relcall/relapply wff we treat it like T except that
;   in the end we shouldn't be upset if it turns out not to have any comparison
; - when a var is used otherwise we translate name to var and add compare info
;   comparison is either an equiv rel or (if this use is an equiv rel) a list
;


(Defun ReferenceVar (origvar comparison varlist &aux var type tname ename entry)
  
  (multiple-value-setq  (var tname ename) (parse-var origvar))
  (when (setf entry  (find var varlist :key #'varname))
    (when (or tname ename)
      (warn "~A is interpreted as referring to the variable ~A" origvar var)
      (setf tname nil ename nil))
    (when (and (Vartype Entry) Type (Not (Eql (Vartype Entry) Type)))
	 (Fail Expanddescription "Multiple Types Declared For" Var))
    (cond ((eq comparison t))			; just return the var
	  ((eq comparison :funcall)
	   (or (varcompare entry) (setf (varcompare entry) :funcall)))
	  ((eq (varcompare entry) :funcall) (setf (varcompare entry) comparison))
	  ((and (listp (varcompare entry)) (listp comparison))
	   (setf (varcompare entry) (append (varcompare entry) comparison)))
	  ((and (not (listp (varcompare entry))) (not (listp comparison)))
	   (cond ((eql comparison (varcompare entry)))
		 (t (fail ExpandDescription "incompatible comparison relations"
			  var (varcompare entry) comparison))))
	  ((listp comparison)
	   (setf (varcompare entry)
		 (check-comparison (varcompare entry) comparison var)))
	  (t (setf (varcompare entry)
		   (check-comparison comparison (varcompare entry) var))))
    entry))

(defun Check-Comparison (Rel Rels var)
  (if (or bootstrapping (null rels)
	  (and (eq rel (first rels))
	       (null (rest rels)))
	  (subsetp Rels (allsupertypes rel)))
      Rel
      (fail ExpandDescription "incompatible comparison relations"
		 var rel rels)))

(declaim (inline VariableName VariableTypeName VariableNameandType))
;; looks like there are actually used (see macros)
(Defun VariableName (x) (values (parse-var x)))

(defun VariableTypeName (x)
  (multiple-value-bind (a b c) (parse-var x)
    (declare (ignore a c)) b))
(Defun VariableNameandType (x)
  (multiple-value-bind (a b c) (parse-var x)
    (declare (ignore c)) (values a (or b 'entity))))

(defun translate-functions (wff &optional (environment *empty-env*))
  ;; handles uses of "?", "$", and "=" as args of primitive wffs
  (map-copy-wff wff
     :environment environment
     :primitive-wff
     #'(lambda (rel &rest args)
	 (declare (special inline?))
	 (multiple-value-bind (ans conjuncts e-vars result-vars)
	     (analyze-functions rel args environment)
	   (when result-vars
	     (error "cannot have a result(?) in a non-expression wff -- ~a"
			      (cons rel args)))
	   (when inline? (setf ans (list inline? ans)))
	   (when conjuncts (setf ans (cons 'and (cons ans conjuncts))))
	   (when e-vars (setf ans (list 'e e-vars ans)))
	   ans))))

(defun analyze-functions (relation args environment
			      &key (e-arg-name "$")
			      (result-arg-name '("~" "?"))
			      (link-arg-name "=")
			      &aux e-vars result-vars conjuncts )
  (labels
    ((arg-p (x which)
       (and (symbolp x)
	    (let ((v (variablename x)))
	    (if (stringp which)
		(symbolname which v)
	      (loop for s in which thereis (symbolname s v))))))
     (new-var (arg &aux gen pkg)
       (multiple-value-bind (vname tname ename) (parse-var arg)
	 (declare (ignore vname))
	 (setf pkg (cond (tname (symbol-package tname))
			 (ename (symbol-package ename))
			 (t *package*)))
	 (when (eql pkg '#.(find-package "LISP"))
	   ;; can't intern in the LISP package, but AP5 is safe because
           ;; it uses LISP
	   (setf pkg (find-package "AP5")))
	 (setf gen (gentemp "X" pkg))
	 (values gen
		 (intern
		   (concatenate 'string
				(if tname
				    (concatenate 'string (symbol-name tname) "#")
				    "")
				(symbol-name gen)
				(if ename
				    (concatenate 'string "@" (symbol-name ename))
				    ""))
		   pkg))))
     (expand-it (arg)
       (multiple-value-bind (expansion macp)
		  (macroexpand-1wff arg environment)
	 (if macp (process-arg expansion) arg)))
     (process-arg (arg &aux rel tail arity)
       (cond ;((constantp* arg :env environment) arg) - moved down ...
	     ((arg-p arg e-arg-name)
	      (multiple-value-bind (new-arg new-var) (new-var arg)
		(push new-var e-vars) new-arg))
	     ((arg-p arg result-arg-name)
	      (multiple-value-bind (new-arg new-var) (new-var arg)
		(push new-var result-vars) new-arg))
	     ((arg-p arg link-arg-name)
	      (error "A ~A may not appear in a non-nested wff -- ~a"
		     link-arg-name (cons relation args)))
	     ((and (listp arg)
		   (setf arg (macroexpand-to-wff arg))
		   ;; --- above for wffmacros -- still have to expand to
		   ;; (rel ...), not a compound wff! - e.g., ok for card
		   (or (and (setf rel (relationp+ (first arg)))
			    (<= (length (rest arg)) (setf arity (arity* rel))))
		       (and (cl-type-name (first arg) environment)
			    (<= (length (rest arg)) (setf arity 1)))
		       (and (descriptionp (first arg))
			    (<= (length (rest arg)) (setf arity (length (caar arg)))))))
	      ;;a wff
	      (cond ((setf tail (member-if #'(lambda (x) (arg-p x link-arg-name))
						(rest arg)))
		     ;; an intended link
		     (when  (member-if #'(lambda (x) (arg-p x link-arg-name))
				       (rest tail))
		       (error "multiple ~a's in a nested wff -- ~a" link-arg-name arg))
		     (when (member-if #'(lambda (x) (arg-p x result-arg-name))
				      (rest arg))
		       (error "cannot have both a ~A and ~A in the same nested wff -- ~a"
			      link-arg-name result-arg-name arg))
		     ; a legitimate link
		     (multiple-value-bind (new-arg new-var)
			 (new-var (first tail))
		       (push new-var e-vars)
		       (push (cons (first arg)
				   (mapcar #'(lambda (x) (process-arg x))
					   (let ((t1 (substitute new-arg (first tail)
						       (rest arg)
						       :count 1)))
					     (if (< (length (rest arg)) arity)
						 (append t1
						   (loop for i below
							 (- arity (length (rest arg)))
							 collect
							 (intern e-arg-name
								 (find-package "AP5"))))

						 t1))))
			     conjuncts)
		       new-arg))
		    (t (expand-it arg))))
	     ((constantp* arg :env environment) arg) ; can cause macroexpansion ...
	     (t (expand-it arg)))))
    (values (cons relation (mapcar #'(lambda (x) (process-arg x)) args))
	    conjuncts
	    (nreverse e-vars)
	    (nreverse result-vars))))

(defvar-resettable all-inline? nil)
(defvar sort-juncts t)
(defvar *no-package-correction* nil) 

; Takes input of the form (vars s.t. wff) and returns a similar thing with
; all definitions and macros expanded, all variables changed to variable objects, 
; with types and comparison relations incorporated.
; This is used by: rule compiler, defined-relation expander, insist, ??, generator.
; The last 3 cases allow runtime expressions both as relations and arguments.
; In the case of relations this has to be recognized even before expansion.
; In the case of arguments, we use AllowEvalArgs to mean just let them through.
; Now this also takes the place of EvalPattern and EvalRels - the results of
; those are the 2nd and 3rd values.
;
;; ExpandDescription is also called by Descriptionp with descriptionp = T.
;; In this case, it only needs to return a boolean (or error)

;; If SOURCE-EXPANSION is non-nil,  embedded lisp expressions are left in place,
;; relation names are NOT replaced by relation objects, and variable names are 
;; NOT replaced by variable objects.  Translate-Functions processing is still
;; performed, and variables with #type or @equivalence are still expanded.

(defun ExpandDescription
 (d &key AllowEvalArgs KeepStarts descriptionp source-expansion
			  (sort-juncts t) dont-warn-for-false
			  (environment *empty-env*)
			  (leave-constants-embedded t)
			  &aux
			  ; delta ; do it all in prev. state?
			  ; no - (atomic <define rel> reveal <use rel>)
			  tcforms varlist evalvars evalrels
			  (wff (third d)) (args (first d))
			  (*no-package-correction* descriptionp))
  (declare (special KeepStarts sort-juncts ;both used by SIMPLIFY
		     ))
  (unless (listp args)
    (when descriptionp (return-from expanddescription nil))
    (error "description variable list is not a list ~s" d))
    
  (labels ((boundvarlist (varlist)
	     (loop for a on varlist
		   never (member (car a) (cdr a) :key #'varname)))
	   (make-type-check-forms (vars temp-p)
	     (loop for v in vars when (vartype v)
		collect (expandwff (list (or (relationnamep (vartype v))
					     (vartype v)) ; for cl-type-name's
					 (varname v))
				   (list v) temp-p)))
	   (ExpandWff (Wff *varlist* *temporalp*)
	     (declare (special
			*varlist*
			;; bound vars visible to current WFF
			;; when multiple vars with the same varname are in
			;; *varlist*, only the first is visible
			*temporalp*
			;; indicates whether current wff is inside a
			;; temporal operator in map-wff recursion
			inline? ;;established by map-wff itself
			))
	     (labels ((catch-equivs (rel &rest args)
		       (when (and 
 #| (not (equivalence-relp rel)) - no, this does the wrong thing for
 (listof x#eq s.t. (equal x 1)) and (listof x#equal s.t. (eq x 1))
 in particular, they are not equivalent and so must not end up
 sharing a generator cache entry! |#
                              (loop for a in (if (eq rel 'apply)
						(butlast args)
						args)
				   thereis
				   (member a *varlist* :test
					   #'(lambda (x y)
					       (and (eql x (varname y))
						    (varcompare-p y)
						    (not (eql rel (varcompare y))))))))
		       ; make up a new version ...
			 (let (evars arglist eqv)
			   (setf arglist
			       (loop for a in (if (eq rel 'apply)
						  (butlast args)
						  args)
				     collect
				     (if (and (setf eqv (car (member a *varlist*
									 :key #'varname)))
						  (varcompare-p eqv)
						  (not (eq rel (setf eqv (varcompare eqv)))))
					     (caar (push (list (gensym "V") a eqv) evars))
					     a)))
			   (when (eq rel 'apply)
			     (setf arglist (nconc arglist (last args))))
			   (map-wff-internal
			     `(E ,(mapcar #'car evars)
			         (and ,.(loop for v in evars collect
					    (let ((x (reverse v)))
					      (when source-expansion
						(setf (first x) (relationnamep (first x))))
					      x))
				      ,(cons rel arglist)))))))
		      (expand-arg (arg compfn)
			(if (and leave-constants-embedded
				 (constantp* arg :env environment))
			       arg
			  (let ((earg (macroexpand arg environment))
				entry)
			    (cond ((assoc earg evalvars) earg)
				; for expanddefn - don't eval already eval'd things
				; and also (r x) == (q x x)
			      
				  ((and (symbolp earg) ;(not always-eval)
					(setf entry
					      (referencevar earg 
					        (funcall compfn)
						*varlist*)))
				   (if source-expansion (varname entry) entry))
				  (AllowEvalArgs
				   (cond (source-expansion arg)
					 ((atom earg)
					  (caar (push (list (gensym "G") earg)
						      evalvars)))
					 (t (multiple-value-bind (#+ignore read #+ignore set)
						nil
						#+ignore ;!!! FOR FUTURE nmg
						(luke::find-free-variable-references
						 earg
						 :variables (mapcar #'varname *varlist*)
						 :environment environment)
					      (cond #+ignore ;!!! FOR FUTURE nmg
						    (set
						     (fail expanddescription "illegal implicit relation" wff))
						    #+ignore ;!!! FOR FUTURE nmg
						    (read
						     (let ((result-var (gensym "G")))
						       (values
							result-var
							`((constant
							   ,(length (rest earg))
							   1
							   (lambda ,read ,earg))
							  ,@read ,result-var))))
						    (t (caar (push (list (gensym "G") arg) evalvars))))))))
				  (t (fail ExpandDescription arg "used as a free variable"))))))
		      (expand-wff-arg (arg rel pos &optional tailp)
			 (expand-arg arg
			   #'(lambda ()
			       (if (dbobject-p rel)
				   (if tailp
				       (loop for i from rel
					     below (arity* rel)
					     collect (get-comparison rel i))
				     (get-comparison rel pos))
				 :funcall))))
		    (expand-wff-args (rel args &aux evars auxwffs)
		      (values
		       (loop for arg in args as pos from 0 collect
			    (multiple-value-bind (var auxwff)
				(expand-wff-arg arg rel pos)
			      (when auxwff
				(push var evars)
				(push auxwff auxwffs))
			      var))
		       evars
		       auxwffs)))
	       (map-copy-wff wff
		 :environment environment
		 :funcall-wff
		 #'(lambda (rel &rest args)
		     (let ((erel (macroexpand rel environment))
			   subwff)
		       (if (and (consp erel) (eq (first erel) 'quote))  
                 ;; someday we'll macroexpand 1 level at a time looking for (RELATION xxx)
			   (map-wff-internal (cons (second erel) args))
			   (if AllowEvalArgs
			       (or (apply #'catch-equivs 'funcall rel args)
				   (if source-expansion
				       `(FUNCALL ,rel ,@args)
				     (multiple-value-bind
					 (expanded-args evars auxwffs)
					(expand-wff-args rel args)
					 (push (list (gensym "G") rel) evalvars)
					 (push (caar evalvars) evalrels)
			       
					 (setf subwff
					       `(FUNCALL ,(caar evalvars)
							 ,.expanded-args))
					 (if evars
					     (map-wff-internal
					      `(e ,evars (and ,subwff ,.auxwffs)))
					   subwff))))
			       (fail ExpandDescription
				 "relcall used in a situation that does not allow evaluation"
				 wff)))))
		 :apply-wff
		 #'(lambda (rel &rest args &aux subwff relvar)
		     (if AllowEvalArgs
			 (or (apply #'catch-equivs 'apply rel args)
			     (if source-expansion
				 `(APPLY ,rel ,@args)
			       (multiple-value-bind (expanded-args evars auxwffs)
				  (expand-wff-args rel (butlast args))
				 (push (list (setf relvar (gensym "G")) rel) evalvars)
				 (push (caar evalvars) evalrels)
				 (multiple-value-bind (var auxwff)
				     (expand-wff-arg
				      (car (last args))
				      rel (1- (length args)) t)
				   (when auxwff
				     (push var evars)
				     (push auxwff auxwffs))
				   (setf subwff
					 `(APPLY ,relvar ; (caar evalvars)
						 ,@expanded-args ,var)))
				 (if evars
				     (map-wff-internal
				      `(e ,evars (and ,subwff ,.auxwffs)))
				   subwff))))
			 (fail ExpandDescription
			       "relapply used in a situation that does not allow evaluation"
			       wff)))

		 :temporal-op
		 #'(lambda (op twff)
		     (when *temporalp*
		       (fail ExpandDescription
			     wff "has a start/previously in another start/previously"))
		     (let ((*temporalp* t)) (declare (special *temporalp*))
			  (list op (map-wff-internal twff))))
		 
		 :quantified-wff
		 #'(lambda (q qvars qwff &aux subwff (*varlist* *varlist*)
			    newvars)
		     (declare (special *varlist*))
		     (setf newvars (mapcar #'establishvar qvars))
		     (unless (boundvarlist newvars)
		       (fail ExpandDescription qvars
			     "contains duplicated variable names"))
		     (setf *varlist* (append newvars *varlist*)
			   subwff (map-wff-internal qwff))
		     (unless (loop for v in newvars always
				   (freein (if source-expansion (varname v) v) subwff))
            ; we even require that typed vars appear in some other context
		       (fail ExpandDescription
			     "not all vars of are free in wff"
			     newvars subwff))
		     (list q
			   (if source-expansion
			       (mapcar #'varname newvars)
			       newvars)
			   (let ((tcforms
				   (make-type-check-forms newvars *temporalp*)))
			     (if tcforms
				 (if (eq q 'e)
				     `(and ,subwff ,.tcforms)
				     (macroexpand-1
				       `(implies
					  (and ,.tcforms) ,subwff)))
				 subwff))))

		 #+ignore 
		 :implicit-relation
		 #+ignore 
		 #'(lambda (wff)
		     (multiple-value-bind (read set)
			 (luke::find-free-variable-references
			  wff :variables (mapcar #'varname *varlist*)
			  :environment environment)
		       (if set
			   (fail expanddescription "illegal implicit relation" wff)
			 (map-wff-internal
			 `((constant ,(length read) (lambda ,read ,wff))
			   ,.read)))))

		 :constant-relation-wff
		 #'(lambda (rel &rest args &aux subwff)
		     (multiple-value-bind (expanded-args evars auxwffs)
			       (expand-wff-args rel args)
			     (setf subwff (cons rel expanded-args))
			     (if evars
				 (map-wff-internal
				     `(e ,evars (and ,subwff ,.auxwffs)))
				   subwff)))

		 :primitive-wff
		 #'(lambda (rel &rest args)
		     (or (apply #'catch-equivs rel args)
			 (let ((defn (let ((d (and
						; removed (eq 'defined (implementationof rel))
						(expanded-defn rel))))
				       (and d	; don't want to do expanded-defn... if no defn
					    (not (eq all-inline? 'notinline))
					    (or (cond ((not sort-juncts) nil)
		;; same reason for not sorting juncts justifies not expanding defns
						      ((eq inline? 'inline) t)
						      ((eq inline? 'notinline) nil)
						      ((inlinerel? rel) t))
		;; if we define eq2 as eq, it must be used inline
		;; else (and (reladder a x) (eq2 x y)) would be accepted
		;; even though the inline version violates equivalence requirements
						(some #'(lambda (x) (not (relationp
									   (varcompare x))))
						      (expanded-defn-vars rel)))
					    d)))
			       subwff)
			   (multiple-value-bind (expanded-args evars auxwffs)
			       (expand-wff-args rel args)
			     (setf subwff (cons
					   (or (and source-expansion (relationnamep rel)) rel)
					   expanded-args))
			     (cond (defn
				     (map-wff-internal (ExpandDefn subwff defn)))
				   (evars
				    (map-wff-internal
				     `(e ,evars (and ,subwff ,.auxwffs))))
				   (t subwff))))))

		 :description-wff
		 #'(lambda (desc &rest args)
		     (let* ((expand (expanddescription desc 
				     :sort-juncts nil :dont-warn-for-false t
				     :source-expansion source-expansion))
			    (args2 (loop for a in args as v in (car expand)
				      collect (expand-arg a
						#'(lambda () (or (varcompare v) t))))))
		     (map-wff-internal (expanddefn (cons desc args2) expand))))
     ;; That's an exponential algorithm!  It could be fixed by caching the
     ;; internal expanddescriptions, of course.  We can't reuse expand
     ;; at the end cause its computation wasn't done in the right context
     ;; of variable names, etc.  We can't do it in the right context cause
     ;; the args have to be eval'd first.
			     ))))

    (setf varlist (mapcar #'establishvar args))  ;; establish varlist for description vars
    (unless (boundvarlist varlist)
      (when descriptionp (return-from expanddescription nil))
      (fail ExpandDescription args "not a legal argument list"))
    (setf wff (ExpandWff (translate-functions wff environment) varlist nil))
    (when (and varlist (setf tcforms (make-type-check-forms varlist nil)))
      (setf wff `(and ,wff ,.tcforms))))
  ; check this BEFORE simplify, so x appears to be in
  ;  (AND (IGNORED-VAR X) FALSE)
  (unless (or descriptionp source-expansion dont-warn-for-false)
    (when (loop for v in varlist thereis (not (freein v wff)))
      (fail ExpandDescription
	    "not all vars are free in wff" varlist wff)))
  ; don't need to simplify if only checking legality
  (unless (or descriptionp source-expansion (not sort-juncts))
    (setf wff (simplify wff)))
  (if descriptionp
      t
      (values `(,(if source-expansion
		     (mapcar #'varname varlist)
		     varlist)
		    s.t.
		    ,wff)
	      (reverse evalvars)
	      evalrels))) 


;; ---  EXPANDED-DEFN(-VARS) ---
; * * * subtle hack * * * (I hope it works!)
; These two functions have to be cautious about caching inside an atomic -
; the atomic may be changing the data on which they depend.  We count on
; the rule THROW-OUT-INVALID-DEFNS to cause the computation to be done
; (and thus the values decached) whenever the critical data change!

; Originally tested Inatomic and decached if so - takes much too long.
; Next tried testing delta (decache if so) - helps a lot, but we seem to
; call these exponentially often recursively.
; Next attempt: don't recompute for same delta.
; Further optimization would be to see whether delta contains updates to 
; relations that would affect the results ...

#+ignore ; not that it's not useful, just not needed here
(defun same-length (x y)
  (loop while (and (consp x) (consp y)) do (pop x) (pop y))
  (not (or (consp x) (consp y))))
#+ignore ; not that it's not useful, just not needed here
(defun equal1 (x y)
  ; lists are equal1 if their elements are pairwise eql
  (or (eql x y) ; actually not needed 
      (and (consp x) (consp y)
	   (same-length x y)
	   (loop for xx in x as yy in y always (eq xx yy)))))

(defun expanded-with-same-delta (rel)
  (and (eq delta (get-structure-property rel 'last-expanded-delta))
       (loop for x in delta as y in
	     (get-structure-property rel 'last-delta-cdrs)
	     always (eq (cdr x) y))))
; new entries are added to front and thus neq first old entry

(defun expanded-defn (rel &aux d des ans)
  (cond ((and (expanded-with-same-delta rel)
	      (get-structure-property rel 'expanded-defn)))
	; needed due to typed and compared vars in defns
	((setf d ;(copy-tree *) discarded
	       (car (getdefn rel)))
	 ;; trying to protect memos in defns from expansion
	 (setf des (expanddescription d
			       :sort-juncts nil :dont-warn-for-false t)
	       ans (list (vars-to-names (car des))
			 (cadr des)
			 (vars-to-names-wff (caddr des))))
	 (put-structure-property rel (car des) 'expanded-defn-vars)
	 (put-structure-property rel ans 'expanded-defn)
	 (put-structure-property rel delta 'last-expanded-delta)
	 (put-structure-property rel 
            (loop for d in delta collect (cdr d)) 'last-delta-cdrs)
	 ans)))
(defun expanded-defn-vars (rel &aux d des)
  (cond ((and (expanded-with-same-delta rel)
	      (get-structure-property rel 'expanded-defn-vars)))
	; needed due to typed and compared vars in defns
	((setf d ;(copy-tree *)
	       (car (getdefn rel)))
	 (setf des (expanddescription d
		      :sort-juncts nil :dont-warn-for-false t))
	 (put-structure-property rel
	     (list (vars-to-names (car des)) (cadr des)
		   (vars-to-names-wff (caddr des)))
	     'expanded-defn)
	 (put-structure-property rel (car des) 'expanded-defn-vars)
	 (put-structure-property rel delta 'last-expanded-delta)
	 (put-structure-property rel 
            (loop for d in delta collect (cdr d)) 'last-delta-cdrs)
	 (car des))))

; might as well do something similar for descriptions ...
;(defvar expanded-defns-for-descs (make-hash-table :test #'equal))
(defun expanded-defn-for-desc (rel &aux des)
  (list (vars-to-names (car (setq des (expanddescription rel))))
	(cadr des)
	(vars-to-names-wff (caddr des)))
  #+ignore ; formerly (hope to reinstall it***)
  (cond ((gethash rel expanded-defns-for-descs))
	; needed due to typed vars in defns
	(t (setf (gethash rel expanded-defns-for-descs)
		 (list (vars-to-names (car (setq des (expanddescription rel))))
		       (cadr des)
		       (vars-to-names-wff (caddr des)))))))
; need a way to decache it when defns change

(defun get-test-function (rel &rest args)
  (declare (special eql-table))
  (setq args (copy-seq args))
  (cond ((member rel eql-table) 
	 (let ((fnname (equiv-name rel)))
	   (cond (args (cons fnname args))
		 (t (list 'function fnname)))))
	((and bootstrapping (eql rel rel-eql))
	 (cond (args (cons 'eql args)) (t #'eql)))
	(args `(?? ,(relationnamep rel) ,@args))
	(t `#'(lambda (x y) (?? ,(relationnamep rel) x y)))))

(defun equiv-name (rel)
  (cond ((eq rel rel-eql) 'eql)
	((eq rel rel-eq) 'eq)
	((eq rel rel-equal) 'equal)
	((eq rel rel-equalp) 'equalp)
	(t (error "strange equality rel ~S" rel))))


(defun run-time-get-test-function (rel)
  (declare (special eql-table))
  (if (member rel eql-table) 
      (equiv-function rel)
      (get-tester rel)))

(defun equiv-function (rel)
  (cond ((eq rel rel-eql) #'eql)
	((eq rel rel-eq) #'eq)
	((eq rel rel-equal) #'equal)
	((eq rel rel-equalp) #'equalp)
	(t (error "strange equality rel ~S" rel))))

(defun expanddefn (wff defn)
  (unless (= (length (car defn)) (length (cdr wff)))
	 (error "wrong number of args in ~s" wff))
  #+ignore ;; needed in order to get typed vars, etc. - now required of callers
  (setf defn (expanddescription defn
		:sort-juncts nil :dont-warn-for-false t))
  (setf (third defn) (vars-to-names-wff (third defn))
	(first defn) (vars-to-names (first defn)))
  ;(copy-tree *) ;; try not to pass back original memo cells so they won't be expanded!
    (subst-free-in-wff (loop for formal in (car defn) as actual in (cdr wff)
			   collect (cons formal
					 (cond ((variable-p actual)
						(varname actual))
					       (t actual))))
		     (third defn)))

(defun freein (var wff)
    (catch :found-free
      (map-wff wff
	  :primitive-wff
	  #'(lambda (ignore &rest args) (declare (ignore ignore))
	      (when (member var args)
		(throw :found-free t)))
	  #+ignore  :comparison
	  #+ignore  #'(lambda (ignore ignore2 x ignore3 y ignore4)
	      (declare (ignore ignore ignore2 ignore3 ignore4))
	      (when (or (eq var x) (eq var y)) (throw :found-free t)))
	  :quantified-wff
	  #'(lambda (ignore qvars qwff) (declare (ignore ignore))
	      (unless (member var qvars)
		(when (freein var qwff) (throw :found-free t))))
	  :funcall-wff
	  #'(lambda (ignore &rest args) (declare (ignore ignore))
	      (when (member var args)
		(throw :found-free t)))
	  :apply-wff
	  #'(lambda (ignore &rest args) (declare (ignore ignore))
	      (loop for a on args while (cdr a)
		    when (eq var (car a))
		    do (throw :found-free t))))))
#+ignore ;;#+ti ; temporarily (I hope) avoid throw and thus a ti microcode bug
(defun freein (var wff &aux found)
  (declare (special found))
      (map-wff wff
	  :primitive-wff
	  #'(lambda (ignore &rest args) (declare (ignore ignore))
	      (when (member var args)
		(setq found t)))
	  :quantified-wff
	  #'(lambda (ignore qvars qwff) (declare (ignore ignore))
	      (unless (or found (member var qvars))
		(when (freein var qwff) (setq found t))))
	  :funcall-wff
	  #'(lambda (ignore &rest args) (declare (ignore ignore))
	      (when (member var args)
		(setq found t)))
	  :apply-wff
	  #'(lambda (ignore &rest args) (declare (ignore ignore))
	      (loop for a on args while (cdr a)
		    when (eq var (car a))
		    do (setq found t))))
      found)

(Defun TemporalP (Wff)  ; does wff contain temporal operators
  (CompoundTemporalP Wff t))

;;; COMPOUNDTEMPORALP presumes an expanded wff
(defun compoundtemporalp (wff &optional inside)
    ; if null Inside, says whether Wff contains temporals that contain temporals
    ; In the current scheme this is usually a bad thing (i.e., an error)
    (and (compoundwffp wff)
      (block inside
	(map-wff wff
	  :quantified-wff
	   #'(lambda (q v qwff) (declare (ignore q v))
		     (return-from inside (compoundtemporalp qwff inside)))
	  :temporal-op
	   #'(lambda (when twff) (declare (ignore when))
	       (return-from inside
		 (if inside t (compoundtemporalp twff t))))
	  :boolean-op
	   #'(lambda (op &rest wffs) (declare (ignore op))
	       (loop for w in wffs
		     when (compoundtemporalp w inside)
		     do (return-from inside t)))))))


(defun same-wff (w1 w2 &optional var-alist compare-by-rels)
  ;recognize two wffs as the same even if the vars are renamed
  ; (but not if that causes them to be reordered?)
  ; var-alist can be supplied if you want to compare descriptions:
  ; (mapcar #'cons vars1 vars2)
  ; in which case you are responsible for checking the varcompare's
  (cond
    ((and w2 (eq w2 (cdr (assoc w1 var-alist)))
	  (eq w1 (caar (member w2 var-alist :key #'cdr))))
     t)
    ((assoc w1 var-alist) nil)
    ((member w2 var-alist :key #'cdr) nil) ; require both ways
    ((eq w1 w2) t) ; un-matched vars and constants
    ((not (listp w1)) nil)
    ((not (listp w2)) nil)
    ((not (eq (length w1) (length w2))) nil)
    ((not (eq (car w1) (car w2))) nil)
    ((member (car w1) '(a e))
     (and (= (length (cadr w1)) (length (cadr w2)))
	  (same-wff (caddr w1) (caddr w2)
		    (append (mapcar #'cons (cadr w1) (cadr w2)) var-alist))))
    ((and compare-by-rels (relationp (car w1)))
     (loop for x in (cdr w1) as y in (cdr w2) as pos from 0 always
	   (cond ((variable-p x) (same-wff x y var-alist))
		 ((variable-p y) nil)
		 (t (let ((c (get-comparison (car w1) pos)))
		      (cond ((eq c t) nil) ; ???
			    ((consp c) (loop for z in c always (testrel z x y)))
			    (t (testrel c x y))))))))
    (t (loop for sw1 in (cdr w1) as sw2 in (cdr w2) always
	     (same-wff sw1 sw2 var-alist)))))

(defun simplify (x &optional (environment *empty-env*))
  (simplify2 (simplify1 x environment)))

(defvar keepstarts nil)
(defun simplify1 (wff &optional (environment *empty-env*))
  (declare (special type-entity dnf-ify keepstarts sort-juncts))
  (map-copy-wff wff
      :environment environment
      :boolean-op
       #'(lambda (op &rest args)
	   (if (eq op 'not) ; push in not's
	       (case (first args)
		 (true 'false)
		 (false 'true)
		 (otherwise
		  (case
		    (car (first args))
		    (not (simplify1 (second (first args)) environment)) ;;(not(not x)) ==> x
		    (or ;; (not (or w1 ... wn)) ==> (and (not w1') ... (not wn'))
		     (cons 'and (loop for w in (rest (first args)) collect
				      (simplify1 (list 'not w) environment))))
		    (and ;; (not (and w1 ... wn)) ==> (or (not w1') ... (not wn'))
		     (cons 'or (loop for w in (rest (first args)) collect
				     (simplify1 (list 'not w) environment))))
		    
		    (A ;; (not (A vars wff)) ==> (E vars (not wff))
		     (simplify1 (list 'E (second (first args))
				      (list 'not (third (first args))))
				environment))
		    (E ;; (not (E vars wff)) ==> (A vars (not wff))
		     (simplify1 (list 'A (second (first args))
					(list 'not (third (first args))))
				  environment))
		    #+ignore (incx (simplify1 (list 'incx (cadadr wff)
						    (list 'not (caddr (cadr wff))))
					      environment))
		    (previously ;; (not (previously wff)) ==> (previously (not wff))
		     (simplify1
		       (list 'previously
			     (list 'not (second (first args))))
		       environment))
		    (entity 'false)
		    (otherwise (if (and (boundp 'type-entity) (eql (caar args) type-entity)) ;;YECH
				   ; special case - for others we postpone simplifying arg
				   'false
				   (list 'not (simplify1 (first args) environment)))))))
		 (cons op (loop for w in args collect (simplify1 w environment)))))
       :temporal-op
        #'(lambda (op twff)
	    (case op
		  (previously   ; push in  past all but not
		    (case twff
		      (true 'true)
		      (false 'false)
		      (otherwise
		       (case (first (ilistp twff))
			 ((and or)		; implies equiv 
			  (simplify1
			    (cons (first twff)
				  (loop for w in (rest twff) collect
					(list 'previously w)))
			    environment))
			 ((A E)
			  (simplify1
			    (list (first twff) (second twff)
				  (list 'previously (third twff)))
			    environment))
			 ;(previously (simplify1 twff environment)) ;; (PREVIOUSLY (PREVIOUSLY wff)) ==> wff ????
			 #+ignore (incx (simplify1 (list (car twff) (cadr twff)
							 (list op (caddr twff)))
						   environment))
			 (t (list 'previously (simplify1 twff environment)))))))
		  (start
		    (let ((w (simplify twff environment)))  ;; NOT SIMPLIFY1??
		      (cond ((and (listp w) (relationp (first w)) (not (getdefn (first w)))
				  (not (possibletoupdate (first w) t)))
			     'false)
			    ((and (listp w) (eq (first w) 'not) (relationp (caadr w))
				  (not (getdefn (caadr w)))
				  (not (possibletoupdate (caadr w) nil)))
			     'false)
			    ((or (eq w 'true) (eq w  'false)) 'false)
			    (keepstarts (list 'start w))
			    (t (simplify1
				 `(and ,w (not (previously ,w)))
				 environment)))))
		  (start* (list 'start* (simplify1 twff environment)))))
	#+ignore :incx
	#+ignore #'(lambda (cx cxwff &aux (simp (simplify1 cxwff environment)))
	    (cond ((eq (car (ilistp simp)) 'incx) simp)
		  (t (list 'INCX cx simp))))
	:quantified-wff
	 #'(lambda (q qvars qwff)
	     (let (#+ignore vars suchthats)
		  #+ignore
		  (setf vars 
			  (loop for v in qvars collect
				 (cond ((ilistp v)
					(push (cadr v) suchthats)
					(car v))
				       (t v))))
		  (list q qvars
			  (simplify1
			    (cond ((null suchthats) qwff) ;; holdover from earlier syntax??
				  ((eq q 'a)
				   (list 'or (list 'not (cons 'and suchthats)) qwff))
				  (t (cons 'and (cons qwff suchthats))))
			    environment))))
	 :primitive-wff
	 #'(lambda (&rest wff)
	     (cond ((or (eq (first wff) 'entity)
			(and (boundp 'type-entity) (eql (first wff) type-entity))) ;;YECH
		    'true)
		   ((equivalence-relp (first wff))
		    (cond ((and (symbolp (second wff)) (eq (second wff) (third wff)))
			   ;; will have to worry about symbol macros?
			   'true)
			  ; works for any equiv rel, for either lisp or ap vars
			  ((and (constantp* (second wff) :env environment)
				(constantp* (third wff) :env environment)
				(not bootstrapping)
				(null environment))
			   ; test it here and now
			   (if (testrel (first wff)
					(eval (second wff)) (eval (third wff)))
				  'true
				 'false))
			  ((not sort-juncts) wff)
			  (t (cons (first wff) (sort (copy-seq (rest wff))
						     #'arbitrary-compare)))))
		   ; we could, with a little more trouble, apply the tester
		   (t wff)))))

(declaim (special dnf-ify miniscope))
(setq dnf-ify nil)
(setq miniscope nil)

(defun simplify2 (wff &optional (environment *empty-env*))
  (declare (special type-entity sort-juncts dnf-ify))
  (cond
    ((not (zlistp wff)) wff)
    ((eq (first wff) 'quote) wff)
    (t
     (when (member (car wff) '(and or not a e))
       (setf wff (mapcar #'(lambda (w) (simplify2 w environment)) wff)))
     (case (first (ilistp wff))
       ((and or)
	(and
	  dnf-ify
	  (eq (first wff) 'and)
	  (loop for junct in (rest wff) thereis (eq (first (ilistp junct)) 'or))
	  ; push it toward or's of and's
	  ; this is used for wffs to be triggered
	  ; the triggering stuff follows the form of the wff, which means that
	  ; x,y s.t. (AND (P x y) (OR (NOT (Q x)) (NOT (R y)))) cannot be triggered
	  ; (since if we delete (Q a) we have to find y s.t. (NOT (R y)))
	  ; whereas (OR (AND (P x y) (NOT (Q x))) (AND (P x y) (NOT (R y))))
	  ; can be triggered
	  ; *** I assume that this is not really sufficient, but I'll wait for
	  ; more examples to drive the fixes.
	  (setf wff
		(simplify2
		  (cons 'or
			(let (result)
			  (doxproduct
			    (lits (loop for junct in (rest wff) collect
					(cond ((eq (first (ilistp junct)) 'or)
					       (rest junct))
					      (t (list junct)))))
				      (push (cons 'and (copy-list lits)) result))
			  result))
		  environment)))
	(let (ctrue cfalse)
	 (cond ((eq (first wff) 'and) (setf ctrue 'true  cfalse 'false))
	       (t (setf ctrue 'false  cfalse 'true)))
	 (setf wff
	       (cons (first wff)
		     (remove-duplicates
		       (delete ctrue
			       (loop for w in (rest wff) nconc
				     (cond ((eql (first (ilistp w))
						 (first wff))
					    (copy-seq (rest w)))
					   (t (list w)))))
		       :test #'same-wff)))
	 (when sort-juncts
	   (setf (rest wff) (sort (rest wff) #'arbitrary-compare)))
	 (cond ((null (rest wff)) ctrue)
	       ((member cfalse wff) cfalse)
	       ((null (cddr wff)) (second wff))
	       ((loop for w on (rest wff) thereis
		      #+ignore	; we can do better than this
		      (or (member (list 'not (car w)) w :test #'equal)
			  (and (eq (car (ilistp (car w))) 'not)
			       (member (cadar w) w :test #'equal)))
		      ;but don't have to resimplify - just push in not
		      (member (simplify1 (list 'not (first w)) environment) (rest w)
			      :test #'same-wff))
		cfalse)
	       (t wff))))
       ((a e)
	(let (cand cor cfalse splitvar)
	 (cond ((eq (first wff) 'a)
		(setf cand 'and cor 'or cfalse 'false))
	       (t (setf cand 'or cor 'and cfalse 'true)))
	 (when (eq (first wff) (first (ilistp (third wff))))
	   (setf wff (list (first wff)
			   (union (second wff) (second (third wff)))
			   (third (third wff)))))
	 ; remove unused quantified vars
	 (setf wff (list (first wff)
			 (loop for var in (second wff)
			       when (freein var (third wff)) collect var)
			 (third wff)))
	 (cond
	   ((null (second wff)) ; no quantified variables
	    (third wff))
	   ((eq (caaddr wff) 'eq);; some guarantee that (third wff) is a list?
	    ;(* assume there are multiple objects in the world)
	    cfalse)
	   ((and (eq (caaddr wff) 'not)
		 (eq (caadr (third wff)) 'eq))
	    cfalse)
	   ((eq (caaddr wff) cand)
	    (simplify2 (cons cand (loop for w in (cdaddr wff)
					collect (list (first wff) (second wff) w)))
		       environment))
	   ((and (eq (first wff) 'a) ; only miniscope universals
		 miniscope ; unfortunately, not's turn E's into A's
		 ; avoid triggering on (e(y z)(and (Rxy)(Rxz)~y=z)) by
		 ; having to generate y,z s.t. (and (Rxz)~y=z)
		 (eql (caaddr wff) cor)
		 (setf splitvar
		       (loop for v in (second wff)
			     thereis (and (loop for disj in (cdaddr wff)
						thereis (not (freein v disj)))
					  v)))) ;another thereis conversion
	    ; try some miniscoping, e.g.,
	    ; (A (x y) (and (A (z) (R1 x y z) (R2 x y z))
	    ;               (R3 x y) (R4 x y)))
	    (simplify2
	      `(, (car wff)
		, (remove splitvar (second wff))
		(, cor
		 (, (first wff)
		  (, splitvar)
		  (, cor
		   ,@ (progn (setf splitvar (loop for disj in (cdaddr wff)
						  unless (freein splitvar disj)
						  collect disj))
			     (fldifference (cdaddr wff) splitvar))))
		 ,@ splitvar))
	      environment))
	   #+ignore
	   (nil
	    ; to reinstall this we need a subst-free-in that takes real vars
	    #+IGNORE (and (eql (caaddr wff) cor)
		 (loop for disj in (cdaddr wff)
		       thereis (or (and (eq (car wff) 'e)
					(eq (car disj) 'eq)
					(setq eq disj))
				   (and (eq (car wff) 'a)
					(eq (car disj) 'not)
					(eq (car (setq eq (cadr disj))) 'eq))))
		 (cond ((member (cadr eq) (cadr wff))
			(setq eq (cdr eq)))
		       ((member (caddr eq) (cadr wff))
			(setq eq (list (caddr eq) (cadr eq))))))
	    #+IGNORE (simplify2 (list (car wff)
			     (remove (car eq) (cadr wff))
			     (subst-free-in-wff (list (cons (car eq) (cadr eq)))
						(caddr wff)))
				environment))
	   (t wff))))
       (previously (cond ((member (second wff) '(true false)) (second wff))
			 (t wff)))
       (t wff)))))


#+ignore  ; now subst-free-in-wff
(defun substfree (alist wff &aux newvars)
    (cond ((not (zlistp wff))
	   (or (cdr (assoc wff alist)) wff))
	  ((member (car wff) '(a e))
	   (setq newvars
		 (loop for v in (cadr wff)
		       collect (progn (loop while (loop for a in alist
							thereis (eql v (cdr a)))
						    do (setq v (gensym "V")))
				      v)))
	   ; talk about conservative! (gensym OUGHT to be new!)
	   (list (car wff)
		 newvars
		 (substfree (append (loop for v in (cadr wff) as n in newvars
					  collect (cons v n))
				    alist)
			    (caddr wff))))
	  (t (loop for w in wff
                   collect (substfree alist w)))))


#-aclpc
(defmacro-displace ?? (&rest wff &environment env)
  (translate?? wff :environment env))
#+aclpc ;; &rest fails for (?? . false) but &whole seems ok
        ;; this looks like true CL anyway, whereas the other is
        ;; debatable (atom as &rest) -- why not use &whole as the standard?
(defmacro ?? (&whole wff &environment env)
  (translate?? (rest wff) :environment env))

#+ignore
(setf (macro-function '??)
  #'(lambda (wff env) (translate?? (rest wff) :environment env)))

#+ignore ; this should always work, but it doesn't displace
(setf (macro-function '??)
      #'(lambda (form env) (declare (ignore env))
		(translate?? (cdr form) :environment env)))

(defun with-bindings (bind body)
  (cond (bind `(let ,bind ,body))
	(t body)))
(defvar defrel-available)
(setq defrel-available nil)
; This permits tests and updates to translate into calls on functions
; with computed names, e.g., Add-R.  It doesn't work during bootstrapping
; because on the second load the functions are already defined to use the
; original relations.  Defrelation takes care of this and redefines them.
; Example: Relations defines relgenerator and adds to it.  This defines
; the Add- function.  When relations is compiled it contains calls to
; this function.  When the compiled file is loaded the function is not
; defined.  [Actually, when the compiled file is loaded the second time
; during the compile phase, it IS defined, but it updates the OLD rel!]

(defun translate??
       (originalbody &key (environment *empty-env*) open?
		     &aux EvlVars EvlRels body
		     code macro rel reltuple result)
  (unless (or (zlistp originalbody) (eq originalbody 'true) (eq originalbody 'false))
    (error "~s -- not a tuple" originalbody))
  (multiple-value-setq (body EvlVars EvlRels)
    (ExpandDescription `(nil s.t. ,originalbody)
		       :allowevalargs t
		       :keepstarts t
		       :environment environment))
  (setf body (third body))
  #+ignore (setf body (macroexpand-to-wff originalbody))
  (cond
    ((eq body 'true) t)
    ((eq body 'false) nil)
    ((eq (first body) 'funcall)
     (with-bindings evlvars (cons 'testrel (rest body))))
    ((eq (car body) 'apply)
     (with-bindings evlvars `(apply #'testrel ,@(rest body))))
    ((and (not open?) (setf rel (relationp (first body))))
     (get-tester rel) ; make sure the test can be (is) compiled
     (if defrel-available
	 (with-bindings evlvars
		`(,(pack* "Test-" (relationnamep rel)) ,.(rest body)))
	 (with-bindings evlvars
		`(funcall (get-tester (theap5relation ,(relationnamep rel)))
			  ,.(rest body)))))
    (t
     (cond
       ((eq body 'true) t)			; worry about expanding to T/F
       ((eq body 'false) nil)
       (EvlRels				; variable relations
	`(eval ,(subst-computed-relations body evlvars '(?? . :wff) nil)))
       (t (setf reltuple body
		result
		(cond
		  ((compoundwffp reltuple) (testwff reltuple))
		  ((progn
		     (setf rel (relationp (car reltuple)))
		     (when (and (not rel) (= (length reltuple) 2)
				(cl-type-name (car reltuple) environment))
		       (setf reltuple
			     ;;; should use the test-p form if a defstruct
			     (list 'typep (cadr reltuple)
					    (kwote (car reltuple)))
			     rel (relationp 'typep)))
		     (not rel))
		   (error "~s -- No such Relation" reltuple))
		  ((not (= (length (rest reltuple)) (arity* rel)))
		   (error "Wrong Arity -- ~s" reltuple))
		  (#+ignore ;; replace with next clause
		   (and (setf imp (implementationof rel))
			(setf macro (or (tester-for rel) (tester-for imp))))
		   ;; code similar to testeffort
		   (or (setf macro (tester-for rel))
		       ;; assume if rel has a macro then imp macros won't do
		       ;; if only one imp then no choice
		       ;; avoid error message below from no testeffort
		       (let ((imps (implementations-of rel)))
			 (and (null (cdr imps))
			      (setf macro (tester-for (car imps)))))
		       (let (min effort imp-macro etuple)
			 ;; otherwise minimize over their costs
			 (loop for imp in (implementations-of rel)
			       when (setf imp-macro (tester-for imp)) do
			       ;; effort alone not enough - need code too
			       (setf etuple (get-testeffort imp))
			       (setf effort
				     (macrolet
				      ((error-default
					(real-form &rest error-forms)
					`(multiple-value-bind (ans err)
					      (ignore-errors ,real-form)
					      (cond (err ,@error-forms)
						    (t ans)))))
				      (error-default
				       (apply etuple originalbody)
					(warn "error computing effort for ~A ~
						testeffort ~A - assuming 1000"
					      imp etuple) 1000)))
			       (when (iflessp effort min)
				     (setf min effort macro imp-macro)))
			    macro))
		   (setf code `(not (not (,(apply macro rel (rest reltuple))
					  ,(uneval (car reltuple))
					  ,@(rest reltuple)))))
		   (cond ((or (context-sensitive rel)
			      (and (not (possibletoupdate rel nil))
				   (not (possibletoupdate rel t)))
			      (derivedrel rel)
			      (nonatomic-relation rel))
						; assume it knows what to do - including Delta
			  code)
			 (t `(let ((cxvalue (valueincurrentcx ,(uneval (car reltuple))
							      ,@(rest reltuple))))
			       (cond ((not (eq cxvalue 'inherit)) cxvalue)
				     (t ,code))))))
		  (t (fail cannot-test "unable to test -- ~s" reltuple))))
	  (with-bindings EvlVars result))))))

(defun get-tester-source (rel)
  (cond #+ignore
	((setq tester (get-structure-property rel 'tester))
	 (prevdef tester))
	; I don't recall why this clause is here, but surely it should
	; exclude the case of tester-for rel
	((and (defined-p rel) (not (tester-for rel)))
	 (let ((defn (getdefn rel))
	       ;; worry about typed vars etc.
	       (args (loop for x below (arity* rel) collect (gensym "A"))))
	   (setf defn (expanddescription `(,args s.t. (inline (,rel ,@args)))))
	 `(lambda ,(vars-to-names (car defn))
	      (,(if (nonatomic-relation rel) 'progn 'withreadaccess)
		(?? ,@(vars-to-names-wff (third defn)))))))
	(t (let ((args (loop for x below (arity* rel) collect (gensym "A"))))
	   `(lambda ,args
		(,(if (or (nonatomic-relation rel) (equivalence-relp rel))
		      'progn 'withreadaccess)
		    ,(translate?? `(,rel ,@ args) :open? t)))))))

(declaim (inline get-tester)) ;;make the normal case inline
(defun get-tester (rel)
  (or (get-structure-property rel 'tester)(need-tester rel)))

(defun need-tester (rel)
  (let ((tester (pack* "Test-" (relationnamep rel))))
    (compile-ap (get-tester-source rel) tester)
    (put-structure-property rel tester 'tester)
    tester))


(defun rels-to-names (wff) (list (car wff) (cadr wff) (vars&rels-to-names-wff (caddr wff))))
(defun names-to-rels (wff) (list (car wff) (cadr wff) (map-copy-wff (caddr wff))))

(defun vars-to-names-wff (wff)
  (map-copy-wff wff
    :primitive-wff
    #'(lambda (rel &rest args) (cons rel (vars-to-names args)))
    :quantified-wff
    #'(lambda (quant vars qwff)
	(list quant (vars-to-names vars)
	      (map-wff-internal qwff)))
    :funcall-wff
    #'(lambda (rel &rest args)
	(cons 'funcall (cons rel (vars-to-names args))))
    :apply-wff
    #'(lambda (rel &rest args)
        `(apply ,rel ,.(vars-to-names (butlast args)) ,(car (last args))))))

(defun vars&rels-to-names-wff (wff)
  (map-copy-wff wff
    :primitive-wff
    #'(lambda (rel &rest args) (cons (relationnamep rel) (vars-to-names args)))
    :quantified-wff
    #'(lambda (quant vars qwff)
	(list quant (vars-to-names vars)
	      (map-wff-internal qwff)))
    :funcall-wff
    #'(lambda (rel &rest args)
	(cons 'funcall (cons rel (vars-to-names args))))
    :apply-wff
    #'(lambda (rel &rest args)
        `(apply ,rel ,.(vars-to-names (butlast args)) ,(car (last args))))))

(defun vars-to-names (vars)
  (mapcar #'name-of-var vars))

(defun name-of-var (var)
  (cond ((variable-p var) (varname var))
	((evalvar-p var) (evalvarname var))
	(t var)))

; *** how about a testing cache for compound wffs
; it has to be decachable, of course
(defun testwff (wff &optional recursive &aux result)
  (setq wff (vars-to-names-wff wff))
  ; get rid of the vars - expanddescription useful for simplifying wff
  (cond
    ((eq wff 'true) t)
    ((eq wff 'false) nil)
    ((not (zlistp wff)) (error "unknown wff -- ~s" wff))
    ((compoundwffp wff)
     (when (compoundtemporalp wff)
	  (error "~s -- ~%has a start/previously in another start/previously " wff))
     (setq result
	   (case (car wff)
	     (not (list 'not (testwff (cadr wff) t)))
	     (and (cons 'and  ; *** ought to order these by cost effectiveness
			(loop for conj in (cdr wff)
			      collect (cons '?? conj))))
	     (or (cons 'or  ;*** ditto
		       (loop for dis in (cdr wff)
			     collect (cons '?? dis))))
	     (a (list 'not
		      (macroexpand ; to avoid reexpanding inside loops
			`(forany ,(second wff) s.t.
				 (not ,(vars&rels-to-names-wff (third wff)))
				 (declare (ignore ,@ (second wff)))
				 t
				 ifnone nil))))
	     (e `(not (not ,(macroexpand ; as above
			      `(forany ,(second wff) s.t.
				       ,(vars&rels-to-names-wff (third wff))
				       (declare (ignore ,@ (second wff)))
				       t
				       ifnone nil)))))
	     #+ignore (incx `(incx ,(cadr wff) ,(testwff (caddr wff) t)))
	     (previously `(let ((delta nil))
			    ,(testwff (cadr wff) t)))
	     ((start start* start+)
	      (cond ((or (eq (caadr wff) 'not) (relationp (caadr wff)))
		     (let (tv rel args)
		       (if (eq (caadr wff) 'not)
			   (setq tv nil rel (caadr (cadr wff)) args (cdadr (cadr wff)))
			   (setq tv t rel (caadr wff) args (cdadr wff)))
		       (cond ((defined-p rel)
			      (let ((newwff
				      (list (car wff)
					    (if tv (expanddefn (cadr wff)
						       (expanded-defn rel))
						(simplify
						  (list 'not
						      (expanddefn (cadadr wff)
							  (expanded-defn rel))))))))
				(testwff newwff t)))
			     ((derivedrel rel) ; come back and optimize this later ***
			      `(and (might-have-changed
				      (theap5relation ,(relationnamep rel))
				      #+ignore (memo (relationp ',(relationnamep rel))))
				    ,(testwff (cadr wff) t)
				    (not ,(testwff (list 'previously (cadr wff)) t))))
			     (t `(test-in-delta ,tv
				     (theap5relation ,(relationnamep rel))
				     #+ignore (memo (relationp ',(relationnamep rel)))
				     ,@args)))))
		    (t (testwff (push-in-start nil (cadr wff) (car wff)) t))))
	     (t (error "Impossible Compound Wff -- ~s" wff))))
     (cond ((and (not recursive) (temporalp wff))
	    `(progn (check2states (mmemo (?? ,(vars&rels-to-names-wff wff)))) ,result))
	   (t result)))
    (t (translate?? wff))))

; test-in-delta uses all the stuff in transactions, so I'll put it there

; which of vars (except those in Except) is used freely in wff
(defun varsfreein (wff vars &optional except  &aux ans)
    (declare (special ans))
    (map-wff wff
      :primitive-wff
       #'(lambda (ignore &rest args) (declare (ignore ignore))
	   (loop for w in args
		 when (member w vars)
		 unless (member w except)
		 do (pushnew w ans)))
       #+ignore  :comparison
       #+ignore  #'(lambda (ignore ignore2 x ignore3 y ignore4)
		     (declare (ignore ignore ignore2 ignore3 ignore4))
	   (loop for w in (list x y)
		 ;when (symbolp w)
		 unless (or (member w except) (not (member w vars)))
		 do (pushnew w ans)))
       :funcall-wff
       #'(lambda (ignore &rest args) (declare (ignore ignore))
	   (loop for w in args
		 when (member w vars)
		 unless (member w except)
		 do (pushnew w ans)))
       :apply-wff
       #'(lambda (ignore &rest args) (declare (ignore ignore))
	   (loop for w on args while (cdr w)
		 when (member (car w) vars)
		 unless (member (car w) except)
		 do (pushnew (car w) ans)))
       :quantified-wff
        #'(lambda (ignore qvars qwff) (declare (ignore ignore))
	    (setq ans (remove-duplicates
			(append (varsfreein qwff vars (append qvars except)) ans))))
       )
    ans)

(defun all-vars-in-wff (wff &aux result)
  (map-wff wff :primitive-wff 
     #'(lambda (&rest wff)
	(loop for a in (cdr wff) when (variable-p a) do (pushnew a result))))
  result)

(defun subst-free-in-wff (alist wff)
  ; expect vars to not be digested yet - and leave them that way.
  (map-copy-wff wff
    :QUANTIFIED-WFF
    #'(lambda (q vars qwff &aux newvars)
	(setq newvars
	      (loop for v in vars collect
		    (cond ((rassoc v alist);(loop for a in alist thereis (eql v (cdr a)))
			   (gensym "X"))
			  (t v))))
	(list q newvars
	      (subst-free-in-wff
		(append (loop for v in vars as n in newvars
			      WHEN (OR (ASSOC V ALIST) (NOT (EQ V N)))
			      collect (cons v n))
			alist)
		qwff)))
    :FUNCALL-WFF
    #'(lambda (rel &rest args)
	`(FUNCALL ,rel
		  ,.(loop with pair for w in args
			  when (setq pair (assoc w alist))
			  collect (cdr pair)
			  else collect w)))
    :APPLY-WFF
    #'(lambda (rel &rest args)
	`(APPLY ,rel
		,.(loop with pair for w on args while (cdr w)
			collect (if (setq pair (assoc (car w) alist))
				    (cdr pair)
				  (car w))
			into arguments
			finally (return `(,. arguments ,(car w))))))
    #+ignore  :comparison
    #+ignore  #'(lambda (cmp rel &rest args)
	(cons cmp (cons rel (loop with pair for w in args
				  collect (if (setq pair (assoc w alist))
					      (cdr pair)
					    w)))))
    :PRIMITIVE-WFF
    #'(lambda (rel &rest args)
	(cons rel (loop with pair for w in args
			collect (if (setq pair (assoc w alist))
				    (cdr pair) w))))))

(defun map-wff
       (wff &key ((:environment *wff-environment*) *empty-env*)
	    (quantified-wff #'(lambda (ignore ignore2 qwff)
				(declare (ignore ignore ignore2))
				(map-wff-internal qwff)))
	    (boolean-op #'(lambda (ignore &rest wffs) (declare (ignore ignore))
				  (mapc #'map-wff-internal wffs)))
	    (temporal-op #'(lambda (ignore twff) (declare (ignore ignore))
				   (map-wff-internal twff)))
	    (incx #+ignore ; obsolete
		  #'(lambda (ignore cxwff) (declare (ignore ignore))
			    (map-wff-internal cxwff)))
	    (implicit-relation #'identity) ;!!! FOR FUTURE nmg
	    #+ignore (macro-wff #'(lambda (expanded-wff)
			   (map-wff-internal expanded-wff)))
	    wff-constant funcall-wff apply-wff primitive-wff defined-wff
	    description-wff anon-rel-wff
	    constant-relation-wff ;!!! FOR FUTURE nmg
	    (bad-syntax #'(lambda (&rest wff)
			    (fail expanddescription "wrong number of args" wff)))
	    (arity-operand-mismatch
	     #'(lambda (&rest wff)
		 (fail expanddescription "wrong number of args" wff)))
	    (unknown-relation-wff
	     #'(lambda (&rest wff)
		 (fail expanddescription "unknown relation" wff)))
	    (atomic-wff #'(lambda (wff)
			    (fail expanddescription "not a wff" wff))))
  (declare (special wff-constant quantified-wff boolean-op temporal-op
		    incx funcall-wff apply-wff primitive-wff defined-wff
		    #+ignore macro-wff anon-rel-wff 
		    implicit-relation constant-relation-wff
		    description-wff bad-syntax arity-operand-mismatch
		    atomic-wff unknown-relation-wff *wff-environment*))
  (map-wff-internal wff)
  NIL)

(defun map-copy-wff
       (wff &key ((:environment *wff-environment*) *empty-env*)
	    (quantified-wff #'(lambda (quant vars qwff)
				(list quant vars (map-wff-internal qwff))))
	    (boolean-op #'(lambda (op &rest wffs)
			    (cons op (mapcar #'map-wff-internal wffs))))
	    (temporal-op #'(lambda (op twff) (list op (map-wff-internal twff))))
	    (incx #+ignore ; obsolete
		  #'(lambda (cx cxwff) (list 'INCX cx (map-wff-internal cxwff))))
	    #+ignore (macro-wff #'(lambda (expanded-wff)
			   (map-wff-internal expanded-wff)))
	    (wff-constant #'identity)
	    (funcall-wff #'(lambda (&rest args) (cons 'FUNCALL (copy-list args))))
	    (apply-wff #'(lambda (&rest args) (cons 'APPLY (copy-list args))))
	    (primitive-wff #'(lambda (&rest args) (copy-list args)))
	    (implicit-relation #'identity) ;!!! FOR FUTURE nmg
	    defined-wff description-wff anon-rel-wff
	    constant-relation-wff ;!!! FOR FUTURE nmg
	    (bad-syntax
	     #'(lambda (&rest wff)
		 (fail expanddescription "wrong number of args" wff)))
	    (arity-operand-mismatch
	     #'(lambda (&rest wff)
		 (fail expanddescription "wrong number of args" wff)))
	    (unknown-relation-wff
	     #'(lambda (&rest wff)
		 (fail expanddescription "unknown relation" wff)))
	    (atomic-wff #'(lambda (wff)
			    (fail expanddescription "not a wff" wff)))
	    #+ignore  (comparison #'(lambda (&rest args) (copy-list args)))
	    )
  (declare (special wff-constant quantified-wff	boolean-op temporal-op
		    incx funcall-wff apply-wff primitive-wff defined-wff
		    #+ignore macro-wff anon-rel-wff
		    implicit-relation constant-relation-wff
		    description-wff bad-syntax arity-operand-mismatch
		    atomic-wff unknown-relation-wff *wff-environment*))
  (map-wff-internal wff))

(defvar *potential-wff-macro-form*)

(defun macroexpand-to-wff (wff &optional (wff-environment *empty-env*)
			       &aux was-macro)
  (loop (when (or (not (listp wff))
		    (compoundwffp wff)
		    (relationnamep (car wff))
		    (RelationTypeP (car wff)))
	    (return nil))
	
	(multiple-value-bind (newwff changed)
	    (macroexpand-1wff wff wff-environment)
	  (if changed (setf was-macro t wff newwff)  (return nil))))
    (values wff was-macro))

(defun map-wff-internal (wff &optional inline?)
  (declare (special wff-constant quantified-wff	boolean-op temporal-op inline?
		    incx funcall-wff apply-wff primitive-wff defined-wff
		    #+ignore macro-wff
		    description-wff bad-syntax arity-operand-mismatch
		    implicit-relation constant-relation-wff ;!!! FOR FUTURE nmg
		    atomic-wff unknown-relation-wff anon-rel-wff
		    *wff-environment*))
    (cond
     ((or (eq wff 'true) (eq wff 'false))
      (when wff-constant (funcall wff-constant wff)))
     ((consp wff)
      (case (first wff)
	((inline notinline) (map-wff-internal (cadr wff) (first wff)))
	((AND OR) (when boolean-op (apply boolean-op wff)))
	((NOT)
	 (if (and (consp (cdr wff)) (null (cddr wff)))
	     (when boolean-op (apply boolean-op wff))
	     (apply bad-syntax wff)))
	((START PREVIOUSLY start*)
	 (if (and (consp (cdr wff)) (null (cddr wff)))
	     (when temporal-op (apply temporal-op wff))
	     (apply bad-syntax wff)))
	((A E)
	 (unless (and (consp (cdr wff)) (consp (cddr wff)) (null (cdddr wff)))
	   (cond ((and (consp (cdr wff)) (consp (cddr wff))
		       (symbolp (third wff)) (string-equal (third wff) "s.t.")
		       (consp (cdddr wff)) (null (cddddr wff))
		       (y-or-n-p "It appears you have used \"s.t.\" ~
                                  inside a WFF.~%~s~% Shall I ignore it?" wff))
		  (format *query-io* "You should remove the \"s.t.\" from ~
                                      your source code")
		  (setf wff `(,(car wff) ,(cadr wff) ,. (cdddr wff))))
		 (t (return-from map-wff-internal (apply bad-syntax wff)))))
	 (if (listp (second wff))
	   (when quantified-wff (apply quantified-wff wff))
	   (apply bad-syntax wff)))
	#+ignore
	(INCX
	  (if (and (consp (cdr wff)) (consp (cddr wff)) (null (cdddr wff)))
	      (when incx (apply incx (cdr wff)))
	      (apply bad-syntax wff)))
	((RELCALL FUNCALL)
	  (if (consp (cdr wff))
	      (when funcall-wff (apply funcall-wff (cdr wff)))
	      (apply bad-syntax wff)))
	((RELAPPLY APPLY)
	  (if (consp (cdr wff))
	      (when apply-wff (apply apply-wff (cdr wff)))
	      (apply bad-syntax wff)))
	#+ignore  (:comparison
		    (when comparison (apply comparison wff)))
	(otherwise 
	  (let (rel)
	    (cond
	     ((setq rel (relationp (first wff))) 
	      (unless (= (length (cdr wff)) (arity* rel))
		(return-from map-wff-internal
			     (apply arity-operand-mismatch wff)))
	      (let ((defn (and defined-wff
			       (defined-p rel)
			       ;;(copy-tree *)
			       (expanded-defn rel)))
		      newwff)
		  ; protect memos in defns from expansion
		  ; don't waste time getting def if it won't be used
		  (setq newwff (cons rel (cdr wff)))
		  (cond (defn (funcall defined-wff newwff
				       (ExpandDefn newwff defn)))
			(primitive-wff (apply primitive-wff newwff)))))
	     ;; allow (anon-rel . def) as relation
	     ;; if anon-rel-wff then the value is the result of applying
	     ;; it to the wff, otherwise the rel is replaced and do prim-wff
	     ((and (consp (first wff))
		   (eq (first (first wff)) 'anon-rel))
	      (cond (anon-rel-wff (apply anon-rel-wff wff))
		    (primitive-wff
		     (map-wff-internal
		      (cons (relationnamep (macroexpand (first wff)
							*wff-environment*))
			    (rest wff))))))
	     ;; allow descriptions as relations
	     ;; currently this works in funcall wffs for generating but
	     ;; not for ?? (or ++)
	     ((and (consp (first wff)) (= (length (first wff)) 3)
		   (symbolname "s.t." (cadar wff)))
	      (cond (description-wff
		     (apply description-wff wff))
		    (t (map-wff-internal
			(expanddefn wff (expanded-defn-for-desc
					 (car wff)))))))
	     ((and (consp (first wff)) (eq 'constant (first (first wff))))
	      (let (arity)
		(if (or
		     (and (= 3 (length (first wff)))
			  (integerp (second (first wff)))
			  (setf arity (second (first wff))))
		     (and (= 4 (length (first wff)))
			  (integerp (second (first wff)))
			  (integerp (third (first wff)))
			  (setf arity (+ (second (first wff))
					 (third (first wff))))))
		    (progn
		      (unless (= arity (length (rest wff)))
			(return-from map-wff-internal
				     (apply arity-operand-mismatch wff)))
		      (if constant-relation-wff
			  (apply constant-relation-wff  wff)
			wff))
		  (apply unknown-relation-wff wff))))
	     (t ;; would be more efficient to just check for the existence
		;; of a macro, but not expand, if MACRO-WFF is NIL
	      (let ((*potential-wff-macro-form* wff))
		(multiple-value-bind (expanded-wff macrop)
		    (macroexpand-to-wff wff *wff-environment*)
		  (cond
		   (macrop
		    #+ignore (when macro-wff (funcall macro-wff expanded-wff))
		    (map-wff-internal expanded-wff))
		   ((and (= (length wff) 2)
			 (cl-type-name (car wff) *wff-environment*))
		    (map-wff-internal `(typep ,(cadr wff) ',(car wff))))
		   ((symbolp (first wff))
		    (cond #+ignore ;!!! FOR FUTURE nmg
			  ((macro-function (first wff)
					   *wff-environment*)
			   (map-wff-internal
			    (macroexpand-1 wff *wff-environment*)))
			  #+ignore
			  ((or (fboundp (first wff))
			       #+ignore(function-information
					(first wff) 
					*wff-environment*))
			   (funcall implicit-relation wff))
			  (t (let ((r (check-relation-package-error
				       (first wff) (length (cdr wff)))))
			       (if (eq r (first wff));; no alternative
				   (apply unknown-relation-wff wff)
				 (map-wff-internal (cons r (cdr wff))))))))
		   #+ignore ;!!! FOR FUTURE nmg
		   ((functionp (first wff))
		    (funcall implicit-relation wff))
		   (t (apply unknown-relation-wff wff)))))))))))
     (t (funcall atomic-wff wff))))

;; this is used in new versions of defun etc.

(defun anon-rels-in-wff (wff env &aux ans)
  (map-wff wff
    :environment env
    :primitive-wff
    #'(lambda (rel &rest args &aux def)
	(declare (ignore args))
	(when (setf def (get-structure-property rel :anonymous-def))
	      (push `(eval-when (:compile-toplevel :load-toplevel :execute)
		      (let (*warning-flags*)
		       ;; (unless (relationp ',(relationnamep rel)) ...)
		       ;; unless doesn't work cause it puts all of defrel
		       ;; into one read and some of that has to read after
		       ;; the relation exists
		       (defrelation ,(relationnamep rel) ,@def
			 :cache-generators nil)
		       (make-rel-anonymous
			(relationp ',(relationnamep rel)) ',def)))
		    ans))))
  ans)

; Unfortunately, ***
; this is not quite right - the argument (satisfies zerop) causes
; an error for nil (not a number) and so is considered a non type,
; whereas (typep 0 '(satisfies zerop)) returns T.
(defun cl-type-name (x &optional environment)
  (when (and (symbolp x) (find-class x nil environment))
    (return-from cl-type-name t))
  (unless (member x '(and or)) ; mean something else in ap5
    (multiple-value-bind (ignore error)
	(ignore-errors (typep nil X))
      (declare (ignore ignore))
      (not error))))

#+ignore
(defun relationp-prev (name) ;; a hack until donc returns
  (and (symbolp name)
       (ignore-errors (check2states "relationp")
		      (any r s.t. (previously (relationname r name))))))
#+ignore
(defun arity*-now-or-then (rel) ;; more hackery
  ;;(unless (relationtypep Rel) (error "~S not a relation" rel))
  (or (car (get-structure-property rel 'RelationArity))
      (error "unknown relation ~S" Rel)))

(defun check-relation-package-error (non-rel &optional arity)
  (when *no-package-correction*
    (return-from check-relation-package-error non-rel))
  (block :lookalike
    (let ((others (and (symbolp non-rel)
		       (delete-if-not
			 #'(lambda (sym &aux r)
			     (and (not (eq sym non-rel))
				  (setq r (relationp sym))
				  (or (null arity)
				      (= arity (arity* r)))))
			 (find-all-symbols non-rel)))))
      (when others
	(cerror (cond ((cdr others) "Use one of ~{~s ~}")
		      (t "Use ~{~s~}"))
		"Unknown Relation ~* ~s"
		others non-rel)
	(loop for x in others when
	      (or (null (cdr others))
		  (y-or-n-p "use ~s instead?" x))
	      do (return-from :lookalike x))))
    non-rel)) 

(defun subst-computed-relations (wff evlvars program-context boundvars)
  boundvars ;unused for the time being
  `(progv ',(mapcar #'car evlvars) ;(cons 'boundvars *)
	  (list #+ignore ',boundvars ,. (mapcar #'cadr evlvars))
    (subst (subst-computed-relations-1 ',wff)
	   :wff ',program-context)))

(defun subst-computed-relations-1 (wff)
  (map-copy-wff wff
		:primitive-wff
		#'(lambda (rel &rest args)
		    (cons rel (mapcar #'undigest args)))
		:funcall-wff
		#'(lambda (rel &rest args)
		    (cons (eval rel)
			  (mapcar #'undigest args)))
		:apply-wff 
		#'(lambda (rel &rest args)
		    `(,(eval rel)
		      ,@(mapcar #'undigest (butlast args))
		      ,.(mapcar #'kwote (eval (car (last args))))))
		:quantified-wff
		#'(lambda (q v w)
		    (list q (mapcar #'undigest v)
			  (map-wff-internal w))
		    #+ignore 
		    (let ((boundvars (append v boundvars)))
		      (declare (special boundvars))
		      (list q (mapcar #'undigest v)
			    (map-wff-internal w))))))

(defun undigest (var)
  (cond ((variable-p var)
	 (varname var))
	(t (kwote (eval var)))))
