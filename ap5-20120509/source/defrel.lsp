(in-package "AP5")

(eval-when (:compile-toplevel) (setq defrel-available nil))
; see explanation in wffs

; --- Set-Listof ---

; 2010/10/17 re-represent list as tree for faster testing
(defmacro set-listof (&rest args &environment env)
 "(set-listof vars s.t. (rel . args) new-tuple-list) 
makes (listof vars s.t. (rel . args)) be new-tuple-list."
  (let (desc exp-desc evalargs evalrels compare
	(new-var (gensym "A")) (new-spec (first (last args))))
  ; optimize for constant nil at end
  (setf desc (butlast args))
  ; transform (set-listof R <form>)
  (when (and (null (rest desc)) (relationp (first desc)))
    (let (vars)
      (dotimes (i (arity* (relationp (first desc))))
	(push (gensym) vars))
      (setf desc `(,vars s.t.  (,(first desc) ,. vars)))))
  (unless (listp (first desc))
    (setf desc (cons (butlast desc 2) (nthcdr (- (length desc) 2) desc))))
  (multiple-value-setq (exp-desc evalargs evalrels)
    (expanddescription desc :allowevalargs t
		       :keepstarts t
		       :environment env))
  ; below may be too general since we cannot handle general wffs anyway (yet)
  ; also, we may be able to get better performance by doing more compilation
  (when evalrels               ; i.e., using funcall/apply
    (return-from set-listof
      (let ((val (gensym)))
	`(progv '(,val) (list ,(car (last args)))
	   (eval ,(subst-computed-relations (third exp-desc) evalargs
		   `(set-listof ,(car args) s.t. :wff ,val) nil))))))
  (unless (relationp (caaddr exp-desc))
    (fail bad-update "a relation is required"))
  (dolist (v (first exp-desc))
    (unless (relationp (varcompare v))
	(fail bad-update "~A has no unique comparison" v)))
  (setf compare (get-comparison-and-canonicalizer (first exp-desc)))

  (if (null (first desc))
      (cond ((null new-spec) `(-- ,. (third desc))) ;; use DESC, not exp-desc
	    (t (let ((len (gensym)))
		 `(let* ((,new-var ,new-spec)
			 (,len (length ,new-var))
			 ,@evalargs)
		    (unless (or (zerop ,len)
				(and (= 1 ,len)
				     (null (elt ,new-var 0))))
		      (error "illegal SET-LISTOF result for 0-ary description ~s"
			     ,new-var))
		    (if (zerop ,len)
			(-- ,.(third exp-desc))
			(++ ,.(third exp-desc)))))))
		  
      `(let (,@(when new-spec '((tree (create-duprel)))) ;; 2010
	     ,@evalargs ,@(when new-spec `((,new-var ,new-spec))))
	 ,(when new-spec ;; 2010
	    `(loop for tup in ,new-var do
	       (dupadder ,(if (cdr (first exp-desc)) 'tup '(list tup)) tree
			 ,(constant-equality-sig
			   (mapcar #'(lambda (x)(if (listp x) (car x) x))
				   compare)))))
	 (,(if (nonatomic-relation (first(third exp-desc)))
	       'progn
	       'atomic)
	   (do-s.t. (,(vars-to-names (first exp-desc))
		     ,(vars&rels-to-names-wff (caddr exp-desc)))
	     (unless
	       ,(if new-spec ;; don't need this code for literal NIL
		  `(duptester ;; 2010
		    (list ,@(vars-to-names (first exp-desc)))
		    #+ignore 
		    ,(if (cdar exp-desc)
			 `(list ,@(vars-to-names (first exp-desc)))
		       (varname (caar exp-desc)))
		    tree
		    ,(constant-equality-sig
		      (mapcar #'(lambda (x)(if (listp x) (car x) x))
			      compare)))
		  nil)
		  #+ignore ;; 2010 replaced
		  `(position
			 ,(if (cdar exp-desc)
			      `(list ,@(vars-to-names (first exp-desc)))
			      (varname (caar exp-desc)))
			 ,new-var :test
			 ,(if (null (cdar exp-desc))
			      (get-test-function (varcompare  (caar exp-desc)))
			      `#'(lambda (tup1 tup2)
				   (and ,@(loop for v in (first exp-desc)
						collect
						(get-test-function
						  (varcompare v)
						  '(pop tup1)
						  '(pop tup2)))))))
	       (-- ,@(vars&rels-to-names-wff (caddr exp-desc)))))

	   ,@(when new-spec ;; nothing to assert for literal NIL
	       (let ((tuple (gensym)))
		 `((map nil
			#'(lambda (,tuple)
			    ,(if (cdar exp-desc)
				 `(let ,(loop for v in (first exp-desc) collect
					      (list (varname v)
						    `(if ,tuple (pop ,tuple)
							 (error "tuple too short"))))
				    (when ,tuple (error "tuple too long"))
				    (++ ,@(vars&rels-to-names-wff (third exp-desc))))
				 `(let ((,(varname (caar exp-desc)) ,tuple))
				    (++ ,@(vars&rels-to-names-wff (third exp-desc))))))
			,new-var)))))))))

(defmacro set-listof&rest 
   (&rest args &aux (tail (member-if #'(lambda (x) (and (symbolp x)
							(string= (symbol-name x) "S.T.")))
				     args))
    desc new)
  (if (and (null tail) (relationp (first args)))
    (let (vars)
      (dotimes (i (arity* (relationp (first args))))
	(push (gensym) vars))
      (setf desc `(,vars s.t. (,(first args) ,. vars))
	    new  (rest args)))
    (progn (unless tail (error "bad syntax"))
	   (setf desc (ldiff args (cddr tail))
		 new (cddr tail))))
  
  `((lambda (&rest seq)
      (set-listof ,@desc seq))
    ,. new))

; ----------------
;; relations used by defrelation

(++ baserelname 'nonatomic-relation 1)
(deftypeconstraints nonatomic-relation :incremental relation)
(eval '(?? nonatomic-relation nil)) ;; cache it before defun below causes infinite recursion
(defun nonatomic-relation (rel) (?? nonatomic-relation rel))
(setf (symbol-function 'derived-nonatomic-rel)
   #-aclpc1 #'ignored
   #+aclpc1 (symbol-function 'ignored))
;; really defined in tools - after derived-from*

(++ baserelname 'idempotent 2)
(deftypeconstraints idempotent :incremental rel-or-imp t-or-nil)
(defun idempotent (x y) (?? idempotent x y)) ;; for get-update

(dolist (rel
 '(MATCHRELS DELETEMATCHER ADDMATCHER MATCHWFF MATCHVARS
   MATCHSUCCESSOR TYPEP DOC GENERATOR-CACHE ; REST, FIRST ?
   CLOSED-WFF DESCRIPTION)) 
 (when (relationp rel)
   (++ nonatomic-relation (relationp rel))))
; RELATION-IN-WFF is really nonatomic but we cannot afford to admit it
; since a fair number of rules really do assume it never changes

(dolist (imp '(FULL-INDEX BASE TWO-WAY-STRUCTPROP STRUCTPROP
			      TREEPROP+ TREEPROP TREE))
  (++ idempotent imp nil))

(++ baserelname 'allow-interrupts 2)
(deftypeconstraints allow-interrupts :incremental nonatomic-relation t-or-nil)
(defun allow-interrupts (x y) (?? allow-interrupts x y)) ;; for get-update

(++ proprelname 'parameter-list)
(++ compare-relation (relationp 'parameter-list) 1 (relationp 'equal))
(do-s.t.(x (relationimplementation x 'full-index))
  (get-full-index-data x))

; real defn from full-index (needed for PARTIAL index)
(defun slot-numbers (rel)
  (let ((pl (loop for p in (macro-parameter-lists rel)
		  when (eq 'partial-index (car p)) append (cdr p))))
    (unless pl (return-from slot-numbers :none))
    (sort (remove-duplicates pl :test #'=) #'<)))

(++ doubleproprelname 'default-equivalence)

(deftypeconstraints default-equivalence
		    :incremental type equivalence-relation)

(dolist (x
      '((INTEGER =)
	(description equal)
	(NUMBER =)
	(FUNCTION EQUAL)
	; (STRING STRING-EQUAL) ; now in derivation
	(LIST EQUAL)
	(SYMBOL EQL)
	(ENTITY EQL)))
      (if (and (relationp (car x)) (relationp (cadr x)))
	  (++ default-equivalence (relationp (car x)) (relationp (cadr x)))
	  (error "not yet defined -- ~a" x)))

(defun default-equivalence (type &aux cmp supers)
  (setq cmp (get-comparison type 0 nil))
  (unless (eq cmp t) (return-from default-equivalence cmp))
  ; otherwise anycompare
  (setq supers (listof x y s.t. (and (subrel type x)
				     (default-equivalence x y))))
  (setq supers (loop for s in supers
		     unless (loop for s2 in supers thereis
				  (and (not (eq (car s) (car s2)))
				       (?? subrel (car s2) (car s))))
		     collect s))
  (cond ((and supers
	      (loop for s in supers always (eq (cadr s) (cadar supers))))
	 (return-from default-equivalence (cadar supers))) ; all agree
	((null supers)
	 (cerror "choose an equivalence relation"
		 "There's no data to suggest a comparison for ~A" type))
	(t (cerror "choose an equivalence relation"
		   "Current data suggests several comparisons for ~A~&~A"
		   type supers)))
  (loop do (format *query-io* "~&Name of equivalence relation: ") until
	(or (?? equivalence-relation (setq cmp (relationp (read *query-io*))))
	    (progn (format *query-io*
			   "~&That's NOT the name of an equivalence relation.")
		   nil)))
  cmp)

(defun expand-macro-defn (d &optional env)
  (if (and (consp d) (car d) (symbolp (car d)))
      (multiple-value-bind (exp macp) (macroexpand-1 d env)
	(if macp
	    (expand-macro-defn exp env)
	    d))
      d))

(defmacro CountReq (&rest args) `(restrict-attribute-cardinality ,. args))

(++ proprelname 'previous-defrel)
(++ compare-relation (relationp 'previous-defrel) 1 (relationp 'equal))
(deftypeconstraints previous-defrel relation list)
(countreq entity previous-defrel :countspec :optional :replacing t)

#| -------- DefRelation --------

There are a number of differences between DefRelation and DefAttribute,
other than the obvious difference that DefRelation allows non-binary
relations and the equally obvious differences in syntax.  Those I see
so far include:
- DefRelation does NOT translate :unique countspecs into different calls
 (with different types) for multiple and optional - the types are provided
 explicitly. 
- DefAttribute always defaults type enforcements to :none.
- DefAttribute does not try to deduce equivalences from definitions
 or descriptions.
- DefRelation does not provide a way to define an inverse relation.
- DefRelation does allow you NOT to cache generators.
- At present DefRelation does not provide size estimates to go with
 optional constraints - perhaps it could when the patterns were more
 general than the type constraints?
- DefRelation allows adders, deleters, generators, testers, triggers, etc.

*** Known problems with defrelation: (+ means fixed) *** 
+ save and restore zapped data not appropriate if arity changes
- for maintained relations
  - the maintainrule code should be compiled to the file
  + defrelation should try to cache the data (as save/restore
    would do if the definition were first and then the rep)
  + when the definition changes the cache should be fixed
- add something to the history so that undoing over a defrelation
  causes the relation to be decached (if still exists)
- changing a relation to be inline seems to cause inability to
  canonicalize.  Try defining (R x) as baserel, using it in a rule,
  changing it to == integer, triggering the rule
|#
#+aclpc
(top:defdefiner defrelation relation)

;; note - any change to defrelation arglist must be copied to next form!
(defmacro DefRelation (name &environment env &rest keys
		       &key derivation computation representation
		       nonatomic idempotent allow-interrupts
		       documentation definition arity equivs
		       implementation types type-enforcements
		       count keep-other-countspecs
		       (size nil size-supplied)
		       adder deleter updater
		       tester generator trigger testeffort
		       (inline nil inline-p)
		       (possibletoadd :none) (possibletodelete :none)
		       ;(cache-test t) (cache-add t) (cache-delete t)
		       (cache-generators t c-g-supplied)
		       (define-macro-accessors t)
                       argnames
		       alsofns ;; a list of functions of 1 arg -- the relation
                       ;; see below ***
		       parameter-list 
		       (nontriggerable nil nontrig-p)
		       display-derived-types
		       (compute-derived-types t)
		       inhibit-warnings warnings
		       macro-parameter-lists 
		       &aux (*in-anon-rel-context* t)) 
  "Declare an ap5 relation"
  (declare (ignore env))
  (flet ((warn2 (&rest args) (push (copy-list args) warnings)))
   (block defrelation ;;; for clisp
    (let (type-enf count-args expanded imp first-def joint-afterfn)
      (when (and representation derivation)
	(error "cannot yet specify representation together with derivation"))
      (when (and representation computation)
	(error "cannot specify both representation and computation"))
      (when (and derivation computation)
	(error "cannot specify both derivation and computation"))
      (when (and implementation (or derivation computation representation))
	; later just when imp, then later remove it from param.list
	(warn2 "implementation is meant to be REPLACED by ~
           ~&derivation, computation and representation")
    ;; this prevents infinite loops from :implementation (globalvar foo)
	(setq implementation nil))
      #+ignore ;; replaced:
      (flet ((check-expand (either)
	       (if (?? implementation either)
		   (setf implementation either)
		 (let (first rest)
		   (if (listp either)
		       (setf first (first either) rest (rest either))
		     (setf first either))
		   (return-from DefRelation
		     `(defrelation ,name :parameter-list ,either
				   ,.(apply first name
					    (cons :warnings
						  (cons warnings
							(copy-list keys)))
					    rest)))))))
	    (when implementation (check-expand implementation))
	    (when derivation (check-expand derivation))
	    (when computation (check-expand computation))
	    (when representation (check-expand representation)))
      ;; new version 
      (let (keyword ;; implementation/representation/derivation/computation
	    orig ;; value of that keyword parameter
	    keylists ;; results of expanders
	    imps ; resulting list of imp's
	    queue ; list of imps still to be processed
	    expanded ; have we expanded any implementation macros
	    nextimp) ; next on queue
	(setf keyword
	      (cond (implementation :implementation)
		    (derivation :derivation)
		    (computation :computation)
		    (representation :representation))
	      orig (getf keys keyword))
	(when orig ;; if none we fill it in below
	      (setf queue 
		    (if (and (consp orig) (eq (car orig) :multiple))
			(loop for x in (cdr orig) collect (cons x keys))
		      (list (cons orig keys))))
	      (loop for i from 0 ;; avoid infinite loop !
                while (setf nextimp (pop queue)) do ;; next=(imp . keys)
                (when (> i 10) (error "infinite loop in expanding ~a ?" orig))
                (if (?? implementation (car nextimp))
                    (progn (push (car nextimp) imps)
                           (push (cdr nextimp) keylists))
                  (let (first rest)
                    (if (listp (car nextimp))
                        (setf first (caar nextimp) rest (cdar nextimp))
                      (setf first (car nextimp)))
                    (push (car nextimp) macro-parameter-lists)
                    (setf expanded t)
                    (let* ((new (apply first name
                                       (copy-list (cdr nextimp)) rest))
                           ;; assume that we'll get a result with ONE 
                           ;; of the interesting keys
                           (newimp
                            ;; expect the same keyword as the original
                            ;; bad idea - :imp might expand to :rep
                            ;; use same order as above
                            (or (getf new :derivation)
                                (getf new :computation)
                                (getf new :representation)
                                (getf new :implementation))
                            #+ignore 
                            (getf new keyword)))
                      (unless newimp
                        (error "expansion of ~A did not return ~
					   expected keyword" nextimp))
                      (if (and (consp newimp) (eq (car newimp) :multiple))
                          (loop for x in (cdr newimp) do
                            (push (cons x new) queue))
                        (push (cons newimp new) queue))))))
	      (when expanded ;; let macro mechanism bind keys
		  (return-from DefRelation
			       `(defrelation ,name :parameter-list ,orig
				  ,keyword ,(cons :multiple imps)
				  ;; expanders no longer have to do this:
				  :representation nil :derivation nil
				  :computation nil :implementation nil
				  :macro-parameter-lists
				  ,macro-parameter-lists
				  ,.(merge-defrel-keys keylists))))
	      (progn
		  (setf implementation imps);; in any case
		  (case keyword
			(:implementation)
			(:representation (setf representation imps))
			(:computation (setf computation imps))
			(:derivation (setf derivation imps))))))
      (when (cdr implementation) 
	    (let ((nderived
		   (loop for i in implementation count (?? derived i))))
	      (unless (or (= nderived 0) (= nderived (length implementation)))
		      (error "some derived, some not: ~A" implementation))))
      ;; now derivation will be a list of symbols 
      (when (cdr derivation)
	    (warn "multiple derivations not supported ~A" derivation))
      (when derivation
	    (let ((derivation (car derivation))) ;; just for this stuff 
	      (unless (?? derived derivation)
		      (warn2 "Defrelation :derivation is only to be used for derived relations"))
	      ;; perform TRIGGER tuple expansion. (the EXPANDED set is what is
	      ;; saved in previous-defrel)
	      (labels ((expand-trigger (&rest t-tuples)
				       (mapcan #'expand-1-trigger t-tuples))
		       (expand-1-trigger (t-tuple)
			(cond
			 ((eq '+- (second t-tuple))
			  (expand-trigger (list* (first t-tuple) '+ (cddr t-tuple))
					  (list* (first t-tuple) '- (cddr t-tuple))))
			 ((eq '+- (fourth t-tuple))
			  (expand-trigger (nconc (butlast t-tuple) (list '+))
					  (nconc (butlast t-tuple) (list '-))))
			 ((consp (first t-tuple))
			  (when (descriptionp (first t-tuple))
			    (error "descriptions not yet allowed in trigger specifications"))
			  (mapcar #'(lambda (r) (cons r (rest t-tuple))) (first t-tuple)))
			 (t (list t-tuple)))))
		      (setf trigger (apply #'expand-trigger trigger)))
	      (unless (and trigger (every #'third trigger))
		      (setf nontriggerable t trigger nil)
		      ;; until AP5 wants to retain "partial" triggers
		      )))
      ;; now computation will be a list of symbols 
      (when (cdr computation)
	    (warn "multiple computations not supported ~A" computation))
      (when computation
	    (let ((computation (car computation))) ;; just for this stuff
	      (unless (?? derived computation)
		      ;; eventually distinguish DERIVED from COMPUTED
		      (warn2 "Defrelation :computation is only to be used for computed relations"))
	      (when (or trigger nontriggerable)
		    (warn2 "Computation means there should be no triggers or nontriggerable"))))
      ;; now representation will be a list of symbols 
      (when representation
	    (loop for rep in representation when (?? derived rep) do
		  (warn2 "Defrelation :representation is only to be used for stored relations")))
      (when nonatomic
	(when (or definition computation)
	  (error "Nonatomic is nonsense for computed or defined relations"))
	(when (and (not nontriggerable) nontrig-p)
	  (warn2 "All nonatomic relations are considered NonTriggerable"))
	(setq nontriggerable t)
	(unless (or possibletoadd possibletodelete)
	  (error "All nonatomic relations must be possible to update somehow!"))
	(when (eq possibletoadd :none) (setq possibletoadd t))
	(when (eq possibletodelete :none) (setq possibletodelete t)))
      (loop with var-name and var-type and effective-name for spec in types
	    do (progn (setf effective-name (if (symbolp spec) spec (caar spec)))
		      (multiple-value-setq (var-name var-type) (parse-var effective-name)))
	    collect (when var-type var-name) into names
	    collect (if (symbolp spec) (or var-type spec) spec) into real-types
	    finally (setf types real-types argnames (or argnames names)))
      (when (and inline (not definition))
	(error "Only relations with WFF definitions may be INLINE"))
      (when (or (and (eq-length definition 3)
		     (symbolp (second definition))
		     (string-equal (symbol-name (second definition)) "S.T."))
	    ;;; single defn, using macro
		(and (consp definition) (symbolp (car definition))))
	(setf definition (list definition)))
      (setf definition (mapcar #'(lambda (d) (expand-macro-defn d
						     #+ignore env *empty-env*))
			       definition)
	    first-def (car definition)) ; for now only one defn allowed
      (when first-def
        (unless argnames (setf argnames (mapcar 'parse-var (car first-def))))
	(unless (eq-length first-def 3)
	  (error "definition does not appear to be a description"))
	(when (and arity (not (= arity (length (car first-def)))))
	  (error "Specified arity for ~A ignored disagrees with the definition." name))
	(when equivs
	  (warn2 "Equivalence relations for ~A are derived from the definition~
                 ~&The supplied equivalence signature will be ignored" name))
	(unless (or types (not compute-derived-types))
	  (setf types (derive-types name first-def #+ignore env *empty-env*))
	  (when (and display-derived-types
		     (not (loop for x in types always (eq x 'entity))))
	    (warn2 "~&Type constraints derived from definition of ~A : ~%~A"
		   name types)))
	(setf arity (length (car first-def))
	      expanded (expanddescription first-def
			     :environment #+ignore env *empty-env*))
	(let ((eqvs (loop for v in (car expanded) collect
			  (or (relationnamep (varcompare v)) :any))))
	  (loop for supplied in equivs as derived in eqvs as pos from 0
		unless (or (eq supplied :default) (eq supplied derived))
		do (error "supplied equivalence ~A in position ~A ~
                      ~&disagrees with equivalence ~A derived from definition"
			  supplied pos derived))
	  (setf equivs eqvs))  ; in case supplied list is shorter      
	(unless inline-p
	   (setf inline (or (member :any equivs)
			    (not (or adder deleter updater size-supplied
				     representation
				     (and (< arity 5) ;; &&&
					  (compoundwffp (third expanded))))))))
	(when (and representation inline)
	  (setf representation nil)
	  (warn2 "The relation ~A is inline and so cannot have a representation." name))
	(unless (or inline size-supplied (> arity 4))
		;; don't try to compute exponentially many *****
	  (setf size
	    (let ((ed (expanddescription first-def
			   :environment #+ignore env *empty-env*))
		      result)

		  (doxproduct (v (loop for v in (first ed)
				       collect (list nil v))
				 result)
			      (unless (every #'null v) ;; at least one output
				(setf result
				      (list*
					(loop for x in v collect (if x 'output 'input))
					(relationsize (remove nil v) (third ed))
					result))))))
	  (when (member :defrelation-size *warning-flags*)
	    (warn2 "~&no sizes supplied for ~A ~%estimates are: ~A" name size)))
	)
      (unless arity
	(if (or types equivs) (setf arity (max (length types) (length equivs)))
	    (error "no arity specified for ~A" name)))
      (unless (or (= arity (length types)) (not compute-derived-types))
	(setf types (loop for i below arity collect
			  (if types (pop types) 'entity))))
      (unless implementation
	(setf implementation
	      (if definition
		  (list 'defined) 
		(if (or adder deleter updater tester generator trigger)
		    (error
   "When providing explicit interface code to defrelation, an explicit
derivation, representation, or computation clause is necessary.  Typically,
you want :representation individual or :derivation individual-derived.")
		  (list 'base))))) 
      (setf imp implementation
	    type-enf
	    (loop for a below arity with e
		  with elist = type-enforcements collect
		  (if (or (null elist) (null (setf e (pop elist)))
			  (eq e :default))
		      (if (or first-def nonatomic
			      (?? derived (car imp))) 
			  :none :incremental)
		      e))
	    equivs
	    (loop for a below arity with elist = equivs with tplist = types collect
		  (let ((e (pop elist)) (tp (or (pop tplist) 'entity)))
		    (if (or (null e) (eq e :default))
			(cond ((and (eq-length tp 3) (string-equal (cadr tp) "s.t."))
			       (let ((desc (expanddescription tp
					      :environment #+ignore env *empty-env*)))
				 (unless (eq-length (car desc) 1)
				   (error "non-unary description used as a type constraint"))
				 (or (relationnamep (varcompare (caar desc))) :any)))
			      ((relationp tp)
			       (relationnamep (default-equivalence (relationp tp))))
			      ((cl-type-name tp #+ignore env *empty-env*) 'eql)
			      (t (error "cannot interpret ~A as a type for purposes ~
                                     of finding an equivalence~
                                    ~&(if the type is legal just supply the equivalence)"
					tp)))
			e))))
      (loop while count with arg = (cdr count) do
	    (loop while (keywordp (car arg)) do (setf arg (cddr arg)))
	    (push (ldiff count arg) count-args)
	    (setf count arg arg (cdr arg)))
      (setf count-args (nreverse count-args)) ; may as well preserve order
      (when (or (and generator (symbolp generator)) ; not for nil
		(and (consp generator)
		     (member (car generator)
			     '(lambda simplegenerator simplemultiplegenerator))))
	(setf generator (list generator)))
      `(progn ;;eval-when (load eval)
	 ,.(when first-def (anon-rels-in-wff (third first-def)
				    #+ignore env  *empty-env*))
	 ;; that takes care of wffs, now for other derivations
	 ,.(loop with def
		 for rel in (remove-duplicates (mapcar #'first trigger))
		 when (setf def (get-structure-property (relationp rel)
							:anonymous-def))
		 append `((defrelation ,(relationnamep rel) ,.def)
			  (make-rel-anonymous
			   (relationp ',(relationnamep rel)) ',def)))
	 (eval-when (:compile-toplevel :load-toplevel :execute)
	   (start-defrel ',name))
	 ,(when (and warnings (not inhibit-warnings))
	    `(eval-when (:compile-toplevel :execute)
	       ,.(loop for w in (reverse warnings) collect
		       (cons 'warn (loop for x in w collect (kwote x))))))
         ;; *** alsofns are used to add extra stuff ...
         ;; unfortunately, that stuff doesn't get undone when we redefine
         ;; the relation!!  I think alsofns should come with an undo fn
         ;; (don't want to destroy the rel as part of definition cause that
         ;; would uninstall all that depends on it ...)
	 (eval-when (:compile-toplevel :load-toplevel :execute)
	   ,(when alsofns 
	      (setf joint-afterfn
		    (#+clisp gentemp #-clisp make-symbol
		     (concatenate 'string (string name)
				  "-defrelation-afterfn")))
	      `(defun ,joint-afterfn (rel)
		 ,(unless alsofns '(declare (ignore rel)))
		 ,.(loop for f in alsofns collect `(,f rel))))
	   (do-defrel ',name ,arity ',implementation ',parameter-list
	    ',equivs `((adder ,',adder) (deleter ,',deleter)
		       (updater ,',updater) (testeffort ,',testeffort)
		       (tester ,',tester) (generator ,',generator)
		       (trigger ,',trigger) (size ,',size))
	    ,.(macrolet ((key-if (name)
			   `(when ,name
				(list ,(intern (symbol-name name) "KEYWORD")
				      (kwote ,name)))))
		(nconc (key-if nonatomic)
		       (key-if idempotent)
		       (key-if allow-interrupts)
		       (key-if definition)
		       #-TI (key-if joint-afterfn)
		       ; on TI defun in eval-when treated like lexical fn
		       #+TI
		       (when joint-afterfn
			 `(:joint-afterfn (function ,joint-afterfn)))
		       (key-if inline)
		       (key-if trigger)
		       (key-if nontriggerable)
		       (key-if possibletoadd)
		       (key-if possibletodelete)
		       (key-if argnames)
		       (key-if define-macro-accessors)
		       (key-if documentation)
		       (key-if macro-parameter-lists)))) 
	   (buffer-break)
	   (eval-when (:compile-toplevel :load-toplevel :execute)
	     (cache-test ,name))
	   (eval-when (:load-toplevel :execute)
	     (cache-add-del ,name ,arity t)
	     (cache-add-del ,name ,arity nil))
	   ,(when (and cache-generators
		     (or c-g-supplied (<= arity 3))
		     (or c-g-supplied (not inline)))
	    `(eval-when (:load-toplevel)
	       (cache-generators
		 ,.(if (atom cache-generators)
		       (list name)
		       (mapcar #'(lambda (tem)
				   (loop with g for x in tem
					 do (setf g (gensym))
					 collect g into new-tem
					 when (eq x 'output) collect g into dvars
					 finally (return `(,dvars s.t. (,name ,.new-tem)))))
			       cache-generators)))))
	 (deftypeconstraints ,name
	      ,.(let (ans)
		  (loop for tp in types as te in type-enf do
			;; te may be either an enforcement name, a repair name, 
			;; a list (:repair function), or a 2 element list containing 
			;; an enforcement name and a repair specification, in either order
			;; Some errors are caught here, others in deftypeconstraints.
			(let (when how)
			  (cond ((?? enforcement te)
				 (setf when te how :remove))
				((or (atom te) (eq (first te) :repair))
				 (setf when
				       (if (or first-def nonatomic
					       (?? derived (car imp)))
					   :none :incremental)
				       #+ignore ;; above copied from further up
				       (if (or first-def (?? derived imp))
					   :none :incremental)
				       how te))
				((not (eq-length te 2))
				 (error "illegal type enforcement ~a"
					te))
				((?? enforcement (first te))
				 (setf when (first te) how (second te)))
				((?? enforcement (second te))
				 (setf when (second te) how (first te)))
				(t (error "illegal type enforcement ~a"
					  te)))
			  (push when ans)
			  (push how ans)
			  (push tp ans)))
		  (nreverse ans)))
	   ,(unless (eq T keep-other-countspecs)
	      `(delete-other-countspecs ',name ',(append keep-other-countspecs
							 (mapcar 'car count-args))))
	   ,.(loop for c in count-args collect `(restrict-cardinality ,name ,.c))
	   )
	 #| ;; don't try to make unary relations be known as cl types, for now.
         ,(when (= 1 arity)
	    `(eval-when (:compile-toplevel :load-toplevel :execute)
	       (unless (cl-type-name ',name)
		 ;; don't believe deftype can occur other than top-level.
		 (eval ',`(deftype ,name ()
			    (satisfies ,(pack* "Test-" name)))))))
         |#
	 (eval-when (:compile-toplevel :load-toplevel :execute)
	   (finish-defrel ',name))
	 (relationp ',name))))))

;; for merging multiple representations
;; note that this arglist is supposed to be kept in sync with defrel
(defvar defrel-arglist
  '(name &environment env &rest keys
		       &key derivation computation representation
		       nonatomic idempotent allow-interrupts
		       documentation definition arity equivs
		       implementation types type-enforcements
		       count keep-other-countspecs
		       (size nil size-supplied)
		       adder deleter updater
		       tester generator trigger testeffort
		       (inline nil inline-p)
		       (possibletoadd :none) (possibletodelete :none)
		       ;(cache-test t) (cache-add t) (cache-delete t)
		       (cache-generators t c-g-supplied)
		       (define-macro-accessors t)
		       alsofns ;; a list of functions of 1 arg -- the relation
		       parameter-list 
		       (nontriggerable nil nontrig-p)
		       display-derived-types
		       (compute-derived-types t)
		       inhibit-warnings warnings
		       macro-parameter-lists ;;[**]
		       &aux ;; *** added for anon-rel
		       (*in-anon-rel-context* t)))

(defun merge-defrel-keys (defrel-key-lists) ;; list of lists
  (let ((ignored '(derivation computation representation implementation
			      macro-parameter-lists parameter-list
			      tester testeffort)) ;; special case
	(union '(generator warnings alsofns))
	(append '(size))
	(intersection '(idempotent))
	(and '(allow-interrupts)))
    (labels ((keywd (name) (intern (symbol-name name) "KEYWORD"))
	     (get-key (key list &aux (kw (keywd
					  (if (consp key) (car key) key))))
		(or (cadr (member kw list))
		    (and (consp key) (cadr key)))))
	  (append (loop for u in union append
			(list (keywd u)
			      (remove-duplicates
			       (loop for l in defrel-key-lists append
				     (get-key u l))
			       :test #'equal)))
		  (loop for u in append append
			(list (keywd u)
			      (loop for l in defrel-key-lists append
				     (get-key u l))))
		  (loop for i in intersection append
			(list (keywd i)
			      (let ((ans (get-key i (car defrel-key-lists))))
				(loop for l in (cdr defrel-key-lists) do
				      (setf ans
					    (intersection
					     ans (get-key i l)))))))
		  (loop for a in and append
			(list (keywd a)
			      (loop for l in defrel-key-lists always
				    (get-key a l))))
		  (let ((arity (get-key :arity (car defrel-key-lists)))
			(testers
			 (loop for kl in defrel-key-lists append
			       (let ((thist (get-key :tester kl))
				     (thiste (get-key :testeffort kl)))
				 (when (and thist (null thiste))
				       (warn "tester supplied w/o testeffort ~
                                               - 1000 supplied")
				       (setf thiste 1000))
				 (when (and thiste (null thist))
				       (warn "testeffort supplied w/o tester ~
                                                - ignored"))
				 (when thist (list (list thist thiste))))))
			min effort tester testeffort)
		    (or (numberp arity) (error "no arity found"))
		    (loop for (test teste) in testers do
			  (setf effort
				(if (numberp teste) teste
				  (apply (coerce teste 'function)
					 (cons 'rel
					       (loop for i below arity
						   collect i)))))
			  (when (iflessp effort min)
				(setf min effort
				      tester test
				      testeffort teste)))
		    (when tester (list :tester tester
				       :testeffort testeffort)))
		  (loop for k in (cdr (member '&key defrel-arglist))
			until (eq k '&aux)
			unless (let ((ks (if (consp k) (car k) k)))
				 (or (member ks union)
				     (member ks intersection)
				     (member ks ignored)
				     (member ks and)))
			append
			(let ((answers (loop for l in defrel-key-lists
					     collect (get-key k l))))
			  (loop for a in (cdr answers)
				unless (equal a (car answers)) do
				(error "different values for ~A: ~A, ~A"
				       k (car answers) a))
			  (list (keywd (if (consp k) (car k) k))
				(car answers))))))))

(pushnew :start-defrel *warning-flags*)
(pushnew :finish-defrel *warning-flags*)
(pushnew '(:defrelation-size) *warning-flags*) ; by default no such warnings

(defun start-defrel (name)
  (when (member :start-defrel *warning-flags*)
    (format *standard-output* "~&[defrel ~A" name)
    (force-output *standard-output*)))

(defun finish-defrel (name)
  (declare (ignore name))
  (when (member :finish-defrel *warning-flags*)
    (format *standard-output* "]")
    (force-output *standard-output*)))

(defun do-defrel (name arity implementation parameter-list equivs pdr
		       &key definition nonatomic idempotent allow-interrupts
		       joint-afterfn inline
		       nontriggerable possibletoadd possibletodelete
		       trigger argnames define-macro-accessors
		       documentation macro-parameter-lists)
   (when (inatomic) (error "trying to do DefRelation inside an atomic"))
   (let* ((already (relationp name))
	  (rel (or already (make-dbobject)))
	  (prev (any x s.t. (previous-defrel rel x) ifnone nil))
	  prevdata need-rerep need-cache)
     (transaction "DEFRELATION"
	 (unless (?? derived (car implementation)) ;; only for stored rels
	   (cond ((and already
		       ; same arity as before
		       (?? relationarity already arity)
		       ; no new defn
		       (null definition)
		       ; but something in representation is different
		       (not (and (loop for i in implementation always
				       (?? relationimplementation rel i))
				 (loop for i s.t.
				       (relationimplementation rel i)
				       always (member i implementation))
				 (?? parameter-list rel parameter-list))))
		  (setf need-rerep t
			prevdata (zap-olddata-and-save name rel)))))
	 (when (and definition (not (member 'defined implementation))
                    (not (and (loop for i in implementation always
				    (?? relationimplementation rel i))
			      (loop for i s.t. (relationimplementation rel i)
				    always (member i implementation))
			      (?? wffdefn rel (car definition)))))
	   (setf need-cache t))
	 (atomic
	   (do-arity-name-equivs rel name arity equivs
				 implementation prev nonatomic
				 idempotent allow-interrupts)
	   (do-def-or-imp rel definition implementation)
	   ;(do-parameter-list rel parameter-list) - move to end
	   (when joint-afterfn
	     (funcall joint-afterfn rel)
	     #-(or ti symbolics)
		; bug?!? - c-sh-c seems to do this twice - 2nd time funbound
	        ; on TI this is no longer even a symbol 
	     (fmakunbound joint-afterfn)))
	 (save-previous-defrel rel (cons (list 'implementation implementation) pdr))
	 (if inline (++ inlinerel rel) (-- inlinerel rel))
	 (flet ((pdrget (sym) (second (assoc sym pdr))))
	   (atomic
	     (do-add-del-test-new rel
				  (pdrget 'adder)
				  (pdrget 'deleter)
				  (pdrget 'tester)
				  (pdrget 'updater)
				  (pdrget 'testeffort)
				  prev)
	     (do-parameter-list rel parameter-list)
	     ;; These are in same atomic cause decache can occur either
	     ;;  due to change of tester... or param-list,
	     ;; decache needs all this data
	     ;; Too bad the rerepresentation requires use of adders, deleters
	     ;; testers, generators before they can be defined ...
	     (do-generator rel (pdrget 'generator) prev))
	   ; triggers may use generators so put gen first
	   (do-nontriggerable-add-del rel
		  nontriggerable possibletoadd possibletodelete)
	   ; should be doing something to get TRIGGER code specified
	   ; as LAMBDA expressions COMPILED.
	   (do-trigger rel trigger prev nontriggerable)
	   (do-sizes rel (pdrget 'size) prev)
	   (do-argnames rel argnames)
	   (when (and need-rerep (not (eq prevdata :cannot-generate)))
	     (restore-zapped-data name rel arity prevdata))
	   (when need-cache 
             (set-listof d s.t. (wffdefn rel d) definition)
	     (cache-data rel name (car definition)))))
     (cond ((eql '#.(find-package "LISP") (symbol-package name))
	    ;; not fair to add add macros to symbols in the LISP package
	    nil)
	   (define-macro-accessors
	    (unless (fboundp name)
	      (setf (macro-function name)
		    #+(or TI Symbolics) 'standard-relation-macro
		    #+aclpc1 (symbol-function 'standard-relation-macro)
		    #-(or TI Symbolics aclpc1) #'standard-relation-macro)))
	   (t (when (and (fboundp name)
			 (eql (macro-function name)
			      #+(or TI Symbolics) 'standard-relation-macro
			      #+aclpc1
			      (symbol-function 'standard-relation-macro)
			      #-(or TI Symbolics aclpc1)
			      #'standard-relation-macro))
		(fmakunbound name))))
     (do-documentation rel documentation)
     (do-macro-parameter-lists rel macro-parameter-lists)
     #+symbolics(global::record-source-file-name name 'relation)
     #+ti(system::record-source-file-name name 'relation)
     #+lucid(lcl::record-source-file name 'relation)
     rel))

;; I foresee the need to write rules about parameter lists which
;; will force this to become a relation.
(defun do-macro-parameter-lists (rel macro-parameter-lists)
  (put-structure-property rel macro-parameter-lists 'macro-parameter-lists))
(defun macro-parameter-lists (rel)
  (get-structure-property rel 'macro-parameter-lists))

; zap-olddata-and-save, restore-zapped-data, cache-data in tools
; after with-dormant-rules (which they use)


(defmacro cache-test (name &aux (fn (pack* "Test-" name)) source)
  (setf source
        (try (get-tester-source (relationp name))
         cannot-test
         (return-from cache-test
          `(progn (fmakunbound ',fn)
                  (rem-structure-property (theap5relation ,name) 'tester)))))
  ;; *** ??? ap5::defun causes anon-rels to be redefined infinitely
  ;; but don't we need to be able to compile the generators from inside???
  `(progn (lisp::defun ,fn ,.(rest source))
          (eval-when (:load-toplevel :execute)
            (unless (compiled-function-p (symbol-function ',fn))
              (compile ',fn)))
          (put-structure-property (theap5relation ,name) ',fn 'tester)))

(defmacro cache-add-del (name arity add-p
                        &aux (prefix (if add-p "Add-" "Delete-"))
                        fn pname normal simple)
  (setf fn (pack* prefix name)
        pname (if add-p 'adder 'deleter)
        normal (pack* "Normal-" fn)
        simple (pack* "Simple-" fn))
  (multiple-value-bind (normal-simple-distinct normal-source simple-source)
      (try (get-update-source add-p (relationp name)
                              (loop for i below arity collect i))
           bad-update
           (return-from cache-add-del
             `(progn (fmakunbound ',fn)
                     (rem-structure-property (theap5relation ,name) ',pname))))
    ;; normal-simple-distinct will be true except for
    ;; non-atomic relations, inline relations, and derived relations
    ;; (for which we are dealing with update translators rather than true 
    ;; updaters.)  If normal-simple-distinct is false, then only one source 
    ;; function is returned
    (if normal-simple-distinct
        `(progn (defun ,normal ,.(rest normal-source))
                (defun ,simple ,.(rest simple-source))
                (eval-when (:load-toplevel :execute)
                  (unless (compiled-function-p (symbol-function ',normal))
                    (compile ',normal) (compile ',simple)))
                (setf (symbol-function ',fn)
                      (symbol-function
                       (if (simple-update-p (theap5relation ,name) ',add-p)
                           ',simple ',normal)))
                (put-structure-property (theap5relation ,name) ',fn ',pname))
        `(progn (defun ,fn ,.(rest normal-source))
                (eval-when (:load-toplevel :execute)
                  (unless (compiled-function-p (symbol-function ',fn))
                    (compile ',fn)))
                (put-structure-property (theap5relation ,name) ',fn ',pname)))))


(defun save-previous-defrel (rel args)  (++ previous-defrel rel args))

(defun start-over (rel name)
  ;; not clear whether this should be in the same atomic -
  ; either way there could be rules that would cause aborts if we first
  ; declare a rel some other way
  (delete-other-countspecs name t)
  (set-listof x s.t. (reladder rel x) nil)
  (set-listof x s.t. (relupdater rel x) nil)
  (set-listof x s.t. (reldeleter rel x) nil)
  (set-listof x s.t. (reltester rel x) nil)
  (set-listof x s.t. (testeffort rel x) nil)
  (set-listof x s.t. (relgenerator rel x) nil)
  (-- nontriggerable rel)
  (set-listof x s.t. (possibletoadd rel x) nil)
  (set-listof x s.t. (possibletodelete rel x) nil)
  (set-listof x y z w s.t. (trigger x y z rel w) nil)
  (set-listof x y s.t. (relsize rel x y) nil))

(defun do-arity-name-equivs (rel name arity equivs imp prev
				 &optional nonatomic idempotent allow-interrupts
  ;; *** optional ONLY for compatibility
				 &aux erel)
  ; we could turn of rule all-types-subtype-of-entity here if we
  ; don't mind the condition being false until the end of defrel
  (progn ;atomic  only called in an atomic
    (when (and (relationp rel) ; already a relation
	       (or (not (= arity (arity* rel)))
		   (not (eq nonatomic (?? nonatomic-relation rel)))
		   (not (equal imp (cadr (assoc 'implementation prev))))))
	 (start-over rel name))
    (++ relationarity rel arity)
    (set-listof nil s.t. (nonatomic-relation rel) (when nonatomic '(nil)))
    (set-listof tv s.t. (idempotent rel tv)
		(loop for x in idempotent collect
		      (case x (:add t) (:delete nil)
			    (t (error "idempotent argument must be a list whose elements~
                                       are :add and :delete")))))
    (set-listof tv s.t. (allow-interrupts rel tv)
		(loop for x in allow-interrupts collect
		      (case x (:add t) (:delete nil)
			    (t (error "allow-interrupts argument must be a list whose ~
                                       elements are :add and :delete")))))
    (++ relationname rel name) ; a noop if already defined
    (loop for pos below arity as e in equivs do
	  (cond ((eq e :any)
		 (++ anycomparison rel pos)
		 (loop for x s.t. (compare-relation rel pos x)
		       do (-- compare-relation rel pos x)))
		((null (setq erel (relationp e)))
		 (error "~A is not a relation" e))
		((not (?? equivalence-relation erel))
		 (error "~A is not an equivalence relation" e))
		((eq erel rel-eql)
		 (-- anycomparison rel pos)
		 (loop for x s.t. (compare-relation rel pos x)
		       do (-- compare-relation rel pos x)))
		; maybe a noop, may remove old
		(t (-- anycomparison rel pos)
		   (++ compare-relation rel pos erel))))))

(defun do-def-or-imp (rel logical-definitions imp)
  ; we could turn off rule make-trivial-defns-inline here since inline will 
  ; be overwritten anyway
  (progn ;;atomic
    (when (cdr logical-definitions)
      (error "multiple definitions currently not allowed"))
    ; also implementation defined will be added by a rule if none other
    (if (member 'defined imp)
	;; for maintained rels, defns will be added later
	(set-listof d s.t. (wffdefn rel d) logical-definitions)
	(loop for d s.t. (wffdefn rel d) 
	      ; but remove any old ones so we don't maintain THEM!
	      unless (member d logical-definitions :test #'equal)
	      do (-- wffdefn rel d)))
    ;; if it's a maintained rel then wait to add defn
    (set-listof imp s.t. (relationimplementation rel imp) imp)))

(setf (symbol-function 'do-documentation)
   ;;bootstrapping - redefined later
   #-aclpc1 #'ignored
   #+aclpc1 (symbol-function 'ignored))

(defun coerce-to-fn (x)
  ; actually, aclpc also does that wrong, but fixed elsewhere
  (when x
    #+clisp (when (symbolp x) (return-from coerce-to-fn (symbol-function x)))
    (coerce x 'function)))

(defun do-add-del-test-new (rel adder deleter tester updater testeffort prev)
  (progn ;atomic
    (unless (equal adder (cadr (assoc 'adder prev)))
      (set-listof x s.t. (reladder rel x) (list (coerce-to-fn adder))))
    (unless (equal deleter (cadr (assoc 'deleter prev)))
      (set-listof x s.t. (reldeleter rel x) (list (coerce-to-fn deleter))))
    (unless (equal updater (cadr (assoc 'updater prev)))
      (set-listof x s.t. (relupdater rel x) (list (coerce-to-fn updater))))
    (unless (equal tester (cadr (assoc 'tester prev)))
      (set-listof x s.t. (reltester rel x) (list (coerce-to-fn tester))))
    (unless (equal testeffort (cadr (assoc 'testeffort prev)))
      (set-listof x s.t. (testeffort rel x)
		  (list (if (numberp testeffort)
			    #'(lambda (&rest ignore)
				(declare (ignore ignore))
				testeffort)
			  (coerce-to-fn testeffort)))))))

(defun do-generator (rel generators prev)
  (flet ((real-gen (g)
	   (cond ((member (car (ilistp g))
			  '(simplegenerator simplemultiplegenerator))
		  ;; like simple[multiple]generator but we only get (cdr pat)
		  (let ((pat (cadr g)) (form (caddr g)) (costcode (cadddr g)))
		    (setf pat (loop for p in pat collect
				    (cond ((symbolname "OUTPUT" p) 'output) (t p))))
						; accept output in any package
		    (unless (member 'output pat)
		      (error "~S contains no OUTPUT" pat))
		    (compile nil
		     `(lambda (&rest ignore)
		       (declare (ignore ignore))
		       '((effort , (or costcode (* 5. (1+ (length pat)))))
			 (template , (loop for arg in pat
					   collect (cond ((eq arg 'output) 'output)
							 (t 'input))))
			 (initialstate
			   (lambda (ignore ,.(loop for arg in pat
						   unless (eq arg 'output)
						   collect arg)
				    &aux state)
			     (declare (ignore ignore))
			     (setf state ,form)
			     ,(if (eq (car (ilistp g)) 'simplegenerator)
				  '#'(lambda nil
				       (cond (state
					      (values nil
						      (if (consp state)
							  (pop state)
							  (prog1 state
								 (setf state nil)))))
					     (t t)))
						; otherwise simplemultiplegenerator
				  '#'(lambda nil
				       (cond (state (apply #'values nil (pop state)))
					     (t t)))))))))))
		 (t (coerce g 'function)))))
	(unless (equal generators prev)
	  (set-listof x s.t. (relgenerator rel x)
		      (mapcar #'real-gen generators)))))

(defun do-nontriggerable-add-del (rel nt pta ptd)
  ;(set-listof nil s.t. (nontriggerable rel) (if nt '(nil)))
  (if nt (++ nontriggerable rel) (-- nontriggerable rel))
  (if (eq pta :none) (set-listof x s.t. (possibletoadd rel x) nil)
      (++ possibletoadd rel pta))
  (if (eq ptd :none) (set-listof x s.t. (possibletodelete rel x) nil)
      (++ possibletodelete rel ptd)))

(defun do-trigger (rel trigger prev nontriggerable)
  (flet ((real-trigger (x)
	   (unless (and (listp x) (eq-length x 4)
			(member (second x) '(+ -))
			(member (fourth x) '(+ -)))
	     (error "bad defrelation trigger syntax"))
	   (list (or (relationp (first x))
		     (error "defrelation trigger not a relation - ~A"
			    (first x)))
		 (eq (second x) '+)
		 (if (symbolp (third x))
		     (third x)
		   (coerce-to-fn (third x)))
		 rel (eq (fourth x) '+))))
    (atomic
      (unless nontriggerable
	      (dolist (x trigger) (++ apply 'trigger (real-trigger x))))
      (dolist (x (second (assoc 'trigger prev)))
	(unless (member x trigger :test 'equal) 
	  (-- apply 'trigger (real-trigger x)))))))

(defun do-sizes (rel size prev
		 &aux (old (second (assoc 'size prev))) ;tuples oldtuples
		 )
  (flet ((map-size-list (fn l)
           #+symbolics (declare (sys:downward-funarg fn))
	   (do ((tail l (cddr tail)))
	       ((null tail) nil)
	     (funcall fn (first tail) (second tail)))))
    #|
    (loop while size do
	  (push (list (pop size) (pop size)) tuples))
    (loop while old do
	  (push (list (pop old) (pop old)) oldtuples))
    (atomic (loop for x in oldtuples
		  unless (member x tuples :test 'equal) ;;EQUAL won't test numbers correctly
		  do (-- relsize rel (car x) (cadr x)))
	    (dolist (x tuples) (++ relsize rel (car x) (cadr x))))
    |#
    (atomic
     (map-size-list
      #'(lambda (old-pattern old-value)
	  (block done
	    (map-size-list
	     #'(lambda (new-pattern new-value)
		 (when (equal old-pattern new-pattern)
		   (unless (if= old-value new-value)
		     (-- relsize rel old-pattern old-value))
		   (return-from done)))
	     size)))
      old)
     (map-size-list
      #'(lambda (new-pattern new-value)
	  (++ relsize rel new-pattern new-value))
      size))))

(++ proprelname 'relationargnames)
(++ compare-relation (relationp 'relationargnames) 1 (relationp 'equal))
(deftypeconstraints :incremental relationargnames relation list)
(countreq entity relationargnames :countspec :optional :replacing t)
;; store the names for c-sh-A
(defun do-argnames (rel names)
  (++ relationargnames rel names))

(defun do-parameter-list (rel param-list)
  (set-listof x s.t. (parameter-list rel x) (list param-list))
  ;; ?? too soon in bootstrapping to write SETF here??
  )

(defun standard-relation-macro (prim-wff environment)
  (let* ((l (length (rest prim-wff)))
	 (rel (relationp (first prim-wff)))
	 (arity (and rel (arity* rel)))
	 (real-prim-wff prim-wff) default default-p)
    (when (and (> l 1)
	       (member (nth (1- l) prim-wff) '(default :default)))
      ;; I would like to remove the use of ap5:default here, and only
      ;; use :default, and no longer export ap5:default
	  (setf real-prim-wff (butlast prim-wff 2)
		default (nth l prim-wff)
		default-p t
		l (- l 2)))
    (unless rel
	    (error "~A no longer a relation" (first prim-wff)))
    (when (> l arity)
      (error "~a's arity is only ~d~%~s" (first prim-wff) arity prim-wff))
    (multiple-value-bind (new-wff conjuncts e-vars top-vars)
	(analyze-functions (first real-prim-wff)
	  (if (= l arity)
	      (rest real-prim-wff)
	      (append (rest real-prim-wff) (make-sequence 'list (- arity l)
						     :initial-element '?)))
	  environment)
      (when conjuncts (setf new-wff `(and ,new-wff ,@conjuncts )))
      (when e-vars (setf new-wff `(E ,e-vars ,new-wff)))
      (if top-vars
	  `(any ,top-vars s.t. ,new-wff
		,. (when default-p `(ifnone ,(only-n-values default (length top-vars)))))
	  (if default-p
	      (error "default result supplied for a Test!")
	    `(?? ,. new-wff))))))

(defun only-n-values (form n)
  (case n (0 '(values))
	  (1 ` (values ,form))
	  (otherwise (if (and (consp form) (eq 'values (car form)))
			 `(values ,. (loop for f in (rest form)
					   as i below n collect f))
		       (let ((g (loop for i below n collect (gensym))))
			 `(multiple-value-bind ,g ,form (values ,.g)))))))

(DEFINE-SETF-EXPANDER any (top-vars s.t. wff &rest ignore2)
  (declare (ignore ignore2))
  (when (and top-vars (symbolp top-vars)) (setf top-vars (list top-vars)))
  (unless (descriptionp (list top-vars s.t. wff) t)
    (error "Bad description syntax for SETF~%~s"
	   `(,top-vars s.t. ,wff)))
  (when (or (null top-vars) (rest top-vars))
    (error "SETF cannot handle a multi-variate description.~%~s"
	   `(,top-vars s.t. ,wff)))
  (multiple-value-bind (desc evalvars evalrels)
	   (ExpandDescription (list top-vars 's.t. wff)
			      :allowevalargs t
			      :keepstarts t
			      ;:environment environment
			      )
    (declare (ignore evalrels))
    (let ((new-vars (vars-to-names (first desc)))
	  (new-wff (vars&rels-to-names-wff (third desc)))
	  (store-var (gensym)))

      (values
	(mapcar #'first evalvars)		;temporaries
	(mapcar #'second evalvars)		;values
	(list store-var)
	`(progn (set-listof&rest ,new-vars
				 s.t.
				 ,new-wff
				 ,store-var)
		,store-var)
	`(any ,new-vars s.t. ,new-wff)))))

#| in the following, a list of types is termed "non redundant"
 if no type in the list is a supertype of any other type in the list.
 Such lists are used to represent joint constraints on variables
 and are called joint constraint lists (JCL).
|#

(defun derive-types (rel def &optional (env *empty-env*)
		     &aux result varnames)
  (setf def (copy-tree def)
	rel (relationp rel)
	varnames (mapcar #'variablename (car def))
	result (defined-typeconstraints def env))
  (setf result
	(loop for r in result collect
	      (cons (car r)
		    (mapcar #'relationnamep
			    (if (member rel (cdr r))
				(append (delete rel (cdr r))
					(listof sup s.t. (isubrel rel sup)))
				(cdr r))))))
  ; we don't want x-or-y to be isubrel of itself (after it's defined)
  (setf result
	(loop for v in varnames as pos from 0 collect
	      (or (loop for tp in (cdr (assoc v result)) thereis tp
			#+ignore ; someone please justify this? - DC
			(when (?? E (cmp)
				  (and (compare-relation (relationp tp) 0 cmp)
				       (compare-relation rel pos cmp)))
			  ;; that's certainly wrong when rel is not yet declared!
			  tp))
		  'entity)))
  ; only use the first one (perhaps we should use the others?)
  ; if >1 then build a description??
  result)

(defun defined-typeconstraints (description &optional (env *empty-env*))
  ; return an alist of (var . types) entries
  ; avoid expanddescription since that turns useful info like (type x)
  ; into less useful info like (relationarity x 1)
  (flet ((separate-tcs (varlist)
	   (loop for entry in varlist nconc
		 (loop for v in (car entry) collect
		       (cons v (cdr entry))))))
    (separate-tcs
     (process-joint-typeconstraints
      (loop for v in (car description) collect
	    (multiple-value-bind (name type) (variablenameandtype v)
	      (cons (list name);; &&
		    (unless (eq type 'entity) (list (relationp type))))))
      ;; simplify to push in not's etc.
      (simplify1 (caddr description) env)))))

(defun process-joint-typeconstraints (varlist wff &aux qvarlist)
  (flet ((types-of-constant (rel y)
	   (declare (ignore rel))
	   ;; we want types with comparisons compatible with rel
	   ;; but do we really have enough info to determine that?
	   ;; anycomparison ensures that they're static
	   ;; return all such types and let code below deal with subsumption
	   (most-specific-types-of
	    (loop for x s.t. (and (type x)(anycomparison x 0))
		when (testrel x y) collect x))))
  (map-wff wff
      :primitive-wff
    #'(lambda (rel &rest args &aux tmp)
	(if (?? equivalence-relation rel);; &&
	    (if (and (symbolp (car args)) (symbolp (cadr args)))
		;; merge their entries
		(let ((e1 (loop for v in varlist thereis
				(and (member (car args) (car v)) v)))
		      (e2 (loop for v in varlist thereis
				(and (member (cadr args) (car v)) v))))
		  (unless (eq e1 e2)
		    (setf (car e1) (append (car e1)(car e2)))
		    (loop for tp in (cdr e2) do
			  (further-restrict-entry e1 tp))
		    (setf varlist (remove e2 varlist))))
	      (if (or (symbolp (car args)) (symbolp (cadr args)))
		  (let ((x (car args)) (y (cadr args)) e)
		    (when (symbolp y) (rotatef x y));; x is the var
		    (setf e (loop for v in varlist thereis
				  (and (member x (car v)) v)))
		    (loop for tp in (types-of-constant rel y) do
			  (further-restrict-entry e tp)))))
	  (loop for a in args as pos from 0
		when (and (symbolp a)
			  (setf tmp;; && (assoc a varlist))
				(loop for v in varlist thereis
				      (and (member a (car v)) v)))
			  ;; && (notany #'(lambda (l) (member a l)) qvarlist)
			  )
		do
		(if (cdr args)
		    (loop for type s.t. (typeconstraint (relationp rel) pos type)
			  do (further-restrict-entry tmp type))
		  ;; rel is a type
		  (further-restrict-entry tmp rel)))))
    :wff-constant #'ignored
    :quantified-wff
      #'(lambda (q qvars wff)
	  (declare (ignore q))
	  (push qvars qvarlist)
	  ;; && add
	  (loop for v in qvars do
		(multiple-value-bind (name type) (variablenameandtype v)
		  (push (cons (list name) ;; &&
			      (unless (eq type 'entity) (list (relationp type))))
			varlist)))
	  (map-wff-internal wff)
	  ;; && next two added
	  (loop for v in varlist do
		(setf (car v) (set-difference (car v) (car qvarlist))))
	  (setf varlist (remove-if 'null varlist :key 'car))
	  (pop qvarlist))
    :boolean-op
      #'(lambda (op &rest wffs)
	  (case op
	    (and (mapc #'map-wff-internal wffs))
	    (or ;; &&& (process-disjuncts varlist wffs)
	     ;; convert to original representation, then back
	     ;; admittedly this loses some information, e.g., 
	     ;; (or (((x,y,z) t1)((w) t2)) (((x,y,w) t3)((z) t4)))
	     ;; should really come back with (((x,y) (t1 v t3)) ...)
	     (setf varlist
		   (process-disjuncts varlist wffs))))))) 
  varlist)

(defun process-disjuncts (varlist wffs)
  (flet ((combine-varlists (v1 v2)
	   ;;; v1,v2 are each alists of the form (VAR . types), each entry
           ;;; representing that the var must satisfy ALL the types.
           ;;; types is a JCL. This function SMASHES v1 to incorporate the
	   ;;; restrictions from v2.
	   (mapc #'(lambda (e2 &aux (e1 (assoc (car e2) v1
					       :test 'equal))) ;; &&&
		     (mapc #'(lambda (tp)(further-restrict-entry e1 tp))
			   (cdr e2)))
		 v2)))
    (let ((DNF (loop with l and newconj for wff in wffs do
		   (setf newconj
			 (process-joint-typeconstraints
			   (mapcar #'(lambda (x) (list (car x)))
				   varlist)
			   wff)) 
		   (cond (l ;; not the first disjunct
			  (loop with enew for entry in l when (cdr entry)
			       do (cond ((setf enew
					       (assoc (car entry) newconj
						      :test 'equal)) ;;&&&
					 (push (cdr enew) (cdr entry)))
					(t (rplacd entry nil)))))
  ;; can learn NOTHING about this var from the disjunction, since one of 
  ;; the disjuncts fails to restrict it, so we OMIT restrictions from the result
			    (t (setf l
				  (loop for entry in newconj
					
 ;;; if no cdr, the the disjunct fails to restrict the variable
 ;;; so we OMIT restrictions from the result
					collect (cond ((cdr entry)
						       (list (car entry)
							     (cdr entry)))
						      (t entry))))))
		   finally (return l))))
      
 ;;; each element of DNF is (VAR (TP ... TP) ...)
 ;;; The var is known to be of ALL the types in at least ONE of the lists
 ;;; In particular, an element of the form (VAR) is unrestricted
		  (mapc #'(lambda (entry)
			    (let (jcl) 
			      (doxproduct (disj (cdr entry))
  ;;; disj is a list of types.  Var (car entry) is known to be of at least 1
  ;;;  type in the list

				(setf jcl
				  (apply #'further-restrict-jcl jcl
				     (loop with tmp and supers for tp in disj
					do (setf tmp
					       (or (listof y s.t. (subrel tp y))
						   ;; tp must be a descr.
						   (list tp))
					       supers
					       (cond ((null supers) tmp)
						     (t (nintersection supers
						          tmp))))
					finally (return supers)))))
			      (setf (cdr entry) jcl)))
			DNF)
		  ;;; DNF is now a "standard" var restriction alist
		  (combine-varlists varlist DNF)))
    varlist)

(defun further-restrict-entry (entry type)
  ;; entry is (var . jcl) (<= 0 n)
  (setf (cdr entry) (further-restrict-jcl (cdr entry) type)))

(defun further-restrict-jcl (JCL &rest types)
  ;; return a jcl (possibly smashing JCL) that incorporates the additional
  ;; restrictions from types
  ;; types is not guaranteed to be without redundancy
  (cond ((null JCL) (most-specific-types-of types))
	(t (loop for restrict in types
	     when (some #'(lambda (tp) (or (eq tp restrict)
					   (?? subtype tp restrict)))
			jcl)
	 ;; restrict is already implied, so leave entry unchanged
	     do nil
	     else ;;; add JCL, removing anything implied by it
	     do (setf JCL
		 (cons  restrict
		       (remove-if #'(lambda (tp) (?? subtype restrict tp))
				  JCL))))
	   JCL)))

#+ignore ; old version
(defun defined-typeconstraints1 (description &aux varlist)
  ; return an alist of (var . types) entries
  ; avoid expanddescription since that turns useful info like (type x)
  ; into less useful info like (relationarity x 1)
  (declare (special *used-equiv*))
  (map-copy-wff `(and ,.(loop for v in (car description) collect
			      (list (or (variabletypename  v) 'entity)
				    (car (push (variablename  v) varlist))))
		      ,(simplify (caddr description)))
		      ;; simplify to push in not's etc.
    :wff-constant nil
    :primitive-wff
    #'(lambda (rel &rest args)
	(loop for a in args as pos from 0 when (member a varlist) collect
	      (cons a (cond ((= (length args) 1) (list rel))
			    #+ignore ; start with something already inside ap5
			    ((let (const)
			       (and (member (relationnamep rel) '(eq eql equal))
   ;;; string-equal, for instance, relates symbols to strings
				    (or (constantp (setq const (car args)))
					(constantp (setq const (cadr args))))
				    #+ignore ; returns too many
				    (most-specific-types-of
				      (all-types-of (eval const)))
				    (progn (unless (eq rel rel-eq)
					     (setq *used-equiv* t))
					   (list (fsd::get-type (eval const)))))))

   ;;; *used-equiv* is meant to tell you to check the results.
   ;;; The potential problem here is that a definition could contain something
   ;;; like (equal x c) where get-type returns a type that is not true of all
   ;;; things that are EQUAL to c
   ;;; in which case we would incorrectly say that x has to be of that type.

			    (t (listof type s.t.
				       (typeconstraint
					 (relationp rel) pos type)))))))
    :boolean-op
    #'(lambda (op &rest wffs)
	(case op
	  (and (let (ans entry)
		 (loop for w in wffs do
		       (loop for e in (map-wff-internal w) do
			     (cond ((setq entry (assoc (car e) ans))
				    (rplacd entry (append (cdr e) (cdr entry))))
				   (t (push e ans)))))
		 (loop for e in ans collect
		       (cons (car e) (most-specific-types-of (cdr e))))))
	  (or (let (ans entry)
		(setq ans (loop for x in (map-wff-internal (car wffs)) collect
				(list (car x) (cdr x))))
		(loop for w in (cdr wffs) do
		      (setq ans
			    (loop for e in (map-wff-internal w)
				  when (setq entry (assoc (car e) ans)) collect
				  (cons (car e) (cons (cdr e) (cdr entry))))))
		; now the entry is a list of lists
		(loop for a in ans collect
		      (cons (car a)
			    (most-specific-types-of
			      (let (dist)
				(doxproduct (x (cdr a))
				    (let ((supers (listof y s.t. (subrel (car x) y))))
				      (loop for tp in (cdr x) do
					    (setq supers
						  (intersection supers
							 (listof y s.t. (subrel tp y)))))
				      (push supers dist)))
				(remove-duplicates (apply #'append dist))))))))))
    :quantified-wff
    #'(lambda (q qvars wff)
	(and (eq q 'e)
	     (loop for e in (map-wff-internal wff) unless (member (car e) qvars)
		   collect e)))))

;; The following is generally useful in implementation macros ...
;; we have code that produces an expansion assuming that certain keys are not present
;; We should remove the disallowed keys (save them), get the expansion
(defmacro warn-ignored-keys (name keys-var ignored-keys &body result
			     &aux (ignored-keys-var (gensym "G"))
			     (ignored-key-var (gensym "G"))
			     (temp-var (gensym "G"))
			     (result-var (gensym "G")))
  `(let (,ignored-keys-var ,temp-var ,result-var)
     (loop for ,ignored-key-var in ',ignored-keys
	   when (setq ,temp-var (getf ,keys-var ,ignored-key-var)) do
	   (setf (getf ,keys-var ,ignored-key-var) nil)
	   (push ,temp-var ,ignored-keys-var)
	   (push ,ignored-key-var ,ignored-keys-var))
     (setq ,result-var (progn ,.result))
     (setq ,ignored-keys-var
	   (loop for ,ignored-key-var on ,ignored-keys-var by #'cddr
		 unless (equal (cadr ,ignored-key-var)
			       (getf ,result-var (car ,ignored-key-var)))
		 collect (car ,ignored-key-var)))
     (if ,ignored-keys-var
	 (cons :warnings
	       (cons (cons (list "In DefRelation ~A ignored keys ~A"
				 ,name ,ignored-keys-var)
			   (getf ,keys-var :warnings))
		     ,result-var))
	 ,result-var)))

;; this is for (defrelation foo :derivation basetype)
(defun basetype (name keys)
  (warn-ignored-keys name keys
    (:definition :equivs :implementation :adder :arity
		 :deleter :updater :tester :generator :trigger)
    `(:arity 1 :derivation defined :definition ,(BaseTypeDef name)
	     :adder basetype-adder :deleter basetype-deleter
	     :alsofns
	     ,(cons `(lambda (rel)
		       (atomic
			 (add-matchnodes-for-basetype rel ',(BaseTypeDef name))
			 reveal
			 (++ subtype rel
			     (relationp
			       ',(let ((types (getf keys :types)))
				   (if (and types (symbolp (car types)))
				       (prog1 (car types)
					      (unless (cdr types)
						(setf keys (append '(:types nil) keys))))
				       'entity))))))
		    (getf keys :alsofns))
	     :computation nil :representation nil :implementation nil
	     :derivation nil ,@ keys)))

(defvar *update-macro-list*
	'(++ -- ?? #+ignore Inherit insist defrelation))
;When the FSD pkg wants to add to this list it should reset it.



#|
----------------------------------------------------------------
New macros:
defrepresentation (name &key updater tester generators testeffort
			     checkers)
defderivation (name &key updater tester generators
			 triggers testeffort)
defcomputation (name&key tester generators testeffort)

These, of course, declare new represenations and derivations.
|#

(defmacro defimplementation (name &key updater tester adder deleter
			     generators testeffort
			     derived checkers idempotent)
  (when (numberp testeffort)
    (setf testeffort `(lambda (&rest ignore)(declare (ignore ignore))
				,testeffort)))
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     (atomic (++ implementation ',name)
	   (,(if derived '++ '--) derived ',name)
	   (set-listof x s.t. (relupdater ',name x)
		       ,(when updater `(list #',updater)))
	   (set-listof x s.t. (reladder ',name x)
		       ,(when adder `(list #',adder)))
	   (set-listof x s.t. (reldeleter ',name x)
		       ,(when deleter `(list #',deleter)))
	   (set-listof x s.t. (reltester ',name x)
		       ,(when tester `(list #',tester)))
	   (set-listof x s.t. (relgenerator ',name x)
		       (list ,.(loop for g in generators collect `#',g)))
	   (set-listof x s.t. (checker ',name x)
		       (list ,.(loop for c in checkers collect `#',c)))
	   (set-listof x s.t. (testeffort ',name x)
		  ,(when testeffort `(list #',testeffort)))
	   (set-listof tv s.t. (idempotent ',name tv)
	       ',(loop for x in idempotent collect
		      (case x (:add t) (:delete nil)
			    (t (error "idempotent argument must be a list whose elements~
                                       are :add and :delete"))))))))


(defmacro defrepresentation (name &rest args &key updater tester adder deleter generators testeffort checkers idempotent)
  (declare (ignore updater tester adder deleter generators testeffort checkers idempotent))
  `(defimplementation ,name ,@args))

(defmacro defderivation (name &rest args &key updater tester adder deleter generators testeffort)
  (declare (ignore updater tester adder deleter generators testeffort))
  `(defimplementation ,name :derived t ,@args))

(defmacro defcomputation (name &rest args &key tester generators testeffort)
  (declare (ignore tester generators testeffort))
  `(defimplementation ,name :derived t ,@args))

; needed for transaction ... 
(defun history-label (name)
  (cond ((listp global-history)
	 (push (make-history-record
		 :generation# (incf generation#)
		 :prev-gen# (when global-history (generation# (car global-history)))
		 :consistency-cycles (list (make-consistency-cycle-record)))
	       global-history)
	 (add-structure-property (car global-history) name 'history-label))
	(t (error "cannot label history when history is not being recorded")))
  name)

; temporary until it's defined ...
(setf (macro-function 'cache-generators)
   #-aclpc1 #'ignored
   #+aclpc1 (symbol-function 'ignored))


(do-s.t. (r (relation r))
      (let ((args (make-list (arity* r) :initial-element nil)))
	(get-tester r)
	(try (get-update t r args) bad-update nil)
	(try (get-update nil r args) bad-update nil)))

;; now, for all later files...
(eval-when (:compile-toplevel :load-toplevel :execute)
  (setq defrel-available t))
;; At this point we could also decache all the add/delete/test-ers for
; existing relations so that they could compile into function calls
; rather than having to go thru property list lookup every time.

;; anonymous relation macro (where should this go)
(defmacro anon-rel (&rest def)
  (let ((rel (gethash def *anon-rel-table*)))
    (unless rel
      (when (and *compile-file-pathname* (null *in-anon-rel-context*))
	    (cerror
	     "do the defrelation anyway"
	     "cannot compile anon-rel to file outside defrel, rule, defun"))
      (setf rel (let (*warning-flags*)
		  (eval `(defrelation
			 ,(#+clisp gentemp #-clisp gensym "ANON-REL")
			 ,@def ;; leave it at ,@def so as not to change def
			 :cache-generators nil))))
      ;; gentemp in clisp might cause problems from separate compiles ***
      ;; needed cause compiled top level progn's don't preserve eq-ness
      ;; of gensyms, i.e., treated as if separate top level forms
      (unless (or (derivedrel rel) (?? maintainedrel rel $ $))
         (cerror "use it anyway" "anon-rel ~A should be derived" rel))
      (make-rel-anonymous rel def))
    rel))
