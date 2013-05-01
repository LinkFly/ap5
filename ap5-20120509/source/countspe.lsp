;;;-*- Mode: LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-

(in-package "AP5")

(Defmacro restrict-attribute-cardinality (typename relname &key
					  (countspec :any) (enforcement :incremental)
					  replacing default inverse
					  too-many-repair too-few-repair
					  delete-any-other-countspecs &aux pattern)
  `(restrict-cardinality ,relname ,(setq pattern
					 (cond (inverse (list 'output typename))
					       (t (list typename 'output))))
	:countspec ,countspec :enforcement ,enforcement :replacing ,replacing
	:default ,(when default
		   `(FUNCTIONAL-EQUIVALENCE-TESTABLE
			  #'(lambda (x)
			      (values-list (mapcar #'(lambda (y) (list y))
						   (multiple-value-list (funcall ',default x)))))
			  (list :old-multiple-default-repair ',relname ',pattern ',default)
			  ,(format nil "old-add-default-~a~a" relname pattern)))
	:too-many-repair ,too-many-repair :too-few-repair ,too-few-repair
	:delete-any-other-countspecs
	,(cond ((eq delete-any-other-countspecs t) t)
	       (delete-any-other-countspecs (list delete-any-other-countspecs)))))

(Defmacro restrict-cardinality (relname pattern &environment env &key
				(countspec :any) (enforcement :incremental)
				replacing default
				too-many-report too-few-report
				too-many-repair too-few-repair
				delete-any-other-countspecs
				&aux owff mwff nowff oname mname noname
				oreport mreport orepair mrepair
				oform mform noform)
#|
   Pattern corresponds to an argument list for the relation.
   Its elements should be either typenames or the symbol OUTPUT
   for all tuples of rel matching the types there must be <countspec> output tuples.
   countspec should be one of :unique :optional :multiple :any :none
   (:any can be used to remove a former constraint.)
   (:none is useful for restrictions on subtypes of the overall domain/range)
   enforcement should be one of :none :total :incremental
   delete-any-other-countspecs means for this relation and output pattern, remove
    any count constraints for ALL types, except what the argument specifies:
    T means only these types, a list of typename tuples means those are the
    exceptions (if only one input then the parens can be removed),
    nil of course means all types (don't remove any).
   replacing (only applies if optional or unique) 
    means throw out old on arrival of new
   default (only applies if multiple or unique) means if none otherwise
    then compute one
    default should be a function of input tuple that returns, as multiple values,
    output tuples to be related to the input tuple
|#
  (declare-type (countspec countspec) (enforcement enforcement))
  (loop for p in pattern unless
	(or (eq p 'output) (relationp p) (descriptionp p) (cl-type-name p env))
	do (warn "bad pattern element passed to restrict-cardinality - ~A" p))
  (when (eq countspec :any) (setq enforcement :none))
  (when (or (eq countspec :any) (eq countspec :multiple)
	    (eq countspec :none) (eq enforcement :none))
    (setq replacing nil))
  (when (or (eq countspec :any) (eq countspec :optional)
	    (eq countspec :none) (eq enforcement :none))
    (setq default nil))
  (cond ((eq t delete-any-other-countspecs)
	 (setq delete-any-other-countspecs (list pattern))))
  ; can't coerce a single pattern into a list - want to allow descriptions
  (flet ((rulename (intro)
	    (apply 'pack* intro "-" relname
		   "-FOR"
		   (loop for p in pattern nconc
			 (cond ((consp p) ;; cl-type-name
				(list "-" p))
			       ((eq (symbol-package relname) (symbol-package p))
				(list "-" p))
			       (t (list "-" (package-name (symbol-package p))
					":" p))))))
	 (xsymbols (l) (loop for n below (length l) collect (pack* 'x n))))
    (setf mname (rulename "MULTIPLE")
	mwff ; have to compute it at runtime since the rel and type might not
	     ; exist at macroexpand time
	(cond ((member countspec '(:multiple :unique))
	       `(multiple-trigger-fn ',relname ',pattern))
	      (t ''false))
	mrepair	(cond (default
		       (when too-few-repair
			 (error "Default and Too-Few-Repair both specified"))
		       (let (inputs outputs)
			 (setq inputs (loop for p in pattern as n from 0
					    unless (eq p 'output) collect (pack* 'x n)))
			 (setq outputs (loop for p in pattern as n from 0
					     when (eq p 'output) collect (pack* 'x n)))
		       `(FUNCTIONAL-EQUIVALENCE-TESTABLE
			  #'(lambda ,inputs
			      (loop for tuple in
				    (multiple-value-list (funcall (function ,default) ,@inputs)) do
				    (apply
				      #'(lambda ,outputs
					  (++ ,relname ,.(xsymbols pattern)))
				      tuple)))
			  (list :multiple-default-repair ',relname ',pattern ',default)
			  ,(format nil "add-default-~a~a" relname pattern))))
		      (too-few-repair `(function ,too-few-repair))
		      (t ''ignored))
        mreport	(cond ((eq enforcement :none) ''ignored)
		      (too-few-report `#',too-few-report)
		      (t `(FUNCTIONAL-EQUIVALENCE-TESTABLE
			    #'(lambda (&rest x)
				(report-multiple-violation ',relname ',pattern x))
			    (list :multiple-reporter (relationp ',relname) ',pattern)
			    ,(format nil "report-multiple-~a-for-~a" relname pattern))))
	oname (rulename "OPTIONAL")
	owff (cond ((member countspec '(:optional :unique))
		    `(optional-trigger-fn ',relname ',pattern
					   (compute-comparison ',relname ',pattern)))
		   (t ''false))
	orepair	(cond ((and replacing (member countspec '(:optional :unique)))
		       (when too-many-repair
			 (error "Replacing and Too-Many-Repair both specified"))
		       (let (xin xout)
			 (setq xin (loop for p in pattern as n from 0
					 unless (eq p 'output) collect (pack* 'x n)))
			 (setq xout (loop for p in pattern as n from 0
					  when (eq p 'output) collect (pack* 'x n)))
			 `(FUNCTIONAL-EQUIVALENCE-TESTABLE
			  #'(lambda ,xin
			      (loop for ,xout s.t.
				    (previously
				       (,relname ,.(xsymbols pattern)))
				    do
				    (-- ,relname ,.(xsymbols pattern))))
			  (list :optional-replace-repair (relationp ',relname) ',pattern)
			  ,(format nil "replace-old-~A~A" relname pattern))))
		      (too-many-repair `(function ,too-many-repair))
		      (t ''ignored))
	oreport	(cond ((eq enforcement :none) ''ignored)
		      (too-many-report `#',too-many-report)
		      (t `(FUNCTIONAL-EQUIVALENCE-TESTABLE
			    #'(lambda (&rest args)
				(new-report-optional-violation ',relname ',pattern args))
			    (list :optional-reporter (relationp ',relname) ',pattern)
			    ,(format nil "report-optional-~a-for-~a" relname pattern))))
	noname (rulename "NO")
	;; *** how about noreport?
	nowff (cond ((eq countspec :none)
		     `(none-trigger-fn ',relname ',pattern))
		    (t ''false))))
  (setf mform (cond ((equal mwff ''false) `(remove-rule-if-present ',mname))
		    (t `(neverpermit ',mname ,mwff ,mrepair ,enforcement :reporter ,mreport)))
	oform (cond ((equal owff ''false) `(remove-rule-if-present ',oname))
		    (t `(neverpermit ',oname ,owff ,orepair ,enforcement :reporter ,oreport)))
	noform (cond ((equal nowff ''false) `(remove-rule-if-present ',noname))
		     (t `(neverpermit ',noname ,nowff 'ignored ,enforcement))))
  (let (orule mrule nrule)
    `(eval-when (:compile-toplevel :load-toplevel :execute)
       ,@(when (and (setq orule (any x s.t. (rulename x oname) ifnone nil))
		    (?? ruletrigger orule (eval owff)))
	   ;; eval to get from (optional-trigger-fn ...) to (E (...) ...)
	   (loop for desc in (find-cached-code-for-rule orule)
		 when (compoundwffp (third desc))
		 collect (compile-code-for-desc desc)))
       ,@(when (and (setq mrule (any x s.t. (rulename x mname) ifnone nil))
		    (?? ruletrigger mrule (eval mwff)))
	   (loop for desc in (find-cached-code-for-rule mrule)
		 when (compoundwffp (third desc))
		 collect (compile-code-for-desc desc)))
       ,@(when (and (setq nrule (any x s.t. (rulename x noname) ifnone nil))
		    (?? ruletrigger nrule (eval nowff)))
	   (loop for desc in (find-cached-code-for-rule nrule)
		 when (compoundwffp (third desc))
		 collect (compile-code-for-desc desc)))
       (atomic ,oform ,mform ,noform
	       ,(when delete-any-other-countspecs
		  `(delete-other-countspecs
		     ',relname ',delete-any-other-countspecs))
	       ,countspec))))  ; seems like a good thing to return

; delete-any-other-countspecs defined later - uses optional<=for

(defun remove-rule-if-present (&rest names)
  (atomic (loop for name in names
	    do (forany rule s.t. (rulename rule name)
		       (-- consistencyrule rule)
		       ifnone nil)
	    (insist not (e (rule) (rulename rule name))))))

(defun new-report-optional-violation (rel pattern args)
  (format *error-output*
	  "~&Count constraint violation for relation ~A~A~
           ~% more than one tuple for ~A~%"
	  rel pattern args))
#+ignore ; old
(defun report-optional-violation (rel pattern args &aux inputs outputs1 outputs2)
  (loop for p in pattern unless (eq p 'output) do
	(push (pop args) inputs))
  (setq inputs (reverse inputs))
  (loop for p in pattern when (eq p 'output) do
	(push (pop args) outputs1))
  (setq outputs1 (reverse outputs1))
  (setq outputs2 args)
  (format *error-output*
	  "~&Count constraint violation for relation ~A ~A~
           ~% ~A should not be related to both ~
           ~% ~A and ~A~%"
	  rel pattern inputs outputs1 outputs2))

(defun report-multiple-violation (rel pattern args)
  (format *error-output*
	  "~&Count constraint violation for relation ~A~A ~
           ~% ~A should be related to something~%"
	  rel pattern args))

(defun multiple-trigger-fn (rel pattern)
  `(E ,(loop for p in pattern as n from 0 unless (eq p 'output) collect
		    (pack* 'x n))
      (and (not (E ,(loop for p in pattern as n from 0 when (eq p 'output) collect
			  (pack* 'y n))
		   (,rel ,.(loop for p in pattern as n from 0 collect
				(pack* (cond ((eq p 'output) 'y) (t 'x)) n)))))
	   ,.(loop for p in pattern as n from 0 unless (eq p 'output) collect
		   (list p (pack* 'x n))))))

(defun multiple-triggerp (trigger &aux pattern rel temp temp2)
  ; if trigger really is a multiple trigger, return (rel pattern)
  (and trigger
       (eq-length trigger 3) ;(E (x) and)
       (geq-length (setq temp (third trigger)) 2) ;(and (not ...) (type ...) ...)
       (eq-length (setq temp2 (cadr temp)) 2) ; (not ...)
       (eq-length (setq temp2 (cadr temp2)) 3) ; (e (y) (r ...))
       (listp (setq temp2 (third temp2))) ; (r ...)
       (setq rel (pop temp2))
       (or (setq temp (cddr temp)) t)
       (or (setq pattern
		 (loop for arg in temp2 as n from 0 collect
		       (cond ((eq arg (pack* 'x n)) (car (ilistp (pop temp))))
			     (t 'output))))
	   t)
       (equal trigger (multiple-trigger-fn rel pattern))
       (list (list rel pattern))))

; try to work for descriptions too
(defun compute-comparison (relname pattern &aux rel)
  (cond ((setq rel (relationp relname))
	 (loop for p in pattern as n from 0 when (eq p 'output) collect
	       (relationnamep (get-comparison rel n t))))
	((descriptionp relname)
	 (loop for v in (car (expanddescription relname)) collect
	       (or (relationnamep (varcompare v))
		   (error "no (single) comparison for ~A" relname))))
	(t (error "~A is not a relationname or description"))))

(defun optional-trigger-fn (rel pattern comparetuple)
  (when (= (length comparetuple) (loop for p in pattern count (eq p 'output)))
    `(E ,(loop for p in pattern as n from 0 unless (eq p 'output) collect (pack* 'x n))
	(E (,.(loop for p in pattern as n from 0 when (eq p 'output) collect (pack* 'y n))
	    ,.(loop for p in pattern as n from 0 when (eq p 'output) collect (pack* 'z n)))
	   (and
	     (,rel ,.(loop for p in pattern as n from 0 collect
			   (pack* (cond ((eq p 'output) 'z) (t 'x)) n)))
	     (or ,.(loop for p in pattern as n from 0 when (eq p 'output) collect
			 (list 'not (list (pop comparetuple) (pack* 'y n) (pack* 'z n)))))
	     (or (and 
		   (start (,rel ,.(loop for p in pattern as n from 0 collect
					(pack* (cond ((eq p 'output) 'y) (t 'x)) n))))
		   ,.(loop for p in pattern as n from 0 unless (eq p 'output) collect
			   (list p (pack* 'x n))))
		 (and (,rel ,.(loop for p in pattern as n from 0 collect
				    (pack* (cond ((eq p 'output) 'y) (t 'x)) n)))
		      (start
			(and
			  ,.(loop for p in pattern as n from 0 unless (eq p 'output) collect
				  (list p (pack* 'x n))))))))))))

(defun optional-triggerp (trigger &aux pattern rel compare tr temp temp2 temp3)
  (and trigger
       (eq-length trigger 3) ;(E (x) ..)
       (eq-length (setq tr (third trigger)) 3) ; (E (y z) ..)
       (eq-length (setq tr (third tr)) 4) ;(and ...)
       (ilistp (setq temp (cadr tr))) ; (R ...)
       (setf rel (car temp) pattern (make-list (length (cdr temp))
					       :initial-element 'output))
       (listp (setq temp2 (third tr))) ; (or (not equiv) ...)
       (setq compare (loop for arg in (cdr temp2) collect (car (ilistp (cadr (ilistp arg))))))
       (eq-length (setq temp3 (fourth tr)) 3) ; (or (and ..) (and ..))
       (eq-length (setq temp3 (third temp3)) 3) ; (and (R ..) (start ...))
       (eq-length (setq temp3 (third temp3)) 2) ; (start (and ...))
       (prog1 t (loop for type in (cdr (ilistp (cadr temp3)))
		      when (setq temp2 (position (cadr (ilistp type)) (cdr temp)))
		      do (setf (nth temp2 pattern) (car (ilistp type)))))
       (equal trigger (optional-trigger-fn rel pattern compare))
       (list (list rel pattern compare))))

#+ignore ; old
(defun optional-trigger-fn (rel pattern comparetuple)
  (when (= (length comparetuple) (loop for p in pattern count (eq p 'output)))
    `(E (,.(loop for p in pattern as n from 0 unless (eq p 'output) collect (pack* 'x n))
	 ,.(loop for p in pattern as n from 0 when (eq p 'output) collect (pack* 'y n))
	 ,.(loop for p in pattern as n from 0 when (eq p 'output) collect (pack* 'z n)))
	(and
	  (,rel ,.(loop for p in pattern as n from 0 collect
			(pack* (cond ((eq p 'output) 'y) (t 'x)) n)))
	  (,rel ,.(loop for p in pattern as n from 0 collect
			(pack* (cond ((eq p 'output) 'z) (t 'x)) n)))
	  (or ,.(loop for p in pattern as n from 0 when (eq p 'output) collect
		      (list 'not (list (pop comparetuple) (pack* 'y n) (pack* 'z n)))))
	  ,.(loop for p in pattern as n from 0 unless (eq p 'output) collect
		  (list p (pack* 'x n)))))))
#+ignore ; old
(defun optional-triggerp (trigger &aux pattern rel compare temp temp2 temp3)
  (and trigger
       (eq-length trigger 3) ;(E (x) and)
       (geq-length (setq temp (third trigger)) 4) ;(and rel rel or ...)
       (ilistp (setq temp2 (cadr temp)))
       (setq rel (pop temp2))
       (listp (setq temp3 (fourth temp))) ; (or (not equiv) ...)
       (or (pop temp3) t)
       (or (setq pattern
		 (loop for arg in temp2 as n from 0 with rest = (cddddr temp) collect
		       (cond ((eq arg (pack* 'x n)) (car (ilistp (pop rest))))
			     (t 'output))))
	   t)
       (or (setq compare
		 (loop for arg in temp2 as n from 0 when (eq arg (pack* 'y n)) collect
		       (let ((neq (pop temp3)))
			 (when (and (eq-length neq 2) (eq-length (cadr neq) 3))
			   (caadr neq))))) ; (not (equiv x y)
	   t)
       (equal trigger (optional-trigger-fn rel pattern compare))
       (list (list rel pattern compare))))

(defun none-trigger-fn (rel pattern)
  `(E ,(loop for p in pattern as n from 0 collect
	     (pack* (cond ((eq p 'output) 'x) (t 'y)) n))
      (and (,rel ,.(loop for p in pattern as n from 0 collect
			 (pack* (cond ((eq p 'output) 'y) (t 'x)) n)))
	   ,.(loop for p in pattern as n from 0 unless (eq p 'output) collect
		   (list p (pack* 'x n))))))

(defun none-triggerp (trigger &aux temp temp2 rel pattern)
  (and trigger
       (eq-length trigger 3)
       (geq-length (setq temp (third trigger)) 2)
       (ilistp (setq temp2 (cadr temp)))
       (setq rel (pop temp2))
       (or (setq pattern
		 (loop for arg in temp2 as n from 0 with rest = (cddr temp) collect
		       (cond ((eq arg (pack* 'x n)) (car (ilistp (pop rest))))
			     (t 'output))))
	   t)
       (equal trigger (none-trigger-fn rel pattern))
       (list (list rel pattern))))

#|
;goal:
(multiple-trigger-fn 'rel '(t1 output output t2))
(E (X0 X3)
   (AND (NOT (E (Y1 Y2) (REL X0 Y1 Y2 X3)))
        (T1 X0)
        (T2 X3)))
(multiple-triggerp *)
((REL (T1 OUTPUT OUTPUT T2)))

(optional-trigger-fn 'rel '(t1 output output ((x) s.t. (q x))) '(e1 e2))
(E (X0 X3 Y1 Y2 Z1 Z2)
   (AND (REL X0 Y1 Y2 X3)
        (REL X0 Z1 Z2 X3)
        (OR (NOT (E1 Y1 Z1)) (NOT (E2 Y2 Z2)))
        (T1 X0)
        (((X) S.T. (Q X)) X3)))
(optional-triggerp *)
((REL (T1 OUTPUT OUTPUT ((X) S.T. (Q X))) (E1 E2)))


(none-trigger-fn 'rel '(t1 output output t2))
(E (X0 X3 Y1 Y2)
   (AND (REL X0 Y1 Y2 X3) (T1 X0) (T2 X3)))
(none-triggerp *)
((REL (T1 OUTPUT OUTPUT T2)))
|#

(atomic
  (++ codedrelname 'multiple-trigger
    '((rel pattern trigger) s.t. (equal trigger (multiple-trigger-fn rel pattern))))
  reveal
  (++ compare-relation (relationp 'multiple-trigger) 2 (relationp 'equal))
  (++ compare-relation (relationp 'multiple-trigger) 1 (relationp 'equal)))
(SimpleMultipleGenerator '(multiple-trigger output output trigger)
			 '(multiple-triggerp trigger))
(SimpleGenerator '(multiple-trigger rel pat output)
		 '(list (multiple-trigger-fn rel pat)))


(atomic
  (++ codedrelname 'optional-trigger
    '((rel pattern equiv trigger) s.t.
      (equal trigger (optional-trigger-fn rel pattern equiv))))
  reveal
  (++ compare-relation (relationp 'optional-trigger) 1 (relationp 'equal))
  (++ compare-relation (relationp 'optional-trigger) 2 (relationp 'equal))
  (++ compare-relation (relationp 'optional-trigger) 3 (relationp 'equal)))
(SimpleMultipleGenerator '(optional-trigger output output output trigger)
			 '(optional-triggerp trigger))
(SimpleGenerator '(optional-trigger rel pat equiv output)
		 '(list (optional-trigger-fn rel pat equiv)))


(atomic
  (++ codedrelname 'none-trigger
    '((rel pattern trigger) s.t. (equal trigger (none-trigger-fn rel pattern))))
  reveal
  (++ compare-relation (relationp 'none-trigger) 2 (relationp 'equal))
  (++ compare-relation (relationp 'none-trigger) 1 (relationp 'equal)))
(SimpleMultipleGenerator '(none-trigger output output trigger)
			 '(none-triggerp trigger))
(SimpleGenerator '(none-trigger rel pat output)
		 '(list (none-trigger-fn rel pat)))

(++ definedrelname 'multiple-for
    '((relname pattern) s.t.
      (e (rule trigger)  ;consistencyrule#rule may only make things worse
	 (and (ruletrigger rule trigger)
	      ;(relationname rel relname)
	      (multiple-trigger relname pattern trigger)
	      ; again for efficiency
	      ;(relation-in-defn rel rule)
	      ;(relation-in-defn type rule)
	      ))))
;; The rel-in-defn really does help a lot if we want to GENERATE.
;; However, the code that actually exists only tries to test.
;; The PROBLEM with including it is that we can no longer get constraints
;; recognized for DESCRIPTIONS!

(++ definedrelname 'optional-for
    '((relname pat) s.t.
      (E (RULE TRIGGER EQUIV)  ;consistencyrule#rule may only make things worse
	 (AND ;(relationname rel relname)
	      (RULETRIGGER RULE TRIGGER)
	      (OPTIONAL-TRIGGER RELname pat EQUIV TRIGGER)
	      ; efficiency hack
	      ;(relation-in-defn rel rule)
	      ;(relation-in-defn type rule)
	      ))))

(++ definedrelname 'none-for
    '((relname pattern) s.t.
      (e (rule trigger)  ;consistencyrule#rule may only make things worse
	 (and (ruletrigger rule trigger)
	      ;(relationname rel relname)
	      (none-trigger relname pattern trigger)
	      ; again for efficiency
	      ;(relation-in-defn rel rule)
	      ;(relation-in-defn type rule)
	      ))))

(defun delete-other-countspecs (relname patterns &aux rel check)
  (unless (setq rel (or (relationp relname)
			(and (descriptionp relname)
			     (block find-a-rel
			       (map-wff (caddr relname)
					:primitive-wff
					#'(lambda (&rest args)
					    (return-from find-a-rel (car args))))))))
    (error "~A is neither a relation name nor (non-trivial) description" relname))
  (loop for rule s.t. (relation-in-defn rel rule) do
	(forany trigger s.t. (ruletrigger rule trigger)
		(when (setq check (or (multiple-triggerp trigger)
				      (optional-triggerp trigger)
				      #+ignore
				      (old-optional-triggerp trigger)
				      (none-triggerp trigger)))
		  (when (same-rel-or-desc (caar check) relname)
		    (when (or (eq t patterns)
			      (not (member (cadar check) patterns :test
					   #'(lambda (x y)
					       (loop for xx in x as yy in y
						     always (same-rel-or-desc xx yy))))))
		      (-- consistencyrule rule))))
		ifnone nil)))

; ideally we'd like to detect that two desc's are equivalent
; for now we settle for recognizing synonyms
; next try to recognize trivial defns!
(defun same-rel-or-desc (r1 r2)
  (or (equal r1 r2)
      (let ((rr1 (relationp r1)) (rr2 (relationp r2)) n)
	(or (eq rr1 rr2); compare rels with names and synonyms
	    (and rr1 rr2 ;; if null then arity breaks
		 (= (arity* rr1) (setq n (arity* rr2)))
		 (or (getdefn rr1) (getdefn rr2))
		 (let ((args (loop for i below n collect (gensym "A")))
		       d1 d2)
		   (same-wff (caddr (setq d1 (expanddescription
					       (list args 's.t. (cons r1 args)))))
			     (caddr (setq d2 (expanddescription
					       (list args 's.t. (cons r2 args)))))
			     (mapcar #'cons (car d1) (car d2)))))))
      (and (descriptionp r1) (descriptionp r2)
	   (equal (car r1) (car r2))
	   (equal (expanddescription r1) (expanddescription r2)))))

(++ definedrelname 'Unique-For
    '((rel pat) s.t. (and (multiple-for rel pat) (optional-for rel pat))))

(++ definedrelname 'Any-For
    '((rel pat) s.t.
      (and (not (multiple-for rel pat))
	   (not (optional-for rel pat))
	   (not (none-for rel pat)))))


;---------------- these probably belong elsewhere ----------------
; *** also, these seem like bad names - these names sound like typeconstraints
; whereas the functions seem to be creating conditional typeconstraints


(defmacro-displace restrict-attribute-range (domaintypename relname rangetypename
				    &key (enforcement :incremental) (remove-tuple t)
				    (reporter `(lambda (x y)
					       (report-conditional-rangetype-violation
						 ',relname ',domaintypename
						 ',rangetypename x y))))
  `(restrict-attribute-domain-or-range ,domaintypename ,relname ,rangetypename
	     :enforcement ,enforcement :remove-tuple ,remove-tuple
	     :reporter ,reporter))

(defmacro-displace restrict-attribute-domain (domaintypename relname rangetypename
				    &key (enforcement :incremental) (remove-tuple t)
				    (reporter `(lambda (x y)
					       (report-conditional-domaintype-violation
						 ',relname ',domaintypename
						 ',rangetypename x y))))
  `(restrict-attribute-domain-or-range ,domaintypename ,relname ,rangetypename
	     :inverse t :enforcement ,enforcement
	     :remove-tuple ,remove-tuple :reporter ,reporter))

(defmacro-displace restrict-attribute-domain-or-range (domaintypename relname rangetypename
				    &key enforcement (remove-tuple t) inverse reporter
				    &aux name wff repair)
  ; for all x of type <domaintypename>, for all y s.t. (<relname> x y), 
  ;  y is of type <rangetypename>
  ; (if INVERSE = T, the interpretation is
  ; for all y of type <rangetypename>, for all x s.t. (<relname> x y), 
  ;  x is of type <domaintypename> 
  ; enforcement should be one of :none :total :incremental
  ; to remove a constraint, use entity for rangetype (domaintype if inverse)
  ; remove-tuple means (as in unconditional type constraints)
  ;  that if the constraint is violated by a change of type , then fix the problem by
  ;  removing the tuple of the relation
  (declare-type (typename domaintypename rangetypename)
		(binary-relationname relname) (enforcement enforcement))
  (setq name
	(intern (concatenate 'string "TYPE-OF-" (symbol-name relname)
			     (if inverse "<=" "")
			     "-OF-" (symbol-name domaintypename))
		(symbol-package relname))
	wff
	(cond ((and (null inverse)(eql rangetypename 'entity) 'true))
	      ((and inverse (eql domaintypename 'entity) 'true))
	      (inverse `(A (d		      
			    ,(intern (concatenate 'string (symbol-name rangetypename) "#")
				      (symbol-package rangetypename)))
		     (implies (,relname d ,rangetypename) (,domaintypename d))))
	      (t `(A (,(intern (concatenate 'string (symbol-name domaintypename) "#")
			 (symbol-package domaintypename))		      
		      r)
		     (implies (,relname ,domaintypename r) (,rangetypename r))))))
  (setq repair
	(if remove-tuple
	    (if inverse
		`(lambda (d r)
		  (declare (optimize (speed 3)(safety 1)(compilation-speed 0)))
		   (or (?? start (,rangetypename r))
				   (?? start (not (,domaintypename d))))
		   (-- ,relname d r))
	      `(lambda (d r)
		 (declare (optimize (speed 3)(safety 1)(compilation-speed 0)))
		 (or (?? start (,domaintypename d))
				 (?? start (not (,rangetypename r))))
		 (-- ,relname d r)))
	  'ignored ))
  `(alwaysrequire ',name ',wff ',repair ,enforcement :reporter ',reporter))

(defun report-conditional-rangetype-violation (rel domain range x y)
  (format *error-output*
	  "~%Conditional type constraint violation for relation ~A ~
           ~% ~A was of type ~A but ~A was not of type ~A"
	  rel x domain y range))

(defun report-conditional-domaintype-violation (rel domain range x y)
  (format *error-output*
	  "~%Conditional type constraint violation for relation ~A ~
           ~% ~A was of type ~A but ~A was not of type ~A"
	  rel y range x domain))

; ----------------
;; here are some new things that originated in fsd-relations

; Too bad we can't really test subrel for descriptions.
; It would also be nice if we could look for constraints on superrel relations.

(defun cardinality-of-pattern (rel-or-name pattern &aux rel pat min max)
  (unless (setq rel (or (relationp rel-or-name)
			(and (descriptionp rel-or-name)
			     (block find-a-rel
			       (map-wff (caddr rel-or-name)
					:primitive-wff
					#'(lambda (&rest args)
					    (return-from find-a-rel (car args))))))))
    (error "~A is not a relation name or (non-trivial) description" rel-or-name))
  (unless (= (cond ((listp rel-or-name) (length (car rel-or-name)))
		   (t (arity* rel)))
	     (length pattern))
    (error "wrong number of arguments for ~A" rel-or-name))
  (setq pat (loop for p in pattern collect
		  (cond ((eq p 'output) p)
			((relationp p))
			((descriptionp p))
			(t (error "~A is not a type or description" p)))))
  (do-s.t. ((rule tr)
	    (and (relation-in-defn rel rule) (ruletrigger rule tr)))
       (declare (ignorable rule))
       ; lucid evidently WARNs if it's not declared ignored,
       ; but aclpc signals an ERROR (!!) if it is declared ignored.
	(let (rtype rpat)
	  (when (or (and (null max)
			 (setq rpat (or (optional-triggerp tr)
					#+ignore
					(old-optional-triggerp tr)))
			 (setq rtype :optional))
		    (and (null min)
			 (setq rpat (multiple-triggerp tr))
			 (setq rtype :multiple))
		    (and (none-triggerp tr)
			 (setq rtype :none)))
	    ; A constraint for person holds for employee but not vice versa.
	    ; At most n for (person output output) => at most n for (person project output)
	    ;  but at least n for (person output output) does not restrict it.
	    ; At least n for (person project output) does imply something about
	    ;  (person output output) - at least n times the number of projects.
	    ;  However we do not try to handle this at present.
	    (when (and (same-rel-or-desc (caar rpat) rel-or-name)
		       (loop for rp in (cadar rpat) as p in pat always
			     (or (and (eq p 'output) (eq rp 'output))
				 (and (eq rp 'output) (not (eq rtype :multiple)))
				 (?? subrel p (relationp rp)))))
	      (ecase rtype
		(:none (return-from cardinality-of-pattern :none))
		(:optional (setq max t))
		(:multiple (setq min t)))))
	  (when (and min max) (return-from cardinality-of-pattern :unique))))
  (cond (min :multiple) (max :optional) (t :any)))


; This one at least works for constraints that use descriptions in the pattern.
(defun cardinality-for-tuple (rel-or-name i-o-pattern
				&optional (output-indicator 'output)
				&aux rel min max)
  (unless (setq rel (or (relationp rel-or-name)
			(and (descriptionp rel-or-name)
			     (block find-a-rel
			       (map-wff (caddr rel-or-name)
					:primitive-wff
					#'(lambda (&rest args)
					    (return-from find-a-rel (car args))))))))
    (error "~A is not a relation name or (non-trivial) description" rel-or-name))
  (unless (= (cond ((listp rel-or-name) (length (car rel-or-name)))
		   (t (arity* rel)))
	     (length i-o-pattern))
    (error "wrong number of arguments for ~A" rel-or-name))
  (loop for (rule tr) s.t. (and (relation-in-defn rel rule) (ruletrigger rule tr)) do
	(let (rtype rpat)
	  (when (or (and (null max)
			 (setq rpat (or (optional-triggerp tr)
					#+ignore
					(old-optional-triggerp tr)))
			 (setq rtype :optional))
		    (and (null min)
			 (setq rpat (multiple-triggerp tr))
			 (setq rtype :multiple))
		    (and (none-triggerp tr)
			 (setq rtype :none)))
	    ; remarks above apply
	    (when (and (same-rel-or-desc (caar rpat) rel-or-name)
		       (loop for rp in (cadar rpat) as x in i-o-pattern always
			     (or (and (eq x output-indicator) (eq rp 'output))
				 (and (eq rp 'output) (not (eq rtype :multiple)))
				 (and (not (eq rp 'output)) (not (eq x output-indicator))
				      (?? funcall rp x)))))
	      (ecase rtype
		(:none (return-from cardinality-for-tuple :none))
		(:optional (setq max t))
		(:multiple (setq min t)))))
	  (when (and min max) (return-from cardinality-for-tuple :unique))))
  (cond (min :multiple) (max :optional) (t :any)))

