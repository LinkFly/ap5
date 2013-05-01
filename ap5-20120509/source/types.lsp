;;;-*- Mode:LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-
(in-package "AP5")

; This file must be compiled after it is loaded (which is after relations is loaded),
; but before Rule-Idioms is loaded (which changes the adder for SubType), and 
; with BootStrapping set to T (Final sets it to nil).
(eval-when (:compile-toplevel :load-toplevel :execute) (setq bootstrapping t))

#+symbolics
(eval-when (:compile-toplevel)
  (or (equal (si:undigest (theonly x s.t. (reladder (relationp 'subtype) x)))
	     '(lambda (&rest ignore) (declare (ignore ignore)) 'subtype-adder-temp))
      (error "this file has to be compiled before loading subtyperules")))
;
; Create the type lattice, define (I)SubRel, etc.
; this file must be compiled with Bootstrapping set to T - 
; so that the references to rels will be written in a form
; that can be read back in before the rels and readers exist.

; need types for restrictions for relations:
; matchnode trigger[s.t.-expression] name[symbol] fn text[->DocumentationObject]
; 

;;       Summary of initial type structure:
;
; Entity (def: lambda(x)t)
;   Number (def: lambda(x)(numberp x))
;     Integer
;   Context ;***
;   Text ;***
;     string
;   Function
;   List-Or-Nil
;     List
;       description (vars s.t. wff) 
;   Rel-Or-imp
;     Relation
;   symbol
;   Integer-Or-Nil
;     Integer
;   string
;   ...
;   DBObject (def: lambda(x)(DBObject-p x))
;     <here are all the base types - person, etc.>
;     MatchNode 
;     Rule
;       AutomationRule
;       ConsistencyRule
;     Relation (i.e., in the Implementation relation)
;       Type (i.e., in the Type relation)
;         BaseType (i.e., defined via classification and subtype)

;; in addition to those with *** after them, we are missing (from ap3):
;  Code (something that can be eval'd)
;  non-nil-symbol
;  real (number)
;  array
;  process
;  package

; --------------------------------
; becomes a lot simpler with two-way-structprop ...

(add-imparityname (setq Rel-ISubRel (make-dbobject))
		  'two-way-structprop  2 'ISubRel)

(++ RelSize Rel-ISubRel '(Input Output) 1)
(++ RelSize Rel-ISubRel '(Output Input) 2)

; ---------------- tclosure ----------------

(++ derived 'tclosure)
(++ baserelname 'tclosure 2)
(++ definedrelname 'transitive-closure
    '((x y) s.t.
      (E (rel closure) (and (relationname rel x)
			    (relationname closure y)
			    (tclosure rel closure)))))
(++ reladder (relationp 'transitive-closure)
    '(lambda (&rest ignore) (declare (ignore ignore)) 'transitive-closure-adder))
(defun transitive-closure-adder (ignore immediate closure)
  (declare (ignore ignore))
  (cond ((?? transitive-closure immediate closure)
	 (insist "supposed to add it" transitive-closure immediate closure))
	(t (let ((irel
		   (or (relationp immediate)
		       (abort 'unknown-relation "no relation named ~A" immediate)))
		 (rel (make-dbobject)))
	     (atomic (add-imparityname rel 'tclosure 2 closure)
		     (++ tclosure irel rel))))))
(++ reltester 'tclosure
    '(lambda (rel &rest ignore) (declare (ignore ignore)) (test-tclosure rel)))
(defun test-tclosure (rel &aux genxdesc genx genxcost
			  genydesc geny genycost 
			  compare compare-cost)
  (setf compare (get-comparison rel 0 t))
  (setf compare-cost (testeffort `(,compare x y)))
  (setf genxdesc
	(expanddescription
	 `((z) s.t (,rel z y)) :allowevalargs t)
	genydesc
	(expanddescription
	 `((z) s.t (,rel x z)) :allowevalargs t)
	genx (findgenerator (car genxdesc) (caddr genxdesc) t)
	geny (findgenerator (car genydesc) (caddr genydesc) t))
  (when genx (setf genxcost (ifplus (effort genx)
				    (iftimes compare-cost (size genx)))))
  (when geny (setf genycost (ifplus (effort geny)
				    (iftimes compare-cost (size geny)))))
  (unless (or genx geny) (error "cannot even test ~A" rel))
  `(lambda (ignore x y) (declare (ignore ignore))
     (loop for z s.t.
	   ,(if (iflessp genxcost genycost)
		`(,rel z y)
	        `(,rel x z))
	   thereis
	   ,(get-test-function (get-comparison rel 0 t) 'z
			       (if (iflessp genxcost genycost) 'x 'y)))))

(defun constant-t () t)
(defun tclosure-generator (ignore vars rel &rest ignore2 &aux
				  (irel (theonly r s.t. (tclosure r rel)))
				  (compare (get-comparisons-and-canonicalizers rel))
				  desc gen result direction direction-cost)
  (declare (ignore ignore ignore2 vars))
  (flet ((deffort (args)
	   (iftimes (effort gen)
		    (ifquotient (relationsize '(x) (cons rel args)) 
				(relationsize '(x) (cons irel args)))))
	 (tcinitstate (args)
	   `(lambda (ignore y &aux tree queue fn cell compare)
	      (declare (ignore ignore))
	      ; state consists of a tree containing previously
	      ; generated, a queue of elements to be expanded
	      ; and the current generating function
	      (setf tree (createtree) queue (list y) fn 'constant-t
		    cell (list nil) ; to be smashed
		    compare (load-memo (list #',(if (listp (cadr compare)) (caadr compare) (cadr compare)))))
	      #+ignore
	       (setf (car compare) ; how can I do '(#'...) ?
		    #',(if (listp (cadr compare)) (caadr compare) (cadr compare)))
	      #'(lambda (&aux next done)
		  (declare (ignorable done))
		  (loop
		    (cond
		      ((multiple-value-setq (done next) (funcall fn))
		       (if (null queue)
			   (return t)
			   (setf fn
				 (funcall (LOAD-MEMO
					    (LOOKUP-GEN
					      (MMEMO ((X0) S.T.
						      (,(relationnamep irel)
						       ,.args)))))
					  (pop queue)))))
		      ((treetester
			 ; reuse a cons cell instead of consing every time
			 (progn (setf (car cell) ,(cond ((listp (cadr compare))
							 (list (cadadr compare) 'next))
							(t 'next)))
				cell)
			 tree compare))
		      (t (treeadder cell tree compare)
			 (push next queue)
			 (return (values nil next)))))))))
  (when (setf gen (findgenerator (car (setf desc (expanddescription
						  `((x) s.t. (,irel x y))
						  :allowevalargs t)))
				(caddr desc)
				t))
    (push
      `((template (output input))
	(effort ,(deffort '(x y)))
	; assume that effort per tuple is same as for irel
	(initialstate ,(tcinitstate '(x0 c0))))
      result))
  (when (setf gen (findgenerator (car (setf desc (expanddescription
						  `((y) s.t. (,irel x y))
						  :allowevalargs t)))
				(third desc)
				t))
    (push
      `((template (input output))
	(effort ,(deffort '(y x)))
	; assume that effort per tuple is same as for irel
	(initialstate ,(tcinitstate '(C0 X0))))
      result)))
  (when (setf gen (findgenerator (car (setf desc (expanddescription
						  `((x y) s.t. (,irel x y))
						  :allowevalargs t)))
				(third desc)
				t))
    ; in this case we know that the other two generators exist
    (push `((template (output output))
	    (effort
	      ,(let ((effort (ifplus (effort gen)
				     (iftimes 20 (relationsize '(x y) (cons rel '(x y)))))))
		 ; estimate 20 instructions per output?
		 (if (ifleq (cadr (assoc 'effort (car result)))
			    (cadr (assoc 'effort (cadr result))))
		     (setf direction t direction-cost (cadr (assoc 'effort (car result))))
		     (setf direction nil direction-cost (cadr (assoc 'effort (cadr result)))))
		 (if (ifleq effort direction-cost) (ifplus 1 direction-cost) effort)))
	    ; cost of total MUST be more than of one direction or we get infinite recursion
	    (initialstate
	      (lambda (ignore &aux gen1 val1 gen2 val2)
		(declare (ignore ignore))
		(setq gen1 (funcall
			     (load-memo
			       (lookup-this-generator
				 ((X0) S.T. (E (X1) (,(relationnamep irel)
						     ,.(if direction '(X0 X1)
							   '(X1 X0))))))))
		      gen2 'constant-t)
		#'(lambda (&aux exhausted)
		    #+lucid (declare (ignore exhausted))
		    (block tclosure-gen
		      (loop
			(if (not (multiple-value-setq (exhausted val2) (funcall gen2)))
			    (return-from tclosure-gen
			      (values nil ,.(if direction '(val1 val2) '(val2 val1))))
			    (if (multiple-value-setq (exhausted val1) (funcall gen1))
				(return-from tclosure-gen t)
				(setf gen2
				      (funcall
					(load-memo
					  (lookup-this-generator
					    ((x0) S.T. (,(relationnamep rel)
							,.(if direction '(c0 X0)
							      '(X0 c0))))))
					val1))))))))))
	  result))
  (values-list result))

(++ relgenerator 'tclosure 'tclosure-generator)


; This same function has to work for any implementation of irel.  The solution is to
; cache a function to be compiled on first use.
;; THIS SHOULD BE DONE SO THE COMPILATION GOES TO A FILE
(defun trigger++tclosures (crel addp delp &aux code irel)
  (declare (ignore addp delp))
  (unless (and (setq code (get-structure-property crel 'tclosure-adder))
	       (?? tclosure (cdr code) crel)
	       (setq code (car code))) ;make sure it's the right tclosure
    (setq irel (any x s.t. (tclosure x crel)))
    (setq code
	  (let ((equiv (relationnamep (get-comparison irel 0 t)))
		(iname (relationnamep irel))
		(cname (relationnamep crel)))
	    (compile-ap
	      `(lambda nil
		 (loop for (arg1 arg2) s.t. (start (,iname arg1 arg2)) do
		       (loop for (x y) s.t.
			     (and (or (,cname x arg1) (,equiv x arg1))
				  (or (,cname arg2 y) (,equiv y arg2)))
			     unless (?? previously (,cname x y))
			     do (++ ,cname x y)))))))
    (put-structure-property crel (cons code irel) 'tclosure-adder))
  (funcall code))


;; THIS SHOULD BE DONE SO THE COMPILATION GOES TO A FILE
(defun trigger--tclosures (crel addp delp &aux code irel)
  (declare (ignore addp delp))
  (unless (and (setq code (get-structure-property crel 'tclosure-deleter))
	       (?? tclosure (cdr code) crel)
	       (setq code (car code))) ;make sure it's the right tclosure
    (setq irel (any x s.t. (tclosure x crel)))
    (setq code
	  (let ((equiv (relationnamep (get-comparison irel 0 t)))
		(iname (relationnamep irel))
		(cname (relationnamep crel)))
	    (compile-ap
	      `(lambda nil
		 (loop for (arg1 arg2) s.t. (start (not (,iname arg1 arg2))) do
		       (loop for (x y) s.t.
			     (previously
			       (and (or (,cname x arg1) (,equiv x arg1))
				    (or (,cname arg2 y) (,equiv y arg2))))
			     unless (?? ,cname x y)
			     do (-- ,cname x y)))))))
    (put-structure-property crel (cons code irel) 'tclosure-deleter))
  (funcall code))

;; more constraints later

; ---------------- SubRel ----------------
(add-imparityname (make-dbobject) 'two-way-structprop  2 'SubRel-stored)
(++ definedrelname 'subrel '((sub super) s.t. (subrel-stored sub super)))
#+ignore ; no longer compatible with adder
 (++ inlinerel (relationp 'subrel))

; that indirection allows us to supply an adder for subrel

; later on we'll maintain isubrel+ as isubrel plus the identity relation on
; relations, and subrel-stored as isubrel+* defined below:

(add-imparityname (make-dbobject) 'two-way-structprop  2 'isubrel+)
    
(++ transitive-closure 'isubrel+ 'isubrel+*)

; these have to be added since they are not yet maintained

(++ Possibletoadd (relationp 'isubrel+*) t)
(++ Possibletodelete (relationp 'isubrel+*) t)
(++ trigger (relationp 'isubrel+) nil 'trigger--tclosures (relationp 'isubrel+*) nil)
(++ trigger (relationp 'isubrel+) t 'trigger++tclosures (relationp 'isubrel+*) t)

(++ RelSize (relationp 'SubRel-Stored) '(Input Output) 3)
(++ RelSize (relationp 'SubRel-Stored) '(Output Input) 10)


(++ DefinedRelName 'type '((r) s.t. (RelationArity r 1)))
(++ inlinerel (relationp 'type))

(++ definedrelname 'subtype
    '((x y) s.t. (and (type x) (subrel x y))))
; of course this implies (type y) as well

; Note that these only access the relation ISubRel.
; They are therefore automatically sensitive to Delta and to contexts.
; I'm not sure where they're needed (if at all) any more - 
; Try to remove them someday ***

(defun allsupertypes (types)
  (setq types (mapcar #'relationp (if (listp types) types (list types))))
  (loop with expanded and tp while (setq tp (pop types))
	do (unless (member tp expanded)
	     (loop for isuper s.t. (isubrel tp isuper)
		   do (push isuper types))
	     (push tp expanded))
	finally (return expanded)))

; This is included to get a generator cached while bootstrapping is still T.
; It turns out that when bootstrapping is nil we need this generator in order
; to compile others (comes from expanddescription.declarevar.check-comparison)
(listof x s.t. (isubrel nil x))

(defun allsubtypes (types)
  (setq types (mapcar #'relationp
		      (if (listp types) types (list types))))
  (loop with expanded and tp
	while (setq tp (pop types))
	do (unless (member tp expanded)
	     (loop for isub s.t. (isubrel isub tp)
		   do (push isub types))
	     (push tp expanded))
	finally (return expanded)))

; probably the default estimate of testeffort is adequate
; this is a temporary hack to allow assertions of subtypes in reasonable places
(++ RelAdder (setq Rel-SubType (relationp 'subtype))
    '(lambda (&rest ignore) (declare (ignore ignore)) 'subtype-adder-temp))

(declaim (special subtypetuples))
(setq subtypetuples nil)

(defun subtype-adder-temp (ignore sub super) (declare (ignore ignore))
  (push (list sub super) subtypetuples))

; ---------------- Classification ----------------

(++ TreeProp+RelName 'Classification) ;; just a starting point
(setq rel-classification (relationp 'classification))

(declaim (special exception-class-table))
(setq exception-class-table (make-hash-table))

(++ relgenerator (relationp 'classification) 'classgenerator)
(++ reladder (relationp 'classification) 'addclass)
(++ reldeleter (relationp 'classification) 'delclass)
(++ reltester (relationp 'classification) 'testclass)

(Defun AddClass (rel &rest ignore &aux
			 (cnc (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel x y)
     ,.(cond ((listp (car cnc)) `((setq x (,(cadar cnc) x)))))
     ,.(cond ((listp (cadr cnc)) `((setq y (,(cadadr cnc) y)))))
 ;;; (put-structure-property x (cons y (get-structure-property x rel)) rel)
     (cond ((dbobject-p x) (push y (classes x)))
	   ((symbolp x) (push y (get x 'classification)))
	   (t (push y (gethash x exception-class-table))))
     (TreeAdder (list y x)
       (GETTreeData rel)
       ',(mapcar #'(lambda (x) (cond ((listp x) (car x)) (t x)))
		 (reverse cnc)))))

(Defun DelClass (rel &rest ignore &aux
			    (cnc (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel x y)
     ,.(cond ((listp (car cnc)) `((setq x (,(cadar cnc) x)))))
     ,.(cond ((listp (cadr cnc)) `((setq y (,(cadadr cnc) y)))))
     #+ignore ; for DelTreeprop
     (put-structure-property x
	     (delete y (get-structure-property x rel)
		     :test (function ,(cond ((listp (cadr cnc)) (caadr cnc)) (t (cadr cnc))))
		     :count 1)
	rel)
     (cond ((dbobject-p x)
	    (setf (classes x)
		  (delete y (classes x) :count 1 :test
			  (function ,(cond ((listp (cadr cnc)) (caadr cnc))
					   (t (cadr cnc)))))))
	   ((symbolp x)
	    (setf (get x 'classification) 
		  (delete y (get x 'classification) :count 1 :test
			  (function ,(cond ((listp (cadr cnc)) (caadr cnc))
					   (t (cadr cnc)))))))
	   (t (setf (gethash x exception-class-table) 
		    (delete y (gethash x exception-class-table) :count 1 :test
			    (function ,(cond ((listp (cadr cnc)) (caadr cnc))
					     (t (cadr cnc))))))))
     (TreeDeleter (list y x)
	(GETTreeData rel)
	',(mapcar #'(lambda (x) (cond ((listp x) (car x)) (t x)))
		  (reverse cnc)))))

(defun TestClass (rel &rest ignore &aux
			 (cnc (get-c-and-c rel 0)))
  (declare (ignore ignore))
  `(lambda (r x y)
     (declare (ignore r))
     ,.(cond ((listp cnc) `((setq x (,(cadr cnc) x)))))
     (cond ((DBObject-p x)
	    (member y (classes x) ;(get-structure-property x r)
		    :test ,(get-test-function (get-comparison rel 1 t))))
	   ((symbolp x)
	    (member y (get x 'classification) ;(get-structure-property x r)
		    :test ,(get-test-function (get-comparison rel 1 t))))
	   (t (member y (gethash x exception-class-table) ;(get-structure-property x r)
		      :test ,(get-test-function (get-comparison rel 1 t)))))))

(defun ClassGenerator (ignore ignore2 r x ignore3 &aux
				   (cnc (get-comparisons-and-canonicalizers r)))
  (declare (ignore ignore ignore2 ignore3))
  `((initialstate
      (lambda (r dbo &aux state)
	(declare (ignore r))
	,.(when (listp (car cnc)) `((setq dbo (,(cadar cnc) dbo))))
	(setq state (cond ((DBObject-p dbo)
			   (classes dbo))
			  ((symbolp dbo)
			   (get dbo 'classification))
			  (t (gethash dbo exception-class-table))))
	#'(lambda () #+ignore (declare (sys:downward-function))
		  (cond (state (values nil (pop state)))
			(t t)))))
    (template (input output))
    (effort , (iftimes 2.5 (relationsize '(%x) (list r x '%x))))))
; make it look cheaper than structprop (which is times 3)

(defun declassify (object &rest origtypes &aux types)
  (setq types (allsubtypes (mapcar #'(lambda(x) (or (relationp x)
						    (error "~A not a type" x)))
				   origtypes)))
  (atomic (loop for c s.t. (classification object c) when (member c types)
		do (-- classification object c)))
  (loop for tp in origtypes do (insist "supposed to delete it" not (funcall tp object))))

(++ RelSize Rel-Classification '(Input Output) 1)
(++ RelSize Rel-Classification '(Output Input) 1000)
(++ RelSize Rel-Classification '(Output Output) 1000000)

;      TYPE
;
; defn moved earlier (needed for subtype)
(setq type-type (relationp 'type))
#+ignore (++ Implementation (setq type-type (make-dbobject)) 'Defined 1 'type)
#+ignore (++ WffDefn type-type (BaseTypeDef type-type))
#+ignore (++ Classification type-type type-type)
(++ relsize (relationp 'type) '(output) 500)

; ---------------- binaryrelation ----------------
;
(++ definedrelname 'binaryrelation '((r) s.t. (relationarity r 2)))
(++ inlinerel (relationp 'binaryrelation))
(++ subtype (relationp 'binaryrelation) (relationp 'relation))
(++ subtype (relationp 'equivalence-relation) (relationp 'binaryrelation))
(++ relsize (relationp 'binaryrelation) '(output) 1000)

; ---------------- BaseType ----------------

(Defun BaseTypeDef (name)
  `((obj) s.t.
     (E (tp) (and (SubRel tp (theap5relation ,name)) (Classification obj tp)))))
; memo relationp is needed in order to allow uses of basetypes to compile to files
; (we can't expect to dump relation objects)

; have to do this before defining basetype
; BaseTypeDefn is a coded but unchanging rel:
; note that this relates non-rels as well - don't want to restrict it because
; then it would change whenever relations were (un)defined
(++ CodedRelName 'BaseTypeDefn
    '((name def) s.t. (equal def (BaseTypeDef name))))

(++ compare-relation (relationp 'basetypedefn) 1 (relationp 'equal))
(++ testeffort (relationp 'basetypedefn) '(lambda (&rest ignore)
					    (declare (ignore ignore)) 1000))
; *** measure this?

; we could supply (SimpleGenerator '(BaseTypeDef output a) ...) 
; but it wouldn't be very valuable.  Cannot generate (BaseTypeDef a x).

(++ DefinedRelName 'BaseType
    '((tp) s.t. (and (type tp)
		     (E (defn name) (and (WffDefn tp defn)
					 (relationname tp name)
					 (BaseTypeDefn name defn))))))



; ---------------- BaseTypeName ----------------
; exists for the purpose of declaring new types
(++ DefinedRelName 'BaseTypeName
    '((name) s.t. (E (rel) (and (RelationName rel name)
				(BaseType rel)))))

(++ RelAdder (relationp 'BaseTypeName)
    '(lambda (&rest ignore) (declare (ignore ignore)) 'basetypename-adder))

#+ignore ; done after we get special matchers
(defun basetypename-adder (ignore name &aux rel) (declare (ignore ignore))
  (cond ((?? BaseTypeName name)
	 (Insist "supposed to add it" BaseTypeName name))
	(t (atomic
	     (add-imparityname (setq rel (make-dbobject)) 'Defined 1 name)
	     (++ WffDefn rel (BaseTypeDef name))
	     ; (++ SubType rel (relationp 'DBObject))
	     ; this cannot be done here because the arity isn't known yet
	     ; instead it will be done by a rule
	     (++ reladder rel 'basetype-adder)
	     (++ reldeleter rel 'basetype-deleter)))))

(defun basetype-adder (&rest ignore) (declare (ignore ignore)) 'add-to-basetype)

(++ reldeleter (relationp 'BaseTypeName) 'namedrel-deleter)

(defun add-to-basetype (type object)
  (++ classification object type))

(defun basetype-deleter (&rest ignore) (declare (ignore ignore)) 'del-from-basetype)

(defun del-from-basetype (type object)
  (declassify object type))

;; ---------------- now create some types ----------------


#+ignore 
(++ RelAdder type-type
    #'(lambda (&rest ignore) (declare (ignore ignore))
	#'(lambda (ignore rel) (declare (ignore ignore))
	    (cond ((?? type rel)
		   (Insist "supposed to add it" type rel))
		  (t (++ Classification rel type-type))))))


;        ENTITY
(++ CodedRelName 'Entity '((x) s.t. (progn x t)))
(setq Type-Entity (RelationP 'Entity))
#+ignore (++ Type Type-Entity)
(++ anycomparison type-entity 0)

;        SYMBOL
(++ CodedRelName 'Symbol '((x) s.t. (Symbolp x)))
(setq Type-Symbol (RelationP 'Symbol))
#+ignore (++ Type Type-Symbol)
(++ anycomparison type-symbol 0)

;        T-OR-NIL
(++ definedrelname 'T-Or-Nil '((x) s.t. (or (eql x t) (eql x nil))))
(++ subtype (relationp 't-or-nil) (relationp 'symbol))

;        LIST
(++ CodedRelName 'List '((x) s.t. (Listp x)))
(setq Type-List (RelationP 'List))
#+ignore (++ Type Type-List)
(++ anycomparison type-list 0)

;        List-Or-Symbol
(++ CodedRelName 'List-Or-Symbol '((x) s.t. (or (listp x) (symbolp x))))
(setq type-list-or-symbol (relationp 'list-or-symbol))
(++ anycomparison type-list-or-symbol 0)
(++ SubType Type-List Type-List-Or-Symbol)
(++ SubType Type-Symbol Type-List-Or-Symbol)
(++ SubType Type-List-Or-Symbol type-entity)

;        Description
(defun descriptionp (x &optional allowevalargs)
  (and (listp x)
       (listp (car x))
       (listp (cdr x))
       (symbolp (cadr x))
       (string-equal (symbol-name (cadr x)) "s.t.")
       (listp (cddr x))
       (null (cdddr x))
       (try (expanddescription x :allowevalargs allowevalargs :descriptionp t)
	    'ExpandDescription nil)))
(++ CodedRelName 'Description 
    '((x) s.t. (descriptionp x)))
(++ possibletoadd (relationp 'description) t)
(++ possibletodelete (relationp 'description) t)
(++ nontriggerable (relationp 'description))
(++ testeffort (relationp 'description) '(lambda (&rest ignore)
					   (declare (ignore ignore)) 250000))
; much more difficult to test than the usual coded rel
; *** measure this some day

#+ignore (++ Type (relationp 'description))
(++ anycomparison (relationp 'description) 0)
(++ SubType (relationp 'description) (relationp 'list))

;        closed-wff
(++ CodedRelName 'Closed-Wff
    '((x) s.t. (?? description (list nil 's.t. x))))
(++ testeffort (relationp 'closed-wff)
    '(lambda (&rest ignore) (declare (ignore ignore)) 250000))
(++ possibletoadd (relationp 'closed-wff) t)
(++ possibletodelete (relationp 'closed-wff) t)
(++ nontriggerable (relationp 'closed-wff))
(++ anycomparison (relationp 'closed-wff) 0)
(++ subtype (relationp 'closed-wff) type-list-or-symbol)

;        STRING
(++ CodedRelName 'String '((x) s.t. (Stringp x)))
(setq Type-String (RelationP 'String))
#+ignore (++ Type Type-String)
(++ SubType Type-String Type-Entity)
(++ anycomparison type-string 0)

;        FUNCTION
(++ CodedRelName 'Function '((x) s.t. (or (Functionp x) (symbolp x))))
; Both TI and SYMBOLICS fail to implement commonlisp spec that any symbol is functionp
(setq Type-Function (RelationP 'Function))
#+ignore (++ Type Type-Function)
(++ SubType Type-Function Type-Entity)
(++ subtype type-symbol type-function)
(++ anycomparison type-function 0)
; this is supposed to be a static type? [I can't quite tell from CLTL]
; if not then add possibletoadd/delete and nontriggerable

;        NUMBER
(++ CodedRelName 'Number '((x) s.t. (numberp x)))
(setq Type-Number (RelationP 'Number))
#+ignore (++ Type Type-Number)
(++ SubType Type-Number Type-Entity)
(++ anycomparison type-number 0)

;        character
(++ CodedRelName 'Character '((x) s.t. (characterp x)))
(setq Type-Character (RelationP 'Character))
#+ignore (++ Type Type-Character)
(++ SubType Type-Character Type-Entity)
(++ anycomparison type-character 0)

;        INTEGER
(++ CodedRelName 'Integer
    '((x) s.t. (or (integerp x)
		   (and (numberp x)
		    (Integerp (canonicalize-= x))))))
(setq Type-Integer (RelationP 'Integer))
#+ignore (++ Type Type-Integer)
(++ SubType Type-Integer Type-Number)
; may want to remove this in order to generate ... 
(++ anycomparison type-integer 0)


;        DBObject
(++ CodedRelName 'DBObject '((x) s.t. (DBObject-p x)))
(setq Type-DBObject (RelationP 'DBObject))
#+ignore (++ Type Type-DBObject)
(++ SubType Type-DBObject Type-Entity)
(++ anycomparison type-dbobject 0)

;        MatchNode
(++ CodedRelName 'MatchNode '((x) s.t. (MatchNode-p x)))
#+ignore (++ Type (relationp 'MatchNode))
(++ SubType (relationp 'MatchNode) (relationp 'DBObject))
(++ anycomparison (relationp 'MatchNode) 0)

;        Relation
; defined and documented earlier.
#+ignore (++ Type Type-Relation)
;(++ SubType Type-Relation Type-DBObject)
; will be under rule-or-relation

;        Implementation
(++ baserelname 'implementation 1)
; (listof x s.t. (E (y) (relationimplementation y x)))

(buffer-break)

(dolist (imp '(TREE CODED DEFINED TREEPROP TREEPROP+
		    STRUCTPROP TWO-WAY-STRUCTPROP TCLOSURE BASE))
  (++ implementation imp))

;        Rel-Or-imp
(++ DefinedRelName 'Rel-Or-imp
		  '((x) s.t. (or (Relation x) (implementation x))))
(++ SubType (relationp 'Rel-Or-imp) (relationp 'Entity))
(++ SubType (relationp 'Relation) (relationp 'Rel-Or-imp)) 
(++ SubType (relationp 'implementation) (relationp 'Rel-Or-imp))

;        Type
; already defined and documented as a relation
#+ignore (++ Type (setq Type-Type (relationp 'Type)))
(++ SubType Type-Type Type-Relation)

; while we're at it, ...
(Defun PrintType (Rel)
  (printDBO 'Type (RelationNameP Rel)))

(++ Printer type-type 'printtype)
(++ Reader type-type 'readrelation)

(defun PrintMatchNode (node)
  (printdbo 'MatchNode (vars-to-names (matchvars node)) 's.t.
	    (vars-to-names-wff (matchwff node))))

(++ printer (relationp 'matchnode) 'printmatchnode)
; no reader as yet

;        BaseType
(setq Type-BaseType (RelationP 'BaseType))
#+ignore (++ Type Type-BaseType)
(++ SubType Type-BaseType Type-Type)

#+ignore ; newer (and better) defn in tools
(defun most-specific-types-of (types &aux ans disqualified)
  ; elements of types that are not supertypes of other elements
  (cond ((cdr types)
	 (loop for tp in types unless (member tp disqualified) do
	       (loop for super in (allsupertypes tp) do
		     ; *** could be optimized further
		     (or (member super disqualified) (push super disqualified))
		     (and (member super ans) (setq ans (delete super ans))))
	       (push tp ans))
	 ans)
	(t types)))

#+ignore  ;old version
(defun all-types-of (x)
  ; a list of all the types of x - useful in things like tell-me-about
  (loop for type# s.t. true when (CheckType type x) collect type))

;; now that we have a rule that guarantees that all types are subtypes
; of entity we can improve it:
(defun all-types-of (object &aux queue answer seen type)
  (setq queue (list type-entity))
  (loop while (setq type (pop queue))
	unless (member type seen :test #'eq)
	unless (member type answer :test #'eq)
	when (testrel type object)
	do
	(push type answer)
	(loop for x s.t. (isubrel x type)
	      do (push x queue)))
  answer)

;; We'll cache the tester in the Tester property of the relation. 
; Here's a case where we need to notice changes in the defns and
; decache the compiled code. ***
; Notice that when I tried to make this a relation I got into trouble -
; I think due to atomics?

(defmacro-displace CheckType (type object)
  `(TestRel ,type ,object))

(defun PrintDBObject (object &optional stream ignore)
  (declare (ignore ignore))
  (format stream "~A" 
    (cond ((member object InPrintDBObject) "<unprintable>")
	  (t (let ((InPrintDBObject (cons object InPrintDBObject)))
	       (or #+ignore (car (get-structure-property object rel-proper-name))
		   (cond #+ignore
			 ((fboundp 'proper-name-if-any)
			  (proper-name-if-any object))
			 (t (any x s.t. (proper-name object x)
				 ifnone nil)))
		   (and Bootstrapping (bootstrap-printer object))
		   (loop for (type printer) s.t. (printer type printer)
			 thereis
			 (and (checktype type object)
			      (funcall printer object)))
		   (PrintDBO 'dbobject (anyclass object)
			     (%pointer object))))))))


(defvar PrintDBObject 'PrintDBObject)

(defun anyclass (x)
  (forany c s.t. (classification x c) (relationnamep c) ifnone 'unclassified))

; now one should be able to do stuff like
; (++ BaseTypeName 'person)
; (++ BaseTypeName 'employee)
; (++ SubType '#ap(Relation employee) '#ap(Relation person))
; (++ classification (setq DonC (make-dbobject)) Employee)
; (?? Person DonC) => T
