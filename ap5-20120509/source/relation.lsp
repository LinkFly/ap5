;;;-*- Mode:LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-
;
(in-package "AP5")

(declaim (inline coerce-if))
(defun coerce-if(x) (when x (coerce x 'function)))

; Relation declarations and data
; this file must be compiled with Bootstrapping set to T - 
; so that the references to types will be written in a form
; that can be read back in before the types and readers exist.
(eval-when (:compile-toplevel :load-toplevel :execute) (setq bootstrapping t))
; start with global data structures and variables

; user level vars: 
(setf Fix-Maintained-Relation nil
      global-history nil
      generator-cost-record nil
      DefaultRelSize 100
      GenEffortWarning 9999999
      GenSizeWarning 9999
      TriggerEffortWarning 99999
      triggersizewarning 99)
; obsolete - see *warning-flags* (setq Warnings '((DefaultRelSize)))
(defvar-resettable Delta nil) ; rebound in update for use by user code
(setf *GlobalCx* 'global #+ignore (Make-Context :CxName 'Global)
      CurrentCx *GlobalCx*)
(defvar-resettable CurrentCx nil *GlobalCx*)
; yes this does make sense.  Setq instead of defvar is to change the value
; the second time this file is loaded; defvar-resettable still needed to
; get it reset on warm boot - to latest version of globalcx.
;; I don't know - should currentcx survive warm boot? ***

; these are probably of no interest to the user

(setf DebugSwitches '((CheckUpdate DoDBUpDates))
      generator-cache (createtree)
      matchcode-fn-cache (make-hash-table :test #'equal))
; almost certainly of no interest to users

(setf DefaultRelSizePats NIL ; table of warnings (so as not to repeat)
      TreeGeneratorTable nil
      RelationOfName (make-hash-table :size 50) ; get from names to relations
      |DangerousP | nil) ; t when the database is in a critical section
;;(setq |Contexts | (list CurrentCx)) 

; very bottom level of bootstrapping
; first the fns from utilities that will be redefined at the end
(defun Boot-Arity* (Rel)
  (unless (relationtypep Rel) (error "~S not a relation" rel))
  (or (car (get-structure-property rel 'RelationArity))
      (error "unknown relation ~S" Rel)))
; was (CADDR (FASSOC Rel (GETBaseData Rel-Implementation))))
(setf (symbol-function 'arity*) (symbol-function 'Boot-Arity*))
; despite the fact that relations are no longer litatoms, we insist that
; two relations (with non-anonymous names) not have the same name.

(defun Boot-Implementations-Of (rel)
  (unless (relationtypep rel) (error "~S not a relation" rel))
  (get-structure-property rel 'RelationImplementation))
(setf (symbol-function 'Implementations-Of)
      (symbol-function 'Boot-Implementations-Of))
(defun Boot-defined-p (rel)
  (member 'defined (boot-implementations-of rel)))
(setf (symbol-function 'defined-p)
      (symbol-function 'Boot-defined-p))

; now used to translate a relation name to the relation as well as to 
; identify relations and relation names
(defun RelationP (relname)
  (cond ((RelationTypeP relname) relname)
	((not (symbolp relname)) nil)
	(t ;formerly (not (symbolname "anonymous" relname))
	 (getrelationofname relname))))


; oh well, might as well go the other way (it's used)
(defun Boot-RelationNameP (rel)
  (cond ((RelationTypeP rel)
	 (car (get-structure-property rel 'RelationName)))
	; formerly could have been 'anonymous
	((GetRelationOfName rel) rel)))
(setf (symbol-function 'RelationNameP) (symbol-function 'Boot-RelationNameP))

(defun boot-get-comparison (rel pos &optional err-if-non-rel)
  (setq rel (relationp rel))
  (or (and (member (list rel pos) (getbasedata rel-anycompare) :test 'equal) t)
      (assoc rel (getbasedata rel-equivalence))
      (and (GetDefn rel)
	   (let ((ans (varcompare (nth pos (expanded-defn-vars rel)))))
	     (unless (relationp ans)
	       (when err-if-non-rel
		 (error "no (single) comparison for ~A position ~A" rel pos)))
	     (or ans t)))
      (prog (Z xtree ytree tree)
	; (any z s.t. (comparison rel pos z) :ifnone rel-eql)
	; special deal - optimize a compilation that assumes comparison is a treerel
	(setf tree (gettreedata rel-comparison))
	(flet ((follow-tree (tree key)
		 (if (integerp (first tree))
		      (cdr (assoc key (rest tree)))
		    (gethash key (car tree)))))
	      (unless (setf xtree (follow-tree tree rel))
		      (return rel-eql))
	      (unless (setf ytree (follow-tree xtree pos))
		      (return rel-eql)))
	(unless (setq z (if (integerp (first ytree))
			    (second ytree)
			   ; find some element of ytree that maps to T
			   ; should never happen since there's only 1
			   (error "shouldn't have to do this - get-comparison")))
	    (return rel-eql))
      (return z))))
(setf (symbol-function 'get-comparison) (symbol-function 'boot-get-comparison))

(defun Boot-GetDefn (DefinedRel)
  (setq DefinedRel (RelationP DefinedRel))
  (AND DefinedRel
       #+ignore (eq 'Defined (ImplementationOf DefinedRel))
       (copy-tree (get-structure-property DefinedRel rel-WffDefn))))
(setf (symbol-function 'GetDefn) (symbol-function 'Boot-GetDefn))

(defun boot-equivalence-relp (rel)
   (assoc rel (getbasedata rel-equivalence)))
(setf (symbol-function 'equivalence-relp) (symbol-function 'boot-equivalence-relp))

(defun boot-nontriggerablep (rel)
   (assoc rel (getbasedata rel-nontriggerable)))
(setf (symbol-function 'nontriggerablep) (symbol-function 'boot-nontriggerablep))

(defun boot-tester-for (x)
  (coerce-if (copy-tree (cadr (assoc x (getbasedata rel-tester))))))
(setf (symbol-function 'tester-for) (symbol-function 'boot-tester-for))

(defun boot-generators-for (x)
  (loop for y in (getbasedata rel-generator) when (eql (car y) x) collect (cadr y)))
(setf (symbol-function 'generators-for)
      (symbol-function 'boot-generators-for))

(defun boot-all-gens-for (rel) 
  (nconc (boot-generators-for rel)
	 (boot-generators-for (car (boot-implementations-of rel)))))
(setf (symbol-function 'all-generators-for)
      (symbol-function 'boot-all-gens-for))

(defun boot-rel-sizes (rel &aux tree xtree)
  (setq tree (gettreedata rel-size))
  (when (setq xtree
	     (COND ((NUMBERP (car tree)) (cdr (assoc rel (cdr tree))))
		   (t (gethash rel (car tree)))))
       (collecttree xtree 2)))
(setf (symbol-function 'rel-sizes) (symbol-function 'boot-rel-sizes))

(defun boot-get-testeffort (x)
  (coerce-if (cadr (assoc x (getbasedata rel-testeffort)))))

(setf (symbol-function 'get-testeffort) (symbol-function 'boot-get-testeffort))

(defun boot-get-canonicalizer (x) (assoc x (getbasedata rel-canonicalizer)))
(setf (symbol-function 'get-canonicalizer) (symbol-function 'boot-get-canonicalizer))

(defun boot-cxvaluefn (rel &aux (data (getbasedata rel-cxvaluefn)))
  (cadr (or (assoc rel data) (assoc (car (implementations-of rel)) data))))
(setf (symbol-function 'cxvaluefn) (symbol-function 'boot-cxvaluefn))

(defun boot-derivedrel (rel)
  (assoc (car (implementations-of rel)) (getbasedata rel-derived)))
(setf (symbol-function 'derivedrel) (symbol-function 'boot-derivedrel))

;; formerly boot-get-update-macro
(defun boot-get-adder-or-deleter (rel tv &aux data)
  (setq data (case tv
	       ((t) rel-adder)
	       ((nil) rel-deleter)
	       #+ignore (inherit rel-inheriter)
	       (otherwise (error "illegal truthvalue"))))
  (setq data (getbasedata data))
  (coerce-if (cadr (or (assoc rel data)
		       (assoc (car (implementations-of rel)) data)))))
(setf (symbol-function 'get-adder-or-deleter)
      (symbol-function 'boot-get-adder-or-deleter))

(defun boot-get-checkers (x)
  (loop for checker in (getbasedata rel-checker)
	when (eql (car checker) x) collect (cadr checker)))
(setf (symbol-function 'get-checkers) (symbol-function 'boot-get-checkers))

;; defined for real later 
(setf (symbol-function 'simple-update-p) (symbol-function 'ignored))
(setf (symbol-function 'inlinerel?) (symbol-function 'ignored))
(setf (symbol-function 'get-depends-on) (symbol-function 'ignored))
(setf (symbol-function 'get-depends-on2) (symbol-function 'ignored))
(setf (symbol-function 'nonatomic-relation) (symbol-function 'ignored))
; with any luck setf will enable us to
; define these in another file without complaint
(setf (symbol-function 'maintainedrels-affected-by-rel) (symbol-function 'ignored))
(setf (symbol-function 'maintainedrels-affected-by-node) (symbol-function 'ignored))
(setf (symbol-function 'not-allowed-to-update) (symbol-function 'ignored))
(setf (symbol-function 'get-add-del-triggers) (symbol-function 'ignored))
(setf (symbol-function 'get-updater) (symbol-function 'ignored))
(setf (symbol-function 'unchanged) (symbol-function 'ignored))
(setf (symbol-function 'get-triggers) (symbol-function 'ignored))
(setf (symbol-function 'descriptionp) (symbol-function 'ignored))
(setf (symbol-function 'macroexpand-1wff) (symbol-function 'ignored))
(setf (symbol-function 'derived-nonatomic-rel) (symbol-function 'ignored))

(defun collecttree (tree depth) ; adapted from printtree
  (cond ((= depth 1.)
	 (cond ((numberp (car tree))
		(mapcar #'list (cdr tree)))
	       (t (prog (ans)
			(declare (special ans))
			(maphash (function (lambda (x ignore)
					     (declare (ignore ignore))
					     (push (list x) ans)))
				 (car tree))
			(return ans)))))
	((numberp (car tree))
	 (loop for subtree in (cdr tree) nconc
	       (loop for tuple in (collecttree (cdr subtree) (- depth 1))
		     collect (cons (car subtree) tuple))))
	(t (prog (ans)
		 (declare (special ans depth))
		 (maphash #'(lambda (x y)
			      (loop for tuple in (collecttree y (- depth 1)) do
				    (push (cons x tuple) ans)))
			  (car tree))
		 (return ans)))))

; these have to exist before first createrel
(setq rel-printer (make-dbobject))
(setq rel-reader (make-dbobject))
(setq rel-eql (make-dbobject))

(defvar eql-table)

(setq eql-table (list rel-eql))
(setq rel-anycompare (make-dbobject))
(setq rel-equivalence (make-dbobject))
(setq rel-canonicalizer (make-dbobject))
(setq type-relation (make-dbobject))
                                                                ;RelationArity
(setq rel-arity (make-dbobject))
(put-structure-property rel-arity '(2) 'RelationArity)
(put-structure-property rel-arity '(base) 'RelationImplementation)
(PutRelationOfName 'RelationArity rel-arity)
                                                                ;RelationName
(setq rel-Name (make-dbobject))
(put-structure-property rel-name '(2) 'RelationArity)
(put-structure-property rel-name '(base) 'RelationImplementation)
(PutRelationOfName 'RelationName rel-name)
                                                           ;RelationImplementation
(setq Rel-Implementation (make-dbobject))
(put-structure-property rel-implementation '(2) 'RelationArity)
(put-structure-property rel-implementation '(base) 'RelationImplementation)
(PutRelationOfName 'RelationImplementation Rel-Implementation)

                                                                ;RelAdder
(setq Rel-Adder (make-dbobject))
(put-structure-property rel-adder '(2) 'RelationArity)
(put-structure-property rel-adder '(base) 'RelationImplementation)
(PutRelationOfName 'RelAdder Rel-Adder)
                                                                ;Derived
(setq Rel-Derived (make-dbobject))
(put-structure-property rel-derived '(1) 'RelationArity)
(put-structure-property rel-derived '(base) 'RelationImplementation)
(PutRelationOfName 'Derived Rel-Derived)
                                                                ;RelTester
(setq Rel-Tester (make-dbobject))
(put-structure-property rel-tester '(2) 'RelationArity)
(put-structure-property rel-tester '(base) 'RelationImplementation)
(PutRelationOfName 'RelTester Rel-Tester)
                                                                ;Checker
(setq Rel-Checker (make-dbobject))
(put-structure-property rel-checker '(2) 'RelationArity)
(put-structure-property rel-checker '(base) 'RelationImplementation)
(PutRelationOfName 'Checker Rel-Checker)
                                                                ;Trigger
(setq rel-trigger (make-dbobject))
(put-structure-property rel-trigger '(5) 'RelationArity)
(put-structure-property rel-trigger '(base) 'RelationImplementation)
; later to be changed to full-index
(PutRelationOfName 'Trigger Rel-trigger)
                                                                ; CxValueFn
(setq Rel-CxValueFn (make-dbobject))
(put-structure-property rel-CxValueFn '(2) 'RelationArity)
(put-structure-property rel-CxValueFn '(base) 'RelationImplementation)
(PutRelationOfName 'CxValueFn Rel-CxValueFn)

                                                                ; comparison
(setq rel-comparison (make-dbobject))
(put-structure-property rel-Comparison '(3) 'RelationArity)
(put-structure-property rel-Comparison '(tree) 'RelationImplementation)
(PutRelationOfName 'Compare-Relation Rel-Comparison)

(defvar rels-needed-to-add)
(setq rels-needed-to-add
      (list rel-arity rel-name rel-implementation rel-checker rel-adder
	    rel-tester rel-trigger rel-derived rel-cxvaluefn rel-comparison))

(putbasedata rel-implementation
  (loop for rel in rels-needed-to-add collect
	(list rel (car (get-structure-property rel 'relationimplementation)))))

(putbasedata rel-arity
  (loop for rel in rels-needed-to-add collect
	(list rel (car (get-structure-property rel 'relationarity)))))

(putbasedata rel-name
  (loop for rel in rels-needed-to-add collect
	(list rel (car (get-structure-property rel 'relationname)))))

(PutBaseData Rel-Adder '((Base AddBaseTuple)))

(PutBaseData Rel-Tester '((Base TestBaseTuple))) ; actually need this to add

(defun bootstrap-printer (x &optional stream)
  (cond ((relationp x) (format stream "#,(relationp '~S)" (relationnamep x)))
	(t (PrintDBO 'dbobject (%pointer x)))))
; temporary for being able to compile bootstrap code to file

(setq rel-proper-name nil) ; temporary so we can print if errors arise
(setf (symbol-function 'maintain-mnode) (symbol-function 'ignored)) ; also temporary
(setf (symbol-function 'PossibleToUpdate)
      #'(lambda (ignore ignore2) (declare (ignore ignore ignore2)) t))
; also temporary:
; needed in order to test, which is needed to assert
; defined for real at bottom of this file

(setf (symbol-function 'matchconsistencies)
      #'(lambda (&rest ignore) (declare (ignore ignore)) nil)) ;; bootstrapping
(setf (symbol-function 'matchautomations)
      #'(lambda (&rest ignore) (declare (ignore ignore)) nil)) ;; bootstrapping
(setq rel-Wffdefn (make-dbobject)) ;; bootstrapping
(setq Rel-TestEffort (make-dbobject))
; Now we can arrange for the Implementation properties and the RelationName's
; to be done automatically:
; Since we have RelAdder defined as a baserel, and we have its Adder, 
; now finally ...

(++ RelAdder 'StructProp 'AddStructProp)
(++ RelTester 'StructProp 'StructPropTester)

; now we can say what really happens when relnames are added
(++ RelAdder Rel-name
    '(lambda (&rest ignore)
       (declare (ignore ignore))
       'rel-name-adder))

(defun rel-name-adder  (Relname rel name &aux (tuple (list rel name)))
  (PutBaseData relname (CONS Tuple (GETBaseData Relname)))
  ; like AddBaseTuple plus
  (putrelationofname name rel))

; what really happens when relimplementations are added
(++ RelAdder Rel-implementation
    '(lambda (&rest ignore)
       (declare (ignore ignore))
       'rel-implementation-adder))

(defun  rel-implementation-adder (Relimp rel imp &aux (tuple (list rel imp)))
  (PutBaseData relimp (CONS Tuple (GETBaseData Relimp)))
  ; like AddBaseTuple plus
  (add-structure-property rel imp 'relationimplementation))

; what really happens when relarities are added
(++ RelAdder Rel-arity
    '(lambda (&rest ignore)
       (declare (ignore ignore))
       'rel-arity-adder))

(defun rel-arity-adder (Relarity rel arity &aux (tuple (list rel arity)))
  (PutBaseData relarity (CONS Tuple (GETBaseData Relarity)))
  ; like AddBaseTuple plus
  (add-structure-property rel arity 'relationarity))

; declare the relations that are directly accessed in the code above

(++ checker 'structprop
    (compile nil
     '(lambda (structproprel adds dels) (declare (ignore dels structproprel))
	(loop for tup in adds always (DBObject-p (car tup))))))

(++ checker 'treeprop
    (compile nil
     '(lambda (treeproprel adds dels) (declare (ignore dels treeproprel))
	(loop for tup in adds always (DBObject-p (car tup))))))

(defun add-imparityname (rel imp arity name)
  (atomic (++ relationarity rel arity)
	  (++ relationname rel name)
	  (++ relationimplementation rel imp)))

;(setq Rel-canonicalizer (make-dbobject))
(add-imparityname Rel-canonicalizer 'base 3 'Canonicalizer)
;(setq rel-equivalence-test-fn (make-dbobject))
;(add-imparityname rel-equivalence-test-fn 'base 2 'Equivalence-Function)
;(setq Rel-equivalence (make-dbobject))
(add-imparityname rel-equivalence 'base 1 'Equivalence-Relation)
;(setq rel-anycompare (make-dbobject))
(add-imparityname rel-anycompare 'base 2 'AnyComparison)
(setq Rel-Generator (make-dbobject))
(add-imparityname Rel-Generator 'base 2 'RelGenerator)
(setq Rel-Deleter (make-dbobject))
(add-imparityname Rel-Deleter 'base 2 'RelDeleter)
;(setq Rel-Inheriter (make-dbobject))
;(Add-imparityname Rel-Inheriter 'base 2 'RelInheriter)
(setq Rel-Size (make-dbobject))
(Add-imparityname Rel-Size 'tree 3 'RelSize)
; above (setq Rel-TestEffort (make-dbobject))
(Add-imparityname Rel-TestEffort 'base 2 'TestEffort)
;(setq rel-Wffdefn (make-dbobject)) ; moved earlier
(add-imparityname rel-Wffdefn 'StructProp 2 'WffDefn)
(setq rel-Codedefn (make-dbobject))
(add-imparityname rel-Codedefn 'StructProp 2 'CodeDefn)

(buffer-break)
(++ relgenerator 'defined 'definedrelgenerator)

; addbasetuple was already bootstrapped in so we could do those ++'s
; here are the other properties of base relations

;(++ RelInheriter 'Base 'DefaultCxMechanism)
(++ RelDeleter 'Base 'DeleteBaseTuple)
(++ RelTester 'Base 'TestBaseTuple)
(++ RelGenerator 'Base 'BaseRelGenerator)
(++ TestEffort 'Base
    '(LAMBDA (&rest Pat)
       (* (RelationSize (CDR Pat) Pat) 3 (LENGTH (cdr Pat)))))

; *** These are offered with some trepidation - de-implementing relations may
; not make any sense if the relation has tuples and appears in rules (or
; other compiled code).  Nevertheless, it seems important to allow it.
(++ RelDeleter Rel-Implementation
    '(lambda (&rest ignore)
       (declare (ignore ignore))
       'rel-implementation-deleter))

(defun equal1 (a b)
    ; for comparing tuples (known to be same length)
    ; of course assuming that the comparisons are all EQL!!
    (loop for x in a as y in b always (eql x y)))
(defun fmemb2 (x l)
    ; for testing baserels - arity checked before
    (loop for y in l thereis (and (equal1 x y) y)))

(defun rel-implementation-deleter (Rel r i &aux memb)
	  (cond ((setq memb (fmemb2 (list r i) (getbasedata rel)))
		 (putbasedata rel (delete memb (getbasedata rel)))))
	  (put-structure-property r
	       (remove i (get-structure-property r 'relationimplementation))
	       'relationimplementation))

(++ RelDeleter Rel-Name
    '(lambda (&rest ignore)
       (declare (ignore ignore))
       'rel-name-deleter))
(defun rel-name-deleter (Rel r n &aux memb)
	  (cond ((setq memb (fmemb2 (list r n) (getbasedata rel)))
		 (putbasedata rel (delete memb (getbasedata rel)))))
	  (put-structure-property r
	       (remove n (get-structure-property r 'relationname))
	       'relationname)
	  (when (eql r (gethash n RelationOfName))
	    ; have to watch out for making it the name of something else
	    ; in the same atomic and that update getting done first!
	    (RemHash n RelationOfName)))

(++ RelDeleter Rel-arity
    '(lambda (&rest ignore)
       (declare (ignore ignore))
       'rel-arity-deleter))
(defun rel-arity-deleter  (rel r a &aux memb)
  #+ignore (abort 'remove-arity "not allowed to remove arity of a relation")
  (cond ((setq memb (fmemb2 (list r a) (getbasedata rel)))
	 (putbasedata rel (delete memb (getbasedata rel)))))
  (put-structure-property r
			  (remove a (get-structure-property r 'relationarity)
				  :test #'=)
			  'relationarity))

; Actually, partof rels are no longer used in the kernel
; PartOfRels (see defn of Relation structure for possible instances)
; (The Adder was part of the bootstrap process so as to define a postmodify)
;
#+ignore (
 (++ RelAdder 'PartOfRel 'AddRelPart)
; (++ RelInheriter 'PartOfRel 'DefaultCxMechanism)
 (++ RelDeleter 'PartOfRel 'DelRelPart)
 (++ RelTester 'PartOfRel 'RelPartTester)
 (++ TestEffort 'PartOfRel '(lambda (&rest pat) 50))
 (++ RelGenerator 'PartOfRel 'RelPartGenerator)
)

; StructPropRels 
;(++ RelInheriter 'StructProp 'DefaultCxMechanism)
(++ RelDeleter 'StructProp 'DelStructProp)
(++ TestEffort 'StructProp
    '(lambda (rel &rest ignore)
	 (declare (ignore ignore))
	 (let ((size1 (relationsize '(x) (list rel 'a 'x)))) ; compiler bug
	   (iftimes 3 size1))))
(++ RelGenerator 'StructProp 'StructPropGenerator)

; two way structprops
(++ RelAdder 'two-way-StructProp 'Add2StructProp)
(++ RelTester 'two-way-StructProp 'StructProp2Tester)
(++ checker 'two-way-structprop
    (compile nil
     '(lambda (structproprel adds dels) (declare (ignore dels structproprel))
	(loop for tup in adds always
	      (and (DBObject-p (car tup))
		   (DBObject-p (cadr tup)))))))

(++ RelDeleter 'two-way-StructProp 'Del2StructProp)
(++ TestEffort 'two-way-StructProp
    '(lambda (rel &rest pat)
       (let ((size0 (relationsize '(x) (list rel 'x 'a)))
	     (size1 (relationsize '(x) (list rel 'a 'x))))
	 (iftimes 3 (cond ((iflessp size0 size1) size0) (t size1))))))
(++ RelGenerator 'two-way-StructProp 'StructProp2Generator)


; DefinedRels
(++ Derived 'Defined)
;; These are no longer used.  In some sense, defined relations have been 
;  promoted to the status of internal-to-AP5.  In fact, before any wff is
;  processed it is expanded (type#var, relation definitions) and simplified.
;  The advantage of this is that simplification can have the effect of
;  global optimization.  Of course, we lose the ability to give advice
;  about defined relations, but this was really a hack - the advice ought
;  to be given about wffs so that it will be available no matter where that
;  wff comes from.
#+ignore (++ RelTester 'Defined 'DefRelTester)
#+ignore (++ RelGenerator 'Defined 'DefRelGenerators)
#+ignore (++ TestEffort 'Defined
    '(LAMBDA (&rest Pat)
       (loop for x in (getdefn (car pat)) minimize
	     (TestEffort (ExpandDefn Pat x)))))


;;Coded relations

(defun DefCodedRel (RName Args Form &aux rel)
  (setq rel (or (relationp RName) (make-dbobject)))
  ; try to use old one
  (add-imparityname rel 'Coded (LENGTH Args) RName)
  (++ CodeDefn rel (list Args 's.t. Form))
  (++ RelTester rel (coerce
		     `(lambda (&rest ignore)
		       (declare (ignore ignore))
		       '(LAMBDA (ignore ,@Args) (declare (ignore ignore)) ,Form))
		     'function)))

; don't worry about non-defrel-maintained-tester stuff - this not used with defrel
(defun DefCodedRel1 (rel Args Form)
  (++ relationimplementation rel 'coded) ; presumably already has arity&name
  (++ CodeDefn rel (list Args 's.t. Form))
  (++ RelTester rel `(lambda (&rest ignore)
		       (declare (ignore ignore))
		       '(LAMBDA (ignore ,@Args) (declare (ignore ignore)) ,Form))))

(defun SimpleGenerator (pat form &optional costcode)
    (SETQ Pat (loop for p in pat collect
		    (cond ((symbolname "OUTPUT" p) 'output) (t p))))
    ; accept output in any package
    (unless (member 'output (cdr pat)) (error "~S contains no OUTPUT" pat))
    (unless (boundsymbollist (cdr pat)) (error "~S illegal argument list" pat))
    (++
     relgenerator
     (or (relationp (car pat)) (car pat))
     ; allow implementations here (unless they are named as relations)
     ; formerly (compile-ap *) - this code is not expensive to interpret and
     ; is only run at macro expand time.
     ; The advantage to leaving it interpreted is that when a simplegen is
     ; redone, the generator is recognized as equal and nothing is added
     (compile nil
      `(lambda (&rest ignore)
	(declare (ignore ignore))
	'((effort , (or costcode (* 5. (length pat))))
	  (template , (loop for arg in (cdr pat)
			    collect (cond ((eq arg 'output) 'output)
					  (t 'input))))
	  (initialstate (lambda (ignore ,.(loop for arg in (cdr pat)
					        unless (eq arg 'output)
					        collect arg)
				 &aux state)
			  (declare (ignore ignore))
			  (setq state ,form)
			  #'(lambda nil
			      (cond (state (values nil
						   (if (consp state)
						       (pop state)
						       (prog1 state (setq state nil)))))
				    (t t)))))))))
    pat)

(defun SimpleMultipleGenerator (pat form &optional costcode)
    (SETQ Pat (loop for p in pat collect
		    (cond ((symbolname "OUTPUT" p) 'output) (t p))))
    ; accept output in any package
    (unless (member 'output (cdr pat)) (error "~S contains no OUTPUT" pat))
    ;(or (boundsymbollist (cdr pat)) (error "~S illegal argument list" pat))
    (++
     relgenerator
     (or (relationp (car pat)) (car pat))
     ; allow implementations here (unless they are named as relations)
     ; formerly (compile-ap *) - this code is not expensive to interpret and
     ; is only run at macro expand time.
     ; The advantage to leaving it interpreted is that when a simplegen is
     ; redone, the generator is recognized as equal and nothing is added
     (compile nil
      `(lambda
	(&rest ignore)
	(declare (ignore ignore))
	'((effort , (or costcode (* 5. (length pat))))
	  (template , (loop for arg in (cdr pat)
			    collect (cond ((eq arg 'output) 'output)
					  (t 'input))))
	  (initialstate (lambda (ignore ,.(loop for arg in (cdr pat)
					        unless (eq arg 'output)
					        collect arg)
				 &aux state)
			  (declare (ignore ignore))
			  (setq state ,form)
			  #'(lambda nil
			      (cond (state (apply #'values nil (pop state)))
				    (t t)))))))))
    pat)


(++ testeffort 'coded '(lambda (&rest args) (* 2 (length args))))
; most coded rels will be very cheap - this way we need only annotate the exceptions

(++ Derived 'Coded)
; our first coded relations are equivalence relations
;
;(DefCodedRel 'EQL '(x y) '(EQL x y)) - have to (?) use existing rel-eql dbobject
(add-imparityname rel-eql 'Coded 2 'eql)
(++ CodeDefn rel-eql (list '(x y) 's.t. '(eql x y)))
(++ RelTester rel-eql
    '(lambda (&rest ignore) (declare (ignore ignore))
	     '(LAMBDA (ignore x y) (declare (ignore ignore)) (eql x y))))
(DefCodedRel 'EQ '(x y) '(EQ x y))
(DefCodedRel 'EQUAL '(x y) '(EQUAL x y))
(DefCodedRel 'EQUALP '(x y) '(EQUALP x y))

(++ equivalence-relation (relationp 'EQL))
(++ equivalence-relation (relationp 'EQ))
(++ equivalence-relation (relationp 'EQUAL))
(++ equivalence-relation (relationp 'EQUALP))

(setf eql-table (list rel-eql
		      (setf rel-eq (relationp 'eq))
		      (setf rel-equal (relationp 'equal))
		      (setf rel-equalp (relationp 'equalp))))

;(SimpleGenerator '(EQ output a) '(LIST a))
;(SimpleGenerator '(EQ a output) '(LIST a))

;; This is needed so often and early that we just add it here ...
(defcodedrel '= '(x y) '(or (eql x y) (ignore-errors (= x y))))
(++ equivalence-relation (relationp '=))
(++ canonicalizer (relationp '=) (relationp 'eql) 'canonicalize-=)

; canonicalize = into eql
; see discussions in CLtL pp. 13-20, 77-82, 193-195
(defun canonicalize-= (x)
  ;;; integers are by far the most common in our applications,
  ;;; so make them them REAL fast
  (when (integerp x) (return-from canonicalize-= x))

  (when (numberp x)
    (when (complexp x) ; 4+5i = 4.0+5.0i
      (let ((cr (canonicalize-= (realpart x)))
	    (ci (canonicalize-= (imagpart x))))
	(unless (and (eql cr (realpart x)) (eql ci (imagpart x)))
	  (setq x (complex cr ci)))))
    ; this is done automatically only for (complex rational) - p.20
    (when (and (complexp x) (= 0 (imagpart x))) (setq x (realpart x)))
    (when (floatp x)
      (let (new)
	(when (and (typep x 'long-float)
		   (= x (setq new (coerce x 'double-float))))
	  (setq x new))
	(when (and (typep x 'double-float)
		   (= x (setq new (coerce x 'single-float))))
	  (setq x new))
	(when (and (typep x 'single-float)
		   (= x (setq new (coerce x 'short-float))))
	  (setq x new))
	(when (= x (setq new (floor x)))  ; is floor cheapest?
	  ; this takes care of 0.0 vs. -0.0
	  (setq x new)))))
  x)

; property list relations
#+ignore 
(
(++ RelAdder 'Prop 'PropAdder)
;(++ RelInheriter 'Prop 'DefaultCxMechanism)
(++ RelDeleter 'Prop 'PropDeleter)
(++ RelTester 'Prop 'PropTester)
(++ RelGenerator 'Prop 'PropGenerator)
(++ testeffort
    'prop
    '(lambda (rel x y)
	     (* 3.
		    (relationsize '(output)
                                  (list rel 'input 'output)))))
)

; tree relations
(++ RelAdder 'Tree 'AddTreeTuple)
(++ RelDeleter 'Tree 'DeleteTreeTuple)
;(++ RelInheriter 'Tree 'DefaultCxMechanism)
(++ RelTester 'Tree 'TestTreeTuple)
(++ testeffort 'tree '(lambda (&rest pat) (* 50. (length pat))))
;; *** This is not really right - see generators - they can be cheaper
; depending on # tuples expected - or maybe THAT estimate is wrong.
(++ RelGenerator 'Tree 'TreeGenerator)

; now that we have trees ...
(++ RelSize (RelationP 'EQL) '(Output Output) NIL)
(++ RelSize (RelationP 'EQL) '(Output Input) 1)
(++ RelSize (RelationP 'EQL) '(Input Output) 1)
(++ RelSize (RelationP 'EQ) '(Output Output) NIL)
(++ RelSize (RelationP 'EQ) '(Output Input) 1)
(++ RelSize (RelationP 'EQ) '(Input Output) 1)
(++ RelSize (RelationP 'EQUAL) '(Output Output) NIL)
(++ RelSize (RelationP 'EQUAL) '(Output Input) 1)
(++ RelSize (RelationP 'EQUAL) '(Input Output) 1)
(++ RelSize (RelationP '=) '(Output Output) NIL)
(++ RelSize (RelationP '=) '(Output Input) 1)
(++ RelSize (RelationP '=) '(Input Output) 1)
(++ compare-relation rel-arity 1 (relationp '=))
(++ compare-relation rel-size 2 (relationp '=))
(++ compare-relation (relationp 'anycomparison) 1 (relationp '=))
(++ compare-relation (relationp 'compare-relation) 1 (relationp '=))

; TreePropRels
(++ RelAdder 'TreeProp 'AddTreeProp)
(++ RelDeleter 'TreeProp 'DelTreeProp)
;(++ RelInheriter 'TreeProp 'DefaultCxMechanism)
(++ RelTester 'TreeProp 'TestTreeProp)
(++ TestEffort 'TreeProp 
 '(lambda (&rest pat) (min 50 (* 3 (relationsize '(x)(cons (car pat) '(a x)))))))
(++ RelGenerator 'TreeProp 'TreePropGenerators)

;; now we can define a few more relations for the convenience of the users...

#|
(setq Rel-Help (make-dbobject))
(Add-imparityname Rel-Help 'StructProp 2 'Help)
(++ RelSize (relationp 'help) '(input output) 1)
(++ compare-relation rel-help 1 (relationp 'equal))
|#

(++ relsize rel-comparison '(input output output) 3)
(++ relsize rel-comparison '(input input output) 1)

(++ RelSize Rel-Adder '(Input Output) 1)
(++ compare-relation rel-adder 1 (relationp 'equal))

(++ RelSize Rel-Checker '(Input Output) 1)
(++ compare-relation rel-checker 1 (relationp 'equal))

(++ relsize rel-equivalence '(output) 10)

(++ relsize rel-anycompare '(input output) 1)

(++ relsize rel-canonicalizer '(output output output) 10)
(++ compare-relation rel-canonicalizer 2 (relationp 'equal))

#+ignore 
(
(++ relsize rel-equivalence-test-fn '(output output) 10)
(++ help rel-equivalence-test-fn
"(Equivalence-Function equivalence-relation function) means that the given 
equivalence relation can be tested by the given lisp function.  This is used
for optimization.")
)

(++ RelSize Rel-Generator '(Input Output) 1)
(++ compare-relation rel-generator 1 (relationp 'equal))

(++ RelSize Rel-Tester '(Input Output) 1)
(++ compare-relation rel-tester 1 (relationp 'equal))

;(setq rel-printer (make-dbobject))
(add-imparityname rel-printer 'Tree 2 'Printer)
(++ RelSize Rel-Printer '(Input Output) 1)
(++ compare-relation rel-printer 1 (relationp 'equal))

;(setq rel-reader (make-dbobject))
(add-imparityname rel-Reader 'StructProp 2 'Reader)
(++ RelSize Rel-Reader '(Input Output) 1)
(++ compare-relation rel-reader 1 (relationp 'equal))

(++ RelSize Rel-CxValueFn '(Input Output) 1)
(++ compare-relation rel-cxvaluefn 1 (relationp 'equal))

;(++ RelSize Rel-Inheriter '(Input Output) 1)
;(++ compare-relation rel-inheriter 1 (relationp 'equal))

; rel tv fn derivedrel derivedtv
(++ RelSize Rel-Trigger '(Input Output output output output) 2)
(++ RelSize Rel-Trigger '(Output output output Input output) 2)
(++ compare-relation rel-trigger 2 (relationp 'equal))

(++ RelSize Rel-Deleter '(Input Output) 1)
(++ compare-relation rel-deleter 1 (relationp 'equal))

(++ RelSize Rel-Size '(Input Input Output) 1)
(++ compare-relation rel-size 1 (relationp 'equal))

(++ RelSize rel-TestEffort '(Input Output) 1)
(++ compare-relation rel-testeffort 1 (relationp 'equal))

(++ RelSize Rel-CodeDefn '(Input Output) 1)
(++ compare-relation rel-codedefn 1 (relationp 'equal))

(++ RelSize Rel-WffDefn '(Input Output) 1)
(++ compare-relation rel-wffdefn 1 (relationp 'equal))

; now we can go on to define some more relations...

;This would have been defined with defrel, but we need to use the existing object
(Add-imparityname type-relation 'Defined 1 'Relation)
(++ WffDefn type-relation '((r) s.t. (E (x)(relationarity r x))))
; while we're at it, this is convenient for undefining relations ...
(++ reldeleter (relationp 'relation) '(lambda (&rest ignore)
					(declare (ignore ignore)) 'deleterel))

(defun deleterel (ignore rel)
  (declare (ignore ignore))
  (loop for a s.t. (relationarity rel a) do (-- relationarity rel a))
  (insist "supposed to delete it" not (relation rel)))

(Defun ReadRelation (&rest list)
  (or (relationp (cadr list))
      (when (symbolp (cadr list))
	(let ((new (check-relation-package-error (cadr list))))
	  (unless (eq new (cadr list)) (relationp new))))))
(++ Reader type-relation 'readrelation)

(Defun PrintRelation (Rel)
  (printDBO 'Relation (or (RelationNameP Rel) '<unnamed>)))
(++ Printer type-relation 'printrelation)

(Defun namedrel-deleter (&REST IGNORE)
  (DECLARE (IGNORE IGNORE))
  'DELETERELNAME)

(defun deleterelname (ignore rel-or-name &rest ignore2)
  (declare (ignore ignore ignore2))
  (forany  a s.t. (relationarity (relationp rel-or-name) a) 
	(-- relationarity (relationp rel-or-name) a)
	ifnone nil))
#+ignore ; leave this to the caller - might want to atomically kill and make another
(insist "supposed to delete it" not (E (rel) (relationname rel relname)))

; this is defined here because it uses ++ (and thus has to be recompiled
; anyway whenever this bootstrapping process is done)

(defun DefRel (RelName Args Defn &aux rel)
  (try (ExpandDescription (list args 's.t. defn))
    'ExpandDescription
    (abort 'bad-definition
	   "bad definition for ~S~%~S~%~S"
	   RelName (list Args 's.t. Defn) tryvalue))
  (setq rel (or (relationp RelName) (make-dbobject)))
  ; try to use old one ...
  (Add-imparityname rel 'Defined (LENGTH Args) RelName)
  (++ WffDefn rel (list Args 's.t. Defn))
  Defn)

                                                                ; DefinedRelName
(defrel 'DefinedRelName '(relname def)
  '(e (rel arity)(and (relationarity rel arity)
		      (relationname rel relname)
		      (relationimplementation rel 'defined)
		      (WffDefn rel def))))
(++ compare-relation (relationp 'definedrelname) 1 (relationp 'equal))

(++ RelAdder (RelationP 'DefinedRelName)
    '(lambda (&rest ignore)
       (declare (ignore ignore))
	'definedrelname-adder))

(defun definedrelname-adder (ignore relname def)
  (declare (ignore ignore))
  (cond ((?? definedrelname relname def)
	 (insist "supposed to add it" DefinedRelname relname def))
	(t (defrel relname (car def) (caddr def)))))

(++ reldeleter (relationp 'definedrelname) 'namedrel-deleter)
;
; we could supply a reltester and relgenerator here, but I don't see the need
; (same applies for all the other implementation types)

                                                                ; CodedRelName
(++ DefinedRelName 'CodedRelName
    '((rname code) s.t.
      (e (rel arity)(and (relationarity rel arity)
			 (relationname rel rname)
			 (relationimplementation rel 'coded)
			 (CodeDefn rel code)))))
;***(++ compare-relation (relationp 'codedrelname) 1 (relationp 'equal))

(++ RelAdder (RelationP 'CodedRelName)
    '(lambda (&rest ignore) (declare (ignore ignore))
	'codedrelname-adder))

(defun codedrelname-adder (ignore name def) (declare (ignore ignore))
  (cond ((loop for var in (car def) thereis
	       (VariableTypeName var))
	 (abort 'typed-var-in-codedefn
		"CodedRel definitions have no typed parameters:~%~S" def))
	((?? codedrelname name def)
	 (insist "supposed to add it" CodedRelName name def))
	(t (defcodedrel name (car def) (caddr def)))))

(++ reldeleter (relationp 'codedrelname) 'namedrel-deleter)

(++ DefinedRelName 'CodedRel
    '((rel code) s.t.
      (e (arity)(and (relationarity rel arity)
		     (relationimplementation rel 'coded)
		     (CodeDefn rel code)))))

;***(++ compare-relation (relationp 'codedrel) 1 (relationp 'equal))

(++ RelAdder (RelationP 'CodedRel)
    '(lambda (&rest ignore) (declare (ignore ignore))
	'codedrel-adder))

(defun codedrel-adder (ignore rel def) (declare (ignore ignore))
  (cond ((loop for var in (car def) thereis
	       (VariableTypeName var))
	 (abort 'typed-var-in-codedefn
		"CodedRel definitions have no typed parameters:~%~S" def))
	((?? codedrel rel def)
	 (insist "supposed to add it" CodedRel rel def))
	(t (defcodedrel1 rel (car def) (caddr def)))))

                                                                ; BaseRelName
(++ definedrelname 'BaseRelName
    '((name arity) s.t. (e (r) (and (RelationImplementation r 'Base)
				    (relationarity r arity)
				    (relationname r name)))))
;***(++ compare-relation (relationp 'baserelname) 1 (relationp '=))

(++ RelAdder (RelationP 'BaseRelName)
    '(lambda (&rest ignore) (declare (ignore ignore))
	'baserelname-adder))
(defun baserelname-adder (ignore name arity) (declare (ignore ignore))
  (cond ((?? BaseRelName name arity)
	 (insist "supposed to add it" BaseRelName name arity))
	(t (Add-imparityname (make-dbobject) 'base arity name))))

(++ reldeleter (relationp 'baserelname) 'namedrel-deleter)

                                                                ; PropRelName
(++ definedrelname 'PropRelname
    '((name) s.t. (e (r)(and (relationarity r 2)
			     (relationImplementation r 'structprop)
			     (relationname r name)))))
(++ RelAdder (RelationP 'PropRelName)
    '(lambda (&rest ignore) (declare (ignore ignore))
      'proprelname-adder))
(defun proprelname-adder (ignore name) (declare (ignore ignore))
  (cond ((?? PropRelName name)
	 (insist "supposed to add it" PropRelName name))
	(t (add-imparityname (make-dbobject) 'structprop 2 name))))
(++ reldeleter (relationp 'proprelname) 'namedrel-deleter)

                                                                ; DoublePropRelName
(++ definedrelname 'DoublePropRelname
    '((name) s.t. (e (r)(and (relationarity r 2)
			     (relationImplementation r 'two-way-structprop)
			     (relationname r name)))))
(++ RelAdder (RelationP 'DoublePropRelName)
    '(lambda (&rest ignore) (declare (ignore ignore))
      'doubleproprelname-adder))
(defun doubleproprelname-adder (ignore name) (declare (ignore ignore))
  (cond ((?? doublePropRelName name)
	 (insist "supposed to add it" doublePropRelName name))
	(t (add-imparityname (make-dbobject) 'two-way-structprop 2 name))))
(++ reldeleter (relationp 'doubleproprelname) 'namedrel-deleter)

                                                                ; TreeRelName
(++ definedrelname 'TreeRelName
    '((relname arity) s.t. (e (r)(and (relationarity r arity)
				      (relationImplementation r 'tree)
				      (relationname r relname)))))
;***(++ compare-relation (relationp 'treerelname) 1 (relationp '=))
(++ RelAdder (RelationP 'TreeRelName)
    '(lambda (&rest ignore) (declare (ignore ignore))
	'treerelname-adder))
(defun treerelname-adder (ignore name arity) (declare (ignore ignore))
  (cond ((?? TreeRelName name arity)
	 (insist "supposed to add it" TreeRelName name arity))
	(t (add-imparityname (make-dbobject) 'tree arity name))))
(++ reldeleter (relationp 'treerelname) 'namedrel-deleter)

                                                                ; treeproprelname
(++ definedrelname 'TreePropRelName
    '((name) s.t. (e (r) (and (relationname r name)
			      (relationarity r 2)
			      (relationimplementation r 'treeprop)))))
(++ reladder (relationp 'treeproprelname)
    '(lambda (&rest ignore) (declare (ignore ignore)) 'treepropname-adder))
(defun treepropname-adder (ignore name) (declare (ignore ignore))
  (cond ((?? treeproprelname name)
	 (insist "supposed to add it" treeproprelname name))
	(t (add-imparityname (make-dbobject) 'treeprop 2 name))))
(++ reldeleter (relationp 'treeproprelname) 'namedrel-deleter)

                                                                ; treeprop+
(++ RelAdder 'TreeProp+ 'AddTreeProp)
(++ RelDeleter 'TreeProp+ 'DelTreeProp)
(++ RelTester 'TreeProp+ 'TestTreeProp)
(++ TestEffort 'TreeProp+
 '(lambda (&rest pat) (min 50 (* 3 (relationsize '(x)(cons (car pat) '(a x)))))))
(++ RelGenerator 'TreeProp+ 'TreePropGenerators)

                                                                ; treeprop+relname
(++ definedrelname 'TreeProp+RelName
    '((name) s.t. (e (r) (and (relationname r name)
			      (relationarity r 2)
			      (relationimplementation r 'treeprop+)))))
(++ reladder (relationp 'treeprop+relname)
    '(lambda (&rest ignore) (declare (ignore ignore)) 'treeprop+name-adder))
(defun treeprop+name-adder (ignore name) (declare (ignore ignore))
  (cond ((?? treeprop+relname name)
	 (insist "supposed to add it" treeprop+relname name))
	(t (add-imparityname (make-dbobject) 'treeprop+ 2 name))))
(++ reldeleter (relationp 'treeprop+relname) 'namedrel-deleter)

                                                                ; relationname
(++ relsize (RelationP 'RelationName) '(output output) 1000)
(++ relsize (RelationP 'RelationName) '(input output) 1)
(++ relsize (RelationP 'RelationName) '(output input) 1)
                                                                ; RelationArity
(++ relsize (RelationP 'RelationArity) '(input output) 1)
(++ relsize (RelationP 'RelationArity) '(output output) 1000)
(++ relsize (RelationP 'RelationArity) '(output input) 500)
; as in 500 binary rels
                                                        ; RelationImplementation
(++ relsize (RelationP 'RelationImplementation) '(output output) 1000)
(++ relsize (RelationP 'RelationImplementation) '(input output) 1)
(++ relsize (RelationP 'RelationImplementation) '(output input) 100)
; as in basetype?

; with optimized testers, again assuming no forgeries
;
(++ reltester (relationp 'RelationName)
    '(lambda (&rest wff)
       'relationname-tester))
(defun relationname-tester (ignore rel name) (declare (ignore ignore))
  (and (dbobject-p rel)
       (member name (get-structure-property rel 'relationname))))

(++ reltester (relationp 'RelationArity)
    '(lambda (&rest wff)
       'relationarity-tester))
(defun relationarity-tester (ignore rel arity) (declare (ignore ignore))
  (and (dbobject-p rel)
       (member arity (get-structure-property rel 'relationarity)
	       :test #'=)))
(++ reltester (relationp 'RelationImplementation)
    '(lambda (&rest wff)
       'RelationImplementation-tester))
(defun RelationImplementation-tester (ignore rel imp) (declare (ignore ignore))
  (and (dbobject-p rel)
       (member imp (get-structure-property rel 'relationimplementation))))

(++ testeffort (relationp 'relationname)
    #'(lambda (&rest ignore) (declare (ignore ignore)) 10))
(++ testeffort (relationp 'relationarity)
    #'(lambda (&rest ignore) (declare (ignore ignore)) 10))
(++ testeffort (relationp 'relationimplementation)
    #'(lambda (&rest ignore) (declare (ignore ignore)) 10))

;
; also optimized generators
; these all rely on count constraints that we have to be sure to include
;
(SimpleGenerator '(RelationName output a) '(mklist (GetRelationOfName a)))
(SimpleGenerator '(relationname a output)
		 '(and (dbobject-p a)
		       (get-structure-property a 'relationname)))
(SimpleGenerator '(relationarity a output)
		 '(and (dbobject-p a)
		       (get-structure-property a 'relationarity)))
(SimpleGenerator '(relationimplementation a output)
		 '(and (dbobject-p a)
		       (get-structure-property a 'relationimplementation)))


; proper-name relation - combination of proprel and treerel
(setq Rel-Proper-Name (make-dbobject))
(Add-imparityname Rel-Proper-Name 'TreeProp+ 2 'Proper-Name)

(++ RelSize (relationp 'proper-name) '(input output) 1)
(++ RelSize (relationp 'proper-name) '(output input) 1)

(++ BaseRelName 'PossibleToAdd 2)
(setq rel-possibletoadd (relationp 'Possibletoadd))
(++ RelSize (relationp 'Possibletoadd) '(input output) 1)

(++ BaseRelName 'PossibleToDelete 2)
(setq rel-possibletodelete (relationp 'Possibletodelete))
(++ RelSize (relationp 'Possibletodelete) '(input output) 1)

(++ BaseRelName 'NonTriggerable 1)
(setq rel-nontriggerable (relationp 'nontriggerable))

(++ baserelname 'inlinerel 1)

(++ baserelname 'not-allowed-to-update 2)
(defun not-allowed-to-update (rel tv)
  (?? not-allowed-to-update rel tv))

(++ RelAdder (relationp 'not-allowed-to-update) 
    '(lambda (&rest ignore)
       (declare (ignore ignore))
       'add-not-allowed-to-update))

(defun add-not-allowed-to-update (rel r tv &aux (tuple (list r tv)))
  (PutBaseData rel (CONS Tuple (GETBaseData Rel)))
  ; like AddBaseTuple plus
  ;; couldn't this decaching be done by a rule, like all the others?
  ;; in any case, this is no good cause it calls relationp during primitive update...
  ;(decache-rel r :adder :deleter)
  (rem-structure-property r 'adder)
  (rem-structure-property r 'deleter))

(++ Reldeleter (relationp 'not-allowed-to-update) 
    '(lambda (&rest ignore)
       (declare (ignore ignore))
       'del-not-allowed-to-update))

(defun del-not-allowed-to-update (Rel r n &aux memb)
  (cond ((setq memb (fmemb2 (list r n) (getbasedata rel)))
	 (putbasedata rel (delete memb (getbasedata rel)))))
  ; see remarks on adder ...
  (rem-structure-property r 'adder)
  (rem-structure-property r 'deleter))

(++ baserelname 'relupdater 2)
(++ relsize (relationp 'relupdater) '(input output) 1)

(++ baserelname 'wffmacro 1)

(buffer-break)

(dolist (m '(IMPLIES EQUIV NEQUIV ALL EXISTS NEED-UPDATE
		     IF-THEN-ELSE MULTIPLE OPTIONAL CHANGE IGNORE-VARS
		     SUBSET-GEN))
  (++ wffmacro m))

(defun macroexpand-1wff (wff env)
  (if (consp wff)
      (if (atom (first wff))
	  (if (testrel (theap5relation wffmacro) (car wff))
	      (macroexpand-1 wff env)
	      (values wff nil))
	  #+ignore ;; unknown why this was here.  Hypothesis --
          ;; it permitted (AND ((IMAGE-ORDER < AGE) p1 p2) ...)
	  (multiple-value-bind (new macp)
	      (macroexpand-1 (first wff) env)
	    (if macp
		(values (cons new (rest wff)) t)
		(values wff nil)))
	  (values wff nil))
      (values wff nil)))

; -------- now that we have it all loaded ... --------
(do-s.t. (r (relation r))
     (rem-structure-property r 'tester)
     (rem-structure-property r 'adder)
     (rem-structure-property r 'deleter)
     (rem-structure-property r 'canonicalizetuple)
     (rem-structure-property r 'rel-comparerels)
     (rem-structure-property r 'comparetuple))
; some of these were compiled with the wrong equivalence relations
; also get rid of all the generators
(setf generator-cache (createtree))
(declaim (special first-legitimate-compile))
(setf first-legitimate-compile (compile-ap '(lambda nil nil)))
; any use of an earlier compile-ap is not legitimate!
;
;                replace all the bootstrap definitions
;
; These functions are defined here because they access the database.  The bootstrap 
; versions are sufficient for loading this file, but they don't take into account
; delta.  Also, in order to reinitialize AP it is not necessary to reload the code. 
; It IS necessary to redefine functions that use the database, since the old
; compilations would refer to obsolete relations.

; these definitions can not be used until they are compiled

; this is just for bootstrapping - cache some generators
; it would be unnecessary if compiling x|Rax also cached x|Rxy
(any x y s.t. (possibletoadd x y) ifnone nil)
(any x s.t. (possibletoadd nil x) ifnone nil)
(any x y s.t. (possibletodelete x y) ifnone nil)
(any x s.t. (possibletodelete nil x) ifnone nil)
(any x y s.t. (reladder x y) ifnone nil)
(any x y s.t. (reldeleter x y) ifnone nil)
(any x y s.t. (relupdater x y) ifnone nil)
(any x s.t. (relupdater nil x) ifnone nil)
(any x y z u v s.t. (trigger x y z u v) ifnone nil)
(any x y z s.t. (trigger x y z nil nil) ifnone nil)

(++ TreeRelName 'MaintainedRel 3)
(++ compare-relation (relationp 'maintainedrel) 1 (relationp 'equal))
(++ TreePropRelName 'MatchMaintain)
; don't use wffdefn - that would require an expanddescription
; instead we use matchmaintain - which requires that it be declared here

(++ doubleproprelname 'maintain-mnode)
; this is to be cached to speed up compte-maintain-indirect in atomic transitions
(declaim (special maintaining-mnodes))
(setq maintaining-mnodes nil) ;later will be reset
(compile-or-mexpand 'maintain-mnode
 '(lambda (rel)
    (cond (maintaining-mnodes
	   (any mnode s.t. (maintain-mnode rel mnode) ifnone nil))
	  (t (any mnode s.t.
		  (e (def rule) (and (maintainedrel rel def rule)
				     (matchmaintain mnode rule)))
		  ifnone nil)))))
; looks like the compilation would be unaffected by the size declarations to come

(defun rels-maintained-by (mnode) (listof rel s.t. (maintain-mnode rel mnode)))

(defmacro-displace DBO (&rest x) `(apply #'ReadDBO ',x))

(Defun ReadDBO (&rest x &aux type)
  ;(or (char-equal (read-char stream) #\p) (help "ap readmacro?"))
  ;(setq rd (si:read-recursive stream))
  (cond ((not (cdr x))
	 (cond ((fboundp 'get-object-with-proper-name)
		;; aviod compiler warning about unbound function
		(funcall (symbol-function 'get-object-with-proper-name) (car x)))
	       (t (theonly xx s.t. (proper-name xx (car x))
			   :ifnone (error "nothing has proper name ~S" (car x))
			   :ifmany (error "ambiguous proper name ~S" (car x))))))
	((not (setq type (RelationP (car x))))
	 (error "DBO expects list to start with a type")) 
	((loop for reader in (get-structure-property type rel-reader)
	       thereis (apply reader x)))
	(t (error "no reader accepts ~S" x))))


; faster version that does no consing in a 1-state situation
; subfunctions needed to avoid consing!!
(compile-or-mexpand 'relationp1
 '(lambda (x)
   (any n s.t. (relationarity x n) ifnone nil)))
(compile-or-mexpand 'relationp2 
 '(lambda (x)
   (any (r) s.t. (relationname r x) ifnone nil)))

; **** we have to get the memos computed while delta is nil ****
;                  or before relationp is redefined
(relationp1 nil)
(relationp2 nil)

#-lucid
(defun relationp3 (x)
  (cond ((dbobject-p x)
	 (when (cond ((or delta	;(not (eq currentcx *globalcx*))
			  )
		      (relationp1 x))
		     (t (get-structure-property x 'relationarity)))
	       x))
	((symbolp x)
	 (cond ((or delta ;(not (eq currentcx *globalcx*))
		    )
		(let ((r (relationp2 x))) (when (relationp1 r) r)))
	       (t (values (gethash x RelationOfName)))))))
(progn
  #+lucid 
  (setf (symbol-function 'relationp3)
	#'(lambda (x)
	   (cond ((dbobject-p x)
		  (when (cond ((or delta ;(not (eq currentcx *globalcx*))
				   )
			       (relationp1 x))
			      (t (get-structure-property x 'relationarity)))
		    x))
		 ((symbolp x)
		  (cond ((or delta ;(not (eq currentcx *globalcx*))
			     )
			 (let ((r (relationp2 x))) (when (relationp1 r) r)))
			(t (values (gethash x RelationOfName))))))))
  (unless (compiled-function-p #'relationp3) (compile 'relationp3))
  (setf (symbol-function 'relationp) (symbol-function 'relationp3)))

(compile-or-mexpand 'implementations-of
 '(lambda (rel)
    (listof i s.t. (relationimplementation rel i))))
#+ignore 
(compile-or-mexpand 'ImplementationOf
 '(lambda (rel)
  #+ignore  ; macroexpand
  (any x s.t. (relationimplementation rel x))
  ; =>
  (PROG (X |State |)
     (SETQ |State |
	(LET ((ORIGINAL
		(LET (STATE)
		  (SETQ STATE
			(AND (DBOBJECT-p REL)
			     (GET-STRUCTURE-PROPERTY REL 'RELATIONIMPLEMENTATION)))
		      #'(LAMBDA NIL
			  (COND (STATE (VALUES NIL (POP STATE))) (T T)))))
	      POS NEG)
	  (cond ((or delta (not (eql currentcx *globalcx*)))
		 (MULTIPLE-VALUE-SETQ (POS NEG)
		   (COMPUTE-POS-AND-NEG REL-IMPLEMENTATION
			(#-symbolics progn
			 #+symbolics zl::let-closed
			 #+symbolics ((rel rel))
			 #'(LAMBDA (ARGS)  (EQL REL (CAR ARGS))))
			#'(LAMBDA (TUPLE &AUX (ARGS (TUPARGS TUPLE)))
			    (LIST (CAR (CDR ARGS))))))
		 (cond ((or pos neg)
			#-symbolics
			#'(LAMBDA (&REST IGNORE)
			    (declare (ignore ignore))
			    (COND (POS (psetf neg pos (cdr pos) neg  pos (cdr pos))
				       ;;; REUSE the cons cell that is POS
				       (APPLY 'VALUES NIL (CAR NEG)))
				  (T (GET-NEXT-INNERANSWER ORIGINAL NEG
					   #'(LAMBDA (CXTUPLE NEXT)
					        (EQL (CAR (CDR CXTUPLE))
							 (CAR (CDR NEXT))))))))
			#+symbolics
			(zl:let-closed ((pos pos) (neg neg) (original original))
			  #'(LAMBDA (&REST IGNORE)
			      (declare (ignore ignore))
			    (COND (POS (psetf neg pos (cdr pos) neg  pos (cdr pos))
				       ;;; REUSE the cons cell that is POS
				       (APPLY 'VALUES NIL (CAR NEG)))
				  (T (GET-NEXT-INNERANSWER ORIGINAL NEG
					   #'(LAMBDA (CXTUPLE NEXT)
					        (EQL (CAR (CDR CXTUPLE))
							 (CAR (CDR NEXT))))))))))
		       (t original)))
		(t original))))
     (when (LET (|Exhausted |)
		#+lucid(declare (ignore |Exhausted |))
	        (MULTIPLE-VALUE-SETQ (|Exhausted | X) (FUNCALL |State |)))
       (break "no implementation found"))
     (RETURN X))))



(compile-or-mexpand 'RelationNameP
 '(lambda (rel-or-name)
  (cond ((?? Relation rel-or-name)
	 (any n s.t. (relationname rel-or-name n) ifnone nil))
	((?? E (REL) (RELATIONNAME REL REL-OR-NAME)) rel-or-name))))

; it seems relname has to precede arity*
; we do this so as to avoid infinite recursion in arity*:

(defvar aritygen)
(setq aritygen
      (LOOKUP-GEN
	(MMEMO ((X0)
		S.T.
		(RELATIONARITY C0 X0)))))

(any x y s.t. (relationarity x y))

(compile-or-mexpand 'Arity*
 '(lambda (Rel) #+ignore ; macroexpand
	  (any x s.t. (relationarity rel x))
	  ; =>
	  (LET (|Exhausted | X (G10198 REL))
	       (declare (special aritygen) (ignorable |Exhausted |))
	     (COND ((MULTIPLE-VALUE-SETQ
		       (|Exhausted | X)
		       (FUNCALL (FUNCALL aritygen G10198)))
		    (ERROR "unsatisfied forany"))
		   (T X)))
	  ))

(compile-or-mexpand 'get-comparison
 '(lambda (rel pos &optional err-if-non-rel)
  (setq rel (relationp rel))
  (cond ((or (eq rel rel-anycompare) (eq rel rel-comparison))
	 (if (= pos 1) (theap5relation =) rel-eql))
	;; the assertions claim these two use = for position 1
	;; still need to fix special cases for illegal positions when err-if-non-nil?
	((eq rel rel-equivalence) rel-eql)
	((testrel rel-equivalence rel)  ;;switched with following clause
                                        ;;to get through bootstrapping --nmg
	 (when err-if-non-rel (error "no (single) comparison for ~A position ~A" rel pos))
	 (list rel))
	((testrel rel-anycompare rel pos)
	 (when err-if-non-rel (error "no comparison for ~A position ~A" rel pos))
	 t)
	; special case since code below uses it (otherwise infinite recursion)
	((testrel rel-implementation rel 'defined)
	 (let ((ans (varcompare (nth pos (expanded-defn-vars rel)))))
	   (unless (relationp ans)
	     (when err-if-non-rel
	       (error "no (single) comparison for ~A position ~A" rel pos)))
	   (or ans t)))
	;; returns a list or t (= anycompare) in some cases - ok?
	((any z s.t. (compare-relation rel pos z) ifnone rel-eql)))))

(compile-or-mexpand 'GetDefn
 '(lambda (DefinedRel)
  ;(setq DefinedRel (RelationP DefinedRel))
  (AND DefinedRel
       #+ignore (?? RelationImplementation DefinedRel 'Defined)
       (copy-tree (listof def s.t. (wffdefn definedrel def))))))

(compile-or-mexpand 'equivalence-relp
 '(lambda (x) (?? equivalence-relation x)))

(compile-or-mexpand 'nontriggerablep
 '(lambda (x) (?? nontriggerable x)))

; more bootstrapping pain ...
(any x y s.t. (reltester x y))

(compile-or-mexpand 'tester-for
 '(lambda (x)
   (coerce-if (copy-tree (any y s.t. (reltester x y) ifnone nil)))))

; more bootstrapping pain ...
(any x y s.t. (relgenerator x y))

(compile-or-mexpand 'generators-for
 '(lambda (x)
    (loop for y s.t. (relgenerator x y) collect
	(if (and (consp y) (eql (car y) 'lambda))
	    (let (comp gen)
	      (setq comp
		    (if (symbolp x) (get x 'compiled-gens)	; imp
			(get-structure-property x 'compiled-gens)))	; rel
	      (unless (setq gen (assoc y comp :test 'equal))
		(setq gen (list y (compile-ap (copy-tree y))))
		(if (symbolp x) (push gen (get x 'compiled-gens))
		    (add-structure-property x gen 'compiled-gens)))
	      (cadr gen))
	    y))))

(compile-or-mexpand 'all-generators-for
 '(lambda (rel)
    (nconc (generators-for rel)
	   (loop for imp s.t. (relationimplementation rel imp)
		 nconc (generators-for imp)))))

(compile-or-mexpand 'rel-sizes
 '(lambda (rel) (listof x y s.t. (relsize rel x y))))

(compile-or-mexpand 'get-testeffort 
 '(lambda (x)
    (coerce-if (any y s.t. (testeffort x y) ifnone nil))))

(compile-or-mexpand 'get-canonicalizer
 '(lambda (x)
  (forany y z s.t. (canonicalizer x y z) (list x y z) ifnone nil)))

; more bootstrapping pain ...
(any x y s.t. (cxvaluefn x y) ifnone nil)

(compile-or-mexpand 'cxvaluefn ;; we don't actually use this any more ...
 '(lambda (rel)
  (any f s.t. (cxvaluefn rel f)
       ifnone (any f s.t. ;; was (cxvaluefn (implementationof rel) f)
		   (E (imp) (and (relationimplementation rel imp)
				 (cxvaluefn imp f)))
		   ifnone nil))))

(compile-or-mexpand 'derivedrel
 '(lambda (rel)
    ;; was (?? derived (implementationof rel))
    (?? E (imp) (and (relationimplementation rel imp) (derived imp)))))

(defun get-triggers (rel)
  (listof (tv fn derived-rel derived-tv) s.t.
	  (trigger rel tv fn derived-rel derived-tv)))

(defun get-triggers-of (rel)
  (listof (stored-rel tv fn derived-tv) s.t.
	  (trigger stored-rel tv fn rel derived-tv)))

#+ignore ;; unused since multirep
(compile-or-mexpand 'get-update-macro
 '(lambda (rel tv)
    ; 2nd value says whether for rel or imp
    (case tv
      ((t) (forany m s.t. (reladder rel m) (values m t) ifnone
		   (any m s.t. (reladder (implementationof rel) m) ifnone nil)))
      ((nil) (forany m s.t. (reldeleter rel m) (values m t) ifnone
		     (any m s.t. (reldeleter (implementationof rel) m) ifnone nil)))
      #+ignore
      (inherit (any m s.t. (reladder rel m) ifnone
		    (any m s.t. (relinheriter (implementationof rel) m) ifnone nil)))
      (otherwise (error "illegal truth value")))))

(compile-or-mexpand 'get-checkers
 '(lambda (x) (listof c s.t. (checker x c))))
       
; meaning what rels trigger rel x
(defun get-depends-on (x)
  (remove-duplicates
    (loop for (rel tv fn derivedtv)
	  s.t. (trigger rel tv fn x derivedtv)
	  ;; trigger rel tv fn x derivedtv ;; warnings ...
	  collect rel)))
; lists of both of these are needed in transactions
; meaning what rels are triggered by rel x
(defun get-depends-on2 (x)
  (remove-duplicates
    (loop for (tv fn derivedrel derivedtv)
	  s.t. (trigger x tv fn derivedrel derivedtv)
	  collect derivedrel))) 

(compile-or-mexpand 'inlinerel? '(lambda (rel) (testrel 'inlinerel rel)))

; not needed for bootstrapping - used only to compile rules
(defun something-triggers? (rel addp)
  (forany (r tv fn) s.t. (trigger r tv fn rel addp) (declare (ignore r tv fn)) t ifnone nil))

(defun really-not-possible-to-update (rel addp)
  (cond (addp (?? possibletoadd rel nil))
	(t (?? possibletodelete rel nil))))
; yeah, it's useful - in this case we're really sure, even for derived rels.
#+ignore ;; unused since multirep
(defun get-update-fn (rel );&aux delta)
  ;; previously state needed to avoid accessing the db during update
  ; 2nd value says whether for the rel or the imp
  (forany x s.t. (relupdater rel x) (values x t) ifnone
	  (any x s.t. (relupdater (implementationof rel) x)
	       ifnone nil)))

(defun PossibleToUpdate (rel addp)
  ; can rel be added/deleted
  (cond ((cond (addp (forany x s.t. (possibletoadd rel x)
			     (return-from PossibleToUpdate x) ifnone nil))
	       (t (forany x s.t. (possibletodelete rel x)
			  (return-from PossibleToUpdate x) ifnone nil))))
	((forany (x tv fn) s.t. (trigger x tv fn rel addp)
		 (declare (ignore x tv fn)) t ifnone nil))
	(t (multiple-value-bind (single set cannot)
	       (update-code rel addp
			    (loop for i below (arity* rel) collect 'x))
	       (declare (ignore set single))
	       (not cannot)))
	;; above replaces all of below:
	;; are there enough adders/deleters/updaters
	#+ignore((get-update-fn rel))
	#+ignore (addp (?? E (x) (or (reladder rel x) (reladder imp x))))
	#+ignore (t (?? E (x) (or (reldeleter rel x) (reldeleter imp x))))))

(compile-or-mexpand 'defined-p
 '(lambda (rel)
    (?? relationimplementation rel 'defined)))

(compile-or-mexpand 'get-adder-or-deleter
 '(lambda (rel tv)
    (coerce-if (case tv
		 ((t) (any m s.t. (reladder rel m) ifnone nil))
		 ((nil) (any m s.t. (reldeleter rel m) ifnone nil))
		 (otherwise (error "illegal truth value"))))))

(compile-or-mexpand 'get-updater
 '(lambda (rel)
   (any x s.t. (relupdater rel x) ifnone nil)))
