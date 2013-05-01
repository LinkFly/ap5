;-*- Mode:LISP; Package:AP5; Base:10.; Syntax:Common-Lisp -*-
;
; implementations for relations
;
(in-package "AP5")

;(Defun FetchRelField (field) (relationnamep field))
; formerly  (intern (string-append "DATA-BASE-RELATION-" *) 'user))
;(Defun Alter-Relation () 'Alter-DBRelation)
;(Defun FieldName (field) (relationnamep field))

;;(* Base relations)
; base relations do not canonicalize - the tuple supplied is the tuple stored
; in order to test they use the comparison relation as given

(Defun AddBaseTuple (&rest ignore)
  (declare (ignore ignore))
  'Add1BaseTuple)

(defun Add1BaseTuple  (rel &rest tuple)
      (PutBaseData rel (CONS (copy-seq Tuple) (GETBaseData rel))))

(defun deletebasetuple (rel &rest ignore)
  (declare (ignore ignore))
  `(lambda (rel &rest tuple)
       (delete1basetuple rel tuple
	   #'(lambda (tuple data)
	       (fmemb3 tuple data ,rel)) ;;not a closure
	   )))

(defun delete1basetuple (rel tuple tail-finder)
  (declare #+symbolics (sys:downward-funarg tail-finder))
  (let (tail data)
    (if (setf tail (funcall tail-finder tuple (setf data (getbasedata rel))))
	(cond ((eq tail data) (putbasedata rel (rest data)))
	      ((null (rest tail))    (nbutlast data))
	      (t (psetf (first tail) (second tail) (rest tail) (cddr tail)))))))

(Defun TestBaseTuple (rel &rest ignore)
  (declare (ignore ignore))
  `(lambda (rel &rest tuple)
      (fmemb3 tuple (getbasedata rel) ,rel)))

(defun baserelgen (rel &rest ignore)
  (declare (ignore ignore))
  (let ((state (getbasedata rel)))	;symbolics bug
    #'(lambda (&rest ignore)
	(declare (ignore ignore))
	(if state
	    #+clisp ;; clisp likes the original
	    (apply #'values nil (pop state))
	    #-clisp ; most others seem to like this much better
	    (values-list (cons nil (pop state)))
	  t))))


(defun baserelgenerator (ignore vars rel &rest args)
  (declare (ignore ignore vars))
    ;; this test should never fail -- we believe it is TOTALLY unnecessary
    (unless (= (length args) (arity* rel))
	   (error "wrong arity ~s" (cons rel args)))
    ; new version: initialstate contains code which is applied to
    ; (rel &rest constant-args) [as before] but returns [rather than state]
    ; a closure which can be funcall'd to produce what pulsecode used to 
    ; return [except new state]
    `((initialstate baserelgen)
      (template ;,(loop for arg in args collect 'output)
       ,(make-list (length args) :initial-element 'output))
      (effort , (iftimes (relationsize args (cons rel args))
			 (iftimes 3. (length args))))))


;;(* relations defined by code)

;; defcodedrel and defcodedrelfn are moved to Relations, since they use ++


;;(* StructProp implementation package)
; relations that are stored in the property list of structures
; with property lists (such as relations).
; these are only two place relations whose first place is the structure

; structproprels handle equivalence by canonicalizing the first object
; (eq,eql,equal are all the same for structures)
; the second object is stored as given

(defun addstructprop (rel &rest ignore &aux
		      (cnc (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  (if (listp (car cnc))
      `(lambda (r x y)
	 (addstructprop-internal r ,(cadar cnc) y))
      'addstructprop-internal))

(defun addstructprop-internal (r x y)
       (push y (get-structure-property x r)))


(defun delstructprop (rel &rest ignore &aux
			  (cnc (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (r x y)
     (delstructprop-internal r ,(if (listp (first cnc)) `(,(cadar cnc) x) 'x)
			     y ,(get-test-function (get-comparison rel 1 t)))))

(defun delstructprop-internal (r x y test)
  (put-structure-property x
	(delete y (get-structure-property x r)  :test test  :count 1)
	r))

(defun structproptester (rel &rest ignore &aux
			     (cnc (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (r x y)
     ; canonicalize first, in case the canonicalizer turns a non-dbo into a dbo
     (structproptester-internal r ,(if (listp (first cnc))
				       `(,(cadar cnc) x)
				     'x)
		     y ,(get-test-function (get-comparison rel 1 t)))))

(defun structproptester-internal (r x y test)
  (and (DBObject-p x)
       (member y (get-structure-property x r)  :test test)))

(defun structpropgen (prop dbo)
 (let ((state (and (DBObject-p dbo)
		   (get-structure-property dbo prop))))
   #'(lambda ()  (if state
		     (values nil (pop state))
		   t))))

(defun structpropgenerator (ignore ignore2 r x ignore3 &aux
				   (cnc (get-comparisons-and-canonicalizers r)))
  (declare (ignore ignore ignore2 ignore3))
  `((initialstate 
      (lambda (r dbo)
	(structpropgen r
 	 ,(if (listp (car cnc))
	      `(,(cadar cnc) dbo)
	    'dbo))))
    (template (input output))
    (effort , (iftimes 3. (relationsize '(%x) (list r x '%x))))))

;; two way structprop (double pointers)
; these handle equivalence by canonicalizing both objects
; then of course it doesn't matter which of eq/eql/equal are used

; problem: we need 2 property names for each rel (if we used the same two names
; then all such rels would be the same)
; solution: use gensyms and store those property names with the relation
; This means that the property names cannot be compiled in - we have to
; use a memo that will be recomputed each time the code is loaded.

(defun forward-name (rel)
  #+ignore
  (or (get-structure-property rel 'forward-name)
      (put-structure-property rel (gensym "Forward") 'forward-name))
  (let ((n (relationnamep rel)))
    (intern (concatenate 'string (symbol-name n) "-" "Forward")
	    (symbol-package n))))

(defun backward-name (rel)
  #+ignore
  (or (get-structure-property rel 'backward-name)
      (put-structure-property rel (gensym "Backward") 'backward-name))
  (let ((n (relationnamep rel)))
    (intern (concatenate 'string (symbol-name n) "-" "Backward")
	    (symbol-package n))))

(defun add2structprop (rel &rest ignore &aux
			   (cnc (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel x y) (declare (ignore rel))
     ,.(when (listp (first cnc)) `((setf x (,(cadar cnc) x))))
     ,.(when (listp (second cnc)) `((setf y (,(cadadr cnc) y))))
     (add-structure-property x y  ;,(copy-tree '(memo (forward-name rel)))
			     ',(forward-name rel))
     (add-structure-property y x ;,(copy-tree '(memo (backward-name rel)))
			     ',(backward-name rel))))

(defun del2structprop (rel &rest ignore &aux
			   (cnc (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel x y) (declare (ignore rel))
     (del2structprop-internal
      ,(if (listp (first cnc)) `(,(cadar cnc) x) 'x)
      ,(if (listp (second cnc)) `(,(cadadr cnc) y) 'y)
      ,(get-test-function (get-comparison rel 0 t))
      ,(get-test-function (get-comparison rel 1 t))
      ;,(copy-tree '(memo (forward-name rel)))
      ',(forward-name rel)
      ;,(copy-tree '(memo (backward-name rel)))
      ',(backward-name rel))))

(defun del2structprop-internal (x y domain-test range-test fwd bkd)
  (put-structure-property
   x (delete y (get-structure-property x fwd)
	     :test range-test
	     :count 1)
   fwd)
  (put-structure-property
   y (delete x (get-structure-property y bkd)
	     :test domain-test
	     :count 1)
   bkd))

; for dbobjects, it's hard to imagine equivalence other than eql

(defun structprop2tester-internal (prop x y test)
  (and (DBObject-p x)
       (member y (get-structure-property x prop) :test test)))

(defun structprop2tester (rel &rest ignore &aux
			      (cnc (get-comparisons-and-canonicalizers rel))
			      (size0 (relationsize '(x) (list rel 'x 'a)))
			      (size1 (relationsize '(x) (list rel 'a 'x))))
  (declare (ignore ignore))
  (if (iflessp size1 size0)
      `(lambda (rel x y)
	 (declare (ignore rel))
	 (structprop2tester-internal
	  ;,(copy-tree '(memo (forward-name rel)))
	  ',(forward-name rel)
	  ,(if (listp (first cnc)) `(,(cadar cnc) x) 'x)
	  y
	  ,(get-test-function (get-comparison rel 1 t))))
      `(lambda (rel x y)
	 (declare (ignore rel))
	 (structprop2tester-internal
	  ;,(copy-tree '(memo (backward-name rel)))
	  ',(backward-name rel)
	  ,(if (listp (second cnc)) `(,(cadadr cnc) y) 'y)
	  x
	  ,(get-test-function (get-comparison rel 0 t))))))

; Only generate the things related to a constant 
; assume that plist objects cannot be enumerated

(defun structprop2generator (ignore ignore1 rel ignore2 ignore3 &aux
				    (cnc (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore ignore1 ignore2 ignore3))
  (values
    `((initialstate
	(lambda (rel x) (declare (ignore rel))
	  (structpropgen ;,(copy-tree '(memo (forward-name rel)))
	                 ',(forward-name rel)
			 (,(if (listp (car cnc)) (cadar cnc) 'progn) x))))
      (template (input output))
      (effort , (iftimes 3. (relationsize '(x) (list rel 'a 'x)))))
    `((initialstate
	(lambda (rel x) (declare (ignore rel))
	  (structpropgen ;,(copy-tree  '(memo (backward-name rel)))
	   ',(backward-name rel)
	   (,(if (listp (cadr cnc)) (cadadr cnc) 'progn) x))))
      (template (output input))
      (effort , (iftimes 3. (relationsize '(x) (list rel 'x 'a)))))))



;;(* PartOfRel implementation package) - removed
;;(* PropRel implementation package) - removed

(defun get-comparisons-and-canonicalizers (rel &aux relp)
  ; for each arg of rel either one of the symbols eq,eql,equal, or a list
  ; of the form (eq/eql/equal canonicalizer-function)
  (or (setf relp (relationp rel)) (error "~s not a relation" rel))
  (loop for arg below (arity* relp) collect (get-c-and-c relp arg)))

(defun get-c-and-c (rel arg)
  (c-and-c (get-comparison rel arg t)))

(defun c-and-c (compare &aux entry)
  (declare (special eql-table))
  (cond ((member compare eql-table) (equiv-name compare))
	((setf entry (get-canonicalizer compare))
	 (or (member (cadr entry) eql-table)
	     (error "~s does not canonicalize to a primitive equivalence" compare))
	 (list (equiv-name (cadr entry)) (caddr entry))) ; (equiv-rel canon-fn)
	(t (error "~s cannot be canonicalized" compare))))

; just like rel but for arbitrary vars
(defun get-comparison-and-canonicalizer (vars)
  (declare (special eql-table))
  (loop for var in vars collect
	(let ((compare (varcompare var)))
	  (when (listp compare) ;(and (not bootstrapping)) ?
	    (let ((realcompare (loop for c in compare thereis
				     (and (fsubset compare (allsupertypes c))
					  c))))
	      (if realcompare
		  (setf compare realcompare)
		  (error "no most specific comparison for ~S" var))))
	  (c-and-c compare))))








;; TreeProp: a combination of structprop and treerels for binary relations, e.g., 
; proper-name which relates dbobjects to names - the name will be stored
; as a property of the object, but the object will be associated with the
; name in a table stored with the relation.

; put together tree and structprop - but tree has args reversed, and we know
; in advance that they're x and y

(DefMacro-displace GetTreeData+ (Rel compare)
  `(or (Get-Structure-Property , Rel 'TreeData+)
       (put-structure-property , Rel (make-hash-table :test ,compare) 'TreeData+)))

(Defun AddTreeprop+ (rel x y equiv)
 (cond ((dbobject-p x)
	(push y (get-structure-property x rel)))
       ((symbolp x) (push y (get x rel)))
       (t (push y (gethash x (GETTreeData+ rel equiv))))))

;; treeprop+ is a generalization of treeprop. 
;; if a relation has both implementations, we can just treat it as treeprop+
(Defun AddTreeprop (rel &rest ignore &aux
			 (cnc (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel x y)
     ,.(when (listp (car cnc)) `((setf x (,(cadar cnc) x))))
     ,.(when (listp (cadr cnc)) `((setf y (,(cadadr cnc) y))))
     ,(if (member 'treeprop+ (implementations-of (relationp rel)))
	  `(addtreeprop+ rel x y
			 ',(if (listp (first cnc)) (caar cnc) (first cnc)))
	'(push y (get-structure-property x rel)))
     #+ignore ; single imp version
     ,(ecase (implementationof (relationp rel)) ; in case we get the name
	(treeprop
	  '(push y (get-structure-property x rel)))
	(treeprop+ `(addtreeprop+ rel x y ',(if (listp (first cnc))
						(caar cnc)
					        (first cnc)))))
     (TreeAdder (list y x)
       (GETTreeData rel)
       ',(mapcar #'(lambda (x) (if (listp x) (first x) x))
		 (reverse cnc)))))

(Defun DelTreeprop+ (rel x y domain-equiv range-equiv)
  (cond ((dbobject-p x)
	 (put-structure-property x
	    (delete y (get-structure-property x rel)
		    :test range-equiv
		    :count 1)
	    rel))
	((symbolp x)
	 (setf (get x rel) 
	       (delete y (get x 'classification) :count 1
		       :test range-equiv)))
	(t (let ((table (GETTreeData+ rel domain-equiv)))
	     (setf (gethash x table) 
		   (delete y (gethash x table)
			   :count 1 :test range-equiv))))))

(Defun DelTreeprop (rel &rest ignore &aux
			    (cnc (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel x y)
     ,.(when (listp (car cnc)) `((setf x (,(cadar cnc) x))))
     ,.(when (listp (cadr cnc)) `((setf y (,(cadadr cnc) y))))
     ,(if (member 'treeprop+ (implementations-of (relationp rel))) 
	  `(DelTreeprop+ rel x y
			 ',(if (listp (first cnc)) (caar cnc) (first cnc))
			 #',(if (listp (second cnc))
				(caadr cnc)
			      (second cnc)))
	`(put-structure-property x
	    (delete y (get-structure-property x rel)
		    :test (function ,(if (listp (second cnc))
					 (caadr cnc)
				       (second cnc)))
		    :count 1)
	    rel))
     #+ignore ;; single imp version
     ,(ecase (implementationof (relationp rel))
	(treeprop
	  `(put-structure-property x
	     (delete y (get-structure-property x rel)
		     :test (function ,(if (listp (second cnc))
					  (caadr cnc)
					  (second cnc)))
		     :count 1)
	     rel))
	(treeprop+
	 `(DelTreeprop+ rel x y
		',(if (listp (first cnc))
		      (caar cnc)
		      (first cnc))
		#',(if (listp (second cnc))
		       (caadr cnc)
		       (second cnc)))))		  
      (TreeDeleter (list y x)
	(GETTreeData rel)
	',(mapcar #'(lambda (x) (if (listp x) (first x) x))
		  (reverse cnc)))))

(defun TestTreeprop+ (r x y domain-equiv range-test)
  (cond ((dbobject-p x)
	 (member y (get-structure-property x r)	:test range-test))
	((symbolp x) (member y (get x r) :test range-test))
	(t (member y (gethash x (GETTreeData+ r domain-equiv))
		   :test range-test))))

(defun TestTreeprop (rel &rest ignore &aux (cnc (get-c-and-c rel 0)))
  (declare (ignore ignore))
  `(lambda (r x y)
     ,.(when (listp cnc) `((setf x (,(cadr cnc) x))))
     ,(let ((eqv (get-test-function (get-comparison rel 1 t))))
	(if (member 'treeprop+ (implementations-of (relationp rel)))
	    `(testtreeprop+ r x y
			    ',(if (listp cnc) (first cnc) cnc)
			    ,eqv)
	  `(and (DBObject-p x)
		(member y (get-structure-property x r) :test ,eqv)))
	#+ignore ;; single imp version
	(ecase (implementationof (relationp rel))
          (treeprop
	   `(and (DBObject-p x)
		 (member y (get-structure-property x r) :test ,eqv)))
	  (treeprop+ 
	   `(testtreeprop+ r x y
			   ',(if (listp cnc) (first cnc) cnc)
			   ,eqv))))))

;; use the proprel tester on the assumption that this implementation will be used
; for situations where the prop list is short.

(Defun TreepropGenerators (subsetflg vars r x y)
  (declare (special treegenproptable))
  (values-list
    (cons (if (member 'treeprop+ (implementations-of (relationp r)))
	      (generalpropgenerator subsetflg vars r x y)
	    (structpropgenerator subsetflg vars r x y))
	  #+ignore ;; single imp version
	  (ecase (implementationof (relationp r))
	    (treeprop (structpropgenerator subsetflg vars r x y))
	    (treeprop+ (generalpropgenerator subsetflg vars r x y)))
	  (loop for g in treegenproptable collect
		(cons (list 'effort
			    (iftimes 50. ; careful about output comparisons
				     (let ((args (loop for x in
						       (cadr (assoc 'template g))
						       collect
						       (cond ((eq x 'output)
							      (gensym "V"))
							     (t x)))))
				       (relationsize (remove 'input args)
						     (cons r args)))))
		      (flet ((fix-treeprop-equiv (rel)
			       (let ((c (get-c-and-c rel 1)))
				 (if (listp c)
				     `(setf CMP0 #',(car c)
					    INPUT0 (,(cadr c) INPUT0))
				     `(setf CMP0 #',c)))))
			(subst (fix-treeprop-equiv r) '*tree-equiv-code-here* g)))))))

(defun genprop-gen (r dbo domain-equiv)
  (let ((state (cond ((DBObject-p dbo) (get-structure-property dbo r))
		     ((symbolp dbo) (get dbo r))
		     (t (gethash dbo (GETTreeData+ r domain-equiv))))))
    #'(lambda ()  (if state (values nil (pop state)) t))))

(defun generalpropGenerator (ignore ignore2 r x ignore3 &aux
				   (cnc (get-comparisons-and-canonicalizers r)))
  (declare (ignore ignore ignore2 ignore3))
  `((initialstate
      (lambda (r dbo) (genprop-gen r
			  ,(if (listp (first cnc)) `(,(cadar cnc) dbo) 'dbo)
			  ',(cond ((listp (car cnc)) (caar cnc))
						    (t (car cnc))))))
    (template (input output))
    (effort , (iftimes 3.0 (relationsize '(%x) (list r x '%x))))))


#+ignore 
(defun treegen-out-in (REL INPUT0 CMP0) ;generated from the normal tree generator table but edited
   (let ((STATE (CONS 'START (GETTREEDATA REL))))
     #'(LAMBDA ()
	 (PROG NIL
	       (COND ((EQ (CAR STATE) 'START)
		      (SETF STATE
			    (LIST NIL NIL (LIST (CONS NIL (CDR STATE)))))
		      (GO GEN1START))
		     (T (GO CONT)))
	    GEN0CONT
	       (RETURN T)
	    GEN1START
	       (TREE-CONSTANT-NON-LAST (CDR STATE) INPUT0 CMP0)
	    GEN1CONT
	       (AND (TREE-EXHAUSTED (CDR STATE)) (GO GEN0CONT))
	    GEN2START
	       (TREE-VARIABLE-LAST STATE)
	    GEN2CONT CONT
	       (AND (TREE-EXHAUSTED STATE) (GO GEN1CONT))
	       (RETURN (MULTIPLE-VALUE-PROG1
			 (VALUES NIL (CAAR STATE))
			 (RPLACA STATE (CDAR STATE))))))))

(defun treegen-out-in (REL INPUT0 CMP0)
  ;generated from the normal tree generator table but edited
   (let ((STATE (CONS 'START (GETTREEDATA REL))))
     #'(LAMBDA ()
	 (PROG ()
	       (if (EQ (CAR STATE) 'START)
		   (SETF STATE
			 (LIST NIL NIL (LIST (CONS NIL (CDR STATE)))))
		   (GO CONT))
	       (TREE-CONSTANT-NON-LAST (CDR STATE) INPUT0 CMP0)
	    GEN1CONT
	       (when (TREE-EXHAUSTED (CDR STATE)) (return t))
	       (TREE-VARIABLE-LAST STATE)
	    CONT
	       (AND (TREE-EXHAUSTED STATE) (GO GEN1CONT))
	       (RETURN (MULTIPLE-VALUE-PROG1
			 (VALUES NIL (CAAR STATE))
			 (pop (car state))))))))

#+ignore 
(defun treegen-out-out (REL)
  (let ((STATE (CONS 'START (GETTREEDATA REL))))
    #'(LAMBDA NIL
	(PROG NIL
	      (COND ((EQ (CAR STATE) 'START)
		     (SETF STATE
			   (LIST NIL NIL (LIST (CONS NIL (CDR STATE)))))
		     (GO GEN1START))
		    (T (GO CONT)))
	   GEN0CONT
	      (RETURN T)
	   GEN1START
	      (TREE-VARIABLE-NON-LAST (CDR STATE))
	   GEN1CONT
	      (AND (TREE-EXHAUSTED (CDR STATE)) (GO GEN0CONT))
	   GEN2START
	      (TREE-VARIABLE-LAST STATE)
	   GEN2CONT CONT
	      (AND (TREE-EXHAUSTED STATE) (GO GEN1CONT))
	      (RETURN (MULTIPLE-VALUE-PROG1
			(VALUES NIL (CAAR STATE) (CAAAR (CDR STATE)))
						; switch order of outputs
			(RPLACA STATE (CDAR STATE))))))))

(defun treegen-out-out (REL)
  (let ((STATE (CONS 'START (GETTREEDATA REL))))
    #'(LAMBDA ()
	(PROG ()
	      (if (EQ (CAR STATE) 'START)
		  (SETF STATE
			(LIST NIL NIL (LIST (CONS NIL (CDR STATE)))))
		  (GO CONT))
	      (TREE-VARIABLE-NON-LAST (CDR STATE))
	   GEN1CONT
	      (when (TREE-EXHAUSTED (CDR STATE)) (return t))
	      (TREE-VARIABLE-LAST STATE)
	   CONT
	      (AND (TREE-EXHAUSTED STATE) (GO GEN1CONT))
	      (RETURN (MULTIPLE-VALUE-PROG1
			(VALUES NIL (CAAR STATE) (CAAAR (CDR STATE)))
						; switch order of outputs
			(pop (first state))))))))

(setf treegenproptable 
 '(((TEMPLATE (OUTPUT INPUT))  ; switched order
      (INITIALSTATE
	 (LAMBDA (REL INPUT0 &AUX CMP0)
	   *TREE-EQUIV-CODE-HERE*
	   (treegen-out-in REL INPUT0 CMP0))))
   ; skip (OUTPUT INPUT) since it's better as a prop
   ((TEMPLATE (OUTPUT OUTPUT))
      (INITIALSTATE treegen-out-out))))


(defun tree-variable-non-last (loc)
  (rplaca loc (cond ((integerp (cadr (caadr loc)))
		     (cdr (cdaadr loc)))
		    (t (let (apspec1)
			 (maphash
			   #'(lambda (x y)	;switch order from ilisp
			       (push (cons x y) apspec1))
			   (car (cdaadr loc)))
			 apspec1 )))))

(defun tree-variable-last (loc)
  (rplaca loc (cond ((integerp (cadr (caadr loc)))
		     (cdr (cdaadr loc)))
		    (t (let (apspec1)
			 (maphash
			   #'(lambda (x y)	;switch order from ilisp
			       (declare (ignore y)) ; avoid a compiler warning
			       (push x apspec1))
			   (car (cdaadr loc)))
			 apspec1 )))))

(defun tree-constant-non-last (loc constant compare
			       &aux (table (cadr (caadr loc))))
  (rplaca loc (cond ((integerp table)
		     (let ((val (assoc constant (cdr (cdaadr loc))
				       :test compare)))
		       (and val (list val))))
		    (t (let ((val (gethash constant table)))
			 (and val (list (cons constant val))))))))

(defun tree-constant-last (loc constant compare
			   &aux (table (cadr (caadr loc))))
  (rplaca loc (cond ((integerp table)
		     (and (member constant (cdr (cdaadr loc))
				  :test compare)
			  '(found)))
		    (t (let ((val (gethash constant table)))
			 (and val (list (cons constant val))))))))

(defun tree-exhausted (loc)
  (unless (car loc)
    (rplaca (cdr loc) (cdadr loc))
    t))