;-*- Mode:LISP; Package:AP5; Base:10.; Syntax:Common-Lisp -*-

(in-package "AP5")
;;(* tree relation package)
;
; A tree of level n is either a "short" tree of level n or a "long" tree
; of level n.  A short tree of level 1 is a list (length .  elements).  A long
; tree of level 1 is a hashtable that associates with each element the
; value T.  A short tree of level n+1 is a list of the form
; (length . alist) where alist associates with each element a tree of 
; level n.  A long tree of level n+1 is a list whos only element is a
; hashtable that associates with each element a tree of level n.
; At the moment, trees start short, and may become long, but never
; return to short representation.

; TreeRels store only canonicalized objects, so they can use eq/eql/equal hashtables


(defvar *MaxTreeList* 30)

(declaim (inline createtree))
(defun CreateTree () (list 0))

(defun constant-equality-sig (names)
  (unless (every #'symbolp names)
      (error "non-symbolic equality"))
  #-lucid
  `(load-memo				;memo
    (list ,.(mapcar #'(lambda (x)
			`(function ,x))
		    names)))
  #+lucid
  `',(copy-list names))

(DefMacro-displace GetTreeData (Rel)
  `(or (Get-Structure-Property , Rel 'TreeData)
       (put-structure-property , Rel (CreateTree) 'TreeData)))

(Defun AddTreeTuple (rel &rest ignore &aux
			 (compare (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel &rest tuple)
     ,@(unless compare '((declare (ignore tuple))))
      ,(if compare
	   `(TreeAdder
	      ,(if (some #'listp compare)
		   `(list ,.(loop for cmp in compare collect
				  (if (listp cmp)
				      (list (cadr cmp) '(pop tuple))
				      '(pop tuple))))
		   'tuple)
	      (GETTreeData rel)
	      ,(constant-equality-sig
		(mapcar #'(lambda (x)(if (listp x) (car x) x))
		       compare)))
	   ; arity 0
	   `(setf (first (GETTreeData rel)) 1))))

(Defun DeleteTreeTuple (rel &rest ignore &aux
			    (compare (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel &rest tuple)
     ,@(unless compare '((declare (ignore tuple))))
      ,(if compare
	   `(TreeDeleter
	      ,(if (some #'listp compare)
		   `(list ,.(loop for cmp in compare collect
				  (if (listp cmp)
				      (list (cadr cmp) '(pop tuple))
				      '(pop tuple))))
		   'tuple)
	      (GETTreeData rel)
	      ,(constant-equality-sig
	       (mapcar #'(lambda (x)(if (listp x) (car x) x))
		       compare)))
	   ; arity 0
	   `(setf (first (GETTreeData rel)) 0))))


(Defun TestTreeTuple (rel &rest ignore &aux
			    (compare (get-comparisons-and-canonicalizers rel)))
  (declare (ignore ignore))
  `(lambda (rel &rest tuple)
     ,@(unless compare '((declare (ignore tuple))))
      ,(if compare     
	   `(TreeTester
	      ,(if (some #'listp compare)
		   `(list ,.(loop for cmp in compare collect
				  (if (listp cmp)
				      (list (cadr cmp) '(pop tuple))
				      '(pop tuple))))
		   'tuple)
	      (GETTreeData rel)
	      ,(constant-equality-sig
	       (mapcar #'(lambda (x)(if (listp x) (car x) x))
		       compare)))
	   ; arity 0
	   `(= (the integer (first (GETTreeData rel))) 1))))

(defun convert-tree-to-hashtable
       (tree comp leaf-p
	&aux (ht (make-hash-table
			     :size (round (* 1.5 *maxtreelist*))
			     :test comp)))
  (declare (type list tree))
  (dolist (x (rest tree))
    (if leaf-p
	(setf (gethash x ht) t)
	(setf (gethash (first x) ht)
	      (rest x))))
  (setf (first tree) ht
	(rest tree) nil))

(defun treeadder
       (tuple tree compare-fns &optional return-added-p &aux subtree)
  (declare  (type list tuple  compare-fns))
  (cond ((integerp (first tree)) ; list representation
	 (cond
	   ((rest tuple)
	    (cond ((setf subtree (assoc (first tuple) (rest tree)
					:test (first compare-fns))) ;already stored
		   (treeadder (rest tuple) (rest subtree) (rest compare-fns) return-added-p))
		  (t  ; has to be inserted
		   (cond ((> (incf (the integer (first tree)))
			     (the integer *maxtreelist*))
			  (convert-tree-to-hashtable tree (first compare-fns) nil)
			  (treeadder tuple tree compare-fns return-added-p))
			 (t
			  (setf subtree (createtree))
			  (push (cons (car tuple) subtree)
				(rest tree))
			  (treeadder (rest tuple) subtree
				     (rest compare-fns) return-added-p))))))
	   (t ; lowest level
	    (cond ((member (first tuple) (rest tree) :test (first compare-fns)) nil)
		  ((> (incf (the integer (first tree)))
		      (the integer *maxtreelist*))
		   (convert-tree-to-hashtable tree (first compare-fns) t)
		   (setf (gethash (first tuple) (first tree)) t)
		   t)
		  (t (push (first tuple) (rest tree)) t)))))
	(t ;hash array representation
	 (if (rest tuple) ; upper level
	     (if (setf subtree (gethash (first tuple) (first tree)))
		 ; already stored
		 (treeadder (rest tuple) subtree (rest compare-fns)
			    return-added-p)
		 (progn (setf (gethash (first tuple) (first tree))
			      (setf subtree (createtree)))
			(treeadder (rest tuple) subtree (rest compare-fns)
				   return-added-p)))
	       ;lowest level
	     (if (and return-added-p (gethash (first tuple) (first tree)))
		 nil
		 (setf (gethash (first tuple) (first tree)) t))))))



(defun treedeleter (tuple tree compare-rels &aux subtree)
  (cond ((null (rest tuple)) ;; last slot
	 (cond ((integerp (first tree))
		(when (setf subtree
			    (member (first tuple) (rest tree) :test (first compare-rels)))
		  (if (zerop (decf (the integer (first tree))))
		      (progn (setf (rest tree) nil) t)
		      (progn (setf (rest tree)
				   (delete (first tuple) (rest tree) :count 1
					   :test (first compare-rels)))
			     nil))))
	       (t (remhash (first tuple) (first tree))
		  (zerop (hash-table-count (first tree))))))
	((integerp (first tree))
	 (cond ((setf subtree (assoc (first tuple) (rest tree)
				     :test (first compare-rels)))
		(when (treedeleter (rest tuple) (rest subtree)
				   (rest compare-rels))
		  ;; subtree is now empty, so remove it
		  (if (zerop (decf (the integer (first tree))))
		      (progn (setf (rest tree) nil) t)
		      (progn (setf (rest tree)
				   (delete subtree (rest tree) :count 1))
			     nil)))
		  )))
	((setf subtree (gethash (first tuple) (first tree)))
	 (when (treedeleter (rest tuple) subtree (rest compare-rels))
	   (remhash (first tuple) (first tree))
	   (zerop (hash-table-count (first tree)))))))

(defun treetester (tuple tree compare-rels)
  (declare (type list tuple compare-rels) )
  (cond ((null tuple) t) ;; leaf
	((integerp (first tree))
	 (if (rest tuple)
	     (let ((subtree (assoc (first tuple) (rest tree)
				   :test (first compare-rels))))
	       (and subtree (treetester (rest tuple) (rest subtree)
					(rest compare-rels))))
	     (member (first tuple) (rest tree) :test (first compare-rels))))
	(t (let ((subtree (gethash (first tuple) (first tree))))
		 (and subtree (treetester (rest tuple) subtree
					  (rest compare-rels)))))))

(defun treegenerator (subsetflg vars rel &rest args &aux stored 
		       (lng (length args)))
    (cond ((not (= lng (arity* rel)))
	   ;; this test should never fail -- we believe it is TOTALLY unnecessary
	   (error "wrong arity ~s" (cons rel args)))
	  ((not (setf stored (assoc lng treegeneratortable)))
	   (push (setf stored
		       (cons lng
			     (loop for iomask below (1- (ash 1 lng))
			     ;; in  IOMASK, 1 bits represent input slots 
                             ;; 0 bits represent output slots
			     ;; no generator requested for all inputs
				   collect (treegen lng iomask))))
		 treegeneratortable)))
    (values-list
      (loop with temp for gen in (rest stored) when
	    ; don't return any more general than needed; return those more
	    ; specific if SubsetFlg - sort of anti-MatchTemplate
	    (loop for tmp in (setf temp (second (assoc 'template gen)))
		  as a in args
		  always (or (eq tmp 'input) (member a vars)))
	    unless
	    (and (not subsetflg)
		 (loop for tmp in temp as a in args
		       thereis (and (eq tmp 'input) (member a vars))))
	    collect
	    (cons (list 'effort
	       	     (iftimes 50. ; careful - output's may have different compare's
			      (let ((args (loop for x in temp collect
						(if (eq x 'output)
						    (gensym "V") ;seems unnecessary
						    x))))
				(relationsize (remove 'input args) (cons rel args)))))
		  (subst (fix-tree-equiv rel temp)
			 '*tree-equiv-code-here*
			 gen)))))

(defun fix-tree-equiv (rel temp)
  (cons 'setf
	(loop for pos from 0 as tmp in temp when (eq tmp 'input) nconc
	      (let ((c (get-c-and-c rel pos))
		    (cmpvar (pack* 'cmp pos)))
		(if (listp c)
		    (let ((ivar (pack* 'input pos)))
		      (list cmpvar `#',(car c)
			     ivar (list (cadr c) ivar)))
		    (list cmpvar `#',c))))))


(defun treegen (arity iomask)
  (declare (type fixnum iomask))

  `((template ,(loop for i below arity
		     collect (if (logbitp i iomask) 'input 'output)))
    ; Effort computed above for each rel
    (initialstate
      ,(loop with input and comparison
	  for i below arity as pos from 0
	  when (logbitp i iomask)
	  do (setf input (pack* 'input pos)
		   comparison (pack* 'cmp pos))
	  and collect input into inputs
	  and collect comparison into comparisons
        finally
	(return
	 `(lambda (rel ,.inputs &aux ,.comparisons)
	    ,(when inputs '*tree-equiv-code-here*)
	    (treegen-common
	      rel ,arity ,iomask
	      ;; ,(treegen-output-gatherer arity iomask)

	      ;; the following list cannot be stack consed
	      ;; because pointers to tails are retained
	      (list ,. (mapcan #'list inputs comparisons )))))))))


#|
the shared tree generator works off a vector whose elements correspond
to generator ouput slots.  Each entry contains a list of the
form (gendata . following-inputs).  GENDATA is a data structure
which is used to:
  o  obtain the currently generated output, in the case of success
  o  produce the next potential output for the same output slot,
     given an unchanged set of preceding outputs

FOLLOWING-INPUTS is NIL if the following slot is an output slot.
Otherwise, it is a list whose CAR is the number of input slots that
follow this one (before the next output slot) and whose CDR is
a list of alternating input-value comparison-function for those slots.

Note that comparison functions are needed because the 
representatation of index trees is a union type.  It can be either:
o a lisp association list with a size (size . alist)
 , which does not carry its own equality function, or
o a hash table, which does carry and equality function.
This is a design tradeoff -- omitting the comparison fn
from the alist rep of an index tree  saves one pointer per tree,
at a cost of passing around the comparison functions for all
accessing code.  (If the trees carried their comparison fns with them,
then the comparison fns would only need to be passed around
with ADDing code, which is when the trees are built.)

Since we cannot know
until we pick up a particular index tree which form it will have, 
we cannot know which, if any, of the inputs will need a comparison
function.  The comparison function is one of the parameters passed
to NEXTTREE, which ignores it when the current tree is a hashtable.

One further complication is that the alist representation of index trees
is further optimized in the final position.  Instead of (size . alist),
we will find (size . members)

Gendata is an alist index-tree for any slot but a final slot.
(caar gendata) is the "currently proposed" output.
For a final slot it is simply a list of possible values.

|#

(defmacro treegen-gendata (cell) `(first ,cell))
(defmacro treegen-inputs (cell) `(rest ,cell))
(defmacro make-treegen-cell (gendata inputs)
  `(cons ,gendata ,inputs))

(declaim (inline purify-tree))
(defun purify-tree (l)
  (if (integerp (first l)) (rest l) (first l)))

(defun nexttree (data final-p value comparison)
  (if final-p
      (if (consp data)
	  (member value data :test comparison)
	  (gethash value data))
      (purify-tree
	(if (consp data)
	    (rest (assoc value data :test comparison))
	    (gethash value data)))))

(declaim (inline currently-proposed-output-final currently-proposed-output-non-final))
(defun currently-proposed-output-final
       (cell &aux (gendata (treegen-gendata cell)))
  (if (null (treegen-inputs cell))
      (first gendata)
      (caar gendata)))

(defun currently-proposed-output-non-final (cell)
  (caar (treegen-gendata cell)))

(defun check-inputs (tree inputs final-output &aux (count (pop inputs)))
  (dotimes (n count tree)
    (unless (setf tree
		  (nexttree tree
			 (and final-output (= n (1- count)))
			 (pop inputs) (pop inputs)))
      (return nil))))

(defmacro make-gendata (tree final-p)
   `(if (consp ,tree) 
	,tree ;; NOTE no gensym binding for tree
	(convert-to-gendata ,tree ,final-p)))
  
(defun convert-to-gendata (tree final-p)
  (if (consp tree)
      tree
      (let* ((l (make-list (hash-table-count tree)))
	     (ltail l))
	(maphash (if final-p
		     #'(lambda (key val) (declare (ignore val))
			 (setf (first ltail) key
			       ltail (rest ltail)))
		     #'(lambda (key val)
			 (setf (first ltail) (cons key val)
			       ltail (rest ltail))))
		 tree)
	l)))


(defconstant *min-output-gatherer-size* 10)
(defvar *treegen-output-gatherers* (make-array *min-output-gatherer-size*
					       :initial-element nil))
(defun enter-treegen-output-gatherer (nout)
  (when (>= nout (length *treegen-output-gatherers*))
    ;; grow it --- we always keep it a simple vector for
    ;; optimal access speed.
    (let ((new (make-array (+ nout 5) :initial-element nil)))
      (replace new *treegen-output-gatherers*)
      (setf *treegen-output-gatherers* new)))
  (setf (svref *treegen-output-gatherers* nout)
	(compile nil
		 `(lambda (vec)
		    (values nil
			    ,. (loop for i below nout
				     collect
				     `(,(if (= i (1- nout))
					    'currently-proposed-output-final
					    'currently-proposed-output-non-final)
				       (svref vec ,i))))))))

(defun treegen-common
       (rel arity iomask  inputs&comparisons)
  (treegen-common-from-data arity iomask
    inputs&comparisons (purify-tree (gettreedata rel))))

(defun treegen-common-from-data
       (arity iomask inputs&comparisons index-tree)
  (let ((position-index
	  (dotimes (i arity
		      (return-from treegen-common-from-data
			(let (notfirst)
			  #'(lambda () (prog1 notfirst
					      (setf notfirst t))))))
	    (unless index-tree
	      (return-from treegen-common-from-data #'(lambda () t)))
	    (if (logbitp i iomask) ;; leading input
		(setf index-tree
		      (nexttree index-tree 
				(= i (1- arity))
				(pop inputs&comparisons)
				(pop inputs&comparisons)))
		(return i)))))

    (flet ((count-inputs (&aux (count 0) (tail inputs&comparisons))
	     (loop do (incf position-index)
		   while (logbitp position-index iomask)
		   do (progn (incf count)
			     (setf inputs&comparisons
				   (cddr inputs&comparisons))))
	     (unless (zerop count) (cons count tail))))

      (let* ((nout (- arity (logcount iomask)))
	     (vec (make-array nout))
	     (outputn 0)
	     (results-fn (or (when
			       (or (< nout *min-output-gatherer-size*)
				   (< nout (length *treegen-output-gatherers*)))
			       (svref *treegen-output-gatherers* nout))
			     (enter-treegen-output-gatherer nout))))
	(declare (type fixnum outputn))
	(setf (svref vec 0)
	      (make-treegen-cell
		(make-gendata index-tree (= position-index (1- arity)))
		(count-inputs)))
	(loop while (< position-index arity)
	      do (setf (svref vec (incf outputn))
		       (make-treegen-cell nil (count-inputs))))

	(let ((first t)) 
	  #'(lambda () 
	      (multiple-value-prog1
		(if (treegen-internal vec first nout)
		  (funcall results-fn vec)
		  t)
		(setf first nil))))))))


(defun treegen-internal (vec first nout)
  (declare (type simple-vector vec) (type fixnum nout))
  (let* ((maxslot (1- nout))
	 (slot (if first
		   ;; first time
		   0
		   maxslot))
	 (cell (svref vec slot))
	 next-tree)
    (declare (type fixnum maxslot slot))
    (flet ((subtree-for-current (cell final-outp &aux (gendata (treegen-gendata cell)))
	    (cond ((null gendata) nil)
		  ((and  final-outp
		      (null (treegen-inputs cell)))
		   t) ;; final slot has no subtrees
		  (t (purify-tree (rest (first gendata))))))
	   (pulse-gendata (cell final-outp
				&aux (gendata (treegen-gendata cell)))
    	      ;; returns nil if exhausted
	      ;; otherwise, "pulses" the gendata entry of cell
              ;; and returns the next index tree
	      (when (rest gendata)
		(pop (treegen-gendata cell))
		(if (and final-outp (null (treegen-inputs cell)))
		    t
		    (purify-tree (rest (first (treegen-gendata cell))))))))
      (setf next-tree
	    (if first
		(subtree-for-current cell (= slot maxslot))
		;; get rid of value already produced
		(pulse-gendata cell t)))
      
      (loop 
	(if ;find an acceptable output
	  (and next-tree
	       (let ((inputs (treegen-inputs cell)))
		 (loop  (when (or (null inputs)
				  (setf next-tree
					(check-inputs next-tree inputs
						      (= slot maxslot))))
			  (return t))
			(unless
			  (setf next-tree (pulse-gendata cell (= slot maxslot)))
			  (return nil)))))
	  ;; success
	  (progn (incf slot)
		 (if (= slot nout)
		     (return T)
		     (setf cell (svref vec slot)
			   (treegen-gendata cell)
			     (make-gendata next-tree
					   (and (= slot maxslot)
						(null (treegen-inputs cell))))
			   next-tree (subtree-for-current cell
						(= slot maxslot)))))
	  ;; no more outputs
	  (if (zerop slot)
	      (return nil)
	      (progn (setf cell (svref vec (decf slot))
			   next-tree (pulse-gendata cell nil))
		     )))))))


#+ignore 
(defun treeprinter (tree depth)
  (or (numberp depth)
      (print (list 'depth
		   (setf depth 1.))))
  (cond ((= depth 1.)
	 (cond ((numberp (car tree))
		(cdr tree))
	       (t (let (ans)
		    (declare (special ans))
		    (maphash (function (lambda (x ignore)
					 (declare (ignore ignore))
					 (push x ans)))
			     (car tree))
		    ans ))))
	((numberp (car tree))
	 (loop for x in (cdr tree)
	       collect (cons (car x) (treeprinter (cdr x) (- depth 1)))))
	(t (let (ans)
	      ; wrong for commonlisp (declare (special ans depth))
	     (maphash #'(lambda (x y)
			  (push (cons x (treeprinter y (- depth 1))) ans))
		      (car tree))
	     ans ))))

