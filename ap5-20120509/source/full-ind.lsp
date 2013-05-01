;;; -*- Mode: Lisp; Package:AP5; Syntax:COMMON-LISP; Base:10 -*-

(in-package "AP5")

;;
;; ----------------------------------------------------------------
;; formerly completely indexed relations (AP3 relations, overkill relations)
;;
;; These relations maintain a hashtable for each slot.  In addition we
;; keep a list of all tuples and a count
;; Partial index relations are similar but do not keep all the tables.

;; note that (:multiple (partial-index 1 2) full-index) is NOT what
;; you expect - the full-index will be ignored !! 
;; also (this was a bug before) changing from (partial-index 1) to
;; full-index does not have the desired effect, cause the full-index-data
;; is only decached when you use the partial-index macro...
;; I think the answer here is not to use full-index at all, just partial.

(defun partial-index (name keys &rest slots &aux actual-slots
			   (arity (getf keys :arity))
			   (warnings (getf keys :warnings))
			   tmp)
  (declare (ignore name))
  (unless arity
    (when (setf tmp (or (getf keys :arity)(getf keys :equivs)))
	   (setf arity (length tmp))))
  (unless arity
    (error "Arity must be specified for partial index"))
  (unless (integerp arity)
    (error "Non-integer arity specified for partial index"))
  (dolist (x slots)
    (unless (integerp x) 
      (error "Non-integer slot number for partial index (~a)" x))
    (when  (>= x arity)
      (error "Slot number must be between 0 and ~d"
	     (- arity 1)))
    (if (member x actual-slots :test #'=)
	(push (list "Slot number ~d re-specified. Ignoring it." x) warnings)
	(pushnew x actual-slots :test #'=)))
  (unless actual-slots			; NO SLOTS SPECIFIED !!
    (push '("Partially indexed relation without any slot numbers! (= base)")
	  warnings))
  #+ignore 
  (if slots 
      (if (= (length slots) (getf keys :arity -1))
	  (warn "ALL slots specified to index. Easier to use full-index!")))
  `(:representation full-index
    :alsofns
    ((lambda (rel)
	 (if (indices-changed? rel ',slots) 
	     (rem-structure-property rel 'full-index-data)))
     ,.(getf keys :alsofns))
    :warnings ,warnings
    ,.keys))

(defun indices-changed? (rel pl)
  (not (equal (sort (remove-duplicates pl :test #'=) #'<)
	      (loop for x in 
		    (cdr (get-structure-property rel 'full-index-data))
		    as i from 0 
		    when x 
		    collect i))))

;;slot-numbers redefined in defrel where parameter-list is defined
(setf (symbol-function 'slot-numbers)
      #'(lambda (rel) (declare (ignore rel)) :none))

(defun get-full-index-data (rel &aux pl)
  ;; cannot initialize pl since this may be called from dodbupdates when
  ;; db read is illegal but when the property already exists
  (or (get-structure-property rel 'full-index-data)
      (put-structure-property rel
        (cons nil
	      (loop for x below (arity* rel) collect
		    (if (or (eq (setq pl (slot-numbers rel)) :none)
			    (member x pl :test #'=))
			(make-hash-table 
			  :test
			  (let ((compare (get-c-and-c rel x)))
			    (if (listp compare)
				(car compare) compare))))))
	'full-index-data)))

; format of data: list of arity+1 elements:
; first is a list of all tuples stored as in baserel,
; rest are hasharrays that associate elements at that position with lists:
; first element is # tuples, other elements are the tuples


(++ Implementation 'full-index)
(++ reladder 'full-index 'add-full-index)
(++ reldeleter 'full-index 'delete-full-index)
(++ reltester 'full-index 'test-full-index)
(++ RelGenerator 'full-index 'generate-full-index)

(defun test-full-index (rel &rest args &aux
			(compare (get-comparisons-and-canonicalizers rel)))
  (setq args (loop for x below (length args) collect (gensym "A")))
  `(lambda (rel &rest args)
     (let (data entry) ; symbolics compiler bug
       ,.(loop for i from 0 as c in compare when (listp c) collect
	       `(setf (nth ,i args) (,(cadr c) (nth ,i args))))
       (loop for x in (cdr (get-full-index-data rel)) as a in args do
	     (cond ((not x))  ;; not indexed by that slot
		   ((eq (setq entry (gethash a x empty)) empty)
		    ; not there
		    (setq data nil)
		    (return nil))
		   ((or (null data) (< (car entry) (car data)))
		    ; shorter list of tuples
		    (setq data entry))))
       (if data (fmemb3 args (cdr data) ,rel)
	   (fmemb3 args (car (get-full-index-data rel)) ,rel)))))

(defun add-full-index (rel &rest args &aux	
		       (compare (get-comparisons-and-canonicalizers rel)))
  (setf args (mapcar #'(lambda (x) (declare (ignore x)) (gensym "A")) args))
  `(lambda (rel &rest args)
     (let (data entry) ; compiler bug
       ,.(loop for i from 0 as c in compare when (listp c) collect
	       `(setf (nth ,i args) (,(cadr c) (nth ,i args))))
       (setf args (copy-list args)) ; this will become the tuple
       (loop for x in (cdr (setq data (get-full-index-data rel))) as a in args do
	     (cond ((not x))  ;; no hash table to update
		   ((eq (setq entry (gethash a x empty)) empty)
		    (setf (gethash a x) (list 1 args)))
		   (t (incf (car entry)) (push args (cdr entry)))))
       (push args (car data)))))

(defun delete-full-index (rel &rest args &aux
			  (compare (get-comparisons-and-canonicalizers rel)))
  (setf args (mapcar #'(lambda (x) (declare (ignore x)) (gensym "A")) args))
  `(lambda (rel &rest args)
     (let (data entry shortest) ; compiler bug
       ,.(loop for i from 0 as c in compare when (listp c) collect
	       `(setf (nth ,i args) (,(cadr c) (nth ,i args))))
       ; first we have to find the tuple - copy from test
       (loop for x in (cdr (setq data (get-full-index-data rel))) as a in args do
	     (cond ((not x))	;; no hash table to update
		   ((eq (setf entry (gethash a x empty)) empty)
		    ; not there
		    (setf shortest nil)
		    (return nil))
		   ((or (null shortest) (< (car entry) (car shortest)))
		    ; shorter list of tuples
		    (setf shortest entry))))
       (if shortest
	   (setf args (car (fmemb3 args (cdr shortest) ,rel))) ; get the exact (EQ) tuple
	   (setf args (car (fmemb3 args (car data) ,rel))))
       (setf (car data) (delete args (car data) :test #'eq :count 1))
       (loop for x in (cdr data) as a in args do
	     (cond ((not x))
		   ((eq (setq entry (gethash a x empty)) empty))
						; not supposed to happen
		   ((= 1 (car entry)) (remhash a x))
		   (t (decf (car entry))
		      (setf (cdr entry) (delete args (cdr entry) :test #'eq :count 1))))
	     ))))

(defun generate-full-index (ignore vars rel &rest args  &aux temp
				   slots
				   (cnc (get-comparisons-and-canonicalizers
					  rel)))
  (declare (ignore ignore vars))
  (setq slots (slot-numbers rel))
  (apply #'values
    `((initialstate
	(lambda (rel &aux state) ; compiler bug
	  (setq state (car (get-full-index-data rel)))
	  #'(lambda ()
	      (cond (state (apply #'values nil (pop state))) (t)))))
      (template ,(make-list (length args) :initial-element 'output))
      (effort ,(iftimes 3 (relationsize '(x) (cons rel (make-list (length args) :initial-element 'x))))))
    (loop for in-pos below (length args)
	  when (or (eq slots :none)
		   (member in-pos slots :test #'=))
	  collect
	  `((template ,(setq temp (loop for i below (length args) collect
					(cond ((eq i in-pos) 'input) (t 'output)))))
	    (effort ,(ifplus 20 (iftimes 3 (relationsize '(output) (cons rel temp)))))
	    (initialstate
	      (lambda (rel in &aux state)
		,.(cond ((listp (nth in-pos cnc))
			 `((setq in (,(cadr (nth in-pos cnc)) in)))))
		(setq state (cdr (gethash in (nth ,in-pos (cdr (get-full-index-data rel))))))
		#'(lambda (&aux tuple) ;compiler bug
		    (setq tuple (pop state))
		    (cond ((not tuple))
			  (t (values nil ,.(loop for i below (1- (length args)) collect
						 (cond ((eq i in-pos)
							'(progn (pop tuple) (pop tuple)))
						       (t '(pop tuple))))))))))))))
; the (progn pop pop) is admittedly suboptimal for the last one ...

(++ DefinedRelName 'FullIndexRelName
    '((name arity) s.t. (E (x) (and (RelationImplementation x 'full-index)
				    (RelationName x name)
				    (relationarity x arity)))))
(++ reldeleter (relationp 'fullindexrelname) 'namedrel-deleter)
(++ RelAdder (dbo relation FullIndexRelName) 'make-full-index-rel)

(defun make-full-index-rel (&rest ignore)
  (declare (ignore ignore))  
  '(lambda (ignore name arity)
     (declare (ignore ignore))
     (cond ((?? FullIndexRelName name arity)
	    (insist "supposed to add it" FullIndexRelName name arity))
	   (t (add-imparityname (make-dbobject) 'full-index arity name)))))


