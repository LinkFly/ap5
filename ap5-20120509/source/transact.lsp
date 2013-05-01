;-*- Mode:LISP; Package:AP5; Base:10.; Syntax:Common-Lisp -*-

(in-package "AP5")

(defvar true-matchnode)
(defvar indexdelta nil)

;;;; Contexts and Update records

(defstruct (tuple (:conc-name nil) ;:named
	   (:print-function printtuple))
	   tuprel 
	   tupargs
           tuptv)
;;; Tuple has a relation, a sequence of argument objects and a truth value
;;; which is either T, NIL, 'Inherit (which is not actually stored in Cx)

(defun printtuple (tuple stream depth)
  (declare (ignore depth))
  (format stream "~A~A~:A"  ;; :A prints NIL as ()
	  (ecase (tuptv tuple) ((t) "") ((nil) "~") (inherit "??"))
	  ;; ?? for inheriting
	  (relationnamep (tuprel tuple))
	  (tupargs tuple)))

(DefStruct (UpdateRec (:conc-name nil) ;:named
		      (:print-function printupdate))
  UpdTuple #+ignore UpdCx UpdReason UpdCode-set updcode-single
  #+ignore UpdCxEval UpdCheckers UpdTester)
;;; UpdateRecord has a tuple, context and justification (the format of which will 
;;; be further specified later but is so far):
;;; - an update expression: ++, --, Inherit
;;; - (DefinedUpdate <update expression> <source update>)

(defun printupdate (updaterec stream depth)
  (declare (ignore depth))
  (printtuple (updtuple updaterec) stream nil)
  #+ignore 
  (cond ((eq (updcx updaterec) *globalcx*)
	 (printtuple (updtuple updaterec) stream nil))
	(t (format stream "~S in ~S"
	  (UpdTuple UpdateRec)
	  (UpdCx UpdateRec)))))
;;;
;;; Macro is a fn to expand a defined update by doing more primitive updates
;;; UpdCode is a function to do the primitive update
;;; UpdCxEval is a function to find the explicit value in cx (T, NIL, Inherit)

; history and abortdata
(DefStruct (consistency-cycle-record (:conc-name nil) )
  direct directdelta indirect maintain again delta activations)
#+ignore ; moved to utils cause of using dbo
(defstruct (history-record (:conc-name nil) )
  originalupdates generation# consistency-cycles prev-gen#)

(defvar Generation# 0)
(defvar *atomic-id* 0)

;;; Contexts
(declaim (inline context-sensitive))
(defun context-sensitive (rel)
  (declare (ignore rel))
  nil
  #+ignore (cxvaluefn rel))
;;; formerly (assoc (implementationof rel) (getbasedata rel-cxsensitive)))


(declaim (inline equaltuple equal-canon-tuple))
(defun equaltuple (rel tup1 tup2)
  (funcall (tuple-comparison rel) tup1 tup2))

(defun equal-canon-tuple (rel tup1 tup2)
  (funcall (tuple-canon-comparison rel) tup1 tup2))

(defun tuple-comparison (rel)
  (or (get-structure-property rel 'comparetuple)
      (put-structure-property
	rel
	(compile-ap
	  `(lambda (tup1 tup2) (equal2 tup1 tup2 ,rel)))
	'comparetuple)))

(defun tuple-canon-comparison (rel)
  (or (get-structure-property rel 'comparecanontuple)
    (let (cnc)
      (tuple-comparison rel) ;get comparetuple cached
      (setf cnc (get-comparisons-and-canonicalizers rel))
      (put-structure-property rel
	   (if (some #'listp cnc)
		     (compile-ap
		       `(lambda (tup1 tup2) nil
				(and ,.(loop for c in cnc collect
					     (list (if (listp c) (car c) c)
						   '(pop tup1) '(pop tup2))))))
		     (get-structure-property rel 'comparetuple))
	   'comparecanontuple))))


(defun rel-comparisons (rel)
  (or (get-structure-property rel 'rel-comparerels)
      (put-structure-property
	rel
	(loop for c in (get-comparisons-and-canonicalizers rel)
	      collect (cond ((listp c) (car c)) (t c)))
	'rel-comparerels)))

(defvar |Output| "output place holder") ;; a real crock!!

(defun canonicalize-tuple (rel tuple &aux canonfn)
  (unless (setf canonfn (get-structure-property rel 'canonicalizetuple))
      (put-structure-property
	rel
	(setf canonfn
	      (let ((cnc (get-comparisons-and-canonicalizers rel)))
		(cond
		  ((some #'listp cnc)
		   (compile-ap
		     `(lambda (tuple)
			(list 
			  ,.(loop for cmp in cnc collect
				  (cond ((listp cmp)
					 `(cond ((eq (car tuple) |Output|)
						 (pop tuple))
						(t (,(cadr cmp) (pop tuple)))))
					(t '(pop tuple))))))))
		  (t #'identity))))
	'canonicalizetuple))
  (funcall canonfn tuple))

(defun test-in-delta (tv rel &rest args &aux entry)
  (when delta
    (if (setf entry (rest (assoc rel indexdelta)))
	(let ((tuple (canonicalize-tuple rel args))
	      shortest  this)
	  (loop for x in entry as y in tuple do
		(cond ((eq x (setf this (gethash y x x)))
		       ;; can't NIL suffice as the default here?
		       (return-from test-in-delta nil))
		      ((or (null shortest)
			   (< (first this) (first shortest)))
		       (setf shortest this))))
	  (loop with compfn = (tuple-canon-comparison rel)
		for u in (rest shortest)
		thereis (and (eq tv (tuptv (updtuple u)))
			     (funcall compfn tuple (tupargs (updtuple u))))))
	(let ((entries (rest (assoc rel delta))))
	  (when entries
	    (loop with compfn = (tuple-comparison rel)
		  for u in entries thereis
		  (and (eq tv (tuptv (updtuple u)))
		       (funcall compfn args (tupargs (updtuple u))))))))))
; Optimize large updates 11/25/86 17:10:30
; in addition to delta we introduce a special (global) var,
; indexeddelta, which represents the same data as delta but in
; another format:
; list of entries of form (rel index1 ... indexn) (get right tentry with assoc)
; where each index is a hasharray mapping canonicalized objects in that position
; to lists whose car is the length of the cdr, and whose cdr is a list of tuples
; we will only create entries for relations with lots of updates (>10?)
; one problem is when to create and update this data ... how about just for 
; consistency rules?


(defvar empty "nothing stored here")
(defun get-delta-tuples (rel tuple &aux entry)
  (cond ((and delta ; have to make sure that binding delta to nil prevents
	      ; us from looking in indexdelta
	      (setq entry (cdr (assoc rel indexdelta))))
	 (setq tuple (canonicalize-tuple rel tuple))
	 (let (shortest this)
	   (loop for x in entry as y in tuple do
		 (cond ((eq empty (setq this (gethash y x empty)))
			(return (setq shortest nil)))
		       ((or (null shortest) (< (car this) (car shortest)))
			(setq shortest this))))
	   (cdr shortest)))
	(t (cdr (assoc rel delta)))))

(defun get-delta-tuples-pat (rel args &aux entry canon)
  (cond ((null delta) nil) ; get rid of quick cases first
	((null args) (cdr (assoc rel delta)))
	((and (notevery #'(lambda (x) (eq x |Output|)) args)
	      (setq entry (cdr (assoc rel indexdelta))))
	 (setq canon (canonicalize-tuple rel args))
	 (let (shortest this)
	   (loop for x in entry as y in canon as a in args do
		 (cond ((eq a |Output|))
		       ((eq empty (setq this (gethash y x empty)))
			(return (setq shortest nil)))
		       ((or (null shortest) (< (car this) (car shortest)))
			(setq shortest this))))
	   (cdr shortest)))
	(t (cdr (assoc rel delta)))))

; this is supposed to be useful for atomicupdate advice
(defun map-updates (mapfn &key (rel :transition)
		    relpred tuplespec tuplepred (tv '(T NIL))
		    &allow-other-keys #+ignore cxpred)
  (declare (special |Direct | |Maintain |)
	   #+symbolics (sys:downward-funarg mapfn))
  ; mapfn is the function to apply to each matching update
  ; its arguments are (rel tuple tv)
  ; Matching updates are those that satisfy all of the tests supplied:
  ; rel is either a relation or list of relations or one of two keywords below
  ; relpred is a predicate of relations --
  ; if it returns T, tuples are of interest to mapfn
  ; tuplespec is a list of objects and :any's (trailing :any's assumed)
  ; tuplepred is a predicate of truthvalue, tuple
  ; tv is a list of truthvalues
  (check2states 'map-updates)
  (flet ((per-rel (r &aux d)
	   (cond ((and relpred (null (funcall relpred r))) nil)
		 ((setq d (assoc r delta))
		  (let (comparerels tup tval)
		    (loop for u in
			  (get-delta-tuples-pat (car d)
				(loop for s in tuplespec collect
				      (cond ((eq s :any) |Output|) (t s)))) do
			  ; compute this when we have to
			  (or comparerels
			      (setq comparerels
				    (or (loop for s in tuplespec as pos from 0 collect
					      (unless (eq s :any)	; worthwhile optimization?
						(get-comparison (car d) pos t)))
					t)))	; I guess for 0-ary rels?
			  (setq tup (tupargs (updtuple u)) tval (tuptv (updtuple u)))
			  (when (and (loop for arg in tup
					   as pat in tuplespec
					   as rel in comparerels always
					   (or (eq pat :any) (testrel rel arg pat)))
				     (or (null tuplepred) (funcall tuplepred tval tup))
				     (member tval tv)
				     #+ignore
				     (or (null cxpred)
					 (cond ((context-p cxpred)
						(eq cxpred (updcx u)))
					       (t (funcall cxpred (updcx u))))))
			    (funcall mapfn (car d) tup tval #+ignore (updcx u))))))
		 ; not in delta - if it's stored then there's nothing to do
		 ((and (dbobject-p r) (not (derivedrel r))))
 		 ; so now it must be derived - try to prove it didn't change
		 ((and (dbobject-p r)	; not a description
		       (not (might-have-changed r))))
		 ; otherwise we're in trouble (have to compute)
		 (t; I guess we just have to generate them
		  (let ((tuplespec tuplespec)
			(arity (cond ((dbobject-p r) (arity* r))
				     ((listp r) (length (car r))))))	; for description
		    (when (or (= (length tuplespec) arity)
			      (when (null tuplespec)
				(setq tuplespec (loop for i below arity collect :any))))
		      (loop for tval in tv do ;; inherit?
			    (dolist (tuple
				      (eval (find-changed-tuples r tuplespec tval)))
				  (when (or (null tuplepred) (funcall tuplepred tval tuple))
				  ;; cxpred, cx arg below
				   (funcall mapfn r tuple tval))))))))))
    (case rel
      ((:transition :Stored&NotMaintained)
       (mapc #'(lambda (x) (per-rel (first x))) |Direct |))
      (:stored
	(mapc #'(lambda (x) (per-rel (first x))) |Direct |)
	(mapc #'(lambda (x) (per-rel (first x))) |Maintain |))
      (otherwise
	(if (atom rel)
	    (per-rel rel)
	    (mapc #'per-rel rel))))))

; I don't see any better way ...
; this may be hard to extend to tv inherit
(defun find-changed-tuples (rel tuplespec tv &aux vars (n 0))
  (setq tuplespec (copy-list tuplespec)) ; in case user wants to reuse it
  (loop for x on tuplespec do
	(setf (car x) (cond ((eq (car x) :any) (car (push (pack* 'x (incf n)) vars)))
			    (t (kwote (car x))))))
  `(loop for ,(reverse vars) s.t.
	 (start ,(cond (tv `(,rel ,.tuplespec))
		       (t `(not (,rel ,.tuplespec)))))
	 collect (list ,.tuplespec)))



(defun explicitvaluein (rel arglist #+ignore cx &aux found)
  ;; what truthvalue is "stored" (if none then 'Inherit) for tuple in cx
  ;; doesn't look in global DB (except delta)
  ;; if the value is to be found in the global db this just returns 'inherit
  ;; second value used to say whether it came from delta (new) or not (old)
  ;; It was worthless, since a new inherit could cause either new or old
  ;; data to be inherited
  (when (eq |UpdateStatus | 'primitive)
    (cerror "Ignore the tuples found in delta.~%~
             This error does indicate a problem that must be corrected, however."
	     "acessing the database during a primitive update!")
    (return-from explicitvaluein 'inherit))
  (cond ((let ((entries (get-delta-tuples rel arglist)))
	   (when entries
	     (setf found
		   (let ((compfn (tuple-comparison rel)))
		     (find-if #'(lambda (x) (funcall compfn arglist x))
			      entries
			      :key #'(lambda (entry)
				       (tupargs (updtuple entry))))
		   #+ignore
		   (loop with compfn = (tuple-comparison rel)
			 for u in entries	; change format of delta
			 thereis (and		;(eql cx (updcx u))
						;(eql rel (tuprel (updtuple u)))
				   (funcall compfn arglist (tupargs (updtuple u)))
				   u))))))
	 (tuptv (updtuple found)))
	#+ignore 
	((context-sensitive rel)
	 (let ((currentcx cx)) (funcall (cxvaluefn rel) rel arglist)))
	#+ignore ; no contexts at the moment ...
	((setq found
	       (loop for known in (cxdata cx)
		     thereis (and (eql rel (tuprel known))
				  (equaltuple rel arglist (tupargs known))
				  known)))
	 (tuptv found))
	(t 'inherit)))

(defun valueincurrentcx (rel &rest args)
  (if delta (explicitvaluein rel args) 'inherit))


(defun tuplesofrelin (rel cx args &aux answer shadow compfn)
  ;; for use in generators
  ;; find all tuples (with TV) of rel afected by cx (inc. delta)
  (declare (ignore cx))
  (progn ;loop while cx do 
	;; becomes false when we get parent of global
	(progn
	  (loop for x in (get-delta-tuples-pat rel args) ;change format of delta
		; when (eql cx (updcx x))
		when (eql rel (tuprel (setq x (updtuple x))))
		; should always be T but x is reset and check is cheap
		unless (progn (unless compfn
				(setf compfn (tuple-comparison rel)))
			      (loop for a in answer
				    thereis (funcall compfn
					  (tupargs a) (tupargs x))))
		do (cond ((eq (tuptv x) 'inherit)
			  (push x shadow))
			 (t (push x answer))))
	  #+ignore
	  (loop for x in (cxdata cx)
		when (eql rel (tuprel x))
		unless (loop for a in answer
			     thereis (equaltuple rel (tupargs a) (tupargs x)))
		unless (loop for a in shadow
			     thereis (equaltuple rel (tupargs a) (tupargs x)))
		do (push x answer))
	  (setq shadow nil)
	  #+ignore (setq cx nil #+ignore (cxparent cx))))
  answer)

;;; these macros are introduced in order to improve readability after a
;;; (macroexpand-1 <form>)
#+ignore 
(defmacro cxsensitize-init (inputs template initializer rel)
  ;; we're getting a form to compute rel and internally we want the relation
  (setq rel (eval rel))
  `(let ((original ,initializer) pos neg)
     (cond
       ((or (assoc |Rel | delta)
	    #+ignore (not (eq currentcx *globalcx*)))
	(multiple-value-setq (pos neg)
	  (compute-pos-and-neg |Rel |
	       ,(cond ((not (member 'input template)) nil)
		  (t
		   `(#+symbolics global::let-closed
		     #+symbolics ,(mapcar #'(lambda (v) (list v v)) inputs)
		     #-symbolics progn
		     #'(lambda (args)
			(and ,.(loop for temp in template with inp = inputs  as i from 0
				   as element = 'args then (list 'cdr element)
				   when (eq temp 'input) collect
				   (get-test-function (get-comparison rel i t)
						      (pop inp)
						      (list 'car element))))))))
	       ,(cond ((not (member 'input template)) '(function tupargs))
		      (t `#'(lambda (tuple &aux (args (tupargs tuple)))
			      (list ,.(loop for temp in template
					  as element = 'args  then (list 'cdr element)
					  when (eq temp 'output)
					  collect (list 'car element))))))
	       ,.(let ((in inputs))
		   (loop for tem in template collect
			 (cond ((eq tem 'input) (pop in)) (t '|Output|))))))
	(cond ((or pos neg)
	       #+symbolics  ;; dynamic closures save time/space in infrequent branches
	       (global::let-closed ((pos pos) (neg neg) (original original))
		  #'(lambda (&rest ignore) (declare (ignore ignore))
			    ,(cxsensitize-pulse template rel)))
	       #-symbolics
	       #'(lambda (&rest ignore) (declare (ignore ignore))
			 ,(cxsensitize-pulse template rel)))
	      (t original)))
       (t original))))

(defun compute-pos-and-neg (rel filter tuple-components &rest args)
  #+symbolics (declare (sys:downward-funarg filter tuple-components))
  (when (eq |UpdateStatus | 'primitive)
    (cerror "Ignore the tuples found in delta.~%~
             This error does indicate a problem that must be corrected, however."
	     "accessing the database during a primitive update!")
    (return-from compute-pos-and-neg (values nil nil)))
  (loop with outputs and pos and neg for tuple in (tuplesofrelin rel currentcx args)
       when (or (null filter) (funcall filter (tupargs tuple)))
       do (setq outputs (funcall tuple-components tuple))
	  (cond ((tuptv tuple) (push outputs pos)) (t (push outputs neg)))
	  finally (return (values pos neg))))

#+ignore 
(defun cxsensitize-pulse (template rel)
  `(cond (pos
	  ; since we now filter out noops, elements of pos can
	  ; never be generated by original, so they need not be stored
	  #+ignore
	   ((psetf neg pos (cdr pos) neg  pos (cdr pos))
	    ;;; REUSE the cons cell that is POS
	    )
	    (apply 'values nil (pop pos)))
	   (t ; (setq |State | (caddr |MyState |))
	      ; filter the context data from the global generator
	      (get-next-inneranswer original neg
		  #'(lambda (cxtuple next)
		      (and ,. (loop for temp in template as i from 0
			          when (eq temp 'output) collect
				  (get-test-function (get-comparison rel i t)
						     '(pop cxtuple)
						     '(pop next)))))))))

(defun get-next-inneranswer (original neg filter)
  #+symbolics (declare (sys:downward-funarg filter original))
  #+ignore
  (loop with inneranswer
	when (car (setq inneranswer (multiple-value-list (funcall original))))
	return t   ; global generator is exhausted
	when (let ((next (cdr inneranswer)))
	      (loop for cxtuple in neg never (funcall filter cxtuple next)))
	return (values-list inneranswer))

  (loop (multiple-value-lambda-bind (&rest inneranswer)
	  (funcall original)
	  (when (car inneranswer)	; global generator is exhausted
	    (return-from get-next-inneranswer t))
	  (unless (some #'(lambda (cxtuple)
			    (funcall filter cxtuple (cdr inneranswer)))
			neg)
	    (return-from  get-next-inneranswer
	      (values-list inneranswer))))))

#+ignore 
(defun cxsensitize (subgen rel &aux
		    (gen (sgen subgen))
		    (temp (cadr (assoc 'template gen))) 
		    (args (loop for tmp in temp collect (gensym "A")))
		    (inputs (loop for a in args as tmp in temp
				  when (eq tmp 'input) collect a))
		    newinit)
    ;; make another subgen (with slightly different initializer and pulser of gen)
    ;; to generate x s.t. (R x y) in cx:
    ;; initializer must get (TuplesOfRelIn <rel> currentcx),
    ;;   and filter out those which don't match y (inputs).  (result in xx)
    ;;   InitialState is (list <negatives of xx> <positives of xx>
    ;;                         <cx-independent initialstate>)
    ;; pulser must see if (cadr state) - if so, move an element to (car state) and
    ;;   return it, else use initial pulser, but filter out results in (car state)
    (setq newinit `(lambda (|Rel | ,@inputs)
		     (cxsensitize-init ,inputs ,temp
				       ,(expand-initializer gen (wff subgen)
							     (cons '|Rel | inputs))
				       (theap5relation ,(relationnamep rel))
				       #+ignore (memo (relationp ',(relationnamep rel))))))
    (setq subgen (copy-subsetgen subgen))
    ;;alter-subsetgen
    (setf (sgen subgen)
	  (setq gen (mapcar #'(lambda (x) (copy-seq x))
			    (sgen subgen))))
    ;; two level copy - ((prop val) ...)
    (rplaca (cdr (assoc 'initialstate gen)) newinit)
    subgen)

;;;; utility fns to help with macro expansion

(defmacro selector (key comparefn &rest clauses)
  `(let ((key ,key))
     (cond
       ,@(loop for c in clauses collect
	       (cons (let ((l (car c)))
		       (cond ((eq l t))
			     ((ilistp l) `(member key ',l
						  :test (function ,comparefn)))
			     (t `(,comparefn key ',l))))
		     (cdr c))))))
(eval-when (:compile-toplevel :load-toplevel :execute)
 (defun next-keyword-form (tail &rest names)
  (loop for name in names when (symbolname name (car tail)) return
	(values name
		(ldiff (cdr tail)
		       (setq tail
			     (loop for x on (cdr tail) thereis
				   (and (symbolp (car x))
					(loop for n in names thereis
					      (symbolname n (car x)))
					x))))
		tail))))


#|           ABORT processing using CL Condition system

Numerous problems can prevent the successful termination of an ATOMIC
transaction.  Some of these may be intended, such as consistency rule
violations, and will be dealt with by an application.  Others are more
likely to indicate errors in the application code, in "library" code
being used by an application, or even errors in AP5 system code.

All these situations are dealt with using CL's condition signalling and
handling capabilities.  When an atomic transaction fails, a condition of
type ATOMIC-ABORT (or a subtype thereof) is signalled.  The fields of
ATOMIC-ABORT are:
TAG -- a symbol.  Accessed with ATOMIC-ABORT-TAG.  Intended for use by
       application initiated aborts.  See the function ABORT.
DESCRIPTION --  a string.  A format string which will be applied to 
       the contents of the ABORTDATA field to report the
       condition.  Subtypes of ATOMIC-ABORT may report more than this.
ABORTDATA -- a list.  The contents serve as the arguments for the format string
       in the DESCRIPTION field.  May contain additional values not consumed
       by that string.  AP5 places no further interpretation on this data.

predefined SUBTYPES of ATOMIC-ABORT signalled by the AP5 run-time system:
<the meaning and additional fields of these must be documented>
    CONSISTENCY-VIOLATION
        RULES-DO-ONLY-NOOPS
        UNFIXED-CONSISTENCY-VIOLATION
    ADDCHECKER
    BAD-DEFINITION
    BAD-ENFORCEMENT-LEVEL
    BAD-SUBREL
    CANNOT-TRIGGER
    CHANGE-RULE-TRIGGER
    CHANGE-RULE-ENFORCEMENT
    CONTRADICTORY-UPDATES
    INSIST
    TYPED-VAR-IN-CODEDEFN
    UNDEFINED-UPDATE
    UNKNOWN-RELATION
    UPDATE-MAINTAIN

==========================
ABORT(condition &optional description &rest data)
This function may be called by an application to explicitly abort
an atomic transaction while:
  gathering the initial proposed update
  from a consistency repair rule
  from code that translates updates to derived relations
If called elsewhere, whether within an atomic or not, an ERROR is
signalled (but not an ATOMIC-ABORT).

If condition is a condition object it is signalled; description and
data should not be provided.

If condition is a symbol, and is the name of a subtype of
ATOMIC-ABORT, a condition of the named subtype is signalled, with
description and data filling the DESCRIPTION and ABORTDATA fields.

If condition is any other symbol, a condition of type ATOMIC-ABORT is
signalled, with description and data filling the DESCRIPTION and
ABORTDATA fields.  The symbol is stored in the TAG field.

========================

ATOMIC

The ifabort clause(s) of the ATOMIC macro provides a means for the
programmer to scope an ATOMIC-ABORT handler around an atomic that
excludes any atomics that may be executed as a result of triggered
automation rules.  The code in the ifabort clause(s) may use the
variable ABORT-CONDTION, which will be bound to the signalled
condition --- an instance of ATOMIC-ABORT.

            NEW ABORT PROCESSING in AP5

When AP5 was implemented Common Lisp did not yet have exception
handling capabilities.  It had only an exception signalling function,
ERROR, with each vendor supplying its own additional facilities for
signalling and and handling exceptions.

Of the exceptions signalled by ap5, the kind an application is most
likely to want to handle is the ABORT from an atomic transaction.
That capability was given to the application programmer by providing
an optional IFABORT clause in the syntax of the ATOMIC macro.
Implemented using the exception handling extensions of each vendor,
this clause was invoked if the transaction to which it was attached
aborted without commiting the change to the database.  The AP5
run-time system will abort transactions in a variety of situations.
Applications are themselves allowed to abort transactions in some
situations.

The ifabort clause had access to a characterization of the reason for
the failure in the form of a list (accessible from an advertised
variable) which, at least for the exceptions signalled by AP5,
included a symbol that "classified" the problem, a string that
described it, and some other data that varied with the classification.
If an atomic aborted and there was no ifabort clause provided, the
lisp ERROR mechanism for signalling exceptions was invoked, which
would cause the program to enter the debugger unless some general
error handler caught the exception.

It is now the case that Common Lisp has a sophisticated exception
signalling and handling standard, which has been implemented by all
major vendors.  (In most cases the standard interface functions and
macros have been put into some package other than LISP; but otherwise
they seem to conform to the published standard.)  It is now possible
to integrate AP5 exception signalling and handling with this standard.

This integration enables cleanup of some internal code in AP5, but
this is rather minor and not programmer visible.  There are four
significant aspects from the programmers' standpoint:

[1] Atomic aborts can be handled in more ways than were previously
possible.  In addition to the IFABORT clause, ordinary exception
handlers can be scoped over an entire atomic (including triggered
automation rules) or over program segments that may execute many
atomic transactions.  There is an advertised (though very flat)
hierarchy of types of exceptions, which applications may extend if
they perform explicit aborts.

[2] Reporting of atomic failures is encapsulated in the condition
reporting mechanism.  In particular, no report will be printed
directly by AP5.  In the previous implementation, if an exception was
handled by some means other than an ifabort clause, some of the error
reporting output would have been done anyway.

[3] The data that is provided to an ifabort clause to characterize the
reason for the abort is slightly different than it was, although it
contains the same information.  (in my proposal it is simply the
condition object that was signalled.)  It is my belief that very few
programs that used ifabort clauses actually inspected this data.  If I
am wrong, we can make the old form of the data available as before as
well as making the new form available.

[4] The proposal does not necessitate recompilation of any AP5
application code.

|#

(defun report-atomic-abort (condition stream)
  (apply #'format stream
   (atomic-abort-description condition)
   (atomic-abort-abortdata condition)))

(define-condition atomic-abort (error)
  ((tag #-lucid :accessor #-lucid atomic-abort-tag
	#-lucid :initarg #-lucid :tag)
   (description #-lucid :initform #-lucid ""
		#-lucid :type #-lucid string
		#-lucid :accessor #-lucid atomic-abort-description
		#-lucid :initarg #-lucid :description)
   (abortdata #-lucid :initform #-lucid nil
	      #-lucid :accessor #-lucid atomic-abort-abortdata
	      #-lucid :initarg #-lucid :abortdata))
  (:documentation "signalled by a failed atomic transaction")
  (:report report-atomic-abort))

(defun report-consistency-violation (condition stream)
  (report-consistency-violations
   (consistency-violation-triggers condition) stream)
  (fresh-line stream)
  (report-atomic-abort condition stream))

(define-condition consistency-violation (atomic-abort)
  ((triggers #-lucid :initform #-lucid nil #-lucid :type #-lucid list
	     #-lucid :accessor #-lucid consistency-violation-triggers
	     #-lucid :initarg  #-lucid :triggers))
  (:report report-consistency-violation))
;;transactions
(define-condition rules-do-only-noops (consistency-violation) ())
(define-condition unfixed-consistency-violation (consistency-violation) ())
(define-condition insist (atomic-abort) ())
(define-condition update-maintain (atomic-abort) ())
(define-condition contradictory-updates (atomic-abort) ())
(define-condition undefined-update (atomic-abort) ())

;; misc-rules
(define-condition change-rule-trigger (atomic-abort) ())
(define-condition change-rule-enforcement (atomic-abort) ())
;; misc-rules, relations
(define-condition bad-definition (atomic-abort) ())
;; relations
(define-condition typed-var-in-codedefn (atomic-abort) ())
;; ruledeclare
(define-condition cannot-trigger (atomic-abort) ())
(define-condition bad-enforcement-level (atomic-abort) ())
;; stored-place
(define-condition addchecker (atomic-abort) ())
;; subtyperules
(define-condition bad-subrel (atomic-abort) ())
;; types
(define-condition unknown-relation (atomic-abort) ())

(defvar *report-abort* 'error)

(defvar-resettable *automation-queue* nil)

(defvar ifabort-supplied nil)
(defvar ifnormal-supplied nil)

(defmacro-displace Atomic (&rest given-body &aux atomic-body foo
		 ifabort  ifabort-supplied
		 ifnormal ifnormal-supplied atomic-tail)
  (declare (ignorable foo))
  (setq given-body (substitute '(do-subatomic) 'reveal given-body))
  (multiple-value-setq (foo atomic-body atomic-tail)
    (next-keyword-form (cons 'atomic given-body)
		       "atomic" "ifabort" "ifnormal"))
  (loop while atomic-tail do
	(multiple-value-bind (which code tail)
	    (next-keyword-form atomic-tail "ifabort" "ifnormal")
	  (setq atomic-tail tail)
	  (when which
	    (selector which string-equal
		      ("ifabort" (setq ifabort code ifabort-supplied t))
		      ("ifnormal" (setq ifnormal code ifnormal-supplied t)))))) 
  #+ignore
  `(atomic1 #'(lambda nil ,@ atomic-body)
	    ,ifabort-supplied
	    ,ifnormal-supplied
	    #'(lambda nil ,@ ifabort)
	    #'(lambda nil ,@ ifnormal))
  ; hope this works on symbolics
  `(atomic1-conditioned #'(lambda nil ,@ atomic-body)
	    ,(when ifabort-supplied `#'(lambda nil ,@ ifabort))
	    ,(when ifnormal-supplied `#'(lambda nil ,@ ifnormal))))

#+ignore ; previous version
(defmacro-displace Atomic (&rest given-body &aux atomic-body foo
		 (ifabort '((funcall *report-abort* abortdata)))  ifabort-supplied
		 (ifnormal '((values-list abortdata))) ifnormal-supplied atomic-tail)
  #+lucid (declare (ignore foo))
  (setq given-body (substitute '(do-subatomic) 'reveal given-body))
  (multiple-value-setq (foo atomic-body atomic-tail)
    (next-keyword-form (cons 'atomic given-body)
		       "atomic" "ifabort" "ifnormal"))
  (loop while atomic-tail do
	(multiple-value-bind (which code tail)
	    (next-keyword-form atomic-tail "ifabort" "ifnormal")
	  (setq atomic-tail tail)
	  (when which
	    (selector which string-equal
		      ("ifabort" (setq ifabort code ifabort-supplied t))
		      ("ifnormal" (setq ifnormal code ifnormal-supplied t)))))) 
  `(atomic1 #'(lambda nil ,@ atomic-body)
	    ,ifabort-supplied
	    ,ifnormal-supplied
	    #'(lambda nil ,@ ifabort)
	    #'(lambda nil ,@ ifnormal)))

(defvar *abort-fns*)
(defvar *normal-fns*)
(defun after-atomic-abort (fn)
  (case |UpdateStatus |
     ; a lot faster when the common case is first!
     ((consistency maintain definition atomic trigger) (push fn *abort-fns*))
     ((nil primitive checking report-inconsistency every-transition-advice
	   automationgenerating nonatomic-definition transparent)
      (error "Illegal context in which to enqueue a function for after an atomic"))
     (t (error "Unknown UpdateStatus -- ~s"  |UpdateStatus |))))
(defun after-atomic-normal (fn)
  (case |UpdateStatus |
     ; a lot faster when the common case is first!
     ((consistency maintain definition atomic trigger) (push fn *normal-fns*))
     ((nil primitive checking report-inconsistency every-transition-advice
	   automationgenerating nonatomic-definition transparent)
      (error "Illegal context in which to enqueue a function for after an atomic"))
     (t (error "Unknown UpdateStatus -- ~s"  |UpdateStatus |))))

(defvar-resettable block-undo nil) ; means that we're in a non-undoable transition

(defun block-undo ()
  (when (intransaction)
    (error "trying to do something in a transaction that is not undoable!"))
  (case |UpdateStatus |
     ; a lot faster when the common case is first!
     ((consistency maintain definition atomic trigger) (setf block-undo t))
     ((nil primitive checking report-inconsistency every-transition-advice
	   automationgenerating nonatomic-definition transparent)
      (error "Illegal context in which to enqueue a function for after an atomic"))
     (t (error "Unknown UpdateStatus -- ~s"  |UpdateStatus |))))

#+ignore ; old version
(defun atomic1 (body ifabort-supplied ifnormal-supplied ifabort ifnormal)
  (cond ((inatomic)
	 (when ifabort-supplied (report-nested-abort-handler "ifabort"))
	 (when ifnormal-supplied (report-nested-abort-handler "ifnormal"))
	 (funcall body))
	(t (let (abortdata ok recover
		   ;(initial-automation-queue *automation-queue*)
		   *automation-queue*)
	       (loop
		 (let (*abort-fns* *normal-fns*)
		   (unwind-protect
		       (catch 'atomic-retry
			 (with-unnamed-restart
			   ("Back out of Atomic and prepare to retry")
			   (setf *automation-queue* nil
				 abortdata (multiple-value-list
					     (atomic3
					       (if recover #'recover-atomic body))))
			   (when (eq (car abortdata) '|Abort |)
			     (setf abortdata (copy-list (cdr abortdata)) ok :abort)
			     (mapc #'funcall *abort-fns*)
			     (setf *abort-fns* nil)
			     (return-from atomic1 (funcall ifabort)))
			   (setf ok t)))
		     (progn (mapc #'funcall (if (eq ok t) *normal-fns* *abort-fns*))
			    ; second case covers both throw and abort - abort is noop
			    (setf *abort-fns* nil *normal-fns* nil)
			    ;; in case we are taking the restart path
			    )))
		 (when ok ;; did not abort or throw to ATOMIC-RETRY
		   (doautomationrulesNew)
		   (return-from atomic1 (funcall ifnormal)))
		 ;; if control reaches this point, the CATCH has trapped a throw 
		 ;; or the restart has been activated

		 ;;DON at this point you can check browse-please
		 (cerror "Retry executing the Atomic operation~
                         ~:[~;~&possibly without reevaluating the code in the atomic~]"
			 "Prepared to retry the Atomic operation"
			 (and abortdata
			      (get-structure-property
				(car (last abortdata)) '|InAtomicUpdate|)))
		 (setf recover
		       (and abortdata (null *abort-fns*) (null *normal-fns*)
			    (get-structure-property (car (last abortdata)) '|InAtomicUpdate|)
			    (y-or-n-p
			      "~&The code inside the atomic had finished so ~
                             ~&it's possible to just start with the updates ~
                             ~&proposed by that code before (not reexecute it). ~
                             ~&Is this what you want to do? "))))))))

(defvar abort-condition)

#|
 outline of atomic1-conditioned
(defun atomic1-conditioned (body ifabort ifnormal)
  (cond
   ((inatomic) ..)
   (t (let (abortdata ok recover *abort-fns* *normal-fns* *automation-queue*)
	(loop
	  (unwind-protect
	    (flet ((atomic1guts () 
                     ;calls ATOMIC3 supporting retry
		     ;reports ABORTs
		     ))
		  (if ifabort
		      (handler-bind ...
			(atomic1guts))
		    (atomic1guts)))
	      (progn (mapc #'funcall (if (eq ok t) *normal-fns* *abort-fns*))

		     ))
	  (when (eq ok t) ;; did not abort or throw to ATOMIC-RETRY
	    (doautomationrulesNew)
	    (return-from atomic1-conditioned
	      (if ifnormal
		  (funcall ifnormal)
		(values-list abortdata))))
	 ;; if control reaches this point, the CATCH has trapped a 
	 ;; throw or the restart has been activated
	  ...)))))
|#

(defun atomic1-conditioned (body ifabort ifnormal)
  (cond
   ((inatomic)
    (flet ((report-nested-abort-handler (type)
	     (warn
	      "Executing a nested atomic with an explicit ~A~
                     ~& -- see the AP5 manual~%" type)))
      (when ifabort (report-nested-abort-handler "ifabort"))
      (when ifnormal (report-nested-abort-handler "ifnormal")))
    (funcall body))
   (t (let (abortdata ok recover *abort-fns* *normal-fns*
	;(initial-automation-queue *automation-queue*)
	    *automation-queue*)
	(loop
	  (unwind-protect
	    (flet ((atomic1guts ()
		     (catch 'atomic-retry
		       (with-unnamed-restart
			("Back out of Atomic and prepare to retry")
			(setf *automation-queue* nil
			      abortdata
			      (multiple-value-list
			       (atomic3
				(if recover #'recover-atomic body))))
			    
			(when (eq (car abortdata) '|Abort |)
			      (setf abortdata (cadr abortdata) ok :abort)
			      (mapc #'funcall *abort-fns*)
			      (setf *abort-fns* nil)
			      (let (|Updates | |Requirements | EXPLICIT-MI
				    ORIGINALUPDATES DELTA
				    |Again | AGAINTREES |Maintain | |Direct |
				    DIRECTTREES OLD-DIRECT
				    INDEXDELTA *automation-queue*)
				(declare (special |Updates | |Requirements |
					  EXPLICIT-MI ORIGINALUPDATES DELTA
					  |Again | AGAINTREES |Maintain |
					  |Direct | DIRECTTREES OLD-DIRECT
					  INDEXDELTA *automation-queue*))
      ;;; the let bindings are just to compensate for the bindings still
      ;;; visible from atomics compiled when the *outer-atomic-state-vars*
      ;;; were scoped to widely.
				(setf abortdata
				      (multiple-value-list
				      (funcall *report-abort*
					       #+no-conditions "~A"
					       abortdata)))))
			(setf ok t)))))
	          (setf *abort-fns* nil *normal-fns* nil)
		  (if ifabort
		      #+no-conditions
		      (let ((*report-abort*
			     #'(lambda (&rest rest)
				 (declare (ignore rest))
				 (throw 'do-ifabort-code '|do abort code|))))
			(let ((result (catch 'do-ifabort-code (atomic1guts))))
			  (if (eq result '|do abort code|)
			      (let ((*abort-condition* abortdata))
				(return-from atomic1-conditioned
					     (funcall ifabort)))
			    result)))
		      #-no-conditions		      
		      (handler-bind
			  ((atomic-abort
			    #'(lambda (c) (declare (ignore c))
				;; lucid compiler complains anyway!!
				 (return-from
				     atomic1-conditioned
				   (let ((*abort-condition* abortdata))
				     (funcall ifabort))))))
			(atomic1guts))
		    (atomic1guts)))
	      (progn (mapc #'funcall (if (eq ok t) *normal-fns* *abort-fns*))
			; second case covers both throw and abort - abort is noop
		     (setf *abort-fns* nil *normal-fns* nil)
			;; in case we are taking the restart path
		     ))
	  (when (eq ok t) ;; did not abort or throw to ATOMIC-RETRY
	    (incf *atomic-id*)
	    (doautomationrulesNew)
	    (return-from atomic1-conditioned
	      (if ifnormal
		  (funcall ifnormal)
		(values-list abortdata))))


	  ;; if control reaches this point, the CATCH has trapped a throw 
	  ;; or the restart has been activated

	  ;;DON at this point you can check browse-please
	  (flet ((his (aa) (first (last (atomic-abort-abortdata aa)))))
		(cerror "Retry executing the Atomic operation~
                  ~:[~;~&possibly without reevaluating the code in the atomic~]"
		  "Prepared to retry the Atomic operation"
		  (and abortdata
		       (get-structure-property (his abortdata)
					       '|InAtomicUpdate|)))
	  (setf recover
	    (and abortdata (null *abort-fns*) (null *normal-fns*)
		 (get-structure-property (his abortdata)  '|InAtomicUpdate|)
		 (y-or-n-p
		      "~&The code inside the atomic had finished so ~
                       ~&it's possible to just start with the updates ~
                       ~&proposed by that code before (not reexecute it). ~
                       ~&Is this what you want to do? ")))))))))



#+ignore ; previous version
(defun report-abort (abortdata)
    (let (|Updates | |Requirements | EXPLICIT-MI ORIGINALUPDATES DELTA
	  |Again | AGAINTREES |Maintain | |Direct | DIRECTTREES OLD-DIRECT
	  INDEXDELTA *automation-queue*)
      (declare (special |Updates | |Requirements | EXPLICIT-MI ORIGINALUPDATES DELTA
	  |Again | AGAINTREES |Maintain | |Direct | DIRECTTREES OLD-DIRECT
	  INDEXDELTA *automation-queue*))
      ;;; the let bindings are just to compensate for the bindings still
      ;;; visible from atomics compiled when the *outer-atomic-state-vars*
      ;;; were scoped to widely.

      (apply #'format *error-output* (cdr abortdata))
      (abort-call-error)))



#+ignore ; previous version
(defun abort-call-error ()
  (error "More data (possibly MUCH more!) can be found in ap5::abortdata"))



(defun recover-atomic (&aux (event (first (last (atomic-abort-abortdata abortdata))))
			    (in-recover-atomic t)
			    reqs cc)
  (declare (special in-recover-atomic))
  (check-generation# event)
  (setf |Updates | (originalupdates event))
  (when (setf cc (consistency-cycles event))
    (when (y-or-n-p
	    "~&The aborted atomic had completed ~A consistency cycle~P.~
             ~&Start with the set of updates computed by the last cycle? "
	    (length cc) (length cc))
      (setf |Updates |
	    (loop for x in (direct (car cc)) append (cdr x)))))
  (when (setf reqs (get-structure-property event 'requirements))
    (when (y-or-n-p
	    "~&The aborted atomic had done ~A insist~P.~
             ~&Continue to enforce? " (length reqs) (length reqs))
      (setf |Requirements | reqs)))
  (cerror "try to do the atomic"
	  "~&You may now examine the updates with (browse-atomic),~
           ~&add new updates with ++ and --, and retract updates~
           ~&with (Retract-Update ...)"))

(defun check-generation# (hist-rec &aux prev#)
  (when (history-record-p hist-rec)
    ;(setq gen# (generation# hist-rec))
    (setq prev# (or (prev-gen# hist-rec) -1))
    (loop for h in global-history do
	  (cond ((= (generation# h) prev#)
		 (when (get-structure-property h 'unrecorded-history-follows)
		   (cerror "continue" "unrecorded events have occurred since this event"))
		 (return-from check-generation# t))
		((< (generation# h) prev#)
		 (cerror "continue" "current state appears earlier than this event")
		 (return-from check-generation# nil))
		((and (> (generation# h) prev#)
		      (delta (car (consistency-cycles h))))
		 (cerror "continue" "current state has changed since this event")
		 (return-from check-generation# nil))))
    (cerror "continue" "not enough history saved to place this event")))

;; I'll put that recovery stuff in tools ...


(defvar indirect-computed)
(defun atomic3 (body-function)
  #+symbolics (declare (sys:downward-funarg body-function))
  (let (|Updates | |Requirements | EXPLICIT-MI ORIGINALUPDATES DELTA
	|Again | AGAINTREES |Maintain | |Direct | DIRECTTREES
	OLD-DIRECT INDEXDELTA indirect-computed block-undo)
    (declare (special |Updates | |Requirements | EXPLICIT-MI ORIGINALUPDATES
		      DELTA |Again | AGAINTREES |Maintain | |Direct |
		      DIRECTTREES OLD-DIRECT INDEXDELTA indirect-computed))
    (withwriteaccess
      (multiple-value-call #'AtomicGuts
			   (catch '|OuterAtomic |
			     (let ((|UpdateStatus | 'Atomic))
			       (funcall body-function)))))))

#|
   By throwing to the tag ATOMIC-RETRY, a program can reach a breakpoint
   on the stack OUTSIDE the atomic, from which it may retry the entire
   atomic transaction.  It is ok for this throw to occur from inside the
   atomic body or from a repair rule during the consistency cycle.
   The catch does NOT encompass the execution of automation rules, but
   does (currently) include the computation of the queue elements
   (including the execution of any automationgenerating code), as well as the
   running of entries in *advice-for-every-transition*.
   It also encompasses the execution of reladders and reldeleters, but
   they should NEVER throw to this tag (or any other tag outside their
   own body.)  The real intent is only to provide a safe backout point
   for problems encountered in the applications atomic body or in
   consistency repair rules.  Under the current implementation (12/87)
   it is also safe to back out of certain other code, but it is not important
   that the implementation continue to support this.  By SAFE I mean
   that NO changes have occurred in the database or the history.

 For a given implementation of AP5, it is desirable to cause the error handler
   to offer a continuation option for throwing to this tag when an error 
   occurs inside an atomic (except when inside dodbupdates).
|#

(defun report-nested-abort-handler (type)
       (warn ;;format *trace-output*
	"Executing a nested atomic with an explicit ~A~
         ~& -- see the AP5 manual~%" type))


(defun AtomicGuts (&rest abdata)
  (declare (special originalupdates))
  (cond ((and (null |UpdateStatus |)
	      (not (eq (car abdata) '|Abort |))	; detect an abort
	      (or originalupdates |Updates | |Requirements | block-undo))
	 ; I guess we should call abort if no updates are
	 ; proposed but requirements are not meant
	 (multiple-value-lambda-bind (&rest abortdata2)
	     (catch '|OuterAtomic | (AtomicUpdate |Updates |))
	     ; atomicupdate will now simply push things onto automationqueue
	     (values-list (cond ((eq (car abortdata2) '|Abort |) abortdata2)
				(t abdata)))))
	(t (values-list abdata))))

;;; the following, in SPITE OF ITS NAME, is really obsolete.
;;; it is being retained for a time so that code compiled under the
;;; prior def'n of ATOMIC will still work.
#+ignore
(defun AtomicGutsNew (abortdata2)
  (declare (special originalupdates))
  (when (and (null |UpdateStatus |)
	      (not (eq (car abortdata) '|Abort |)) ; detect an abort
	      (or originalupdates |Updates | |Requirements |))
	 ; I guess we should call abort if no updates are
	 ; proposed but requirements are not meant
	 (setq abortdata2
	       (multiple-value-list
		 (catch '|OuterAtomic |
		   ; atomicupdate will now simply push things onto automationqueue
		   (AtomicUpdate |Updates |))))
	 (when (eq (car abortdata2) '|Abort |)
	   (setq abortdata abortdata2))))

; we do the automations outside this catch - if they abort it's their own atomic

; This is the easy one to implement:
; (do-subatomic) can be called from within an atomic and it makes everything
; previously done in the atomic visible in the rest of the atomic.
; It cannot be executed from inside consistency repair code, etc.
;
(defun do-subatomic (&aux updates update)
  (declare (special updates originalupdates |Updates | |Requirements |
		    |Direct | old-direct |UpdateStatus | indirect-computed))
  (remove-indirect-computed)
  (setq updates |Updates |)
  (unless (member |UpdateStatus | '(transparent atomic))
    (error "subatomics are currently not supported outside atomics,~
            ~%in rules or update code"))
  (setq originalupdates (nconc originalupdates updates))
  (loop while (setq update (pop updates)) do (process-update update t))
  (get-directdelta |Direct | old-direct) ; now just sets delta
  ; translate inherit's into ++/--
  (setq old-direct (loop for d in |Direct | collect (cons (car d) (cdr d))))
  (setq |Updates | nil))

;;; Now a new version of ++ and -- along with (new function) Inherit

(Defmacro-displace ++ (&rest Tuple &environment e)
  (TranslateUpdate Tuple T e))

(Defmacro-displace -- (&rest Tuple &environment e)
  (TranslateUpdate Tuple nil e))

#+ignore 
(DefMacro-displace Inherit (&rest Tuple &environment e)
  (TranslateUpdate Tuple 'Inherit e))

(defun translateupdate (tuple given-tv environment)
  (multiple-value-bind (expanded-tuple tv)
      (expand-update-wff tuple given-tv :environment environment)
    (when (compoundwffp expanded-tuple)
      (cond ((and (not tv) (eq (car (ilistp expanded-tuple)) 'E))
						; may be doable
	     )
	    (t (fail bad-update "compound wff can't be updated -- ~s" tuple))))
    (cond
      ((eq (car (ilistp expanded-tuple)) 'funcall)
       `(computed-update-body ',tv ,. (rest expanded-tuple)))
      ((eq (car (ilistp expanded-tuple)) 'apply)
       `(apply (function computed-update-body) ',tv
	       ,. (rest expanded-tuple)))
      ;; formerly `(eval (cons (case tv (inherit 'inherit) ((nil) '--) (t '++))
      ;;                       (cons (first expanded-tuple) (kwote (rest expanded-tuple)))))
      ((and (not tv) (eq (car (ilistp expanded-tuple)) 'E))
       `(set-listof ,(second expanded-tuple) s.t. ,(third expanded-tuple) () ))
      (defrel-available
       (get-update tv (first expanded-tuple) (rest expanded-tuple))
       `(,(pack* (if tv "Add-" "Delete-") (relationnamep (first expanded-tuple)))
		 ,@(rest expanded-tuple)))
      (t `(funcall (get-update ,tv (theap5relation ,(relationnamep (first expanded-tuple)))
				       ',(mapcar #'ignored (rest expanded-tuple)))
			   ,@(rest expanded-tuple))))))

; given a ++ or -- translate it into something 
(defun expand-update-wff (wff tv &key (environment *empty-env*))
   (let ((expansion
	   (third (expanddescription `(() s.t. ,wff)
				     :allowevalargs t :keepstarts t
				     :source-expansion t
				     :dont-warn-for-false t
				     :environment environment))))
     (labels ((expand-update-internal (wff tv)
		(values
		  (map-copy-wff wff
  		    ;; never let map-wff recur into subwffs on its own.
		    :environment environment 
		    :quantified-wff #'(lambda (q qvars qwff)
					(return-from expand-update-wff
					  (values (list q qvars qwff) tv)))
		    :boolean-op #'(lambda (op &rest wffs)
				    (return-from expand-update-wff
				      (cond ((eq op 'not)
					     (expand-update-internal
					       (first wffs) (not tv)))
					    (t (values (cons op (copy-list wffs)) tv)))))
		    :temporal-op #'(lambda (op twff) 
				     (return-from expand-update-wff
				       (values (list op twff) tv)))
		    :defined-wff
		    #'(lambda (original-wff expanded-wff)
			(return-from expand-update-wff
			  (cond ((or
				  #+ignore ;; this was wrong anyway
				  (get-update-macro (first original-wff) tv)
				  ;; the new way:
				  (multiple-value-bind (single set cannot)
				      (update-code (first original-wff) tv
						   (rest original-wff))
				      (declare (ignore set single))
				      (not cannot))
				  (not-allowed-to-update (first original-wff) tv))
				 (values original-wff tv))
				(t (expand-update-internal expanded-wff tv))))))
		  tv)))
       (expand-update-internal expansion tv))))

#+ignore 
(defun expand-update-wff (tuple tv
			  &key args-already-evaled (environment *empty-env*))  
  (values
    (map-copy-wff (simplify (if args-already-evaled tuple
			 (translate-functions tuple environment)))
     ;; never let map-wff recur into subwffs on its own.
     :environment environment 
     :quantified-wff #'(lambda (q qvars qwff)
			   (return-from expand-update-wff
			     (values (list q qvars qwff) tv)))
     :boolean-op #'(lambda (op &rest wffs)
		     (return-from expand-update-wff
		       (cond ((eq op 'not)
			      (expand-update-wff (first wffs) (not tv)
						 :args-already-evaled t
						 :environment environment))
			     (t (values (cons op (copy-list wffs)) tv)))))
     :temporal-op #'(lambda (op twff) 
		      (return-from expand-update-wff
			(values (list op twff) tv)))
     :defined-wff
       #'(lambda (original-wff expanded-wff)
	   (return-from expand-update-wff
	     (cond ((or (get-update-macro (first original-wff) tv)
			(not-allowed-to-update (first original-wff) tv))
		    
		    (values original-wff tv))
		   (t (expand-update-wff expanded-wff tv
					 :args-already-evaled t
					 :environment environment))))))
    tv))

#+ignore ;;prior defn
(defun expand-update-wff
       (tuple tv &key args-already-evaled (environment *empty-env*)
	      &aux (current-tv tv) #+ignore(all-inline? 'notinline))
  (declare (special current-tv))
  (simplify
    (map-copy-wff (list 'notinline
			(if args-already-evaled tuple
			    (translate-functions tuple environment)))
       :environment environment
       :boolean-op
       #'(lambda (op &rest wffs)
	   (cond ((eq op 'not)
		  (let ((current-tv (not current-tv)))
		    (declare (special current-tv))
		    (list op (map-wff-internal (car wffs)))))
		 (t (cons op (mapcar #'map-wff-internal wffs)))))
       :defined-wff
       #'(lambda (original-wff expanded-wff)
	   (cond ((get-update-macro (car original-wff) current-tv)
		  ;;; seems sort of strange if this is not the outermost wff
		  ;;; why do this inside boolean-ops, but not inside quantifiers?
		  original-wff)
		 ((not-allowed-to-update (car original-wff) current-tv)
		  original-wff)
		 (t (map-wff-internal expanded-wff)))))
    environment))

(defun do-update (tv rel &rest tuple)
  (apply (get-update tv rel tuple) tuple))

(defun update-not-allowed (&rest args)
  (declare (ignore args))
  (error "trying to do a disallowed update"))

(defun get-update (tv rel tuple
		   &aux (fname (get-structure-property rel (if tv 'adder 'deleter))))
  (when fname (return-from get-update fname))
  (setf fname (pack* (if tv "Add-" "Delete-") (relationnamep rel)))
  (when (not-allowed-to-update rel tv)
    (fail bad-update (format nil "disallowed update to ~A" rel)))
  (multiple-value-bind (both nrm smp)
	     (get-update-source tv rel tuple)
    (cond (both
	   (let ((normal (pack* "Normal-" fname))
		 (simple (pack* "Simple-" fname)))
	     (compile-ap nrm normal)
	     (compile-ap smp simple)
	     (setf (symbol-function fname)
		   (symbol-function
		    (if (simple-update-p rel tv) simple normal)))))
	  (t (compile-ap nrm fname))))
     (put-structure-property rel fname (if tv 'adder 'deleter))
     fname)

(defun update-code (rel tv tuple &aux macro fn)
  ; return list of single updates, list of set updates, impossible flag
  (cond ((setf macro (get-adder-or-deleter rel tv))
	 (values (list (apply macro rel tuple)) nil))
	((setf fn (get-updater rel))
	 (values nil (list fn)))
	(t (let (singles sets)
	     (loop for imp in (implementations-of rel) do
		   (cond ((setf fn (get-updater imp)) (push fn sets))
			 ((setf macro (get-adder-or-deleter imp tv))
			  (push (apply macro rel tuple) singles))
			 (t (return-from update-code
					 (values nil nil t)))))
	     (values singles sets)))))

;; major changes from multirep:
;; have to be able to combine updaters and add/delete'ers
#+ignore
(defun get-update-source (tv rel tuple) 
  ; => both normal-src simple-src, both means that simple is returned too
  (when (not-allowed-to-update rel tv)
    (fail bad-update (format nil "disallowed update to ~A" rel)))
  (cond ((inlinerel? rel) ;; case added 9/90 - DC
	 (let ((formals (loop for tup in tuple collect (gensym "A"))))
	   (multiple-value-bind (expanded-tuple new-tv)
	       (expand-update-wff (cons rel formals) tv)
	     (when (compoundwffp expanded-tuple)
	       (cond ((and (not new-tv) (eq (car (ilistp expanded-tuple)) 'E))
					; may be doable 
                      ;; macro expand. let it signal bad-update.
		      (macroexpand (cons '-- expanded-tuple)))
		     (t (fail bad-update
			      "compound wff can't be updated -- ~s"
			      expanded-tuple))))
	     ; the resulting code cannot necessarily be compiled
	     ; again let it signal bad update
	     (macroexpand (cons (if new-tv '++ '--) expanded-tuple))
	     (values nil `(lambda ,formals (,(if new-tv '++ '--)
					    ,. expanded-tuple))))))
	#+ignore ;;  old version replaced below
	((nonatomic-relation rel)
	 (multiple-value-setq (single singlep) (get-update-macro rel tv))
	 (multiple-value-setq (set setp) (get-update-fn rel))
	 (unless (or single set)
	   (fail bad-update
		 (format nil "~A cannot be ~A" rel (if tv "added" "deleted"))))
	 (cond ((and singlep (not setp)) (setf set nil))
	       ((and set (not singlep)) (setf single nil)))
	 (let* ((formals (loop for a in tuple collect (gensym "A")))
		(form (if single (apply (get-update-macro rel tv) rel tuple)
			  `(,set ,(uneval rel)
				 ,(when tv `(list ,(cons 'list formals)))
				 ,(unless tv `(list ,(cons 'list formals)))))))
	   
	   (when single (setf form `(,form ,(uneval rel) ,@formals)))
	   (unless (idempotent (if (or (and single singlep) (and set setp)) rel
				   (implementationof rel))
			       tv)
	     (setf form
		   `(,(if tv 'unless 'when) (?? ,(relationnamep rel) ,@formals)
		     ,form)))
	   (unless (allow-interrupts rel tv)
	     (setf form `(without-interrupts ,form)))
	   (values nil `(lambda ,formals ,form))))
	((nonatomic-relation rel)
	 (let* ((formals (loop for a in tuple collect (gensym "A")))
		form singles sets impossible (relexp (uneval rel))
		(ttups (gensym "TTUPS")) (ftups (gensym "FTUPS")))
	   (multiple-value-setq (singles sets impossible)
				(update-code rel tv tuple))
	   (when impossible
		 (fail bad-update
		       (format nil "~A cannot be ~A" rel
			       (if tv "added" "deleted"))))
	   (setf form
		 (append ;; get both
		  (loop for s in singles collect `(,s ,relexp ,@formals))
		  (loop for s in sets collect
			 `(,s ,relexp ,ttups ,ftups))))
	   (if sets
	       (setf form `(let ((,ttups
				  ,(when tv `(list ,(cons 'list formals))))
				 (,ftups
				  ,(unless tv `(list ,(cons 'list formals)))))
			     ,form))
	     (push 'progn form))
	   (unless (or (idempotent rel tv)
		       (loop for i in (implementations-of rel)
			     always (idempotent i tv)))
		   (setf form
			 `(,(if tv 'unless 'when)
			   (?? ,(relationnamep rel) ,@formals)
			   ,form)))
	   (unless (allow-interrupts rel tv)
	     (setf form `(without-interrupts ,form)))
	   (values nil `(lambda ,formals ,form))))
	((derived-nonatomic-rel rel) ;; no updaters allowed here ...
	 ;;derived from a nonatomic rel
	 (let ((formals (loop for a in tuple collect (gensym "A")))
	       macro) ;; macro was (get-update-macro rel tv)
	   (setf macro (or (get-adder-or-deleter rel tv)
			   (get-adder-or-deleter
			    (car (implementations-of rel)) ;; only one
			    tv)))
	   (unless macro 
	     (fail bad-update
		   (format nil "~A cannot be ~A" rel
			   (if tv "added" "deleted"))))
	   (values
	    nil
	     `(lambda ,formals
		(let ((|UpdateStatus | 'nonatomic-definition))
		  (,(apply macro rel tuple)
		   ,(uneval rel) ,@formals))))))
	#+ignore ;; old version replaced below
	(t (multiple-value-setq (single singlep) (get-update-macro rel tv)) 
	   (multiple-value-setq (set setp) (get-update-fn rel))
	   #+ignore ;; this doesn't work - we have to compile ++/-- in cases
	            ;; such as trigger code where no update is really executed 
	   (unless (or single set)
	     (fail bad-update
		   (format nil "~A cannot be ~A" rel (if tv "added" "deleted"))))
	   (cond ((and singlep (not setp)) (setf set nil))
		 ((and set (not singlep)) (setf single nil)))
	   ; if one comes from the rel and the other from the imp, throw out the imp
	   (when single
	     (setf single (apply single rel tuple))
	     (setf single (cond ((or (and single (symbolp single))
				     (and (consp single) (eq (car single) 'lambda)))
				 `(function ,single))
				(t single))))
	   (if (or (derivedrel rel) (getdefn rel))
	       (values
		nil
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   (compiled-update-body ',tv ,(uneval rel) copy
			 ,single ',set
			 ',(append (get-checkers rel)
				   (get-checkers (implementationof rel)))
			 (cons ',(relationnamep rel) copy)
			 ',(get-tester rel))))
	     (flet ((common-args ()
		      `(',tv ,(uneval rel) copy
			 ,single ',set
			 ',(append (get-checkers rel)
				   (get-checkers (implementationof rel)))
			 (cons ',(relationnamep rel) copy)
			 ',(get-tester rel))))
	       (values
		t
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   (compiled-update-body ,. (common-args)))
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   (funcall 
		    (if (or (inatomic)  
			    (matchconsistencies true-matchnode))
			#'compiled-update-body
		      #'do-simple-update)
		    ,. (common-args)))))))	
	(t
	 (let (single set impossible)
	   (multiple-value-setq (single set impossible)
				(update-code rel tv tuple))
	   #+ignore
	   ;; this doesn't work - we have to compile ++/-- in cases
	   ;; such as trigger code where no update is really executed 
	   (when impossible
		 (fail bad-update
		       (format nil "~A cannot be ~A" rel
			       (if tv "added" "deleted"))))
	   (if (or (derivedrel rel) (getdefn rel))
	       ;; only one imp -- not necessarily so for maintained rels!
	       (values
		nil
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   ;; single/set slots will now take a list of fns 
		   (compiled-update-body ',tv ,(uneval rel) copy
			;; we want a quoted list of functions
			',(loop for s in single collect
				  (if (consp s) ;; assume lambda
				      (compile nil s)
				    ;; symbol?
				    s
				    #+ignore (coerce s 'function)) ;; ok?
				 #+ignore
				 (if (or (symbolp s)
					 (and (consp s)
					      (eq 'lambda (car s))))
				     `(function ,s)
				   s))
			',set
			',(loop for x in (cons rel (implementations-of rel))
				append (get-checkers x))
			#+ignore
			(append (get-checkers rel)
				(get-checkers (implementationof rel)))
			(cons ',(relationnamep rel) copy)
			',(get-tester rel))))
	     (let ((common-args 
		      `(',tv ,(uneval rel) copy
			 ;; we want a quoted list of compiled functions
			 ',(loop for s in single collect
				   (if (consp s) ;; assume lambda
				       (compile nil s)
				     #+ignore ;; symbol?
				     (coerce s 'function)
				     s)
				  #+ignore ;; ok??
				  (if (or (symbolp s)
					  (and (consp s)
					       (eq 'lambda (car s))))
				      `(function ,s)
				    s))
			 ',set
			 ',(loop for x in (cons rel (implementations-of rel))
				 append (get-checkers x))
			   #+ignore
			   (append (get-checkers rel)
				   (get-checkers (implementationof rel)))
			 (cons ',(relationnamep rel) copy)
			 ',(get-tester rel))))
	       (values
		t
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   (compiled-update-body ,.common-args))
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   (funcall 
		    (if (or (inatomic)  
			    (matchconsistencies true-matchnode))
			#'compiled-update-body
		      #'do-simple-update)
		    ,.common-args)))))))))

;; don't put compiled code into macro expansions!!
(defun get-update-source (tv rel tuple) 
  ; => both normal-src simple-src, both means that simple is returned too
  (when (not-allowed-to-update rel tv)
    (fail bad-update (format nil "disallowed update to ~A" rel)))
  (cond ((inlinerel? rel) ;; case added 9/90 - DC
	 (let ((formals (loop for tup below (length tuple) collect (gensym "A"))))
	   (multiple-value-bind (expanded-tuple new-tv)
	       (expand-update-wff (cons rel formals) tv)
	     (when (compoundwffp expanded-tuple)
	       (cond ((and (not new-tv) (eq (car (ilistp expanded-tuple)) 'E))
					; may be doable 
                      ;; macro expand. let it signal bad-update.
		      (macroexpand (cons '-- expanded-tuple)))
		     (t (fail bad-update
			      "compound wff can't be updated -- ~s"
			      expanded-tuple))))
	     ; the resulting code cannot necessarily be compiled
	     ; again let it signal bad update
	     (macroexpand (cons (if new-tv '++ '--) expanded-tuple))
	     (values nil `(lambda ,formals (,(if new-tv '++ '--)
					    ,. expanded-tuple))))))
	#+ignore ;;  old version replaced below
	((nonatomic-relation rel)
	 (multiple-value-setq (single singlep) (get-update-macro rel tv))
	 (multiple-value-setq (set setp) (get-update-fn rel))
	 (unless (or single set)
	   (fail bad-update
		 (format nil "~A cannot be ~A" rel (if tv "added" "deleted"))))
	 (cond ((and singlep (not setp)) (setf set nil))
	       ((and set (not singlep)) (setf single nil)))
	 (let* ((formals (loop for a below (length tuple) collect (gensym "A")))
		(form (if single (apply (get-update-macro rel tv) rel tuple)
			  `(,set ,(uneval rel)
				 ,(when tv `(list ,(cons 'list formals)))
				 ,(unless tv `(list ,(cons 'list formals)))))))
	   
	   (when single (setf form `(,form ,(uneval rel) ,@formals)))
	   (unless (idempotent (if (or (and single singlep) (and set setp)) rel
				   (implementationof rel))
			       tv)
	     (setf form
		   `(,(if tv 'unless 'when) (?? ,(relationnamep rel) ,@formals)
		     ,form)))
	   (unless (allow-interrupts rel tv)
	     (setf form `(without-interrupts ,form)))
	   (values nil `(lambda ,formals ,form))))
	((nonatomic-relation rel)
	 (let* ((formals (loop for a below (length tuple) collect (gensym "A")))
		form singles sets impossible (relexp (uneval rel))
		(ttups (gensym "TTUPS")) (ftups (gensym "FTUPS")))
	   (multiple-value-setq (singles sets impossible)
				(update-code rel tv tuple))
	   (when impossible
		 (fail bad-update
		       (format nil "~A cannot be ~A" rel
			       (if tv "added" "deleted"))))
	   (setf form
		 (append ;; get both
		  (loop for s in singles collect `(,s ,relexp ,@formals))
		  (loop for s in sets collect
			 `(,s ,relexp ,ttups ,ftups))))
	   (if sets
	       (setf form `(let ((,ttups
				  ,(when tv `(list ,(cons 'list formals))))
				 (,ftups
				  ,(unless tv `(list ,(cons 'list formals)))))
			     ,form))
	     (push 'progn form))
	   (unless (or (idempotent rel tv)
		       (loop for i in (implementations-of rel)
			     always (idempotent i tv)))
		   (setf form
			 `(,(if tv 'unless 'when)
			   (?? ,(relationnamep rel) ,@formals)
			   ,form)))
	   (unless (allow-interrupts rel tv)
	     (setf form `(without-interrupts ,form)))
	   (values nil `(lambda ,formals ,form))))
	((derived-nonatomic-rel rel) ;; no updaters allowed here ...
	 ;;derived from a nonatomic rel
	 (let ((formals (loop for a below (length tuple) collect (gensym "A")))
	       macro) ;; macro was (get-update-macro rel tv)
	   (setf macro (or (get-adder-or-deleter rel tv)
			   (get-adder-or-deleter
			    (car (implementations-of rel)) ;; only one
			    tv)))
	   (unless macro 
	     (fail bad-update
		   (format nil "~A cannot be ~A" rel
			   (if tv "added" "deleted"))))
	   (values
	    nil
	     `(lambda ,formals
		(let ((|UpdateStatus | 'nonatomic-definition))
		  (,(apply macro rel tuple)
		   ,(uneval rel) ,@formals))))))
	#+ignore ;; old version replaced below
	(t (multiple-value-setq (single singlep) (get-update-macro rel tv)) 
	   (multiple-value-setq (set setp) (get-update-fn rel))
	   #+ignore ;; this doesn't work - we have to compile ++/-- in cases
	            ;; such as trigger code where no update is really executed 
	   (unless (or single set)
	     (fail bad-update
		   (format nil "~A cannot be ~A" rel (if tv "added" "deleted"))))
	   (cond ((and singlep (not setp)) (setf set nil))
		 ((and set (not singlep)) (setf single nil)))
	   ; if one comes from the rel and the other from the imp, throw out the imp
	   (when single
	     (setf single (apply single rel tuple))
	     (setf single (cond ((or (and single (symbolp single))
				     (and (consp single) (eq (car single) 'lambda)))
				 `(function ,single))
				(t single))))
	   (if (or (derivedrel rel) (getdefn rel))
	       (values
		nil
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   (compiled-update-body ',tv ,(uneval rel) copy
			 ,single ',set
			 ',(append (get-checkers rel)
				   (get-checkers (implementationof rel)))
			 (cons ',(relationnamep rel) copy)
			 ',(get-tester rel))))
	     (flet ((common-args ()
		      `(',tv ,(uneval rel) copy
			 ,single ',set
			 ',(append (get-checkers rel)
				   (get-checkers (implementationof rel)))
			 (cons ',(relationnamep rel) copy)
			 ',(get-tester rel))))
	       (values
		t
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   (compiled-update-body ,. (common-args)))
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   (funcall 
		    (if (or (inatomic)  
			    (matchconsistencies true-matchnode))
			#'compiled-update-body
		      #'do-simple-update)
		    ,. (common-args)))))))	
	(t
	 (let (single set impossible)
	   (declare (ignorable impossible))
	   (multiple-value-setq (single set impossible)
				(update-code rel tv tuple))
	   #+ignore
	   ;; this doesn't work - we have to compile ++/-- in cases
	   ;; such as trigger code where no update is really executed 
	   (when impossible
		 (fail bad-update
		       (format nil "~A cannot be ~A" rel
			       (if tv "added" "deleted"))))
	   (if (or (derivedrel rel) (getdefn rel))
	       ;; only one imp -- not necessarily so for maintained rels!
	       (values
		nil
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   ;; single/set slots will now take a fn or a list of fns 
		   (compiled-update-body ',tv ,(uneval rel) copy
			,(if (and single (null(rest single)))
			     `(function ,(first single))
			   ;; we would like to avoid consing up the
			   ;; list of functions on each call
			     `(progn ;load-memo
				(list ,.(loop for s in single collect
					   `(function ,s)))))
			',set
			#+(or abcl lispworks) ;; thx to Rene De Visser
                        (load-time-value 
                         (loop for x in
			   (cons (relationp ',(relationnamep rel))
				 (implementations-of
				  (relationp ',(relationnamep rel))))
			   append (get-checkers x)))
                        #-(or abcl lispworks)
			',(loop for x in (cons rel (implementations-of rel))
				append (get-checkers x))
			#+ignore
			(append (get-checkers rel)
				(get-checkers (implementationof rel)))
			(cons ',(relationnamep rel) copy)
			',(get-tester rel))))
	     (let ((common-args 
		    `(',tv ,(uneval rel) copy
			   (progn	;load-memo
			     (list
				   ,.(loop for s in single collect
					   `(function ,s))))
			 ',set
			 #+(or abcl lispworks) ;; thx to Rene De Visser
			 ;; The problem here is that get-checkers returns
			 ;; closures and we're trying to dump those to
			 ;; compiled files.  Which means having to dump
			 ;; environments.  See also typecons.lsp.
                         (load-time-value 
                          (loop for x in
			    (cons (relationp ',(relationnamep rel))
				  (implementations-of
				   (relationp ',(relationnamep rel))))
			    append (get-checkers x)))
                         #-(or abcl lispworks)
			 ',(loop for x in (cons rel (implementations-of rel))
				 append (get-checkers x))
			 (cons ',(relationnamep rel) copy)
			 ',(get-tester rel))))
	       (values
		t
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   (compiled-update-body ,.common-args))
		`(lambda (&rest arglist &aux (copy (copy-list arglist)))
		   (funcall 
		    (if (or (inatomic)  
			    (matchconsistencies true-matchnode))
			#'compiled-update-body
		      #'do-simple-update)
		    ,.common-args)))))))))


(defun do-simple-update (tv rel args update-single update-set checkers
			    cons-rel-args testfn
    &aux |Direct | |Indirect | |Maintain | |Activations | directdelta
    directtrees indirecttrees againtrees history |Again | upd delta
    indirect-computed *automation-queue*)
  (declare (special |Direct | |Indirect | |Maintain | |Activations | directdelta
		    directtrees indirecttrees againtrees history |Again |
		    indirect-computed *automation-queue*))
  (checkupdateallowed cons-rel-args tv)
  (withwriteaccess
    (setq upd (make-updaterec
	       :updtuple
	       (make-tuple :tuprel rel :tupargs args :tuptv tv)
	       :updreason cons-rel-args
	       ; :updcx currentcx
	       :updcode-single update-single
	       :updcode-set update-set 
	       ))
    (unless (eq tv (apply testfn args))
      (setq delta (list (list rel upd)) |Direct | delta directdelta delta
	    history (make-history-record
		      :generation# (incf generation#)
		      :prev-gen# (when (consp global-history)
				   (generation# (car global-history)))
		      :originalupdates (list upd)
		      :consistency-cycles
		      (list (make-consistency-cycle-record
			      :direct delta :directdelta delta
			      :delta delta))))
      (loop for fn in checkers
	    unless
	    (let ((|UpdateStatus | 'checking))
	      (funcall fn rel (when tv (list args)) (unless tv (list args))))
	    do (error "checker failed for update ~A" upd))
      (record-history history)
      (let (done)
	(unwind-protect
	  (progn
	    (unless (member :automation suspended-rule-classes) (trigger-nil-st-true))
	    (do-advice-for-every-transition)
	    (setf done t))
	(when (and (not done) (consp global-history)
		   (eq history (car global-history)))
	  (pop global-history))))
      ;(when *watch-do-update* (funcall *watch-do-update* upd))
      ; forget DangerMessage warning on error, wholine
      (writing
       ;; have to do *both* set and single,
       ;; also the updates are now LISTS of functions
       (loop for s in update-set do
	     ;; ok, so I'm wasting a list on each extra call ...
	     (funcall s rel (when tv (list args)) (unless tv (list args))))
       (if (not (consp update-single))
	   (apply update-single rel args)
	 (loop for s in update-single do
	       (apply s rel args)))))
    (incf *atomic-id*)
    (doautomationrulesnew)
    nil))

(defun trigger-nil-st-true ()
  (loop for rule in (matchautomations true-matchnode)
	unless (member rule suspended-rules) do
	(let ((rc (effective-rule-code rule nil)))
	  (if (automationgenerator-P rule)
	      (let ((|UpdateStatus | 'automationgenerating)
		    (*current-rule* rule))
		(funcall rc))
	    (push (list rule rc nil) *automation-queue*)))))

(defun compiled-update-body (tv rel args update-single update-set
				#+ignore updcx-fn checkers cons-rel-args testfn)
  (checkupdateallowed cons-rel-args tv)
  (atomic
     (push
       (make-updaterec
	 :updtuple
	 (make-tuple :tuprel rel :tupargs args :tuptv tv)
	 :updreason cons-rel-args
	 ; :updcx currentcx
	 :updcode-single
	 (unless (eq |UpdateStatus | 'trigger) update-single)
	      ;; no value in this for triggers
	 :updcode-set update-set
	 ; :updcxeval
	 ; (unless (eq |UpdateStatus | 'trigger) updcx-fn)
	 :UpdCheckers checkers
	 :updtester testfn)
       |Updates |)
     nil))

(defun computed-update-body (tv &rest wff &aux rel)
  (if (setq rel (relationp (first wff)))
      (apply (get-update tv rel (rest wff)) (rest wff))
      (if (descriptionp (first wff) t)
	  (eval `(,(ecase tv ((t) '++) ((nil) '--)
			 #+ignore (otherwise 'inherit))
		  ,(first wff) ,@(mapcar #'kwote (rest wff))))
	  (error "~s is not a relation.  The first argument to FUNCALL or APPLY ~
                 ~&in a WFF must evaluate to a relation or the name of a relation."
		 (first wff)))))
#+ignore  ;previous version
(defun computed-update-body (tv &rest wff); &aux rel expanded-tuple
  (unless
    (or (relationp (first wff)) (descriptionp (first wff) t))
     (error "~s is not a relation.  The first argument to FUNCALL or APPLY 
            in a WFF must evaluate to a relation or the name of a relation."
	    (first wff)))
     (eval `(,(case tv ((t) '++) ((nil) '--) (otherwise 'inherit))
	     ,(first wff) ,@(mapcar #'kwote (rest wff)))))
#| ; below fails for
   ; (++ R x) when (R x) == (R2 x 'asd) -- the problem is evaluation of the asd
   ; Neil suggests compiling an adder for R (seems a good idea)
   (setf expanded-tuple (expand-update-wff wff tv
			   :args-already-evaled t) ;; handle derived rels
	 rel (relationp (first expanded-tuple)))
   (unless rel (error "Attempt to update ~s, which is not updateable"
		      (first wff)))
   (apply #'DO-UPDATE tv rel (copy-list (rest expanded-tuple)))
|#

(defun TestRel (relation &rest objects &aux rel)
  (cond ((dbobject-p relation) (setq rel relation))
	(t (setq rel (relationp relation))))
  (cond (rel (apply (get-tester rel) objects))
	;((stringp relation) (mmemo-error? relation))
	(t (eval `(?? ,relation ,@(mapcar #'kwote objects))))))

#+ignore  ; no longer used
(defun generic-op (compiler rel args &aux code)
    ; in order to save run time we use one generic operation (independent of the
    ; particular arguments) which need only be compiled once.  Compiler is a
    ; base relation, e.g. RelAdder.  We cache it as a StructProp.
    ; already know that rel is a relation
    ; should decache when rel is undeclared ***
    (cond ((not (eql (length args) (arity* rel)))   ;already know it's a rel
	   (error "~S wrong arity" (cons rel args)))
	  ((loop for x in (get-structure-property rel compiler) thereis x))
	  ; not clear that caching is a good idea, since things may change
	  ((and (setq code (getbasedata compiler))
		(setq code (or (assoc rel code)
			       (assoc (implementationof rel) code))))
	   (setq code (apply (cadr code) rel
				     (loop for arg in args collect 
					   (gensym "A"))))
	   (put-structure-property rel (list code) compiler)
           code)
	  (t (error "unable to find code s.t. ~S" (list compiler rel 'code)))))

(defun checkupdateallowed (tuple tv)
  (declare (ignore tv))
    (case |UpdateStatus |
     ; a lot faster when the common case is first!
     ((nil consistency maintain definition atomic trigger) nil)
     (primitive
      (error "Attempt to update tuple (e.g., ++) in a primitive database update ~%~s"
	    tuple))
     (checking
      (error "Attempt to update tuple (e.g., ++) in a primitive checker ~%~s" tuple))
     (report-inconsistency
       (error "attempt to update the database when reporting inconsistency"))
     (every-transition-advice
       (error "attempt to update the database while doing advice for every transition"))
     (automationgenerating
       (error "attempt to update the database while generating automation invocations"))
     (responder-search
      (error "attempt to update the database while computing a dynamic responder for a rule"))
     (nonatomic-definition
       (error "attempt to update atomic relation as part of update to nonatomic relation"))
     (transparent
      (error "ap5 error: updates should never happen with updatestatus ~A" |UpdateStatus |))
     (t (error "Unknown UpdateStatus -- ~s"  |UpdateStatus |)))
    #+ignore ; no longer use inherit
    (cond ((and (eq tv 'inherit) (eql currentcx *globalcx*))
           (error "can't inherit in global context ~s" tuple))))

(defun Check2states (operation)
    (case
     |UpdateStatus |
     ((nil primitive nonatomic-definition)
      (error "temporal reference meaningless here -- ~s" operation))
     ((atomic ; makes sense if you use subatomics
	checking ; see -single checker
	report-inconsistency every-transition-advice automationgenerating
	responder-search trigger
	transparent consistency maintain definition)
      nil)
     (t (error "Unknown UpdateStatus -- ~s"  |UpdateStatus |))))

(Defvar-resettable |UpdateStatus | nil)
; The following values are meaningful:
;
; nil - we're not altering the database (normal global value)
; Atomic - doing user code in an atomic - changes accepted for atomic processing
; Definition - expanding an update of a dependent change into independent changes
;            a change is interpreted as part of the definition of the original
; Trigger - enumerating the dependent consequences of independent changes
;            a change is interpreted as part of the consequences
; Maintain - running maintain rules
; Transparent - in AtomicUpdate - it will produce meaningful error messages if
;            it decides to abort
; Primitive - executing code that is supposed to directly change the database
;            updates not allowed
; Checking - executing code that checks validity of a tuple - updates not allowed
; Consistency - running consistency rules - updates meaningful
; Report-Inconsistency - running the reporting code for failing consistency rules
; every-transition-advice - doing advice for every transition
; automationgenerating - gathering data for atomations
; nonatomic-definition - expanding update of nonatomic relation into other 
;            nonatomic updates

(declaim (inline inatomic two-states-visible))

(defun InAtomic () |UpdateStatus |)
(defun two-states-visible ()
  (not (member |UpdateStatus | '(nil atomic nonatomic-definition))))
; nonatomic-definition can occur in 2state situation but update code cannot
; count on this

(defvar *max-history-length* nil)

; these are used in suspending rules
(defvar-resettable suspended-matchnodes nil) 
(defvar-resettable suspended-rules nil) 
(defvar-resettable suspended-rule-classes nil)

; these are for watching progress in (large) atomic updates
(defvar *rule-cycle*)
(defvar *watch-consistency-cycle* 'start-ccycle)     ; fn of cycle#, updates, delta
(defvar *watch-update* nil)                ; fn of update
(defvar *watch-consistency-trigger* nil)   ; fn of update to trigger from
(defvar *watch-automation-trigger* nil)    ; fn of update to trigger from
(defvar *watch-do-update* nil)             ; fn of update - now obsolete (set updates)
(defvar *watch-maintain-indirect* nil)     ; fn of step

(defun start-ccycle (cycle# updates delta)
  (declare (ignore cycle# updates))  ;;  not delta cause it's special
       nil)
; mainly for tracing

(defun watch-large-atomics ()
  (setq *watch-consistency-cycle* 'watch-consistency-cycle
	*watch-update* 'watch-update
 	*watch-consistency-trigger* 'watch-consistency-trigger
	*watch-automation-trigger* 'watch-automation-trigger
	*watch-do-update* 'watch-do-update
	*watch-maintain-indirect* 'watch-maintain-indirect))

(defun watch-consistency-cycle (&rest ignore)
  (declare (ignore ignore)
	   (special update# consistency# automation# do-update# MIStep#))
  (setq update# 0 consistency# 0 automation# 0 do-update# 0 MIStep# 0))

(defun watch-update (u)
  (declare (ignore u) (special update#))
  (when (= (mod (incf update#) 100) 0)
    (format *error-output* "~&~A update # ~A"
	    (print-current-time nil) update#)))
(defun watch-consistency-trigger (u)
  (declare (ignore u) (special consistency#))
  (when (= (mod (incf consistency#) 100) 0)
    (format *error-output* "~&~A consistency trigger # ~A"
	    (print-current-time nil)
	    consistency#)))
(defun watch-automation-trigger (u)
  (declare (ignore u) (special automation#))
  (when (= (mod (incf automation#) 100) 0)
    (format *error-output* "~&~A automation trigger # ~A"
	    (print-current-time nil)
	    automation#)))
(defun watch-maintain-indirect (u)
  (declare (ignore u) (special MIStep#))
  (when (= (mod (incf MIStep#) 100) 0)
    (format *error-output* "~&~A Maintain-Indirect step # ~A"
	    (print-current-time nil) MIStep#)))
(defun watch-do-update (u)
  (declare (ignore u) (special do-update#))
  (when (= (mod (incf do-update#) 100) 0)
    (format *error-output* "~&~A do-update # ~A"
	    (print-current-time nil) do-update#)))

; Updates is a list of UpdateRec's, i.e., {tuple, cx, reason}.
; History records stages of development of the atomic transaction for debugging.
; Direct is monotonically growing set of direct (independent) changes.
; Again is monotonically growing set of tuples that are already true 
;  (needn't reassert), yet may not be contradicted.
; Indirect contains indirect (dependent) changes, presumably dependent only on
;  direct and not on each other - we assume they are consistent both with direct
;  and with each other.  They are recomputed on each cycle.
; Maintain contains updates of maintained rels.  These may depend on each other
;  as well as direct and indirect.  Maintained rel tuples should not occur in
;  again, direct, indirect.  Maintained rels either have to be allowed to
;  "change back and forth" on the same cycle (the last value will still be right
;  (if there are no cycles!) but it might take a long time) or they have to be
;  ordered so that none is evaluated until all its predecessors have been.
; DirectDelta is a mapping from direct that views inherits as adds or deletes.
; Delta is the union of DirectDelta, Indirect and Maintain.
; IndexDelta is an ap3 relation representation of delta,
; the trees for other data are for detecting duplicates
;
(defun atomicupdate (updates &aux update |MIQueue | ; |Maintain | moved outside
			     (|UpdateStatus | 'transparent)  |Indirect |
			     |Activations | history old-ddelta
			     old-indirect old-maintain old-delta
			     directdelta activationtrees indirecttrees
			     ;|Again | delta directtrees againtrees
			     ;old-direct indexdelta |Direct |
			     do-whostates
			     |InAtomicUpdate|) ; only use is testing boundp
  (declare (special |Direct | |Indirect | |Maintain | |Activations | updates
		    old-direct old-ddelta directdelta ifabort-supplied |MIQueue |
		    activationtrees directtrees indirecttrees againtrees explicit-MI
		    history update |Again | originalupdates
		    old-delta old-indirect old-maintain do-whostates |InAtomicUpdate|))
  (setf originalupdates (nconc originalupdates updates)
	history (make-history-record :originalupdates originalupdates
		     :generation# (incf generation#)
		     :prev-gen# (when (consp global-history)
				  (generation# (car global-history)))))
  (when (and originalupdates suspended-rules)
    (suspend-matchnodes-for-rules suspended-rules))
  (loop for *rule-cycle* from 1 while (or updates (= *rule-cycle* 1)) do
	; loop over consistency cycles - at least once, even if all updates in subatomics
    (do-1-cycle))
  ;; run checkers at end so they have access to ultimate delta
  (loop for r in |Requirements | unless (apply (car r) (cdddr r)) do
	(abort 'Insist "Insist failed:~%~A~%~A~%~A" (cadr r) (caddr r) (cdddr r)))
  (when (or delta block-undo)
    (dolist (e |Direct |) (run-checkers e))
    (dolist (e |Maintain |) (run-checkers e))
    (setf |Activations | nil activationtrees nil)
    (record-history history)
    (let (done)
      (unwind-protect
	(progn
	  (unless (member :automation suspended-rule-classes)
	    (with-whostate "Trigger Automations" (trigger-automations)))
	  (do-advice-for-every-transition)
	  (setf done t))
      (when (and (not done) (eq history (car global-history)))
	(pop global-history))))
    (dodbupdates)
    nil))

(defun do-1-cycle (&aux triggers)
  (declare (special update updates |Direct | old-direct  |Maintain |
		    explicit-MI old-ddelta directdelta |Indirect |
		    old-indirect old-maintain |Activations | history
		    |Again |))
  (and *watch-consistency-cycle*
       (funcall *watch-consistency-cycle* *rule-cycle* updates delta))
  (check-cycle-limit *rule-cycle*)
  (unless (= *rule-cycle* 1) (setf do-whostates t))
  (loop while (setf update (pop updates)) do (process-update update nil))
  (setf |Updates | nil)
  (get-directdelta |Direct | old-direct)	; now just sets delta
						; translate inherit's into ++/--
  (when (and (null do-whostates)
	     (or (cdr delta) (cddar delta)))	; more than one update
    (setf do-whostates t))		; whostates too expensive for small updates
  (when (and triggers (loop for d in |Direct | always
			    (eq (cdr d) (cdr (assoc (car d) old-direct)))))
    #+ignore
    (progn
      (unless ifabort-supplied (report-consistency-violations triggers))
      (abort 'rules-do-only-noops "No reaction to consistency rules" triggers))
    ; hope this works on symbolics
    (abort (make-condition
	    'rules-do-only-noops
	    :description "No reaction to consistency rules."
	    :triggers triggers)))
  (cond ((member :maintain suspended-rule-classes)
	 (loop for u in explicit-MI do		; would otherwise be done by CMI
	       (unless (member u (assoc (tuprel (updtuple u)) delta)) 
		 (add-to-delta u (tuprel (updtuple u))))
	       (unless (member u (assoc (tuprel (updtuple u)) |Maintain |)) 
		 (pushassoc u (tuprel (updtuple u)) |Maintain |))))
	(t (compute-maintain-indirect delta)))
  ; updates maintain, indirect, delta
  ; :maintain in suspended-rule-classes implies no rules at all
  (setf old-direct (loop for d in |Direct | collect (cons (car d) (cdr d)))
		; for next use in get-directdelta
	directdelta (loop for d in delta collect (cons (car d) (cdr d))))
 ; this has to be done even if compute-maintain-indirect is not called at all!
  (unless (member :consistency suspended-rule-classes)
    (with-whostate "Check Consistency" (compute-activations))
    (setf old-ddelta
	  (loop for d in Directdelta collect (cons (car d) (cdr d)))
	  old-indirect |Indirect |
	  old-maintain |Maintain |))
	; for next cycle - need cdr of each element to be eq
  (push (make-consistency-cycle-record
	  :direct |Direct | :directdelta directdelta
	  :indirect |Indirect | :maintain |Maintain | :again |Again |
	  :delta delta :activations |Activations |)
	(consistency-cycles history))
	; optimization: first see if any are just plain abort
  (let ((|UpdateStatus | 'Consistency) |Updates |)
    (with-whostate "Do Consistency"
      (setf triggers (DoConsistencyRules |Activations |)))
    (setq updates |Updates |))
  (when (and triggers (null updates))
    #+ignore
    (progn
      (unless ifabort-supplied (report-consistency-violations triggers))
      (abort 'unfixed-consistency-violation
	     "No reaction to consistency rules" triggers))
    ; hope this works on symbolics
    (abort (make-condition
	    'unfixed-consistency-violation
	    :description "No reaction to consistency rules."
	    :triggers triggers))))

#+ignore ; old version
(defun do-1-cycle (&aux triggers)
  (declare (special update updates |Direct | old-direct  |Maintain |
		    explicit-MI old-ddelta directdelta |Indirect |
		    old-indirect old-maintain |Activations | history
		    |Again |))
  (and *watch-consistency-cycle*
       (funcall *watch-consistency-cycle* *rule-cycle* updates delta))
  (check-cycle-limit *rule-cycle*)
  (unless (= *rule-cycle* 1) (setf do-whostates t))
  (loop while (setf update (pop updates)) do (process-update update nil))
  (setf |Updates | nil)
  (get-directdelta |Direct | old-direct)	; now just sets delta
						; translate inherit's into ++/--
  (when (and (null do-whostates)
	     (or (cdr delta) (cddar delta)))	; more than one update
    (setf do-whostates t))			; whostates too expensive for small updates
  (when (and triggers (loop for d in |Direct | always
			    (eq (cdr d) (cdr (assoc (car d) old-direct)))))
    (unless ifabort-supplied (report-consistency-violations triggers))
    (abort 'rules-do-only-noops "No reaction to consistency rules." triggers))
  (cond ((member :maintain suspended-rule-classes)
	 (loop for u in explicit-MI do		; would otherwise be done by CMI
	       (unless (member u (assoc (tuprel (updtuple u)) delta)) 
		 (add-to-delta u (tuprel (updtuple u))))
	       (unless (member u (assoc (tuprel (updtuple u)) |Maintain |)) 
		 (pushassoc u (tuprel (updtuple u)) |Maintain |))))
	(t (compute-maintain-indirect delta)))
  ; updates maintain, indirect, delta
  ; :maintain in suspended-rule-classes implies no rules at all
  (setf old-direct (loop for d in |Direct | collect (cons (car d) (cdr d)))
		; for next use in get-directdelta
	directdelta (loop for d in delta collect (cons (car d) (cdr d))))
 ; this has to be done even if compute-maintain-indirect is not called at all!
  (unless (member :consistency suspended-rule-classes)
    (with-whostate "Check Consistency" (compute-activations))
    (setf old-ddelta
	  (loop for d in Directdelta collect (cons (car d) (cdr d)))
	  old-indirect |Indirect |
	  old-maintain |Maintain |))
	; for next cycle - need cdr of each element to be eq
  (push (make-consistency-cycle-record
	  :direct |Direct | :directdelta directdelta
	  :indirect |Indirect | :maintain |Maintain | :again |Again |
	  :delta delta :activations |Activations |)
	(consistency-cycles history))
	; optimization: first see if any are just plain abort
  (let ((|UpdateStatus | 'Consistency) |Updates |)
    (with-whostate "Do Consistency"
      (setf triggers (DoConsistencyRules |Activations |)))
    (setq updates |Updates |))
  (when (and triggers (null updates))
    (unless ifabort-supplied (report-consistency-violations triggers))
    (abort 'unfixed-consistency-violation
	   "No reaction to consistency rules." triggers)))

; don't allow Fix-Maintained-Relation hack unless UpdateStatus = atomic
(defun process-update (update subatomic-P &aux tuple rel)
  (declare (special directtrees |Direct | againtrees explicit-MI |Maintain |))
  (when *watch-update* (funcall *watch-update* update))
  (setq tuple (updtuple update))
  (cond					;classify the update
    ((tuple-already-seen update tuple (list directtrees againtrees)))
    ((undefined-update update))
    ((derivedrel (setq rel (tuprel tuple)))		; Defined update 
     (do-defined-update update tuple))
    ((detect-noop update tuple))
    ((maintain-mnode rel)
     (cond ((and Fix-Maintained-Relation
		 (or (eq |UpdateStatus | 'atomic)
		     (eq |UpdateStatus | 'transparent)))
	    (push update explicit-MI)
	    (when subatomic-p
	      (add-to-delta update rel)
	      ; in Maintain so remove-mi will get rid of it
	      (pushassoc update rel |Maintain |)))
	   (t (abort 'update-maintain "attempt to update a maintained relation"
		     rel))))
    (t ;(run-checkers update tuple) put this off until the end
       (setq directtrees (add-update-tree update tuple directtrees nil))
       (pushassoc update rel |Direct |))))


; for now we treat (nil s.t. true) as THEONLY special case

(unless (boundp 'true-matchnode)
  (setq true-matchnode (make-matchnode :matchwff 'true)))

(defun trigger-automations ()
  (declare (special directdelta |Activations |)) ; |Indirect | |Maintain |
  (dolist (entry directdelta)		; new format
	(dolist (u (rest entry))
	      (when *watch-automation-trigger*
		(funcall *watch-automation-trigger* u))
	      (activate-from-update u :automation)))
  (loop for a in (cons (list true-matchnode nil) |Activations |)
	when (cdr a) do ; non-negligible optimization
	(loop for rule in (matchautomations (car a))
	      unless (member rule suspended-rules) do
	      (if (automationgenerator-P rule)
		  (let ((|UpdateStatus | 'automationgenerating)
			(*current-rule* rule))
		    (dolist (act (rest a))
			    (apply (effective-rule-code rule act) act)))
		(dolist (act (rest a))
			(push (list rule
				    (effective-rule-code rule act)
				    act)
			      *automation-queue*))))))

(defvar *rule-cycle-limit* 7)
(defun check-cycle-limit (rule-cycle)
  (and *rule-cycle-limit* (> rule-cycle *rule-cycle-limit*)
       (cerror "continue"
	       "The current attempt to update the database is now starting~
                ~%consistency cycle # ~A, which indicates that it might be~
                ~%in an infinite loop.  If you want to see what the rules ~
                ~%are doing you should trace ap5::doconsistencyrule and~
                ~%continue.  You can change the cycle limit after which these~
                ~%warnings are issued by setting ap5::*rule-cycle-limit* to~
                ~%another number or nil (meaning never warn)."
	       rule-cycle)))

(defun run-checkers (entry &aux pos neg)
  (when (and (cdr entry) (updcheckers (cadr entry)))
    (loop for upd in (cdr entry) do
	  (if (tuptv (updtuple upd)) (push (tupargs (updtuple upd)) pos)
	      (push (tupargs (updtuple upd)) neg)))
    ; atomicupdate optimized to do this only once per update in Direct+Maintain
    (unless
      (let ((|UpdateStatus | 'checking) #+ignore (currentcx (updcx update)) #+ignore delta)
	(declare (special |UpdateStatus | delta))
	; checkers should see only previous state? -single checker looks at new...
	(loop for fn in (UpdCheckers (cadr entry))
	      always (funcall fn (car entry) pos neg)))
      (error "checker failed for relation ~A" (car entry)))))

(defun tuple-already-seen (update tuple treeslist &aux tree)
  (declare (special Directtrees Againtrees history |Again |))
  ; again is checked cause it holds noops as well as repeated updates
  (cond ((loop for category in treeslist thereis
	       (and (setq tree (cdr (assoc (list (tuprel tuple)
						 (tuptv tuple)
						 #+ignore (updcx update))
					   category :test #'equal)))
		    (treetester (canonicalize-tuple (tuprel tuple) (tupargs tuple))
				tree
				(rel-comparisons (tuprel tuple)))))
	 (pushassoc update (tuprel tuple) |Again |)
	 ; no need to record it again in a tree
	 t) ; value to return
	((loop for category in treeslist thereis
	       (loop for tv in '(t nil inherit) thereis
		     (and (not (eq tv (tuptv tuple)))
			  (setq tree (cdr (assoc (list (tuprel tuple)
						       tv
						       #+ignore (updcx update))
					   category :test #'equal)))
			  (treetester (canonicalize-tuple (tuprel tuple) (tupargs tuple))
				      tree
				      (rel-comparisons (tuprel tuple))))))
	 (abort 'contradictory-updates "Contradictory updates: ~%~A"
		update))))  ; otherwise return nil

(defun undefined-update (update)
  (declare (special history))
  (cond ((and (null (updcode-single update))
	      (null (updcode-set update))
	      #+ignore 
	      (or (not (eq (tuptv tuple) 'inherit))
		  (not (context-sensitive (tuprel tuple)))))
	 ; special dispensation - inherits can default
	 (abort 'undefined-update "Undefined update: ~%~A" update))))

(defun do-defined-update (update tuple) 
  (let (|Updates | #+ignore (currentcx (updcx update))
	(|UpdateStatus | 'definition))
    (declare (special |Updates | |UpdateStatus | updates))
    (apply (if (consp (updcode-single update))
	       (car (updcode-single update))
	     (updcode-single update))
	   ;; for now: only one updcode-single allowed for derived rels
	   (tuprel tuple) (tupargs tuple))
    (loop for u in |Updates | do ;alter-updaterec
	  (setf (updreason u) (list 'definedupdate (updreason u) update))
	  (push u updates))))

(defun detect-noop (update tuple &aux value)
  (declare (special |Again | againtrees))
  (cond ((eql (tuptv tuple) ; two cases
	      (cond (t ;(not (context-sensitive (tuprel tuple)))
		     (setq value (explicitvaluein (tuprel tuple)
						  (tupargs tuple)
						  #+ignore (updcx update)))
		     (and (eq value 'inherit)
			  #+ignore (eql *globalcx* (updcx update))
			  ; explicitvaluein can return inherit for global
			  (setq value ; get global value
				(apply (updtester update) ;'testrel ; (updcxeval update)
				       ;(tuprel tuple)
				       (tupargs tuple))))
		     (not (not value)))
		    #+ignore ; no contexts ...
		    (t (let (#+ignore (currentcx (updcx update)))
			 (testrel ;apply (updcxeval update)
				(tuprel tuple)
				(tupargs tuple))))))
	 (pushassoc update (tuprel tuple) |Again |)
	 (setq againtrees (add-update-tree update tuple againtrees nil))
	 t))) ; return t to indicate that this case applies


; this version does not promise to eval key only once
(defmacro pushassoc (value key alist &key (test '(function eql)))
  `(let ((entry (assoc ,key ,alist :test ,test)))
     (cond (entry (push ,value (cdr entry)))
	   ; assume it won't be nil - if we delete we have to remove empty entries
	   (t (push (list ,key ,value) ,alist)))))

(defun add-update-tree (update tuple treelist return-added-p
			&aux tree key)
  (declare (ignore update))
  (or (setq tree (cdr (assoc (setq key (list (tuprel tuple) (tuptv tuple)
					     #+ignore (updcx update)))
			     treelist :test #'equal)))
      (push (cons key (setq tree (createtree))) treelist))
  (values treelist
	  (treeadder (canonicalize-tuple (tuprel tuple) (tupargs tuple))
		     tree (rel-comparisons (tuprel tuple))
		     return-added-p)))

(defun get-directdelta (Direct old-direct &aux d  tuple #+ignore value)
  ; translate inherits into ++/-- to get the effect of direct
  ; optimized to use results of previous cycles
  (loop for e in Direct do
	(let ((olde (cdr (assoc (car e) old-direct)))) 
	  (loop for dd on (cdr e) until (eq dd olde) #+ignore unless
		#+ignore ; no inherits allowed now ...
		(and (eq (tuptv (setq tuple (updtuple (setq d (car dd))))) 'inherit)
		     (eql (let ((delta nil) (currentcx (updcx d)))  ;previous
			    (apply (function valueincurrentcx)
				   (tuprel tuple) (tupargs tuple)))
			  (setq value
				(let ((delta Direct) #+ignore (currentcx (updcx d))) ;new
				  ; *** is this right with indexdelta? ***
				  (apply (function valueincurrentcx)
					 (tuprel tuple) (tupargs tuple))))))
		do
		(setq tuple (updtuple (setq d (car dd))))
		(add-to-delta #+ignore
			      (cond ((eq (tuptv tuple) 'inherit)
				     (make-updaterec :updreason d
						     ; :updcx (updcx d)
						     :updtuple
						     (make-tuple :tuprel (tuprel tuple)
								 :tupargs (tupargs tuple)
								 :tuptv value)))
				    (t d))
			      d
			      (tuprel tuple))))))

; Maintained and derived relations may depend on each other.  We compute their
; updates according to a partial order which guarantees that all changes
; to a relation will be computed before that relation is used to compute changes
; to any other relation.  
; later we should try to avoid recomputing from one cycle to the next
; first we try to recognize that the results are the same
(defun compute-maintain-indirect (updates &aux |MIRelsDone | |MIRelsUndone |
					  |MIDelayed | |MIProgress | |Activations |
					  activationtrees entry foundentries)
  ; updates arg is now actually delta
  (declare (special |MIRelsDone | |MIRelsUndone | |MIDelayed | |MIProgress |
		    |MIQueue | history |Indirect | |Maintain | |Activations |
		    indirecttrees activationtrees explicit-MI old-delta
		    old-maintain old-indirect *rule-cycle*))
  (loop for e in updates
	; since we really only want Direct tuples we filter these from delta 
	unless (assoc (car e) old-maintain)
	unless (assoc (car e) old-indirect) do
	(let ((old (cdr (assoc (car e) old-delta))))
	  (loop for u on (cdr e)
		until (when (eq u old) (push old foundentries))
		do (enqueue-update (car u)))))
  (unless (or |MIQueue | explicit-MI) (return-from compute-maintain-indirect nil))
  (remove-indirect-computed)
  (remove-MI-index) ; first remove maintain/indirect from indexdelta
  (setq |Indirect | nil |Maintain | nil indirecttrees nil)
  (loop for u in explicit-MI do
	(add-to-delta u (tuprel (updtuple u)))
	(pushassoc u (tuprel (updtuple u)) |Maintain |) ; assume it's not already there?
	(enqueue-update u))
  ; recompute each time - not necessarily monotonic!!
  ; queue elements are either
  ; (function derived-rel) where fn is to compute updates to derived rel
  ;  or (matchnode . inputs)
  ; Relstatus stores status of relations (described in rel-status)
  (loop for e in foundentries do
	(loop for u in e do (enqueue-update u)))
  (setq |MIDelayed | |MIQueue |) ; for other reasons we enqueue to queue, not delayed
  (when |MIQueue |
    (setq do-whostates t)
    (with-whostate "DerivedRels" 
      (loop while |MIDelayed | do
	    (setq |MIQueue | |MIDelayed | |MIDelayed | nil |MIRelsUndone | nil)
	    (loop while |MIQueue | do (do-step (pop |MIQueue |)))	; may add to undone
	    (when (and |MIDelayed | |MIRelsUndone |)
	      (TrytoProveRelsDone |MIRelsUndone | |MIDelayed |))
	    (cond (|MIProgress | (setq |MIProgress | nil))
		  (t (error "no progress can be made -- ~s" |MIDelayed |))))))
  ; this will be of vanishing utility when we can avoid recomputing
  (setq old-delta (loop for x in delta collect (cons (car x) (cdr x))))
  (setq |Indirect |
	(loop for x in |Indirect | collect
	      (cond ((eq x (setq entry (assoc (car x) old-indirect))) x)
		    ((and (= (length x) (length entry))
			  (loop for y in (cdr x) as z in (cdr entry) always
				(and (eq (tuptv (updtuple y)) (tuptv (updtuple z)))
				     (equal (tupargs (updtuple y)) (tupargs (updtuple z))))))
		     entry)
		    (t x))))
  (setq |Maintain |
	(loop for x in |Maintain | collect
	      (cond ((eq x (setq entry (assoc (car x) old-maintain))) x)
		    ((and (= (length x) (length entry))
			  (loop for y in (cdr x) as z in (cdr entry) always
				(and (eq (tuptv (updtuple y)) (tuptv (updtuple z)))
				     (equal (tupargs (updtuple y)) (tupargs (updtuple z))))))
		     entry)
		    (t x)))))

(defun TryToProveRelsDone (rels steps &aux queue ans next delta)
  (declare (special delta)) ; do this as of previous state
  ; try to prove that rels cannot be affected by steps
  ; these rels are either maintained or depend on other rels
  (declare (special |MIRelsDone | |MIProgress |))
  (loop for s in steps do
	(cond ((matchnode-p (car s)) (pushnew (car s) queue))
	      (t
	       ; *** obviously obsolete ***
	       ;(loop for x in (sixth s) do (pushnew x queue))
	       ;(loop for x in (fifth s) do (pushnew x queue))
	       (push (cadr s) queue)))
	#+ignore 
	(pushnew (cond ((matchnode-p (car s)) (car s)) (t (fourth s))) queue))
  ; (print queue)
  (loop while (setq next (pop queue)) 
	unless (member next ans) do
	(unless (matchnode-p next) (push next ans))
	(setq queue (nconc (cond ((matchnode-p next)
				  (maintainedrels-affected-by-node next))
				 (t (nconc (get-depends-on2 next)
					   (maintainedrels-affected-by-rel next))))
			   queue)))
  ; (print ans)
  (loop for rel in rels unless (member rel ans) do
	(push rel |MIRelsDone |) (setq |MIProgress | t)))

#+ignore
(defun get-new-entries-from (rel) ;like enqueue update
  (declare (special |PAQueue |))
  (setq |PAQueue | (nconc |PAQueue | (get-depends-on2 rel)))
  ; setq in case it was nil
  (loop for node in (get-structure-property rel 'deletematchers)
	when (member :maintain (matchactive node))
	unless (member node (assoc :maintain suspended-matchnodes))
	do (push node |PAQueue |))
  (loop for node in (get-structure-property rel 'addmatchers)
	when (member :maintain (matchactive node))
	unless (member node (assoc :maintain suspended-matchnodes))
	do (push node |PAQueue |)))

(defun do-step (step)
  (declare (special |MIProgress | |MIDelayed |))
  (and *watch-maintain-indirect* (funcall *watch-maintain-indirect* step))
  (cond ((matchnode-p (car step))
	 (cond ((loop for rel in (matchrels (car step)) always
		      (eq (relstatus rel) 'done))
		(do-match-step step)
		(setq |MIProgress | t))
	       (t (push step |MIDelayed |))))
	; otherwise it's an add/deltrigger
	((let (delta) ; again in previous state
	   (loop for rel in (get-depends-on (second step))
		 always (eq (relstatus rel) 'done)))
	 (do-trigger-step step)
	 (setq |MIProgress | t))
	(t (push step |MIDelayed |))))

; Relations are either done: delta contains all changes to the relation
; or maybe-not: it wasn't provably done when first checked.
; we go by cycles in which we throw out the maybe-not's and try to find
; something to do.  If nothing can be found there seem to be circular 
; dependencies (at the relation level - we cannot tell about the tuple
; level which is a reason for prohibiting recursive definitions)
(defun relstatus (rel &aux delta)
  (declare (special delta)) ; do it w.r.t. previous state
  (declare (special |MIRelsDone | |MIRelsUndone |))
  (cond ((member rel |MIRelsDone |) 'done)
	((member rel |MIRelsUndone |) 'undone)
	((or (get-depends-on rel) (maintain-mnode rel))
	 (push rel |MIRelsUndone |) 'undone)
	(t (push rel |MIRelsDone |) 'done)))

#+ignore ; formerly contained
(((matchrels d2)
  (push rel |MIRelsDone |) ; depends on no relation
  'done)
 ((setq temp
	(some #'(lambda (rel)
		  (and (not (eq (relstatus rel) 'done)) rel))
	      depend)) ; if it's not done we have to wait for it
  (push (cons rel temp) |MIRelStatus |)
  'waiting)
 ; otherwise, the relation is either waiting for something to add its
 ; tuples to Indirect or for something to add its tuples to Maintain
 (d1 ;waiting for indirect
   (cond ((waiting-for-indirect rel)
	  (push (cons rel t) |MIRelStatus |)
	  'ready)
	 (t (push (cons rel nil) |MIRelStatus |)
	    'done)))
 ; waiting for something to maintain - is there anything in the queue?
 (d2
   (cond ((waiting-for-maintain rel)
	  (push (cons rel t) |MIRelStatus |)
	  'ready)
	 (t (push (cons rel nil) |MIRelStatus |)
	    'done))))
#+ignore
(defun waiting-for-indirect (rel)
  ; *** we currently assume that addtriggers etc. will relate the primitives
  ; to the derived.  At the cost of an occasional transitive closure here
  ; we could allow addtriggers to relate derived to other derived rels. ***
  (declare (special |MIQueue | |MIDelayed |))
  (or (loop for x in |MIQueue | thereis (eq rel (fourth x)))
      (loop for x in |MIDelayed | thereis (eq rel (fourth x)))))

#+ignore
(defun waiting-for-maintain (rel &aux mnode predecessors)
  (declare (special |MIQueue | |MIDelayed |))
  ; cache predecessor nodes of the matchnode ...
  (or (setq predecessors (get-structure-property (setq mnode (maintain-mnode rel))
						 'predecessor*))
      (put-structure-property mnode (setq predecessors (get-predecessor* mnode))
			      'predecessor))
  (or (loop for x in |MIQueue | thereis (member (car x) predecessors))
      (loop for x in |MIDelayed | thereis (member (car x) predecessors))))

#+ignore
(defun get-predecessor* (mnode &aux queue ans)
  ; primitive transitive closure computation
  (setq queue (list mnode))
  (loop while (setq mnode (pop queue)) do
	(cond ((member mnode ans))
	      (t (push mnode ans)
		 (setq queue (append (matchpredecessors mnode) queue)))))
  ans)

(defun do-trigger-step (step &aux rel relevance addp delp |Updates |
			     (|UpdateStatus | 'trigger))
  (declare (special |Updates | |UpdateStatus |
		    delta |Indirect | indirecttrees))
  (setq rel (cadr step) relevance (relevant-updates rel)
	addp (loop for x in (car relevance) thereis
		   (not (member x suspended-rule-classes)))
	delp (loop for x in (cdr relevance) thereis
		   (not (member x suspended-rule-classes))))
  (funcall (car step) rel addp delp)
  (loop for u in |Updates |
	; only record "interesting" updates (that can lead to rules)
	when (and (eq (tuprel (updtuple u)) rel)
		  (if (tuptv (updtuple u)) addp delp))
	unless (tuple-already-seen u (updtuple u) (list indirecttrees)) do
	; complain if cx-sensitive rel triggers or
	; is triggered by cx-insensitive (?)
	(setf (updreason u) (list 'trigger (car step) (updreason u)))
	(add-to-delta u (tuprel (updtuple u)))
	(pushassoc u (tuprel (updtuple u)) |Indirect |)
	(setq indirecttrees (add-update-tree u (updtuple u)
					     indirecttrees nil))
	(enqueue-update u))
  #+ignore (decache-relstatus (car step))
  #+ignore (decache-relstatus (fourth step)))
;be sure trigger results are really changes (not true before) - user's job?
; abort if any of these produces contradiction with Direct+Again+Inherited+indirect
;   (should be impossible if primitive vs. derived is observed)
; Note that we do need to check for redundant updates, e.g., if I atomically
; add (R a b) and (R a c) and am maintaining tclosure of R ...

; used for computing starts of derived rels
(defun compute-from-triggers (rel tv &aux fns add-p
				  |Updates | (|UpdateStatus | 'trigger))
  (declare (special |Updates | |UpdateStatus | delta |Indirect | indirecttrees))
  (loop for (stored-rel stored-tv fn derived-tv) in (get-triggers-of rel)
	when (eq derived-tv tv) do
	(progn stored-rel stored-tv ;; still doesn't avoid warnings
	       ;; evidently I'm supposed to replace the vars with NIL
	       (pushnew fn fns)))
  (loop for f in fns do (funcall f rel tv (not tv)))
  ; this will force computation of whatever those fn need (all the predecessor rels)
  (loop for u in |Updates |
	when (eq (tuprel (updtuple u)) rel)
	when (eq tv (tuptv (updtuple u))) do
	(setf (updreason u) 'start-generated)
	(multiple-value-setq (indirecttrees add-p)
	  (add-update-tree u (updtuple u) indirecttrees t))
	(when add-p
	  (add-to-delta u (tuprel (updtuple u)))
	  (pushassoc u (tuprel (updtuple u)) |Indirect |))))

;ditto
(defun add-derived-to-delta (rel tv &rest tuple &aux upd add-p)
  (declare (special |Indirect | indirecttrees))
  (setq upd (make-updaterec :updreason 'start-generated
			    :updtuple (make-tuple :tuprel rel :tuptv tv
						  :tupargs (copy-list tuple))))
  (multiple-value-setq (indirecttrees add-p)
    (add-update-tree upd (updtuple upd) indirecttrees t))
  (when add-p
    (add-to-delta upd rel)
    (pushassoc upd rel |Indirect |)))

(declaim (special class-to-activate))

(defun do-match-step (step &aux (class-to-activate :maintain) ; special
			   entry acttree (node (car step)) (tuple (cdr step)))
  (declare (special |Activations | |MIQueue | activationtrees |Indirect |
		    indirecttrees))
  (or (setq entry (assoc node |Activations |))
      (push (setq entry (list node)) |Activations |))
  (or (setq acttree (cdr (assoc node Activationtrees)))
      (push (cons node (setq acttree (createtree))) Activationtrees))
  (loop for output in (do-matchcode node tuple)
	unless (do-matchcompare node output acttree)
	do (treeadder output acttree (matchcompare node))
	(push output (cdr entry))
	(loop for successor in (matchsuccessors node)
	      when (member :maintain (matchactive successor))
	      unless #+ignore ; old way
	      (member successor (assoc :maintain suspended-matchnodes))
	      (eql generation# (get-structure-property successor :maintain))
	      do (push (cons successor output) |MIQueue |))
	; now do the maintain rules of the node (usually none, occasionally one)
	(loop for rule in (let (delta) (matchmaintains node))
	      unless (member rule suspended-rules) do
	      (let
		(|Updates | (|UpdateStatus | 'maintain))
		(declare (special |Updates | |UpdateStatus | delta |Maintain |))
		(domaintainrule rule output)
		(loop for u in |Updates | do
		      ; assume it's not already there:
		      ;  this code due to maintainrules which only happen once
		      ; complain if cx-sensitive rel triggers or
		      ; is triggered by cx-insensitive (?)
		      (setf (updreason u) (list :maintain (updreason u)))
		      (add-to-delta u (tuprel (updtuple u)))
		      (pushassoc u (tuprel (updtuple u)) |Maintain |)
		      (enqueue-update u)
		      #+ignore (decache-relstatus (tuprel (updtuple u))))))
	; now if the node represents a defined rel add it to indirect
	(block defined-update
	  (let ((wff (matchwff node)) rel u negated)
	    (unless (eq (car wff) 'start) (return-from defined-update nil))
	    (setq wff (cadr wff))
	    (when (eq 'not (car wff)) (setq negated t) (setq wff (cadr wff)))
	    (unless (and (dbobject-p (setq rel (car wff)))
			 (defined-p rel))
	      (return-from defined-update nil))
	    (unless (equal (matchvars node) (cdr wff))
		    (return-from defined-update nil))
	    ; we have a defined rel update node
	    (setq u (make-updaterec ; :updcx *globalcx*
		      :updreason :matched
		      :updtuple (make-tuple :tuprel rel :tupargs output
					    :tuptv (not negated))))
	    (unless (tuple-already-seen u (updtuple u) (list indirecttrees))
	      ;; CANNOT ADD TO DELTA because it's not complete!!
	      ; if and when start/cease is computed it will all be added
	      ;(add-to-delta u (tuprel (updtuple u)))
	      ;(pushassoc u (tuprel (updtuple u)) |Indirect |)
	      ;(setq indirecttrees (add-update-tree u (updtuple u) indirecttrees nil))
	      (enqueue-update u))))))

#+ignore  ; instead of this we just decache it all between cycles
(defun decache-relstatus (rel)
  (declare (special |MIRelStatus |))
  ;something about rel is discovered - is it done?
  ; remove cached value of source rel and whatever is waiting for it
  (setq |MIRelStatus |
	(delete rel |MIRelStatus | :test
		#'(lambda (rel el)
		    (and (cdr el) (or (eq rel (car el)) (eq rel (cdr el))))))))

(defvar maintaining-relevant-updates)
(setq maintaining-relevant-updates nil)
; we'll turn on this switch when the rule is defined
(defun relevant-updates (rel)
  ; what kind of rules could notice changing a tuple of rel to tv
  ; result is cons of add classes, del classes
  ; this is only used for derived rels
  ; note that :maintain is as good as all ...
  (or (get-structure-property rel 'relevant-updates)
      (let (adds dels)
	(loop for n in
	      (get-structure-property rel 'addmatchers) do
	      (loop for a in (matchactive n) do (pushnew a adds)))
	(loop for n in
	      (get-structure-property rel 'deletematchers) do
	      (loop for a in (matchactive n) do (pushnew a dels)))
	(loop for (tv fn derived-rel derived-tv) in (get-triggers rel) do
	  ;; evidently have to change fn to nil to avoid warning
	      ;(tv fn derived-rel derived-tv) s.t.
	      ;(trigger rel tv fn derived-rel derived-tv)
	      (let ((z (relevant-updates derived-rel)))
		(loop for x in (if derived-tv (car z) (cdr z)) do
		      (if tv (pushnew x adds) (pushnew x dels)))))
	(if maintaining-relevant-updates
	    (put-structure-property rel (cons adds dels) 'relevant-updates)
	    (cons adds dels)))))

(defun enqueue-update (u &aux tuple delta rel tv nodes new)
  (declare (special |MIQueue | |MIDelayed | delta))
  (setq rel (tuprel (setq tuple (updtuple u)))
	tv (tuptv tuple)
	nodes (get-structure-property
		rel (case tv ((nil) 'deletematchers)
			  (t 'addmatchers))))
  (loop for ;(fn derived-rel derived-tv) s.t. (trigger rel tv fn derived-rel derived-tv)
	(tvx fn derived-rel derived-tv) in (get-triggers rel) when (eq tv tvx)
	when (loop for c in (if derived-tv ;; former "tv" is wrong ...
				(car (relevant-updates derived-rel))
				(cdr (relevant-updates derived-rel)))
		   thereis (not (member c suspended-rule-classes)))
	; Since maintain/indirect is being recomputed from ground zero we
	; only have to worry about new updates, not updates from previous
	; cycles that disappear.
	unless
	(progn (setq new (list fn derived-rel))
	       (or (member new |MIQueue | :test 'equal)
		   (member new |MIDelayed | :test 'equal)))
	do 
	(push new |MIQueue |))
  #+ignore ; previous version
  (loop for code-target in
	(get-add-del-triggers rel tv)
	; optimization: only compute triggers if they can lead to a rule
	; thus delta will no longer contain ALL such tuples
	; like defined rels, these are computed when accessed anyway
	; note that we must compute them if they lead to ANY type of rule, though
	; - not dormant rules, though
	;  - for now we do not make this optimization so as to simplify map-updates
	when (let ((newrel (cadr code-target)))
	       (or (loop for n in (get-structure-property newrel 'addmatchers)
			 thereis (matchactive n))
		   (loop for n in (get-structure-property newrel 'deletematchers)
			 thereis (matchactive n))
		   ; or if it triggers another rel (which we could check further triggers..)
		   (get-add-del-triggers (cadr code-target) t)
		   (get-add-del-triggers (cadr code-target) nil)))
	do (push (list rel (car code-target) tuple (cadr code-target))
		 |MIQueue |))
  (loop for node in nodes
	when (member :maintain (matchactive node))
	unless #+ignore (member node (assoc :maintain suspended-matchnodes))
	(eql generation# (get-structure-property node :maintain))
	do (push (cons node (tupargs tuple)) |MIQueue |)))

(defvar *index-threshold* 6)

; we keep this around in order to experiment by temporarily setting delta
(defun compute-index-delta ()
  (loop for d in delta when (geq-length d *index-threshold*) do
	(push (cons (car d)
		    (loop for x below (arity* (car d)) collect
			  (make-hash-table :test
			     (let ((compare (get-c-and-c (car d) x)))
			       (if (listp compare) (car compare) compare)))))
	      indexdelta)
	(loop for upd in (cdr d) do
	      (let ((tuple (canonicalize-tuple (car d) (tupargs (updtuple upd)))))
		(loop for arg in tuple as table in (cdar indexdelta) do
		      (let ((data (gethash arg table)))
			(or data (setf (gethash arg table) (setq data (list 0))))
			(incf (car data))
			(push upd (cdr data))))))))

(defun add-to-delta (upd rel &aux entry)
  (pushassoc upd rel delta)
  (cond ((setq entry (assoc (setq rel (tuprel (updtuple upd))) indexdelta))
	 ; add this one
	 (let ((tuple (canonicalize-tuple rel (tupargs (updtuple upd)))))
		(loop for arg in tuple as table in (cdr entry) do
		      (let ((data (gethash arg table)))
			(or data (setf (gethash arg table) (setq data (list 0))))
			(incf (car data))
			(push upd (cdr data))))))
	((geq-length (setq entry (assoc rel delta)) *index-threshold*)
	 ; add all of them
	(push (cons rel
		    (loop for x below (arity* rel) collect
			  (make-hash-table :test
			     (let ((compare (get-c-and-c rel x)))
			       (if (listp compare) (car compare) compare)))))
	      indexdelta)
	(loop for upd in (cdr entry) do
	      (let ((tuple (canonicalize-tuple rel (tupargs (updtuple upd)))))
		(loop for arg in tuple as table in (cdar indexdelta) do
		      (let ((data (gethash arg table)))
			(or data (setf (gethash arg table) (setq data (list 0))))
			(incf (car data))
			(push upd (cdr data)))))))))

(defun remove-indirect-computed ()
  (declare (special |Indirect | indexdelta indirect-computed))
  (setq delta (loop for d in delta unless (assoc (car d) indirect-computed)
		    collect d))
  (setq indexdelta (loop for d in indexdelta unless
			 (assoc (car d) indirect-computed)
			 collect d))
  (setq indirect-computed nil))

(defun remove-MI-index () ;(&aux entry)
  (declare (special |Maintain | |Indirect |))
  ; since it's relations that are indirect or maintained, we
  ; never have to look at the tuples - just remove the alist entries
  ; while we're at it, do the same for delta
  (setq delta (loop for d in delta unless
		    (or (assoc (car d) |Maintain |) (assoc (car d) |Indirect |))
		    collect d))
  (setq indexdelta (loop for d in indexdelta unless
			 (or (assoc (car d) |Maintain |) (assoc (car d) |Indirect |))
			 collect d))
  #+ignore
  (loop for MI in (list |Maintain | |Indirect |) do

	(loop for d in MI when (setq entry (assoc (car d) indexdelta)) do
	      (loop for upd in (cdr d) do
		    (let ((tuple (canonicalize-tuple (car d) (tupargs (updtuple upd)))))
		      (loop for arg in tuple as table in (cdr entry) do
			    (let ((data (gethash arg table)))
			      (or data (error "trying to delete what's not there: ~A" upd))
			      (decf (car data))
			      (setf (cdr data) (delete upd (cdr data) :count 1)))))))))
	
(defun geq-length (list length)
  (loop while (and (> length 0) (consp list)) do
	(setq list (cdr list))
	(setq length (- length 1)))
  (= 0 length))

;(defvar timings nil)

(defun compute-activations (&aux changedrels kept)
  (declare (special old-ddelta directdelta old-indirect old-maintain
		    |Activations | activationtrees)) ;|Indirect | |Maintain |
  ; this is specific to consistency rules
  ; find activations of matchnodes - optimized to use previous cycle
  ;(push (get-internal-run-time) timings)
  (loop for entry in directdelta
	unless (eq (cdr entry) (cdr (assoc (car entry) old-ddelta)))
	do (push (car entry) changedrels))
  (loop for entry in old-ddelta
	;; also notice any that changed back to no change !!
	unless (assoc (car entry) directdelta)
	do (push (car entry) changedrels))
  ;; old-ddelta updates will only be redone (below) if needed 
  ; since directdelta is only pushed to we simply check the front
  ;; directdelta now includes the others
  #+ignore
  (loop for entry in |Indirect |
	unless (eq (cdr entry) (cdr (assoc (car entry) old-indirect)))
	do (pushnew (car entry) changedrels))
  #+ignore
  (loop for entry in |Maintain |
	unless (eq (cdr entry) (cdr (assoc (car entry) old-maintain)))
	do (pushnew (car entry) changedrels))
  ; for now assume that all such rels have to be retriggered
  ; otherwise we'd have to see whether the set of updates was the same
  ; start with the activations that were not affected
  ;(push (get-internal-run-time) timings)
  (loop for A in |Activations | do
	(cond ((loop for r in (matchrels (car A)) thereis (member r changedrels))
	       (rplacd A nil))
	      (t (push A kept))))
  (loop for A in activationtrees do
	(cond ((loop for r in (matchrels (car A)) thereis (member r changedrels))
	       (rplacd A nil))))
  ; now we can trigger the actual changes
  ;(push (get-internal-run-time) timings)
  (loop for e in directdelta when (member (car e) changedrels) do
	(loop for u in (cdr e) do
	      (and *watch-consistency-trigger* (funcall *watch-consistency-trigger* u))
	      (activate-from-update u :consistency)))
  #+ignore
  (loop for e in |Indirect | when (member (car e) changedrels) do
	(loop for u in (cdr e) do
	      (and *watch-consistency-trigger* (funcall *watch-consistency-trigger* u))
	      (activate-from-update u :consistency)))
  #+ignore
  (loop for e in |Maintain | when (member (car e) changedrels) do
	(loop for u in (cdr e) do
	      (and *watch-consistency-trigger* (funcall *watch-consistency-trigger* u))
	      (activate-from-update u :consistency)))
  ; now activate the successors of those kept
  ;(push (get-internal-run-time) timings)
  (loop for A in kept when (cdr a) do ; a good cheap filter
	(loop for next in (matchsuccessors (car A))
	      when (member :consistency (matchactive next))
	      unless (assoc next kept) ;; this is more expensive
	      unless #+ignore (member next (assoc :consistency suspended-matchnodes))
	      (eql generation# (get-structure-property next :consistency)) do
	      (loop for outputs in (cdr A) do
		    (MatchActivate next outputs :consistency))))
  ;(push (get-internal-run-time) timings)
  )

(defun activate-from-update (upd ruletype &aux (tuple (updtuple upd)))
  (loop for node in
	(get-structure-property (tuprel tuple)
				(case (tuptv tuple)
				  ((nil) 'deletematchers)
				  (t 'addmatchers)))
	when (member ruletype (matchactive node))
	unless #+ignore (member node (assoc ruletype suspended-matchnodes))
	(eql generation# (get-structure-property node ruletype))
	do (matchactivate node (tupargs tuple) ruletype)))

(defvar *advice-for-every-transition* nil)

(defun do-advice-for-every-transition (&aux (|UpdateStatus | 'every-transition-advice))
  (when delta
    (loop for *current-rule* in *advice-for-every-transition*
	  unless (member *current-rule* suspended-rules)
	  do (funcall *current-rule*))))

(defmacro enqueue-automation (&rest body)
  `(if (or (eq |UpdateStatus | 'automationgenerating)
	   (eq |UpdateStatus | 'every-transition-advice))
       (push (list *current-rule* (function (lambda () ,. body)) nil)
	     *automation-queue*)
       (error "enqueue-automation can only be executed from an automation generator")))

(defvar-resettable last-recorded-transition nil)
;; when we stop recording we set this so we can record 
;; the fact that unrecorded events took place.

(defun record-history (history)
  (cond ((listp global-history)
	 (when block-undo (put-structure-property history t 'block-undo))
	 (dolist (cc (consistency-cycles history))
	       (setf (activations cc) nil))	; optimize out the space
	 (push history global-history)
	 (put-structure-property history (current-process-name) 'process)
	 (when *max-history-length*
	   (let ((tail (nthcdr (1- *max-history-length*) global-history)))
	     (when tail (rplacd tail nil)))))
	(last-recorded-transition
	 (put-structure-property last-recorded-transition t 'unrecorded-history-follows))))

(defvar dodbupdates-delta #+ignore "illegal-delta" nil)
; that goes along with use of memo rather than loadmemo
; with memo you sometimes have to call relationp during dodbupdates
; in order to fill in a memo for the update code

(Defvar DangerMessage
  "~%You are aborting out of a critical section in which the ~
  (AP) database is being written.  This could leave it in ~
  an inconsistent state!  It would be advisable to try using ~
  (history) to undo backward to the previous state.~%")


(defun dodbupdates (&aux (|UpdateStatus | 'primitive) (delta dodbupdates-delta))
  (declare (special |Direct | |Maintain |))
  (writing
    (with-whostate "Modify Database"
      (let ((DangerousP t))
	(unwind-protect
	    (progn
	      (flet ((do-updates (r &aux fn)
		       ;; now have to do BOTH set and single updates
		       ;; also the update fns are now LISTS
		       (when (setq fn (updcode-set (cadr r)))
			     ;; assume they're all the same ...
			   (let (adds dels tup)
			     (loop for u in (cdr r) do
				   (if (tuptv (setq tup (updtuple u)))
				       (push (tupargs tup) adds)
				       (push (tupargs tup) dels)))
			     (loop for f in fn do
				   (funcall f (car r) adds dels))))
		       (when (updcode-single (cadr r))
			     (loop for d in (cdr r) do
				   (if (not (consp (updcode-single d)))
				       (apply (updcode-single d)
					      (tuprel (updtuple d))
					      (tupargs (updtuple d)))
				     (loop for updater in (updcode-single d) do
					   (apply updater
						  (tuprel (updtuple d))
						  (tupargs (updtuple d)))))
				   ))))
		(loop for r in |Maintain | do (do-updates r))
		(loop for r in |Direct | do (do-updates r)))
	      (setq dangerousp nil))
	  (when DangerousP
		(warn DangerMessage) (throw 'atomic-retry nil)))))))

#+ignore ; former inside of dodbupdates
	   (loop for class in (list |Maintain | |Direct |) do
		 (loop for e in class do
		       (loop for d in (cdr e) do
			     (and *watch-do-update* (funcall *watch-do-update* d))
			     (cond ((context-sensitive (car e))
				    (let ((currentcx (updcx d)))
				      ; must be bound even if global
				      (apply (updcode d)
					     (tuprel (updtuple d))
					     (tupargs (updtuple d)))))
				   ((eql *globalcx* (Updcx d))
				    (apply (updcode d)
					   (tuprel (updtuple d))
					   (tupargs (updtuple d))))
				   (t (updateincx d))))))

; This should only happen if an error occurs in dodbupdates and
; the user tries to abort rather than fix it.



; for my own debugging convenience ...
(defun showdelta (&key (field 'delta) (record 0))
"Field is one of direct, directdelta, indirect, maintain, again, delta, activations.
Record can either be a number, meaning (car (nth n global-history) or a list of the
values of the fields listed above"
  (when (numberp record)
    (setq record (car (consistency-cycles (nth record global-history)))))
  (case field 
    (direct (direct record))
    (directdelta (directdelta record))
    (indirect (indirect record))
    (maintain (maintain record))
    (again (again record))
    (delta (delta record))
    (activations (activations record))
    (t '(direct directdelta indirect maintain again delta activations))))

(defun remove-forms-from-wff (wff env &aux evlvars boundvars)
  (declare (special boundvars))
  (values
   (flet ((pushit (x &optional (bool (or (member x boundvars)
					 (constantp* x :env env))))
	    (if bool
		x
		(let ((g (gensym "G")))
		  (push (cons g x) evlvars)
		  g))))
     (map-copy-wff wff :environment env
	:primitive-wff #'(lambda (&rest original)
			   (cons (car original)
				 (mapcar #'pushit (cdr original))))
	:funcall-wff #'(lambda (rel &rest args)
			 `(funcall ,(pushit rel nil) ,.(mapcar #'pushit args)))
	:apply-wff #'(lambda (rel &rest args)
		       `(apply ,(pushit rel nil)
			       ,. (mapcar #'pushit (butlast args))
			       ,(pushit (first (last args)) nil)))
	:quantified-wff
	#'(lambda (q v w &aux (boundvars (append (mapcar #'variablename v)
						 boundvars)))
	    (declare (special boundvars))
	    (list q v (map-wff-internal w)))))
   (reverse evlvars)))

(defmacro-displace insist (optional-explanation-string
			    &rest wff &environment env)
  (let (newwff evlvars)
    ; have to allow variables bound at insist site 
    (cond ((not (stringp optional-explanation-string))
	   (push optional-explanation-string wff)
	   (setf optional-explanation-string "")))
    (multiple-value-setq (newwff evlvars) (remove-forms-from-wff wff env))
    (setf newwff (vars&rels-to-names-wff newwff))
    `(atomic
       (checkrequireallowed ',newwff)
       (push
	 (list
	   #'(lambda ,(mapcar #'first evlvars)
	       (?? . ,newwff))
	   ,optional-explanation-string
	   '(lambda ,(mapcar #'first evlvars)
	      (?? . ,newwff))
	   ,.(mapcar #'rest evlvars))
	 |Requirements |)
       nil)))
; return nil instead of some huge form
;; Why not use closures? When someone does (insist P x) we want the current
;    value of x to be used, even if x is later reset.
;  - Is this really better than using the closure and insisting for the final values?
;; Why not use nilary functions rather than forms to eval?  fine

(defun checkrequireallowed (wff)
  (case |UpdateStatus |
    ((nil) (error "Attempt to insist when not in an Atomic -- ~S" wff))
    (primitive (error "Attempt to insist from primitive update code -- ~s"
		      wff))
    (checking
      (error "Attempt to insist in a primitive checker ~%~s" wff))
    (report-inconsistency
       (error "attempt to insist when reporting inconsistency"))
    (every-transition-advice
       (error "attempt to insist while doing advice for every transition"))
    (automationgenerating
       (error "attempt to insist while generating automation invocations"))
    (responder-search
       (error "attempt to insist while computing a dynamic responder for a rule"))
    ((trigger transparent maintain)
      (error "ap5 error: insists should never happen with updatestatus ~A" |UpdateStatus |))
    ((consistency definition atomic) nil)
    (t (error "Unknown UpdateStatus -- ~s"  |UpdateStatus |))))

(defun abort (tag &optional format-string &rest reason)
  (declare (special history update))
  ;; tag should be either a condition object, (an instance of atomic-abort
  ;; or a subtype thereof), or a symbol.
  (if (symbolp tag)
      (setf reason
	    #+ignore (cons tag (cons format-string (copy-list reason)))
	    ; hope this works on symbolics
	    (make-condition
	     (if (ignore-errors (subtypep tag 'atomic-abort))
		 tag
	       'atomic-abort)
	     :tag tag :description format-string
	     :abortdata reason))
    (setf reason tag))
  #+no-conditions (setf reason (list reason)) ; for later append
  ;; needed for passing out stack list
  (flet ((return-with-added-reasons (&rest adds)
	   ; hope this works on symbolics
	   #+no-conditions (setf reason (append reason adds))
	   #-no-conditions
	   (setf (atomic-abort-abortdata reason)
		 (append (atomic-abort-abortdata reason) adds))
	
	   (throw '|OuterAtomic |
		      ; again not tried for symbolics
		      (values '|Abort | reason)
		      #+ignore 
		      (apply #'values '|Abort | `( ,@reason ,@adds)))))
      (flet ((illegal-abort (help)
	       (error "Attempt to Abort ~a.~%~a" help reason)))
	 (case |UpdateStatus |
	       ((nil) (illegal-abort "when not in an Atomic"))
	       (primitive (illegal-abort "from primitive update code"))
	       (Report-Inconsistency (illegal-abort "from code to report inconsistency"))
	       (automationgenerating (illegal-abort "from AutomationGenerating code"))
	       (atomic
		(return-with-added-reasons
		 "from code in atomic" |Updates |
		 (make-history-record
		  :generation# (incf generation#)
		  :prev-gen# (when (consp global-history)
				   (generation# (car global-history))))))
	       (every-transition-advice
		(illegal-abort "from advice for every transition"))
	       (trigger (illegal-abort "from trigger code"))
	       (checking (illegal-abort "from checking code"))
	       ((maintain consistency)
		(put-structure-property history t '|InAtomicUpdate|)
		(put-structure-property history |Requirements | 'requirements)
		(return-with-added-reasons |UpdateStatus | history))
	       (definition
		 (when (boundp '|InAtomicUpdate|)
		       (put-structure-property history t '|InAtomicUpdate|))
		 (put-structure-property history |Requirements | 'requirements)
		 (return-with-added-reasons |UpdateStatus | update history))
	       (transparent
		(put-structure-property history t '|InAtomicUpdate|)
		(put-structure-property history |Requirements | 'requirements)
		(return-with-added-reasons history))
	       (t (error "Unknown UpdateStatus -- ~s"  |UpdateStatus |))))))

#+ignore ; previous version
(defun abort (tag format-string &rest reason)
  (declare (special history update))
  (setq reason (cons tag (cons format-string (copy-seq reason))))
  ;; needed for passing out stack list
  (case |UpdateStatus |
    ((nil) (error "Attempt to Abort when not in an Atomic~%~A" reason))
    (primitive (error "Attempt to Abort from primitive update code~%~A"
		      reason))
    (Report-Inconsistency
      (error "attempt to abort from code to report inconsistency"))
    (automationgenerating
      (error "attempt to abort from AutomationGenerating code"))
    (atomic (throw '|OuterAtomic |
	      (values-list
		`(|Abort | ,@reason "from code in atomic" ,|Updates |
			   ,(make-history-record
			      :generation# (incf generation#)
			      :prev-gen# (when (consp global-history)
					   (generation# (car global-history))))))))
    (every-transition-advice
      (error "attempt to abort from advice for every transition"))
    (trigger
      (error "attempt to abort from trigger code"))
    (checking
      (error "attempt to abort from checking code (which should instead return nil)"))
    ((maintain consistency)
     (put-structure-property history t '|InAtomicUpdate|)
     (put-structure-property history |Requirements | 'requirements)
     (throw '|OuterAtomic | (values-list
			      `(|Abort | ,@reason ,|UpdateStatus |
					 ,history))))
    (definition
     (when (boundp '|InAtomicUpdate|)
       (put-structure-property history t '|InAtomicUpdate|))
     (put-structure-property history |Requirements | 'requirements)
     (throw '|OuterAtomic | (values-list
			      `(|Abort | ,@reason ,|UpdateStatus |
					 ,update ,history))))
    (transparent
      (put-structure-property history t '|InAtomicUpdate|)
      (put-structure-property history |Requirements | 'requirements)
      (throw '|OuterAtomic | (values-list `(|Abort | ,@reason ,history))))
    (t (error "Unknown UpdateStatus -- ~s"  |UpdateStatus |))))



#||
(TRANSACTION . forms) -- macro
provides an "undoable" transaction on the database.
Forms may perform sequential changes.  No other process may write into the
database until all forms have completed.  The values returned are the values
returned by the last form.

It is an error to execute a TRANSACTION from inside an ATOMIC.

(ABORT-TRANSACTION . values) may be invoked ONLY from a process engaged in 
a transaction.  It "undoes" any changes made so far by the INNERMOST 
executing transaction, returns the designated values from the call on
TRANSACTION.

(INTRANSACTION) returns T if the process from which it is invoked is
engaged in a transaction.  It returns NIL otherwise.

If control should pass out of TRANSACTION by any means other than normal
termination of the last form, or execution of ABORT-TRANSACTION, and if
the transaction has modified the database, the changes are undone.
||#

(defvar-resettable *intransaction* nil)
(defun INTRANSACTION () *intransaction*)

(defun ABORT-TRANSACTION (&rest values)
  ;(when (inatomic) (error "cannot abort a transaction from inside an atomic"))
  ; decided that this is reasonable after all
  (cond (*intransaction* (throw 'abort-transaction (values-list values)))
	(t (error "ABORT-TRANSACTION called from outside a transaction"))))

(defmacro TRANSACTION
   (&body forms &aux (start (if (symbolp (first forms))
				(copy-symbol (pop forms))
				(make-symbol (if (stringp (first forms))
						 (pop forms)
						 "APTRANSACTION")))))
  `(do-transaction ',start #'(lambda () ,.forms)))

(defun do-transaction (start fn)
  (when (inatomic) (error "TRANSACTION initiated within an ATOMIC"))
  (withwriteaccess
    (let ((*intransaction* t) *max-history-length* ok label-event)
      (progv (when (eq t global-history) '(global-history))
	     (when (eq t global-history) (list (new-history)))
	(history-label start)
	(setf label-event (first global-history))
	(put-structure-property label-event t 'transaction-in-progress)
	(unwind-protect
	    (multiple-value-lambda-bind
	      (&rest results)
	      (catch 'abort-transaction
		(multiple-value-prog1
		  (funcall fn)
		  (rem-structure-property label-event
					  'transaction-in-progress)
		  (setf ok t)))
	      (unless ok (undo-to start) (setf ok t))
	      (values-list results))
	  (unless ok  ;; throwing through the transaction
	    (rem-structure-property label-event
				    'transaction-in-progress)
	    (undo-to start))
	  #+ignore 
	  (pop history-labels))))))

#|
when and if feasible(i.e., not expensive), I would like to detect
non-retractible primitive changes (that is, additions that have no deleter
and v.v.) when they take place within a TRANSACTION.  I'm not sure what the
best thing to do then is; I think it is to signal a proceedable error
that lets the computation continue if the application wants to chance it.

|#




(defun cxsensitize (subgen rel &aux
		    (gen (sgen subgen))
		    (temp (cadr (assoc 'template gen))) 
		    (args (loop for tmp below (length temp) collect (gensym "A")))
		    (inputs (loop for a in args as tmp in temp
				  when (eq tmp 'input) collect a))
		    newinit)
    ;; make another subgen (with slightly different initializer and pulser of gen)
    ;; to generate x s.t. (R x y) in cx:
    ;; initializer must get (TuplesOfRelIn <rel> currentcx),
    ;;   and filter out those which don't match y (inputs).  (result in xx)
    ;;   InitialState is (list <negatives of xx> <positives of xx>
    ;;                         <cx-independent initialstate>)
    ;; pulser must see if (cadr state) - if so, move an element to (car state) and
    ;;   return it, else use initial pulser, but filter out results in (car state)
    (setf newinit `(lambda (|Rel | ,@inputs)
		     (cxsensitize-init ,(relationnamep rel)
				       ,inputs ,temp
				       ,(expand-initializer gen (wff subgen)
							     (cons '|Rel | inputs))))
	  subgen (copy-subsetgen subgen))
    ;;alter-subsetgen
    (setf (sgen subgen)
	  (setf gen (mapcar #'(lambda (x) (copy-seq x))
			    (sgen subgen))))
    ;; two level copy - ((prop val) ...)
    (rplaca (cdr (assoc 'initialstate gen)) newinit)
    subgen)


(defmacro-displace cxsensitize-init (relname inputs template initializer
					     &aux (rel (relationp relname)))
  `(cxsensitive-generator |Rel | ,initializer
	 ,(if (not (member 'input template))
	      nil
	      `(#+symbolics global::let-closed
		 #+symbolics ,(mapcar #'(lambda (v) (list v v)) inputs)
		 #-symbolics progn
		 #'(lambda (args)
		     (and ,.(loop for temp in template with inp = inputs  as i from 0
				  as element = 'args then (list 'cdr element)
				  when (eq temp 'input) collect
				  (get-test-function (get-comparison rel i t)
						     (pop inp)
						     (list 'car element)))))))
	 
	    ,(if (not (member 'input template))
		 '#'tupargs
		 `#'(lambda (tuple &aux (args (tupargs tuple))) ;; not a closure -- 
   ;REALLY COMPUTE-POS-AND-NEG should pass (tupargs tuple) to this function.
   ;The only call on COMPUTE-POS-AND-NEG not represented here is in some
   ;bootstrapping code in RELATIONS.LISP
			      (list ,.(loop for temp in template
					  as element = 'args  then (list 'cdr element)
					  when (eq temp 'output)
					  collect (list 'car element)))))
	    #'(lambda (cxtuple next) ;; not a closure
		      (and ,. (loop for temp in template as i from 0
			          when (eq temp 'output) collect
				  (get-test-function (get-comparison rel i t)
						     '(pop cxtuple)
						     '(pop next)))))
	    ,.(let ((in inputs))
		(loop for tem in template collect
		      (cond ((eq tem 'input) (pop in)) (t '|Output|))))))


(defun cxsensitive-generator 
    (rel original filter outputfilter innerfilter &rest args &aux pos neg)
 (cond  ((or (assoc rel delta)
	     #+ignore (not (eq currentcx *globalcx*)))
	 (multiple-value-setq (pos neg)
		(apply #'compute-pos-and-neg rel filter outputfilter args))
	 (if (or pos neg)
	     #'(lambda (&rest ignore) (declare (ignore ignore))
		 (if pos
		     (apply #'values nil (pop pos))
		   (get-next-inneranswer  original neg innerfilter)))
	     original))
  (t original)))

