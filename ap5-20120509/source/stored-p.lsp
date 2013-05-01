;;; -*- Mode: Lisp; Package:AP5; Syntax:COMMON-LISP; Base:10 -*-

(in-package "AP5")

#|
Many useful representations of relations have a common abstraction in
terms of the common-lisp notion of a "generalized variable".  The
characteristic of such an implemenation is that it may be used for an
n-ary relation, and for any set of n-1 values, it is possible to
compute a location where a list of values for the final slot of the
relation corresponding to the n-1 values for the first n-1 slots.  For
any such implementation, there is a natural "single-valued" version
for cases where there is never more than one tuple for any n-1 values
in the initial slot, in which case it is not necessary to store a list
of values for the final slot, but just a single value or an indication
that no tuple is stored.  Given only the code necessary to find this
location, it is possible to automatically provide TESTING code and
GENERATING code for the pattern (INPUT... INPUT OUTPUT).

We capture this class of representations with the parameterized AP5 
implementations STORED-IN-PLACE and STORED-IN-PLACE-SINGLE.  Both
use STORED-WHERE as an implementation parameter relation.  STORED-WHERE
relates a relation that uses one of these implementations to a function
capable of generating the search code needed to find the "location" mentioned
above.  This function, like a macro, returns code as its value.  When
used with an n-ary relation R, this function is applied to 2(n-1) arguments.
The first n-1 arguments are always symbols, which at execution time will be
bound to specific values for the first n-1 slots of a (possible) tuple
of R.  The final n-1 arguments are the AP5 equivalence relations
for the first n-1 slots.  These are provided because the search code
may need to use the given values as "indices" into some data structure,
and searching the data structure correctly requires this information.
For example, an association list of (key . values) pairs can be used to
implement a binary relation.  Finding the entry corresponding to a given
value for the key requires knowing the correct :test parameter to pass
to ASSOC.  The STORED-WHERE function is only applied at compile time (it is
a code generator), so efficiency is not crucial.  The AP5 utility function
GET-TEST-FUNCTION is generally useful for this.  When HASHING is needed,
the AP5 relation CANONICALIZER provides a way to get to the key you need in
order to use lisp hashtables.

Deleting from stored-in-place relations is not as efficient as
could be hoped, because it involves both a READ (to get the old value)
and a WRITE (to store the new value).  [Common lisp does not provide
a DELETE analog to PUSH].  Thus the search for the location is done
twice for each deletion.  This could be avoided with zetalisp
"locatives", but not in common-lisp.

Common Lisp's abstraction of generalized variables does not include the
concept of "deallocating" the variable.  When generalized variables are
part of collections of such variables (entries in hashtables and alists,
for example), it is sometimes desirable to remove the variable from the set.
E.g., when the variable itself holds a collection, the application may
make no distinction between having the variable hold the EMPTY collection
and not having the variable present in the collection of variables.  It may,
for example, make no distinction between a hashtable containing an
entry with key=K and value=NIL and the same hashtable with no entry
for K.  The predefined generalized variable constructors of common lisp, such
as gethash, never remove variables.  When an ap5 application accesses
such a variable SOLELY through relations implemented with the stored-in-place
idiom, it absolutely cannot distinguish whether the underlying implementation
is removing the variable or storing the empty list of tuples in the variable.
It would probably provide better performance, in most situations, to remove the
variable.  Certainly we could let the programmer advise our code generators
by adding an optional second parameter, a "deallocater", to the idiom.

Frequently, "indexed" lisp data structures have the property that
only a restricted set of lisp values may serve as indices for the
most natural searches.  E.g., for an array, the indices must
be INTEGERs within the bounds of the array.  Rather than require
that the code for finding the storage location check the suitability
of the indices, we treat ANY error occurring within this code 
(in testing and generating) as an indication that no tuples exist for
the given indices.  This incurs a performance penalty, particularly for
those cases where ALL indices are legal.  Perhaps the burden should be
placed on the search code?

A number of useful relation macros are provided for common uses of this facility.
global variables -- unary relations. The generatlized variable must be a symbol
                    and symbol-value holds the tuple(s)
structure fields -- for binary relations.  Domain is a structure. The field
                     name is fixed (per relation).
symbol properties -- for binary relations. The domain is a symbol.
                      The property name is fixed (per relation).  
alists -- for binary relations. The generatlized variable must hold an alist.
          The domain is a key.
hashtables -- for binary relations. The generatlized variable must hold a
              hashtable. The domain is a key.

Desired extension -- for STORED-IN-PLACE-SINGLE, an additional functional
parameter, NO-VALUE-FN.  When applied to one argument, it should serve
as a predicate to test whether the contents of a location represents
the ABSENCE of any tuples.   When applied to no arguments, it should
return a value to store to represent the absence of any tuples.
This is still not powerful enough for some ways of representing
the absence of tuples -- e.g., makunbound for a symbol, or remhash of a
hashtable entry.  These could be handled by the same means as suggested
above for deallocating variables in STORED-IN-PLACE.

A problem encountered when generalizing to allow multiple representations:
Having multiple places does not tell us which one should be used
for testing.  There ought to be a way to specify one that's preferred,
e.g., array would be better than hashtable. 
(A more general solution would be to associate testefforts with testers.)
|#

#|  this stuff now specified in the defimplementation below
 (++ Implementation 'stored-in-place)
 (++ idempotent 'stored-in-place nil) ;; delete from list
 ;; but NOT stored-in-place-single - there we should test before del,
 ;; since the delete code will just replace the place with nothing-stored
 (++ testeffort 'stored-in-place
     '(LAMBDA (&rest Pat)
       (iftimes (RelationSize '(x) (append (butlast Pat) '(x))) 3)))
 (++ reltester 'stored-in-place 'test-stored-in-place-tuple)
 (++ reladder 'stored-in-place 'add-stored-in-place-tuple)
 (++ reldeleter 'stored-in-place 'delete-stored-in-place-tuple)
 (++ RelGenerator 'stored-in-place 'generate-stored-in-place-tuple)
 (++ checker 'stored-in-place 'check-place)
|#

(defrelation stored-where :arity 2 :equivs (eql SYMBOL-FUNCTIONAL-EQUIVALENTP))
 ; changed to get add/del/tester
(++ relsize (theap5relation stored-where) '(input output) 1)
(++ relsize (theap5relation stored-where) '(output input) 1)
;(++ compare-relation (theap5relation stored-where) 1 *rel-symbol-functional-equivalentp*)

#+ignore ;; multiple stored-wheres allowed now
(restrict-cardinality stored-where (entity output)
		      :countspec :optional :replacing t)

(defun test-for-slot(rel column &rest inputs)
  ;; if INPUTS is nil, returns a piece of code that evaluates to
  ;; a function that performs the correct equiv test for column of rel.
  ;; Otherwise, INPUTS must be a list of two expressions, and a lisp
  ;; expression is returned that performs the corresponding equivalence
  ;; test on the values of those expressions.
  (apply #'get-test-function (get-comparison rel column) inputs))

(defun place-equivalence-rels (rel)
  (loop for i below (1- (arity* rel)) collect (get-comparison rel i)))

(defun place-args (rel)
  (loop for i from 1 below (arity* rel) as code from (char-code #\A)
      collect (make-symbol (string (code-char code)))))

(defun test-stored-in-place-tuple
       (rel &rest ignore &aux (place-args (place-args rel)))
  (declare (ignore ignore))
  (forany the-place s.t. (stored-where rel the-place)
	  `(lambda (rel ,@ place-args range)
	     (declare (ignore rel))
	     (member range (ignore-errors
			      ,(apply the-place
				    (append place-args
					    (place-equivalence-rels rel))))
		     :test  ,(test-for-slot rel (1- (arity* rel)))))))

(defun add-stored-in-place-tuple (rel &rest ignore
				  &aux (place-args (place-args rel)))
  (declare (ignore ignore))
  `(lambda (rel ,@ place-args range)
     (declare (ignore rel))
     ,.(loop for the-place s.t. (stored-where rel the-place) collect
        `(push range ,(apply the-place
			  (append place-args
				  (place-equivalence-rels rel)))))))

(defun delete-stored-in-place-tuple (rel &rest ignore
				     &aux (place-args (place-args rel)))
  (declare (ignore ignore))
  `(lambda (rel ,@ place-args range)
     (declare (ignore rel))
     ,.(loop for the-place s.t. (stored-where rel the-place)
	 collect  (let ((where (apply the-place (append place-args
					 (place-equivalence-rels rel)))))
		    `(setf ,where
		       (delete range ,where
			       :test ,(test-for-slot rel (1- (arity* rel)))
			       :count 1))))))

(defun generate-stored-in-place-tuple (subsetflg varsx rel &rest ignore
				       &aux (place-args (place-args rel)))
  (declare (ignore subsetflg varsx ignore))
  (values-list
      (loop for the-place s.t. (stored-where rel the-place) collect
       `((initialstate
	  (lambda (ignore ,@ place-args &aux state)
	    (declare (ignore ignore))
	    (setf state (ignore-errors
			 ,(apply the-place (append place-args
					     (place-equivalence-rels rel)))))
	    #'(lambda () (if state (values nil (pop state)) T))))
	    (template (,@ (make-list (1- (arity* rel)) :initial-element 'input)
			  output))
	  (effort ,(relationsize '(var) `(,rel ,@ place-args var)))))))

(defun check-place (rel adds dels &aux place-check-fn arglist)
  (declare (ignore dels))
  (unless (setf place-check-fn (get-structure-property rel 'place-check-fn))
    (put-structure-property rel
       (setf place-check-fn
        (compile-ap
	 `(lambda ,(setf arglist (loop for a below (arity* rel) collect (gensym "A")))
	    (declare (ignore ,.(last arglist)))
	    ,(forany place s.t. (stored-where rel place)
		 `(eq t
		      (ignore-errors
			,(apply place (append (butlast arglist)
					      (place-equivalence-rels rel)))
			t))))))
       'place-check-fn))
  (loop for tup in adds always (apply place-check-fn tup)))

(defimplementation stored-in-place
    :idempotent (:delete)
    :testeffort (LAMBDA (&rest Pat)
                 (iftimes (RelationSize '(x) (append (butlast Pat) '(x))) 3))
    :tester test-stored-in-place-tuple
    :adder  add-stored-in-place-tuple
    :deleter delete-stored-in-place-tuple
    :generators (generate-stored-in-place-tuple)
    :checkers (check-place)
    )


#| this stuff now specified in the defimplementation below
 (++ Implementation 'stored-in-place-single)
 (++ testeffort 'stored-in-place-single
     '(lambda (&rest ignore) (declare (ignore ignore)) 1))
 (++ reltester 'stored-in-place-single 'test-stored-in-place-single-tuple)
 (++ reladder 'stored-in-place-single 'add-stored-in-place-single-tuple)
 (++ reldeleter 'stored-in-place-single 'delete-stored-in-place-single-tuple)
 (++ RelGenerator 'stored-in-place-single
     'generate-stored-in-place-single-tuple)
 (++ checker 'stored-in-place-single 'check-place-single)
|#

(defparameter *no-single-value-stored* (list "none stored"))

(defun test-stored-in-place-single-tuple (rel &rest ignore
					  &aux 	(place-args (place-args rel)))
  (declare (ignore ignore))
  (forany the-place s.t. (stored-where rel the-place)
	  `(lambda (rel ,@ place-args range)
	     (declare (ignore rel))
	     (multiple-value-bind (found err)
		 (ignore-errors
		   ,(apply the-place (append place-args
					     (place-equivalence-rels rel))))
	       (when err (setf found *no-single-value-stored*))
	       (cond ((eq found *no-single-value-stored*) nil)
		     (t ,(test-for-slot rel (1- (arity* rel)) 'range 'found)))))))

(defun add-stored-in-place-single-tuple (rel &rest ignore
					 &aux (place-args (place-args rel)))
  (declare (ignore ignore))
  `(lambda (rel ,@ place-args range)
     (declare (ignore rel))
     ,.(loop for the-place  s.t. (stored-where rel the-place) collect 
        `(setf ,(apply the-place (append place-args
					 (place-equivalence-rels rel)))
	   range))))

(defun delete-stored-in-place-single-tuple (rel &rest ignore
					    &aux (place-args (place-args rel)))
  (declare (ignore ignore))
  ;;[**] ***** basically we need the tester code here - should be sensitive
  ;; to a declaration of which place is cheapest to find
  (forany the-place s.t. (stored-where rel the-place)
   (let ((where (apply the-place  (append place-args
					  (place-equivalence-rels rel)))))
     `(lambda (rel ,@ place-args range &aux (found ,where))
	(declare (ignore rel))
	(when ,(test-for-slot rel (1- (arity* rel)) 'range 'found)
	 ;; if what is now stored is not equivalent to the value to be deleted,
         ;; it must be due to a store done in the same atomic that has already
         ;; happened
	 ;; but this test could be optimized out for nonatomic rels [dc 12/96]
	  ,.(loop for the-place s.t. (stored-where rel the-place) collect
             `(setf ,(apply the-place
			    (append place-args (place-equivalence-rels rel)))
		 *no-single-value-stored*)))))))

(defun generate-stored-in-place-single-tuple
      (subsetflg varsx rel &rest ignore &aux (place-args (place-args rel)))
  (declare (ignore subsetflg varsx ignore))
  (values-list
   (loop for  the-place s.t. (stored-where rel the-place) collect
    `((initialstate
       (lambda (ignore ,@ place-args)
	 (declare (ignore ignore))
	 (multiple-value-bind (state err)
	     (ignore-errors
	      ,(apply the-place (append place-args
					(place-equivalence-rels rel))))
	   (when err (setf state *no-single-value-stored*))
	   #'(lambda ()
	       (if (eql state *no-single-value-stored*)
		   T
		 (values nil
			 (prog1 state
			   (setf state *no-single-value-stored*))))))))
       (template (,@ (make-list (1- (arity* rel)) :initial-element 'input)
		       output))
       (effort 1)))))

(defun check-place-single (rel adds dels &aux check-fn arglist)
  (declare (ignore dels))
  (unless (setf check-fn (get-structure-property rel 'place-check-fn))
    (put-structure-property rel
       (setf check-fn
        (compile-ap
	 `(lambda ,(setf arglist (loop for a below (arity* rel) collect (gensym "A")))
	    (declare (ignore ,.(last arglist)))
	    ,(forany place s.t. (stored-where rel place)
		 `(multiple-value-bind (data error)
		      (ignore-errors
			,(apply place (append (butlast arglist)
					      (place-equivalence-rels rel))))
		    (declare (ignore data))
		    (not error)
		    #+ignore
		    (when error (abort 'addchecker "no such place")))))))
       'place-check-fn))
  (unless (loop for tup in adds always (apply check-fn tup))
    (return-from check-place-single nil))
  ; so all the places exist, now check that we're not trying to put >1 tuple in a place
  (unless (setf check-fn (get-structure-property rel 'multiple-add-check-fn))
    (put-structure-property rel
       (setf check-fn
        (compile-ap
	 `(lambda ,(setf arglist (loop for a below (arity* rel) collect (gensym "A")))
	    ; recompute in case first fn was already cached ...
	    (declare (ignore ,.(last arglist)))
	    (and (fortheonly ,(last arglist) s.t. (start (,rel ,.arglist))
			     (declare (ignore ,. (last arglist) )) t
			     ifmany nil)
		 (forany ,(last arglist) s.t. (previously (,rel ,.arglist))
			 (?? start (not (,rel ,.arglist)))
			 ifnone t)))))
       'multiple-add-check-fn))
  (loop for a in adds always (apply check-fn a)))

(defimplementation stored-in-place-single
    :idempotent (:delete)
    :testeffort (lambda (&rest ignore) (declare (ignore ignore)) 1)
    :tester test-stored-in-place-single-tuple
    :adder  add-stored-in-place-single-tuple
    :deleter delete-stored-in-place-single-tuple
    :generators (generate-stored-in-place-single-tuple)
    :checkers (check-place-single)
    )

; ---------------- general places ----------------

(defun stored-in-place (name keys placer)
  ; (warn-ignored-keys name keys (:adder :deleter :updater :tester) *below*)
  ; might as well allow them...
  (declare (ignore name))
  `(:representation stored-in-place
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel
			      ,(if (symbolp placer) (kwote placer)
				   `(FUNCTIONAL-EQUIVALENCE-TESTABLE
				      (function ,placer)
				      '(stored-place ,placer)))))
	   (getf keys :alsofns))
    ,.keys))

(defun stored-in-place-single (name keys placer)
  (declare (ignore name))
  ; (warn-ignored-keys name keys (:adder :deleter :updater :tester) *below*)
  `(:representation stored-in-place-single
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel
			      ,(if (symbolp placer) (kwote placer)
				   `(FUNCTIONAL-EQUIVALENCE-TESTABLE
				      (function ,placer)
				      '(stored-place-single ,placer)))))
	   (getf keys :alsofns))
    :size ,(cons (append (loop for i below (1- (getf keys :arity)) collect 'input)
			 '(output))
		 (cons 1 (getf keys :size)))
    ,.keys))


; ---------------- global vars ----------------

(defun globalvar (name keys varname)
 (warn-ignored-keys name keys (:arity)
   ;; allow :adder :deleter :updater :generator :tester 
  `(:representation stored-in-place :arity 1
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel ,(stored-in-symbol-placer varname t)))
	   (getf keys :alsofns))
    ,.keys)))

(defun globalvar-single (name keys varname)
 (warn-ignored-keys name keys (:size :arity)
   ;; allow  :adder :deleter :updater :generator :tester
  `(:representation stored-in-place-single :arity 1
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel ,(stored-in-symbol-placer varname nil)))
	   (getf keys :alsofns))
    :size ((output) 1)
    ,.keys)))

(defun stored-in-symbol-placer (var nil-or-nothing)
  (cond (nil-or-nothing
	 `(FUNCTIONAL-EQUIVALENCE-TESTABLE
	   #'(lambda () (list 'unbound-is-nil '',var))
	   '(unbound-is-nil ',var)))
	(t `(FUNCTIONAL-EQUIVALENCE-TESTABLE
	     #'(lambda () (list 'unbound-is-nothing '',var))
	     '(unbound-is-nothing ',var)))))

(defun unbound-is-nil (symbol)
  (when (boundp symbol) (symbol-value symbol)))
(defun unbound-is-nothing (symbol)
  (cond ((boundp symbol) (symbol-value symbol))
	(t *no-single-value-stored*)))
;; Monday 2010/10/11 -- set is deprecated
;(defsetf unbound-is-nil set)
;(defsetf unbound-is-nothing set)
(defsetf unbound-is-nil (x)(y) `(setf (symbol-value ,x) ,y))
(defsetf unbound-is-nothing (x)(y) `(setf (symbol-value ,x) ,y))

;;----------------  STRUCTURE FIELDS ----------------

(defun structure (name keys structname fieldname)
 (warn-ignored-keys name keys (:arity) ; :adder :deleter :updater :tester 
  `(:representation stored-in-place :arity 2
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel
			      ,(stored-in-field-placer structname fieldname)))
	   (getf keys :alsofns))
    ,.keys)))

(defun structure-single (name keys structname fieldname)
 (warn-ignored-keys name keys (:arity) ; :adder :deleter :updater :tester 
  `(:representation stored-in-place-single :arity 2
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel
			      ,(stored-in-field-placer structname fieldname)))
	   (getf keys :alsofns))
    :size ,(cons '(input output) (cons 1 (getf keys :size)))
    ,.keys)))

(defun stored-in-field-placer (structure field)
  ;; Thursday 2006/02/16 - we can do this in common lisp now
  `#'(lambda (struc equiv) (declare (ignore equiv))
       (list 'slot-value struc '',field))
  #+ignore ;; in fact I see no advantage of a functional equivalence here
  `(FUNCTIONAL-EQUIVALENCE-TESTABLE
    #'(lambda (struc equiv) (declare (ignore equiv))
	(list ',(defstruct-access-function-name structure field) struc))
    '(stored-in-field-placer ,structure ,field)))

#|
(defstruct abc (xx2))
(defrelation z1 :representation (structure abc xx2))
(declaim (special zzz))
(setf zzz (make-abc :xx2 '(two)))
(listof x s.t. (z1 zzz x))
 ==> (TWO)
(++ z1 zzz 'three)
(listof x s.t. (z1 zzz x))
 ==> (THREE TWO)
(-- z1 zzz 'two)
(listof x s.t. (z1 zzz x))
 ==> (THREE)
|#

;; now for my own uses of it ...
;; organizationally, these would be better located in some other file
(defrelation matchsuccessor :representation (structure matchnode matchsuccessors)
	     :generator
	     ((simplegenerator (output node) (matchpredecessors node)))
	     :types (matchnode matchnode)
	     :type-enforcements (:none :none)
	     :nonatomic t)
(defrelation matchvars :representation (structure-single matchnode matchvars)
	     :types (matchnode list)
	     :type-enforcements (:none :none)
	     :nonatomic t)
(defrelation matchwff :representation (structure-single matchnode matchwff)
	     :types (matchnode entity) :equivs (eql equal)
	     :type-enforcements (:none :none)
	     :nonatomic t)

;; needed in rule decache-matchrels
(defrelation matchrels :representation (structure-single matchnode matchrels)
	     :types (matchnode entity) :equivs (eql equal)
	     :type-enforcements (:none :none)
	     :nonatomic t)

(defrelation addmatcher :arity 2
	     :nonatomic t
	     :types (relation matchnode)
	     :type-enforcements (:none :none)
	     :representation
	     (stored-in-place (lambda (x equiv) (declare (ignore equiv))
				      `(get-structure-property ,x 'addmatchers))))
(defrelation deletematcher :arity 2
	     :nonatomic t
	     :types (relation matchnode)
	     :type-enforcements (:none :none)
	     :representation
	     (stored-in-place (lambda (x equiv) (declare (ignore equiv))
				      `(get-structure-property ,x 'deletematchers))))
 

;;----------------  SYMBOL PROPERTIES ----------------

(defun symbolprop (name keys propname)
 (warn-ignored-keys name keys (:arity) ; :adder :deleter :updater :tester 
  `(:representation stored-in-place :arity 2
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel
			      ,(stored-on-plist-placer propname nil)))
	   (getf keys :alsofns))
    ,.keys)))

(defun symbolprop-single (name keys propname)
 (warn-ignored-keys name keys (:arity) ; :adder :deleter :updater :tester 
  `(:representation stored-in-place-single :arity 2
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel
			      ,(stored-on-plist-placer propname t)))
	   (getf keys :alsofns))
    :size ,(cons '(input output) (cons 1 (getf keys :size)))
    ,.keys)))

(defun stored-on-plist-placer (indicator missing-is-nothing)
   `(FUNCTIONAL-EQUIVALENCE-TESTABLE
     #'(lambda (sym equiv) (declare (ignore equiv))
          (list 'get sym '',indicator
		,(when missing-is-nothing '*no-single-value-stored*)))
     '(stored-on-plist-placer ,indicator ,missing-is-nothing)))


;;----------------  HASH TABLES ----------------

(defun hashtable (name keys code)
 (warn-ignored-keys name keys (:arity)
   ; :generator :adder :deleter :updater :tester 
  `(:representation stored-in-place :arity 2
    :alsofns
    ,(cons `(lambda (rel)
	      (++ Stored-where rel
		  ;; cannot compute the placer code at macroexpand time,
		  ;; because I need the canonicalizer for the key, if
		  ;; there is one.  But by the time this code executes,
		  ;; REL will be bound to the relation, from which I
		  ;; can obtain the canonicalizer for its 0th column
		  (stored-in-hash-table-placer ',code nil)))
	   (getf keys :alsofns))
    ,.keys)))

(defun hashtable-single (name keys code)
 (warn-ignored-keys name keys (:arity)
   ; :generator :adder :deleter :updater :tester 
  `(:representation stored-in-place-single :arity 2
    :alsofns
    ,(cons `(lambda (rel)
	      (++ Stored-where rel
		  (stored-in-hash-table-placer ',code t)))
	   (getf keys :alsofns))
    :size ,(cons '(input output) (cons 1 (getf keys :size)))
    ,.keys)))

(defun stored-in-hash-table-placer (hash-table-code missing-is-nothing)
     (FUNCTIONAL-EQUIVALENCE-TESTABLE
       #'(lambda (key equiv)
	   ;; canonicalize key if needed
	   ;; KEY is just a symbol, which AT RUN TIME, will be bound to
	   ;; an actual value
	   (forany f s.t. (canonicalizer equiv $ f)
		   (setf key `(,f ,key))
		   ifnone nil)
	   `(gethash ,key ,hash-table-code
		     ,(when missing-is-nothing '*no-single-value-stored*))) 
       `(stored-in-hash-table-placer  ,hash-table-code  ,missing-is-nothing)))

; now add generators for entire hashtable
(defun gen-hash-table-single (ignore vars rel &rest ignore2 &aux placer)
  ; comparisons not needed for (o o) - whatever is in the table will do
  (declare (ignore ignore ignore2 vars))
  (forany x s.t. (parameter-list rel x)
	  (if (eq (car x) 'hashtable-single) (setf placer (cadr x))
	      (return-from gen-hash-table-single nil))
	  ifnone (return-from gen-hash-table-single nil))
  (values
    ; For the next two, we must first make a list of all the keys
    ; so that they can be accessed one at a time as they are needed
    `((initialstate
      (lambda (&rest ignore)
	(declare (ignore ignore))
        (let (pair-list the-table)
	  (setf the-table ,placer)
	  (maphash #'(lambda (key val)
		       (unless (eq val *no-single-value-stored*)
			 (push (cons key val) pair-list)))
		   the-table)
	  ;; THIS GENERATES canonical KEYS, NOT THE REAL TUPLE VALUES!!
	  #'(lambda ()
	      (if pair-list
		  (values nil (caar pair-list) (cdr (pop pair-list)))
		T)))))
      (template (output output))
      (effort ,(iftimes (relationsize '(x y) (cons rel '(x y))) 20)))))
(++ relgenerator 'stored-in-place-single 'gen-hash-table-single)

(defun gen-hash-table (ignore vars rel &rest ignore2 &aux placer)
  (declare (ignore ignore ignore2 vars))
  (forany x s.t. (parameter-list rel x)
	  (if (eq (car x) 'hashtable) (setf placer (cadr x))
	      (return-from gen-hash-table nil))
	  ifnone (return-from gen-hash-table nil))
  (values
    ; For the next two, we must first make a list of all the keys
    ; so that they can be accessed one at a time as they are needed
    `((initialstate
      (lambda (rel &rest ignore)
	(declare (ignore ignore rel))
        (let (key-list the-table vals)
	  (setf the-table ,placer)
	  (maphash #'(lambda (key val) (when val (push key key-list)))
		   the-table)
	  (push nil key-list) ;; hack because of initial POP in pulse code
	  #'(lambda ()
	      (unless vals
		(pop key-list)
		(when key-list
		  (setf vals (gethash (first key-list) the-table))))
	      (if key-list (values nil (first key-list) (pop vals))
		T)))))
      (template (output output))
      (effort ,(iftimes (relationsize '(x y) (cons rel '(x y))) 20)))))
(++ relgenerator 'stored-in-place 'gen-hash-table)

#|
(declaim (special zh))
(setf zh (make-hash-table))
(defrelation zh :representation (hashtable zh))
(listof x s.t. (zh 0 x))
 ==> nil
(++ zh 0 'one)
(listof x s.t. (zh 0 x))
 ==> (ONE)
(++ zh 0 'two)
(listof x s.t. (zh 0 x))
 ==> (TWO ONE)
(-- zh 0 'one)
(listof x s.t. (zh 0 x))
==> (TWO)
(-- zh 0 'two)
(listof x s.t. (zh 0 x))
 ==> nil
|#


;;----------------  ASSOCIATION LISTS ----------------

(defun alist (name keys code)
 (warn-ignored-keys name keys (:arity)
   ; :generator :adder :deleter :updater :tester 
  `(:representation stored-in-place :arity 2
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel
			      (stored-in-alist-placer ',code nil)))
	   (getf keys :alsofns))
    ,.keys)))

(defun alist-single (name keys code)
 (warn-ignored-keys name keys (:arity)
   ; :generator :adder :deleter :updater :tester 
  `(:representation stored-in-place-single :arity 2
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel
			      (stored-in-alist-placer ',code t)))
	   (getf keys :alsofns))
    :size ,(cons '(input output) (cons 1 (getf keys :size)))
    ,.keys)))

(defun stored-in-alist-placer (alist-code missing-is-nothing)
  (FUNCTIONAL-EQUIVALENCE-TESTABLE
   #'(lambda (key equiv)
       `(assoc-place ,key ,alist-code
	    ,(get-test-function equiv)
	    ,(when missing-is-nothing '*no-single-value-stored*)))
   `(stored-in-alist-placer ,alist-code , missing-is-nothing)))

(defun assoc-place (key alist test &optional default
		    &aux (pair (assoc key alist :test test)))
  (if pair (cdr pair) default))


(defun replace-alist-entry (key value alist test &aux entry)
  (cond ((setf entry (assoc key alist :test test))
	 (rplacd entry value)
	 alist)
	(t (cons (cons key value) alist))))

(DEFINE-SETF-EXPANDER assoc-place (key access-form test &optional default)
  (multiple-value-bind (temps vals stores store-form access-form)
      (get-setf-expansion access-form)
    (let ((kv (gensym "G")) (store (gensym "G")) (stemp (first stores)))
      (values (cons kv temps)
	      (cons key vals)
	      (list store)
	      `(let ((,stemp (replace-alist-entry ,kv ,store ,access-form ,test)))
		 ,store-form
		 ,store)
	      `(assoc-place ,kv ,access-form ,test ,default)))))

; now add the other generators for alists
(defun gen-alist (ignore vars rel &rest ignore2 &aux placer)
  (declare (ignore ignore ignore2 vars))
  (forany x s.t. (parameter-list rel x)
	  (if (eq (first x) 'alist) (setf placer (second x))
	      (return-from gen-alist nil))
	  ifnone (return-from gen-alist nil))
  (values
    `((initialstate
	(lambda (rel &aux the-component the-tuple) ;compiler bug prevents initialization
	  (declare (ignore rel))
	  (setf the-tuple ,placer) ;; misnamed variable
	  (setf the-component (cdar the-tuple))
	  #'(lambda (&rest ignore)
	      (declare (ignore ignore))
	      (loop while (and the-tuple (null the-component)) do
		    (pop the-tuple)
		    (setf the-component (cdar the-tuple)))
	      (if the-tuple
		  (values nil (caar the-tuple) (pop the-component))
		T))))
      (template (output output))
      (effort ,(iftimes (relationsize '(x y) (cons rel '(x y))) 3))
     )))
(++ relgenerator 'stored-in-place 'gen-alist)

(defun gen-alist-single (ignore vars rel &rest ignore2 &aux placer)
  (declare (ignore ignore ignore2 vars))
  (forany x s.t. (parameter-list rel x)
	  (if (eq (first x) 'alist-single) (setf placer (second x))
	      (return-from gen-alist-single nil))
	  ifnone (return-from gen-alist-single nil))
  (values
    `((initialstate
	(lambda (rel &aux the-tuple) ;compiler bug prevents initialization
	  (declare (ignore rel))
	  (setf the-tuple ,placer)
	  #'(lambda (&rest ignore)
	      (declare (ignore ignore))
	      (loop while (eq (cdar the-tuple) *no-single-value-stored*)
		    do (pop the-tuple))
	      (if the-tuple
		  (values nil (caar the-tuple) (cdr (pop the-tuple)))
		T))))
      (template (output output))
      (effort ,(iftimes (relationsize '(x y) (cons rel '(x y))) 3))
     )))
(++ relgenerator 'stored-in-place-single 'gen-alist-single)

#| 
(declaim (special myalist))
(setf myalist '(a ((b c) (d e f))))
(defrelation alistrel :representation (alist (cadr myalist)))
(listof x s.t. (alistrel 'd x))
 ==> (E F)
(++ alistrel 'd 'three)
(listof x s.t. (alistrel 'd x))
 ==> (THREE E F)
(-- alistrel 'd 'three)
(listof x s.t. (alistrel 'd x))
 ==> (E F)
(-- alistrel 'd 'e)
(-- alistrel 'd 'f)
(listof x s.t. (alistrel 'd x))
 ==> NIL
|#


;;----------------  ARRAYS ----------------

; we should avoid giving a function defn to a symbol in the lisp package!
(defun array (name keys code)
 (declare (ignore name))
; (warn-ignored-keys name keys (:generator :adder :deleter :updater :tester) ...)
  `(:representation stored-in-place
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel ,(stored-in-array-placer code)))
	   (getf keys :alsofns))
    ,.keys))

(defun array-single (name keys code)
 (declare (ignore name))
; (warn-ignored-keys name keys (:generator :adder :deleter :updater :tester) ...)
  `(:representation stored-in-place-single
    :alsofns
    ,(cons `(lambda (rel) (++ Stored-where rel ,(stored-in-array-placer code)))
	   (getf keys :alsofns))
    :size ,(cons '(input output) (cons 1 (getf keys :size)))
    ,.keys))

(defun stored-in-array-placer (array-code)
  `(FUNCTIONAL-EQUIVALENCE-TESTABLE
     #'(lambda (&rest indices-plus)
	 (cons 'aref (cons ',array-code
			   (ldiff indices-plus
				  (nthcdr (/ (length indices-plus) 2)
					  indices-plus)))))
     '(stored-in-array-placer ,array-code)))

; now add all the other generators
(defvar singlearraygeneratortable nil)
(defun gen-array-single (subsetflg vars rel &rest args
			     &aux stored temp placer arity)
  (forany x s.t. (parameter-list rel x)
	  (if (eq (first x) 'array-single)
	      (setf placer (second x) arity (arity* rel))
	      (return-from gen-array-single nil))
	  ifnone (return-from gen-array-single nil))
  (unless (setf stored (assoc arity singlearraygeneratortable))
    (push (setf stored
		(cons arity
		      (let (result)
			(doxproduct (template
				      (make-sequence 'list arity
						     :initial-element
						     '(input output)))
				    (when (cdr (member 'output template))
						; otherwise we already have gen's
				      (push (arraygen1 '(output)
						       (copy-list template) placer)
					    result)))
			result)))
	  singlearraygeneratortable))
  (values-list
      (loop for gen in (cdr stored) when
	    ; don't return any more general than needed; return those more
	    ; specific if SubsetFlg - sort of anti-MatchTemplate
	    (loop for tmp in (setf temp (cadr (assoc 'template gen)))
		  as a in args
		  always (or (eq tmp 'input) (member a vars)))
	    unless
	    (and (not subsetflg)
		 (loop for tmp in temp as a in args
		       thereis (and (eq tmp 'input) (member a vars))))
	    collect
	    (cons (list 'effort
			(iftimes 5 (relationsize '(output) (cons rel temp))))
		  (fix-arraygen1 gen rel temp placer)))))

(defun fix-arraygen1 (gen rel temp placer &aux (size (array-dimensions (eval placer))))
  (subst (loop for s in size as x in temp when (eq x 'input) collect s)
	 '*array-input-size-here*
	 (subst (loop for s in size as x in temp when (eq x 'output) collect s)
		'*array-output-size-here*
		(subst (get-test-function (get-comparison rel (length size) t) 'last 'aref)
		       '*equiv-here*
		       gen))))


(defun arraygen1 (vars pat placer &aux indexlist limitlist inputlist subscriptlist)
     (declare (ignore vars))
     (loop for p on pat when (cdr p) do
	   (cond ((eq (car p) 'output)
		  (push (gensym "LIMIT") limitlist)
		  (push (gensym "INDEX") indexlist)
		  (push (car indexlist) subscriptlist))
		 (t (push (gensym "A") inputlist)
		    (push (car inputlist) subscriptlist))))
     (setf subscriptlist (nreverse subscriptlist)
	   inputlist (nreverse inputlist)
	   indexlist (nreverse indexlist))
     `((template ,pat) ; Effort computed above for each rel
       (initialstate
	 (lambda (rel ,@inputlist ,@(when (eq (car (last pat)) 'input) '(last))
		  &aux ,@limitlist ,@indexlist
		  (outlimit '*array-output-size-here*)
		  ,@(when (member 'input (butlast pat))
		      '((inlimit '*array-input-size-here*)))
		  (array ,placer))
	   (declare (ignore rel))
	   ,.(loop for ll in limitlist collect `(setf ,ll (pop outlimit)))
	   (cond
	     ((not (and ,.(loop for i in inputlist collect
				`(and (integerp ,i) (< -1 ,i (pop inlimit))))))
	      ;; indices not in range
	      #'(lambda nil t))
	     (t ,.(loop for x on indexlist collect
			`(setf ,(car x) ,(cond ((cdr x) 0) (t -1))))
		#'(lambda nil
		    (prog (aref) ; need prog to return to
			  (go start)
		       gen0 (return t)    ;exhausted
			  ,@(loop for index on indexlist as limit in limitlist
				  as index# from 1 nconc
				  `(,(pack* 'gen index#)
				    ,@(unless (cdr index) '(start))
				    (when (= (incf ,(car index)) ,limit)
				      (setf ,(car index) -1)
				      (go ,(pack* 'gen (1- index#))))))
			     (when (eq *no-single-value-stored*
				       (setf aref (aref array ,@subscriptlist)))
			       (go start))
			     ,@(when (eq (car (last pat)) 'input)
				 `((unless *equiv-here* (go start))))
			     (return (values nil ,@indexlist
					     ,@(when (eq (car (last pat)) 'output)
						 `(aref))))))))))))
(++ relgenerator 'stored-in-place-single 'gen-array-single)

(defvar arraygeneratortable nil)
(defun gen-array (subsetflg vars rel &rest args
			     &aux stored temp placer arity)
  (forany x s.t. (parameter-list rel x)
	  (if (eq (car x) 'array)
	      (setf placer (second x) arity (arity* rel))
	      (return-from gen-array nil))
	  ifnone (return-from gen-array nil))
  (unless (setf stored (assoc arity arraygeneratortable))
    (push (setf stored
		(cons arity
		      (let (result)
			(doxproduct
			  (template		; always output on the end
			    (make-sequence 'list (1- arity)
					   :initial-element '(input output)))
			  (when (member 'output template)
						; otherwise we already have gen's
			    (push (arraygen '(output)
					    (append template '(output)) placer)
				  result)))
			result)))
	  arraygeneratortable))  
  (values-list
      (loop for gen in (rest stored) when
	    ; don't return any more general than needed; return those more
	    ; specific if SubsetFlg - sort of anti-MatchTemplate
	    (loop for tmp on (setf temp (cadr (assoc 'template gen)))
		  as a in args
		  always (or (null (cdr tmp)) (eq (car tmp) 'input)
			     (member a vars)))
	    ; not quite so picky as array1 since we only have half as many
	    unless
	    (and (not subsetflg)
		 (loop for tmp in temp as a in args
		       thereis (and (eq tmp 'input) (member a vars))))
	    collect
	    (cons (list 'effort
			(iftimes 5 (relationsize '(output) (cons rel temp))))
		  (fix-arraygen gen rel temp placer)))))

(defun fix-arraygen (gen rel temp placer &aux (size (array-dimensions (eval placer))))
  (declare (ignore rel))
  (subst (loop for s in size as x in temp when (eq x 'input) collect s)
	 '*array-input-size-here*
	 (subst (loop for s in size as x in temp when (eq x 'output) collect s)
		'*array-output-size-here*
		gen)))

(defun arraygen (vars pat placer &aux indexlist limitlist inputlist subscriptlist)
     (declare (ignore vars))
     (loop for p on pat when (cdr p) do
	   (cond ((eq (car p) 'output)
		  (push (gensym "LIMIT") limitlist)
		  (push (gensym "INDEX") indexlist)
		  (push (car indexlist) subscriptlist))
		 (t (push (gensym "A") inputlist)
		    (push (car inputlist) subscriptlist))))
     (setf subscriptlist (nreverse subscriptlist)
	   inputlist (nreverse inputlist)
	   indexlist (nreverse indexlist))
     `((template ,pat) ; Effort computed above for each rel
       (initialstate
	 (lambda (rel ,@inputlist ,@(when (eq (car (last pat)) 'input) '(last))
		  &aux ,@limitlist ,@indexlist
		  (outlimit '*array-output-size-here*)
		  ,@(when (member 'input (butlast pat))
		      '((inlimit '*array-input-size-here*)))
		  (array ,placer))
	   (declare (ignore rel))
	   ,.(loop for ll in limitlist collect `(setf ,ll (pop outlimit)))
	   (cond
	     ((not (and ,.(loop for i in inputlist collect
				`(and (integerp ,i) (< -1 ,i (pop inlimit))))))
	      #'(lambda nil t))
	     (t ,.(loop for x on indexlist collect
			`(setf ,(car x) ,(cond ((cdr x) 0) (t -1))))
		(let (aref)
		 #'(lambda nil
		    (prog nil ; need prog to return to
		       (go start)
		       gen0 (return t)    ;exhausted
		       ,@(loop for index on indexlist as limit in limitlist
			       as index# from 1 nconc
			       `(,(pack* 'gen index#)
				 ,@(unless (cdr index) '(next))
				 (when (= (incf ,(car index)) ,limit)
				   (setf ,(car index) -1)
				   (go ,(pack* 'gen (1- index#))))))
		       (setf aref (aref array ,@subscriptlist))
		       start
		       #+ignore,@(cond
			   ((eq (car (last pat)) 'input)
			    `((unless *equiv-here* (go next))
			      (return (values nil ,@indexlist))))
			   (t `((unless aref (go next))
				(return (values nil ,@indexlist (pop aref))))))
		       (unless aref (go next))
		       (return (values nil ,@indexlist (pop aref))))))))))))
(++ relgenerator 'stored-in-place 'gen-array)

#|
(declaim (special myarray))
(setf myarray (list (make-array '(7 9 3))))
(setf (aref (car myarray) 1 2 2) '(a b c d))
(defrelation z9 :arity 4 :representation (array (car myarray)))
(listof x s.t. (z9 1 (1+ 1) (1- 3) x))
 ==> (A B C D)
(++ z9 1 2 2 'three)
(listof x s.t. (z9 1 2 2 x))
 ==> (THREE A B C D)
(-- z9 1 2 2 'three)
(listof x s.t. (z9 1 2 2 x))
 ==> (A B C D)
(listof x z s.t. (z9 x 2 z 'c))
 ==> ((1 2))
|#
