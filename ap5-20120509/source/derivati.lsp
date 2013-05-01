;;; -*- Mode: LISP; Package: AP5; Syntax: Common-Lisp; Base: 10 -*-

; contents: lisp-predicate, lisp-function, coded, tclosure, 
;           cardinality, sum, extreme


(in-package "AP5")

;; this is potentially useful even for non derived relations,
;; but mostly for retrieving defrel parameters for derivations
(defun derived-param-list (rel derivation)
  (loop for p in (macro-parameter-lists rel) thereis
	(and (eq (car p) derivation) p)))

(defrepresentation individual)
(defderivation individual-derived)
(defun find-first-key (target-list keys)
  (or (loop for k in keys thereis (and (member k target-list) k))
      (error "none of expected elements ~A found in ~A" target-list keys)))

; ---------------- lisp-predicate ----------------
(defun lisp-predicate (name keys &optional (predname name) &aux imp-word)
 (warn-ignored-keys name keys (:definition :tester) 
  `(,(setq imp-word
	   (find-first-key '(:derivation :computation :representation) keys))
    ,(if (eq imp-word :representation) 'individual 'individual-derived)
    :tester (lambda (&rest ignore) (declare (ignore ignore))
		    '(lambda (rel &rest args)
		       (declare (ignore rel)
			   (optimize (speed 3)(safety 1)(compilation-speed 0)))
		       (ignore-errors (apply (function ,predname) args))))
    :derivation nil
    :computation nil
    :representation nil
    ,@keys
    :define-macro-accessors ,(not (eql name predname))
    :testeffort ; supply one if none mentioned
    (lambda (&rest ignore) (declare (ignore ignore)) 3))))

(defmacro def-some-lisp-preds ()
  (cons 'progn
	(append
	  (loop for n in '(< > <= >=) collect
		`(defrelation ,n :arity 2 :types (number number)
			      :size ((output output) nil)
			      :computation (lisp-predicate)))
	  (loop for n in '(string< string> string<= string>=
			   string-lessp string-greaterp string-not-lessp
			   string-not-greaterp) collect
		`(defrelation ,n :arity 2 :types
			      (((x) s.t. (or (string x) (symbol x)))
			       ((x) s.t. (or (string x) (symbol x))))
			      :size ((output output) nil) :equivs (:any :any)
			      :computation (lisp-predicate)))
	  (loop for n in '(char< char> char<= char>= 
			   char-lessp char-greaterp char-not-lessp
			   char-not-greaterp) collect
		`(defrelation ,n :arity 2 :types (character character)
			      :size ((output output) nil) :equivs (:any :any)
			      :computation (lisp-predicate))))))
(def-some-lisp-preds)

#-clisp
(or (find-package "LISP-EQUIV")
    (make-package "LISP-EQUIV" :use nil))
#+clisp ; likes to evaluate that make-package at compile time
(eval '(or (find-package "LISP-EQUIV")
	   (make-package "LISP-EQUIV" :use nil)))

; We want this to be like DEF - reloading makes apropriate changes.
; However we make no promises if name was previously defined some other way.
(defmacro lisp-predicate-equivalence-relation
	  (name sub &optional domain-test &rest canonicalizer
	   &aux (other-name (intern (string name)
				    (find-package "LISP-EQUIV"))))
  (when (and canonicalizer (null (rest canonicalizer)))
    (push domain-test canonicalizer)
    (setf domain-test nil))
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     ; have to do this in case sub changes - besides it's not a DB update
     (defun ,other-name (x y)
       (or (?? ,sub x y)
	   ,(if domain-test
		`(and (,domain-test x) (,domain-test y)(,name x y))
	      `(ignore-errors (,name x y)))))
     (progn ;; unless (?? equivalence-relation (relationp ',name)) ; previously defined
       (defrelation ,name :computation (lisp-predicate ,other-name) :arity 2
	    :define-macro-accessors nil
	    :alsofns ((lambda (rel)
			(++ equivalence-relation rel)
			,(cond
			   (canonicalizer
			    ; it's replacing - a noop is cheap
			    `(++ canonicalizer rel
				 (theap5relation ,(first canonicalizer))
				 ',(second canonicalizer)))
			   (t	; there might have been one before
			    '(-- canonicalizer rel $ $))))))
)
     
     ; previous sub might have been more specific
     (funcall ;; putting in the funcall rather than just the form avoids dumping
              ;; a loaded memo cell on the symbolics.
       #'(lambda ()
	   (do-s.t. 
	     ((sub) (and (isubrel sub (dbo relation ,name))
			 (not (subrel (dbo relation ,sub) sub))))
	     (-- subrel sub (dbo relation ,name)))))
	   
     (++ subrel (dbo relation ,sub) (dbo relation ,name))
     (dbo relation ,name)))

; = moved much earlier ...

;; claim: the relations char= and eql are identical
(lisp-predicate-equivalence-relation char= eql characterp eql identity)


(defun canonicalize-char-equal (c)
  (if (characterp c) (char-upcase c #+ignore (make-char c)) c))

(lisp-predicate-equivalence-relation char-equal eql characterp
				     eql canonicalize-char-equal)
(++ subrel (dbo relation char=) (dbo relation char-equal))

(defun arbitrary-compare-le (x y)
  (not (eq :greater (arbitrary-order x y))))

(defrelation arbitrary-compare-le :arity 2 :size ((output output) nil)
	     :equivs (:any :any) :computation (lisp-predicate))

(defun canonical-cl-string= (x)
  (if (symbolp x) (symbol-name x)
    (if (characterp x) (string x) x)))

; string= and string-equal work on either
(defun string-or-symbolp (x)
  (or (stringp x) (symbolp x)))

(lisp-predicate-equivalence-relation string= EQUAL STRING-OR-SYMBOLP
				     EQUAL canonical-cl-string=)
;;; (the relation ship) (string= x y) holds iff
;;; (the lisp predicate)(EQUAL x y) holds, or
;;; each of x and y is a string, char, or symbol, and they're
;;; STRING=.

;; CLtL provides almost NO help for us to canonicalize string-equal!
; If we wanted to do it "right" we'd just define the string-equal relation
; via our own program.
; As it is, we assume that different fonts never make characters non-char-equal.
(defun canonical-cl-string (x)
  (if (or (symbolp x) (stringp x) (characterp x))
      (string-upcase (map 'string 'canonicalize-char-equal (string x)))
    x))

(lisp-predicate-equivalence-relation string-equal string= STRING-OR-SYMBOLP
				     EQUAL canonical-cl-string)
;;; (the relation ship) (string-equal x y) holds iff
;;; (the lisp predicate)(EQUAL x y) holds, or
;;; each of x and y is a string, char, or symbol, and they're
;;; STRING-EQUAL.

(buffer-break)

;;(++ default-equivalence (relationp 'STRING) (relationp 'STRING-EQUAL))
(++ default-equivalence (relationp 'STRING) (relationp 'STRING=))

(loop for x in
      '((= <=) (= >=) (< <=) (> >=)
	(string< string<=) (string> string>=) (string= string<=) (string= string>=)
	(string-lessp string-not-greaterp) (string-greaterp string-not-lessp)
	(string-equal string-not-greaterp) (string-equal string-not-lessp)
	(char< char<=) (char> char>=) (char= char<=) (char= char>=)
	(char-lessp char-not-greaterp) (char-greaterp char-not-lessp)
	(char-equal char-not-greaterp) (char-equal char-not-lessp)
	;(char-lessp char<) seems not to be true (from the manual)
	)
      do (++ subrel (relationp (car x)) (relationp (cadr x))))

(defrelation typep :arity 2 :equivs (:any :any) :derivation (lisp-predicate)
	     :possibletoadd t :possibletodelete t)

(defrelation pathname
  :computation (lisp-predicate pathnamep)
  :arity 1 :equivs (:any))

(eval-when (:compile-toplevel :load-toplevel :execute)
(++ default-equivalence (theap5relation pathname)
      (theap5relation equal)))



; ---------------- lisp-function ----------------
; lisp-function
(defun lisp-function (name keys fname in-arity out-arity &aux imp-word)
 (warn-ignored-keys name keys (:definition :arity :tester :testeffort) 
  `(,(setq imp-word
	   (find-first-key '(:derivation :computation :representation) keys))
    ,(if (eq imp-word :representation) 'individual 'individual-derived)
    :arity ,(+ in-arity out-arity)
    :tester test-lisp-function
    :generator
    ,(cons 'lisp-function-generator (getf keys :generator nil))
    :size
    ,(cons (append (loop for i below in-arity collect 'input)
		   (loop for i below out-arity collect 'output))
	   (cons 1 (getf keys :size nil)))
    :derivation nil
    :computation nil
    :representation nil
    ,@keys
    :define-macro-accessors ,(not (eql name fname))
    :testeffort ; in case none supplied
    (lambda (&rest ignore) (declare (ignore ignore)) 5))))

(defun TEST-LISP-FUNCTION (rel &rest args &aux
			       (param-list
				(derived-param-list rel 'lisp-function))
			       input-arity output-arity fn)
  (setq args (copy-list args))
  (setf fn (cadr param-list)
	input-arity (caddr param-list)
	output-arity (cadddr param-list))
  (if (= 1 output-arity)
      `(lambda (ignore ,@args)
	 (declare (ignore ignore))
	 (ignore-errors
	   ,(get-test-function
	      (get-comparison rel (+ input-arity output-arity -1) t)
	      (cons fn (butlast args))
	      (car (last args)))))
      (let* ((gens (nthcdr input-arity args))
	     (vals (mapcar #'(lambda (g) (declare (ignore g)) (gensym "A")) gens)))
	`(lambda (ignore ,@args)
	   (declare (ignore ignore))
	   (ignore-errors
	     (multiple-value-bind ,vals
		 (,fn ,@(butlast args output-arity))
	       (and ,.(loop for v in vals as i from input-arity as g in gens collect
			    (get-test-function
			       (get-comparison rel i t) v g)))))))))

(defun lisp-function-generator (subsetflg vars rel &rest args &aux
				   (param-list
				    (derived-param-list rel 'lisp-function))
				   input-arity output-arity fn)
  (declare (ignore args subsetflg vars))
  (setf fn (cadr param-list)
	input-arity (caddr param-list)
	output-arity (cadddr param-list))
  (when t #+ignore ; this screws up on permutations!
	; Inappropriate gen's filtered elsewhere anyway.
    (or subsetflg
	(and (= output-arity (length vars))
	     (loop for v in vars as i from 0 always
		   (eq v (nth (+ i input-arity) args)))))
    `((initialstate
	(lambda (ignore &rest inputs)
	  (declare (ignore ignore))
	  (let ((state *lf-done*) state2) ; compiler bug
	    ; we use *lf-done* to signify done
	    ; if error no values will be generated
	    (ignore-errors
	      (multiple-value-lambda-bind (&rest vals)
		(apply #',fn inputs)
		;;; optimized for case of a single output value that
                ;;; is not list-valued
		(setq state
		      (cond ((null vals) *lf-done*)
			    ((or (cdr vals) (consp (car vals)))
			     (copy-list vals))
			    (t (car vals))))))
	    (setq state2 state)  ;; reduces consing on symbolics!!!
	    #'(lambda nil
		(cond ((eq state2 *lf-done*) t)
		      ((consp state2)
		       (multiple-value-prog1
			       (apply #'values nil state2)
			       (setq state2 *lf-done*)))
		      (t (multiple-value-prog1 (values nil state2)
				(setq state2 *lf-done*))))))))
      (template
	,(loop for i  below (+ input-arity output-arity)
	       when (< i input-arity)
	       collect 'input
	       else collect 'output))
      (effort ,(testeffort (cons rel (list-of-xs (+ input-arity output-arity))))))))

(defparameter *lf-done* (cons nil nil))

; some people will do anything for a cons
; used to be &aux #, (loop ...) but #, doesn't compile well on hp
(defvar *xs* (loop for i below 20 collect 'x))

(defun list-of-xs (n &aux (xs *xs*))
   (if (< n 0) ()
     (if (<= n 20) (loop for i from n below 20 do (pop xs)
			 finally  (return xs))
       (loop for i from 20 below n do (push 'x xs)
	     finally  (return xs)))))

(defrelation + :types (number number number) :computation (lisp-function + 2 1)
	     :size ((output output output) nil
		    (output input input) 1
		    (input output input) 1)
	     :generator
	     ((simplegenerator (a output c)
			       (and (numberp a) (numberp c) (- c a)))
	      (simplegenerator (output a c)
			       (and (numberp a) (numberp c) (- c a)))))

(defrelation - :definition ((x y z) s.t. (+ y z x))
	     :inline t :types (number number number))
; types needed cause most-specific-types-of not define yet

(defrelation * :types (number number number) :computation (lisp-function * 2 1)
	     :size ((output output output) nil
		    (output input input) 1
		    (input output input) 1))
; can't generate x s.t. (* 0 x 0)

(defrelation / :types (number number number) :computation (lisp-function / 2 1)
	     :size ((output output output) nil
		    (output input input) 1
		    (input output input) 1)
	     :generator
	     ((simplegenerator (a output c)
			       (and (numberp a) (numberp c)
				    (ignore-errors (/ a c))))
	      (simplegenerator (output a c)
			       (and (numberp a) (numberp c) (not (zerop a))
				    (ignore-errors (* c a))))))

(defrelation max :types (number number number) :computation (lisp-function max 2 1)
	     :size ((output output output) nil))
(defrelation min :types (number number number) :computation (lisp-function min 2 1)
	     :size ((output output output) nil))
(defrelation gcd :types (integer integer integer) :computation (lisp-function gcd 2 1)
	     :size ((output output output) nil))
(defrelation lcm :types (integer integer integer) :computation (lisp-function lcm 2 1)
	     :size ((output output output) nil))
(defrelation expt :types (number number number) :computation (lisp-function expt 2 1)
	     :size ((output output output) nil))


(defrelation truncate :types (number number integer number)
	     :computation (lisp-function truncate 2 2)
	     :size ((output output output output) nil
		    (output input input input) 1)
	     :generator
	     ((simplegenerator (output divisor quotient remainder)
		 (let ((divisor (canonicalize-= divisor))
		       (quotient (canonicalize-= quotient))
		       (remainder (canonicalize-= remainder)))
		   (and (numberp divisor) (integerp quotient) (numberp remainder)
			(not (complexp divisor)) (not (complexp remainder))
			(< (abs remainder) (abs divisor))
			(+ remainder (* divisor quotient)))))))

(defrelation floor :types (number number integer number)
	     :computation (lisp-function floor 2 2)
	     :size ((output output output output) nil))
(defrelation ceiling :types (number number integer number)
	     :computation (lisp-function ceiling 2 2)
	     :size ((output output output output) nil))
(defrelation round :types (number number integer number)
	     :computation (lisp-function round 2 2)
	     :size ((output output output output) nil))

(defrelation abs :types (number number)
	     :computation (lisp-function abs 1 1)
	     :size ((output output) nil))
(defrelation isqrt :types (integer integer)
	     :computation (lisp-function isqrt 1 1)
	     :size ((output output) nil))
(defrelation numerator :types (rational integer)
	     :equivs (= =) ; doesn't know equiv for rational
	     :computation (lisp-function numerator 1 1)
	     :size ((output output) nil))
(defrelation denominator :types (rational integer)
	     :equivs (= =) ; doesn't know equiv for rational
	     :computation (lisp-function denominator 1 1)
	     :size ((output output) nil))

(defrelation length :equivs (:any =) :types (list integer)
	     :computation (lisp-function length 1 1)
	     :size ((output output) nil))

;; For some reason these used to be defined with equivalence EQUAL EQUAL.
;; Also, perhaps we should consider them to be near relations (not claim
;; they're never smashed).
;
; Since these are never used and one might want different versions to be
; triggerable or not, I'll just leave them out for now...
#+ignore ; similarly for rest
(defrelation first :equivs (:any :any) :types (list entity)
	     :computation (lisp-function first 1 1)
	     :size ((output output) nil))

(defrelation symbol-name :equivs (eql string=) :types (symbol string)
	     :computation (lisp-function symbol-name 1 1)
	     :size ((output output) nil))

;; We could certainly add a few more generators here:
; abs could have two (the other of size 2)
; isqrt could have two - generate all from input^2 thru ((input+1)^2-1)

; ---------------- coded ----------------

(defun coded (name keys codedefn &aux arity imp-word)
  ;; codedefn should be ((var*) s.t. declaration* form*)
 (warn-ignored-keys name keys (:definition :arity :tester) 
  (unless (and (> (length codedefn) 2) (or (listp (first codedefn))
					   (symbolp (first codedefn)))
	       (symbolp (second codedefn))
	       (string-equal "s.t." (symbol-name (second codedefn))))
    (error "illegal code defn ~A" codedefn))
  ;; ( var s.t. ...) ==> ((var) s.t. ...)
  (unless (listp (first codedefn))
    (setf codedefn (cons (list (first codedefn)) (rest codedefn))))
  (setf arity (length (first codedefn)))
  `(,(setf imp-word
	   (find-first-key '(:derivation :computation :representation) keys))
    ,(if (eq imp-word :representation) 'individual 'individual-derived)    
    :arity ,arity
    :tester (lambda (&rest ignore) (declare (ignore ignore))
		    '(lambda (ignore ,@(first codedefn))
		       (declare (ignore ignore))
		       ,.(cddr codedefn)))
    :derivation nil :computation nil :representation nil
    ,@keys
    :testeffort ; in case none supplied
    (lambda (&rest ignore) (declare (ignore ignore)) 30))))


(defun between-gen (&rest ignore)
  (declare (ignore ignore))
  (copy-list
    '((template (output input input))
      (initialstate
	(lambda (ignore lower upper &aux state)
	  (declare (ignore ignore))
	  (cond ((and (?? integer lower) (?? integer upper))
		 (setq lower (canonicalize-= lower)
		       upper (canonicalize-= upper))
		 (setf state (1- lower))
		 #'(lambda nil (if (< state upper)
				   (values nil (incf state))
				   T)))
		(t #'(lambda nil t)))))
      (effort 300))))
; generator apparently has to come first

(defrelation integer-in-range :types (integer integer integer)
	     :generator (between-gen)
	     :computation
	     (coded ((n lower upper)
			 s.t.
			 (and (?? integer n)
			      (?? integer lower)
			      (?? integer upper)
			      (<= lower (canonicalize-= n) (canonicalize-= upper))))))
; I don't know where this "belongs", but let's think of it as 3-ary <= ...



; *** I don't think this is worth while.
; The relation below is really only good for eql elements so the last argument
; is wasted.
; NOTE: Display UPDATE code for description's uses MEMBER with arbitrary
; equivalence relations as slot 2. ;BIB 04/27/89 11:45:19
(defrelation MEMBER
   :computation (coded ((x l EQUIV) s.t.
		       (and (consp l)
			    (?? equivalence-relation equiv)
			    (member x l :test #'(lambda (x y)
						  (testrel  equiv x y))))))
   :types (entity entity equivalence-relation)
   :type-enforcements (:none :none :none)
   :equivs (:default :any :default)
   ; 1st would be more useful as :any but findgenerators is too smart:
   ; it realizes that vars without comparisons cannot be generated!
   :generator ((simplegenerator
		 (OUTPUT L E)
		 (and (consp l) (?? equivalence-relation E)
		      (remove-duplicates L :test #'(lambda (x y) (testrel E x y)))))))

(defrelation MEMBER-eql
   :computation (coded ((x l) s.t.
		       (and (consp l)
			    (member x l :test #'eql))))
   :types (entity entity)
   :type-enforcements (:none :none)
   :equivs (eql :any)
   :generator ((simplegenerator
		 (OUTPUT L)
		 (and (consp l)
		      (remove-duplicates L :test #'eql)))))
(defrelation MEMBER-equal
   :computation (coded ((x l) s.t.
		       (and (consp l)
			    (member x l :test #'equal))))
   :types (entity entity)
   :type-enforcements (:none :none)
   :equivs (equal :any)
   :generator ((simplegenerator
		 (OUTPUT L)
		 (and (consp l)
		      (remove-duplicates L :test #'equal)))))
(defrelation MEMBER-=
   :computation (coded ((x l) s.t.
		       (and (consp l)
			    (member x l :test #'=))))
   :types (entity entity)
   :type-enforcements (:none :none)
   :equivs (= :any)
   :generator ((simplegenerator
		 (OUTPUT L)
		 (and (consp l)
		      (remove-duplicates L :test #'=)))))

(defrelation MEMBER-STRING-EQUAL
   :computation (coded ((x l) s.t.
		       (and (consp l)
			    (member x l :test #'STRING-EQUAL))))
   :types (entity entity)
   :type-enforcements (:none :none)
   :equivs (STRING-EQUAL :any)
   :generator ((simplegenerator
		 (OUTPUT L)
		 (and (consp l)
		      (remove-duplicates L :test #'string-equal)))))

(defrelation MEMBER-STRING=
   :computation (coded ((x l) s.t.
		       (and (consp l)
			    (member x l :test #'STRING=))))
   :types (entity entity)
   :type-enforcements (:none :none)
   :equivs (STRING= :any)
   :generator ((simplegenerator
		 (OUTPUT L)
		 (and (consp l)
		      (remove-duplicates L :test #'string=)))))

; What has become of the declaration for equalp? ***
;(++ equivalence-relation (dbo relation equalp))
;(++ subrel (dbo relation equal) (dbo relation equalp))

; ---------------- tclosure ----------------

(defun tclosure (name keys irelname &aux irel cmp)
 (warn-ignored-keys name keys (:definition :arity :equivs :tester :generator :trigger)
  ;; allow anon-rel for irelname
  (when (consp irelname)
      (setf irelname
	    (relationnamep (relationp+ irelname))))
  (unless (setq irel (relationp irelname))
    (error "no such relation as ~a" irelname))
  (unless (eq (setq cmp (get-comparison irel 0 t)) (get-comparison irel 1 t))
    (error "~A does not have consistent comparisons" irelname))
  `(,(find-first-key '(:derivation :computation) keys) tclosure 
    :arity 2 :equivs (,(relationnamep cmp) ,(relationnamep cmp))
    :types ,(getf keys :types
		  (loop for pos below 2 collect
			(forany x s.t. (typeconstraint irel pos x)
				(or (relationnamep x) x) ; description
				ifnone 'entity)))
    :alsofns
    ,(cons `(lambda (rel) (++ tclosure (relationp ',irelname) rel))
	   (getf keys :alsofns))
    :trigger ((,irelname - trigger--tclosures -)
	      (,irelname + trigger++tclosures +))
    :derivation nil :computation nil
    ,@keys)))

; ----------------------------------------------------------------
#|
The examples below are all derived from the same relation:
(works-on% person project date percent)

Count:
(defrelation count-projects :derivation (cardinality works-on% (input output input output) &optional zero-tuples))
(count-projects person date z) iff
   (zero-tuples or (z neq 0)) and
   (loop for (u v) s.t. (works-on% person u date v) count t) = z

Sum:
(defrelation total-percent :derivation (sum works-on% (input output input sum)))
(total-percent person date z) iff
  (?? E (u v) (works-on% person u date v)) and
  (loop for (u v) s.t. (works-on% person u date v) sum v) = z
The implementation ASSUMES that all tuples will contain numbers in the "sum" position.

Extreme:
(Defrelation highest-effort-project 
   :derivation (extreme works-on% > (input output input extreme)))
(highest-effort-project person project date percent) iff
  (works-on% person project date percent) and
  (A (x y) (implies (works-on% person x date y)
		    (or ( percent y)
			(and (eql x project) (= percent y)))))
Similarly
(DefRelation latest-data
   :derivation (extremerel works-on% later (input output extreme output)))
would include for each person all tuples with the latest date.
The implementation ASSUMES that the ordering relation is transitive and static.
----------------------------------------------------------------
|#

; ---------------- cardinality ----------------
; the :representation translator
(defun cardinality (name keys origrelname i-o-pattern &optional zero-tuples
			 &aux arity equivs origrel)
  (declare (ignore zero-tuples))
 (warn-ignored-keys name keys 
  (:definition :arity :equivs :implementation :types
	       :tester :trigger)
  ;; allow anon-rel for origrelname
  (when (consp origrelname)
      (setf origrelname
	    (relationnamep (relationp+ origrelname))))
  (loop for x in i-o-pattern unless (member x '(input output)) do
	(error "The i-o-pattern for a countrel may only contain INPUT and OUTPUT"))
  (unless (setf origrel (relationp origrelname))
    (error "unknown relation - ~A" origrelname))
  (unless (= (arity* origrel) (length i-o-pattern))
    (error "The i-o-pattern should have one element for each argument of ~A"
	   origrelname))
  (setf arity (1+ (loop for x in i-o-pattern when (eq x 'input) count t))
	equivs (nconc
		(loop with r
		   for x in i-o-pattern as i from 0 when (eq x 'input) collect
		     (if (setf r (relationp (get-comparison origrel i)))
			 (relationnamep r)
			 (error "Countrel of relation with ambiguous comparisons")))
		(list '=)))

  `(:derivation cardinality
    :arity ,arity
    :equivs ,equivs
    :count
    ,(append `((,.(loop for i below (1- arity) collect 'entity) output)
	       :countspec :optional :enforcement :none)
	     (getf keys :count))
    :types (,.(loop for i from 0 as p in i-o-pattern
		    when (eq p 'input) collect
		    (let ((tp (any x s.t. (typeconstraint origrel i x) ifnone 'entity)))
		      (or (relationnamep tp) tp)))
	    integer)
    :size
    ,(append `((,.(loop for i below (1- arity) collect 'input) output) 1)
	     (getf keys :size))
    :trigger ((,origrelname +- trigger-count +-))
    :implementation nil :representation nil :computation nil
    ,@keys)))

;; THIS SHOULD BE DONE VIA A GENSYM DEFUN IN ALSOFNS
;; SO THE COMPILATION GOES TO A FILE
(defun trigger-count (countrel &rest ignore) (declare (ignore ignore))
  (funcall
    (or (get-structure-property countrel 'cached-trigger-fn)
	(put-structure-property countrel (compile-count-trigger countrel)
				'cached-trigger-fn))))

(defun compile-count-trigger (countrel)
  (let ((parmlist (derived-param-list countrel 'cardinality)))
    (let ((origrel (relationp+ (second parmlist)))
	  (pattern (third parmlist))
	  (zero-tuples (when (fourth parmlist) t))
	  invars outvars allvars maintainedrel)
      (setf allvars (mapcar #'(lambda (p) (declare (ignore p)) (gensym "X")) pattern)
	    invars (loop for a in allvars as p in pattern when (eq p 'input)
			 collect a)
	    outvars (loop for a in allvars as p in pattern when (eq p 'output)
			  collect a)
	    maintainedrel  ;; hack because countrel can't be maintained
	    (loop for (rel desc rule) s.t. (and (MaintainedRel rel desc rule)
						(relation-in-defn countrel rel))
		  thereis (and (eq countrel (car (third desc)))
			       (equal (car desc) (cdr (third desc))))))
      (compile-ap
	`(lambda (&aux difference previous)
	   (do-s.t. (,invars (change ,outvars (,origrel ,@allvars)))
		 (setf difference
		       (- (loop for ,outvars s.t.
				(start (,origrel ,@allvars)) count t)
			  (loop for ,outvars s.t.
				(start (not (,origrel ,@allvars))) count t)))
		 (unless (zerop difference)
		   (setf previous
		     (any n s.t. (previously (,(or maintainedrel countrel) ,@invars n))
			      ifnone 0))
		   (unless (and ,(not zero-tuples) (zerop previous))
		     (-- ,countrel ,@invars previous))
		   (unless (and ,(not zero-tuples)
				(= difference (- previous)))
		     (++ ,countrel ,@invars (+ previous difference))))))))))

(defun test-countrel (rel &aux (var (gensym "X"))
			  (zero-tuples
			   (fourth
			    (derived-param-list rel 'cardinality)))
			  (args (loop for i below (arity* rel) collect (gensym "V"))))
  `(lambda (ignore ,@args) (declare (ignore ignore))
     (and (integerp ,(car (last args)))
	  ,@(unless zero-tuples `((not (zerop ,(car (last args))))))
	  (loop for ,var s.t. (,rel ,@(butlast args) ,var)
		;; this is a crock -- using source code in terms of REL itself!
		thereis (= ,var ,(car (last args)))))))

#|
We will always generate the count (all templates end in OUTPUT)
Example: rel = (count-projects person date)
         newrel = (works-on% person project date percent)
         pat = (input output input output)
         vars = (var-person var-count), args = (var-person date1 var-count)
Goal program:
 <create a tree: person => number
 (loop for (person project percent) s.t.
       (works-on%person project date1 percent) do
       (incf (tree person)))
 generate the tree
|#
;; altered for case of zero-tuples/subsetflg 1/94 - donc 
#+ignore
(defun generate-countrel (subsetflg vars rel &rest args
			   &aux (parmlist
				 (derived-param-list rel 'cardinality))
			   (pat (third parmlist))
			   (zero-tuples (fourth parmlist)))
  (when (and (null subsetflg) zero-tuples)
    ;; can't generate anything but the count!!
    (let ((non-count-args (butlast args)))
      (loop for v in vars when (member v non-count-args) do
	(return-from generate-countrel nil))))
  (when subsetflg
    (return-from generate-countrel
      (remove nil
	      (loop for v in (xproduct (loop for x in vars collect
					     (if (eq x (car (last args)))
						 (list x)
					       (list nil x))))
		    nconc (apply #'generate-countrel nil (remove nil v) rel args)))))
  
  (let ((newrel (relationp+ (second parmlist)))
	(equivs (mapcar #'varcompare vars))
	(vars (vars-to-names vars))
	(args (vars-to-names args))
	(nvars 0)
	desc newvars newargs gen)
    (let ((aa args))
      (loop for p in pat do;; this throws away the last arg ...
	   (cond ((eq p 'input)
		  (push (pop aa) newargs)
		  ;; this is really correct - every input is an arg and no others
		  ;; (except the count at the end) are ...
		  (when (member (first newargs) vars)
		    (incf nvars)
		    (push (first newargs) newvars)))
		 (t (let ((new (gensym "V")))
		      (push new newvars)
		      (push new newargs))))))
    (setf newvars (nreverse newvars) newargs (nreverse newargs))
    (setf desc (expanddescription
		`(,newvars s.t. (notinline (,newrel ,@newargs)))
		:allowevalargs t))
    (unless (setf gen (findgenerator (first desc) (third desc) t))
      (return-from generate-countrel nil))

    `((template (,.(loop for x in
			       (or (second (assoc 'template (sgen gen)))
				   (make-list (length pat) :initial-element 'input)) ; for testers
			 as y in pat when (eq y 'input) collect x)
		   output))
      (effort ,(+ (effort gen)		; generate the tuples and classify each
		  (* 30 (relationsize (first desc) (third desc)) (length vars))))
      (initialstate
       (lambda (rel ,.(loop for arg in (rest (third desc))
			    unless (member arg (first desc)) collect arg))
	 (declare (ignore rel))
	 ,(if zero-tuples
	      `(let ((n (loop for ,(vars-to-names (first desc))
		               s.t. ,(vars-to-names-wff (third desc))
		          count t)))
		 #'(lambda ()
		     (if n
		       (values nil (prog1 n (setf n nil)))
		       t)))
	      `(let ((tree (createtree)))
		 (loop for ,(vars-to-names (first desc)) s.t. ,(vars-to-names-wff (third desc))
		       do (increment-tree-count tree
				    ,.(loop for v in vars as e in equivs
					    as i below nvars nconc (rel-or-fn v e))))
		 (treegen-common-from-data
		  ,(1+ nvars)
		  0
		  nil
		  (purify-tree tree)))))))))

(defun generate-countrel (subsetflg origvars rel &rest origargs
			   &aux (parmlist
				 (derived-param-list rel 'cardinality))
			   (vars origvars) (args origargs)
			   (pat (third parmlist))
			   (zero-tuples (fourth parmlist)))
  (when (and (null subsetflg) zero-tuples)
    ;; can't generate anything but the count!!
    (let ((non-count-args (butlast args)))
      (loop for v in vars when (member v non-count-args) do
	(return-from generate-countrel nil))))
  (when subsetflg
    (return-from generate-countrel
      (values-list
       (remove nil
	      (loop for v in (xproduct (loop for x in vars collect
					     (if (eq x (car (last args)))
						 (list x)
					       (list nil x))))
		    collect (apply #'generate-countrel nil
				   (remove nil v) rel args))))))
  ;; "new" below really means pertaining to the basis rel  
  (let ((newrel (relationp+ (second parmlist)))
	#+ignore (equivs (mapcar #'varcompare vars))
	(vars (vars-to-names vars))
	(args (vars-to-names args))
	(nvars 0)
	desc sub newvars newargs gen)
    (let ((aa args))
      (loop for p in pat do;; this throws away the last arg ...
	   (cond ((eq p 'input)
		  (push (pop aa) newargs)
		  ;; really correct - every input is an arg and no others
		  ;; (except the count at the end) are ...
		  (when (member (first newargs) vars)
		    (incf nvars)
		    (push (first newargs) newvars)))
		 (t (let ((new (gensym "V")))
		      (push new newvars)
		      (push new newargs))))))
    (setf newvars (nreverse newvars) newargs (nreverse newargs))
    (multiple-value-setq ;; *** save sub to put back in desc, needed
	;; to figure out the right args for lambda below.
     (desc sub)
     (expanddescription
      `(,newvars s.t. (notinline (,newrel ,@newargs)))
      :allowevalargs t))
    (setf desc (sublis (loop for s in sub collect (cons (car s)(cadr s)))
		       desc))
    (unless (setf gen (findgenerator (first desc) (third desc) t))
      (return-from generate-countrel nil))
 ;; Below is a generator for the countrel.  Its template, the args to its
 ;; initialstate and the outputs should be ordered by the arglist of the
 ;; countrel, not the basis rel !! ***
    `((template ,(loop for a on args collect
		       (if (not (cdr a)) 'output ;; count is always output
			 (if (member (car a) vars) 'output 'input)))
		#+ignore ;; ***
		(,.(loop for x in
			 (or (second (assoc 'template (sgen gen)))
			     ;; for testers
			     (make-list (length pat) :initial-element 'input))
			 as y in pat when (eq y 'input) collect x)
		   output))
      (effort ,(+ (effort gen)	;; generate the tuples and classify each
		  (* 30 (relationsize (first desc) (third desc)) (length vars))))
      (initialstate
       (lambda (rel ,.(loop for a in args unless (member a vars) collect a)
		    #+ignore ;; ***
		    (loop for arg in (rest (third desc))
			  unless (member arg (first desc)) collect arg))
	 (declare (ignore rel))
	 ,(if zero-tuples
	      `(let ((n (loop for ,(vars-to-names (first desc))
		               s.t. ,(vars-to-names-wff (third desc))
		          count t)))
		 #'(lambda ()
		     (if n
		       (values nil (prog1 n (setf n nil)))
		       t)))
	      `(let ((tree (createtree)))
		 (loop for ,(vars-to-names (first desc))
		       s.t. ,(vars-to-names-wff (third desc))
		       do (increment-tree-count tree
				,.(loop for a on args as oa in origargs
					when (cdr a) ;; except count
					when (member (car a) vars) nconc
					(rel-or-fn (car a) (varcompare oa)))
				#+ignore ;; ***
				(loop for v in vars as e in equivs
				      as i below nvars nconc (rel-or-fn v e))))
		 (treegen-common-from-data
		  ,(1+ nvars)
		  0
		  nil
		  (purify-tree tree)))))))))

(defderivation cardinality
  :tester (lambda (rel &rest ignore) (declare (ignore ignore)) (test-countrel rel))
  :generators (generate-countrel))


; adapted from treeadder
(defun construct-tree (tree &rest val-equiv-pairs &aux subtree)
  (loop while val-equiv-pairs do
	(let ((val (pop val-equiv-pairs)) (equiv (pop val-equiv-pairs)))
	  (tagbody loop
	      (cond ((integerp (first tree))	; list representation
		     (cond ((setf subtree (assoc val (rest tree) :test equiv))
			    (setf tree (rest subtree)))	;already stored
			   (t			; has to be inserted
			    (cond ((> (incf (first tree)) *maxtreelist*) 
				   (convert-tree-to-hashtable tree equiv nil)
				   (go loop))
				  (t (setf subtree (createtree))
				     (push (cons val subtree)
					   (rest tree))
				     (setf tree subtree))))))
		    (t				;hash array representation
		     (if (setf subtree (gethash val (first tree)))	; already stored
			 (setf tree subtree)
			 (setf (gethash val (first tree))
			       (setf tree (createtree)))))))))
  tree)

(defun increment-tree-count (tree &rest val-equiv-pairs)
  (setf tree (apply #'construct-tree tree val-equiv-pairs))
  (if (rest tree) (incf (cadr tree)) (setf (rest tree) (list 1))))

(defun rel-or-fn (v e)
  (let ((cnc (c-and-c e)))
    (if (member cnc '(eq eql equal)) `(,v (function ,cnc))
	`((,(cadr cnc) ,v) (function ,(car cnc))))))

#|
(defrelation works-on% :arity 4)

(defrelation count-projects
	     :derivation (cardinality works-on% (input output input output))
	     :cache-generators nil)

(set-listof a s d f s.t. (works-on% a s d f) nil)
(loop for (person project day foo) in
      '((don fsd today 10)
	(don kbsa today 20)
	(don fsd yesterday 30)
	(bob fsd yesterday 15)
	(bob fsd today 25)
	(bob kbsa yesterday 35))
      do (++ works-on% person project day foo))
(listof x y s.t. (count-projects x 'today y))
((DON 2) (BOB 1))
(listof x y s.t. (count-projects x y 2))
((DON TODAY) (BOB YESTERDAY))
(?? count-projects 'BOB 'YESTERDAY 2)
T
(?? count-projects 'BOB 'YESTERDAY 3)
NIL
(defautomation note-add-count-projects
	       ((x y z) s.t. (start (count-projects x y z)))
 (lambda (x y z) (format *standard-output* "(++ count-projects ~A ~A ~A)" x y z)))
(defautomation note-del-count-projects
	       ((x y z) s.t. (start (not (count-projects x y z))))
  (lambda (x y z) (format *standard-output* "(-- count-projects ~A ~A ~A)" x y z)))
(++ works-on% 'bob 'b-o 'yesterday 40)
 =>(-- count-projects BOB YESTERDAY 2)
   (++ count-projects BOB YESTERDAY 3)
(-- works-on% 'bob 'b-o 'yesterday 40)
 =>(-- count-projects BOB YESTERDAY 3)
   (++ count-projects BOB YESTERDAY 2)
; also adding a first tuple, deleting a last tuple
|#

; ---------------- sum ----------------

; the :representation translator
(defun sum (name keys origrelname i-o-pattern
		 &aux (arity 0) sum-pos equivs origrel)
 (warn-ignored-keys name keys
  (:definition :arity :equivs :implementation :types
	       :computation :tester :trigger)
  ;; allow anon-rel for origrelname
  (when (consp origrelname)
      (setf origrelname
	    (relationnamep (relationp+ origrelname))))
  (dolist (x i-o-pattern)
    (cond ((eq x 'sum)
	   (if sum-pos
	       (error "The i-o-pattern for a sumrel may contain only one SUM")
	       (setf sum-pos arity)))
	  ((or (eq x 'input) (eq x 'output)))
	  (t (error "The i-o-pattern for a sumrel may only contain SUM once")))
    (incf arity))
  (unless sum-pos (error "The i-o-pattern for a sumrel must contain SUM"))
  (unless (setf origrel (relationp origrelname))
    (error "unknown relation - ~A" origrelname))
  (unless (= (arity* origrel) arity)
    (error "The i-o-pattern should have one element for each argument of ~A" origrelname))
  (setf arity (1+ (count 'input i-o-pattern)))
  (setf equivs (nconc
		 (loop for x in i-o-pattern as i from 0 with r
		     when (eq x 'input) collect
		     (if (setf r (relationp (get-comparison origrel i)))
			 (relationnamep r)
			 (error "Sumrel of relation with ambiguous comparisons")))
		 (list '=)))
  `(:derivation sum
    :arity ,arity :equivs ,equivs
    :count
    ,(append `((,.(loop for i below (1- arity) collect 'entity) output)
	       :countspec :optional :enforcement :none)
	     (getf keys :count))
    :types (,.(loop for i from 0 as p in i-o-pattern
		    when (eq p 'input) collect
		    (let ((tp (any x s.t. (typeconstraint origrel i x) ifnone 'entity)))
		      (or (relationnamep tp) tp)))
	    number)
    :size
    ,(cons (nconc (loop for i below (1- arity) collect 'input)  '(output))
	   (cons 1 (getf keys :size)))
    :trigger ((,origrelname +- trigger-sum +-))
    ,@keys)))

;; THIS SHOULD BE DONE VIA A GENSYM DEFUN IN ALSOFNS
;; SO THE COMPILATION GOES TO A FILE
;; AND THE CODE MUST BE PRODUCED TO USE RELATION NAMES RATHER
;; THAN RELATION OBJECTS.
(defun trigger-sum (sumrel &rest ignore) (declare (ignore ignore))
  (funcall
    (or (get-structure-property sumrel 'cached-trigger-fn)
	(put-structure-property sumrel (compile-sum-trigger sumrel)
				'cached-trigger-fn))))

(defun compile-sum-trigger (sumrel)
  (let ((parmlist (derived-param-list sumrel 'sum)))
    (let ((origrel (relationp+ (cadr parmlist)))
	  (pattern (caddr parmlist))
	  invars outvars sumvars allvars maintainedrel)
      (setf allvars (mapcar #'(lambda (p) (declare (ignore p))
				(gensym "X")) pattern)
	    invars (loop for a in allvars as p in pattern when (eq p 'input)
			 collect a)
	    outvars (loop for a in allvars as p in pattern when (eq p 'output)
			  collect a)
	    sumvars (loop for a in allvars as p in pattern when (eq p 'sum)
			  collect a)
	    maintainedrel ;; hack because sumrel can't be maintained
	    (loop for (rel desc rule) s.t. (and (MaintainedRel rel desc rule)
						(relation-in-defn sumrel rel))
		  thereis (and (eq sumrel (relationp (car (third desc))))
			       (equal (car desc) (cdr (third desc)))
			       rel)))
      (compile-ap
	`(lambda nil
	   (loop for (,@invars ,@sumvars) s.t. (change ,outvars (,origrel ,@allvars))
		 with difference with previous with add with delete do
		 (setf add nil delete nil)
		 (setq difference
		       (- ,(if (possibletoupdate origrel t)
			       `(loop for (,@outvars ,@sumvars) s.t.
				      (start (,origrel ,@allvars))
				      do (setf add t) sum ,@sumvars)
			       0)
			  ,(if (possibletoupdate origrel nil)
			       `(loop for (,@outvars ,@sumvars) s.t.
				      (start (not (,origrel ,@allvars)))
				      do (setf delete t) sum ,@sumvars)
			       0)))
		 (cond ,.(when (possibletoupdate origrel t)
			   `(((and add
				   ,(if maintainedrel
					`(?? not (e (n) (previously (,maintainedrel
								     ,@invars n))))
					`(?? not (e (,@outvars ,@sumvars)
						    (previously (,origrel ,@allvars))))))
			      (++ ,sumrel ,@invars difference))))
		       ,.(when (possibletoupdate origrel nil)
			   `(((and delete (?? not (e (,@outvars ,@sumvars)
						     (,origrel ,@allvars))))
			      (-- ,sumrel ,@invars (- difference)))))
		       ((zerop difference))
		       (t (setq previous 
				(any n s.t. (previously (,(or maintainedrel sumrel)
							 ,@invars n))
				     ifnone 0 ;;; ifnone clause should not occur
				     ))
			  (-- ,sumrel ,@invars previous)
			  (++ ,sumrel ,@invars (+ previous difference))))))))))

(defun test-sumrel (rel &aux (var (gensym "X"))
			  (args (loop for i below (arity* rel) collect (gensym "V"))))
  `(lambda (ignore ,@args) (declare (ignore ignore))
     (and (numberp ,(car (last args)))
	  (loop for ,var s.t. (,rel ,@(butlast args) ,var)
		thereis (= ,var ,(car (last args)))))))

#|
We will always generate the sum (all templates end in OUTPUT)
Example: rel = (total% person date)
         newrel = (works-on% person project date percent)
         pat = (input output input sum)
         vars = (var-person var-sum), args = (var-person date1 var-sum)
Goal program:
 <create a tree: person => number
 (loop for (person project percent) s.t.
       (works-on%person project date1 percent) do
       (incf (tree person) percent))
 generate the tree
|#

#+ignore
(defun generate-sumrel (subsetflg vars rel &rest args
				    &aux desc newvars newargs sumvar gen equivs
				    newrel pat (nvars 0))
  (when subsetflg
    (return-from generate-sumrel
      (remove nil ; no need to cache - this will probably only happen once anyhow
	      (loop for v in (xproduct (loop for x in vars collect
					     (if (eq x (car (last args))) (list x)
						 (list nil x))))
		    nconc
		    (apply #'generate-sumrel nil (remove nil v) rel args)))))
  (let ((parmlist (derived-param-list rel 'sum)))
    (setf newrel (relationp+ (second parmlist))
	  pat (third parmlist)
	  equivs (mapcar #'varcompare vars)
	  vars (vars-to-names vars)
	  args (vars-to-names args))
    (let ((aa args))
      (loop for p in pat do ; this throws away the last arg ...
	  (cond ((eq p 'input)
		 (push (pop aa) newargs)
		 (when (member (first newargs) vars)
		   (incf nvars)
		   (push (first newargs) newvars)))
		((eq p 'sum)
		 (push (setf sumvar (gensym "V")) newvars)
		 (push sumvar newargs))
		(t (let ((new (gensym "V")))
		     (push new newvars)
		     (push new newargs))))))
    (setf newvars (nreverse newvars) newargs (nreverse newargs))
    (setf desc (expanddescription `(,newvars s.t. (notinline (,newrel ,@newargs)))
				  :allowevalargs t))
    (unless (setf gen (findgenerator (first desc) (third desc) t))
	(return-from generate-sumrel nil))
    `((template (,.(loop for x in
			 (or (second (assoc 'template (sgen gen)))
			     (make-list (length pat) :initial-element 'input)) ; for testers
			 as y in pat when (eq y 'input) collect x)
		 output))
      (effort ,(+ (effort gen) ; generate the tuples and classify each
		  (* 30 (relationsize (first desc) (third desc)) (length vars))))
      (initialstate
	(lambda (rel ,.(loop for arg in (rest (third desc))
			     unless (member arg (first desc)) collect arg))
	  (declare (ignore rel))
	  (let ((tree (createtree)))
	    (loop for ,(vars-to-names (first desc)) s.t. ,(vars-to-names-wff (third desc))
		  do (increment-tree-sum tree ,sumvar
			  ,.(loop for v in vars as e in equivs
				  as i below nvars nconc (rel-or-fn v e))))
	    (treegen-common-from-data
	      ,(1+ nvars)
	      0
	      nil
	      (purify-tree tree))))))))

(defun generate-sumrel (subsetflg vars rel &rest args
				    &aux desc newvars newargs sumvar gen equivs
				    newrel pat (nvars 0))
  (when subsetflg
    (return-from generate-sumrel
      (values-list
       ;; no need to cache - this will probably only happen once anyhow
       (remove nil
	      (loop for v in (xproduct (loop for x in vars collect
					     (if (eq x (car (last args)))
						 (list x)
					       (list nil x))))
		    collect
		    (apply #'generate-sumrel nil (remove nil v) rel args))))))
  (let ((parmlist (derived-param-list rel 'sum)))
    (setf newrel (relationp+ (second parmlist))
	  pat (third parmlist)
	  equivs (mapcar #'varcompare vars)
	  vars (vars-to-names vars)
	  args (vars-to-names args))
    (let ((aa args))
      (loop for p in pat do ; this throws away the last arg ...
	  (cond ((eq p 'input)
		 (push (pop aa) newargs)
		 (when (member (first newargs) vars)
		   (incf nvars)
		   (push (first newargs) newvars)))
		((eq p 'sum)
		 (push (setf sumvar (gensym "V")) newvars)
		 (push sumvar newargs))
		(t (let ((new (gensym "V")))
		     (push new newvars)
		     (push new newargs))))))
    (setf newvars (nreverse newvars) newargs (nreverse newargs))
    (setf desc (expanddescription `(,newvars s.t. (notinline (,newrel ,@newargs)))
				  :allowevalargs t))
    (unless (setf gen (findgenerator (first desc) (third desc) t))
	(return-from generate-sumrel nil))
    `((template (,.(loop for x in
			 (or (second (assoc 'template (sgen gen)))
			     (make-list (length pat) :initial-element 'input)) ; for testers
			 as y in pat when (eq y 'input) collect x)
		 output))
      (effort ,(+ (effort gen) ; generate the tuples and classify each
		  (* 30 (relationsize (first desc) (third desc)) (length vars))))
      (initialstate
	(lambda (rel ,.(loop for arg in (rest (third desc))
			     unless (member arg (first desc)) collect arg))
	  (declare (ignore rel))
	  (let ((tree (createtree)))
	    (loop for ,(vars-to-names (first desc)) s.t. ,(vars-to-names-wff (third desc))
		  do (increment-tree-sum tree ,sumvar
			  ,.(loop for v in vars as e in equivs
				  as i below nvars nconc (rel-or-fn v e))))
	    (treegen-common-from-data
	      ,(1+ nvars)
	      0
	      nil
	      (purify-tree tree))))))))

(defderivation sum
  :tester (lambda (rel &rest ignore) (declare (ignore ignore)) (test-sumrel rel))
  :generators (generate-sumrel))

(defun increment-tree-sum (tree incr &rest val-equiv-pairs)
  (setf tree (apply #'construct-tree tree val-equiv-pairs))
  (if (cdr tree) (incf (cadr tree) incr) (setf (cdr tree) (list incr))))

#|
(defrelation total%
	     :derivation (sum works-on% (input output input sum))
	     :cache-generators nil)
(loop for (person project day foo) in
      '((don fsd today 10)
	(don kbsa today 20)
	(don fsd yesterday 30)
	(bob fsd yesterday 15)
	(bob fsd today 25)
	(bob kbsa yesterday 35))
      do (++ works-on% person project day foo))
(listof x y s.t. (total% x 'today y))
((DON 30) (BOB 25))
(?? total% 'DON 'today 30)
T
(?? total% 'DON 'today 22)
NIL
(listof x y s.t. (total% x y 30))
((DON TODAY) (DON YESTERDAY))
(defautomation note-add-total%
	       ((x y z) s.t. (start (total% x y z)))
  (lambda (x y z) (format *standard-output* "(++ total% ~A ~A ~A)" x y z)))
(defautomation note-del-total%
	       ((x y z) s.t. (start (not (total% x y z))))
  (lambda (x y z) (format *standard-output* "(-- total% ~A ~A ~A)" x y z)))
(++ works-on% 'bob 'b-o 'yesterday 40)
 =>(-- total% BOB YESTERDAY 50) (++ total% BOB YESTERDAY 90)
(-- works-on% 'bob 'b-o 'yesterday 40)
 =>(-- total% BOB YESTERDAY 90) (++ total% BOB YESTERDAY 50)
(-- works-on% 'bob 'fsd 'today 25) => (-- total% BOB TODAY 25)
(++ works-on% 'bob 'fsd 'today 25) => (++ total% BOB TODAY 25)
|#
; ---------------- extreme ----------------
; the :representation translator
(defun extreme (name keys origrelname order-name i-o-pattern &key (trigger t)
			&aux (arity 0) origrel extreme-pos)
 (warn-ignored-keys name keys
  (:definition :arity :equivs :implementation :types
	       :computation :tester :trigger)
  ;; allow anon-rel for origrelname
  (when (consp origrelname)
      (setf origrelname
	    (relationnamep (relationp+ origrelname))))
  (dolist (x i-o-pattern)
    (cond ((eq x 'extreme)
	   (if extreme-pos
	       (error "The i-o-pattern for a extremerel may only contain EXTREME once")
	       (setf extreme-pos arity)))
	  ((or (eq x 'input) (eq x 'output)))
	  (t (error "The i-o-pattern for a extremerel may only contain EXTREME, INPUT and OUTPUT")))
    (incf arity))
  (unless extreme-pos
    (error "The i-o-pattern for a extremerel must contain EXTREME"))
  (unless (setf origrel (relationp origrelname))
    (error "unknown relation - ~A" origrelname))
  (unless (= (arity* origrel) arity)
    (error "The i-o-pattern should have one element for each argument of ~A" origrelname))
  (unless (?? relationarity (relationp order-name) 2)
    (error "The ordering relation ~A is not a binary relation" order-name))
  (let* ((rel (relationp origrelname))
	 (order (relationp+ order-name))
	 (equiv (get-comparison rel extreme-pos t))
	 (orderequiv (get-comparison order 0)))
    (unless (and (eql orderequiv (get-comparison order 1))
		 (or (eq t orderequiv) ; anycomparison
		     (?? subrel equiv orderequiv)))
      (error "The comparisons for the ordering relation ~A ~
              ~&are incompatible with that of position ~A of ~A"
	     order-name extreme-pos origrelname))) 
  `(:derivation extreme
    :arity ,arity :equivs ,(loop for i below arity with r collect
				 (if (setq r (relationp (get-comparison origrel i)))
				     (relationnamep r)
				     (error "Extremerel of relation with ambiguous comparisons")))
    :types ,(loop for i below arity collect
		  (forany tp s.t. (typeconstraint origrel i tp) (relationnamep tp)
			  ifnone 'entity))
    ,@(when trigger `(:trigger ((,origrelname +- trigger-extreme +-))))
    ,@keys)))

;; THIS SHOULD BE DONE VIA A GENSYM DEFUN IN ALSOFNS
;; SO THE COMPILATION GOES TO A FILE
(defun trigger-extreme (extremerel add del)
  (funcall
    (or (get-structure-property extremerel 'cached-trigger-fn)
	(put-structure-property extremerel (compile-extreme-trigger extremerel)
				'cached-trigger-fn))
    add del))

;; Thursday 2012/03/15
;; use of maintainedrel seems not to have been working before addition of
;; relationnamep; after that it (surprisingly) does seem to work as long as 
;; the maintained rel is declared before the trigger is needed
;; next the test is moved to run time so we don't have to decache this
;; when maintained rels are added and removed ...
;; or would it be better to toggle a setting when maintained rels are added
;; and removed?
;; we should really be comparing the costs of different maintained rels
;; and for that matter, the extremerel itself
;; also, if number of extreme elements affected is large, it might be cheaper
;; to iterate once over the entire basis rel -- again to be determined
;; at run time
(defun compile-extreme-trigger (extremerel)
  (let ((parmlist (derived-param-list extremerel 'extreme)))
    (let ((origrel (relationp+ (second parmlist)))
			;(order (relationp (third parmlist)))
	  (pattern (fourth parmlist)))
      (multiple-value-bind (allvars invars noninvars noninvarnames equivs)
	  (loop with v and thisvarform for p in pattern as i from 0
		collect (setf v (gensym "X")) into ALLVARS ;LOCAL TO LOOP
		collect (let ((cnc (c-and-c (get-comparison origrel i))))
			     (if (listp cnc) (list v (setf thisvarform (list (cadr cnc) v))
						   (car cnc))
				 (list v (setf thisvarform v) cnc))) into EQUIVS ;LOCAL TO LOOP
		when (eq p 'input) collect v into INVARS ;LOCAL TO LOOP
		  else collect v into NONINVARS  ;LOCAL TO LOOP
		    and collect thisvarform into NONINVARNAMES ;;LOCAL TO LOOP
		finally (return (values allvars invars noninvars noninvarnames equivs)))
	
	(flet ((relname-or-rel (r) (or (relationnamep r) r)))
	  (compile-ap
	    `(lambda (add del &aux (equiv-arg ',(loop for a in noninvars
					      collect (third (assoc a equivs))))
                      maintainedrel)
               (setf maintainedrel
                     (loop for (rel desc rule) s.t.
                       (and (MaintainedRel rel desc rule)
                            (relation-in-defn ',(relname-or-rel extremerel) rel))
                       thereis (and (eq ',(relname-or-rel extremerel)
                                        (car (third desc)))
                                    (equal (car desc) (cdr (third desc)))
                                    rel)))
	       ;; if we only add and there's a maintained rel then there's a better way ...
	       (do-s.t. (,invars (change ,noninvars (,(relname-or-rel origrel) ,@allvars)))
		 (let (newlist (newtree (createtree)) oldlist (oldtree (createtree))
		       tuple)

		   (do-s.t. (,noninvars
			       (previously (funcall (or maintainedrel
                                                        ',(relname-or-rel
                                                           extremerel))
					    ,@allvars)))
		     (setf tuple (list ,@noninvarnames))
		     (when del (push tuple oldlist))
		     (when add (treeadder tuple oldtree equiv-arg)))
		   (do-s.t. (,noninvars (,(relname-or-rel extremerel) ,@allvars))
		     (setf tuple (list ,@noninvarnames))
		     (when add (push tuple newlist))
		     (when del (treeadder tuple newtree equiv-arg)))
		   (when add
		     (dolist (tuple newlist)
		       (unless (treetester tuple oldtree equiv-arg)
			 (++ ,(relname-or-rel  extremerel)
			     ,@(loop for v in allvars  as p in pattern collect
				     (if (eq p 'input) v '(pop tuple)))))))
		   (when del
		     (dolist (tuple oldlist)
		       (unless (treetester tuple newtree equiv-arg)
			 (-- ,(relname-or-rel  extremerel)
			     ,@(loop for v in allvars  as p in pattern collect
				     (if (eq p 'input) v '(pop tuple))))))))))))))))

#|  following version replaced by NMG 8/3/89
(defun compile-extreme-trigger (extremerel)
  (forany parmlist s.t. (parameter-list extremerel parmlist) 
    (let ((origrel (relationp (cadr parmlist)))
	  ;(order (relationp (caddr parmlist)))
	  (pattern (fourth parmlist))
	  invars outvars extremevars allvars maintainedrel equivs)
      (setq allvars (loop for p in pattern collect (gensym "X"))
	    invars (loop for a in allvars as p in pattern when (eq p 'input)
			 collect a)
	    outvars (loop for a in allvars as p in pattern when (eq p 'output)
			  collect a)
	    extremevars (loop for a in allvars as p in pattern when (eq p 'extreme)
			  collect a)
	    equivs (loop for i from 0 as v in allvars collect
			 (let ((cnc (c-and-c (get-comparison origrel i))))
			   (if (listp cnc) (list v (list (cadr cnc) v) (car cnc))
			       (list v v cnc))))
	    maintainedrel
	    (loop for (rel desc rule) s.t. (and (MaintainedRel rel desc rule)
						(relation-in-defn extremerel rel))
		  thereis (and (eq extremerel (car (third desc)))
			       (equal (car desc) (cdr (third desc))))))
      (compile-ap
	`(lambda (&aux (equiv-arg '(,@(loop for v in outvars collect
					    (caddr (assoc v equivs)))
				    ,(caddr (assoc (car extremevars) equivs)))))
	   ;; if we only add and there's a maintained rel then there's a better way ...
	   (loop for ,invars s.t. (change (,@outvars ,@extremevars) (,origrel ,@allvars))
		 do
		 (let (newlist (newtree (createtree)) oldlist (oldtree (createtree)) tuple)
		   (loop for (,@outvars ,@extremevars) s.t.
			 (previously (,(or maintainedrel extremerel) ,@allvars))
			 do
			 (push (setq tuple (list ,@(loop for v in outvars collect
							 (cadr (assoc v equivs)))
						 ,(cadr (assoc (car extremevars) equivs))))
			       oldlist)
			 (treeadder tuple oldtree equiv-arg))
		   (loop for (,@outvars ,@extremevars) s.t.
			 (,extremerel ,@allvars) do
			 (push (setq tuple (list ,@(loop for v in outvars collect
							 (cadr (assoc v equivs)))
						 ,(cadr (assoc (car extremevars) equivs))))
			       newlist)
			 (treeadder tuple newtree equiv-arg))
		   (loop for tuple in newlist unless (treetester tuple oldtree equiv-arg)
			 do (++ ,(relationnamep extremerel)
				,@(loop for v in allvars collect
					(if (member v invars) v '(pop tuple)))))
		   (loop for tuple in oldlist unless (treetester tuple newtree equiv-arg)
			 do (-- ,(relationnamep extremerel)
				,@(loop for v in allvars collect
					(if (member v invars) v '(pop tuple))))))))))))
|#

(defun test-extremerel (rel &aux 
			    (args (loop for i below (arity* rel) collect (gensym "V")))
			    (genvars (loop for i below (arity* rel) collect (gensym "V")))
			    (pat (fourth
				  (derived-param-list rel 'extreme))))
  `(lambda (ignore ,@args) (declare (ignore ignore))
	   (loop for ,(loop for v in genvars as p in pat unless (eq p 'input) collect v)
		 s.t. (,rel ,@(loop for v in genvars as p in pat as a in args collect
				    (if (eq p 'input) a v)))
		 thereis (and ,@(loop for v in genvars as p in pat as a in args
				      as pos below (arity* rel) unless (eq p 'input)
				      collect (get-test-function
						(get-comparison rel pos t)
						v a))))))

#|
We will always generate the extreme and outputs
Example: rel = (highest-effort-project person project date percent)
         newrel = (works-on% person project date percent) ; the ground relation
         pat = (input output input extreme)
	 order= #,(theap5relation >)
         vars = (var-person var-extreme)
	 args = (var-person project1 date1 var-extreme)
Goal program:
 <create a tree: person => list of tuples
 (loop for (person project percent) s.t.
       (works-on% person project date1 percent) do
       <add <project percent> to list of tuples for person>)
 where adding a tuple means also removing any that are "subsumed"
 generate the tree
|#

#+ignore 
(defun generate-extremerel (subsetflg vars rel &rest args
				    &aux desc newvars newargs extremevar
				    newrel order pat gen equivs treevars listvars)
  (let ((parmlist (derived-param-list rel 'extreme)))
    (when subsetflg
      (return-from generate-extremerel
	(remove nil ; no need to cache - this will probably only happen once anyhow
		(loop for v in (xproduct (loop for x in vars as p in pat collect
					       (if (eq p 'input) (list nil x) (list x))))
		      nconc
		      (apply #'generate-extremerel nil (remove nil v) rel args)))))
    (setf newrel (relationp+ (second parmlist))
	  order (relationp+ (third parmlist))
	  pat (fourth parmlist)
	  equivs (mapcar #'varcompare vars)
	  vars (vars-to-names vars)
	  args (vars-to-names args))
    (loop for p in pat as aa in args do ; this throws away the last arg ...
	  (cond ((eq p 'input)
		 (push aa newargs)
		 (when (member (first newargs) vars)
		   (push (first newargs) newvars)))
		((eq p 'extreme)
		 (push (setf extremevar (gensym "V")) newvars)
		 (push extremevar newargs))
		(t (let ((new (gensym "V")))
		     (push new newvars)
		     (push new newargs)))))
    (setf newvars (nreverse newvars) newargs (nreverse newargs))
    (setf desc (expanddescription `(,newvars s.t. (notinline (,newrel ,@newargs)))
				  :allowevalargs t))
    (unless (setf gen (findgenerator (first desc) (third desc) t))
	(return-from generate-extremerel nil))
    `((template (,.(loop for a in newargs collect (if (member a newvars) 'output 'input))))
      (effort ,(+ (effort gen) ; generate the tuples and classify each
		  (* 30 (relationsize (first desc) (third desc)) (length vars))))
      (initialstate
	(lambda (rel ,.(loop for arg in newargs unless (member arg newvars) collect arg))
	  (declare (ignore rel))
	  (let ((tree (createtree)))
	    (loop for ,newvars s.t. (,newrel ,@newargs)
		  do (increment-tree-extreme tree (theap5relation ,(relationnamep order))
			  (list ,@(setf listvars
					(loop for p in pat as a in newargs
					      unless (eq p 'input)
					      collect a))) ; need not be canonicalized
			  ,(loop for p in pat until (eq p 'extreme) count (eq p 'output))
			  ,.(loop for v in newargs as e in equivs as p in pat
				  when (eq p 'input) when (member v newvars)
				  nconc (progn (push v treevars) (rel-or-fn v e)))))
	    (let ((pulser (treegen-common-from-data
			    ,(1+ (length treevars))
			    0
			    nil
			    (purify-tree tree))))
	      #'(lambda ()
		  (let (,@(setf treevars (reverse treevars))
			,@listvars exhausted listvarslist)
		    (multiple-value-setq (exhausted ,@treevars listvarslist)
		      (funcall pulser))
		    (unless exhausted
		      ,(if (rest listvars)
			   `(multiple-value-setq ,listvars (values-list listvarslist))
			 `(setf ,(first listvars) (first listvarslist))))
		    (if exhausted
			t
			(values nil ,@(loop for p in pat as a in newargs
					      when (or (not (eq p 'input)) (member a newvars))
					  collect a))))))))))))

(defun generate-extremerel (subsetflg vars rel &rest args
				    &aux desc newvars newargs extremevar
				    newrel order pat gen equivs treevars listvars)
  (let ((parmlist (derived-param-list rel 'extreme)))
    (setf pat (fourth parmlist)) ;; *** moved up from below - used here
    (when subsetflg
      (return-from generate-extremerel
        (values-list
         ;; no need to cache - this will probably only happen once anyhow
	 (remove nil 
		 (loop for v in (xproduct (loop for x in vars as p in pat collect
					       (if (eq p 'input) (list nil x) (list x))))
		      collect
		      (apply #'generate-extremerel nil (remove nil v)
			     rel args))))))
    (setf newrel (relationp+ (second parmlist))
	  order (relationp+ (third parmlist))
	  equivs (mapcar #'varcompare vars)
	  vars (vars-to-names vars)
	  args (vars-to-names args))
    (loop for p in pat as aa in args do ; this throws away the last arg ...
	  (cond ((eq p 'input)
		 (push aa newargs)
		 (when (member (first newargs) vars)
		   (push (first newargs) newvars)))
		((eq p 'extreme)
		 (push (setf extremevar (gensym "V")) newvars)
		 (push extremevar newargs))
		(t (let ((new (gensym "V")))
		     (push new newvars)
		     (push new newargs)))))
    (setf newvars (nreverse newvars) newargs (nreverse newargs))
    (setf desc (expanddescription `(,newvars s.t. (notinline (,newrel ,@newargs)))
				  :allowevalargs t))
    (unless (setf gen (findgenerator (first desc) (third desc) t))
	(return-from generate-extremerel nil))
    `((template (,.(loop for a in newargs collect (if (member a newvars) 'output 'input))))
      (effort ,(+ (effort gen) ; generate the tuples and classify each
		  (* 30 (relationsize (first desc) (third desc)) (length vars))))
      (initialstate
	(lambda (rel ,.(loop for arg in newargs unless (member arg newvars) collect arg))
	  (declare (ignore rel))
	  (let ((tree (createtree)))
	    (loop for ,newvars s.t. (,newrel ,@newargs)
		  do (increment-tree-extreme tree (theap5relation ,(relationnamep order))
			  (list ,@(setf listvars
					(loop for p in pat as a in newargs
					      unless (eq p 'input)
					      collect a))) ; need not be canonicalized
			  ,(loop for p in pat until (eq p 'extreme) count (eq p 'output))
			  ,.(loop for v in newargs as e in equivs as p in pat
				  when (eq p 'input) when (member v newvars)
				  nconc (progn (push v treevars) (rel-or-fn v e)))))
	    (let ((pulser (treegen-common-from-data
			    ,(1+ (length treevars))
			    0
			    nil
			    (purify-tree tree))))
	      #'(lambda ()
		  (let (,@(setf treevars (reverse treevars))
			,@listvars exhausted listvarslist)
		    (multiple-value-setq (exhausted ,@treevars listvarslist)
		      (funcall pulser))
		    (unless exhausted
		      ,(if (rest listvars)
			   `(multiple-value-setq ,listvars (values-list listvarslist))
			 `(setf ,(first listvars) (first listvarslist))))
		    (if exhausted
			t
			(values nil ,@(loop for p in pat as a in newargs
					      when (or (not (eq p 'input)) (member a newvars))
					  collect a))))))))))))

(defderivation extreme
  :tester (lambda (rel &rest ignore) (declare (ignore ignore)) (test-extremerel rel))
  :generators (generate-extremerel))

(defun increment-tree-extreme (tree order tuple extremepos
			       &rest val-equiv-pairs)
  (setf tree (apply #'construct-tree tree val-equiv-pairs))
  (if (cdr tree)
      (when					; tuple not subsumed by current
	(loop for tup in (rest tree) always
	      (or (testrel order (nth extremepos tuple) (nth extremepos tup))
		  (not (testrel order (nth extremepos tup) (nth extremepos tuple)))))
	(setf (rest tree)
	      (cons tuple
		    (delete-if
		      #'(lambda (tup)
			  (and (testrel order (nth extremepos tuple) (nth extremepos tup)) 
			       (not (testrel order (nth extremepos tup) (nth extremepos tuple)))))
		      (rest tree)))))
      (setf (rest tree) (list tuple))))

#|
(defrelation main-project
	     :derivation (extreme works-on% >= (input output input extreme))
	     :cache-generators nil)
(loop for (person project day foo) in
      '((don fsd today 10)
	(don kbsa today 20)
	(don fsd yesterday 30)
	(bob fsd yesterday 15)
	(bob fsd today 25)
	(bob kbsa yesterday 35))
      do (++ works-on% person project day foo))
(listof x y z s.t. (main-project x y 'today z))
((DON KBSA 20) (BOB FSD 25))
(listof x y z w s.t. (main-project x y z w))
((DON KBSA TODAY 20)
 (DON FSD YESTERDAY 30)
 (BOB KBSA YESTERDAY 35)
 (BOB FSD TODAY 25))
(?? main-project 'DON 'today 'KBSA 20)
NIL
(?? main-project 'DON 'KBSA 'today 20)
T
(defautomation note-add-main-project
	       ((x y z w) s.t. (start (main-project x y z w)))
  (lambda (x y z w) (format *standard-output* "(++ main-project ~A ~A ~A ~A)" x y z w)))
(defautomation note-del-main-project
	       ((x y z w) s.t. (start (not (main-project x y z w))))
  (lambda (x y z w) (format *standard-output* "(-- main-project ~A ~A ~A ~A)" x y z w)))
(++ works-on% 'bob 'b-o 'yesterday 40)
  => (++ main-project BOB B-O YESTERDAY 40)(-- main-project BOB KBSA YESTERDAY 35)
(-- works-on% 'bob 'b-o 'yesterday 40)
 => (++ main-project BOB KBSA YESTERDAY 35)
    (-- main-project BOB B-O YESTERDAY 40)
(++ works-on% 'bob 'b-o 'yesterday 35)
=> (++ main-project BOB B-O YESTERDAY 35)
(-- works-on% 'bob 'b-o 'yesterday 35)
=> (-- main-project BOB B-O YESTERDAY 35)
|#

; *** need a size function - in this case same as Existentials

; *** can we arrange to get counts/subs/extremes/tclosures/... of descriptions?

; *** count and size should be all right - should be same as orig with pattern outputs
; replaced by count inputs
; *** types should be maintained same as orig slots (+ integer)
