;-*- mode:LISP; Package:(AP5); Base:10.; Syntax:Common-Lisp -*-
;
; Misc. Utilities
(in-package "AP5")

;; needed in old zetalisp version
;(defun symbol-name (x)(get-pname x))
;(defun find-package (x) (pkg-find-package x))
;(defun integerp(x) (fixp x))
(defun symbolname (name sym) (when (symbolp sym) (string-equal sym name)))
 
;;(* Misc utilities)
(defun Help(&optional x y) ; an approximation
  (error "Help! ~S ~S" x y))
; hope to eventually get rid of all calls to help

(declaim (inline ilistp zlistp nlistp))
(defun Ilistp (x) (when (listp x) x))
(defun Zlistp (x) (consp x) ;(when x (listp x))
       )
; these are cleverly written to be valid for either common or zeta listp
; from now on, listp will refer to common lisp listp
(defun nlistp (x) (not (listp x)))
(defun kwote(x)
  (cond ((or (null x) (eq x t) (stringp x) (numberp x)) x)
	(t (list 'quote x))))
; It's handy to provide comments for users, and sometimes the program 
; may actually use them - no more - too many conflicts with other defns

; since ignore is a symbol in the lisp package, I've got to rename this ...
(defun ignored (&rest ignore) (declare (ignore ignore)) nil)
; turns out you sometimes need a fn
;are these still used?
(defun mklist(x)(cond ((listp x) x)(t (list x))))
#+ignore
(defmacro-displace pack* (&rest args)
  `(intern (with-output-to-string (pack*stream)
	     ,@ (loop for a in args collect (list 'princ a 'pack*stream)))))

(defvar *system-packages*
  (loop for p in '("LISP" "CLOS" "PCL" #+TI "TICL"
		   #+allegro "EXCL" #+symbolics "SCL" #+lucid "LCL"
		   #+aclpc "ACL")
        when (find-package p) collect (find-package p)))

(defun pack* (&rest args &aux pck (*print-radix* nil)
		    (*print-case* :upcase)
		    ;#+symbolics (global:*nopoint t)
		    #+ti (global:*nopoint t)
		    name)
  (setq name (with-output-to-string (pack*stream)
	       (loop for a in args
		     unless pck
		      when (and (symbolp a)
				(not (member (symbol-package a)
					     *system-packages*)))
		      do (setq pck (symbol-package a))
		     when (and (floatp a) (= a (floor a))) ; is floor cheapest?
		      do (setq a (floor a))
		     do (princ a pack*stream))))
  #+symbolics (zl:condition-bind ((si:package-locked
				 #'(lambda (c)
				     (when (zl:send c :proceed-type-p :no-action)
				       (zl:send c :proceed :no-action)))))
		  (intern name (or pck (find-package "AP5"))))
  #-symbolics (intern name (or pck (find-package "AP5"))))

(declaim (inline fsubset fldifference))
(defun fsubset (x y)
  (subsetp x y)
  ;(loop for z in x always (member z y))
  )

(defun fldifference (x y)
  ;(set-difference x y) ; yes, the order does matter!!!
  (loop for z in x unless (member z y) collect z)
  )

(Defun FEqSet (A B)
  (AND (= (LENGTH A) (LENGTH B))
       (FSubset A B)
       (FSubset B A)))

;; newer versions that use equivalence rels
; formerly (loop for x in a as y in b always (eql x y)))
;
(defmacro-displace equal2 (a b rel-or-list)
  (if (listp rel-or-list)
    `(let ((tup1 ,a)(tup2 ,b))
	 (and ,.(loop for l in rel-or-list collect
		      (cond ((listp l)	; worry about get-match-compare
			     `(let ((x (pop tup1)) (y (pop tup2)))
				(and ,. (loop for r in l collect
					      (get-test-function r 'x 'y)))))
			    (t (get-test-function l '(pop tup1) '(pop tup2)))))))
    (let* ((rel* (relationp rel-or-list))
	   (arity (arity* rel*)))
       ; for comparing tuples (known to be same length)
      `(let ((tup1 ,a)(tup2 ,b))
	 (and ,.(loop for pos below arity collect
		      (get-test-function (get-comparison rel* pos t)
					 '(pop tup1) '(pop tup2))))))))



(defmacro-displace fmemb3 (target l rel) 
    ; for testing baserels - arity checked before
  (unless (symbolp target) (warn "FMEMB3 called with non-symbol target"))
  `(member-if #'(lambda (tpl) (equal2 ,target tpl ,rel)) ,l)
  ;`(loop for y on ,l thereis (and (equal2 ,target (first y) ,rel) y))
  )
; returns tail to make it easy to delete
;formerly (AND (EQLENGTH Y <Length X>) (for Z in Y as W in X always (EQ W Z)))


;; arithmetic on extended numbers
;; only extension is NIL to represent "inifinity"
(Defun IFEXPT (x y)
  (AND (NUMBERP x) (NUMBERP y) (EXPT x y)))

(Defun IFIX (x)
  (when (NUMBERP x) (round x)))

(defun if= (x y)
  (if x
      (and y (= x y))
      (null y)))

(defun iflessp (x y)
    (and x
	 (or (null y)
	     (< x y))))

(defun ifleq (x y)
  (if x
      (or (null y)
	  (<= x y))
      (null y)))

(defun ifplus (x y)
    (and x y (+ x y)))

(defun ifquotient (x y)
    (and x y (float (/ x y))))
; make sure it's floating point

(defun iftimes (x y)
  (and x y (* x y)))

(defun xproduct (l &aux cdrxp)
    ; (* L is a list of lists - compute the set of choices of an element from each)
    (cond ((null l)
           (list nil))
          (t
           (setq cdrxp (xproduct (cdr l)))
           (loop for x in (car l)
                 nconc (loop for y in cdrxp
                             collect (cons x y))))))

;;; DOXPRODUCT allows an interation over all cross products of
;;; a list of lists, LL.  On each iteration, a variable, IV, is bound
;;; to a different cross-product.  (A list of length |LL|).
;;; DOXPRODUCT reuses list structure in generating the cross products,
;;; so if the iteration body wishes to hold onto any of them (or tails
;;; of any of them) it should do a copy-list first.
(defmacro doxproduct
       ((iv ll &optional result)
	&rest body &aux (llvar (gensym "G")) (lltailvar (gensym "G")))
   ; L is a list of lists - evaluate the body with iv
   ; successively bound to each element of the cross product
  `(let* ((,llvar ,ll) (,lltailvar (mapcar #'ignored ,llvar)))
     (mapxproduct ,llvar ,lltailvar ,lltailvar   #'(lambda (,iv) ,. body))
     ,result))

(defun mapxproduct (remaining xp xptail fn)
  (declare #+symbolics(sys:downward-funarg fn))
  (cond ((null remaining) (funcall fn xp))
	(t (loop for x in (car remaining)
              do (rplaca xptail x)
	         (mapxproduct (cdr remaining) xp (cdr xptail) fn)))))


(defmacro-displace multiple-value-lambda-bind (lambda-list mvform &rest body)
  `(multiple-value-call #'(lambda ,lambda-list ,.body) ,mvform))

;;(* Relation objects)
(defstruct (DBObject ; :named  (:type vector)
	     (:conc-name nil)
	     (:print-function dbobject-print))
  classes Properties)


; copied from triggers just to avoid defining properties in two files
(defstruct (matchnode (:include DBObject) (:conc-name nil) ; :named  (:type vector)
		      (:print-function dbobject-print))
  matchvars matchwff matchcode matchcompare
  matchsuccessors matchpredecessors matchrels matchactive)

(defstruct (history-record (:include DBObject) (:conc-name nil) ; :named
			   (:print-function print-history-record))
  originalupdates generation# consistency-cycles prev-gen#)

; Now I'll redo dbo just so the last defn of the accessors require only
; that the argument be a dbo, and not a more specialized thing
#+ignore ;; Thursday 2006/02/16  #+clisp seems not to require this any longer?  Good!
(defstruct (DBObject ; :named  (:type vector)
	     (:conc-name nil)
	     (:print-function dbobject-print))
  classes Properties)

(defun dbobject-print (dbobject stream depth)
  (declare (ignore depth) (special printdbobject))
  ; ~A gets rid of quotes around the strings
  ; The printers should use ~S to preserve packages and case distinctions
  (Cond ((boundp 'printdbobject)
	 (funcall printdbobject dbobject stream))
        ((fboundp 'bootstrap-printer) 
	 (format stream "~A" (bootstrap-printer dbobject)))
	(t (princ '<dbobject> stream))))

(defun print-history-record (rec stream depth)
  (declare (ignore depth))
  (cond ((generation# rec)
	 (format stream "<history event #~S>" (generation# rec)))
	(t (format stream "<history label ~S>"
		   (get-structure-property rec 'history-label)))))

;; get-structure-property returns its third argument
;; if property was missing -- so you don't have an ambiguous meaning
;; for a NIL result.  -- just like GETF

; Adaptive version - move frequently accessed properties closer to the front
#+symbolics
(defun get-structure-property (ob prop &optional default &aux plist prevtail)
  (without-interrupts ; altering pointers!
    (setq plist (properties ob))
    (unless plist (return-from get-structure-property (values nil nil)))
    (when (eq prop (car plist))
      (return-from get-structure-property (values (cadr plist) t)))
    (setf prevtail plist plist (cddr plist))
    (loop (when (null plist) (return-from get-structure-property default))
	  (when (eq prop (car plist))
	    (psetf (car prevtail) (car plist) (cadr prevtail) (cadr plist)
		   (car plist) (car prevtail) (cadr plist) (cadr prevtail))
	    (return-from get-structure-property (cadr prevtail)))
	  (psetf prevtail plist plist (cddr plist)))))


#-symbolics ;;straighforward, fast version
(progn
(declaim (inline get-structure-property))
(defun get-structure-property (struc ind &optional default)
  (getf (Properties struc) ind default))
)

#|
 (defmacro-displace get-structure-property-1 (struc indicator)
  (let ((value (gensym "G")))
    `(let ((default (memo (cons nil nil))))
       (let ((,value (getf (Properties ,struc) ,indicator default)))
	  (cond ((eql ,value default) (values nil nil))
		(t (values ,value t)))))))
 ;; The original problem here is that the commonlisp definers blew it by
 ;  not giving back a second value to tell whether the property was there.
 ;  Then symbolics prevented us from just using a cons cell by writing a
 ;  compiler that identified them all (that's why we went to gensyms).
 ;  Finally the hplisp compiler prevented us from using gensyms in compiled
 ;  code (written on binary files) because gensyms are allocated in heap
 ;  space and thus relocated, but the pointer to them from compiled code
 ;  is never fixed.  Thus we fall back on a memo.

 (defun get-structure-property (struc indicator)
  (get-structure-property-1 struc indicator))
 (defmacro-displace put-structure-property-1 (struc value indicator)
  `(setf (getf (Properties ,struc) ,indicator) ,value))
|#


(defmacro put-structure-property (struc value indicator)
   `(let ((struc ,struc) (value ,value) (indicator ,indicator))
      (progn ;without-interrupts
	(setf (getf (Properties struc) indicator) value))))
; if this operation is interrupted the data could be read in an inconsistent state
; however we want it to act more like the function below in that the entire
; evaluation of the args need not be without-interrupts
; Another problem with that is when the value computation itself contains
; a put-struct-prop of the same struc ...

#+ignore ; hplisp bug ..
(defun put-structure-property (struc value indicator)
  (let ((props (properties struc)))
    (cond 
      ((loop while props do (cond ((eq (car props) indicator) (return t))
			          (t (setq props (cddr props)))))
       (rplaca (cdr props) value))
      (t (setf (properties struc) (cons indicator (cons value (properties struc))))))
    value))

(defsetf get-structure-property (struc ind) (val)
  `(put-structure-property ,struc ,val ,ind))

#+ignore 
(defmacro rem-structure-property-1 (struc indicator)
  `(progn ;without-interrupts
     (remf (Properties ,struc) ,indicator)))

(defun rem-structure-property (struc indicator)
  (progn ;without-interrupts
    (remf (Properties struc) indicator)))

#+ignore 
(defmacro-displace add-structure-property-1 (struc value indicator) ; &optional at-front
; simplified (donc)
  `(let ((struc ,struc) (indicator ,indicator))
     (put-structure-property struc
			     (cons ,value (get-structure-property struc indicator))
			     indicator)))

(defun add-structure-property (struc value indicator)
  (progn ;without-interrupts
    (push value (getf (Properties struc) indicator))))


(defun printDBO (&rest x)
  (format nil
	  (cond (*print-escape* "#,~S")
		(t "#,~A"))
	  (cons 'DBO x)))

(setq InPrintDBObject nil)

(setq Bootstrapping t)

; Types may have among their properties a Printer and Reader property.
; To print an object search for a type with a printer that is willing to print it.
; The convention is that it prints something like (type identifier) where the
; Reader property of the type can convert the identifer back into the object.

; (set-syntax-#-macro-char #\a 'apreader)
; move the defn to bootstrap, since it contains code that is relation dependent
;; instead of using a # readmacro, we'll just define a function (DBO type &rest args)
; which finds an object.  One can use #. and #, to get it evaluated at odd times.

(Defun RelationTypeP (x)
  (and (DBObject-p x)						;(typep x 'DBObject)
       (get-structure-property x 'RelationArity)))

;;;(declaim (inline getbasedata putbasedata))
;;; INLINEING GETBASEDATA wreaks havoc with constant-folding
(defun GetBaseData (Rel) (Get-Structure-Property Rel 'BaseData))
(defun PutBaseData (Rel Val) (Put-Structure-Property Rel Val 'BaseData))

(Defun GetRelationOfName(Name)
  (cond ((symbolp name)
	 ;(setq name (intern (make-symbol (symbol-name name)) 'keyword))
	 ;(GetHash (intern Name 'keyword) RelationOfName)
	 (values (GetHash Name RelationOfName)) ;; only want 1 value
	 )
	(t nil))) ; strange relation name

(Defun PutRelationOfName(Name Relation)
  #+ignore (cond ((symbolp name)
	 (setq name (intern (make-symbol (symbol-name name)) 'keyword))))
  (setf (gethash Name RelationOfName) Relation)
  (put-structure-property relation
			  (cons name (get-structure-property relation 'relationname))
			  'RelationName))

(defun compoundwffp (x)
  (member (car (ilistp x))
	'(a e and or not incx previously start))) ;implies equiv 

(defun prevdef (symbol)
  (cond ((eq (symbol-package symbol) (find-package "KEYWORD"))
	 (setq symbol (intern (symbol-name symbol)
			      (find-package "AP-COMPILED")))))
  (get symbol :previous-definition))

(defvar undef-list nil)

(defun undef (symbol)
  (unless symbol (error "trying to undef NIL!!"))
  (cond ((eq (symbol-package symbol) (find-package "KEYWORD"))
	 (setq symbol (intern (symbol-name symbol)
			      (find-package "AP-COMPILED")))))
  (or (and (get symbol :previous-definition) (fboundp symbol))
      (error "~S does not have both a current and previous definition" symbol))
  (push symbol undef-list)
  (let ((def (symbol-function symbol))) 
    (setf (symbol-function symbol) (get symbol :previous-definition))
    (setf (get symbol :previous-definition) def)))


