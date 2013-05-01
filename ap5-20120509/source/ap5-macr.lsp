; -*- Mode: LISP; syntax: common-lisp; Package: AP5;  Base: 10. -*-
(in-package "AP5")

(defconstant *EQ* (theap5relation eq))
(defconstant *EQL* (theap5relation eql))
(defconstant *EQUAL* (theap5relation equal))
(defconstant *EQUALP* (theap5relation equalp))


(defmacro Create-Instance (type-or-name &rest assignments &aux (g (gensym)))
  ; create an object of given type with the attributes and values provided
  ; each assignment is a list of form (attribute-name value1 value2 ...)
  `(let ((,g (make-dbobject)))
     (atomic (++ funcall (relationp ,type-or-name) ,g)
	     ,@(loop for (a . vals) in assignments nconc 
		       (loop for val in vals
			   when (null (?? relationarity (relationp a) 2))
			   do (error "~s -- not an attribute" a)
			   collect `(++ ,a ,g ,val))))
     ,g))

(defstruct (anomalous (:print-function
		       (lambda (ignore stream level) (declare (ignore ignore level)) (princ "Anomalous" stream))))
  #+TI ignored-field)
(defvar *anomalous* (make-anomalous))

(declaim (inline ANOM ANOM? NOTANOM?))
(defun ANOM () *anomalous*)
(defun ANOM? (X)  (EQ X *anomalous*))
(defun NOTANOM? (X)  (Not (EQ X *anomalous*)))

(declaim (inline IS ISNT))
(defun IS  (X)  (when (NOT (ANOM? X)) X))
(defun ISNT (X) ;; transformation on (NOT (IS X))
  (or (ANOM? X) (not X)))

(defmacro one-is (&rest forms)
       (let ((var (gensym)))
	 `(let (,var)
	    (cond ,@ (mapcar #'(lambda (form) `((not(anom? (setf ,var ,form))) ,var)) forms)
		  (t (anom))))))
(defmacro when-is (test &rest body) `(when (is ,test) ,.body))
(defmacro unless-is (test &rest body) `(unless (is ,test) ,.body))

;**************** macros for accessing binary relations ****************
(++ wffmacro 'fetch)

(defmacro FETCH (&rest original-form &aux (altered-form (copy-list original-form))
		       arity) 
  
  (cond ((and (boundp '*potential-wff-macro-form*)
	      (eq (rest *potential-wff-macro-form*) original-form))
	 (setf (first altered-form)
	       (check-relation-name-ok (first altered-form) 'fetch))
         (setf arity (if (relationp (first altered-form))
			 (arity* (relationp (first altered-form)))
					;a description
		       (length (caar altered-form))))
         (if (and (symbolp (cadr altered-form))
		  (member (cadr altered-form) '(of is =) :test 'string-equal)
		  (rest (member-if
			 #'(lambda (x)
			     (and (symbolp x)
				  (member x '(is =) :test 'string-equal)))
			 (rest altered-form)))
		  (= arity (- (length altered-form) 2 (if (string-equal (cadr altered-form) 'of)
							  1 0))))
	     `(,(first altered-form)
	       ,.(remove-if #'(lambda (x)
				(and (symbolp x)
				     (member x '(of is =) :test 'string-equal)))
			    (rest altered-form) :count 2))
	   (error "syntax error --~%~s~%" (cons 'fetch original-form))))
	(t
	 (when (null (rest altered-form)) (nconc altered-form (list 'of)))
         
	 (if (and (> (length altered-form) 4)
		  (symbolp (cadr altered-form))
		  (string-equal (cadr altered-form) 'whose))
	     (process-whose-fetch altered-form original-form)
	   (progn
	     (setf (first altered-form)
		   (check-relation-name-ok (first altered-form) 'fetch))
	     (setf arity
		   (if (relationp (first altered-form))
		       (arity* (relationp (first altered-form)))
					; a description
		     (length (caar altered-form))))
	     (if (and (symbolp (cadr altered-form))
		      (member (cadr altered-form) '(of is =) :test 'string-equal)
		      (rest (member-if #'(lambda (x)
					   (and (symbolp x)
						(member x '(is =) :test 'string-equal)))
				       (rest altered-form)))
		      (= arity (- (length altered-form) 2 (if (string-equal (cadr altered-form) 'of)
							      1 0)))
		      (notany #'(lambda (x) (and (symbolp x)
						 (string= x "?")))
			      (rest altered-form)))
		 `(?? ,(first altered-form)
		      ,.(remove-if #'(lambda (x)
				       (and (symbolp x)
					    (member x '(of is =) :test 'string-equal)))
				   (rest altered-form) :count 2))
	       (if (and (symbolp (cadr altered-form))
			(string-equal (cadr altered-form) 'of)
			(> arity (count-if-not
				  #'(lambda (x)
				      (and (symbolp x)
					   (member x '("is" "=" "?")
					   :test 'string-equal)))
				  (cddr altered-form))))
		   ;; not all columns supplied -- form an "any"
		   (let (given needed (index 0))
		     (dolist (x (cddr altered-form))
		       (unless (and (symbolp x)
				    (member x '(is =) :test 'string-equal))
			 (if (and (symbolp x)
				  (string= "?" x))
			     (push (list index (gensym)) needed)
			   (push (list index (gensym) x) given))
			 (incf index)))
		     (dotimes (i (- arity index))
		       (push (list (+ i index) (gensym)) needed))
		     (setf needed (nreverse needed))
		     (flet ((inline-ordered-args (given needed arity)
			       (do ((i (1- arity) (1- i))
				    l tmp)
				   ((minusp i) l)
				 (push (if (setf tmp (assoc i given :test #'=))
					   (third tmp)
					 (cadr (assoc i needed :test #'=)))
				       l))))
		     `(any ,(mapcar #'cadr needed)
			   s.t. (,(first altered-form)
				 ,.(inline-ordered-args
				    given needed arity))
			   ifnone (values ,.
				  (mapcar #'(lambda (x) (declare (ignore x))
						      (list 'anom))
						  needed)))))
		 (error "syntax error --~%~s~%" (cons 'fetch original-form)))))))))


(defun process-whose-fetch (altered-form original-form)
  (let* ((g (first altered-form)) (g-as-var (first altered-form) ))
    (multiple-value-bind (vname ignore1 ignore2) (parse-var g)
      (declare (ignore ignore1 ignore2))
      (if (not (eq g vname)) (setf g-as-var vname)
	(if (?? typename g)
	    (setf g-as-var g
		  g (intern (concatenate 'string (string g) "#")
			    (symbol-package g))))))
    `(any ,g s.t.
	(and ,. (loop with lastrel and arity and tail = (cddr altered-form) while tail
		   do (progn
			(setf (first tail)
			      (check-relation-name-ok (first tail) "fetch ... whose ... "))
			(setf arity
			    (if (relationp (first tail))
				(arity* (relationp (first tail)))
				(length (caar tail)))))
		   unless (and (symbolp (cadr tail))
			       (member (cadr tail) '(is =) :test 'string-equal))
		   do (error "syntax error --~%~s~%" (cons 'fetch original-form))
		   collect  
		   `(,(setf lastrel (pop tail)) ,g-as-var
		     ,.(loop initially (pop tail) for i below (1- arity)
			  when (or (null tail)
				   (and (symbolp (first tail))
					(member (first tail) '(is =) :test 'string-equal)))
			  do (error "insufficient arguments for ~a in ~a"
				    lastrel (cons 'fetch original-form))
			  collect (pop tail)))))
	ifnone (anom))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; used in macro expansions within this file
(defun check-relation-name-ok
	 (name op &aux (rel (relationp name)))
  (unless rel
    (when (descriptionp name t) (return-from check-relation-name-ok name))
    (unless (eq name (setf rel (check-relation-package-error name)))
      (return-from check-relation-name-ok rel))
    #-ti
    (check-type name (satisfies relationp)
		(format nil "a legitimate relation name for ~a" op))
    #+ti
    (DO ()
    ((TYPEP NAME '(SATISFIES relationp)))
      (SETF NAME
	(CERROR '(:ARGUMENT-VALUE) NIL 'SYS:WRONG-TYPE-ARGUMENT
		"The argument ~2@*~A was ~1@*~S, which is not ~3@*~A."
		'(SATISFIES relationp) NAME 'NAME
		(FORMAT NIL "a legitimate relation name for ~a" OP))))
    )
  name))

(defmacro UPDATE (&rest FORM &aux from from-specified
				    domain new tmp error arity)
  (setf (first form) (check-relation-name-ok (first form) 'update)
	arity (if (relationp (first form))
		  (arity* (relationp (first form)))
						; a description
		  (length (caar form))))
  (multiple-value-setq (from from-specified)
    (DB-ACCESSOR-MACRO-GET (cdr FORM) '(FROM WAS) '(TO = OF)))
  (multiple-value-setq (domain tmp)
    (DB-ACCESSOR-MACRO-GET (cdr FORM) 'OF  '(FROM WAS TO =)))
  (unless tmp (setf error 'OF)) ;; OF slot is required
  (multiple-value-setq (new tmp)
    (DB-ACCESSOR-MACRO-GET (cdr FORM) '(TO =) '(FROM WAS OF)))
  (unless tmp (setf error 'TO)) ;; TO slot is required
  (when error (error "missing ~a field~%~s~%" error (cons 'update form)))
  (when from (unless (= (length from) (length new))
	       (error "must supply same number of old and new slots in update ~%~s"
		      form)))
  (flet ((tilde-p  (x) (and (symbolp x)
			    (or (string= x "~")
				(string= x "?")))))
    (let* ((d (loop for exp in domain as i from 0 unless (tilde-p exp)
		    collect (list i (gensym) exp)))
	   (tld (nconc
		 (loop for exp in domain as i from 0 when (tilde-p exp)
		       collect (list i (gensym)))
		 (loop for i from (length domain) below arity
		       collect (list i (gensym)))))
	   (r (mapcar #'(lambda (exp x) (list (first x) (gensym) exp)) new tld))
	   (f (mapcar #'(lambda (exp x) (list (first x) (gensym) exp)) from tld)))
      (unless (= (length tld) (length new))
	(error "Incorrect number of new values supplied in UPDATE"))
      (unless (or (null from) (= (length from) (length new)))
	(error "Incorrect number of old values supplied in UPDATE"))

      (flet ((ordered-args (given needed arity)
              (do ((i (1- arity) (1- i))
		   l)
		  ((minusp i) l)
		(push (cadr (or (assoc i given :test #'=)
				(assoc i needed :test #'=)))
		      l))))
	`(let (,.(mapcar #'cdr d) ,.(mapcar #'cdr r) ,.(mapcar #'cdr f))
	 (atomic
	  ,(if from-specified
	       (let ((ordered (ordered-args d f arity)))
		 #+ignore
		 `(forany () s.t. ,(cons (first form) ordered)
			  (-- ,(first form) ,@ ordered)
			  (++ ,(first form) ,@(ordered-args d r arity))
			  ifnone (throw 'uninsert-failure ',(first form)))
		 `(if (?? ,(first form) ,@ ordered)
		      (progn (-- ,(first form) ,@ ordered)
			     (++ ,(first form) ,@(ordered-args d r arity)))
		    (abort 'uninsert-failure
                           "required precondition not true: ~a ~a"
                           ',(first form) (list ,@ordered))))
	     (let ((ordered (ordered-args d r arity))
		   (ordered2 (ordered-args d tld arity)))
	       `(progn
		  (unless (?? ,(first form) ,. ordered)
		    (forany ,(mapcar #'cadr tld) s.t. ,(cons (first form) ordered2)
			    (-- ,(first form) ,@ ordered2)
			    ifnone nil))
		  (++ ,(first form) ,@ordered)))))
	 (values ,.(mapcar #'cadr r)))))))


(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; used in macro expansions within this file
(DEFUN DB-ACCESSOR-MACRO-GET (FORM PROPERTY other-properties 
			      &aux (properties (MKLIST PROPERTY)))
  (do ((tail form (cdr tail)))
      ((null tail) (values nil nil))
    (when (and (symbolp (first tail))
	       (member (first tail) properties :test #'string-equal))
      (return (values (loop for x in (cdr tail)
			    until (and (symbolp x)
				       (member x other-properties :test 'string-equal))
			    collect x)
		      t))))))


(defun possibletoupdate-directly (rel original-tv)
  ;; currently used only in create macro
  (flet ((generic-tuple (relation &aux rel arity)
	   (setf relation (if (relationp relation)
			      relation
			      (check-relation-package-error relation))
		 rel (relationp relation)
		 arity (if rel (arity* rel)
			   (if (descriptionp relation t)
			       (length (car relation)))))
	   (if arity
	       (cons relation (make-sequence 'list arity
					     :initial-element nil))
	       (error "~s not a relation" relation))))
    (let ((wff (generic-tuple rel)))
      (multiple-value-bind (expanded-wff tv)
	  (expand-update-wff wff original-tv)
	(if (atom expanded-wff)
	    nil
	    (let ((rel (relationp (first expanded-wff))))
	      (when  rel
		(unless (?? or (not-allowed-to-update rel tv)
			    (maintainedrel rel $ $))
		  (multiple-value-bind (single set cannot)
		     (update-code rel tv
			    (loop for i below (arity* rel) collect 'x))
		     (declare (ignore set single))
		     (not cannot))
		  ;; [**] above replaces implementationof below...
		  #+ignore ;; This was wrong - no mention of updaters
		  (if tv
		      (or (?? reladder (implementationof rel) $)
			  (?? reladder rel $))
		      (or (?? reldeleter (implementationof rel) $)
			  (?? reldeleter rel $)))))))))))

(DEFmacro CREATE (var-name &rest assignments
					&aux (tail assignments)
					var type-name
					clos-class)
  (multiple-value-setq (var type-name)
    (parse-var var-name))
  (when (eq var-name var)  (setf type-name var-name))
  (unless (?? type (relationp type-name))
    (setf type-name (check-relation-package-error type-name 1)))
  (unless (relationp type-name)
    (when (eq var var-name) (setf type-name 'entity))
    (warn "~a, used in (CREATE ~a ...), does not designate a class"
	  var-name var-name))
  (when (and (relationp type-name)
	     (not (?? relationarity (relationp type-name) 1)))
    (error "~a designates a relation, but not a type." type-name))

  `(atomic
    (let ((,var
	  ,(if (setf clos-class
		 (clos-class-for-relation (relationp type-name) $))
	      `(make-instance ',type-name)
	      '(make-dbobject))))
      ,.(unless (or clos-class
			   (eq type-name 'entity) (eq type-name 'dbobject))
		 `((,(if (possibletoupdate-directly  type-name t)
			 '++
			 'insist)
		    ,type-name ,var )))
      ,.(loop with arity and rel while tail
	   unless (and (symbolp (second tail)) (string= (second tail) "="))
	   do (error "syntax error -- missing \"=\" separator somewhere in~%~s"
			   (cadr tail) `(create ,var-name ,.assignments))
	   do (setf (first tail) (check-relation-name-ok (first tail) "create ... "))
	    when (= 1 (setf arity
			(if (relationp (first tail))
			    (arity* (relationp (first tail)))
			  ;; a description
			  (length (caar tail)))))
	    do (error "~s is a type. Used improperly in create" (first tail))
	    collect `(++ ,(setf rel (pop tail)) ,var
			      ,.(loop with arg initially (pop tail) ;; pop off =
				      for i below (1- arity)
				      do (setf arg (pop tail))
				      when (and (symbolp arg)(string= arg "="))
				      do (error "too few operands for ~s" rel)
				      collect arg
				      finally (when (and (symbolp (first tail))
							 (string= (first tail)
								  "="))
						(error
						  (error "too few operands for ~s"
							 rel))))))
      ,var)))


(DEFmacro DEFINE-CLASS (NAME &OPTIONAL PARENT-LIST  size &rest defrel-keys)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     (defrelation ,name :derivation basetype
		  ,@ (when size `(:size ((output) ,size)))
		  ,.defrel-keys)
     ,(when parent-list `(do-supers ',name ',(mklist parent-list)))
     (relationp ',name)))

(defun do-supers (sub supers &aux (subrel (relationp sub)))
  (atomic (dolist (s supers) (++ subtype subrel (relationp s)))))


;;; *** DEFATTRIBUTE***

(defvar *default-defattribute-count-enforcement* :incremental)

(defmacro defattribute (relname domain-name range-name
				&rest keys
				&key (countspec :any)
				(inverse-countspec :any)
				(domain-equivalence :default)
				(range-equivalence :default)
				replacing inverse-replacing
				default inverse-default
				(domain-type-enforcement '(:incremental :remove) dte-supplied)
				(range-type-enforcement '(:incremental :remove)
							rte-supplied)
				(count-enforcement *default-defattribute-count-enforcement*
						   ce-supplied)
				(inverse-count-enforcement *default-defattribute-count-enforcement*
							   ice-supplied)
				(size nil size-provided)
				(inverse-size nil inverse-size-provided)
				(total-size nil total-size-provided)
				(inverse-name nil inverse-name-provided)
				definition derivation computation
				&allow-other-keys
				&aux (named-type-repair-methods '(:remove :norepair)))
 
  
  (when (or definition derivation computation)
    (unless dte-supplied (setf domain-type-enforcement :none))
    (unless rte-supplied (setf range-type-enforcement :none))
    (unless ce-supplied (setf count-enforcement :none))
    (unless ice-supplied (setf inverse-count-enforcement :none)))

  (setf domain-type-enforcement (mklist domain-type-enforcement)
	range-type-enforcement (mklist range-type-enforcement)
	count-enforcement (mklist count-enforcement)
	inverse-count-enforcement (mklist inverse-count-enforcement))
  (when (and (eq :default (first count-enforcement))
	     (eq-length count-enforcement 2))
    (setf count-enforcement (list *default-defattribute-count-enforcement*
				  count-enforcement)))
  (when (and (eq :default (first inverse-count-enforcement))
	     (eq-length inverse-count-enforcement 2))
    (setf count-enforcement (list *default-defattribute-count-enforcement*
				  inverse-count-enforcement)))
  
  `(progn ;eval-when (load eval compile)
     (defrelation ,relname :arity 2 
	:types (,domain-name ,range-name)
	,@ (unless (and (eq domain-equivalence :default) (eq range-equivalence :default))
	     `(:equivs (,domain-equivalence ,range-equivalence)))
	:type-enforcements
	,(let (domain-when domain-how range-when range-how)
	   (flet ((repair-p (x) (or (member x named-type-repair-methods)
				    (and (consp x) (eq (first x) :repair))))
		  (enforce-p (x) (?? enforcement x)))
	     (setf
	       domain-when (or (find-if #'enforce-p domain-type-enforcement)
			       :incremental)
	       range-when  (or (find-if #'enforce-p range-type-enforcement)
			       :incremental)
	       domain-how (or (find-if #'repair-p domain-type-enforcement)
			      :remove)
	       range-how  (or (find-if #'repair-p range-type-enforcement)
			      :remove)))
	  (list (list domain-when domain-how) (list range-when range-how)))

	:count
	,(flet ((type-name (name)
		 (#-clisp progn #+clisp block #+clisp type-name
		  (unless (symbolp name) (return-from type-name name))
		   (multiple-value-bind (var-name var-type)
		       (parse-var name)
		     (declare (ignore var-name))
		     (or var-type name)))))
	   (let ((dtn (type-name domain-name))
		 (rtn (type-name range-name)))
	   `(,.(make-rc-args (list dtn 'OUTPUT)
			     countspec count-enforcement
			     default replacing)
	     ,.(make-rc-args  (list 'OUTPUT rtn)
			      inverse-countspec inverse-count-enforcement
			      inverse-default inverse-replacing))))
	:size (,.(when size-provided (list '(input output) size))
		,.(unless (or size-provided (eq countspec :any)(eq countspec :multiple))
		   (list '(input output) 1))
		,.(when inverse-size-provided (list '(output input) inverse-size))
		,.(unless (or inverse-size-provided
			     (eq inverse-countspec :any)(eq inverse-countspec :multiple))
		   (list '(output input) 1))
		,.(when total-size-provided
		   (list '(output output) total-size)))
	 ;;; pass all other keywords on to DEFRELATION
	 ,. (do ((tail keys (rest (rest tail)))
		 forward)
		((null tail) forward)
	      (unless (member (first tail)
			 '(:countspec :inverse-countspec :domain-equivalence
			   :range-equivalence :replacing :inverse-replacing
			   :default :inverse-default
			   :domain-type-enforcement :range-type-enforcement
			   :count-enforcement :inverse-count-enforcement
			   :size :inverse-size :total-size :inverse-name)
			 :test #'eq)
		(setf forward `(,(first tail) ,(second tail) ,. forward))))
	 )
   ; #+symbolics(global::record-source-file-name ',relname 'relation)
   ; #+ti(system::record-source-file-name ',relname 'relation)
     
     ,.(when inverse-name-provided 
	    `((defrelation ,inverse-name
				:definition ((x y) s.t. (,relname y x)))
              ;#+symbolics(global::record-source-file-name ',inverse-name 'relation)
              ;#+ti(system::record-source-file-name ',inverse-name 'relation)
	      ))
     (relationp ',relname)))


(defun make-rc-args (pattern countspec count-enforcement
			 default replacing &aux too-many too-few)

  (flet ((find-repair (code)
	   (second (find-if #'(lambda (x) (and (consp x)(eq (first x) code)))
			    count-enforcement))))
    ;;; check for default encoded in enforcement
    (let ((ed (find-repair :default)))
      (when ed
	(when default
	  (error "duplicate count repair specification for ~a -- ~a, ~a"
		 count-enforcement default ed))
	(setf default ed)))
    ;;; check for replace encoded in enforcement
    (let ((er (find-repair :replace)))
      (when er
	(when replacing
	  (error "duplicate count repair specification for ~a -- ~a, ~a"
		 count-enforcement replacing er))
	(setf replacing er)))

    (setf too-many (find-repair :too-many-repair)
	  too-few (find-repair :too-few-repair))
  
  (flet ((convert-to-nary-default (fn &aux (o (gensym)))
	   `(lambda (,o)
	      (declare (optimize (safety 1)(speed 3) (compilation-speed 0)))
	      (multiple-value-call
		#'(lambda (&rest vals)
		    (values-list (mapcar #'list vals)))
		(,fn ,o)))))
    `(,pattern :countspec ,countspec
	 :enforcement ,(or (find-if #'(lambda (x) (?? enforcement x ))
				    count-enforcement)
			   *default-defattribute-count-enforcement*)
	 ,. (when replacing (list :replacing replacing))
	 ,. (when default (list :default (convert-to-nary-default default)))
	 ,. (when too-many (list :too-many-repair too-many))
	 ,. (when too-few (list :too-few-repair too-few))))))

(defmacro defunion-class (Name Subclasses &rest defrel-keys)
  (multiple-value-bind (true-name type ename) (parse-var name)
    (when type (warn "ignoring ~s in ~s" type name))
    `(eval-when (:compile-toplevel :load-toplevel :execute)
       (defrelation ,true-name
	 :definition
	 ((,(if ename
		(intern (concatenate 'string "X@" (string ename))
			(find-package "AP5"))
		'x))
	  s.t. (or ,. (mapcar #'(lambda (c) (list c 'x)) subclasses)))
	 ,.defrel-keys)
       (let ,(when ename `((uequiv (theap5relation ,ename))))
	  ,.(mapcar
	      #'(lambda (c &aux (st `(++ subtype (theap5relation ,c) (relationp ',true-name))))
		  (if ename
		      `(when (eq uequiv (get-comparison (theap5relation ,c) 0))
			 ,st)
		      st))
	      Subclasses)))))

(defun unionclass (name keys &rest Subclasses &aux equiv (var 'x))
  (warn-ignored-keys name keys
    (:definition :equivs :implementation :adder :arity
		 :deleter :updater :tester :generator :trigger)
    (when (eq (car subclasses) :equiv) (pop subclasses)
	  (setf equiv (pop subclasses))
	  (setf var (intern (concatenate 'string "X@" (string equiv))
			    (find-package "AP5"))))
    `(:arity 1 :derivation defined :definition
	     ((,var) s.t. (or ,. (mapcar #'(lambda (c) (list c 'x)) subclasses)))
	     :alsofns
	     ,(cons `(lambda (rel)
		       (atomic reveal ; to get at the relation in the atomic
			 (loop for sub in ',subclasses
			       when (eql (get-comparison (relationp sub) 0)
					 (get-comparison rel 0))
			       do (++ subrel (relationp sub) rel))))
		    (getf keys :alsofns))
	     :computation nil :representation nil :implementation nil
             ;; 2012-5 - :derivation => defined for defrel multiple rep code
	     :derivation defined ,@ keys)))

(defmacro defintersection-class (Name Superclasses &rest defrel-keys)
  (multiple-value-bind (true-name type ename) (parse-var name)
    (when type (warn "ignoring ~s in ~s" type name))
    `(eval-when (:compile-toplevel :load-toplevel :execute)
       (defrelation ,true-name
		    :definition
	 ((,(if ename
		(intern (concatenate 'string "X@" (string ename)) (find-package "AP5"))
		'x))
	  s.t. (and ,. (mapcar #'(lambda (c) (list c 'x)) superclasses)))
	 ,. defrel-keys)
       (let ,(when ename `((uequiv (thea5relation ,ename))))
	 ,.(mapcar
	     #'(lambda (c &aux (st `(++ subtype (relationp ',true-name) (theap5relation ,c))))
		 (if ename
		     `(when (eq uequiv (get-comparison (theap5relation ,c) 0))
			,st)
		     st))
	     Superclasses)))))

(defun intersectionclass (name keys &rest Supclasses &aux equiv (var 'x))
  (warn-ignored-keys name keys
    (:definition :equivs :implementation :adder :arity
		 :deleter :updater :tester :generator :trigger)
    (when (eq (car supclasses) :equiv) (pop supclasses)
	  (setf equiv (pop supclasses))
	  (setf var (intern (concatenate 'string "X@" (string equiv))
			    (find-package "AP5"))))
    `(:arity 1 :definition
	     ((,var) s.t. (and ,. (mapcar #'(lambda (c) (list c 'x)) supclasses)))
	     ,(cons `(lambda (rel)
		       (atomic reveal ; to get at the relation in the atomic
			 (loop for sup in ',supclasses
			       when (eql (get-comparison (relationp sup) 0)
					 (get-comparison rel 0))
			       do (++ subrel rel (relationp sup)))))
		    (getf keys :alsofns))

	     :computation nil :representation nil :implementation nil
             ;; 2012-5 - :derivation => defined for defrel multiple rep code
	     :derivation defined ,@ keys)))

(pushnew 'fetch *update-macro-list*)
(pushnew 'update *update-macro-list*)
