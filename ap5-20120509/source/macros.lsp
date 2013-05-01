;;; -*- Mode:LISP; Package:AP5; Base:10.; Syntax:Common-Lisp -*-

(in-package "AP5")

; define this here in order stay independent of ilk:
(defun mkprogn (list)
  (cond ((not (consp list)) (error "bad argument to mkprogn"))
	((not (cdr list)) (car list))
	(t (cons 'progn list))))

(defun makevarlist (l)
  (if (listp (car l))
      (values (car l) (and (cdr l) t))
    (values l (notevery #'symbolp l))))


#-lucid
(defun report-no-data  (condition stream)
  (write-string "no data found satisfying:" stream)
  (terpri stream)
  (write (no-data-description condition) :stream stream))
  
#-lucid ; formerly #+(or allegro ti) - hope it works for symbolics etc.
(define-condition no-data (error)
    ((description :initform nil :type list :accessor no-data-description
		  :initarg :description))
    (:documentation "signalled by a failed database retrieval")
    (:report report-no-data))

#+lucid
(define-condition no-data (error)
    ((description nil))
    (:report (lambda (condition stream)
	       (write-string "no data found satisfying:" stream)
	       (terpri stream)
	       (write (no-data-description condition)
		      :pretty t :stream stream))))


(defun no-values-found (&optional desc)
  (if desc
       (progn
	 (restart-case (error 'no-data :description desc)
	   (no-data (&rest args)
	       :report "Supply values"
	       :interactive
	         (lambda ()
		   (let ((n (if (consp desc)
				(length (first desc))
			      (arity* (relationp desc)))))
		     (format *query-io* "supply ~a for ~s~%~
                                 (enter an expression to evaluate.)"
			     (if (= n 1) "a value" (format nil "~d values" n))
			     desc)
		     (let ((e (read *query-io*)))
		       (if (= n 1)
			   (list (eval e))
			 (multiple-value-list (eval e))))))
		 (return-from no-values-found (values-list args)))))
    (error 'no-data)))

(defmacro attempt
  (&body body &aux (block-name (gensym)) (this-form-block (gensym)))
  `(block ,block-name
     (macrolet ((no-values-found (&rest ignore)
		       `(return-from ,',this-form-block nil)))
			       
       ,@ (mapcar
	    #'(lambda (f)
		`(block ,this-form-block
		   (return-from ,block-name ,f)))
	    body))
     (error 'no-data)))

; as in loop-s.t. we now get the generator outside the bindings of the IV's
; *** perhaps we should do all the db reading in the same state??
(defmacro forany (&rest source) ;&environment env
     (let (body err ifnone foo ;evlrels evlvars desc varnames
		(wff 'true))
       (declare (ignorable foo))
       (multiple-value-bind (ignore vars tail)
	  (next-keyword-form (cons 'forany source) "forany" "s.t." "ifnone")
	  (declare (ignore ignore))
	  (if (string-equal (first tail) "s.t.");; s.t. explicit
	      (setf wff (second tail) tail (cddr tail))
	  ;; consider the first non-symbol (or NIL) after (car source) as the
	  ;; first body form.
	  ;; Each symbol must name a unary relation.
	  (loop for xx on (rest vars)
		while (and (first xx) (symbolp (first xx)))
		collect (first xx) into v
		finally (setf vars
			      (process-standalone-varlist (cons (first source) v))
			      tail (append xx tail))))
      (multiple-value-setq (vars err) (makevarlist vars))
      (when err
	(error "can't parse variables~&~s" (cons 'forany source)))
    ;;; tail is now set at the beginning of the forms to evaluate
      (setf ifnone `((no-values-found '(,vars s.t. ,wff))))
      (multiple-value-setq (foo body tail)
	(next-keyword-form (cons 'ifnone-body tail) "ifnone-body" "ifnone"))
      (loop while tail do
	    (multiple-value-bind (which code next-tail)
		(next-keyword-form tail "ifnone")
	      (when which (setf ifnone code tail next-tail))))
      #+ignore
      (progn
      (try (multiple-value-setq (desc evlvars evlrels)
	     (ExpandDescription (list vars 's.t. wff)
				:allowevalargs t
				:keepstarts t
				:environment env))
	   expanddescription
	   (fail ap5-cannot-generate (list vars 's.t. wff)
		 "not a valid description" tryvalue))
      (setf varnames (vars-to-names (car desc)))
      `(let (|Exhausted | ,@varnames ;;; this is wrong -- it scopes varnames over IFNONE
	     (|Gen | (let ,evlvars ,(get-generator desc evlvars evlrels))))
	 #+lucid (declare (ignore |Exhausted |))
	 ,.(when (temporalp (caddr desc))
	     `((check2states (mmemo (generate ,.(rels-to-names
						  (list vars 's.t. wff)))))))
	 (cond ((multiple-value-setq (|Exhausted | ,.varnames)
		  (do-pulse |Gen |))
		,.ifnone)
	       (t ,.body))))
      (let ((varnames (mapcar #'variablename vars))
	    (bname (gensym))
	    (bool (gensym))
	    (decl (loop while (and (consp (first body))(eq 'declare (caar body)))
		    collect (pop body))))
        ;; check that the generator can be found -- Saturday 2009/01/31 (!!)
        (macroexpand `(generator ,vars s.t. ,wff))
      `(block ,bname
	 (multiple-value-bind (,bool ,.varnames)
	   (withreadaccess (funcall (generator ,vars s.t. ,wff)))
	   ,.decl
	 (unless ,bool (return-from ,bname (progn ,.body))))
	 ,.ifnone)))))

(defmacro fortheonly (&rest source ;&environment env
				     )
  (let (ifone foo ifnone ifmany  err ;evlvars evlrels desc varnames
	(wff 'true))
    (declare (ignorable foo))
    (multiple-value-bind (ignore vars tail)
	(next-keyword-form (cons 'fortheonly source)
			   "fortheonly" "s.t." "ifnone" "ifmany")
      (declare (ignore ignore))
      (if (string-equal (car tail) "s.t.")  ;;  s.t. explicit
	  (setf wff (cadr tail) tail (cddr tail))
	  ;; consider the first non-symbol (or NIL) after (car source) as the
	  ;; first body form.
	  ;; Each symbol must name a unary relation.
	  (loop for xx on (cdr vars)
	   while (and (first xx) (symbolp (first xx)))
	   collect (first xx) into v
	   finally (setf vars
		     (process-standalone-varlist (cons (car source) v))
		     tail (append xx tail))))
      (multiple-value-setq (vars err) (makevarlist vars))
      (when err
	(error "can't parse variables~&~s" (cons 'fortheonly source)))
      (setf ifnone `((no-values-found '(,vars s.t. ,wff)))
	    ifmany `((error "multiply satisfied fortheonly ~A" ',(list vars 's.t. wff))))
    ;;; tail is now set at the beginning of the forms to evaluate
      #+ignore (setf memory (loop for v in vars collect (gensym)))
      (multiple-value-setq (foo ifone tail)
	(next-keyword-form (cons 'fortheonly-ifone tail)
			   "fortheonly-ifone" "ifnone" "ifmany"))
      ;; body is now the forms to evaluate; tail is what remains
      (loop while tail do
	    (multiple-value-bind (which code next-tail)
		(next-keyword-form tail "ifnone" "ifmany")
	      (setf tail next-tail)
	      (when which
		(selector which string-equal
			  ("ifmany" (setf ifmany code))
			  ("ifnone" (setf ifnone code))))))
      #+ignore
      (progn
	(try (multiple-value-setq (desc evlvars evlrels)
	       (ExpandDescription (list vars 's.t. wff)
				  :allowevalargs t
				  :keepstarts t
				  :environment env))
	     expanddescription
	     (fail ap5-cannot-generate (list vars 's.t. wff)
		   "not a valid description" tryvalue))
	(setf varnames (vars-to-names (car desc)))
	`(let (|Exhausted | ,@varnames
	       (|Gen | (let ,evlvars ,(get-generator desc evlvars evlrels))))
	   #+lucid (declare (ignore |Exhausted |))
	   ,.(when (temporalp (caddr desc))
	       `((check2states (mmemo (generate ,.(rels-to-names (list vars 's.t. wff)))))))
	   (cond ((multiple-value-setq (|Exhausted | ,.varnames) (do-pulse |Gen |))
		  ,.ifnone)
		 ((do-pulse |Gen |) ,.ifone)
		 (t ,.ifmany))))
      (let ((varnames (mapcar #'variablename vars))
	    (gname (gensym)) ;;used for both a variable and a block name
	    (switch (gensym))
	    (decl (loop while (and (consp (first ifone))(eq 'declare (caar ifone)))
		    collect (pop ifone))))
	;; this code grabs readaccess AROUND both pulses of the generator,
        ;; as well as establishing the generator
      `(block ,gname
	 (if (let  (,switch ,.varnames)
	       ;; the following expression must set switch to T if there are NO tuples,
	       ;; NIL if there are multiple,
	       ;; and :ok if there is just one, in which case it should also set varnames
	       ;; to the elements of that tuple
	       
	       (withreadaccess
		 (let ((,gname (generator ,vars s.t. ,wff)))
		   (multiple-value-setq (,switch ,.varnames) (funcall ,gname))
		   (unless ,switch
		     (when (funcall ,gname)
		       (setf ,switch :ok)))))
	       (if (eq ,switch :ok)
		   (return-from ,gname ((lambda ,varnames ,.decl ,.ifone) ,.varnames))
		   ,switch))
	     (progn ,.ifnone)	     
	     (progn ,.ifmany)))))))

(defmacro any (&rest source &aux (wff 'true) err)
  (multiple-value-bind (ignore vars tail)
      (next-keyword-form (cons 'any source) "any" "s.t." "ifnone")
    (declare (ignore ignore))
    (if (string-equal (first tail) "s.t.")  ;;  s.t.  explicit
	(setf wff (second tail) tail (cddr tail))
	(cond ((and (relationp (first vars))
		    (null (rest vars)))
	       (setf vars nil)
	       (dotimes (i (arity* (relationp (first source))))
			(push (gensym) vars))
	       (return-from any
                 `(any ,vars s.t. (,(first source) ,. vars) ,. (rest source))))
	      ((null (rest vars))
	       (let ((r (check-relation-package-error (first vars))))
		 (if (eq r (first vars))
		     (error "~s does not name a relation." (first vars))
		   (return-from any `(any ,r ,.tail)))))
	      (t (setf vars (process-standalone-varlist vars)))))
    (multiple-value-setq (vars err) (makevarlist vars))
    (when err (error "can't parse variables~&~s" (cons 'any source)))
    (when (and tail (not (symbolname "ifnone" (first tail))))
      (error "syntax error -- ~s" tail))
    `(forany ,vars s.t. ,wff (values ,. (mapcar #'variablename vars))
	     ,. tail)))


; This allows stuff like (any relation) - supply a type
(defun process-standalone-varlist (vars)
  (loop for v in vars collect
	(if (variabletypename v)
	    v
	  (let ((r (relationp v)))
	    (if (and r (= 1 (arity* r)))
	      (pack* v "#" v)
	      (error "~s does not name a unary relation." v))))))

(defmacro theonly (&rest source &aux (wff 'true) err)
  (multiple-value-bind (ignore vars tail)
      (next-keyword-form (cons 'theonly source)
			 "theonly" "s.t." "ifnone" "ifmany")
    (declare (ignore ignore))
    (if (string-equal (car tail) "s.t.")  ;;  s.t. explicit
	(setf wff (cadr tail) tail (cddr tail))
	(cond ((and (relationp (first vars))
		    (null (rest vars)))
	       (setf vars nil)
	       (dotimes (i (arity* (relationp (first source))))
		 (push (gensym) vars))
	       (return-from theonly
		 `(theonly ,vars s.t.
			   (,(first source) ,. vars) ,. (rest source))))
	      ((null (rest vars))
	       (let ((r (check-relation-package-error (first vars))))
		 (if (eq r (first vars))
		     (error "~s does not name a relation." (first vars))
		   (return-from theonly `(theonly ,r ,.tail)))))
	      (t (setf vars (process-standalone-varlist vars)))))
    (multiple-value-setq (vars err) (makevarlist vars))
    (when err
      (error "can't parse variables~&~s" (cons 'theonly source)))
    (when (and tail (not (or (symbolname "ifnone" (first tail))
			     (symbolname "ifmany" (first tail)))))
      (error "syntax error -- ~s" tail))
    `(fortheonly ,vars s.t. ,wff (values ,. (mapcar 'variablename vars)) ,.tail)))


#|
 (listof <vars> s.t. <wff>) => list of all the values
 if a single var then just the values, otherwise a list of lists
 provide the obvious (?) interpretation of
 (listof (any . desc))
 more importantly, of (listof e), 
 where e macroexpands into (any . desc)
 so we can use the notational shortcuts like (R x ~ y ~)
|#

(Defmacro ListOf (&environment e &rest x &aux vars wff tail)
  (when (and (consp (first x))
	     (null (rest x))
	     (symbolp (caar x)))
    (let ((m (ignore-errors (macroexpand-1 (first x) e))))
      (when (and (consp m) (eq (first m) 'any))
	(setf x `(,(mklist (second m)) s.t. ,(fourth m))))))
  (setf vars (ldiff x (setf tail (member "s.t." x :test #'symbolname))))
  (when (and (null tail) (rest vars)) (error "missing s.t.~%"))
  (when (and (null tail) (null (rest x)))
    (let ((rel (first x)))
      (unless (relationp rel)
	(let ((r (check-relation-package-error rel)))
	  (if (eq r rel)
	      (error "~s does not name a relation." rel)
	    (setf rel r))))
      (setf vars nil)
      (dotimes (i (arity* (relationp rel)))
	(push (gensym) vars))
      (return-from listof
	`(listof ,vars s.t. (,rel ,. vars)))))
  (when (listp (car vars))
    (if (cdr vars) (error "junk before s.t.") (setf vars (car vars))))
  (when (cddr tail) (error "junk at the end of ListOf ~s" (cddr tail)))
  (when (null tail)
    (setf vars (process-standalone-varlist vars)
	  tail
	  (list 's.t. 'true)))
  (setf wff (second tail))
  `(withreadaccess
     (loop for ,vars s.t. ,wff collect
	 ,(cond ((cdr vars)
		 `(list ,@(mapcar
			    #'(lambda (x)
				(cond ((symbolp x)(variablename x))
				      (t (error "Non-symbol used as variable -- ~s"
						x))))
			    vars)))
		(t (variablename (car vars)))))))


; (tuple-count . desc) => integer, number of tuples satisfying description
(Defmacro tuple-count (&rest x &aux vars tail rel)
  (setf vars (ldiff x (setf tail (member "s.t." x :test #'symbolname))))
  (when (and (null tail) (rest vars)) (error "missing s.t.~%"))
  (when (and (null tail)
	     (null (rest x))
	     (symbolp (first x))
	     (or (relationp (setf rel (first x)))
		 (relationp
		  (setf rel (check-relation-package-error (first x))))))
    (setf vars nil)
    (dotimes (i (arity* (relationp rel))) (push (gensym) vars))
    (return-from tuple-count
      `(tuple-count ,vars s.t. (,rel ,. vars))))
  (when (listp (car vars))
    (if (rest vars) (error "junk before s.t.") (setf vars (first vars))))
  (when (cddr tail) (error "junk at the end of tuple-count ~s" (cddr tail)))
  (if tail
      (let ((count-var (gensym)))
	`(let ((,count-var 0))
	   (do-s.t. (,vars ,(second tail) ,count-var)
		(incf ,count-var))))
    (let ((r (check-relation-package-error (first vars))))
      (if (eq r (first vars))
	  (error "~s does not name a relation." (first vars))
	`(tuple-count ,r)))))


; and now the typed variable stuff ...

(defmacro defun-typed (name lambda-list &rest body
		       &aux new-lambda-list type-decls tp)
  (loop for x in lambda-list
	when (member x '(&optional &key &rest &aux &allow-other-keys))
	collect x into nll
	else when (symbolp x)
	collect (VariableName x) into nll
	and when (setq tp (VariableTypeName x))
	collect (list tp (VariableName x)) into tds
	else do nil
	else collect (cons (VariableName (car x)) (cdr x)) into nll
	and when (setq tp (VariableTypeName (car x)))
	collect (list tp (VariableName (car x))) into tds
	finally (setq new-lambda-list nll type-decls tds))
  (multiple-value-bind (decls forms)
      (split-off-declarations body)
    `(defun ,name ,new-lambda-list ,. decls
	    ,. (when type-decls `((declare-type ,. type-decls)))
	    ,. forms)))

(defmacro declare-type (&rest declarations)
  `(progn
     ,.(loop for d in declarations nconc
	     (loop for var in (cdr d)
		   collect `(loop until (?? ,(car d) ,var)
				  do (setq ,var (FAIL PARAMETER-TYPE-FAULT
						      ',var ',(car d)
						      ,var)))))))


(defmacro returning (type &body forms)
  (cond ((and (listp type) (eq (car type) 'values))
	 `(multiple-value-call
	    #'(lambda (&rest values)
		(flet ((coerce-if-needed (testfn type index &aux (obj (nth index values)))
			 (loop until (funcall testfn obj) do
			       (setf (nth index values)
				     (setf obj
					   (FAIL RESULT-TYPE-FAULT type obj))))))
		,@(loop for tp in (rest type) as i from 0
		      collect `(coerce-if-needed #'(lambda (x) (?? ,tp x)) ',tp ,i)))
		(values-list values))
	    (progn ,.forms)))
	(t `(loop with bodyvalue = (progn ,.forms)
		  until (?? ,type bodyvalue)
		  do (setf bodyvalue (FAIL RESULT-TYPE-FAULT ',type bodyvalue))
		  finally (RETURN bodyvalue)))))

(defmacro let-typed (bindings &rest body)
  `(let ,.(prog-let-typed-expander bindings body)))

(defmacro prog-typed (bindings &rest body)
  `(prog ,.(prog-let-typed-expander bindings body)))

(defun prog-let-typed-expander (bindings body)
  (loop with tp for b in bindings
	when (listp b)
	collect (cons (VariableName (car b)) (cdr b)) into new-b
	and when (setq tp (VariableTypeName (car b)))
	collect (list tp (VariableName (car b))) into tds
	else do nil
	else collect (VariableName b) into new-b
	and when (setq tp (VariableTypeName b))
	collect (list tp (VariableName b)) into tds
	finally (multiple-value-bind (decls forms)
		    (split-off-declarations body)
		  (return
		    `(,new-b ,.decls
		      ,.(and tds `((declare-type ,. tds))) ,. forms)))))


(defun split-off-declarations (body)
  (when body
     (let ((forms (do ((tail body (rest tail)))
		      (nil)
		    (cond ((and (consp (first tail))
				(eq (caar tail) 'declare))
						;a declaration
			   )
			  ((and (stringp (first tail)) (rest tail))
			   ;; a doc string
			   )
			  (t (return tail))))))
       (values (ldiff body forms) forms))))

(defmacro aptypecase (key &rest clauses)
  `(LET (($$TSLQ ,key))
     (COND ,. (mapcar #'tsq1 clauses))))

(defun TSQ1 (l)
  (cond
   ((not (consp l)) (error "atomic clause in aptypecase - ~A" l))
   ((listp (car l))
    (or (loop for r in (car l) always (or (relationp r) (descriptionp r)))
	(error "not a list of types - ~A" (car l)))
    `((or ,@(mapcar #'(lambda (tp) `(?? ,tp $$TSLQ)) (car l)))
      ,.(cdr l)))
   ((member (car l) '(t otherwise))
    `(t ,.(cdr l)))
   (t
    (OR (relationp (car l))
	(descriptionp (car l))
	(ERROR "non type ~A" (CAR L)))
    `((?? ,(CAR L) $$TSLQ)
      ,.(CDR L)))))

#+(or ti symbolics)
(progn
(global:defflavor fail-error (tag messages)(global:error)
  :initable-instance-variables
  :gettable-instance-variables)

#+symbolics
(global:defmethod (:report fail-error)(stream)
  (format stream
	  "An untrapped failure of class ~a occured with arguments:~&~{  ~s~&~}."
	  tag messages))

#+ti
(ticl:defmethod (fail-error :report)(stream)
  (format stream
	  "An untrapped failure of class ~a occured with arguments:~&~{  ~s~&~}."
	  tag messages))

(global:defflavor PARAMETER-TYPE-FAULT (formal actual required-type
					(callee nil) (caller nil))(fail-error)
  :gettable-instance-variables
  :settable-instance-variables)

#+symbolics
(progn
(defmacro examine-stack (frame &body forms)
  `(catch :here
     (scl:condition-bind
       ((global:ferror #'(lambda (condit)
		    (throw :here
			   (dbg::with-erring-frame (,frame condit) ,.  forms)))))
       (global:ferror ""))))

(defun find-interesting-active-frame-named
       (name &optional (frame dbg::*current-frame*))
  (do ((Fr  frame (dbg:FRAME-PREVIOUS-INTERESTING-ACTIVE-FRAME Fr)))
      ((null Fr) nil)
    (when (eq name (sys:FUNCTION-NAME (sys:FRAME-FUNCTION Fr)))
      (return fr))))

(global:defmethod (:init PARAMETER-TYPE-FAULT :after) (&rest ignore )
  (setq formal (car messages)
	required-type (cadr messages)
	actual (caddr messages))
  (multiple-value-bind (c1 c2) 
      (examine-stack cf
	(let* ((signal-frame (find-interesting-active-frame-named 'scl::signal cf))
	       (f1 (when signal-frame
		     (dbg:FRAME-PREVIOUS-INTERESTING-ACTIVE-FRAME signal-frame)))
	       (f2 (when f1
		     (dbg:FRAME-PREVIOUS-INTERESTING-ACTIVE-FRAME f1))))
	  (values (when f1 (sys:FUNCTION-NAME (sys:FRAME-FUNCTION f1)))
		  (when f2 (sys:FUNCTION-NAME (sys:FRAME-FUNCTION f2))))))
    (setq callee c1 caller c2 )))

(global:defmethod (:report PARAMETER-TYPE-FAULT)(stream)
  (format stream
	  "A paramater of the wrong type was passed.~&The formal parameter is named ~a, of type ~a.~&" 
	  formal required-type)
  (format stream "The actual parameter was ~s."
	  actual  )
  (format stream "~&The function ~a was being called by ~a."
	  callee caller))
)

#+ti
(ticl:defmethod (PARAMETER-TYPE-FAULT :report)(stream)
  (format stream
	  "A paramater of the wrong type was passed.~&The formal parameter is named ~a, of type ~a.~&" 
	  formal required-type)
  (format stream "The actual parameter was ~s."
	  actual  )
  (format stream "~&The function ~a was being called by ~a."
	  callee caller))

(global:defflavor RESULT-TYPE-FAULT (required-type return-value from to )(fail-error)
  :gettable-instance-variables
  :settable-instance-variables)

#+symbolics
(global:defmethod (:init RESULT-TYPE-FAULT :after) (&rest ignore)
  (setq required-type (car messages)
	return-value (cadr messages))
  (multiple-value-bind (c1 c2)
      (examine-stack cf
	(let* ((signal-frame (find-interesting-active-frame-named 'signal cf))
	       (f1 (when signal-frame
		     (dbg:FRAME-PREVIOUS-INTERESTING-ACTIVE-FRAME signal-frame)))
	       (f2 (when f1
		     (dbg:FRAME-PREVIOUS-INTERESTING-ACTIVE-FRAME f1))))
	  (values (when f1 (sys:FUNCTION-NAME (sys:FRAME-FUNCTION f1)))
		  (when f2 (sys:FUNCTION-NAME (sys:FRAME-FUNCTION f2))))))
    (setq from c1 to c2 )))

#+symbolics
(global:defmethod (:report RESULT-TYPE-FAULT)(stream) 
  (format stream
	  "A value of the wrong type is being returned.~&The required type is ~a.~&" 
	  required-type)
  (format stream "The value is ~s." return-value  )
  (format stream
	  "~&The value is being returned from the function ~a to the function ~a."
	  from to))

#+ti
(ticl:defmethod (RESULT-TYPE-FAULT :report)(stream) 
  (format stream
	  "A value of the wrong type is being returned.~&The required type is ~a.~&" 
	  required-type)
  (format stream "The value is ~s." return-value  )
  (format stream
	  "~&The value is being returned from the function ~a to the function ~a."
	  from to))
)

#||
WFF-IF is like the GIST if -- 
(1) uses the if-then-elseif-else  syntax
(2) requires WFFs, not lisp expressions, following IF and ELSEIF
(3) provides access to bindings of leading existential/universal quantified
   variables in the appropriate forms

(unlike gist, THEN clauses are not required for the IF/ELSEIF clauses.
Omitted then clauses are treated like THEN T.  Also, an omitted final
ELSE clause is treated like ELSE T) 
||#

(defmacro wff-if (&rest ifform)
  (labels ((wff-iftail (tail &aux  in-this-case newtail quant vars wff response)
	     (unless (cdr tail) (error  "bad WFF-IF syntax ~a"  tail))
	     (cond ((string-equal (car tail) "else")
		    (list (cons t (cdr tail))))
		   (t (when (null (cddr tail))
			; no then clause - treat it as THEN T
			(setq tail `(,.tail then t)))
		      (if (and (listp (cadr tail)) (member (caadr tail) '(A E)))
			  (setq vars (second (cadr tail))
				wff (third (cadr tail)) 
				quant (caadr tail))
			(setq wff (cadr tail)))
		      (cond ((and (symbolp (caddr tail))
				  (string-equal (caddr tail) "then"))
			     (unless (cdddr tail) (error "bad WFF-IF syntax ~a" tail))
			     (multiple-value-setq (in-this-case newtail)
				 (flet ((gobble-forms (forms )
					  (loop for tail = forms then (cdr tail) while tail
						until (and (symbolp (car tail))
							   (member (car tail) '("else" "elseif") :test #'string-equal))
						collect (car tail) into result
						finally (return (values result tail)))))
				   (gobble-forms (cdddr tail))))
			     (setq response in-this-case))
			    (t;; no then clause
			     (setq response (list t))
			     (setq newtail (cddr tail))
			     (unless (and (symbolp (car newtail))
					  (or (string-equal (car newtail) "else")
					      (string-equal (car newtail) "elseif")))
			       (error "bad WFF-IF syntax ~a" tail))))
		      (cond ((eq quant 'E)
			     `((t (forany ,vars s.t. ,wff ,. response ifnone
					  ,(when newtail
					     (cons 'cond (wff-iftail newtail)))))))
			    ((eq quant 'A)
			     `((t (forany ,vars s.t. (not ,wff)
					  ,(when newtail (cons 'cond (wff-iftail newtail)))
					  ifnone ,.response))))
			    (t `(((?? ,. wff) ,.response)
				 ,.(and newtail (wff-iftail newtail)))))))))
    (cons 'cond (wff-iftail (cons 'wff-if ifform)))))


#+ignore 
"(wff-if (relation x) then (foo)
	Elseif (and (eql a b)(E (y) (relationname x y)))
	then (fum) (bar)
	else (junk))

(wff-if (relation x) then (foo)
	elseif (E (y) (relationname x y))
	then (fum y) (bar)
	else (junk))

(wff-if (relation x) then (foo)
	elseif (E (z) (relationname x z))
	then (bar z)
	elseif (A (y) (relationname x y))
	then (fum )
	else (junk y))
"
