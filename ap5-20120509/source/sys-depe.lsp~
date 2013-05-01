;-*- Mode: Lisp; Package:AP5; Syntax:COMMON-LISP; Base:10 -*-

(in-package "AP5")

#+allegro ;; map any compound feature names to non-compound ones
(eval-when (:compile-toplevel :load-toplevel :execute)
  (when (read-from-string "(#+(version>= 4 3 2) t)")
    (pushnew :allegro>=4-3-2  *features*))
  (when (read-from-string "(#+(version>= 5 0) t)")
    (pushnew :allegro>=5-0  *features*)))



#| 
There are several sections:
 1. stuff that will probably not be changed for a new implementation
 2. stuff that has default implementations but you may want to change
    it for a new one
 3. stuff that needs to be reimplemented
|#

; section 1. stuff that will probably not be changed for a new implementation

;                                                 ----- buffer-break
; The purpose of buffer-break is to prevent compile-file from
; putting two forms together when the first one has to be evaluated
; before the second can successfully read, e.g., if the first defines
; relation R and the second contains something like #,(relationp R).

#+(or lispworks (and lucid sparc))
(defmacro buffer-break ()
  '(eval-when (:load-toplevel :execute) nil))

#-(or lispworks (and lucid sparc))
(defmacro buffer-break () nil)

;                                                ----- *empty-env*
; a default for environment arguments - cltl2 p208 says nil should be ok
;; #+clisp(defvar *empty-env* (vector nil nil))
;; sys::*toplevel-environment* ??
(defconstant *empty-env* nil)

;                                                ----- defmacro-displace
#-symbolics
(defmacro defmacro-displace (&rest arg) `(defmacro ,.arg))

;                                                ----- displaced
#-(or symbolics ti)
(defmacro displaced(x y) (declare (ignore x)) y)

;                                                ----- unmacroexpand
(lisp:defun unmacroexpand (form)
  (cond ((and (consp form)
	      (eq (car form)
		  #+symbolics 'si::displaced
		  #+ti 'sys::displaced
		  #-(or ti symbolics) 'displaced))
	 (unmacroexpand (cadr form)))
	(t form)))

#+symbolics(or (member (find-package "AP5") si:*reasonable-packages*)
	       (push (find-package "AP5") si:*reasonable-packages*))


;                                                          ----- compile
;; The only change is to bind the special variable *fn-being-compiled*.
;; We'd like to be able to trace out the generators used by a particular
;; piece of code in order to be able to put them into compiled files.
;; Lookup-gen will record that it was called on some argument during the
;; compilation of a particular function.  

(defvar *fn-being-compiled* nil)
#-lucid
(lisp:defun compile (*fn-being-compiled* &rest args )
 ;;(let ((sys::*fasoutput-stream* nil)) ;; clisp bug?
   (apply #'lisp::compile *fn-being-compiled* args))
 ;;)

#+lucid
(progn
 #+ignore ; #+lcl4.1 ; ? originally #-LCL4.0
 (eval-when (:compile-toplevel :load-toplevel :execute)
  (mapc #'(lambda (x) 
	    (export (intern x sys:*lucid-package*)
		    sys:*lucid-package*))
	'("*COMPILE-OUTPUT-FILENAME*"
	  "MAKE-LOADTIME-EVALMARKER"))
 )
 (lisp:defun compile (*fn-being-compiled* &rest args)
  (declare (special lucid::*compile-output-filename*))
  (if (boundp 'lucid::*compile-output-filename*)
      (let (lucid::*compile-output-filename*)
	(declare (special lucid::*compile-output-filename*))
	(apply #'lisp::compile *fn-being-compiled* args))
      (apply #'lisp::compile *fn-being-compiled* args)))
)

;; notice that we can't put stuff just in compile and expect it to be
; done on every compilation, e.g. compile-file doesn't call compile

;                                                          ----- mycompile

#+TI
(lisp:defun MyCompile (*fn-being-compiled* lambda-exp &aux
					   (fspec *fn-being-compiled*))
  (let ((compiler:*suppress-debug-info* t) compiler::qc-file-in-progress)
	(compile fspec lambda-exp)))

(defmacro with-optimizations (opt &body b &aux (old-opt (gensym "OLD-OPT")))
  #-(or lucid allegro)(declare (ignore opt old-opt))
  `(let (#+lucid(,old-opt (copy-tree lucid::*compiler-optimizations*))
	 #+allegro (,old-opt #+allegro>=4-3-2
			    `((speed ,excl::.speed.) (safety ,excl::.safety.)
			      (space ,excl::.space.) (debug ,excl::.debug.))
			    #-allegro>=4-3-2
			    `((speed ,comp::.speed.) (safety ,comp::.safety.)
			      (space ,comp::.space.) (debug ,comp::.debug.))))
     (unwind-protect
	 (progn
	   #+(or allegro lucid) (proclaim '(optimize ,.opt))
	   ,.b)
       #+allegro (proclaim (cons 'optimize ,old-opt))
       #+lucid
       (proclaim (cons 'optimize
		   (mapcar #'(lambda (qq) (list (first qq) (rest qq)))
                        ,old-opt ))))))

; perhaps the whole compile of ap5 ought to be done with such optimizations?
#-ti
(lisp:defun MyCompile (*fn-being-compiled* lambda-exp)
  (with-optimizations ()
		      #+ignore ((speed 3) (safety 2) (compilation-speed 0))
    (compile *fn-being-compiled* lambda-exp)))


; ansi loop macro now loaded
;                                                                 ------ loop

(defvar *ap5-loop-universe* nil)

;; for some reason in allegro the excl package is used instead ansi-loop ...
(eval-when (:compile-toplevel :load-toplevel :execute)
 (setf *ap5-loop-universe*
       (#-allegro ansi-loop::make-ansi-loop-universe
	#+allegro excl::make-ansi-loop-universe
	t))
 (setf (gethash "S.T." (#-allegro ansi-loop::loop-universe-for-keywords
			#+allegro excl::loop-universe-for-keywords
			*ap5-loop-universe*))
       '(LOOP-FOR-S.T.)))
(defmacro loop (&environment env &rest keywords-and-forms)
  (#-allegro ansi-loop::loop-standard-expansion
   #+allegro excl::loop-standard-expansion
   keywords-and-forms env *ap5-loop-universe*))

(lisp::defun loop-for-s.t. (originalvars wff datatypes
		      &aux outputs pulser
		      (genfn (gentemp "GenFn "))
		      (exhausted (gentemp "Exhausted ")))
    (when (or (and (symbolp wff) (not (member wff '(true false))))
	      (descriptionp wff t))
	   (setf wff (cons wff (copy-list originalvars))))
    (multiple-value-bind (varnames evlvars initializer temporal)
	(analyze-desc originalvars wff)
    #-allegro(ansi-loop::loop-make-iteration-variable varnames nil datatypes)
    #-allegro(ansi-loop::loop-make-iteration-variable exhausted nil nil)
    #-allegro(ansi-loop::loop-make-iteration-variable genfn
		     `(let ,evlvars ,initializer) nil)
    #+allegro(excl::loop-make-iteration-variable varnames nil datatypes)
    #+allegro(excl::loop-make-iteration-variable exhausted nil nil)
    #+allegro(excl::loop-make-iteration-variable genfn
		     `(let ,evlvars ,initializer) nil)
    ; do init without IV's bound, e.g. *package* might affect the computation
    ;; Monday 2010/10/11 ignorable was under #+allegro
    ;; Thursday 2010/10/14 make all vars ignorable since 
    ;; there's no way to declare them so
    (push `(ignorable ,exhausted ,.varnames)
	  #-allegro ANSI-LOOP::*LOOP-DECLARATIONS*
	  #+allegro EXCL::*LOOP-DECLARATIONS*)
    (setq outputs (cons exhausted varnames))
    (setq pulser `(multiple-value-setq ,outputs (do-pulse ,genfn)))
    ; eachtime {pretest steps posttest pseudo} firsttime {pretest ...}
    (list nil nil pulser nil
	  (cond (temporal #+ignore (temporalp (caddr body))
		 `(check2states
		    (mmemo (generate ,.(rels-to-names
					 (list originalvars 's.t. wff)))))))
	  ; not actually used as a test
	  nil pulser nil)))

#+ignore 
(#+(or symbolics lucid) (shadow '(lisp::loop) (find-package "AP5")) 
    ; make it displacing on symbolics
    ; needed for (loop for vars s.t. wff ...) syntax in lucid
 #+allegro (require :loop) ;; don't know how to displace here ...
 ;; for now we just keep TI loop

 #+symbolics
 (global:defmacro-displace loop (&environment e &rest body)
   (macroexpand-1 `(lisp:loop ,.body) e))
 ; lisp:loop is not displacing so we better macroexpand it
 ; expansion fn on symbolics seems not to use env ... 
 ; formerly (global:defmacro-displace loop (&rest body) `(lisp:loop ,.body))

 #+(or ti symbolics)
 (shadowing-import 
  '(si::loop-make-iteration-variable si::loop-for-keyword-alist))
 #+allegro
 (shadowing-import 
  '(loop::loop-make-iteration-variable loop::loop-for-keyword-alist))
 #+lucid
 (defmacro ap5::loop (&rest args &aux pos (result args) (start 0))
   (lisp::loop while (setf pos (position-if #'(lambda (y)
					     (when (symbolp y) 
					       (string-equal "s.t."
						 (symbol-name y))))
					    result
					    :start start))
	 do
	 (setf result (append (subseq result 0 (- pos 1))
			      (let ((vars (nth (1- pos) result)))
				(unless (listp vars)
				  (setf vars (list vars)))
				`(,vars being the tuples of))
			      (nthcdr (1+ pos) result))
	       start (+ pos 5)))
   (cons 'lisp::loop result))
)

;                                                ----- theap5relation
(lisp:defun relationp-err (name)
  (or (relationp name)
      (relationp (check-relation-package-error name))
      (error "~s is not a relation" name)))

#-(or symbolics) ;  allegro
(defmacro theap5relation (name)
  (cond ((symbolp name)
	 `(the dbobject (load-memo (relationp-err ',name))))
	((descriptionp name)
	 `',name)
	(t (error "~s not a relation" name))))

#+(or symbolics) ;  allegro
;; wouldn't be needed if load-memo compilation to file could
; eliminate call on DATA-FROM
(defmacro theap5relation (name)
  (cond ((symbolp name)
	 `(quote ,(relationp-err name)))
	((descriptionp name)
	 `',name)
	(t (error "~s not a relation" name))))

; Maybe-memo - for machines that can't dump dbo's, translate them into memos
; formerly for (or TI symbolics) - it's cleaner to stay in commonlisp
(defmacro mmemo (x) (kwote x))


;                                              ----- compile-or-MExpand
; in order to selectively avoid compilation ...
(lisp:defun compile-or-MExpand (name lambda-exp &optional dont-compile-p)
  #+lucid (declare (special lucid::*compile-output-filename*))
  DONT-COMPILE-P
  (progn #+lucid (if (boundp 'lucid::*compile-output-filename*)
		     (let (lucid::*compile-output-filename*)
		       (declare (special lucid::*compile-output-filename*))
		       (compile name lambda-exp))
		     (compile name lambda-exp))
	 #-lucid (compile name lambda-exp))
)

;                                                         ---- defun
#+(or ti symbolics)
(eval-when (:compile-toplevel :load-toplevel :execute)
 (progn
  (defvar *lisp-defun* (find-symbol "DEFUN" "LISP"))
  ; This is ugly but seems to work
  (defmacro new-defun (*fn-being-compiled* &rest body &environment env
					   &aux expansion)
  (setf (get *fn-being-compiled* 'uses-generator) nil)
  ; mexpand in order to see what gen's it uses
  (setq expansion (mexpand-all (cons 'lambda body) env))
  ; as long as it's done, might as well use it?
  `(progn
     ;; *** note - this has not been tested for ti/symbolics
      ,.(loop for desc in (get *fn-being-compiled* 'uses-generator)
	    append (anon-rels-in-wff (third desc) env))
      ,@(save-generators-for-fn *fn-being-compiled*)
      (,*lisp-defun* ,*fn-being-compiled* ,@(cdr expansion))))
  (defvar *ap5-defun* (find-symbol "DEFUN" "AP5"))
  (setf (macro-function *ap5-defun*) (macro-function 'new-defun))
  (setf (symbol-function *ap5-defun*) (symbol-function 'new-defun))
 ))

(defvar *in-anon-rel-context* nil) ;; see wffs
#-(or ti symbolics)
(defmacro defun (*fn-being-compiled* arglist &environment env &rest body
		 &aux (*in-anon-rel-context* t))
  (setf (get *fn-being-compiled* 'uses-generator) nil)
  (mexpand-all
	 `(lambda nil (lisp::defun ,*fn-being-compiled* ,arglist ,.body))
	  env)
  ;; recursive macroexpansion can be truly horrendous in size ...
  ;; some implementations of mexpand-all return it, some don't
  `(progn
      ,.(loop for desc in (get *fn-being-compiled* 'uses-generator)
	    append (anon-rels-in-wff (third desc) env))
      ,@(save-generators-for-fn *fn-being-compiled*)
      (lisp::defun ,*fn-being-compiled* ,arglist ,@body)))


;                                                         ---- defmethod
;;#-(or lucid allegro)
(defmacro defmethod (&environment env &rest body)
  (let ((*fn-being-compiled* (gensym)) (*in-anon-rel-context* t))
    (mexpand-all `(lambda ()
		    (#+(or lucid) clos:defmethod
		     #-(or lucid) lisp:defmethod
		     ,.body))
		 env)
    (prog1
	`(progn
	   ,.(loop for desc in (get *fn-being-compiled* 'uses-generator)
		 append (anon-rels-in-wff (third desc) env))
	   ,@(save-generators-for-fn *fn-being-compiled*)
	   (#+(or lucid) clos:defmethod
	      #-(or lucid) lisp:defmethod
	      ,.body))
      ;; why is this needed - the gensym will be gc'd, right?
      (setf (symbol-plist *fn-being-compiled*) nil))))

#+ignore ;was (or lucid allegro)
(defmacro defmethod (&environment env &rest body)
  (let ((*fn-being-compiled* (gensym)))
    (multiple-value-bind (gfname qualifiers sll body-forms)
	(#+lucid CLOS-SYSTEM:PARSE-DEFMETHOD
         #+allegro CLOS::PARSE-DEFMETHOD
	 body)
      (declare (ignore qualifiers))
      (multiple-value-bind (ignore full)
	  (#+lucid CLOS-SYSTEM:PARSE-SPECIALIZED-LAMBDA-LIST
	   #+allegro CLOS::PARSE-SPECIALIZED-LAMBDA-LIST
	   sll)
	(declare (ignore ignore))
	(let ((pure-lambda `(lambda ,full ,.body-forms)))
	  (mexpand-all `(lambda nil
			  (flet (#+lucid(lcl:next-method-p () nil)
				 #+lucid(lcl:call-next-method (&rest args)
				   (declare (ignore args))
				   nil))
			    ,(if (symbolp gfname)
			       `(block ,gfname #',pure-lambda)
			     `#',pure-lambda)))
		       env))))
	; block needed in case of return-from
    (prog1
	`(progn ,@(save-generators-for-fn *fn-being-compiled*)
		(#+lucid clos:defmethod
		 #+allegro lisp:defmethod
		 ,.body)
		)
      (setf (symbol-plist *fn-being-compiled*) nil))))


(lisp::defun save-generators-for-fn (fname)
  (when (symbolp fname)
    (loop for desc in (get fname 'uses-generator)
	  when (compoundwffp (third desc))
	  collect (compile-code-for-desc desc))))

; set these to alter behavior
(defvar *compile-ap-to-file* t)
(defvar *compile-ap-source-to-file* nil)

(defvar saveprops '(initialstate effort template))
; not permutation ntimesfound output size

(lisp::defun compile-code-for-desc
	     (description &aux fn def
			  (tfn (#-clisp gensym #+clisp gentemp "GEN"))
	      (desc (list (first description) (second description)
			  (map-copy-wff (third description))))
	      (entry (gen-cache-i-i-o desc)))
  
  (when (and *compile-ap-to-file*
	     (setf fn (cadr (assoc 'initialstate entry)))
	     ;; need two different set's to test both conditions
	     (setf def (or (let ((old (prevdef fn)))
			     (when (and (consp old)
					(eq (car old) 'lambda))
			       old))
			   (get-generator-source desc))))
    `(progn
       (defun ,tfn ,@(copy-list (cdr def))) ; get rid of the lambda
       ; copy it so the macros don't get displaced
       (let ((desc (list ',(car desc) 's.t.
			 (map-copy-wff ',(vars&rels-to-names-wff
					  (caddr desc))))))
	 
	 ;; shouldn't the preceding be INSIDE the unless?
	 (unless (gen-cache-i-i-o desc)
	   (let ((newfn (gentemp "F" ap-compiled)))
	     
	   ,.(loop for x in (get fn 'uses-generator) collect
		 `(let ((*fn-being-compiled* newfn))
		    (record-use-of-generator
		      (list ',(first x) 's.t.
			    (map-copy-wff ',(vars&rels-to-names-wff
					     (third x)))))))
	   (setf (symbol-function newfn) (symbol-function ',tfn))
	   ,(when *compile-ap-source-to-file*
	      `(setf (get newfn :previous-definition) ',def))
	   ; these used to be above, outside the unless - the result was that
	   ; when a defun was INTERPRETED we got an interpreted ap-compiled fn.
	   ; (It was never used but ugly.)
	   (genadder desc
		     (list ,@(loop for x in entry
				   when (member (car x) saveprops)
				   collect
				   (cond ((eq (car x) 'initialstate)
					  `(list 'initialstate newfn))
					 (t (kwote x)))))))))
       (fmakunbound ',tfn))))

#+ignore ;lucid
(defun compile-now-if-possible (fspec defn)
  (with-compiler-locked-if-available (gotit)
    (if gotit
	(compile symbol defn)
      (progn
	(unless fspec (setf fspec (gensym)))
	(let ((new-defn
	        #'(lambda (&rest args)
		     (apply
		      (with-compiler-locked-if-available (gotit)
			 (if gotit
			     (compile fspec defn)
			   defn))
		      args)))))
	  (setf (symbol-function fspec) new-defn)
	  fspec))))

;; compiler lock is lucid:*compiler-lock*
	




; section 2


;                                                    ------ defvar-resettable
; for systems that have some notion of warm boot (lispms)

#+symbolics
(import '(global::defvar-resettable) "AP5")

#+TI
(progn
 (defvar *warm-boot-bindings* nil
  "List of lists of length two, each length two list has a car of a variable 
 and a cadr of a value to be bound to that variable at warm boot time.  
 This is used by defvar-resettable.")

 (lisp:defun initialize-resettable-bindings (name-of-list)
  (declare (type list name-of-list))
  (let ((binding-list (symbol-value name-of-list)))
    (map nil #'(lambda (x) (setf (symbol-value (car x)) (cadr x)))
	 binding-list))) 

 (global::add-initialization
  "Restore resettable variable values"
  '(initialize-resettable-bindings '*warm-boot-bindings*)
  :warm)

 (lisp:defun remember-variable-bindings (name value name-of-list)
  (declare (type symbol name name-of-list))
  (let ((old-value (assoc name (symbol-value name-of-list) :test #'eq)))
    (if old-value
	(setf (second old-value) value)
	(push (list name value) (symbol-value name-of-list)))))

 (defmacro defvar-resettable (name initial-value &optional
			     (warm-boot-value initial-value) documentation)
  `(prog1 (defvar ,name ,initial-value ,documentation)
	  (remember-variable-bindings ',name
				      ,warm-boot-value 
				      '*warm-boot-bindings*)))) 

#-(or TI SYMBOLICS)
(defmacro defvar-resettable (var &rest args)
  `(defvar ,var ,.(when args `(,(car args)))))




;                                                ------ current-process(-name)
; for systems with multiple processes

#+(or ti symbolics)
(defmacro current-process () 'global::current-process)
#+(or ti symbolics)
(lisp:defun current-process-name () (global::send (current-process) :name))
#+allegro
(eval-when (:compile-toplevel :load-toplevel :execute) (require :process))
#+allegro
(progn
 ;;(use-package :multiprocessing) ;???WHY
 ;#+allegro (mp::start-scheduler)
 (defmacro current-process () 'mp:*current-process*)
  ; gotta get these two in the right order
 (lisp:defun current-process-name () (mp:process-name (current-process))))
#+lucid
(progn
 (defmacro current-process () 'lcl:*current-process*)
 (lisp:defun current-process-name () (lcl:process-name (current-process))))
#+lispworks ;; harlequin
(progn
 ; not a good thing to stick in a file, since it never returns
 ;(mp::initialize-multiprocessing)
 (defmacro current-process () 'mp:*current-process*)
 (lisp:defun current-process-name ()
     (when (current-process) (mp:process-name (current-process)))))

#+(and clisp mt)
(progn
 (defmacro current-process () '(mt:current-thread))
 (lisp:defun current-process-name () (mt:thread-name (current-process))))

; for others we still need a process name to record in history
#-(or lucid ti allegro symbolics lispworks (and clisp mt))
(lisp:defun current-process-name () "the only process")

#| Saturday 2009/02/21
Note that before now I never tried to make this stuff work in machines that
actually could run two processes/threads at once.  In a situation where only
one can run at a time, without-interrupts really means that no other thread
can run while the without-interrupts body runs.  I now have to change the
implementation so that other threads can run during that time.
The current uses of without-interrupts seems to be limited to implementation
of read/write locks (and update of nonatomic rels, which really should also
be withwriteaccess).  (Also process-wait inside implementations of locks.)

|#

#+(and clisp mt)
(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; we'll have ONE mutex that we use for getting/returning read/write access
  (defvar *scheduling-mutex* (mt:make-mutex :name "scheduling-mutex"))
  (defmacro without-interrupts (&rest forms)
    ;; this now means NOT that nothing else executes at the same time
    ;; or even that the forms are not interrupted, but rather that
    ;; they happen with exclusive use of the lock
  `(mt:with-mutex-lock (*scheduling-mutex*) ,@forms))
  )
;                                                    ----- without-interrupts
; for systems with multiple processes
#-(or ti symbolics allegro lucid lispworks (and clisp mt))
(defmacro without-interrupts (&rest forms)  `(progn ,@forms))
#+(or symbolics ti) 
(import 'global::without-interrupts)
#+allegro
(defmacro without-interrupts (&rest forms)
  `(mp::without-scheduling ,@forms))
#+lucid
(defmacro without-interrupts (&rest forms)
  `(lcl:with-scheduling-inhibited ,@forms))
#+lispworks
(defmacro without-interrupts (&rest forms)
  `(lispworks:WITHOUT-PREEMPTION ,@forms))

;                                                       ----- with-whostate
; do forms with the whostate bound
; unfortunately, other places don't bind the whostate but just set it,
; so after it changes to tyi, for example, it won't change back.

; In order to install whostates for non-lispms, 
; - provide a new definition for who-line-process-change
; - set do-whostates to T
; - recompile do-with-whostate

(eval-when (:compile-toplevel :load-toplevel :execute)
#+(or TI symbolics)
(import	'(global::process-whostate global::process-wait
	  tv:who-line-process-change))
#+allegro
(import	'(mp::process-whostate mp::process-wait))
#+lucid
(import	'(lcl:process-whostate lcl:process-wait))
)
#+lispworks ; I'm not sure this is quite right, but prob. not even used
(defmacro process-whostate (process)
  `(mp::PROCESS-WAIT-REASON ,process))
#+lispworks 
; mp::process-wait gets a bus error if multiprocessing not initialized
(lisp::defun process-wait (&rest rest)
  (when (current-process) (apply #'mp::process-wait rest)))
#-(or TI symbolics)
(progn (declaim (inline who-line-process-change))
       (lisp:defun who-line-process-change (process)
	 (declare (ignore process))
	 nil))

(defvar do-whostates #+(or ti symbolics) t #-(or ti symbolics) nil)

#+(or TI symbolics allegro lucid)
(lisp:defun do-with-whostate (whostate fn)
  #+symbolics (declare (sys:downward-funarg fn))
  (if do-whostates
      (let ((oldstate (process-whostate (current-process))))
	(unwind-protect
	    (progn (setf (process-whostate (current-process)) whostate)
		   (who-line-process-change (current-process))
		   (funcall fn))
	  (setf (process-whostate (current-process)) oldstate)
	  (who-line-process-change (current-process))))
      (funcall fn)))
#+(or TI symbolics allegro lucid)
(defmacro with-whostate (whostate &body body)
  `(flet ((do-body () ,@body))
     (do-with-whostate ,whostate #'do-body)))
#-(or TI symbolics allegro lucid (and clisp mt))
(defmacro with-whostate (whostate &body body)
  (declare (ignore whostate))
  `(progn ,.body))

#+(and clisp mt)
(defmacro with-whostate (whostate &body body)
  `(let ((*thread-whostate* ,whostate)) ,.body))

; these hold the values that are put in the wholine
; (formerly needed due to incompatibilities with (or ti symbolics) strings)
(declaim (special compile-msg expand-msg))
(setq compile-msg "ap-compile")
(setq expand-msg "expand-s.t.")


;                                                         ----- %pointer
; used only to print out memo cells
#+symbolics
(import 'global::%pointer)
#+ti
(import 'sys::%pointer)
#+(or lucid allegro)
(declaim (inline %pointer))
#+allegro
(lisp:defun %pointer (x) (excl::pointer-to-address x))
#+lucid
(lisp:defun %pointer (x) (system:%pointer x))
#+aclpc
(lisp:defun %pointer (x) (acl::raw-address x))
#+clisp
(lisp:defun %pointer (x) (SYSTEM::ADDRESS-OF x))
#-(or symbolics ti lucid allegro aclpc clisp)
(lisp::defun %pointer (x) (declare (ignore x)) "???")

;                                                      ----- database access
;; This section protects against multiple processes trying to write the 
;  database at the same time.  Perhaps if I'd seen the documentation on 
;  locks I would have used them, but this actually seems to suit my purposes
;  better.
; There's a problem of how to handle non-local returns (e.g., aborting from 
; errors) when the database is locked.
; The current solution is
; - when the DB is known to be consistent, any escape simply aborts the 
;   transaction
; - when DB maybe inconsistent, an escape generates an error which explains the
;   dangers and describes how to override this protection or try to recover.

#-(or ti symbolics allegro lucid lispworks (and clisp mt))
(progn
 (defmacro withreadaccess (&body body) `(progn ,.body))
 ;;(defmacro withreadaccess-if-available (&body body) `(progn ,.body))
 (defmacro WithWriteAccess (&body body) `(progn ,.body))
 (defmacro writing (&body body) `(progn ,.body))
) 
#+(or ti symbolics allegro lucid lispworks)
(progn
 (defvar-resettable |WhoHasDataBaseWriteAccess | nil nil
  "the lock for writing into AP5's database")
 (defvar-resettable |IHaveReadAccess | nil nil
  "T in a process with read access (or waiting for it)")
 (defvar-resettable |Readers | 0 0
  "the number of processes with real access")
 (defvar-resettable |Writer | nil nil
  "the process writing or waiting to write; nil if none")
 (defvar have-it-count 0) ; *** statistic gathering
 (defvar need-it-count 0) ; *** statistic gathering
 ;; current measured cost for checking read access is 7 usec on 3600,
 ;; cost for getting it is another 100 usec on 3600
 (lisp:defun do-withreadaccess (fn)
  (declare #+symbolics (sys:downward-funarg fn)
           (type fixnum |Readers |) ;; should be plenty!
	   (optimize (speed 3) (safety 0)))
  ;; because TI's  2nd level error handler hides special binding
  ;; of |IHaveReadAccess |, WITHREADACCESS can allow control
  ;; to get here when it shouldn't.  
  ;; Under this implementation, where we only know the NUMBER of
  ;; readers, but not WHO they are, this can lead to deadlock on
  ;; a TI.
  (let (gotit)
    #+symbolics (incf need-it-count) ; *** statistic gathering
    (let ((|IHaveReadAccess | t))
      (flet ((grab ()  
		   (unless |Writer |
			   ; lucid seems to need these local declarations
			   (the fixnum (incf (the fixnum |Readers |)))
			   (setf gotit t))))
	    (unwind-protect
		(progn (unless #+(or lucid allegro lispworks)
			       (without-interrupts (grab))
			       #-(or lucid allegro lispworks) nil
			       ;; ALLEGRO and LUCID perform noticably better
                               ;; if the fn can succeed outside p-w !!
			       ; I'll assume lispworks is similar - DC
			       (process-wait "wait for read access" #'grab))
		       (funcall fn))
	      (without-interrupts
	       (when gotit (the fixnum (decf (the fixnum |Readers |))))))))))
 (defmacro withreadaccess (&body body)
  `(flet ((body () ,.body))
     (if |IHaveReadAccess | 
	 (progn #+symbolics (incf have-it-count) ; *** statistic gathering
		(funcall #'body))
	 (do-withreadaccess #'body))))
 (lisp:defun grab-readaccess-if-available ()
  (or |IHaveReadAccess |
      (without-interrupts
       (unless |Writer |
	       (incf (the fixnum |Readers |))))))
 (defmacro withreadaccess-if-available ;; not used
	  (&body body &aux (g (gensym)))
 `(let ((,g (grab-readaccess-if-available)))
    (when ,g
      (unwind-protect
	  (let ((|IHaveReadAccess | t))
	    ,.body)
	(without-interrupts (unless (eq ,g t)
			      (decf (the fixnum |Readers |))))))))
 #+(or ti lucid)
 (lisp:defun do-withwriteaccess (fn)
  (if (eq (current-process) |WhoHasDataBaseWriteAccess |)
      (funcall fn)
      (progn (when |IHaveReadAccess |
	       (error "trying to get write access when you already have read access~
             ~&(this can cause deadlock)"))
	     (#+ti ticl:with-lock
	      #+lucid lcl:with-process-lock
	      (|WhoHasDataBaseWriteAccess |
		#+lucid lcl::*current-process*
		#+ti :whostate
		#+lucid :wait-state "DB Write Lock")
	       (withreadaccess (funcall fn))))))
 #-(or ti lucid) ; lispworks, lucid, symbolics
 (lisp:defun do-withwriteaccess (fn &aux (p (current-process)) gotit)
  #+symbolics (declare (sys:downward-funarg fn))
  (unwind-protect
      (progn
	(unless (eq p |WhoHasDataBaseWriteAccess |)
	  (when |IHaveReadAccess |
	    (error "trying to get write access when you already have read access~
             ~&(this can cause deadlock)"))
	  (process-wait "DB Write Lock"
			;; the process wait fn is uninterruptible!!
			#'(lambda (p)
			    (unless |WhoHasDataBaseWriteAccess |
			      (setf |WhoHasDataBaseWriteAccess | p
				    gotit t)))
			p))
	(withreadaccess (funcall fn)))
    (without-interrupts
     (when gotit  (setf |WhoHasDataBaseWriteAccess | nil)))))
 (defmacro WithWriteAccess (&body body)
  `(do-withwriteaccess #'(lambda () ,.body)))
 (lisp:defun do-writer (fn)
  (declare #+symbolics (sys:downward-funarg fn))
  (when |Writer | (error "trying to become a writer when there's already a writer"))
  (unless (eq (current-process) |WhoHasDataBaseWriteAccess |)
    (error "trying to become a writer without writeaccess"))
  (unwind-protect
      (progn (setf |Writer | (current-process))
	     (process-wait "waiting to write"
			   #'(lambda ()
			       (declare #-ti (type (unsigned-byte 8) |Readers |))
			       (= (the fixnum |Readers |) 1)))
	     (funcall fn))
    (setf |Writer | nil)))
 (defmacro writing (&body body)
  `(do-writer #'(lambda () ,.body)))
)


#| donated by Vladimir Tzankov Sunday 2009/02/22
 - only one thread at a time can have write access 
 - any number can have read access at a time 
 - it is not permitted for one thread to have read access and another  
   to have write access at the same time.    

This is standard read/write lock. While they are part of recent POSIX 
standards - not all pthreads implementation have them. That's the reason 
they are absent.
  
It can be implemented via the mutex and exemptions that are available. 
Something like (barely tested and not refined): 
|#
#+(and clisp mt)
(progn
 (defstruct rwlock
   (lock (mt:make-mutex :name "rwlock-mutex"))
   (r-exemption (mt:make-exemption :name "reader-exemption"))
   (w-exemption (mt:make-exemption :name "writer-exemption"))
   (active-readers 0) ;; active readers
   (active-writer  nil) ;; is there write in progress
   (waiting-readers 0) ;; number of waiting readers
   (waiting-writers 0)) ;; number of waiting writers

 (defvar rw-lock (make-rwlock))

 (lisp:defun rwlock-read-lock (rwlock)
   (mt:with-mutex-lock ((rwlock-lock rwlock))
     (loop while (rwlock-active-writer rwlock) do ; write in progress
       ;; now supposed to be =
       ;; (mt:exemption-wait exemp lock :test (lambda nil (not (rwlock-active-writer rwlock)))
       (let (incremented)
         (unwind-protect
             ;; try to protect against interrupt and return while waiting
             ;; do we need (with-deferred-interrupts (setf incremented ...))?
             ;; *** Yes, to be safe in the general case, since we can't know
             ;; where interrupts may be allowed in the future.
             ;; A safe alternative: do withreadaccess around the timeout.
             ;; The inner withreadaccess's are then noops.
             (progn (setf incremented (incf (rwlock-waiting-readers rwlock)))
                    (mt:exemption-wait (rwlock-r-exemption rwlock)
                                       (rwlock-lock rwlock)))
           (when incremented (decf (rwlock-waiting-readers rwlock))))))
     (incf (rwlock-active-readers rwlock))))

 (lisp:defun rwlock-read-unlock (rwlock)
   (mt:with-mutex-lock ((rwlock-lock rwlock))
     (when (and (zerop (decf (rwlock-active-readers rwlock))) ;; no more readers
                (plusp (rwlock-waiting-writers rwlock))) ;; have waiting writers
       (mt:exemption-signal (rwlock-w-exemption rwlock)))))

 (lisp:defun rwlock-write-lock (rwlock)
   (mt:with-mutex-lock ((rwlock-lock rwlock))
     (loop while (or (rwlock-active-writer rwlock) (plusp (rwlock-active-readers rwlock))) do
       ;; write or reads in progress
       ;; see above
       (let (incremented)
         (unwind-protect
             (progn (incf (rwlock-waiting-writers rwlock))
                    (mt:exemption-wait (rwlock-w-exemption rwlock)
                                    (rwlock-lock rwlock)))
           (when incremented (decf (rwlock-waiting-writers rwlock))))))
     (setf (rwlock-active-writer rwlock) t)))

 (lisp:defun rwlock-write-unlock (rwlock)
   (mt:with-mutex-lock ((rwlock-lock rwlock))
     (setf (rwlock-active-writer rwlock) nil) ;; no more active writer
     (cond
       ((plusp (rwlock-waiting-writers rwlock))
        (mt:exemption-signal (rwlock-w-exemption rwlock)))
       ;; give priority to writers
       ((plusp (rwlock-waiting-readers rwlock))
        (mt:exemption-broadcast (rwlock-r-exemption rwlock))))))

 (defvar |WhoHasDataBaseWriteAccess | nil)
 (defvar |IHaveReadAccess | nil)

 ;; (withwriteaccess (withwriteaccess body)) = (withwriteaccess body)
 ;; (withreadaccess (withreadaccess body)) = (withreadaccess body)
 ;; (withwriteaccess (withreadaccess body)) = (withwriteaccess body)
 ;; (withreadaccess (withwriteaccess body)) = error

 (lisp:defun do-withwriteaccess (fn &aux (p (current-process)) gotit)
  (if (eq p |WhoHasDataBaseWriteAccess |) (funcall fn)
    (if |IHaveReadAccess |
        (error "trying to get write access when you already have read access -> deadlock")
      (unwind-protect
          (progn (setf gotit (rwlock-write-lock rw-lock))
                 (let ((|WhoHasDataBaseWriteAccess | p)
                       (|IHaveReadAccess | t))
                   (funcall fn)))
        (when gotit (rwlock-write-unlock rw-lock))))))
 (defmacro WithWriteAccess (&body body)
  `(do-withwriteaccess #'(lambda () ,.body)))

 ;; looks to me like this is a noop Wednesday 2009/02/25
 ;; but seems worth while to do the checking done by #+symbolics writing above
 ;; make sure there's no other writer, that you have write access, 
 ;; maybe that nobody else has read access ...
 #+ignore (defmacro writing (&body body) `(progn ,.body))
 (lisp:defun do-writer (fn)
  ;; Writer not yet defined here ...
  #+ignore (when |Writer | (error "trying to become a writer when there's already a writer"))
  (unless (eq (current-process) |WhoHasDataBaseWriteAccess |)
    (error "trying to become a writer without writeaccess"))
  (funcall fn)
  #+ignore 
  (unwind-protect
      (progn (setf |Writer | (current-process))
	     (funcall fn))
    (setf |Writer | nil)))
 (defmacro writing (&body body)
  `(do-writer #'(lambda () ,.body)))

 (lisp:defun do-withreadaccess (fn &aux gotit)
  (if |IHaveReadAccess | (funcall fn)
    (unwind-protect
        (progn (setf gotit (rwlock-read-lock rw-lock))
               (let ((|IHaveReadAccess | t)) (funcall fn)))
      (when gotit (rwlock-read-unlock rw-lock)))))
 (defmacro withreadaccess (&body body)
  `(do-withreadaccess #'(lambda () ,.body)))
)

; section 3. stuff that needs to be reimplemented



;                                                     ----- ignore-errors
; this is actually part of cltl2 but enough implementations don't have it
; that I put it in this section (also there's no portable implementation
; for those that don't)

; allegro, lispworks, clisp, aclpc have it

#+symbolics
(import 'global::ignore-errors)
#+ti
(defmacro ignore-errors (&rest body)
  `(ticl::ignore-errors ,.body))

#+ignore ; aclpc
(progn 
 (defmacro ignore-errors (&rest body)
  `(allegro::errorset 
     (let ((allegro::*error-hook* 'unwind-error))  ,.body) 
     (values nil t)))
 (lisp:defun unwind-error (&rest ignore) (declare (ignore ignore))
   (allegro::unwind-stack nil 'error nil)))
;; assume body returns only one value


#+lucid
(defmacro ignore-errors (&rest body)
  `(lcl:handler-case (values (progn ,.body) nil)
		 (error (c) (declare (ignore c))
			(values nil t))))


;                                                  ----- macroexpand-all
#|
The purpose of this is to find out what generators are used so that we
can compile into the compiled file the code to cache them.  For this
purpose it's really only required that the generator expressions (e.g.,
loop for s.t., any, ??, etc.) get macroexpanded.  If necessary you can
just implement this as a noop, in which case generators will not be
compiled to the file.
|#

; Only to be used for lambda expressions!
; This is defined in such a way to avoid the weirdnesses of both 
; TI and Symbolics
; Before you change it, try it on at least the following:
; (lambda (x) (push a x)) - on 3600 si:macroexpand-all returns #'(lambda ...)
; (lambda (push x) (push push x)) - on TI macroexpand-all tries to expand
;  arg list
(lisp:defun mexpand-all (x &optional env)
  #+(or lucid clisp lispworks) (declare (ignore env))
  (unless (eq 'lambda (car x))
    (error "mexpand-all being used on a non-lambda expression"))
  #+symbolics ; returns (function ...)
  (cadr (si:macroexpand-all x :environment env))
  #+ti
  (cadadr (si:macroexpand-all `(apply (function ,x) x) env))
  #+allegro ;; ditto  -- ALLEGRO also has excl::compiler-walk
            ;;        -- It expands COMPILER-MACROs as well as
            ;;        -- regular macros
     
  (cadr (clos::walk-form `(function ,x) env))
  #+lucid
  (first (LWALKER::WALK-FORM (list x)))
  #+clisp
  (EXT:EXPAND-FORM x) ;; exported as of 2.31
  #+ignore ;; previously
  (let (SYSTEM::*FENV* SYSTEM::*VENV*) (SYSTEM::%EXPAND-LAMBDA x))
  #+lispworks
  (first (WALKER::WALK-FORM (list x)))
  #+aclpc (allegro::macroexpand-all x env)
  #+ignore ; something like this might work on other implementations
  ;; seems to work for abcl
  (progn (ignore-errors (old-compile nil x))
	 x)
  #+abcl ;; 2009/04/15
  (system::MACROEXPAND-ALL x env)
)


;                                                     ----- load-memo
; Here's the preferred definition.  If you have load-time-value then
; you shouldn't need to implement memo.
; (Memo is currently defined for lucid, allegro and symbolics.)

#-(or ti symbolics lucid); (and lucid (not lcl4.1)) ;  allegro
(defmacro load-memo (exp) `(load-time-value ,exp))

#+ti
(defmacro load-memo (exp &optional (read-only-p t))
  `(cl::load-time-value ,exp ,read-only-p))

#+lucid ; (and lucid (not lcl4.1))
(defmacro load-memo (exp &optional (read-only-p t))
  (declare (ignore read-only-p))
  `(memo ,exp))

#+symbolics
(progn
 (defstruct (loadmemodata :named (:conc-name LM-)
			  (:print-function print-ptr-lm))
	    data form)
 
 (lisp:defun print-ptr-lm (x stream depth)
   (declare (ignore depth)) 
   (format stream "#<lm@~A>"
	   (%pointer x)))
 
 (defmacro load-memo (form &aux tspecs)
   (loop while (and (consp form) (eq (first form) 'the))
	 do (push (second form) tspecs) (setf form (third form)))
   (flet ((embed-in-tspec (expr)
			  (dolist (s tspecs expr)
				  (setf expr `(the ,s ,expr)))))
	 (embed-in-tspec
	  `(data-from ',(make-loadmemodata :form form :data (eval form))))))

 #+symbolics
 (progn  
  (lisp:defun data-from (cell) ;; only used by interpreted calls on load-memo
    (lm-data cell))
  (compiler:add-optimizer data-from data-from-op)
  
  (lisp:defun data-from-op
	      (whole &aux (cell (second whole)) (form (lm-form cell)))
     ;; QUOTE on the loadmemodata struct has disappeared by the time
      ;  control gets here!!
    (if (boundp 'compiler::*COMPILE-FUNCTION*)
	;; we can tell whether it is to core or a file
	(cond ((and (scl::send compiler::*COMPILE-FUNCTION* :for-file)
		    (not (scl::send compiler::*COMPILE-FUNCTION* :to-core-p)))
	       (list 'quote (cons COMPILER:EVAL-AT-LOAD-TIME-MARKER form)))
	      ;; behaves like #,
	      ((and (scl::send compiler::*COMPILE-FUNCTION* :to-core-p)
		    (not (scl::send compiler::*COMPILE-FUNCTION* :for-file)))
	       (list 'quote (lm-data cell)))
	      (t ; unexpected
	       `(memo ,form)))
	;unexpected
	`(memo ,form)))
  )
 
 #+ignore  ; #+allegro
 (lisp:defun data-from (cell)
   (if (loadmemodata-p cell)
       (lm-data cell)
       ;; from compiled code 
       cell))
)

;                                                          ----- memo
; see comment above on load-memo
; I'm going to try REAL hard not to do anything fancy.
; With any luck that will cure our GC/disksave problems.
#+lucid ; this is the most vanilla form I can think of ...
(defmacro memo (exp &aux (sym (gensym)))
  `(locally (declare (special ,sym))
     (if (boundp ',sym) ,sym (setf ,sym ,exp)))) 
;; *** when this is fixed to be a real LOAD-MEMO
; then DODBUPDATES-DELTA can be properly initialized.

#+ignore ; should no longer be needed #+ti
(progn
 (defmacro memo (form &aux tspecs)
  (loop while (and (consp form) (eq (first form) 'the))
	 do (push (second form) tspecs) (setf form (third form)))
  (flet ((embed-in-tspec (expr &aux tspecs)
	     (dolist (s tspecs expr)
		 (setf expr `(the ,s ,expr)))))
	(embed-in-tspec `(check-memo ',(gensym "MEMO") #'(lambda () ,form)))))

  ;; declaring/proclaiming CHECK-MEMO inline will gain
  ;; some time at the cost of about 4 words of code space.

 (lisp:defun check-memo (cell fn) 
  (cond
    ((boundp cell) (symbol-value cell))
    (t (set cell (funcall fn)))))
)

#+symbolics
(progn
 (defstruct (memodata :named (:conc-name nil)
		     (:print-function print-ptr))
	   data done)

 (lisp:defun print-ptr (x stream depth)
  (declare (ignore depth)) 
  (format stream "#<~Aap@~A>"
	  (if (done x) "!" "")
	  (%pointer x)))
)

#+symbolics
(defmacro-displace memo (exp)
  `(let ((cell ',(make-memodata)))
     (cond ((done cell) (data cell))
	   (t (setf (data cell) ,exp)
	      (setf (done cell) t)
	      (data cell)))))

#+ignore ;; #+allegro
(progn
 ;;; version that stores function in memo cell
 (defmacro memo (form &aux tspecs)
  (loop while (and (consp form) (eq (first form) 'the))
	 do (push (second form) tspecs) (setf form (third form)))
  (flet ((embed-in-tspec (expr &aux tspecs)
	     (dolist (s tspecs expr)
		 (setf expr `(the ,s ,expr)))))
	(embed-in-tspec
	 `(check-memo ',(make-memodata :done `(lambda () ,form)) ))))
 ;;; version that stores function in memo cell
 (lisp:defun check-memo (cell)
  (declare (type memodata cell))
  (cond ((done cell)
	 (prog1 (setf (data cell) (funcall (done cell)))
		(setf (done cell) nil)))
	(t (data cell))))
)
; Be careful about stuff like `(  ...  (memo expression) ..)
; probably ought to be `(  ...  (,'memo expression) ..)
; in order to not share memo cells among different generated lists


;                                       ----- defstruct-access-function-name
; Return the name (symbol) of the access function of a struct's slot.
;; Thursday 2006/02/16 - perhaps we can do this within common lisp ...
;; see only former use in stored-p.lsp
#+ignore 
(eval-when (:compile-toplevel :load-toplevel :execute)
 #+(or ti symbolics)
 (lisp:defun defstruct-access-function-name (struct slot)
  (si:defstruct-slot-description-ref-macro-name
       (cdr (assoc slot (si:DEFSTRUCT-DESCRIPTION-SLOT-ALIST
		      (si:GET-DEFSTRUCT-DESCRIPTION struct))))))
 
 #+allegro
 (lisp:defun defstruct-access-function-name
  (structname slotname &aux (dd (get structname 'EXCL::%STRUCTURE-DEFINITION)))
  (when dd
    #+allegro>=5-0
    (intern (format nil "~A~A" (or (EXCL::DD-CONC-NAME dd) "") slotname)
	    (symbol-package slotname))
    #-allegro>=5-0
    (dolist (s (excl::dd-slots dd))
	   (when (eq (excl::dsd-name s) slotname)
		 (return (excl::dsd-accessor s))))))

 #+lucid
 (lisp:defun defstruct-access-function-name (structname slotname)
   (dotimes (i  (sys:defstruct-info structname))
     (multiple-value-bind (name accessor default type)
	 (sys:defstruct-slot-info structname i)
       (declare (ignore default type))
       (when (eq name slotname)	 (return accessor)))))

 #+aclpc
 (lisp:defun defstruct-access-function-name (structname slotname)
   (dolist (thing (elt (getf (symbol-plist structname)  'acl::struct-info) 1))
       (when (eql (car thing) slotname)
                (return (cadr thing)))))

 #+clisp
 (progn
  (unless (fboundp 'old-ds-make-accessors)
	  (setf (symbol-function 'old-ds-make-accessors)
		(symbol-function 'system::ds-make-accessors)))
  #+ignore ;; maybe time to give up on versions < 1999
  (if (string< "19" (lisp-implementation-version) "1999-01-03")
      ;; new versions look more like "2.26.1..."
      ;; old version had 4 args 
      ;; gives warning - OLD-DS-MAKE-ACCESSORS called with 4 arguments...
      (lisp:defun new-ds-make-accessors (name type concname slotlist)
                  (cons `(setf (get ',name 'concname) ',concname)
                        (old-ds-make-accessors name type concname slotlist))) 
    
      ;; new version has 5 
      (lisp:defun new-ds-make-accessors (name names type concname slotlist) 
                  (cons `(setf (get ',name 'concname) ',concname) 
                        (old-ds-make-accessors
			 name names type concname slotlist))))
  (lisp:defun new-ds-make-accessors (name names type concname slotlist) 
	      (cons `(setf (get ',name 'concname) ',concname) 
		    (old-ds-make-accessors name names type concname slotlist)))
  (setf (symbol-function 'system::ds-make-accessors)
	(symbol-function 'new-ds-make-accessors))
  (lisp:defun defstruct-access-function-name (structname slotname)
      (intern (concatenate 'string (get structname 'concname)
			   (symbol-name slotname))
	      (symbol-package structname))))

 #+lispworks ;; I have no idea whether this will continue to work!
 (lisp:defun defstruct-access-function-name (structname slotname) 
   (let ((prefix
 	  (#-lispworks4 svref #+lispworks4 STRUCTURE:Z-SVREF
	      (get structname 'STRUCTURE::NEW-STRUCTURE-DEFINITION) 12)))
     (if (null prefix) (setf prefix "")
       (if (symbolp prefix) (setf prefix (symbol-name prefix))))
     (intern (concatenate 'string prefix (symbol-name slotname))
	     (symbol-package structname)))))

#+ignore ; Let's test that on every build ...
(eval-when (:compile-toplevel)
 (let (s)
  (defstruct (|Test-structure | (:conc-name "T-S-conc-")) qwerty uiop)
  (setf s (|MAKE-Test-structure | :qwerty 7))
  (unless (ignore-errors (= 7 (funcall (defstruct-access-function-name
					 '|Test-structure | 'qwerty)
				       s)))
	  (error "defstruct-access-function-name not working"))))
	  

; make sure that the condition stuff is defined

; the condition stuff
; assume it need not be imported in standard CL implementations
;;(UPDATE-PACKAGE "AP5") from update-lisp would do this and more!
#+(or lucid ti) ;  allegro
(import
  #+lucid
  '(lcl:define-condition lcl:make-condition lcl:handler-bind lcl:condition
    lcl:restart-case lcl:signal lcl:handler-bind lcl:invoke-restart
    lcl:with-simple-restart)
  #+ti
  '(cleh:define-condition cleh:make-condition cleh:handler-bind cleh:condition
    cleh:restart-case cleh:signal cleh:handler-bind cleh:invoke-restart
    cleh:with-simple-restart)
  (find-package "AP5"))

;; symbolics??

(eval-when (:compile-toplevel :load-toplevel :execute)
  (unless (fboundp 'with-simple-restart)
    (pushnew :no-conditions *features*)))

#+no-conditions
(progn ; define dummy versions for those that are needed
 (defmacro define-condition (&rest rest) (declare (ignore rest)) nil)
 (defmacro make-condition (type &rest rest) (declare (ignore rest)) type)
 (defmacro handler-bind (stuff &rest rest)
   (declare (ignore stuff))
   `(progn ,.rest))
 (defmacro restart-case (exp &rest stuff)
   (declare (ignore stuff)) exp)
 (lisp:defun signal (x) nil) ; never used if no conditions
 (lisp:defun invoke-restart (x) nil) ; never used if no conditions
 (defmacro with-simple-restart (junk &rest body) `(progn ,.body))
)


; with-simple-restart is in cltl2, but defined later just in case
;                                                --- with-unnamed-restart
; this could be moved to an independent file
(defmacro with-unnamed-restart ((format-string &rest format-args) &body b)
  `(with-simple-restart (nil ,format-string ,@format-args)
			      ,.b))
