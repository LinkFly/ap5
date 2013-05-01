;;; -*- Package: (ap5 lisp); Mode:LISP; Base:10.; Syntax:Common-Lisp -*-

(in-package "AP5")

;; see README for instructions on compiling and loading ap5
#+ignore ;aclpc
(defparameter source-default-drive "e")
#+ignore ;aclpc
(defparameter bin-default-drive "e")
    
;; changed these to defvar so that you can assign to them BEFORE you
;; load this file (in the build script) and have uses of them later
;; in this file refer to the value you assigned (rather than having
;; to change the file)
(defvar source-default-path
    #+(or windows mswindows) "g:\\ap5\\source\\foo.lsp"
  ; Dennis "\\langs\\ap5\\source\\foo.lsp"
  #+unix "/home/ap5/source/foo.lsp")

(defvar bin-default-path
  #+aclpc "g:\\ap5\\bin\\aclpc\\foo.fsl"
  #+(and allegro mswindows)
     (format nil "g:\\ap5\\bin\\nt-acl~a\\foo.fsl"
	     (subseq (lisp-implementation-version) 0 3))
  ; Dennis "\\langs\\ap5\\bin\\foo.fsl"
  #+(and lucid pa) "/home/ap5/bin/hp-lucid/foo.hbin"
  #+(and lucid sparc) "/home/ap5/bin/sparc-lucid/foo.sbin"
  #+(and allegro-v4.3 hpprism) "/home/ap5/bin/hp-acl4.3/foo.fasl"
  #+(and allegro-v4.2 hpprism) "/home/ap5/bin/hp-acl4.2/foo.fasl"
  #+(and allegro sparc) "/home/ap5/bin/sparc-acl/foo.fasl"
  #+(and lispworks hpux) "/home/ap5/bin/hp-lispworks/foo.pfasl"
  #+clisp "/home/ap5/bin/clisp/foo.fas")


#+ignore
(defun source (name &optional (default source-default-path))
  (let ((merged (merge-pathnames (subseq name 0 (min (length name) 8)) default)))
    #+aclpc (make-pathname :defaults merged :device source-default-drive)
    #-aclpc merged))

(defun source (name &optional (default source-default-path))
  (merge-pathnames (subseq name 0 (min (length name) 8)) default))

#+ignore
(defun bin (name &optional (default bin-default-path))
  (let ((merged (merge-pathnames (subseq name 0 (min (length name) 8)) default)))
    #+aclpc (make-pathname :defaults merged :device bin-default-drive)
    #-aclpc merged))

(defun bin (name &optional (default bin-default-path))
  (merge-pathnames (subseq name 0 (min (length name) 8)) default))

#+ignore ; switch to merge-pathnames
(; no longer used - assume everything available from local file system
 ; uses are in old versions of functions source and bin
 (defparameter ap5-source-host "hpai23")
 (defparameter ap5-bin-host ap5-source-host)
 
 (defparameter ap5-source-directory 
  #+aclpc '(:ABSOLUTE "langs" "ap5" "source")
  #-aclpc '(:ABSOLUTE "home" "ap5" "source"))

 (setf ap5-source-directory (cons :root (cdr ap5-source-directory)))

 (defparameter ap5-bin-directory
  #+aclpc '(:ABSOLUTE "langs" "ap5" "bin")
  #-aclpc
  '(:ABSOLUTE "home" "ap5" "bin"
	      #+(and allegro hpux) "hp-acl"
	      #+(and allegro sparc) "sparc-acl"
	      #+(and lispworks hpux) "hp-lispworks"
	      #+(and lucid pa) "hp-lucid"
	      #+(and lucid sparc) "sparc-lucid"
	      #+clisp "clisp"))

 #+lucid
 (setf ap5-bin-directory (cons :root (cdr ap5-bin-directory)))

 (defun source (file &optional (directory ap5-source-directory))
  ; make short (DOS) file names the standard to avoid need to convert
  (namestring
   (make-pathname
    :name
    #+(and clisp dos) (string-upcase (subseq file 0 (min (length file) 8)))
    #-(and clisp dos) (subseq file 0 (min (length file) 8))
    :type
    #+(and clisp dos) "LSP"
    #-(and clisp dos) "lsp"
    :directory directory
    :version :newest)))

 (defun bin (file &optional (directory ap5-bin-directory))
   ; short filenames now standard
   (namestring
    (make-pathname
     :directory directory
     :name
     #+(and clisp dos) (string-upcase (subseq file 0 (min (length file) 8)))
     #-(and clisp dos) (subseq file 0 (min (length file) 8))
     :type *bin-type*
     :version :newest))))

(defvar *bin-type*
   #+(and clisp dos) "FAS"
   #+(and clisp (not dos)) "fas"
   #+aclpc "fsl"
   #+symbolics "bin"
   #+TI "xld"
   #+lispworks COMPILER:*FASL-EXTENSION-STRING*
   #+allegro excl:*fasl-default-type*
   #+lucid (first lucid::*load-binary-pathname-types*))

#|
------------------------------------------------------------------------
Inadequacies of the current ap5 system file,
possible fixes using the current make-system mechanism:

In ap5 many  files  depend  on   themselves  -  which   appears  to be
disallowed by make-system.   Perhaps we can define a load-compile-load
transformation  which loads the source, then compiles the source, then
loads  the  binary?   Even  then  we  have  to  be   careful,    since
bootstrapping files cannot be reloaded arbitrarily.   One has to start
over from  relations.   [Perhaps we can make it easier for other files
that use ap5 to be reloaded.   Certainly  this will be made  easier by
equivalence and a lot of optional- replacing constraints.]

There are   transformations   in  building  ap5 that  depend  on other
operations   NOT  having  been  done,  e.g.,   the  file   that   sets
bootstrapping to nil must not be loaded before the bootstrapping files
are compiled.  More precisely, if you remake the system, then the file
that sets  bootstrapping  to T must be  loaded  before  compiling  the
bootstrapping   files,  even if its most  recent  version  is  already
loaded.   Types must be compiled with types loaded more recently  than
subtypes.

Here's a program for  compiling  the entire  system: In general,  if a
file is to be  compiled  at a time  when its  binary  is as new as its
source, and all files before it have not had to be recompiled, then it
need not be recompiled.  Load-compile-or-load means that if this file has
to  be    recompiled    then  it   should   be    loadfile'd    first.
------------------------------------------------------------------------
|#

(defvar info nil)
(defvar ask nil)
(defvar recompile nil)
(defvar nevercompile nil)
(defvar *changed* nil)
(defvar startfile nil)
(defvar stopfile t)
(defvar *start-time* 0)

(defun ask (&rest args)
  (or (not ask) (apply #'format *query-io* args) (y-or-n-p)))

(defun print-current-time (&optional (stream *standard-output*))
   (multiple-value-bind
    (second minute hour day month year)
    (get-decoded-time)
    (format stream "~@?" "~d/~d/~d ~2,'0d:~2,'0d:~2,'0d"
	    month day year hour minute second)))

(defun show-time ()
  (fresh-line t)
  (print-current-time t)
  (multiple-value-bind (hr remainder)
      (truncate (- (get-universal-time) *start-time*) #.(* 60 60))
    (multiple-value-bind (min sec)
      (truncate remainder 60)
      (format t "  ~d:~2,'0d:~2,'0d elapsed" hr min sec))))

(defun current-version-loaded? (file &aux f1 f2)
  #+(or) ; rel.7 symbolics no longer works (how to do it?) - neither does ti
  (and (setf f1 (probe-file  file)
	     f2 (caadar (global:send file :get :file-id-package-alist)))
       (eq (global:send f1 :version)
	   (global:send f2 :version)))
  nil)

(defun fasload* (filename &optional reload &aux file)
  (setf file (bin filename))
  (cond ((and (not reload) (current-version-loaded? file))
	 (format t "~%already loaded ~A" file) t)
	((and info (progn (format t "~%load ~A" file) t)))
	((ask "~%load ~A.bin ? " filename)
	 (format t "~%  Loading ~a " file)
	 (time (load file)) (show-time) t)))
; returns non nil if loaded

(defun loadfile (filename &optional reload &aux file)
  (when (and (start? filename) (notstop? filename))
    (setf file (source filename))
    (cond ((and (not reload) (current-version-loaded? file))
	   (format t "~%already loaded ~A" file) t)
	  ((and info (progn (format t "~%load ~A" file) t)))
	  ((ask "~%load ~A.lisp ? " filename)
	   (format t "~%  Loading ~a " file)
	   (load file) (show-time) t))))
; returns non nil if loaded

; name changed cause of previously existing fn
(defun compile-file* (file &optional reload)
  (loadfile file reload)
  (format t "~%Compiling ~A" (source file))
  (cond (info)
	((ask " ? ")
	 (compile-file (source file) :output-file (bin file))
	 (show-time) t)))
; returns non nil if compiled

(defun compile-if-needed-then-load (file)
  (when (source-newer-than-bin file)
    (compile-file (source file) :output-file (bin file))
    (show-time))
  (when (start? file) (load (bin file))))

(defun source-newer-than-bin (file &optional 
				   (sourcedir source-default-path)
				   (bindir bin-default-path))
  (or (not (probe-file (bin file bindir)))
      (> (or (file-write-date (source file sourcedir)) 0)
	 (file-write-date (bin file bindir)))))

(defun compile? (file)
  (cond (nevercompile nil)
	(recompile (setf *changed* t))
	((source-newer-than-bin file)
	 (setf recompile t *changed* t))))

(defun start? (file)
  (cond ((string-equal file startfile) (setf startfile nil)))
  (null startfile))

(defun notstop? (file)
  (cond ((string-equal file stopfile)
	 (format t "~&stopping before file ~a~%" file)
	 (setf stopfile nil)))
  stopfile)

(defun compile-load (file &optional reload)
  (when (and (start? file) (notstop? file))
    (format t "~2%Compile load file: ~a" file)
    (when (compile? file) (compile-file* file))
    (fasload* file reload)))

(defun load-compile-or-load (file)
  (when (and (start? file) (notstop? file))
    (format t "~2%Load-Compile or Load file: ~a" file)
    (cond ((and (compile? file) (compile-file* file t)))
	  ; if user says not to then maybe fasload
	  (t (fasload* file t)))))

; This compiles whatever might need to be compiled.
; It doesn't necessarily end up with the compiled versions loaded, but it does
; leave the entire system loaded - like make-system if no recompilation needed. 
; Recompile means recompile everything - otherwise it tries to be smart.
; If info is t, this doesn't actually do anything but prints out what it thinks
; has to be done.  Ask means ask the user before actually doing anything.
; break-at-end means to break before throwing out global history
; startfile means don't do anything until you get to that file
;
(defun compile-ap5 (&key recompile nevercompile info ask
			 (break-at-end #+symbolics t) startfile (stopfile t)
			 &aux *changed* (*start-time* (get-universal-time))
			 #+(or symbolics ti) (global:inhibit-fdefine-warnings t))
; (compile-load "sys-depend")
  (declare (special  generator-cost-record record-expensive-and-costs))
  (let #+allegrox((efpo (sys:gsgc-parameter :expansion-free-percent-old))
		 (gcprint (sys:gsgc-switch :print))
		 (gcstats (sys:gsgc-switch :stats)))
       #-allegrox ()
    (unwind-protect
      (progn
	#+allegrox
	(setf (sys:gsgc-switch :print) t
	      (sys:gsgc-switch :stats) t
	      ;(sys:gsgc-parameter :free-bytes-new-other) 2000000
	      ;(sys:gsgc-parameter :expansion-free-percent-new) 80
	      (sys:gsgc-parameter :expansion-free-percent-old) 95
	      )
	(macrolet ((** (fn &rest files) `(mapc #',fn ',(copy-list files))))
		   (** loadfile "ap5pkg" "declare")
		   (** compile-load
                       #+ignore compile-if-needed-then-load
                       "ansi-loop" "sys-depend")
		   (** compile-load
			 "tryfail" "utilities" "wffs" "wffmacros" "treegen"
			 "generators" "implementat" "transactions" "triggers"
			 "macros" #+symbolics "sys-depend2")
		   (** load-compile-or-load
		       "relations" "types" "rulerels" "ruledeclare")
		   (when *changed*  ; these have to be loaded compiled before we turn off bootstrapping
			 (** (lambda (file) (fasload* file t))
			     "relations" "types" "rulerels" "ruledeclare"))
				;#+ti (compile 'cxvaluefn '(lambda (ignore) nil)) ; ***
		      
		   (loadfile "final-boot" t)
		   (load-compile-or-load "maint-rels")
		   (** load-compile-or-load
		       "full-index" "typeconstra" "subtyperules" "countspecs" "disjoint")
		   (** compile-load "defrel" "derivation")
		   (** load-compile-or-load "stored-place" "idiom-rules")
		   (compile-load "tools")
		   #+symbolics (compile-load "more-zmacs")
		   #+ti (compile-load "more-zmacs-ti")
		   #+symbolics (compile-load "more-listen")
		   (load-compile-or-load "misc-rules")
		   (** compile-load #+(or allegro lucid aclpc) "closclas"
		       ;; closclas relies on MOP interfaces somewhat
		       ;; these should be checked out for each platform
		       #-(or allegro lucid aclpc) "ccstub"
		       ;; CCSTUB just defines one relation that is READ
		       ;; by the expander of the macro CREATE 
		       ;; (found in "ap5-macro-extensions")
		       "slot-place"
		       "ap5-macro-extensions"
		       "partial-order" #+lucid "task-triggers")
		   (loadfile "doc")
		   (pushnew :ap5 *features*))
	 (provide "ap5")
	 (and break-at-end (cerror "resume when ready" "ready to throw out history"))
	 (setf generator-cost-record nil record-expensive-and-costs nil)
	 (when (fboundp 'reset-history) (reset-history))
	 (when (fboundp 'history-label) (history-label 'beginning)))
      #+allegrox (setf (sys:gsgc-switch :print) gcprint
		      (sys:gsgc-switch :stats) gcstats
	      ;(sys:gsgc-parameter :expansion-free-percent-old) efpo
		      ))))


(defvar *patchdate* nil
  "A universal time.  Time of last call to LOADPATCHES")


(defun load-ap5 (&rest keys)
  (setf *patchdate* #+ignore (get-universal-time)
	(file-write-date (bin "partial-order")))
  (apply #'compile-ap5 :break-at-end nil :nevercompile t keys)
  ;; (loadpatches)
  #+allegro(excl:gc t)
  #+lucid (lcl:gc)
  #+aclpc (acl:gc -1))

;; nonobvious dependencies: 
; system-dependent uses typep dbobject - defined in utilities


#+ignore 
(defparameter *sourcefiles*
      '("compile-sys" "sys-depend" "memodump"
	"ap5pkg" "declare" "tryfail" "utilities" "wffs" "wffmacros"
	"generators" "implementat" "transactions" "triggers" "macros" "sys-depend2"
	"relations" "types" "rulerels" "ruledeclare"
	"final-boot" "maint-rels"
	"full-index" "typeconstra" "subtyperules" "countspecs" "disjoint"
	"defrel" "derivation" "stored-place"
	"idiom-rules" "tools" "more-zmacs" "more-zmacs-ti" "more-listen"
	"misc-rules" "ap5-macro-extensions" "slot-place" "partial-order" "doc"
	"ap5sys" "read_me"))


;;  functionality for patching AP5 images
#-(or ti symbolics)
(defvar ap5-patch-directory)

#+ignore
(defparameter ap5-patch-directory
  (make-pathname :defaults source-default-path
    :directory (append (butlast (pathname-directory  source-default-path))
		       '("patches" "ap599"))))

#-(or ti symbolics)
(defun loadpatches ()
  "Loads every patch file which has a writedate later than
*patchdate*.  Compiles a patch file if the binary is out of
date.  This implies that old patch files which are modified
can be reloaded out of order."
  (flet ((fullbin (file)
            ))
    (let ((files
	 (sort (directory (make-pathname
			    :defaults ap5-patch-directory
			    :name :wild
			    :type "lisp"
			    :version :newest))
	       #'<
	       :key #'file-write-date)))
    (dolist (file files)
	 (let ((patchdate (file-write-date file)) ;; source date
	       b)
	   (when (> patchdate *patchdate*)
	     (let ((*package* (find-package "AP5"))
		   #+ti (si:inhibit-fdefine-warnings t)
		   #+lucid (lcl:*redefinition-action* nil))
	       ; in case someone forgets (in-package "AP5") in a patch file
	       (setf b (make-pathname
			 :defaults ap5-patch-directory
			 :name (pathname-name file)
			 :type *bin-type*
			 :version :newest))
	       (when (or (not (probe-file b))
			 (> patchdate (file-write-date b)))
		 (format t "~&~A ~A." "Compiling patch" file)
		 (compile-file file :output-file b))
	       (format t "~&~A ~A." "Loading patch" b)
	       (load b))
	     (setf *patchdate* patchdate)))))))

#+allegro-v4.2
(let ((tail (member :READ-INIT-FILE excl:*restart-actions* :key #'car)))
    
    (setf excl:*restart-actions* `(,@ (ldiff excl:*restart-actions* tail)
   				   (:eval . (loadpatches))
				   ,.tail)))

#+allegro-v4.2
(push 'loadpatches  excl:*restart-actions*)
