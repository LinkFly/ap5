#|
Date: Sun, 15 Jun 2008 15:02:45 -0400 
From: Sam Steingold <sds@gnu.org> 
Subject: Re: ap5 build script 

I found this script easier to use than your 2: 
save it in clisp-build.lisp and run like this: 
$ clisp clisp-build.lisp recompile 
$ clisp clisp-build.lisp savemem 
$ ./bin-2.45/ap5 
|#
(format t "ext:*args* = ~a" ext:*args*)

(in-package :cl-user) 
(defpackage "AP5" (:use "CL") (:nicknames "ap5")) 
(in-package :ap5) 
(defparameter *top*
  (or (cadr (member "top" ext:*args* :test 'string=))
      (error "need ap5 directory location")))
(defparameter *liv*
  (let ((liv (lisp-implementation-version))) 
    (or (cadr (member "liv" ext:*args* :test 'string=))
	(subseq liv 0 (position #\Space liv)))))
(defparameter *bin* 
  (make-pathname 
   :directory (append (pathname-directory *top*) 
		      (list (concatenate 'string "bin-" *liv* #+mt "-MT")))
   :defaults *top*))
(load (merge-pathnames "source/compile-.lsp" *top*)) 
(setf source-default-path (merge-pathnames "source/foo.lsp" *top*) 
       bin-default-path (merge-pathnames "foo.fas" *bin*)) 
(ensure-directories-exist bin-default-path :verbose t) 

(defun recompile()(compile-ap5 :recompile t))
(defun load-save()
  (load-ap5) 
  (ext:saveinitmem (format nil "/tmp/ap5-~a~a" *liv* #+mt "MT" #-mt "")
		   :executable t :norc t :documentation "AP5"))
#+ignore 
(ext:fcase equal ext:*args* 
   ((("recompile")) (compile-ap5 :recompile t)) 
   ((("savemem")) (load-ap5) 
    (ext:saveinitmem (merge-pathnames "ap5" *bin*) :executable t :norc t 
        :documentation "AP5")) 
   ((NIL) (format t "usage: ~S [recompile|load]~%" *load-truename*)) 
   (t (error "invalid arguments: ~S" ext:*args*))) 
