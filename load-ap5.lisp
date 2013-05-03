(in-package :ap5)

(eval-when (:compile-toplevel :load-toplevel :execute)
(defparameter *system-dir* (asdf:component-pathname (asdf:find-system :ap5)))
(defun full-path (dir) (merge-pathnames dir *system-dir*))

;;; Configure parameters ;;;
(defparameter *not-compiling* nil)
(defparameter *compiled-pathname* nil)
(defparameter *rel-path-to-source* '("ap5-20120509" "source"))
;; Change parameters ;;
(when (probe-file (full-path "config.lisp"))
  (load (full-path "config.lisp")))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *source-dir* (asdf:component-pathname (asdf:find-component (asdf:find-system :ap5) *rel-path-to-source*)))

(setf source-default-path *source-dir*)
(setf bin-default-path (or *compiled-pathname* 
                           (full-path #+lispworks6.1 "compiled/lw61-fasl/"
                                      #-lispworks6.1 (concatenate 'string 
                                                                  "compiled/"
                                                                  (lisp-implementation-type)
                                                                  " - "
                                                                  (lisp-implementation-version)
                                                                  "/")))) 

(ensure-directories-exist bin-default-path)

)

(load-ap5 :nevercompile *not-compiling*)
