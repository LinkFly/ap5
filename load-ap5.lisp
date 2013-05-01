(in-package :ap5)

(eval-when (:compile-toplevel :load-toplevel :execute)

(defparameter *system-dir* (asdf:component-pathname (asdf:find-system :ap5)))
(defparameter *source-dir* (asdf:component-pathname (asdf:find-component (asdf:find-system :ap5) '(:source))))
(defun full-path (dir) (merge-pathnames dir *system-dir*))

(setf source-default-path *source-dir*)
(setf bin-default-path (full-path #+lispworks6.1 "compiled/lw61-fasl/"
                                  #-lispworks6.1 (concatenate 'string "compiled/" (lisp-implementation-type) " - " (lisp-implementation-version) "/"))) 

(ensure-directories-exist bin-default-path)

  (defun load-ap5 (&rest keys &key (nevercompile t) &allow-other-keys)
    (setf *patchdate* #+ignore (get-universal-time)
          (file-write-date (bin "partial-order")))
    (apply #'compile-ap5 :break-at-end nil :nevercompile nevercompile keys)
    ;; (loadpatches)
    #+allegro(excl:gc t)
    #+lucid (lcl:gc)
    #+aclpc (acl:gc -1))
  (load-ap5 :nevercompile nil)
)
