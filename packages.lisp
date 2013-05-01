(defpackage :ap5
  (:use :cl)
  (:import-from :lispworks #:without-preemption)
  )
(eq (find-package :ap5) (find-package "AP5"))
(describe (find-symbol "DEFUN" "AP5"))
(describe (find-symbol "DEFUN" :ap5))