(asdf:defsystem :ap5
  :depends-on ()
  :serial t
  :components ((:file "features")
               (:file "packages")
               (:file "compile-.lsp")
               (:module "source"
                        :pathname "ap5-20120509/source"
                        :components ();((:cl-source-file.lsp "compile-")
                        )                                     
               (:file "load-ap5" :depends-on ("compile-.lsp" "source"))))