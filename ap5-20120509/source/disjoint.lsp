;;;-*- Mode: LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-
;
; --------------- Disjointness Constraints ----------------
(in-package "AP5")

(Defun DisjointTrigger (type1 type2)
  `(E (x) (and (,type1 x) (,type2 x))))

(Defun DisjointTriggerP (trigger &aux type1 type2 w)
  (and (listp trigger) ; absurd to do (?? closed-wff trigger)
       (eq 'E (first trigger))
       (eq-length trigger 3) ; (e vars (and ...))
       (equal '(x) (second trigger))
       (eq-length (setq w (third trigger)) 3) ; (and (t1 x) (t2 x))
       (eq 'AND (first w))
       ;(not (consp
       (setq type1 (car (ilistp (second w))));))
       ;(not (consp
       (setq type2 (car (ilistp (third w))));))
       (equal trigger (disjointtrigger type1 type2))
       (list type1 type2)))

(atomic
  (++ codedrelname 'disjointTrigger
    '((type1 type2 trigger) s.t.
      (and trigger (equal (disjointtrigger type1 type2) trigger))))
  reveal
  (++ compare-relation (relationp 'disjointtrigger) 2 (relationp 'equal))
  (simplegenerator '(disjointtrigger type1 type2 output)
   '(let ((result (disjointtrigger type1 type2)))
      (and result (list result))))
  (SimpleMultipleGenerator
   '(disjointtrigger output output trigger)
   '(let ((result (disjointtriggerp trigger)))
     (and result (list result)))))

(++ RelSize (relationp 'disjointtrigger)
    '(input input output)
    1)
(++ RelSize (relationp 'disjointtrigger)
    '(output output input)
    1)


(++ TreeRelName 'disjointconstraint 1)
(++ subrel (dbo type disjointconstraint) (dbo type consistencyrule))
(++ relsize (dbo relation disjointconstraint) '(output) 100)

(++ no-trigger
    (canonicalize-trigger
      '((RULE)
	S.T.
	(AND (E (TRIGGER T1 T2)
		(AND (RULETRIGGER RULE TRIGGER)
		     (DISJOINTTRIGGER T1 T2 TRIGGER)))
	     (PREVIOUSLY (NOT (DISJOINTCONSTRAINT RULE)))
	     (START (CONSISTENCYRULE RULE))))))
; it should suffice to trigger on (start RULETRIGGER)

(++ wffdefn (relationp 'DisjointConstraint)
    '((rule) s.t.
      (and (consistencyrule rule)
	   (E (trigger t1 t2)
	      (and (ruletrigger rule trigger)
		   (disjointtrigger t1 t2 trigger))))))

(++ fullindexrelname 'idisjointtypes 2)
(deftypeconstraints idisjointtypes :none
  ((x) s.t. (or (type x) (description x)))
  ((x) s.t. (or (type x) (description x))))

(++ RelSize (relationp 'idisjointtypes) '(input output) 2)
(++ RelSize (relationp 'idisjointtypes) '(output input) 2)

(++ no-trigger
    (canonicalize-trigger
      '((TYPE1 TYPE2)
	S.T.
	(E (RULE TRIGGER)
	   (AND (OR (DISJOINTTRIGGER TYPE1 TYPE2 TRIGGER)
		    (DISJOINTTRIGGER TYPE2 TYPE1 TRIGGER))
		(PREVIOUSLY (NOT (IDISJOINTTYPES TYPE1 TYPE2)))
		(START (RULETRIGGER RULE TRIGGER))
		(DISJOINTCONSTRAINT RULE))))))
; it should be enough to trigger on (start DISJOINTCONSTRAINT)

(++ wffdefn (relationp 'idisjointtypes)
    '((type1 type2) s.t.
      (E (rule trigger)
	 (and (disjointconstraint rule)
	      (ruletrigger rule trigger)
	      (or (disjointtrigger type1 type2 trigger)
		  (disjointtrigger type2 type1 trigger))))))

(++ definedrelname 'disjointtypes
    '((type1 type2) s.t.
      (or (idisjointtypes type1 type2) ; in case of descriptions either way
	  (E (t1 t2)
	     (and (subrel type1 t1) (subrel type2 t2)
		  (idisjointtypes t1 t2))))))

(deftypeconstraints disjointtypes :none
   ((x) s.t. (or (type x) (description x)))
   ((x) s.t. (or (type x) (description x))))


(defvar disjointTypeEnforcement :none)

(++ RelAdder (relationp 'disjointtypes)
   '(lambda (ignore type1 type2) (declare (ignore ignore))
      (disjoint-adder type1 type2)))
(defun disjoint-adder (&rest ignore) (declare (ignore ignore))
  '(lambda (ignore type1 type2) (declare (ignore ignore))
     (cond ((?? disjointtypes type1 type2)
	    (Insist "supposed to add it" disjointtypes type1 type2))
	   (t (let (n1 n2 (*package* (find-package "AP5")) *print-pretty*)
		(setq n1 (if (listp type1) (pack* (format nil "~S" type1))
			     (relationnamep type1))
		      n2 (if (listp type2) (pack* (format nil "~S" type2))
			     (relationnamep type2)))
		(make-consistency
		  (pack* "Disjoint-Types" n1
			 (cond ((eq (symbol-package n1) (symbol-package n2)) "")
			       (t (concatenate 'string
					       (package-name (symbol-package n2))
					       ":")))
			 n2)
		  (disjointtrigger type1 type2)
		  'ignored
		  disjointTypeEnforcement))))))

(++ Reldeleter (relationp 'disjointtypes)
   '(lambda (ignore type1 type2) (declare (ignore ignore))
      (disjoint-deleter type1 type2)))
(defun disjoint-deleter (&rest ignore) (declare (ignore ignore))
   '(lambda (ignore t1 t2) (declare (ignore ignore))
       (insist "supposed to delete it" not (disjointtypes t1 t2))
       (loop for disjointconstraint#rule s.t.
	     (E (trigger)
		(and (ruletrigger rule trigger)
		     (or (disjointtrigger t1 t2 trigger)
			 (disjointtrigger t2 t1 trigger))))
	     do (-- rule rule))))

(defmacro defdisjoint (&optional enforcement &rest typenames)
  `(dodefdisjoint ',enforcement ,@(mapcar 'kwote typenames)))

(defun dodefdisjoint (&optional enforcement &rest typenames &aux
				      (disjointTypeEnforcement disjointTypeEnforcement))
  (if (?? enforcement enforcement) (setq disjointTypeEnforcement enforcement)
      (push enforcement typenames))
  (atomic (loop for l on typenames do
		(loop for m in (cdr l) do
		      (++ disjointtypes (or (relationp (car l)) (car l))
			  (or (relationp m) m))))))
  
;; define a few more types and follow CLtL, p.33

(++ codedrelname 'cons '((x) s.t. (consp x)))
(++ anycomparison (dbo type cons) 0)
(++ subtype (dbo type cons) (dbo type list))
(++ subtype (dbo type description) (dbo type cons))

(++ codedrelname 'array '((x) s.t. (arrayp x)))
(++ anycomparison (dbo type array) 0)
(++ codedrelname 'vector '((x) s.t. (vectorp x)))
(++ anycomparison (dbo type vector) 0)
(++ definedrelname 'sequence '((x) s.t. (or (vector x) (list x))))
(++ subtype (relationp 'vector) (relationp 'sequence))
(++ subtype (relationp 'list) (relationp 'sequence))
(++ subtype (relationp 'vector) (relationp 'array))
(++ subtype (dbo type string) (dbo type vector))
(when (arrayp rel-adder) (++ subtype (dbo type dbobject) (dbo type array)))

(defdisjoint :none number list-or-symbol array character)
(defdisjoint :none string dbobject)
(defdisjoint :none symbol cons)
(unless (arrayp rel-adder) (defdisjoint :none dbobject array))
;(loop for (x y) s.t. (disjointtypes x y) count t) = 14070
;(loop for (x y) s.t. (idisjointtypes x y) count t) = 16
