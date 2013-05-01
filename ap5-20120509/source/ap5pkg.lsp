;;; -*- Package: user; Mode:LISP; Base:10.; Syntax:Common-Lisp -*-

(in-package "AP5")

; let's get this part over with quick ...
(defvar *shadowed-lisp-symbols*
  '(compile	; I really want everyone to use mine instead of CL's
    defun	; but it's not considered polite to change symbols
    loop	; in the lisp package
    defmethod  

    ++		; used as update macro in ap5, top level var in CL
    variable	; name of a record in ap5, documentation type in lisp
    abort 	; aborts transaction in ap5, condition system in CL
    structure	; names an ap5 function (a stored-place implementation)
	        ; but a type in ansi common lisp
    array 	; ditto
    ;; eval-when	; see just below
    ;; gentemp ;; Tuesday 2010/10/26 - nope
    ;; Rene De Visser reports that in LW these are in CL package
    #+lispworks4 true
    #+lispworks4 without-interrupts
    ))
; Packages that use ap5 will probably want to shadowing-import these.
; I won't export them here.

(eval-when (:compile-toplevel :load-toplevel :execute)
 (shadow *shadowed-lisp-symbols* (find-package "AP5")))

;; (lisp::defun gentemp(&optional x y)(gensym x)) ;; Tuesday 2010/10/26 - nope
;; (macroexpand-1 '(Defun make-automation ...)) =>
;; (progn (DEFUN GEN1282 ...) (SETF (SYMBOL-FUNCTION NEWFN) (SYMBOL-FUNCTION 'GEN1282)) ...)

#|
;; no need for backward compatibility at this late date
 (defvar eval-when-alist
  ; sick of those warnings from allegro
  ; then why not fix your source code?
  #+allegro '((:compile-toplevel :compile-toplevel)
	      (:load-toplevel :load-toplevel)
	      (:execute :execute)
	      (lisp:compile :compile-toplevel)
	      (compile :compile-toplevel)
	      (load :load-toplevel)
	      (eval :execute))
  ; that's what I get for wanting to redefine compile ...
  #-allegro '((compile lisp::compile)(lisp:compile lisp:compile) (load load) (eval eval)))

 (defmacro eval-when (situations &rest rest)
  `(lisp::eval-when
    ,(mapcar #'(lambda (s)
		 (or (cadr (assoc s eval-when-alist))
		     (error "bad situation") ;; YOU DON'T EVEN ACCEPT THE CORRECT WORDS?
		     ))
	     situations)
    ,.rest))
|#

(eval-when (:compile-toplevel :load-toplevel :execute)
  #-(or abcl clos pcl) (error "can't find clos or pcl!")
  (unless (find-symbol "DEFCLASS")
      (use-package (list #+clos (find-package "CLOS")
			 #+pcl (find-package "PCL"))
		   (find-package "AP5"))))

(export ; first those in the manual
 '(* *GLOBALCX* + -- +- ?? *no-single-value-stored* A #+ignore ABORT ;; ++
     ABORT-TRANSACTION ABORTDATA *ABORT-CONDITION* TRIGGER
     ALIST ALIST-SINGLE ALL ALL-RELS ALL-TYPES-OF
     ALWAYSREQUIRE ALWAYSREQUIRED AND ANON-REL ANY ANY-FOR
     ANY<=FOR ANYCOMPARISON APTYPECASE #+ignore ARRAY
     ARRAY-SINGLE ATOMIC ATTEMPT AUTOMATION
     AUTOMATIONGENERATOR AUTOMATIONRULE
     AFTER-ATOMIC-ABORT AFTER-ATOMIC-NORMAL
     BASE BASETYPE BLOCK-UNDO
     BASETYPENAME CACHE-GENERATORS
     CANONICALIZE-TRIGGER CANONICALIZER CARDINALITY
     CARDINALITY-FOR-TUPLE CARDINALITY-OF-PATTERN
     CHANGE CHECKER CLASSIFICATION CODED COMPARE-RELATION
     COMPILE-STARTS
     CONSISTENCYCHECKER CONSISTENCYRULE CONSTANT
     CONSTRAINT-ENFORCEMENT-LEVEL DBO DBOBJECT
     DEACTIVATE-MATCHNODE DEACTIVATE-RULE DECACHE-REL
     ACTIVE-RULE-P
     DECACHE-REL-KEYWORD-FN DECLARE-TYPE
     DEFAULT-EQUIVALENCE DEFAUTOMATION DEFAUTOMATIONGENERATOR
     DEFCONSISTENCYCHECKER DEFCOMPUTATION
     DEFDERIVATION DEFDISJOINT DEFINED DEFRELATION
     DEFREPRESENTATION DEFTYPECONSTRAINTS DEFUN-TYPED
     DERIVED DESCRIBEREL DESCRIBE-ALGORITHM
     DESCRIBERULE DISJOINTTYPES DOC DONT-TELL-ME-ABOUT
     E EFFORT ENQUEUE-AUTOMATION EQL EQUIV
     EQUIVALENCE-RELATION EXISTS EXPANDDESCRIPTION EXTREME
     FALSE FORANY FORTHEONLY FULL-INDEX
     GENERATE GENERATOR
     GENERATOR-CACHE GLOBALVAR GLOBALVAR-SINGLE
     HASHTABLE HASHTABLE-SINGLE HISTORY HISTORY-LABEL
     IDISJOINTTYPES IFABORT IFNORMAL IF-THEN-ELSE IGNORE IGNORE-VARS
     IMPLEMENTATION IMPLIES INATOMIC INCONSISTENCY-REPORTER
     INDIVIDUAL INDIVIDUAL-DERIVED
     INITIALSTATE INLINE INLINEREL INSIST
     INTRANSACTION ISUBREL LET-TYPED LISP-FUNCTION
     LISP-PREDICATE
     LISP-PREDICATE-EQUIVALENCE-RELATION LISTOF
     MAINTAINEDREL MAINTAINRULE MAKE-DBOBJECT
     MAP-UPDATES MATCHNODES-< MATCHNODES->
     *MAX-HISTORY-LENGTH*
     MEMBER MEMBER-= MEMBER-equal MEMBER-eql
     MEMBER-STRING-EQUAL MEMBER-STRING=
     MEMO
     MNODETRIGGERS MOST-SPECIFIC-TYPES-OF MULTIPLE-FOR
     MULTIPLE-TRIGGER MULTIPLE-TRIGGER-INVERSE
     MULTIPLE<=FOR NAMES-NOT-ALLOWED-FOR-RELATIONS NEQUIV
     NEVERPERMIT NEVERPERMITTED NO-TRIGGER
     NONTRIGGERABLE NOT NOT-ALLOWED-TO-UPDATE NOTINLINE OPTIONAL-FOR
     OPTIONAL-TRIGGER OPTIONAL-TRIGGER-INVERSE
     OPTIONAL<=FOR OR OUTPUT PARAMETER-LIST POSSIBLETOADD
     POSSIBLETODELETE POSSIBLETOUPDATE  PREVIOUSLY  PRINTER
     PROG-TYPED PROHIBITED PROPER-NAME RBOUNDP REACTIVATE-RULE
     READER RELADDER RELATION RELATION-IN-DEFN
     RELATION-IN-DEFN* RELATIONARITY RELATIONIMPLEMENTATION
     RELATIONNAME RELATIONP RELATIONSIZE RELDELETER RELGENERATOR
     RELCALL RELAPPLY
     RELSIZE RELTESTER RELUPDATER RESTRICT-ATTRIBUTE-CARDINALITY
     RESTRICT-CARDINALITY RETURNING REVEAL RMAKUNBOUND RULECODE
     RULENAME RULES-SENSITIVE-TO RULETRIGGER
     SET-LISTOF SET-LISTOF&REST SET-SOLE-SATISFIERS SHOWDELTA SIMPLEGENERATOR
     SIMPLEMULTIPLEGENERATOR START STORED-IN-PLACE
     STORED-IN-PLACE-SINGLE STORED-WHERE STRUCTPROP
     #+ignore STRUCTURE STRUCTURE-SINGLE
     SUBREL SUBRELTRIGGER SUBTYPE SUM SYMBOL-RELATION SYMBOLPROP
     SYMBOLPROP-SINGLE TCLOSURE TELL-ME-ABOUT TEMPLATE
     TESTEFFORT THEAP5RELATION THEONLY TRANSACTION TREE TREEPROP
     TREEPROP+ TRUE TUPLE-COUNT TWO-WAY-STRUCTPROP TYPECONSTRAINT
     TYPEP UNDO-TO UNIQUE-FOR UNIQUE<=FOR WFF-IF
     WFFDEFN WFFMACRO WITH-DORMANT-RULES WITHREADACCESS WITHWRITEACCESS))

(export ; now those not in the manual
 '(- / < <= = > >= ABS 
     ARBITRARY-COMPARE-LE
     BINARY-RELATIONNAME BINARYRELATION CEILING
     CHAR-EQUAL CHAR-GREATERP CHAR-LESSP
     CHAR-NOT-GREATERP CHAR-NOT-LESSP CHAR< CHAR<=
     CHAR= CHAR> CHAR>= CHARACTER CHECKTYPE CLOSED-WFF
     CODEDEFN CODEDREL COUNTSPEC
     CXVALUEFN DEFAULT DEFAULT-TUPLE-PRINTER DEFINE-CLOS-RELATION
     DENOMINATOR DESCRIPTION DESTROYCONTEXT DO-PULSE
     ENFORCEMENT ENTITY EQ EQUAL
     EXPT FAIL FLOOR  FUNCTION GCD
     INCX ;INHERIT
     INPUT INTEGER INTEGER-IN-RANGE ISQRT ISUBREL+ ISUBREL+*
     LCM LISP-FUNCTION-INPUT-ARITY
     LISP-FUNCTION-OUTPUT-ARITY
     LISP-FUNCTION-RELATION-NAME
     LISP-PREDICATE-RELATION-NAME LIST LIST-OR-SYMBOL
     MAINTAIN-MNODE MAINTAININGCODE MAINTAININGTRIGGER
     MAKESUBCONTEXT MAP-COPY-WFF MAP-WFF MAX MIN
     MULTIPLE  NUMBER NUMERATOR
     OPTIONAL  PARTIAL-INDEX REL-OR-IMP
     RELATION-FOR-FIELD
     RELATION-IN-WFF RELATION-LISPFN RELATIONNAMEP
     RELATIONTYPECONSTRAINT ;RELINHERITER
     RELS-WITHOUT-DEFN RELS-WITHOUT-WFFDEFN
     REMOVE-INACTIVE-MATCHNODES RESET-HISTORY
     RESTRICT-ATTRIBUTE-RANGE ROUND RULE
     RULE-OR-RELATION RULEMATCHTREE S.T. DO-S.T. S.T.* ;DO-S.T.+
     SLOT SLOT-SINGLE
     STRING SUBREL-STORED SUBRELATIONCONSTRAINT SYMBOL
     T-OR-NIL TCLOSURE-OFNAME TELL-ME-ABOUT-FNS
     ;TEST      ;;a reasonable name for this function,
                ;;but a terrible name to export, especially for such a rarely
                ;; used function
     TESTREL TRANSITION-DERIVED-FROM TRANSITIVE-CLOSURE
     TRUNCATE TRY TYPE TYPECONSTRAINT-STORED
     TYPECONSTRAINTTRIGGER TYPENAME VARCOMPARE VARNAME
     VARTYPE WITHOUT-RECORDING-HISTORY))

(export '(partial-order-sort partial-order-stable-sort partial-order-merge
	  INVERSE-ORDER PRIORITY-ORDER IMAGE-ORDER Lexicographic-Order
	  order-by-class Literal-Order arbitrary< unordered)
	(find-package "AP5"))

(export '(create Create-Instance fetch update defattribute 
	  define-class defunion-class defintersection-class
	  unionclass intersectionclass
	  anom anom? notanom? is isnt one-is
	  when-is unless-is *EQL* *EQ* *EQUAL*)
	(find-package "AP5"))

(export '(*POTENTIAL-WFF-MACRO-FORM* PARSE-VAR DESCRIPTIONP GET-COMPARISON
          *UPDATE-MACRO-LIST* *TELL-ME-ABOUT-TUPLE-LIMIT*))

(export '(*ATOMIC-ID*
	  atomic-abort atomic-abort-tag atomic-abort-description
	   atomic-abort-abortdata
	   consistency-violation rules-do-only-noops unfixed-consistency-violation
	   no-data
           addchecker bad-definition bad-enforcement-level bad-subrel
	   cannot-trigger change-rule-trigger change-rule-enforcement
	   contradictory-updates insist typed-var-in-codedefn undefined-update
	   unknown-relation update-maintain)
	 (find-package "AP5"))

(export '(rule-handler-bind rule-handler-case) (find-package "AP5"))

(export '(def-process-sentinel process-db-wait) (find-package "AP5"))

(unless (find-package :AP-COMPILED)
  (make-package :AP-COMPILED :use nil :nicknames '("ap-compiled")))

(defvar ap-compiled (find-package 'ap-compiled))
