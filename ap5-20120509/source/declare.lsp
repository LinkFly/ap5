;;; -*- Mode:LISP; Package:AP5; Base:10; Syntax:Common-Lisp -*-

(in-package "AP5")

; should really be global
(proclaim
  '(special DefaultRelSize DefaultRelSizePats GenEffortWarning GenSizeWarning
	    triggerEffortWarning triggerSizeWarning 
	    NullSetGenerator TreeGeneratorTable Warnings RelationOfName
	    global-history generator-cost-record treegenproptable
	    *rule-cycle* *rule-cycle-limit* *current-rule*))
(proclaim '(special  KeepStarts)) ;actually rebound 
(proclaim '(special CurrentCx *GlobalCx* |UpdateStatus | ;|Contexts |
		    |Updates | |DangerousP | |WhoHasDataBaseWriteAccess |
		    |Requirements | Delta))

; vars that hold relations
(proclaim 
  '(special Rel-Implementation Rel-Name Rel-Arity rel-eql rel-comparison
	    rel-equivalence rel-canonicalizer rel-eq rel-equal rel-equalp
	    Rel-Adder Rel-Deleter Rel-Tester Rel-Generator rel-codedefn
	    Rel-Size Rel-TestEffort Rel-WffDefn Rel-CxValueFn Rel-CxSensitive
	    Rel-Checker Rel-Derived ;Rel-Inheriter
	    Rel-Trigger rel-classification type-relation
	    rel-isubrel type-list-or-symbol type-character rel-subrel
	    rel-isubtype rel-subtype type-type type-entity type-symbol
	    type-list type-string type-function type-number type-integer
	    type-dbobject type-basetype rel-anycompare 
	    rel-printer rel-reader rel-proper-name rel-nontriggerable
	    rel-possibletoadd rel-possibletodelete ;rel-help
	    ))
(proclaim
  '(special Fix-Maintained-Relation InPrintDBObject abortdata
	    *abort-condition* Bootstrapping))

(proclaim
  '(special debugswitches tryvalue MaintainedEnforcement prototype-mode
	    suspended-matchnodes suspended-rules suspended-rule-classes	    
	    TypeConstraintEnforcement SubRelEnforcement generator-cache))

(defvar *warning-flags* nil) ; will be added to as warnings appear

; until the compiler problem goes away ...
(proclaim '(special apspec1))

(proclaim '(special bootstrapping))