;;;-*- Mode: LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-
(in-package "AP5")


(deftypeconstraints :incremental NonTriggerable relation)
(deftypeconstraints :incremental no-trigger list)
  ; actually we'd like it to be description, but that can't be enforced
(deftypeconstraints :incremental Constraint-Enforcement-Level
  ConsistencyRule enforcement)
(deftypeconstraints :incremental inconsistency-reporter
  ((x) s.t. (or (consistencyrule x) (ConsistencyChecker x))) function)
(deftypeconstraints :none RelationTypeConstraint relation consistencyrule)
(deftypeconstraints :incremental RuleName rule symbol)
(deftypeconstraints :incremental MatchConsistency matchnode
  ((x) s.t. (or (consistencyrule x) (ConsistencyChecker x))))
(deftypeconstraints :incremental MatchAutomation matchnode
  ((x) s.t. (or (AutomationRule x) (AutomationGenerator x))))
(deftypeconstraints :incremental MatchMaintain matchnode MaintainRule)
(deftypeconstraints :incremental RuleTrigger Rule list-or-symbol)
    ; actually either description or closed-wff at the moment
(deftypeconstraints :incremental RuleCode Rule Function)
(deftypeconstraints :incremental Classification entity basetype)
(deftypeconstraints :incremental Possibletoadd Relation t-or-nil)
(deftypeconstraints :incremental Possibletodelete Relation t-or-nil)
(deftypeconstraints :incremental Proper-Name entity
		    ((x) s.t. (or (string x) (symbol x))))
;(deftypeconstraints :incremental Help DBObject :ignore)
; Help will be further constrained later
(deftypeconstraints :incremental codedefn relation list)
(deftypeconstraints :incremental Wffdefn relation :none description)
(deftypeconstraints :incremental Testeffort rel-or-imp function)
(deftypeconstraints :incremental Relsize relation list
		    ((x) s.t. (or (number x) (= x nil))))
;(deftypeconstraints :incremental Relinheriter rel-or-imp function)
(deftypeconstraints :incremental Reldeleter rel-or-imp function)
(deftypeconstraints :incremental Relgenerator rel-or-imp function)
(deftypeconstraints :incremental Reader type function)
(deftypeconstraints :incremental Printer type function)
(deftypeconstraints :incremental Checker rel-or-imp function)
(deftypeconstraints :incremental Reladder rel-or-imp function)
(deftypeconstraints :incremental trigger relation t-or-nil function relation t-or-nil)
(deftypeconstraints :incremental Cxvaluefn rel-or-imp function)
(deftypeconstraints :incremental Reltester rel-or-imp function)
(deftypeconstraints :incremental Relupdater rel-or-imp function)
(deftypeconstraints :incremental parameter-list relation entity)
(deftypeconstraints :incremental Derived implementation)
(deftypeconstraints :incremental implementation symbol)
(deftypeconstraints :incremental tclosure binaryrelation binaryrelation)
(deftypeconstraints :incremental relationimplementation relation implementation)
(deftypeconstraints :incremental relationarity dbobject integer)
; it's useless to say that only a relation can have arity - that's true by defn!
(deftypeconstraints :incremental relationname relation symbol)
(deftypeconstraints :incremental anycomparison relation integer)
(deftypeconstraints :incremental canonicalizer equivalence-relation
		    equivalence-relation function)
(deftypeconstraints :incremental compare-relation relation integer
		    equivalence-relation)
(deftypeconstraints inlinerel relation)
(deftypeconstraints not-allowed-to-update relation t-or-nil)
(deftypeconstraints known-match-predecessor relation :none description matchnode matchnode)

; now declare the types of defined/coded relations, not to be enforced

(deftypeconstraints :none typeconstraint relation integer 
		    ((x) s.t. (or (description x) (type x))))
(deftypeconstraints :none typeconstraint-stored relation integer
		    ((x) s.t. (or (description x) (type x))))
(deftypeconstraints :none prohibited symbol closed-wff function enforcement)
(deftypeconstraints :none automation symbol description function)
(deftypeconstraints :none typeconstrainttrigger :ignore integer integer :ignore list)
(deftypeconstraints :none treerelname symbol integer)
(deftypeconstraints :none baserelname symbol integer)
(deftypeconstraints :none codedrelname symbol list)
(deftypeconstraints :none definedrelname symbol description)
(deftypeconstraints :none SubRelationConstraint consistencyrule relation relation)
(deftypeconstraints :none SubRelTrigger :ignore :ignore integer list)
(deftypeconstraints :none MaintainedRel relation description maintainrule)
(deftypeconstraints :none Maintainingcode relation integer symbol)
(deftypeconstraints :none Maintainingtrigger description closed-wff)
(deftypeconstraints :none Maintain-Mnode relation matchnode)
(deftypeconstraints :none SubType type type) ; these guaranteed by next one
(deftypeconstraints :none Subrel-stored Relation Relation)
(deftypeconstraints :none Subrel Relation Relation)
(deftypeconstraints :none ISubrel+* Relation Relation)
(deftypeconstraints :none Isubrel+ Relation Relation)
(deftypeconstraints :none Isubrel Relation Relation)
(deftypeconstraints :none transitive-closure symbol symbol)
(deftypeconstraints :none multiple-for symbol list)
(deftypeconstraints :none optional-for symbol list)
(deftypeconstraints :none none-for symbol list)
(deftypeconstraints :none Unique-for symbol list)
;(deftypeconstraints :none Any-for entity entity)
(deftypeconstraints relation-in-wff :none relation list-or-symbol)
(deftypeconstraints relation-in-defn :none relation rule-or-relation)
(deftypeconstraints relation-in-defn* :none relation rule-or-relation)
; formerly enforced but now superceded - see misc-rules

;; this leaves out all the types and equivalence relations

; Here are type constraints that are also subtype constraints
; Fortunately, they turn out the same - each is recognized as the other!
; The only possible difference is the enforcement.
#+ignore
((DEFTYPECONSTRAINTS :INCREMENTAL NONTRIGGERABLE RELATION)
   (DEFTYPECONSTRAINTS :INCREMENTAL DERIVED SYMBOL)
   (DEFTYPECONSTRAINTS :INCREMENTAL NAMES-NOT-ALLOWED-FOR-RELATIONS SYMBOL))

; correct some omissions from ISubrel
; these are the typeconstraints with enforcement :none
(loop for x in
      '((treeproprelname binary-relationname)
	(treeprop+relname binary-relationname)
	(doubleproprelname binary-relationname)
	(proprelname binary-relationname)
	(basetypename typename)
	(basetype type)
	(eq eql)
	(eql equal)
	(eql =)
	; now some other misc. relations
	(subtype subrel)
	)
      do (++ subrel (relationp (car x)) (relationp (cadr x))))

; declare char=, char-equal as equivalence rels? - with canonicalizers!
; no - they don't relate non chars to themselves.

; now I can throw in a whole bunch of count constraints (oh goody!)
; *** should I really be using entity or the required type for the rel?

(CountReq entity relationname :countspec :optional :inverse t)
; *** should I also require that every relation have a name?
(countreq entity inconsistency-reporter :countspec :optional :replacing t)
; unique - use entity for optional
(countreq consistencyrule constraint-enforcement-level :countspec :multiple)
(countreq entity constraint-enforcement-level :countspec :optional)
(countreq rule ruletrigger :countspec :multiple)
(countreq entity ruletrigger :countspec :optional)
(countreq rule rulecode :countspec :multiple)
(countreq entity rulecode :countspec :optional :replacing t)
(countreq entity rulename :countspec :optional :inverse t :enforcement :none)
; already enforced by a rule that declassifies old rules with same name as new
(countreq entity reladder :countspec :optional :replacing t)
(countreq entity reldeleter :countspec :optional :replacing t)
(countreq entity relupdater :countspec :optional :replacing t)
;(countreq entity relinheriter :countspec :optional :replacing t)
(countreq entity reltester :countspec :optional :replacing t)
(countreq entity wffdefn :countspec :optional :replacing t)
(countreq entity codedefn :countspec :optional :replacing t)
(countreq entity testeffort :countspec :optional :replacing t)
(countreq entity possibletoadd :countspec :optional :replacing t)
(countreq entity possibletodelete :countspec :optional :replacing t)
;; constraint removed in multirep change 1/97
;;(countreq entity relationimplementation :countspec :optional :replacing t)
(countreq entity relationarity :countspec :optional :replacing t)

; no replace since these are likely to detect mistakes
(countreq entity cxvaluefn :countspec :optional)
(countreq entity matchmaintain :countspec :optional :inverse t :replacing t)
(countreq entity matchconsistency :countspec :optional :inverse t :replacing t)
(countreq entity matchautomation  :countspec :optional :inverse t :replacing t)
(countreq entity tclosure :countspec :optional :inverse t)
(countreq entity transitive-closure :countspec :optional :inverse t
	  :enforcement :none)

(countreq entity baserelname :countspec :optional :enforcement :none)
(countreq entity codedrelname :countspec :optional :enforcement :none)
(countreq entity treerelname :countspec :optional :enforcement :none)
(countreq entity definedrelname :countspec :optional :enforcement :none)
(countreq entity maintain-mnode :countspec :optional :enforcement :none)
(countreq entity relationtypeconstraint :countspec :optional
	  :enforcement :none :inverse t)

;; I've left out all the lisp function relations and equivalence relations
; also, it would be nice to have count constraints for rels of higher arity
; such as tell-me-about-fns, compare-relation, canonicalizer, relation-for-field
; defstructrelname, defstruct1relname,  lisp-function-relation-name

(restrict-cardinality compare-relation (entity entity output)
		      :countspec :optional :replacing t)
(restrict-cardinality canonicalizer (entity output output)
		      :countspec :optional :replacing t)
; perhaps ought to be unique for equiv's other than {eq,eql,equal}?
(restrict-cardinality relsize (entity entity output)
		      :countspec :optional :replacing t)