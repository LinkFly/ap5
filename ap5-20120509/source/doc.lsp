;;;-*- Mode: LISP; Package:AP5; Base:10.;Syntax:Common-Lisp -*-
;
(in-package "AP5")

(defmacro reldoc (name string)
  #-lucid `(setf (documentation ',name 'relation) ,string)
  #+lucid nil)

(RELDOC /
 "(/ x y z) is true iff, in lisp, (= z (/ x y)) returns T.  This differs 
from (* z y x) when x=y=0, in which case (* z y x) is true and (/ x y z) is not."
 ) 
(RELDOC ALLOW-INTERRUPTS
 "(ALLOW-INTERRUPTS nonatomic-relation truth-value) means that the
adder (for truth value T) or deleter (truth value nil) may be run
without disabling process-switching."
)
(RELDOC ANY-FOR
 "(Any-For relation pattern) means none of None-For, Optional-For and Multiple-For.") 
(RELDOC ANYCOMPARISON
 "(AnyComparison relation position) means that the use of a variable in the given
position of the relation should not be considered to constrain the equivalence
relation used to compare values for that variable.  This should only be true if
there is no way to generate variables at that position and the relation is never
updated.  See the manual for more details."
 ) 
(RELDOC ARRAY "(Array x) is the relation (and type) defined by the lisp function Arrayp.") 
(RELDOC AUTOMATION
 "(Automation name trigger code) means that there is an automation rule with
the given name trigger and code.  New automation rules can be created by
adding to this relation."
 ) 
(RELDOC AUTOMATIONRULE
 "(AutomationRule x) indicates that x is an Automation rule.  For a more
complete discussion of Automation rules, see the manual."
 ) 
#+ignore 
(RELDOC BASERELNAME
 "(BaseRelName relname arity) means that relname is the name of a base
relation (a particularly dumb implementation of relations) of arity arity.
Relations can be declared by doing (++ BaseRel relname arity)."
 ) 
(RELDOC BASETYPE
 "(BaseType x) is true if x is a base type.  Base types are types which include 
all (and only) objects that have been specifically classified to be of that 
type or a subtype.  To declare a new base type, do (++ BaseTypeName name). 
After this you may want to add some tuples to the (I)SubType relation.  Basetypes
can be tested and generated as relations, but they cannot be directly updated,
since that would be ambiguous.  The normal meaning of updating a basetype is
obtained by updating the classification relation."
 ) 
(RELDOC BASETYPENAME
 "(BaseTypeName name) is true if name is the name of a basetype, i.e.
the sort of type that includes objects that have been classified as of 
that type or a subtype.  New basetypes can be declared by asserting new
names into this relation, e.g., (++ BaseTypeName 'person).  This also 
gives the new type an adder and deleter and makes it a subtype of the
type DBObject."
 ) 
(RELDOC BINARY-RELATIONNAME
 "(Binary-RelationName name) means that name is the name of a binary relation") 
(RELDOC BINARYRELATION
 "(BinaryRelation rel) is true if rel is a binary relation, i.e., its arity is 2.") 
(RELDOC CANONICALIZER
 "(Canonicalizer equivalence-relation primitive-equivalence function) means that
the equivalence relation can be defined in terms of the primitive-equivalence,
which is one of {EQ, EQL, EQUAL}, by the function.  See the manual for details."
 ) 
(RELDOC CHARACTER
 "(Character x) is the relation (and type) defined by the lisp function characterp.") 
(RELDOC CHECKER
 "(Checker rel-or-imp code) defines actions for checking updates to rel or any 
relation of implementation imp.  See the manual for details."
 )
(RELDOC CLASSIFICATION
 "(Classification x type) means that x is of type type.
There is no requirement that for every type s.t. (type x), x be classified
as type (or any subtype of type).  However, this is true for basetypes.
It's normally more useful to ask about (type x) than (Classification x type)."
 ) 
(RELDOC CLOSED-WFF
 "(Closed-Wff x) is true if x is a wff with no free variables or non-constant
arguments") 
(RELDOC CODEDEFN
 "(CodeDefn rel defn) holds the definition for relations defined by code.
Assert CodedRelName to define a coded relation."
 )
#+ignore  
(RELDOC CODEDRELNAME
 "(CodedRelName relname defn) means that the relation of the given name
is defined by defn.  One can define relations by doing:
 (++ CodedRelName name defn) where defn is a list of the form
 (vars s.t. lisp-form), where the lisp form uses the variables in
vars freely."
 ) 
(RELDOC COMPARE-RELATION
 "(Compare-Relation relation position equivalence-relation) means that the
equivalence relation is used to compare objects in the given position of the
given relation.  See the manual for more details."
 ) 
(RELDOC CONS "(Cons x) is the relation (and type) defined by the lisp function Consp.") 
(RELDOC CONSISTENCYRULE
 "(ConsistencyRule x) indicates that x is a Consistency rule.  For a more
complete discussion of consistency rules, see the manual."
 ) 
(RELDOC CONSTRAINT-ENFORCEMENT-LEVEL
 "(Constraint-Enforcement-Level consistency-rule enforcement) indicates
the extent to which a constraint is enforced.  The (current) possible values
are :total, :incremental and :none, indicating whether the constraint is checked
at constraint creation time (y,n,n) and whether the code is compiled to
notice when it becomes violated (y,y,n).  None is useful as a way of declaring
intent (which may be useful to the system as an assumption) when enforcement
is impossible, impractical or unnecessary."
 ) 
(RELDOC COUNTSPEC "(CountSpec x) means that x is a legal countspec.") 
#+ignore 
(RELDOC CXVALUEFN
 "(CxValueFn rel-or-imp fn) defines how to get the explicit value of a tuple
of the relation (or a relation of the implementation) in a context.  The function
should take as arguments the relation and its argument list, and return T, NIL, or
Inherit as the value relative to CurrentCx.  Relations that have this ability
are assumed also to know how to add, delete, test and generate relative to 
CurrentCx."
 ) 
(RELDOC DBOBJECT "(DBObject x) is true if x is of the lisp type DBObject")
#+ignore  
(RELDOC DEFINEDRELNAME
 "(DefinedRelName relname wffdefn) means that the relation of the given 
name is defined by wffdefn, a list of the form (arglist s.t. wff).
One can define relations by inserting into this relation."
 )
#+ignore  
(RELDOC DEFSTRUCTRELNAME
 "(DefstructRelName name structure field) means that name is the name of binary
relation which is implemented by a defstruct field.  Structure must be the
name of a defined structure (as in Defstruct), and Field must be one of its
field names.  The first slot (position zero) of the relation can only be
filled by instances of the structure.  The DefStructName relation is provided
as a convenient way of declaring such a relation."
 )
#+ignore  
(RELDOC DEFSTRUCTRELNAME-SINGLE
 "(DefstructRelName-Single name structure field) means that name is the name
of a binary relation which is implemented by a defstruct field.  Structure 
must be the name of a defined structure (as in Defstruct), and Field must 
be one of its field names.  The first slot (position zero) of the relation 
can only be filled by instances of the structure.  The difference between 
this and the DefstructRelName relation is that this implementation can only 
relate a given structure to at most one object.  (The field contains either 
that object or a special empty-marker, whereas in the other case the field 
contains a list of objects.) The DefStruct1Name relation is provided as a 
convenient way of declaring such a relation."
 ) 
(RELDOC DERIVED
 "(Derived symbol) indicates that relations of this implementation 
are derived (as opposed to stored).  See the manual for details."
 ) 
(RELDOC DESCRIPTION
 "(Description x) is true if x is a list of the form (vars s.t. wff), where
wff uses the variables in vars (and no others) freely, and contains no 
runtime expressions.  Such an object is acceptable as a definition for a
relation, or as a rule trigger."
 ) 
(RELDOC DISJOINTCONSTRAINT
 "(DisjointConstraint ConsistencyRule) indicates that the
consistency rule enforces a disjointness constraint between two types."
 ) 
(RELDOC DISJOINTTRIGGER
 "(DisjointTrigger type1 type2 trigger) indicates that the trigger 
is of the form that would be used by a rule that prohibits the two
types from having any elements in common."
 ) 
(RELDOC DISJOINTTYPES
 "(DisjointTypes type1 type2) indicates that disjointness rules in conjunction
with subtype rules imply that the two types have no members in common."
 ) 
(RELDOC DOC
 "(Doc symbol symbol string-or-nil) stores commonlisp documentation.
Ap5 uses the symbols RELATION and RULE in the second slot to hold
documentation for relations and rules with names in the first slot."
 ) 
(RELDOC DONT-TELL-ME-ABOUT
 "(Dont-Tell-Me-About relation) is the way the default filter for Tell-Me-About
decides which relations to tell you about.  It tells you about any that are not
in this relation."
 )
#+ignore  
(RELDOC DOUBLEPROPRELNAME
 "(DoublePropRelName name) means that name is the name of a Two-Way-StructProp
relation, which is a binary relation that relates DBObjects to other DBObjects by
storing each on the property list of the other.  Thus for such a relation it is
impossible to generate {x,y | (R x y)}.  The DoublePropRelName relation is
supplied to make it convenient to declare such relations via ++."
 ) 
(RELDOC ENFORCEMENT
 "(Enforcement x) means that x is a legal enforcement for consistency rules.") 
(RELDOC ENTITY "(Entity x) is true for any x, i.e., Entity is the universal type.") 
(RELDOC EQ "(EQ x y) is the identity relation as defined by the lisp function EQ.") 
(RELDOC EQL "(EQL x y) is the identity relation as defined by the lisp function EQL.") 
(RELDOC EQUAL "(EQUAL x y) is the identity relation as defined by the lisp function EQUAL.") 
(RELDOC EQUIVALENCE-RELATION
 "(Equivalence-Relation x) is true if x is (has been declared to be) an equivalence
relation.  In this case it should be a binary relation, which is a superrelation of
EQ, and is symmetric and transitive.  Such relations should probably also be in the
Canonicalizer relation.  See the manual for a complete description of the use and
meaning of these relations."
 ) 
(RELDOC FUNCTION
 "(Function x) is the relation (and type) defined by the lisp function Functionp.") 
(RELDOC GENERATOR-CACHE
 "(Generator-Cache rel-or-symbol description compiled-generator) is where
AP5 caches generators.  The description slot is a canonical form of a 
description which the last slot specifies how to generate.  (The last
slot can also specify that the description cannot be generated.)  Slot
zero is either the CAR of the wff in the description, ( a relation
or a connective or a quantifier), or a relation lexically inside the wff.  
AP5 does not allow triggering on changes to this relation.
Tuples are only added by AP5 itself as a result of translation of generators."
 ) 
(RELDOC IDEMPOTENT
 "(Idempotent rel-or-imp truth-value) means that the
adder (for truth value T) or deleter (truth value nil) is idempotent.")
(RELDOC IDISJOINTTYPES
 "(IDisjointTypes type1 type2) indicates that a rule states that the two
types have no members in common."
 ) 
(RELDOC IMPLEMENTATION
 "(Implementation x) means that x has been declared as an implementation for
relations.  This type is used for constraining such relations as reladder,
relationimplementation, etc.  The main reason for its existence is to catch
errors in the implementation names you type.  Of course, whenever you invent
a new implementation, you have to add it to this type."
 )
(RELDOC INCONSISTENCY-REPORTER
 "(Inconsistency-Reporter consistency-rule function) means that when an
atomic transition aborts due to inability to satisfy the consistency rule,
the function (whose arguments are the same as those for the rulecode of the
rule) will be called to report something meaningful to the user.  These are
used by the atomic construct's default IFABORT code."
 ) 
(RELDOC INLINEREL
 "(InLineRel relation) means that if relation is a defined relation
then its occurrences in wffs will by default be expanded in line
like macros.  This default can be overridden by occurrences of InLine
and NotInLine in particular wffs."
 ) 
(RELDOC INTEGER
 "(Integer x) is true if x is a lisp number (numberp) which is = to some
lisp integer (integerp).  Thus 2.0 is an integer."
 ) 
(RELDOC ISUBREL
 "(ISubRel r1 r2) means that r1 is an immediate subrelation of r2, which implies
that (SubRel t1 t2).  Normally the SubRel relation is more useful for access.
The SubRel relation can also be asserted, which is equivalent to asserting the
ISubRel relation."
 )
#+ignore  
(RELDOC LISP-FUNCTION-RELATION-NAME
 "(Lisp-Function-Relation-name name input-arity output-arity)
means that name is the name of a lisp function of input-arity arguments,
returning output-arity values. The Lisp-Function relation of that name 
has as its arity the sum of input-arity and output-arity, and is defined by 
the function: it is tested by applying the function to the first input-arity
arguments and comparing the results to the last output-arity arguments -
be sure to assert the appropriate Compare-Relation facts.
This implementation also uses the function to provide a generator for (a 
single value of) the last output-arity arguments given values for the 
first input-arity arguments.
The Lisp-Function-Relation-name relation is supplied to make it convenient
to declare such relations via ++."
 )
#+ignore  
(RELDOC LISP-PREDICATE-RELATION-NAME
 "(Lisp-Predicate-Relation-name name arity)
means that name is the name of a Lisp-Predicate relation defined by the 
function of that name and arity arguments.  Such relations can be tested by
applying the function.  (If this generates an error the test returns nil.)
The implementation itself provides no way to generate or update such a relation.
The Lisp-Predicate-Relation-name relation is supplied to make it convenient
to declare such relations via ++."
 ) 
(RELDOC LIST "(List x) is the relation (and type) defined by the lisp function Listp.") 
(RELDOC LIST-OR-SYMBOL "(List-Or-Symbol x) is the union of the types List and Symbol.") 
(RELDOC MAINTAINEDREL
 "(MaintainedRel relation defn rule) means that the rule maintains the relation,
i.e., the rule changes the  relation as needed in order to keep it equivalent
to defn.  (This is actually a maintained relation!)  The recommended way to 
make it true is to assert a WffDefn and implementation (other than defined)
for relation."
 ) 
(RELDOC MAINTAINRULE
 "(MaintainRule x) indicates that x is a Maintain rule.  For a more
complete discussion of Maintain rules, see the manual."
 ) 
(RELDOC MATCHNODE
 "(MatchNode x) is true if x is a matchnode.  MatchNode is a subtype of DBObject.
These objects are used for triggering rules."
 ) 
(RELDOC MULTIPLE-FOR
 "(Multiple-For relname pattern) means that there is a consistency rule that
requires the relation of the given name to contain certain tuples.  Pattern 
is a list, corresponding to an argument list of relation.  The elements of 
the list are either type names or the symbol OUTPUT.  The constraint says 
that if you replace each non-output element of pattern with an object of 
that type, there will be some values for the output elements satisfying the 
relation.  For instance, the requirement that every employee has an office 
is expressed by the fact (Multiple-For Office (Employee OUTPUT)).
The relation and type names may also be descriptions."
 ) 
(RELDOC NO-TRIGGER
 "(No-Trigger description) advises the rule compiler not to bother trying
to detect instances of the description.  The rule compiler will only recognize
that very wff, and not other equivalent forms.  This relation is therefore
really only useful after you've seen the matchnodes that your rules compile
into.  This relation may be thought of as a way to extend the declarations
PossibleToAdd and PossibleToDelete to general wffs, but of course, those
declarations are more general in that they apply to a large class of equivalent
wffs, e.g., ((x y) s.t. (start (R x y))) and ((y x) s.t. (start (R y x)))."
 ) 
(RELDOC NONATOMIC-RELATION
 "Nonatomic relations do not support atomic semantics - 
all updates take effect immediately and are not recorded in the history.
This can be declared via the :nonatomic argument to defrelation.")
(RELDOC NONE-FOR
 "(None-For relname pattern) means that there is a consistency rule that
prohibits the relation of the given name from containing certain tuples.  
Pattern is a list, corresponding to an argument list of relation.  The 
elements of the list are either type names or the symbol OUTPUT.  The 
constraint says that if you replace each non-output element of pattern 
with an object of that type, there will be no values for the output elements 
satisfying the relation.  The relation and type names may also be descriptions."
 ) 
(RELDOC NONTRIGGERABLE
 "(NonTriggerable relation) means that the relation cannot be triggered.  This
is the case for data that you want to access relationally, even though it is
actually updated without any database operations, e.g., time.  This declaration
will prevent the compilation of rules that have to notice when the relation
changes."
 ) 
(RELDOC NOT-ALLOWED-TO-UPDATE
 "(Not-Allowed-to-Update relation truthvalue) means that 
++ (if truthvalue is T) or -- (if it's nil) are not allowed for
the relation."
 ) 
(RELDOC NUMBER "(Number x) is the relation (and type) defined by the lisp function numberp.") 
(RELDOC OPTIONAL-FOR
 "(Optional-For relname pattern) means that there is a consistency rule that
prohibits the relation of the given name from containing certain tuples.  
Pattern is a list, corresponding to an argument list of relation.  The elements 
of the list are either type names or the symbol OUTPUT.  The constraint says 
that if you replace each non-output element of pattern with an object of that 
type, there will be at most one tuple of output elements satisfying the relation.  
For instance, the requirement that no employee have more than one office is 
expressed by the fact (Optional-for Office (Employee OUTPUT)).
The relation and type names may also be descriptions."
 )
(RELDOC PARAMETER-LIST 
 "(Parameter-List relation entity) relates a relation to the :representation,
:derivation or :computation parameter used to declare it via defrelation."
 ) 
(RELDOC POSSIBLETOADD
 "(PossibleToAdd relation T-or-NIL) means that (in spite of the presence or
absence of reladder tuples), the relation can (if T) or cannot (if NIL) become
true.  If there is no such tuple, the compiler assumes that the relation can
become true if it or its implementation has a RelAdder or ++ Trigger.
The default is normally right, so this relation is only rarely needed, e.g.,
when a coded relation accessed a stored relation.  (In this case a ++ trigger
tuple is also in order.)  The opposite case arises when a relation looks like it
could be updated (say it's a base relation) but actually cannot (perhaps due to
a consistency rule).  This is actually used in constucting the rule triggering
network, which is sensitive to the changes that are actually made."
 ) 
(RELDOC POSSIBLETODELETE
 "(PossibleToDelete relation T-or-NIL) means that (in spite of the presence or
absence of reldeleter tuples), the relation can (if T) or cannot (if NIL) become
false.  If there is no such tuple, the compiler assumes that the relation can
become false if it or its implementation has a RelDeleter or -- Trigger.
The default is normally right, so this relation is only rarely needed, e.g.,
when a coded relation accessed a stored relation.  (In this case a -- trigger
tuple is also in order.)  The opposite case arises when a relation looks like it
could be updated (say it's a base relation) but actually cannot (perhaps due to
a consistency rule).  This is actually used in constucting the rule triggering
network, which is sensitive to the changes that are actually made."
 ) 
(RELDOC PRINTER
 "(Printer type function) provides a way for DBobjects (not arbitrary lisp
objects) to print themselves.  DBObjects are printed by looking for types 
of which they are instances that have printers.  If any of these printers,
when applied to the object return non nil, that value is used to represent
the object.  The suggested convention is that printers should print a list
of the form (DBO type ...), such that a reader for that type can translate
the list back into the object."
 ) 
(RELDOC PROHIBITED
 "(Prohibited name wff code enforcement) means that there is a consistency
rule with the given name that prohibits the wff.  The rule has the given
code and level of enforcement.  Consistency rules may be created by adding
to this relation.  See the manual for more details."
 ) 
(RELDOC PROPER-NAME
 "(Proper-Name entity string-or-symbol) relates objects to names.
The function DBO accepts a proper-name (if it is the proper-name of a unique
object), and the printer for DBObjects prints a proper-name of the object if
there is one."
 )
#+ignore  
(RELDOC PROPRELNAME
 "(PropRelName name) means that name is the name of a StructProp relation,
i.e., a binary relation that relates DBObjects to arbitrary other objects by
storing things on the property list of the DBObject.  Thus for such a relation
it is impossible to generate {x | (R x y)}.  The PropRelName relation is
supplied to make it convenient to declare such relations via ++."
 ) 
(RELDOC READER
 "(Reader type function) reads DBObjects printed by functions in the Printer
relation.  The function should take a list whose car is the type and return the
object that would have printed as (DBO . <the list>)."
 ) 
(RELDOC REL-OR-IMP
 "(Rel-Or-Imp x) is true if x is a relation object or a implementation.
This is the type constraint for relations such as RelAdder."
 ) 
(RELDOC RELADDER
 "(RelAdder rel-or-imp macro) defines how tuples can be added to a relation
or to relations of a given implementation.  See the manual for details."
 ) 
(RELDOC RELATION
 "(Relation relation) is true of all known relations, 
i.e., (loop for r s.t. (Relation r) collect r) will give a list of relations.
The definition of a relation is an object in the first place of a tuple of
the RelationArity relation."
 ) 
(RELDOC RELATION-IN-DEFN
 "(Relation-in-Defn rel rel-or-rule) means that the relation rel appears in the
definition or trigger of rel-or-rule, which must either be a relation or rule.
Its transitive-closure is Relation-in-Defn*."
 ) 
(RELDOC RELATION-IN-DEFN*
 "(Relation-in-Defn* rel rel-or-rule) means that the relation rel is used in the
definition or trigger of rel-or-rule, which must either be a relation or rule.
It is the transitive-closure of Relation-in-Defn."
 ) 
(RELDOC RELATION-IN-WFF
 "(Relation-In-Wff rel wff) means that the relation rel appears in wff, which
is something close to a closed-wff or description, but may have less stringent
requirements in terms of matching equivalence relations etc.  This includes 
expansion of macros in the wff but not expansions of definitions of defined 
relations.  (See Relation-in-Defn.)"
 ) 
(RELDOC RELATION-LISPFN
 "(Relation-LispFn relation lispfn-name) means that lispfn-name is the
name of a function that defines the relation (if its implementation 
is lisp-predicate or lisp-function)."
 ) 
(RELDOC RELATIONARITY "(RelationArity rel arity) relates relations to their arities.") 
(RELDOC RELATIONIMPLEMENTATION
 "(RelationImplementation rel imp) relates relations to their implementations.") 
(RELDOC RELATIONNAME "(RelationName rel name) relates relations to their names.") 
(RELDOC RELATIONTYPECONSTRAINT
 "(RelationTypeConstraint relation consistency-rule) indicates that the
consistency rule enforces a type constraint on the relation.  The type
and position of the constraint can be found from the trigger of the rule
via the relation TypeConstraintTrigger."
 ) 
(RELDOC RELDELETER
 "(RelDeleter rel macro) defines how to delete tuples from the relation
rel.  See the manual for details."
 ) 
(RELDOC RELGENERATOR
 "(RelGenerator rel-or-imp generator) defines generator algorithms.
See the manual for details."
 ) 
#+ignore 
(RELDOC RELINHERITER
 "(RelInheriter rel-or-imp macro) defines how to inherit tuples of the
relation rel.  See the manual for details."
 ) 
(RELDOC RELSIZE
 "(RelSize relation pattern size) tells how to estimate the size of a 
relation (number of tuples).  See the manual for details."
 ) 
(RELDOC RELTESTER
 "(RelTester rel-or-imp macro) defines how to test the relation rel.  See the
manual for details."
 ) 
(RELDOC RELUPDATER
 "(RelUpdater rel-or-imp function) defines how sets of updates can be made to a
relation or to relations of a given implementation.  See the manual for details."
 ) 
(RELDOC RULE
 "(Rule x) means that x is a rule object: an AutomationRule, ConsistencyRule,
ConsistencyChecker, AutomationGenerator or MaintainRule."
 ) 
(RELDOC RULECODE
 "(RuleCode rule code) relates a rule to the piece of lisp code to
be executed when the rule triggers."
 ) 
(RELDOC RULENAME "(RuleName rule symbol) relates a rule to its name.") 
(RELDOC RULETRIGGER "(RuleTrigger rule trigger) relates a rule to its trigger.") 
(RELDOC STRING "(String x) is the relation (and type) defined by the lisp function Stringp.") 
(RELDOC SUBREL
 "(SubRel r1 r2) means that r1 is a subrelation of r2, i.e., all tuples of r1 are
also tuples of r2."
 ) 
(RELDOC SUBRELATIONCONSTRAINT
 "(SubRelationConstraint rule subrel superrel) means that rule is a
constraint that requires subrel to be a subrelation of superrel."
 ) 
(RELDOC SUBTYPE
 "(Subtype t1 t2) means that t1 and t2 are types, and that every object of type t1 is
of of type t2."
 ) 
(RELDOC SYMBOL "(Symbol x) is the relation (and type) defined by the lisp function Symbolp.") 
(RELDOC T-OR-NIL "(T-OR-NIL x) is true if x is either T or NIL.") 
(RELDOC TCLOSURE
 "(TClosure immediaterel closurerel) means that closurerel is the transitive
closure of immediaterel, both binary relations.  For declaring transitive
closure relations, use the relation Transitive-Closure."
 ) 
(RELDOC TESTEFFORT
 "(TestEffort rel-or-implementation macro) tells how to estimate the
effort needed to test tuples of a relation or implementation.  See the manual
for details."
 ) 
#+ignore 
(RELDOC TRANSITIVE-CLOSURE
 "(Transitive-Closure immediaterelname closurerelname) means that closurerelname,
immediaterelname are the names of two binary relations (which we will call irel
and crel), such that crel is the transitive closure of irel.
That means that crel is true of two objects, x and y, iff there is a finite
sequence of at least two objects starting with x and ending with y such that
every adjacent pair of elements is related by irel.  The real purpose of this
relation is to allow you to declare crel by adding a tuple in which you name
irel.  At present irel is not allowed to be a defined relation."
 )
#+ignore  
(RELDOC TREEPROP+RELNAME
 "(TreeProp+RelName name) means that name is the name of a TreeProp+ relation.
It's a generalization of TreeProp in that non-DBObjects can be in the domain.
The data is stored like TreeProp relations for DBObjects.  For symbols the
range values are stored on the symbol property list and for other objects
they're stored in a hashtable."
 )
#+ignore  
(RELDOC TREEPROPRELNAME
 "(TreePropRelName name) means that name is the name of a TreeProp relation -
a binary relation between dbobjects and arbitary objects.  If (<name> x y) is
true, then y is on the property list of x (like a proprel), and x can be found
from y by looking in a hashtable (like a treeprop)."
 )
#+ignore  
(RELDOC TREERELNAME
 "(TreeRelName relname arity) means that relname is the name of a relation
of arity arguments stored as a tree: (R x y z) is stored by z being in the
y branch of the x branch of the R tree (branches are found by assoc or
gethash, depending on the number of branches).  Relations can be declared
by doing (++ TreeRelName relname arity)."
 ) 
(RELDOC TYPE "(Type relation) means that relation is a type, i.e., a unary relation.") 
(RELDOC TYPECONSTRAINT
 "(TypeConstraint relation position type) means that the position'th
element of every true tuple of relation must be of the given type.
Usually the macro DefTypeConstraints is convenient for declaring
such constraints.  See the manual for details."
 ) 
(RELDOC TYPECONSTRAINTTRIGGER
 "(TypeConstrainttrigger rel arity pos type trigger) indicates that the trigger 
is of the form that would be used by a rule that enforces a type constraint on
Relation.  Arity is the arity of Relation of which the  Pos'th argument must be
of type Type."
 ) 
(RELDOC TYPENAME "(TypeName name) means that name is the name of a type") 
(RELDOC UNIQUE-FOR "(Unique-For relation pattern) means both Optional-For and Multiple-For.") 
(RELDOC WFFDEFN
 "(WffDefn rel defn) means that the relation rel is defined to be equivalent
to the description defn.  If rel has the implementation 'Defined, this means
that whenever rel is accessed, the definition will be used.  To get this affect
one can assert into the DefinedRelName relation.  If rel has some other
implementation, it will be maintained by a consistency rule.  If such a rule must
be built, it will be given the enforcement which is the value of the variable
MaintainedEnforcement (initially :incremental).  The MaintainedRel relation can
be used to access the rule that enforces a definition."
 ) 
