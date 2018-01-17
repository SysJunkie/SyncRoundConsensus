---- MODULE MC ----
EXTENDS syncCon2, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_150890223360650000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1FAILNUM
const_150890223360651000 == 
1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_150890223360652000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_150890223360653000 ==
Agreement
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_150890223360654000 ==
Validity
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_150890223360655000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Tue Oct 24 23:30:33 EDT 2017 by varunjai
