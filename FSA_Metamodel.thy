section \<open> FSA Meta-Model \<close>

theory FSA_Metamodel
  imports Main
begin

text \<open> Isabelle's default @{typ string} type is not useful for code generation (it becomes a list
  of characters), and so we hide and replace it with the more useful @{typ String.literal} type. \<close>

hide_type string
type_synonym string = String.literal
type_synonym uname = String.literal

text \<open> I think that in ECore all objects are equipped with a built-in identifier? In which case,
  each record corresponding to a class needs an extra field to record this information. \<close>

record State =
  name :: string
  initial :: bool 

record Transition =
  label :: string
  "from" :: uname
  "to" :: uname

text \<open> The Isabelle document model is sequential and so imposes "define-before-use"; therefore
  we need to define Automaton after @{typ State} and @{typ Transition}. We could manage this
  by an implementation of ECore itself in Isabelle. \<close>

record Automaton =
  name :: string
  states :: "State list" \<comment> \<open> We use lists for multplicity, but we could also use sets or maps \<close>
  transitions :: "Transition list"

text \<open> We have to define the well-formedness constraints, which are implicit in ECore. \<close>

definition wf_Automaton :: "Automaton \<Rightarrow> bool" where
  "wf_Automaton \<A> =
       ((\<forall> t \<in> set (transitions \<A>). from t \<in> State.name ` set (states \<A>))
       \<and>(\<forall> t \<in> set (transitions \<A>). to t \<in> State.name ` set (states \<A>)))"

end