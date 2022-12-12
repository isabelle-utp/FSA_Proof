theory FSA_Example_1
  imports FSA_Semantics
begin

text \<open> We have names at both the meta-logic and logic level. Isabelle records don't support default
  field values, though we could add syntax to support this. \<close>

definition "S = \<lparr> State.name = STR ''S'', initial = True \<rparr>"
definition "A = \<lparr> State.name = STR ''A'', initial = False \<rparr>"
definition "B = \<lparr> State.name = STR ''B'', initial = False \<rparr>"
definition "C = \<lparr> State.name = STR ''C'', initial = False \<rparr>"

definition "t1 = \<lparr> label = STR ''a'', from = State.name S, to = State.name A \<rparr>"
definition "t2 = \<lparr> label = STR ''a'', from = State.name A, to = State.name S \<rparr>"
definition "t3 = \<lparr> label = STR ''b'', from = State.name A, to = State.name B \<rparr>"
definition "t4 = \<lparr> label = STR ''b'', from = State.name B, to = State.name A \<rparr>"
definition "t5 = \<lparr> label = STR ''a'', from = State.name C, to = State.name A \<rparr>"
definition "t6 = \<lparr> label = STR ''c'', from = State.name C, to = State.name B \<rparr>"

definition ABC :: Automaton where
"ABC = \<lparr> name = STR ''ABC''
       , states = [S, A, B, C]
       , transitions = [ t1, t2, t3, t4, t5, t6 ]
       \<rparr>"

text \<open> We can use the following line to check well-formedness, which internally uses the code
  generator for efficient execution. \<close>

value "wf_Automaton ABC"

lemma "\<not> reachable ABC STR ''C''"
  apply (rule unreachable_by_invariant[where I="{STR ''S'', STR ''A'', STR ''B''}"])
  apply (auto simp add: ABC_def fsa_init_sem_def S_def A_def B_def C_def fsa_trans_sem_def t1_def t2_def t3_def t4_def t5_def t6_def)
  done

end