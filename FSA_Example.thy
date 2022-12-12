theory FSA_Example
  imports FSA_Proof
begin

state S initial
state A
state B
state C

transition t1 = label a frm A to A
transition t2 = label a frm A to S
transition t3 = label b frm A to B
transition t4 = label b frm B to A
transition t5 = label a frm C to A
transition t6 = label c frm C to B

automaton ABC =
  states S A B C
  transitions t1 t2 t3 t4 t5 t6

text \<open> We can use the following line to check well-formedness, which internally uses the code
  generator for efficient execution. \<close>

value "wf_Automaton ABC"

lemma C_not_reachable: "\<not> reachable ABC C"
  by (check_reachable "{S, A, B}")

end
