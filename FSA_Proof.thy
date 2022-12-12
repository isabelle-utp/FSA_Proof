theory FSA_Proof
  imports FSA_Semantics FSA_Commands "HOL-Eisbach.Eisbach"
begin

method check_reachable for I :: "State set" =
  (rule unreachable_by_invariant[where I="State.name ` I"]
  ,(auto simp add: State.defs Transition.defs Automaton.defs fsa_init_sem_def fsa_trans_sem_def fsa_defs))
  

end