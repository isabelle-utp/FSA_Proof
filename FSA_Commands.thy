theory FSA_Commands
  imports FSA_Metamodel
  keywords "state" "transition" "automaton" :: "thy_decl_block"
  and "initial" "label" "frm" "to" "states" "transitions"
begin

named_theorems fsa_defs

ML \<open>
structure Command_Toolkit =
struct

open Syntax;
open HOLogic;

fun mk_bool b = (if b then @{const True} else @{const False});

fun mk_command keyword description parser semantics =
  Outer_Syntax.command keyword description (parser >> (Toplevel.local_theory NONE NONE o semantics));

fun get_const ctx n =
  let val consts = (Proof_Context.consts_of ctx)
      val c = Consts.intern consts n
  in c end;

fun simple_definition name attrs term ctx
  = snd (Local_Theory.define
           ((Binding.name name, NoSyn)
         , ((Binding.name (name ^ "_def")
           , attrs)
           , Syntax.check_term ctx 
              term)) ctx);

end
\<close>

ML \<open>



\<close>

ML \<open>

(* States *)

val state_parser =
  let open Scan; open Parse in
  name -- (option @{keyword initial})
  end;

fun state_semantics (name, initial) ctx =
  let open Command_Toolkit
      val term = @{const "State.make"} $ mk_literal name $ (mk_bool (is_some initial))
  in simple_definition name @{attributes [fsa_defs, code_unfold]} term ctx end;

Command_Toolkit.mk_command @{command_keyword "state"} "Create an FSA state" state_parser state_semantics;

(* Transitions *)

val transition_parser =
  let open Scan; open Parse in
  (name --| @{keyword "="}) -- (@{keyword "label"} |-- name) -- ((@{keyword "frm"} |-- name) -- (@{keyword "to"} |-- name))
  end;

fun transition_semantics ((name, label), (from, to)) ctx = 
  let open Command_Toolkit
      val term = @{const Transition.make} $ mk_literal label $ mk_literal from $ mk_literal to
  in simple_definition name @{attributes [fsa_defs, code_unfold]} term ctx end;

Command_Toolkit.mk_command @{command_keyword "transition"} "Create an FSA transition" transition_parser transition_semantics;

(* Automata *)

val automaton_parser =
  let open Scan; open Parse in
  (name --| @{keyword "="}) 
   -- ((@{keyword "states"} |-- repeat1 name) -- (@{keyword "transitions"} |-- repeat1 name))
  end
  
fun automaton_semantics (name, (states, transitions)) ctx =
  let open Command_Toolkit
      val term = @{const Automaton.make} 
                 $ mk_literal name 
                 $ mk_list @{typ "State"} (map (const o get_const ctx) states) 
                 $ mk_list @{typ "Transition"} (map (const o get_const ctx) transitions)
  in simple_definition name @{attributes [fsa_defs, code_unfold]} term ctx end;

Command_Toolkit.mk_command @{command_keyword "automaton"} "Create an FSA" automaton_parser automaton_semantics;

\<close>
end