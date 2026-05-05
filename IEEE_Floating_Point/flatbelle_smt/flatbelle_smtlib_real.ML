(*  Title:      
    Author:     

SMT setup for reals. TODO: add more stuff!
*)

structure SMT_Real: sig end =
struct


(* SMT-LIB logic *)
fun smtlib_logic _ ts = SOME "TODO"

local 
  fun real_num _ i = SOME (string_of_int i ^ ".0")

  fun is_linear [t] = Flatbelle_SMT_Util.is_number t
    | is_linear [t, u] = Flatbelle_SMT_Util.is_number t orelse Flatbelle_SMT_Util.is_number u
    | is_linear _ = false

  fun mk_times ts = Term.list_comb (\<^Const>\<open>times \<^Type>\<open>real\<close>\<close>, ts)
  
  fun times _ _ ts = if is_linear ts then SOME ("*", 2, ts, mk_times) else NONE

in

fun real_type_parser (Flatbelle_SMTLIB.Sym "Real", []) = SOME \<^typ>\<open>Real.real\<close>
  | real_type_parser _ = NONE

fun real_term_parser (Flatbelle_SMTLIB.Dec (i, 0), []) = SOME (HOLogic.mk_number \<^typ>\<open>Real.real\<close> i)
  | real_term_parser (Flatbelle_SMTLIB.Sym "/", [t1, t2]) =
      SOME (\<^term>\<open>Rings.divide :: real => _\<close> $ t1 $ t2)
  | real_term_parser (Flatbelle_SMTLIB.Sym "to_real", [t]) = SOME (\<^term>\<open>Int.of_int :: int => _\<close> $ t)
  | real_term_parser _ = NONE

val _ = Theory.setup (Context.theory_map (
  Flatbelle_SMTLIB_Proof.add_type_parser real_type_parser #>
  Flatbelle_SMTLIB_Proof.add_term_parser real_term_parser))

val setup_builtins =
  Flatbelle_SMT_Builtin.add_builtin_typ Flatbelle_SMTLIB_Interface.smtlibC
    (\<^typ>\<open>real\<close>, K (SOME ("Real", [])), real_num) #>
  fold (Flatbelle_SMT_Builtin.add_builtin_fun' Flatbelle_SMTLIB_Interface.smtlibC) [
    (\<^Const>\<open>less \<^Type>\<open>real\<close>\<close>, "<"),
    (\<^Const>\<open>less_eq \<^Type>\<open>real\<close>\<close>, "<="),
    (\<^Const>\<open>uminus \<^Type>\<open>real\<close>\<close>, "-"),
    (\<^Const>\<open>plus \<^Type>\<open>real\<close>\<close>, "+"),
    (\<^Const>\<open>minus \<^Type>\<open>real\<close>\<close>, "-") ] #>
  Flatbelle_SMT_Builtin.add_builtin_fun Flatbelle_SMTLIB_Interface.smtlibC
    (Term.dest_Const \<^Const>\<open>times \<^Type>\<open>real\<close>\<close>, times)
end

(* setup *)

val _ = Theory.setup (Context.theory_map (
  setup_builtins)) 

end