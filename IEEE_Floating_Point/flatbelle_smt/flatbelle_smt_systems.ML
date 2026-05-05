(*  Title:      HOL/Tools/SMT/smt_systems.ML
    Author:     Sascha Boehme, TU Muenchen

Setup SMT solvers.
*)

signature FLATBELLE_SMT_SYSTEMS =
sig
  val dummy : bool Config.T
end;

structure Flatbelle_SMT_Systems: FLATBELLE_SMT_SYSTEMS =
struct

(* helper functions *)

fun make_available name () = getenv (name ^ "_SOLVER") <> ""

fun make_command name () = [getenv (name ^ "_SOLVER")]

fun outcome_of unsat sat unknown timeout solver_name line =
  if String.isPrefix unsat line then Flatbelle_SMT_Solver.Unsat
  else if String.isPrefix sat line then Flatbelle_SMT_Solver.Sat
  else if String.isPrefix unknown line then Flatbelle_SMT_Solver.Unknown
  else if String.isPrefix timeout line then Flatbelle_SMT_Solver.Time_Out
  else error ""

(* Dummy SMT solvers *)

val dummy = Attrib.setup_config_bool \<^binding>\<open>dummy_solver\<close> (K false)

val dummy_smtlib: Flatbelle_SMT_Solver.solver_config =
  {
    name = "dummy_smtlib",
    class = K SMTLIB_Interface.hosmtlibC,
    available = make_available "DUMMY_SMTLIB",
    command = make_command "DUMMY_SMTLIB",
    options = K [],
    smt_options = [],
    outcome = fn (_ : string) => fn (_ : string list) => (Flatbelle_SMT_Solver.Unsat, [""]),
    parse_proof = NONE,
    replay = NONE }

(* smt tactic *)

(*
val _ = 
  Theory.setup \<^binding>\<open>smt3\<close> 
    (Scan.list parse_smt_options -- Attrib.thms >> (METHOD oo smt_method))
    "()"
*)

(* overall setup *)

val _ = Theory.setup (
  Flatbelle_SMT_Solver.add_solver {dummy = true, solver_default = false} dummy_smtlib) 

end;