(*  Title:      
    Author:     Kristoffer Norrman


*)

signature FLATBELLE_SMT_SOLVER =
sig
  (* configuration *)
  datatype outcome = Unsat | Sat | Unknown | Time_Out

  type parsed_proof = 
    {outcome: SMT_Failure.failure option,
     fact_ids: (int * ((string * ATP_Problem_Generate.stature) * thm)) list option}
  
  type solver_config = {
    name: string,
    class: Proof.context -> Flatbelle_SMT_Util.class,
    available: unit -> bool,
    command: unit -> string list,
    options: Proof.context -> string list,
    smt_options: (string * string) list,
    outcome: string -> string list -> outcome * string list,
    parse_proof: unit option,
    replay: unit option}
     
  (* registry *)
  val add_solver: {dummy: bool, solver_default: bool} -> solver_config -> theory -> theory
  (* filter *)
  val flatbelle_smt_filter : Proof.context -> thm -> 
    ((string * ATP_Problem_Generate.stature) * thm) list -> int -> string list -> parsed_proof
   
  (* tactic *)

  (* solver information *)
  type solver_info = {
    command: unit -> string list,
    smt_options: (string * string) list,
    parse_proof: unit,  (*FIXME: when we need to verify/replay proof.*)
    replay: unit (*FIXME: when we need to verify/replay proofs.*)} 

end;

structure Flatbelle_SMT_Solver : FLATBELLE_SMT_SOLVER =
struct

(* interface to external solvers *)
local
  fun run ctxt name input = 
  (case Config.get ctxt Flatbelle_SMT_Config.problem_dest_file of
    "" => ()
  | path => 
    let val in_path = Path.ext "smt_in" (Path.explode path) in
      Pretty.writeln(Pretty.str("File is written to: " ^ @{make_string} in_path));
      File.write in_path input
    end)
in

fun run_solver ctxt name cmd input = Flatbelle_Util.TODO "run_solver"

(* Here we will invoke SMT translation plus other stuff*)
fun invoke name command options smt_options ithms ctxt =
  let
    val comments = [implode_space options]
    val input = 
      ithms
      |> Flatbelle_SMT_Translate.translate ctxt name smt_options comments
  in
    run ctxt name ("; As of now it is a bit unclear how exactly a correct SMT-LIB 3 model is formatted.\n" ^
                   "; Hence, this will be corrected once the standard is released.\n"^ input)
  end    

end

(* configuration *)
datatype outcome = Unsat | Sat | Unknown | Time_Out

type parsed_proof = { (*TODO: integrate it later on in the project.*)
  outcome: SMT_Failure.failure option,
  fact_ids: (int * ((string * ATP_Problem_Generate.stature) * thm)) list option}

type solver_config = {
  name: string,
  class: Proof.context -> Flatbelle_SMT_Util.class,
  available: unit -> bool,
  command: unit -> string list,
  options: Proof.context -> string list,
  smt_options: (string * string) list,
  outcome: string -> string list -> outcome * string list,
  parse_proof: unit option,
  replay: unit option}


(* check well-sortedness *)
\<comment> \<open> This was a copy and pasted from smt_solver.ML\<close>
val has_topsort = Term.exists_type (Term.exists_subtype (fn
    TFree (_, []) => true
  | TVar (_, []) => true
  | _ => false))

(* top sorts cause problems with atomization *)
\<comment> \<open> This was a copy and pasted from smt_solver.ML\<close>
fun check_topsort ctxt thm =
  if has_topsort (Thm.prop_of thm) then (writeln("TODO: message about assumptions dropped."); TrueI) else thm


(* registry *)
type solver_info = {
  command: unit -> string list,
  smt_options: (string * string) list,
  parse_proof: unit,  (*FIXME: when we need to verify/replay proof.*)
  replay: unit (*FIXME: when we need to verify/replay proofs.*)} 

structure Flatteners = Generic_Data
(
  type T = solver_info Symtab.table
  val empty = Symtab.empty
  fun merge data = Symtab.merge (K true) data
)

fun add_solver {dummy: bool, solver_default: bool} 
      ({name, class, available, command, options, smt_options, outcome,...} : solver_config) =
  let 
    val info = {name = name, dummy = dummy, flatbelle_default = solver_default,
      class = class, available = available, options = options}
    val solver_info = {command = fn () => ["dummy", "commands"], smt_options=smt_options, parse_proof = (), replay = ()}
  in
    Context.theory_map (Flatteners.map (Symtab.update_new (name, solver_info))) #>
    Context.theory_map (Flatbelle_SMT_Config.select_solver name) #> (* this (or similar) should be in systems when defining smt methods *)
    Context.theory_map (Flatbelle_SMT_Config.add_solver info)
  end

fun get_info ctxt name = the (Symtab.lookup (Flatteners.get (Context.Proof ctxt)) name);

fun name_and_info_of ctxt = 
  let val name = Flatbelle_SMT_Config.solver_of ctxt 
  in (name, get_info ctxt name) end


(* filter (for flatbelle) *)

fun flatbelle_smt_filter ctxt goal xfacts i options =
  let
    val ({context = ctxt, prems, concl, ...}, _) = Subgoal.focus ctxt i NONE goal
    
    fun negate ct = Thm.dest_comb ct ||> Thm.apply \<^cterm>\<open>Not\<close> |-> Thm.apply
    val cprop =
      (case try negate (Thm.rhs_of (SMT_Normalize.atomize_conv ctxt concl)) of
        SOME ct => ct
      | NONE => raise SMT_Failure.SMT (SMT_Failure.Other_Failure "cannot atomize goal"))

    val conjecture = Thm.assume cprop
       
    (* has type ((int * Flatbelle_SMT_Util.role) thm) list, list of indexed theorems, representing assumptions and goals to be translated.*)
    val conjecture = Thm.assume cprop
    val thms = (Flatbelle_SMT_Util.Conjecture, conjecture) :: 
          map (pair Flatbelle_SMT_Util.Hypothesis) prems @
          map (pair Flatbelle_SMT_Util.Axiom o snd) xfacts
          |> map (apsnd (check_topsort ctxt))
    val ithms = Flatbelle_SMT_Normalize.normalize ctxt thms
    val (name, {command, smt_options, parse_proof, ...}) = name_and_info_of ctxt
    val invoked = invoke name command options smt_options ithms ctxt
  in
    ({outcome = NONE, fact_ids = NONE} : parsed_proof)
  end
end;