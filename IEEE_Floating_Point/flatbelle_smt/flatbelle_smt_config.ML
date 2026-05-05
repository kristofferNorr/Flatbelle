(*  Title:      
    Author:     


*)

signature FLATBELLE_SMT_CONFIG =
sig
  (* solver *)
  type solver_info = {
    name: string,
    dummy: bool,
    flatbelle_default: bool,
    class: Proof.context -> Flatbelle_SMT_Util.class,
    available: unit -> bool,
    options: Proof.context -> string list}
  val add_solver: solver_info -> Context.generic -> Context.generic
  val select_solver: string -> Context.generic -> Context.generic
  val solver_of: Proof.context -> string
  val solver_class_of: Proof.context -> Flatbelle_SMT_Util.class
  val solver_options_of: Proof.context -> string list  

  (*options*)
  val problem_dest_file: string Config.T
  val proof_dest_file: string Config.T
  val nat_as_int: bool Config.T
end;

structure Flatbelle_SMT_Config : FLATBELLE_SMT_CONFIG =
struct

(* context data *)

type solver_info = {
  name: string,
  dummy: bool,
  flatbelle_default: bool,
  class: Proof.context -> Flatbelle_SMT_Util.class,
  available: unit -> bool,
  options: Proof.context -> string list};

structure FlatData = Generic_Data 
(
  type T = 
    (solver_info * string list) Symtab.table *  (*all solvers*)
    string option;   (*selected solver*)
    (*Cache_IO.cache option; FIXME: add when relevant*)
  val empty: T = (Symtab.empty, NONE);
  fun merge ((ss1, s1): T, (ss2, s2): T) = (Symtab.merge (K true) (ss1, ss2), merge_options (s1, s2));
)
                       
val get_solvers' = #1 o FlatData.get;
val get_solvers = get_solvers' o Context.Proof;
val get_solver =  #2 o FlatData.get o Context.Proof;

fun add_solver (info as {name, ...} : solver_info) context =
  let val map_solver = FlatData.map o apfst in
  map_solver (Symtab.update (name, (info, []))) context end;

fun select_solver name context =
  FlatData.map (apsnd (K (SOME name))) context

fun no_solver_err () = error "No SMT solver selected";

fun solver_of ctxt =
  case get_solver ctxt of 
    SOME name => name
  | NONE => error "No Flattener selected";

fun solver_info_of default select ctxt = 
  (case get_solver ctxt of
    NONE => default ()
  | SOME name => select (Symtab.lookup (get_solvers ctxt) name));

fun solver_class_of ctxt = 
  let fun class_of ({class, ...}: solver_info, _) = class ctxt 
  in solver_info_of no_solver_err (class_of o the) ctxt end;

fun solver_options_of ctxt =
  let
    fun all_options NONE = []
      | all_options (SOME ({options, ...} : solver_info, opts)) =
          opts @ options ctxt
  in solver_info_of (K []) all_options ctxt end;

(* options *)

val problem_dest_file = Attrib.setup_config_string \<^binding>\<open>flatbelle_problem_dest_dir\<close> (K "");
val proof_dest_file = Attrib.setup_config_string \<^binding>\<open>flatbelle_proof_dest_dir\<close> (K "");
val nat_as_int = Attrib.setup_config_bool \<^binding>\<open>flatbelle_nat_as_int\<close> (K false);
  
end;
