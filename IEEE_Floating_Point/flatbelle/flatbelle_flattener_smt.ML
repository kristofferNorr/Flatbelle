(*  Title:      
    Author:     Kristoffer Norrman


*)

signature FLATBELLE_FLATTENER_SMT =
sig
  type params = Flatbelle_Flattener.params
  type flattener_problem = Flatbelle_Flattener.flattener_problem
  type flattener = Flatbelle_Flattener.flattener
  
  val run_smt_flattener : string -> flattener
end;

structure Flatbelle_Flattener_SMT : FLATBELLE_FLATTENER_SMT =
struct

type params = Flatbelle_Flattener.params
type flattener_problem = Flatbelle_Flattener.flattener_problem
type flattener = Flatbelle_Flattener.flattener

fun flatbelle_smt_filter name ({overlord, type_enc, file_name, file_path,...} : params) state goal i facts options =
  let 
    val (nat_as_int) =
      (case type_enc of
        SOME s => (SOME(String.isSubstring "arith" s))
      | NONE => (NONE))
    fun repair_context ctxt = ctxt
      |> (case nat_as_int of 
           SOME nat_as_int => Config.put Flatbelle_SMT_Config.nat_as_int nat_as_int
         | NONE => I)
      |> (if overlord then
          let
            val (path0, name0) = Flatbelle_Flattener.overlord_file_location_of_flattener name
            fun valid_path s = if String.isSuffix "/" s then 
                  String.substring (s, 0, size s - 1) else s
            fun file_base (SOME(path'), SOME(name')) = valid_path path' ^ "/" ^ name' ^ "_" ^ name
              | file_base (NONE, SOME(name')) = path0 ^ "/" ^ name' ^ "_" ^ name
              | file_base (SOME(path'), NONE) = valid_path path' ^ "/" ^ name0
              | file_base _ = path0 ^ "/" ^ name0
          in
            Config.put Flatbelle_SMT_Config.problem_dest_file (file_base (file_path, file_name)) #>
            Config.put Flatbelle_SMT_Config.proof_dest_file (file_base (file_path, file_name))
          end
        else
          I)
      |> Config.put Flatbelle_SMT_Systems.dummy false

    val state = Proof.map_context (repair_context) state
    val ctxt = Proof.context_of state
      
    val filter_result as {outcome,...} = 
      \<^try>\<open>Flatbelle_SMT_Solver.flatbelle_smt_filter ctxt goal facts i  options
         catch exn => {outcome = NONE, fact_ids = NONE}\<close>
  in
    {outcome = outcome, filter_result = filter_result, used_from = facts, run_time = 0}
  end

fun run_smt_flattener name 
    (params as ({overlord, type_enc,...} : params))   
    ({state, goal, subgoal, subgoal_count, factss,...} : flattener_problem) = 
  let
    val {outcome, filter_result = filter_result, used_from, run_time} =
      flatbelle_smt_filter name params state goal subgoal_count [] ["No options"]
  in
    {outcome = NONE, used_facts = [], used_from = []}
  end

end;