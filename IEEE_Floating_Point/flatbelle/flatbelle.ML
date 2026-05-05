(*  Title:      
    Author:     Kristoffer Norrman


*)

signature FLATBELLE =
sig
  type stature = ATP_Problem_Generate.stature
  type fact = Flatbelle_Fact.fact
  type mode = Flatbelle_Flattener.mode
  type params = Flatbelle_Flattener.params
  type flattener = Flatbelle_Flattener.flattener
  type flattener_result = Flatbelle_Flattener.flattener_result

  datatype flatbelle_outcome = 
    SH_Some of flattener_result
  | SH_Unknown
  | SH_Timeout
  | SH_ResourcesOut
  | SH_None
  
  val short_string_of_flatbelle_outcome : flatbelle_outcome -> string
  val flatbelle_run : params -> mode -> (string -> unit) option -> int -> Proof.state -> 
        bool * (flatbelle_outcome * string)
end;

structure Flatbelle : FLATBELLE =
struct

type stature = ATP_Problem_Generate.stature
type fact = Flatbelle_Fact.fact
type mode = Flatbelle_Flattener.mode
type params = Flatbelle_Flattener.params

type flattener = Flatbelle_Flattener.flattener

type flattener_result = Flatbelle_Flattener.flattener_result

datatype flatbelle_outcome = 
    SH_Some of flattener_result
  | SH_Unknown
  | SH_Timeout
  | SH_ResourcesOut
  | SH_None

fun short_string_of_flatbelle_outcome (SH_Some _) = "some"
  | short_string_of_flatbelle_outcome SH_Unknown = "unknown"
  | short_string_of_flatbelle_outcome SH_TimeOut = "timeout"
  | short_string_of_flatbelle_outcome SH_ResourcesOut = "resources_out"
  | short_string_of_flatbelle_outcome SH_None = "none"

fun get_flattener name = Flatbelle_Flattener_SMT.run_smt_flattener name

fun fact_count facts = Facts.fold_static (K (Integer.add 1)) facts 0

fun flatbelle_run (params as {induction_rules, max_facts,...}) mode writeln_result i state = 
  case Flatbelle_Util.subgoal_count state of
    0 => (error "No subgoals")
  | n =>  
    let   
      val print = if mode = Flatbelle_Flattener.Normal andalso is_none writeln_result then writeln else K ()

      val ctxt = Proof.context_of state
      val inst_inducts = induction_rules = SOME Flatbelle_Flattener.Instantiate
      val {facts = chained_thms, goal, ...} = Proof.goal state
      val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal goal i ctxt
      val fact_override = {add = [], del = [], only = false}

      val _ = print "Flattening..."
      val ({elapsed,...}, all_facts) = Timing.timing (Flatbelle_Fact.nearly_all_facts_of_context
            ctxt inst_inducts fact_override chained_thms hyp_ts) concl_t
      
      val problem = 
        {comment = "Flabelle_Flattener.problem #comment", state = state, goal = goal, subgoal = i, subgoal_count = n, 
          factss = []}
      val result = SH_Some (get_flattener "Test" params problem)
    in
      (true, (result, "TODO: add results when more integrated."))
    end
end;