(*  Title:      
    Author:     Kristoffer Norrman


*)

signature FLATBELLE_FLATTENER =
sig
  type atp_failure = ATP_Proof.atp_failure
  type stature = ATP_Problem_Generate.stature
  type type_enc = ATP_Problem_Generate.type_enc
  type fact = Flatbelle_Fact.fact

  datatype mode = Auto_Try | Try | Normal | Minimize | MaSh

  datatype induction_rules = Include | Exclude | Instantiate
  val maybe_filter_out_induction_rules: induction_rules -> fact list -> fact list

  type params =
    {debug : bool,
     verbose : bool,
     overlord : bool,
     file_name: string option,
     file_path: string option,
     flatteners : string list,
     type_enc : string option,
     induction_rules : induction_rules option,
     max_facts : int option,
     slices: int}

  type flattener_problem = 
    {comment : string,
     state : Proof.state,
     goal : thm,
     subgoal : int,
     subgoal_count : int,
     factss : (string * fact list) list}

  type flattener_result =
    {outcome : atp_failure option,
     used_facts : (string * stature) list,
     used_from : Flatbelle_Fact.fact list}
  
  type flattener = params -> flattener_problem -> flattener_result

  val overlord_file_location_of_flattener : string -> string * string
end;

structure Flatbelle_Flattener : FLATBELLE_FLATTENER =
struct
type atp_failure = ATP_Proof.atp_failure
type stature = ATP_Problem_Generate.stature
type type_enc = ATP_Problem_Generate.type_enc

type fact = Flatbelle_Fact.fact

datatype mode = Auto_Try | Try | Normal | Minimize | MaSh

datatype induction_rules = Include | Exclude | Instantiate
fun maybe_filter_out_induction_rules induction_rules : fact list -> fact list = 
  raise Flatbelle_Util.TODO "TODO: Flatbelle_Flattener.maybe_filter_out_induction_rules"

type params =
  {debug : bool,
   verbose : bool,
   overlord : bool,
   file_name: string option,
   file_path: string option,
   flatteners : string list,
   type_enc : string option,
   induction_rules : induction_rules option,
   max_facts : int option,
   slices : int}

type flattener_problem = 
  {comment : string,
   state : Proof.state,
   goal : thm,
   subgoal : int,
   subgoal_count : int,
   factss : (string * fact list) list}

type flattener_result =
  {outcome : atp_failure option,
   used_facts : (string * stature) list,
   used_from : Flatbelle_Fact.fact list}

type flattener = params -> flattener_problem -> flattener_result
   
fun overlord_file_location_of_flattener flattener = (getenv "ISABELLE_HOME_USER", "prob_" ^ flattener)

end;