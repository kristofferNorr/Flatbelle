(*  Title:      
    Author:     Kristoffer Norrman


*)

signature FLATBELLE_COMMANDS =
sig
  type params = Flatbelle_Flattener.params

  val default_params : Proof.context -> (string * string) list -> params
end;

structure Flatbelle_Commands : FLATBELLE_COMMANDS =
struct

val flatN = "flattening"
type params = Flatbelle_Flattener.params


(*** parameters ***)

val default_prover = "dummy"

type raw_params = string * string list

val default_default_params = 
  [("debug","false"),
   ("verbose", "false"),
   ("overlord", "false"),
   ("file_name", "smart"),
   ("file_path", "smart"),
   ("type_enc", "smart"),
   ("induction_rules", "smart"),
   ("max_facts", "smart"),
   ("slices", string_of_int 24)]

(* (Taken from og file) Ensures that type encodings such as "mono_native?" and "poly_guards!!" are
   read correctly. *)
val implode_param = ATP_Util.strip_spaces_except_between_idents o implode_space

structure Data = Generic_Data
(
  type T = raw_params list
  val empty = default_default_params |> map (apsnd single)
  fun merge data = AList.merge (op =) (K true) data
)
(* The first ATP of the list is used by Auto Sledgehammer. *)
fun default_provers_param_value ctxt = "dummy"

fun default_raw_params ctxt =
  Data.get (Context.Proof ctxt)
  |> fold (AList.default (op =))
     [("TODO", [""])]

fun extract_params mode default_params override_params =
  let
    val raw_params = rev override_params @ rev default_params
    val lookup = Option.map implode_param o AList.lookup (op =) raw_params
    val lookup_string = the_default "" o lookup
    
    fun general_lookup_bool option default_value name =
      (case lookup name of
        SOME s => Flatbelle_Util.parse_bool_option option name s 
      | NONE => default_value)
    fun lookup_option lookup' name = 
      (case lookup name of
        SOME "smart" => NONE
      | _ => SOME (lookup' name))
    fun lookup_int name =
      (case lookup name of
        NONE => 0
      | SOME s =>
        (case Int.fromString s of
          SOME n => n
        | NONE => error ("Parameter " ^ quote name ^ " must be assigned an integer value")))
      
    val lookup_bool = the o general_lookup_bool false (SOME false)
    
    val debug = mode <> Flatbelle_Flattener.Auto_Try andalso lookup_bool "debug"
    val verbose = debug orelse (mode <>  Flatbelle_Flattener.Auto_Try andalso lookup_bool "verbose")
    val type_enc = 
      if mode = Flatbelle_Flattener.Auto_Try then
        NONE
      else
        (case lookup_string "type_enc" of
          "smart" => NONE
        | s => (ATP_Problem_Generate.type_enc_of_string ATP_Problem_Generate.Strict; SOME s))
    val file_name = lookup_option lookup_string "file_name"
    val file_path = lookup_option lookup_string "file_path"
    val overlord = (case (file_name, file_path) of 
                      (NONE, NONE) => lookup_bool "overlord"
                    | _ => true)
    val flatteners = [] (*TODO: add standarnd way to listing flatterns (provers) that will be used*)
    val induction_rules = NONE
    val max_facts = lookup_option lookup_int "max_facts"
    val slices = if mode = Flatbelle_Flattener.Auto_Try then 1 else Int.max (1, lookup_int "slices")
  in
    {debug = debug, verbose = verbose, overlord = overlord,
     file_name = file_name, file_path = file_path, 
     flatteners = flatteners, type_enc = type_enc,
     induction_rules = induction_rules,
     max_facts = max_facts, slices = slices}
  end

fun get_params mode = extract_params mode o default_raw_params
fun default_params ctxt = get_params Flatbelle_Flattener.Normal ctxt o map (apsnd single)

(* Flattening things  *)
val silence_state =
  Proof.map_contexts (Try0_HOL.silence_methods)

fun flattening override_params writeln_result subcommand state0 =
  let
    val state = silence_state (Toplevel.proof_of state0)
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state    
    val {goal=goal, facts=facts,...} = Proof.goal state                        
    val params  = get_params Flatbelle_Flattener.Normal ctxt override_params
  in
    ignore (Flatbelle.flatbelle_run params Flatbelle_Flattener.Normal writeln_result  1 state)
  end

(* Parsing and command setup  *)

val parse_query_bang = \<^keyword>\<open>?\<close> || \<^keyword>\<open>!\<close> || \<^keyword>\<open>!!\<close> 
val parse_key = Scan.repeat1 (Parse.embedded || parse_query_bang) >> implode_param
val parse_value = Scan.repeat1 (Parse.name || Parse.float_number || parse_query_bang || Parse.path)
val parse_param = parse_key -- Scan.optional (\<^keyword>\<open>=\<close> |-- parse_value) []
val parse_raw_params = Scan.optional (Args.bracks (Parse.list parse_param)) []
val parse_params = parse_raw_params >> map (apsnd implode_param)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>flattening\<close>
    "Flattening lemmas"
    (Scan.optional Parse.name flatN -- parse_raw_params >>
      (fn (subcommand, params) =>
        Toplevel.keep_proof
          (flattening params NONE subcommand)))


val _ =
  Query_Operation.register {name = flatN, pri = 0}
    (fn {state = st, args, writeln_result, ...} =>
      (case try Toplevel.proof_of st of
        SOME state =>
          let
            val override_params =  [("overlord", ["false"])]            
          in
            flattening override_params (SOME writeln_result) flatN st
          end
      | NONE => error "")) (*FIXME: add message*)

end;