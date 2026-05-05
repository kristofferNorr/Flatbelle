(*  Title:      
    Author:     Kristoffer Norrman


*)

signature FLATBELLE_UTIL =
sig
  val flatbelleN : string
  val log2 : real -> real
  val serial_commas : string -> string list -> string list
  val simplify_spaces: string -> string
  val subgoal_count : Proof.state -> int
  val parse_bool_option: bool -> string -> string -> bool option
  (* TODO exception*)
  val hackish_string_of_term : Proof.context -> term -> string
  exception TODO of string  
end;

structure Flatbelle_Util : FLATBELLE_UTIL =
struct

(* TODO exception*)
exception TODO of string  

val flatbelleN = "flatbelle"

val log10_2 = Math.log10 2.0
fun log2 n = Math.log10 n / log10_2

val serial_commas = Try.serial_commas
val simplify_spaces = ATP_Util.strip_spaces false (K true)

val subgoal_count = Logic.count_prems o Thm.prop_of o #goal o Proof.goal;

fun thms_of_name ctxt name = 
  let
    val keywords = Thy_Header.get_keywords' ctxt
  in
    Token.explode keywords Position.start name
    |> filter Token.is_proper
    |> Source.of_list
    |> Source.source' (Context.Proof ctxt) Token.stopper Attrib.multi_thm
    |> Source.exhaust
  end

fun parse_bool_option option name s =
  (case s of
    "smart" => if option then NONE else raise Option.Option
  | "false" => SOME false
  | "true" => SOME true
  | "" => SOME true
  | _ => raise Option.Option)
  handle Option.Option => error "FIXME: informative error msg."

fun hackish_string_of_term ctxt =
  (* FIXME: map_aterms (fn Free (s, T) => Free (if Name.is_internal s then "_" else s, T) | t => t)
  #> *) Syntax.pretty_term ctxt
  #> Pretty.pure_string_of
  #> simplify_spaces

end;