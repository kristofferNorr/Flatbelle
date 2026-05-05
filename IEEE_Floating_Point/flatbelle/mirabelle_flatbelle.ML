(*  Title:      
    Author:     

Mirabelle action: "flatbelle".
*)

structure Mirabelle_Flatbelle: MIRABELLE_ACTION =
struct

val check_trivialK = "check_trivial" (*=BOOL: check if goals are "trivial"*)
val exhaustive_preplayK = "exhaustive_preplay" (*=BOOL: show exhaustive preplay data*)
val keep_probsK = "keep_probs" (*=BOOL: keep temporary problem files created by flatbelle*)
val keep_proofsK = "keep_proofs" (*=BOOL: keep temporary proof files created by ATPs*)


(*defaults used in this Mirabelle action*)
val check_trivial_default = false
val exhaustive_preplay_default = false
val keep_probs_default = true
val keep_proofs_default = false

val str0 = string_of_int o the_default 0

fun run_sh params keep pos state =
  \<^try>\<open>
    let 
      fun set_file_name (SOME (dir, keep_probs, keep_proofs)) = 
        let
          val file_name = "prob_" ^ 
            StringCvt.padLeft #"0" 5 (str0 (Position.line_of pos)) ^ "_" ^
            StringCvt.padLeft #"0" 6 (str0 (Position.offset_of pos))
          fun mk_smt_file () = dir ^ "/" ^ file_name ^ "__" ^ serial_string ()
        in
          keep_probs ? Config.put Flatbelle_SMT_Config.problem_dest_file (mk_smt_file ())
        end
        | set_file_name NONE = I
     val state' = state |> Proof.map_context (set_file_name keep)

     val ((_, (flatbelle_outcome, msg)), cpu_time) = Mirabelle.cpu_time (fn () =>
       Flatbelle.flatbelle_run params Flatbelle_Flattener.Normal NONE 1 state') ()
    in
      (flatbelle_outcome, msg, cpu_time)
    end
    catch ERROR msg => (Flatbelle.SH_Unknown, "error: ", 0)
\<close>

fun flatbelle_run params output_dir keep_probs keep_proofs thy_index pos pre =
  let 
    val keep =
      if keep_probs orelse keep_proofs then
        let 
          val thy_long_name = Context.theory_long_name (Proof.theory_of pre)
          val session_name = Long_Name.qualifier thy_long_name
          val thy_name = Long_Name.base_name thy_long_name
          val subdir = StringCvt.padLeft #"0" 4 (string_of_int thy_index) ^ "_" ^ thy_name
        in
          Path.append (Path.append output_dir (Path.basic session_name)) (Path.basic subdir)
          |> Isabelle_System.make_directory
          |> Path.implode
          |> (fn dir => SOME (dir, keep_probs, keep_proofs))
        end
      else NONE
    val (flatbelle_outcome, msg, cpu_time) = run_sh params keep pos pre
    val outcome_msg = "FIXME: (SH " ^ string_of_int cpu_time ^ " ms ...) "
  in 
    (flatbelle_outcome, outcome_msg ^ Protocol_Message.clean_output msg) 
  end          

fun make_action ({arguments: Properties.T, timeout, output_dir, label, name,...}: Mirabelle.action_context) =
  let 
    val keep_probs = Mirabelle.get_bool_argument arguments (keep_probsK, keep_probs_default)
    val keep_proofs = Mirabelle.get_bool_argument arguments (keep_proofsK, keep_proofs_default)

    val init_msg = "Now we're running!" 
 
    fun run ({theory_index, pos, pre,...}: Mirabelle.command) = 
      let val goal = Thm.major_prem_of (#goal (Proof.goal pre)) in
        if can Logic.dest_conjunction goal orelse can Logic.dest_equals goal then
          ""
        else
          let
            val params = Flatbelle_Commands.default_params (Proof.context_of pre) arguments 
            val (outcome, log) = 
              flatbelle_run params output_dir keep_probs keep_proofs theory_index pos pre
          in
            log 
            |> Symbol.trim_blanks
            |> prefix_lines (Flatbelle.short_string_of_flatbelle_outcome outcome ^ " ")
          end
        end
  in (init_msg , {run = run, finalize = K "TODO"}) end

val _ = Mirabelle.register_action "flattening" make_action  

end