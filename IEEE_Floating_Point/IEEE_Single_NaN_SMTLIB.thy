(* Author: Tjark Weber, Uppsala University
*)

section \<open>Translation of the IEEE model (with a single NaN value) into SMT-LIB's floating point theory\<close>

theory IEEE_Single_NaN_SMTLIB
  imports
    IEEE_Single_NaN
    keywords
    "flattening" :: diag
begin

text \<open>Mini version of sledgehammer. The builtin sledgehammer (HOL/Tools/Sledgehammer/) and SMT 
  (HOL/Tools/SMT/) code does not currently support dependent types. The code below serves, as of 
  now, as a tool to generate benchmarks for the upcoming SMT-LIB 3. Since declaring dependent types 
  requires fundamental changes in the source code, this provides full control of changes needed.\<close>

ML_file \<open>flatbelle/flatbelle_util.ML\<close>

ML_file \<open>flatbelle_smt/flatbelle_smt_util.ML\<close>
ML_file \<open>flatbelle_smt/flatbelle_smt_config.ML\<close>
ML_file \<open>flatbelle_smt/flatbelle_smt_builtin.ML\<close>
ML_file \<open>flatbelle_smt/flatbelle_smt_normalize.ML\<close>
ML_file \<open>flatbelle_smt/flatbelle_smt_datatypes.ML\<close>
ML_file \<open>flatbelle_smt/flatbelle_smt_translate.ML\<close>
ML_file \<open>flatbelle_smt/flatbelle_smtlib.ML\<close>
ML_file \<open>flatbelle_smt/flatbelle_smtlib_interface.ML\<close>
ML_file \<open>flatbelle_smt/flatbelle_smtlib_proof.ML\<close>
ML_file \<open>flatbelle_smt/flatbelle_smtlib_real.ML\<close>
ML_file \<open>flatbelle_smt/flatbelle_smt_solver.ML\<close>
ML_file \<open>flatbelle_smt/flatbelle_smt_systems.ML\<close>


ML_file \<open>flatbelle/flatbelle_fact.ML\<close>
ML_file \<open>flatbelle/flatbelle_flattener.ML\<close>
ML_file \<open>flatbelle/flatbelle_flattener_smt.ML\<close>
ML_file \<open>flatbelle/flatbelle.ML\<close>
ML_file \<open>flatbelle/flatbelle_commands.ML\<close>

ML_file \<open>flatbelle/mirabelle_flatbelle.ML\<close>
ML_file \<open>flatbelle_smt_float.ML\<close>

text \<open>SMT setup. Note that an interpretation of floating-point arithmetic in SMT-LIB allows external
  SMT solvers that support the SMT-LIB floating-point theory to find more proofs, but---in the
  absence of built-in floating-point automation in Isabelle/HOL---significantly \emph{reduces}
  Sledgehammer's proof reconstruction rate. Until such automation becomes available, you probably
  want to use the interpreted translation only if you intend to use the external SMT solvers as
  trusted oracles.\<close>

(*  
lemma float_cases:
  "is_nan a \<and> is_infinity b \<Longrightarrow> a \<noteq> b"
  for a :: "('x::len,'y::len) floatT"
  and b :: "('x::len,'y::len) floatT"
  flattening 

lemma sterbenz: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> (valof y)/2 \<le> valof x \<and> valof x \<le> 2*(valof y) \<Longrightarrow>
    valof x - valof y = valof (fsub mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  flattening[file_path="~/", file_name=sterbenz] by cheat

lemma poly_test:
  "k = j\<Longrightarrow> n < m"
  for x y :: "('e::len,'f::len) floatSingleNaN"
  flattening[overlord] by cheat


*)
ML \<open>val _ = Theory.setup (Method.setup \<^binding>\<open>cheat\<close> (Scan.succeed (K (Method.cheating true))) "cheat")\<close>
type_synonym ('e,'f) floatT = "('e, 'f) floatSingleNaN" 

lemma poly_test:
  "k = j\<Longrightarrow> n < m"
  for x y :: "('e::len,'f::len) floatT"
  flattening[overlord] by cheat

end
