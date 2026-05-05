(*  Author:     Olle Torstensson, Uppsala University
    Author:     Tjark Weber, Uppsala University
*)

section \<open>Benchmark problems to evaluate the translation from the IEEE model (with a single NaN value) into SMT-LIB's floating point theory\<close>

theory Benchmarks
  (*imports IEEE_Floating_Point.IEEE_Single_NaN*)
  imports IEEE_Floating_Point.IEEE_Single_NaN_SMTLIB
begin

ML \<open>val _ = Theory.setup (Method.setup \<^binding>\<open>cheat\<close> (Scan.succeed (K (Method.cheating true))) "cheat")\<close>


(*half precision*)
(*type_synonym ('e,'f) floatT = "(5,10) floatSingleNaN"*)

(*single precision*)
type_synonym ('e,'f) floatT = "(8,23) floatSingleNaN"

(*double precision*)
(*type_synonym ('e,'f) floatT = "(11,52) floatSingleNaN"*)

(*quadruple precision*)
(*type_synonym ('e,'f) floatT = "(15,112) floatSingleNaN"*)

(*polymorphic*)
(*type_synonym ('e,'f) floatT = "('e,'f) floatSingleNaN"*)


subsection \<open>Classification\<close>

text \<open>Adapted from IEEE\_Floating\_Point/IEEE\_Properties.thy.\<close>

lemma float_cases:
  "is_nan x \<or> is_infinity x \<or> is_normal x \<or> is_subnormal x \<or> is_zero x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_cases_finite: "is_nan x \<or> is_infinity x \<or> is_finite x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_zero1: "is_zero (0::('e::len,'f::len) floatT)"
  by cheat

lemma float_zero2: "is_zero (- x) \<longleftrightarrow> is_zero x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_distinct1: "\<not> (is_nan x \<and> is_infinity x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_distinct2: "\<not> (is_nan x \<and> is_normal x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_distinct3: "\<not> (is_nan x \<and> is_subnormal x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_distinct4: "\<not> (is_nan x \<and> is_zero x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_distinct5: "\<not> (is_infinity x \<and> is_normal x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_distinct6: "\<not> (is_infinity x \<and> is_subnormal x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_distinct7: "\<not> (is_infinity x \<and> is_zero x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_distinct8: "\<not> (is_normal x \<and> is_subnormal x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_distinct9: "\<not> (is_subnormal x \<and> is_zero x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma subnormal_imp_not_zero: "is_subnormal x \<Longrightarrow> \<not>is_zero x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma normal_imp_not_zero: "is_normal x \<Longrightarrow> \<not>is_zero x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma normal_imp_not_subnormal: "is_normal x \<Longrightarrow> \<not>is_subnormal x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma subnormal_zero: "\<not>is_subnormal (0::('e::len,'f::len) floatT)"
  by cheat

lemma subnormal_mzero: "\<not>is_subnormal (minus_zero::('e::len,'f::len) floatT)"
  by cheat

lemma normal_zero: "\<not>is_normal (0::('e::len,'f::len) floatT)"
  by cheat

lemma normal_mzero: "\<not>is_normal (minus_zero::('e::len,'f::len) floatT)"
  by cheat

lemma float_distinct_finite1: "\<not> (is_nan x \<and> is_finite x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_distinct_finite2: "\<not> (is_infinity x \<and> is_finite x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma finite_infinity: "is_finite x \<Longrightarrow> \<not> is_infinity x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma finite_nan: "is_finite x \<Longrightarrow> \<not> is_nan x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma is_finite_nonempty: "{x::('e::len,'f::len) floatT. is_finite x} \<noteq> {}"
  by cheat

lemma is_infinity_cases:
  "is_infinity x \<Longrightarrow> x = plus_infinity \<or> x = minus_infinity"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma is_zero_cases: "is_zero x \<Longrightarrow> x = 0 \<or> x = - 0"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma infinite_infinity: "\<not> is_finite (plus_infinity::('e::len,'f::len) floatT)"
  by cheat

lemma infinite_minfinity: "\<not> is_finite (minus_infinity::('e::len,'f::len) floatT)"
  by cheat

lemma nan_not_finite: "is_nan x \<Longrightarrow> \<not> is_finite x"
  for x :: "('e::len,'f::len) floatT"
  by cheat


subsection \<open>Comparison\<close>

text \<open>Adapted from IEEE\_Floating\_Point/IEEE\_Properties.thy.\<close>

lemma float_lt:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> flt x y \<longleftrightarrow> valof x < valof y"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma float_eq:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> feq x y \<longleftrightarrow> valof x = valof y"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma float_le:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> fle x y \<longleftrightarrow> valof x \<le> valof y"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma float_eq_refl: "feq x x \<longleftrightarrow> \<not> is_nan x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_lt_trans: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> is_finite z \<Longrightarrow> flt x y \<Longrightarrow> flt y z \<Longrightarrow> flt x z"
  for x y z :: "('e::len,'f::len) floatT"
  by cheat

lemma float_le_less_trans: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> is_finite z \<Longrightarrow> fle x y \<Longrightarrow> flt y z \<Longrightarrow> flt x z"
  for x y z :: "('e::len,'f::len) floatT"
  by cheat

lemma float_le_trans: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> is_finite z \<Longrightarrow> fle x y \<Longrightarrow> fle y z \<Longrightarrow> fle x z"
  for x y z :: "('e::len,'f::len) floatT"
  by cheat

lemma float_le_neg: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> \<not> flt x y \<longleftrightarrow> fle y x"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma float_le_infinity: "\<not> is_nan x \<Longrightarrow> fle x plus_infinity"
  for x :: "('e::len,'f::len) floatT"
  by cheat


subsection \<open>Arithmetic\<close>

text \<open>Adapted from IEEE\_Floating\_Point/IEEE\_Properties.thy.\<close>

lemma minus_minus_float: "- (-x) = x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma is_normal_minus_float: "is_normal (-x) = is_normal x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma is_subnormal_minus_float: "is_subnormal (-x) = is_subnormal x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma fadd_comm_eq: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> fadd mode x y = fadd mode y x"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fadd_comm: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> is_finite (fadd mode x y) \<Longrightarrow> feq (fadd mode x y) (fadd mode y x)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma is_zero_uminus: "is_zero (- x) \<longleftrightarrow> is_zero x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma is_infinity_uminus: "is_infinity (- x) = is_infinity x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma is_finite_uminus: "is_finite (- x) \<longleftrightarrow> is_finite x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma is_nan_uminus: "is_nan (- x) \<longleftrightarrow> is_nan x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma valof_uminus: "is_finite x \<Longrightarrow> valof (- x) = - valof x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_neg_add: (*FIXME*)
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> is_finite (fsub mode x y) \<Longrightarrow> valof x + valof (- y) = valof x - valof y"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fadd_minus: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> is_finite (fsub mode x y) \<Longrightarrow> feq (fadd mode x (-y)) (fsub mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma float_abs: "\<not> is_nan x \<Longrightarrow> abs (- x) = abs x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma valof_zero: "valof (0::('e::len,'f::len) floatT) = 0"
  by cheat

lemma valof_mzero: "valof (minus_zero::('e::len,'f::len) floatT) = 0"
  by cheat

lemma val_zero: "is_zero x \<Longrightarrow> valof x = 0"
  for x :: "('e::len,'f::len) floatT"
  by cheat


subsection \<open>Special Inputs\<close>

text \<open>From the IEEE 754-2019 standard.\<close>

lemma rem_fin_inf: "is_finite x \<Longrightarrow> float_rem x plus_infinity = x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma fsqrt_mzero: "fsqrt mode (minus_zero::('e::len,'f::len) floatT) = minus_zero"
  by cheat

lemma compare_cases: "flt x y \<or> feq x y \<or> fgt x y \<longleftrightarrow> \<not>(is_nan x \<or> is_nan y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma compare_unique1: "\<not> (flt x y \<and> feq x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma compare_unique2: "\<not> (flt x y \<and> fgt x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma compare_unique3: "\<not> (flt x y \<and> (is_nan x \<or> is_nan y))"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma compare_unique4: "\<not> (feq x y \<and> fgt x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma compare_unique5: "\<not> (feq x y \<and> (is_nan x \<or> is_nan y))"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma compare_unique6: "\<not> (fgt x y \<and> (is_nan x \<or> is_nan y))"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma zero_eq_mzero: "feq (0::('e::len,'f::len) floatT) minus_zero"
  by cheat

lemma float_id: "\<not> is_nan x \<Longrightarrow> feq x x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma fadd_inf1: "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow> is_infinity (fadd mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fadd_inf2: "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow> is_infinity (fadd mode y x)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fsub_inf1: "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow> is_infinity (fsub mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fsub_inf2: "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow> is_infinity (fsub mode y x)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fmul_inf1: "\<not> is_nan x \<Longrightarrow> \<not> is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow> is_infinity (fmul mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fmul_inf2: "\<not> is_nan x \<Longrightarrow> \<not> is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow> is_infinity (fmul mode y x)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fdiv_inf1: "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow> is_zero (fdiv mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fdiv_inf2: "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow> is_infinity (fdiv mode y x)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fsqrt_inf: "fsqrt mode (plus_infinity::('e::len,'f::len) floatT) = plus_infinity"
  by cheat

lemma abs_nan: "is_nan x \<Longrightarrow> is_nan (abs x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma neg_nan: "is_nan x \<Longrightarrow> is_nan (uminus x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma fadd_nan1: "is_nan x \<Longrightarrow> is_nan (fadd mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fadd_nan2: "is_nan y \<Longrightarrow> is_nan (fadd mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fsub_nan1: "is_nan x \<Longrightarrow> is_nan (fsub mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fsub_nan2: "is_nan y \<Longrightarrow> is_nan (fsub mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fmul_nan1: "is_nan x \<Longrightarrow> is_nan (fmul mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fmul_nan2: "is_nan y \<Longrightarrow> is_nan (fmul mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fdiv_nan1: "is_nan x \<Longrightarrow> is_nan (fdiv mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fdiv_nan2: "is_nan y \<Longrightarrow> is_nan (fdiv mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fma_nan1: "is_nan x \<Longrightarrow> is_nan (fmul_add mode x y z)"
  for x y z :: "('e::len,'f::len) floatT"
  by cheat

lemma fma_nan2: "is_nan y \<Longrightarrow> is_nan (fmul_add mode x y z)"
  for x y z :: "('e::len,'f::len) floatT"
  by cheat

lemma fma_nan3: "is_nan z \<Longrightarrow> is_nan (fmul_add mode x y z)"
  for x y z :: "('e::len,'f::len) floatT"
  by cheat

lemma frem_nan1: "is_nan x \<Longrightarrow> is_nan (frem mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma frem_nan2: "is_nan y \<Longrightarrow> is_nan (frem mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fsqrt_nan: "is_nan x \<Longrightarrow> is_nan (fsqrt mode x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma fintrnd_nan: "is_nan x \<Longrightarrow> is_nan (fintrnd mode x)"
  for x :: "('e::len,'f::len) floatT"
 by cheat

lemma zero_plus_zero: "fadd mode (0::('e::len,'f::len) floatT) 0 = 0"
  by cheat

lemma mzero_plus_mzero: "fadd mode (minus_zero::('e::len,'f::len) floatT) minus_zero = minus_zero"
  by cheat

lemma fmul_inf_zero1: "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow> is_nan (fmul mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fmul_inf_zero2: "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow> is_nan (fmul mode y x)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fma_inf_zero1: "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow> is_nan (fmul_add mode x y z)"
  for x y z :: "('e::len,'f::len) floatT"
  by cheat

lemma fma_inf_zero2: "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow> is_nan (fmul_add mode y x z)"
  for x y z :: "('e::len,'f::len) floatT"
  by cheat

lemma inf_plus_minf1: "is_nan (fadd mode (plus_infinity::('e::len,'f::len) floatT) minus_infinity)"
  by cheat

lemma inf_plus_minf2: "is_nan (fadd mode (minus_infinity::('e::len,'f::len) floatT) plus_infinity)"
  by cheat

lemma inf_minus_inf1: "is_nan (fsub mode (plus_infinity::('e::len,'f::len) floatT) plus_infinity)"
  by cheat

lemma inf_minus_inf2: "is_nan (fsub mode (minus_infinity::('e::len,'f::len) floatT) minus_infinity)"
  by cheat

lemma zero_div_zero: "is_zero x \<Longrightarrow> is_zero y \<Longrightarrow> is_nan (fdiv mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma inf_div_inf: "is_infinity x \<Longrightarrow> is_infinity y \<Longrightarrow> is_nan (fdiv mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma frem_inf: "is_infinity x \<Longrightarrow> is_nan (frem mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma frem_zero: "is_zero y \<Longrightarrow> is_nan (frem mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma fsqrt_neg: "flt x 0 \<Longrightarrow> is_nan (fsqrt mode x)"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma div_zero: "\<not> is_nan x \<Longrightarrow> is_zero y \<Longrightarrow> \<not> is_zero x \<Longrightarrow> is_infinity (fdiv mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat


subsection \<open>Rounding\<close>

text \<open>From ``Handbook of Floating-Point Arithmetic'' by J-M Muller.\<close>

lemma leq_round: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> fle x y \<Longrightarrow>
    fle (round mode (valof x) :: ('e::len,'f::len) floatT) (round mode (valof y))"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma round_id: "is_finite x \<Longrightarrow> feq (round mode (valof x)) x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma round_sym_nearest_even: "(round RNE (-x) :: ('e::len,'f::len) floatT) = - round RNE x"
  by cheat

lemma round_sym_nearest_away: "(round RNA (-x) :: ('e::len,'f::len) floatT) = - round RNA x"
  by cheat

lemma round_sym_zero: "(round RTZ (-x) :: ('e::len,'f::len) floatT) = - round RTZ x"
  by cheat

lemma round_sym_updown: "(round RTP (-x) :: ('e::len,'f::len) floatT) = - round RTN x"
  by cheat

lemma round_add_eq_sub: "\<not> is_nan x \<Longrightarrow> \<not> is_nan y \<Longrightarrow> feq (fadd RTP x y) (- (fsub RTN (-x) y))"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma round_mul_eq: "\<not> is_nan x \<Longrightarrow> \<not> is_nan y \<Longrightarrow> feq (fmul RTN x y) (- fmul RTP (-x) y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma round_zero: "fintrnd RNE (0 :: ('e::len,'f::len) floatT) = 0"
  by cheat

lemma sterbenz: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> (valof y)/2 \<le> valof x \<and> valof x \<le> 2*(valof y) \<Longrightarrow>
    valof x - valof y = valof (fsub mode x y)"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma hauser: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> is_subnormal (fadd mode x y) \<Longrightarrow> valof (fadd mode x y) = valof x + valof y"
  for x y :: "('e::len,'f::len) floatT"
  by cheat


subsection \<open>Various\<close>

lemma triple_zero: "is_zero (fp s 0 0 :: ('e::len,'f::len) floatT)"
  by cheat

lemma some_nan_neq: "\<not> feq NaN x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

lemma float_mul_comm_eq: "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> fmul mode x y = fmul mode y x"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma less_greater_equal: "fle x y \<Longrightarrow> fge x y \<Longrightarrow> feq x y"
  for x y :: "('e::len,'f::len) floatT"
  by cheat

lemma abs_abs_eq: "abs (abs x) = abs x"
  for x :: "('e::len,'f::len) floatT"
  by cheat

end
