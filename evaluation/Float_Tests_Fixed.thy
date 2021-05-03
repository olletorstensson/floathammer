theory Float_Tests_Fixed
imports Main
        IEEE_Floating_Point.IEEE
begin

(*half precision*)
type_synonym floatT = "(5,10) float"

(*single precision*)
(*type_synonym floatT = "(8,23) float"*)

(*double precision*)
(*type_synonym floatT = "(11,52) float"*)

(*quadruple precision*)
(*type_synonym floatT = "(15,112) float"*)


(* CLASSIFICATION *)
(*from IEEE_Floating_point/IEEE_properties.thy*)

lemma float_cases:
  "is_nan x \<or> is_infinity x \<or> is_normal x \<or>
    is_denormal x \<or> is_zero x"
  for x :: floatT
  oops

lemma float_cases_finite: "is_nan x \<or> is_infinity x \<or> is_finite x"
  for x :: floatT
  oops

lemma float_zero1: "is_zero (0::floatT)"
  oops

lemma float_zero2: "is_zero (- x) \<longleftrightarrow> is_zero x"
  for x :: floatT
  oops

lemma float_distinct1: "\<not> (is_nan x \<and> is_infinity x)"
  for x :: floatT
  oops

lemma float_distinct2: "\<not> (is_nan x \<and> is_normal x)"
  for x :: floatT
  oops

lemma float_distinct3: "\<not> (is_nan x \<and> is_denormal x)"
  for x :: floatT
  oops

lemma float_distinct4: "\<not> (is_nan x \<and> is_zero x)"
  for x :: floatT
  oops

lemma float_distinct5: "\<not> (is_infinity x \<and> is_normal x)"
  for x :: floatT
  oops

lemma float_distinct6: "\<not> (is_infinity x \<and> is_denormal x)"
  for x :: floatT
  oops

lemma float_distinct7: "\<not> (is_infinity x \<and> is_zero x)"
  for x :: floatT
  oops

lemma float_distinct8: "\<not> (is_normal x \<and> is_denormal x)"
  for x :: floatT
  oops

lemma float_distinct9: "\<not> (is_denormal x \<and> is_zero x)"
  for x :: floatT
  oops

lemma denormal_imp_not_zero: "is_denormal x \<Longrightarrow> \<not>is_zero x"
  for x :: floatT
  oops

lemma normal_imp_not_zero: "is_normal x \<Longrightarrow> \<not>is_zero x"
  for x :: floatT
  oops

lemma normal_imp_not_denormal:
  "is_normal x \<Longrightarrow> \<not>is_denormal x"
  for x :: floatT
  oops

lemma denormal_zero: "\<not>is_denormal (0::floatT)"
  oops

lemma denormal_mzero: "\<not>is_denormal (minus_zero::floatT)"
  oops

lemma normal_zero: "\<not>is_normal (0::floatT)"
  oops

lemma normal_mzero: "\<not>is_normal (minus_zero::floatT)"
  oops

lemma float_distinct_finite1: "\<not> (is_nan x \<and> is_finite x)"
  for x :: floatT
  oops

lemma float_distinct_finite2: "\<not>(is_infinity x \<and> is_finite x)"
  for x :: floatT
  oops

lemma finite_infinity: "is_finite x \<Longrightarrow> \<not> is_infinity x"
  for x :: floatT
  oops

lemma finite_nan: "is_finite x \<Longrightarrow> \<not> is_nan x"
  for x :: floatT
  oops

lemma is_finite_nonempty: "{x::floatT. is_finite x} \<noteq> {}"
  oops

lemma is_infinity_cases:
  "is_infinity x \<Longrightarrow> x = plus_infinity \<or> x = minus_infinity"
  for x :: floatT
  oops

lemma is_zero_cases: "is_zero x \<Longrightarrow> x = 0 \<or> x = - 0"
  for x :: floatT
  oops

lemma infinite_infinity: "\<not> is_finite (plus_infinity::floatT)"
  oops

lemma infinite_minfinity: "\<not> is_finite (minus_infinity::floatT)"
  oops

lemma nan_not_finite: "is_nan x \<Longrightarrow> \<not> is_finite x"
  for x :: floatT
  oops


(* COMPARISON *)
(*from IEEE_Floating_Point/IEEE_properties.thy*)

lemma float_lt:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    x < y \<longleftrightarrow> valof x < valof y"
  for x y :: floatT
  oops

lemma float_eq:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    x \<doteq> y \<longleftrightarrow> valof x = valof y"
  for x y :: floatT
  oops

lemma float_le:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    x \<le> y \<longleftrightarrow> valof x \<le> valof y"
  for x y :: floatT
  oops

lemma float_eq_refl: "x \<doteq> x \<longleftrightarrow> \<not> is_nan x"
  for x :: floatT
  oops

lemma float_lt_trans:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite z \<Longrightarrow> x < y \<Longrightarrow>
      y < z \<Longrightarrow> x < z"
  for x y z :: floatT
  oops

lemma float_le_less_trans:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite z \<Longrightarrow> x \<le> y \<Longrightarrow>
      y < z \<Longrightarrow> x < z"
  for x y z :: floatT
  oops

lemma float_le_trans:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite z \<Longrightarrow> x \<le> y \<Longrightarrow>
      y \<le> z \<Longrightarrow> x \<le> z"
  for x y z :: floatT
  oops

lemma float_le_neg:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    \<not> x < y \<longleftrightarrow> y \<le> x"
  for x y :: floatT
  oops

lemma float_le_infinity:
  "\<not> is_nan x \<Longrightarrow> x \<le> plus_infinity"
  for x :: floatT
  oops


(* ARITHMETIC *)
(*from IEEE_Floating_point/IEEE_properties.thy*)

lemma minus_minus_float: "- (-x) = x"
  for x :: floatT
  oops

lemma is_normal_minus_float: "is_normal (-x) = is_normal x"
  for x :: floatT
  oops

lemma is_denormal_minus_float: "is_denormal (-x) = is_denormal x"
  for x :: floatT
  oops

lemma float_plus_comm_eq:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> x + y = y + x"
  for x y :: floatT
  oops

lemma float_plus_comm:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite (x + y) \<Longrightarrow> (x + y) \<doteq> (y + x)"
  for x y :: floatT
  oops

lemma is_zero_uminus: "is_zero (- x) \<longleftrightarrow> is_zero x"
  for x :: floatT
  oops

lemma is_infinity_uminus: "is_infinity (- x) = is_infinity x"
  for x :: floatT
  oops

lemma is_finite_uminus: "is_finite (- x) \<longleftrightarrow> is_finite x"
  for x :: floatT
  oops

lemma is_nan_uminus: "is_nan (- x) \<longleftrightarrow> is_nan x"
  for x :: floatT
  oops

lemma valof_uminus: "is_finite x \<Longrightarrow> valof (- x) = - valof x"
  for x :: floatT
  oops

lemma float_neg_add:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite (x - y) \<Longrightarrow>
      valof x + valof (- y) = valof x - valof y"
  for x y :: floatT
  oops

lemma float_plus_minus:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite (x - y) \<Longrightarrow> (x + - y) \<doteq> (x - y)"
  for x y :: floatT
  oops

lemma float_abs: "\<not> is_nan x \<Longrightarrow> abs (- x) = abs x"
  for x :: floatT
  oops

lemma valof_zero: "valof (0::floatT) = 0"
  oops

lemma valof_mzero: "valof (minus_zero::floatT) = 0"
  oops

lemma val_zero: "is_zero x \<Longrightarrow> valof x = 0"
  for x :: floatT
  oops


(* SPECIAL INPUTS *)
(*from the IEEE 754-2019 standard*)

lemma rem_fin_inf: "is_finite x \<Longrightarrow> float_rem x \<infinity> = x"
  for x :: floatT
  oops

lemma sqrt_mzero: "float_sqrt (minus_zero::floatT) = minus_zero"
  oops

lemma compare_cases:
  "flt x y \<or> feq x y \<or> fgt x y \<longleftrightarrow>
    \<not>(is_nan x \<or> is_nan y)"
  for x y :: floatT
  oops

lemma compare_unique1: "\<not> (flt x y \<and> feq x y)"
  for x y :: floatT
  oops

lemma compare_unique2: "\<not> (flt x y \<and> fgt x y)"
  for x y :: floatT
  oops

lemma compare_unique3: "\<not> (flt x y \<and> (is_nan x \<or> is_nan y))"
  for x y :: floatT
  oops

lemma compare_unique4: "\<not> (feq x y \<and> fgt x y)"
  for x y :: floatT
  oops

lemma compare_unique5: "\<not> (feq x y \<and> (is_nan x \<or> is_nan y))"
  for x y :: floatT
  oops

lemma compare_unique6: "\<not> (fgt x y \<and> (is_nan x \<or> is_nan y))"
  for x y :: floatT
  oops

lemma zero_eq_mzero: "(0::floatT) \<doteq> minus_zero"
  oops

lemma float_id: "\<not> is_nan x \<Longrightarrow> x \<doteq> x"
  for x :: floatT
  oops

lemma fadd_inf1:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_infinity (fadd rm x y)"
  for x y ::floatT
  oops

lemma fadd_inf2:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_infinity (fadd rm y x)"
  for x y ::floatT
  oops

lemma fsub_inf1:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_infinity (fsub rm x y)"
  for x y :: floatT
  oops

lemma fsub_inf2:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_infinity (fsub rm y x)"
  for x y :: floatT
  oops

lemma fmul_inf1:
  "\<not> is_nan x \<Longrightarrow> \<not> is_zero x \<Longrightarrow>
    is_infinity y \<Longrightarrow> is_infinity (fmul rm x y)"
  for x y :: floatT
  oops

lemma fmul_inf2:
  "\<not> is_nan x \<Longrightarrow> \<not> is_zero x \<Longrightarrow>
    is_infinity y \<Longrightarrow> is_infinity (fmul rm y x)"
  for x y :: floatT
  oops

lemma fdiv_inf1:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_zero (fdiv rm x y)"
  for x y :: floatT
  oops

lemma fdiv_inf2:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_infinity (fdiv rm y x)"
  for x y :: floatT
  oops

lemma fsqrt_inf: "fsqrt rm (plus_infinity::floatT) = plus_infinity"
  oops

lemma abs_nan: "is_nan x \<Longrightarrow> is_nan \<bar>x\<bar>"
  for x :: floatT
  oops

lemma neg_nan: "is_nan x \<Longrightarrow> is_nan (uminus x)"
  for x :: floatT
  oops

lemma fadd_nan1: "is_nan x \<Longrightarrow> is_nan (fadd rm x y)"
  for x y :: floatT
  oops

lemma fadd_nan2: "is_nan y \<Longrightarrow> is_nan (fadd rm x y)"
  for x y :: floatT
  oops

lemma fsub_nan1: "is_nan x \<Longrightarrow> is_nan (fsub rm x y)"
  for x y :: floatT
  oops

lemma fsub_nan2: "is_nan y \<Longrightarrow> is_nan (fsub rm x y)"
  for x y :: floatT
  oops

lemma fmul_nan1: "is_nan x \<Longrightarrow> is_nan (fmul rm x y)"
  for x y :: floatT
  oops

lemma fmul_nan2: "is_nan y \<Longrightarrow> is_nan (fmul rm x y)"
  for x y :: floatT
  oops

lemma fdiv_nan1: "is_nan x \<Longrightarrow> is_nan (fdiv rm x y)"
  for x y :: floatT
  oops

lemma fdiv_nan2: "is_nan y \<Longrightarrow> is_nan (fdiv rm x y)"
  for x y :: floatT
  oops

lemma fma_nan1: "is_nan x \<Longrightarrow> is_nan (fmul_add rm x y z)"
  for x y z :: floatT
  oops

lemma fma_nan2: "is_nan y \<Longrightarrow> is_nan (fmul_add rm x y z)"
  for x y z :: floatT
  oops

lemma fma_nan3: "is_nan z \<Longrightarrow> is_nan (fmul_add rm x y z)"
  for x y z :: floatT
  oops

lemma frem_nan1: "is_nan x \<Longrightarrow> is_nan (frem rm x y)"
  for x y :: floatT
  oops

lemma frem_nan2: "is_nan y \<Longrightarrow> is_nan (frem rm x y)"
  for x y :: floatT
  oops

lemma fsqrt_nan: "is_nan x \<Longrightarrow> is_nan (fsqrt rm x)"
  for x :: floatT
  oops

lemma fintrnd_nan: "is_nan x \<Longrightarrow> is_nan (fintrnd rm x)"
  for x :: floatT
 oops

lemma zero_plus_zero: "fadd rm (0::floatT) 0 = 0"
  oops

lemma mzero_plus_mzero: "fadd rm (minus_zero::floatT) minus_zero = minus_zero"
  oops

lemma fmul_inf_zero1:
  "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_nan (fmul rm x y)"
  for x y :: floatT
  oops

lemma fmul_inf_zero2:
  "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_nan (fmul rm y x)"
  for x y :: floatT
  oops

lemma fma_inf_zero1:
  "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_nan (fmul_add rm x y z)"
  for x y z :: floatT
  oops

lemma fma_inf_zero2:
  "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_nan (fmul_add rm y x z)"
  for x y z :: floatT
  oops

lemma inf_plus_minf1: "is_nan (fadd rm (plus_infinity::floatT) minus_infinity)"
  oops

lemma inf_plus_minf2: "is_nan (fadd rm (minus_infinity::floatT) plus_infinity)"
  oops

lemma inf_minus_inf1: "is_nan (fsub rm (plus_infinity::floatT) plus_infinity)"
  oops

lemma inf_minus_inf2: "is_nan (fsub rm (minus_infinity::floatT) minus_infinity)"
  oops

lemma zero_div_zero:
  "is_zero x \<Longrightarrow> is_zero y \<Longrightarrow> is_nan (fdiv rm x y)"
  for x y :: floatT
  oops

lemma inf_div_inf:
  "is_infinity x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_nan (fdiv rm x y)"
  for x y :: floatT
  oops

lemma frem_inf: "is_infinity x \<Longrightarrow> is_nan (frem rm x y)"
  for x y :: floatT
  oops

lemma frem_zero: "is_zero y \<Longrightarrow> is_nan (frem rm x y)"
  for x y :: floatT
  oops

lemma fsqrt_neg: "x < 0 \<Longrightarrow> is_nan (fsqrt rm x)"
  for x :: floatT
  oops

lemma div_zero:
  "\<not> is_nan x \<Longrightarrow> is_zero y \<Longrightarrow>
    \<not> is_zero x \<Longrightarrow> is_infinity (x div y)"
  for x y :: floatT
  oops


(* ROUNDING *)
(*from "Handbook of Floating-Point Arithmetic" by J-M Muller*)

lemma leq_round:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    x \<le> y \<Longrightarrow>
      (round rm (valof x) :: floatT) \<le> round rm (valof y)"
  for x y :: floatT
  oops

lemma round_id: "is_finite x \<Longrightarrow> feq (round rm (valof x)) x"
  for x :: floatT
  oops

lemma round_sym_nearest_even:
  "(round To_nearest (-x) :: floatT) = - (round To_nearest x)"
  oops

lemma round_sym_nearest_away:
  "(round To_nearest_away (-x) :: floatT) = - (round To_nearest_away x)"
  oops

lemma round_sym_zero:
  "(round float_To_zero (-x) :: floatT) = - (round float_To_zero x)"
  oops

lemma round_sym_updown:
  "(round To_pinfinity (-x) :: floatT) = - (round To_ninfinity x)"
  oops

lemma round_add_eq_sub:
  "\<not> is_nan x \<Longrightarrow> \<not> is_nan y \<Longrightarrow>
    feq (fadd To_pinfinity x y) (- (fsub To_ninfinity (-x) y))"
  for x y :: floatT
  oops

lemma round_mul_eq:
  "\<not> is_nan x \<Longrightarrow> \<not> is_nan y \<Longrightarrow>
    feq (fmul To_ninfinity x y) (- (fmul To_pinfinity (-x) y))"
  for x y :: floatT
  oops

lemma round_zero: "ROUNDFLOAT 0 = (0::floatT)"
  oops

lemma sterbenz:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    (valof y)/2 \<le> valof x \<and> valof x \<le> 2*(valof y) \<Longrightarrow>
      valof x - valof y = valof (fsub rm x y)"
  for x y :: floatT
  oops

lemma hauser:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_denormal (x+y) \<Longrightarrow> valof (x+y) = valof x + valof y"
  for x y :: floatT
  oops


(* VARIOUS *)

lemma triple_zero: "is_zero (Abs_float (s, 0 , 0) :: floatT)"
  oops

lemma some_nan_neq: "\<not> some_nan \<doteq> x"
  for x :: floatT
  oops

lemma float_mul_comm_eq:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> x * y = y * x"
  for x y :: floatT
  oops

lemma less_greater_equal:
  "fle x y \<Longrightarrow> fge x y \<Longrightarrow> feq x y"
  for x y :: floatT
  oops

end