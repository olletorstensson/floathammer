theory Float_Tests_Poly
imports Main
        IEEE_Floating_Point.IEEE
begin

(* CLASSIFICATION *)
(*from IEEE_Floating_point/IEEE_properties.thy*)

lemma float_cases:
  "is_nan x \<or> is_infinity x \<or> is_normal x \<or>
    is_denormal x \<or> is_zero x"
  oops

lemma float_cases_finite: "is_nan x \<or> is_infinity x \<or> is_finite x"
  oops

lemma float_zero1: "is_zero 0"
  oops

lemma float_zero2: "is_zero (- x) \<longleftrightarrow> is_zero x"
  oops

lemma float_distinct1: "\<not> (is_nan x \<and> is_infinity x)"
  oops

lemma float_distinct2: "\<not> (is_nan x \<and> is_normal x)"
  oops

lemma float_distinct3: "\<not> (is_nan x \<and> is_denormal x)"
  oops

lemma float_distinct4: "\<not> (is_nan x \<and> is_zero x)"
  oops

lemma float_distinct5: "\<not> (is_infinity x \<and> is_normal x)"
  oops

lemma float_distinct6: "\<not> (is_infinity x \<and> is_denormal x)"
  oops

lemma float_distinct7: "\<not> (is_infinity x \<and> is_zero x)"
  oops

lemma float_distinct8: "\<not> (is_normal x \<and> is_denormal x)"
  oops

lemma float_distinct9: "\<not> (is_denormal x \<and> is_zero x)"
  oops

lemma denormal_imp_not_zero: "is_denormal x \<Longrightarrow> \<not>is_zero x"
  oops

lemma normal_imp_not_zero: "is_normal x \<Longrightarrow> \<not>is_zero x"
  oops

lemma normal_imp_not_denormal:
  "is_normal x \<Longrightarrow> \<not>is_denormal x"
  oops

lemma denormal_zero: "\<not>is_denormal 0"
  oops

lemma denormal_mzero: "\<not>is_denormal minus_zero"
  oops

lemma normal_zero: "\<not>is_normal 0"
  oops

lemma normal_mzero: "\<not>is_normal minus_zero"
  oops

lemma float_distinct_finite1: "\<not> (is_nan x \<and> is_finite x)"
  oops

lemma float_distinct_finite2: "\<not>(is_infinity x \<and> is_finite x)"
  oops

lemma finite_infinity: "is_finite x \<Longrightarrow> \<not> is_infinity x"
  oops

lemma finite_nan: "is_finite x \<Longrightarrow> \<not> is_nan x"
  oops

lemma is_finite_nonempty: "{x. is_finite x} \<noteq> {}"
  oops

lemma is_infinity_cases:
  "is_infinity x \<Longrightarrow> x = plus_infinity \<or> x = minus_infinity"
  oops

lemma is_zero_cases: "is_zero x \<Longrightarrow> x = 0 \<or> x = - 0"
  oops

lemma infinite_infinity: "\<not> is_finite plus_infinity"
  oops

lemma infinite_minfinity: "\<not> is_finite minus_infinity"
  oops

lemma nan_not_finite: "is_nan x \<Longrightarrow> \<not> is_finite x"
  oops


(* COMPARISON *)
(*from IEEE_Floating_Point/IEEE_properties.thy*)

lemma float_lt:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    x < y \<longleftrightarrow> valof x < valof y"
  oops

lemma float_eq:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    x \<doteq> y \<longleftrightarrow> valof x = valof y"
  oops

lemma float_le:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    x \<le> y \<longleftrightarrow> valof x \<le> valof y"
  oops

lemma float_eq_refl: "x \<doteq> x \<longleftrightarrow> \<not> is_nan x"
  oops

lemma float_lt_trans:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite z \<Longrightarrow> x < y \<Longrightarrow>
      y < z \<Longrightarrow> x < z"
  oops

lemma float_le_less_trans:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite z \<Longrightarrow> x \<le> y \<Longrightarrow>
      y < z \<Longrightarrow> x < z"
  oops

lemma float_le_trans:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite z \<Longrightarrow> x \<le> y \<Longrightarrow>
      y \<le> z \<Longrightarrow> x \<le> z"
  oops

lemma float_le_neg:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    \<not> x < y \<longleftrightarrow> y \<le> x"
  oops

lemma float_le_infinity:
  "\<not> is_nan x \<Longrightarrow> x \<le> plus_infinity"
  oops


(* ARITHMETIC *)
(*from IEEE_Floating_point/IEEE_properties.thy*)

lemma minus_minus_float: "- (-x) = x"
  for x :: "('e, 'f) float"
  oops

lemma is_normal_minus_float: "is_normal (-x) = is_normal x"
  oops

lemma is_denormal_minus_float: "is_denormal (-x) = is_denormal x"
  oops

lemma float_plus_comm_eq:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> x + y = y + x"
  oops

lemma float_plus_comm:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite (x + y) \<Longrightarrow> (x + y) \<doteq> (y + x)"
  oops

lemma is_zero_uminus: "is_zero (- x) \<longleftrightarrow> is_zero x"
  oops

lemma is_infinity_uminus: "is_infinity (- x) = is_infinity x"
  oops

lemma is_finite_uminus: "is_finite (- x) \<longleftrightarrow> is_finite x"
  oops

lemma is_nan_uminus: "is_nan (- x) \<longleftrightarrow> is_nan x"
  oops

lemma valof_uminus: "is_finite x \<Longrightarrow> valof (- x) = - valof x"
  oops

lemma float_neg_add:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite (x - y) \<Longrightarrow>
      valof x + valof (- y) = valof x - valof y"
  oops

lemma float_plus_minus:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_finite (x - y) \<Longrightarrow> (x + - y) \<doteq> (x - y)"
  oops

lemma float_abs: "\<not> is_nan x \<Longrightarrow> abs (- x) = abs x"
  oops

lemma valof_zero: "valof 0 = 0"
  oops

lemma valof_mzero: "valof minus_zero = 0"
  oops

lemma val_zero: "is_zero x \<Longrightarrow> valof x = 0"
  oops


(* SPECIAL INPUTS *)
(*from the IEEE 754-2019 standard*)

lemma rem_fin_inf: "is_finite x \<Longrightarrow> float_rem x \<infinity> = x"
  oops

lemma sqrt_mzero: "float_sqrt minus_zero = minus_zero"
  oops

lemma compare_cases:
  "flt x y \<or> feq x y \<or> fgt x y \<longleftrightarrow>
    \<not>(is_nan x \<or> is_nan y)"
  oops

lemma compare_unique1: "\<not> (flt x y \<and> feq x y)"
  oops

lemma compare_unique2: "\<not> (flt x y \<and> fgt x y)"
  oops

lemma compare_unique3: "\<not> (flt x y \<and> (is_nan x \<or> is_nan y))"
  oops

lemma compare_unique4: "\<not> (feq x y \<and> fgt x y)"
  oops

lemma compare_unique5: "\<not> (feq x y \<and> (is_nan x \<or> is_nan y))"
  oops

lemma compare_unique6: "\<not> (fgt x y \<and> (is_nan x \<or> is_nan y))"
  oops

lemma zero_eq_mzero: "0 \<doteq> minus_zero"
  oops

lemma float_id: "\<not> is_nan x \<Longrightarrow> x \<doteq> x"
  oops

lemma fadd_inf1:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_infinity (fadd rm x y)"
  oops

lemma fadd_inf2:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_infinity (fadd rm y x)"
  oops

lemma fsub_inf1:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_infinity (fsub rm x y)"
  oops

lemma fsub_inf2:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_infinity (fsub rm y x)"
  oops

lemma fmul_inf1:
  "\<not> is_nan x \<Longrightarrow> \<not> is_zero x \<Longrightarrow>
    is_infinity y \<Longrightarrow> is_infinity (fmul rm x y)"
  oops

lemma fmul_inf2:
  "\<not> is_nan x \<Longrightarrow> \<not> is_zero x \<Longrightarrow>
    is_infinity y \<Longrightarrow> is_infinity (fmul rm y x)"
  oops

lemma fdiv_inf1:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_zero (fdiv rm x y)"
  oops

lemma fdiv_inf2:
  "is_finite x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_infinity (fdiv rm y x)"
  oops

lemma fsqrt_inf: "fsqrt rm plus_infinity = plus_infinity"
  oops

lemma abs_nan: "is_nan x \<Longrightarrow> is_nan \<bar>x\<bar>"
  oops

lemma neg_nan: "is_nan x \<Longrightarrow> is_nan (uminus x)"
  oops

lemma fadd_nan1: "is_nan x \<Longrightarrow> is_nan (fadd rm x y)"
  oops

lemma fadd_nan2: "is_nan y \<Longrightarrow> is_nan (fadd rm x y)"
  oops

lemma fsub_nan1: "is_nan x \<Longrightarrow> is_nan (fsub rm x y)"
  oops

lemma fsub_nan2: "is_nan y \<Longrightarrow> is_nan (fsub rm x y)"
  oops

lemma fmul_nan1: "is_nan x \<Longrightarrow> is_nan (fmul rm x y)"
  oops

lemma fmul_nan2: "is_nan y \<Longrightarrow> is_nan (fmul rm x y)"
  oops

lemma fdiv_nan1: "is_nan x \<Longrightarrow> is_nan (fdiv rm x y)"
  oops

lemma fdiv_nan2: "is_nan y \<Longrightarrow> is_nan (fdiv rm x y)"
  oops

lemma fma_nan1: "is_nan x \<Longrightarrow> is_nan (fmul_add rm x y z)"
  oops

lemma fma_nan2: "is_nan y \<Longrightarrow> is_nan (fmul_add rm x y z)"
  oops

lemma fma_nan3: "is_nan z \<Longrightarrow> is_nan (fmul_add rm x y z)"
  oops

lemma frem_nan1: "is_nan x \<Longrightarrow> is_nan (frem rm x y)"
  oops

lemma frem_nan2: "is_nan y \<Longrightarrow> is_nan (frem rm x y)"
  oops

lemma fsqrt_nan: "is_nan x \<Longrightarrow> is_nan (fsqrt rm x)"
  oops

lemma fintrnd_nan: "is_nan x \<Longrightarrow> is_nan (fintrnd rm x)"
  oops

lemma zero_plus_zero: "fadd rm 0 0 = 0"
  oops

lemma mzero_plus_mzero: "fadd rm minus_zero minus_zero = minus_zero"
  oops

lemma fmul_inf_zero1:
  "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_nan (fmul rm x y)"
  oops

lemma fmul_inf_zero2:
  "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_nan (fmul rm y x)"
  oops

lemma fma_inf_zero1:
  "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_nan (fmul_add rm x y z)"
  oops

lemma fma_inf_zero2:
  "is_zero x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_nan (fmul_add rm y x z)"
  oops

lemma inf_plus_minf1: "is_nan (fadd rm plus_infinity minus_infinity)"
  oops

lemma inf_plus_minf2: "is_nan (fadd rm minus_infinity plus_infinity)"
  oops

lemma inf_minus_inf1: "is_nan (fsub rm plus_infinity plus_infinity)"
  oops

lemma inf_minus_inf2: "is_nan (fsub rm minus_infinity minus_infinity)"
  oops

lemma zero_div_zero:
  "is_zero x \<Longrightarrow> is_zero y \<Longrightarrow> is_nan (fdiv rm x y)"
  oops

lemma inf_div_inf:
  "is_infinity x \<Longrightarrow> is_infinity y \<Longrightarrow>
    is_nan (fdiv rm x y)"
  oops

lemma frem_inf: "is_infinity x \<Longrightarrow> is_nan (frem rm x y)"
  oops

lemma frem_zero: "is_zero y \<Longrightarrow> is_nan (frem rm x y)"
  oops

lemma fsqrt_neg: "x < 0 \<Longrightarrow> is_nan (fsqrt rm x)"
  oops

lemma div_zero:
  "\<not> is_nan x \<Longrightarrow> is_zero y \<Longrightarrow>
    \<not> is_zero x \<Longrightarrow> is_infinity (x div y)"
  oops


(* ROUNDING *)
(*from "Handbook of Floating-Point Arithmetic" by J-M Muller*)

lemma leq_round:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    x \<le> y \<Longrightarrow>
      round rm (valof x) \<le> round rm (valof y)"
  oops

lemma round_id: "is_finite x \<Longrightarrow> feq (round rm (valof x)) x"
  oops

lemma round_sym_nearest_even:
  "round To_nearest (-x) = - (round To_nearest x)"
  oops

lemma round_sym_nearest_away:
  "round To_nearest_away (-x) = - (round To_nearest_away x)"
  oops

lemma round_sym_zero:
  "round float_To_zero (-x) = - (round float_To_zero x)"
  oops

lemma round_sym_updown:
  "round To_pinfinity (-x) = - (round To_ninfinity x)"
  oops

lemma round_add_eq_sub:
  "\<not> is_nan x \<Longrightarrow> \<not> is_nan y \<Longrightarrow>
    feq (fadd To_pinfinity x y) (- (fsub To_ninfinity (-x) y))"
  oops

lemma round_mul_eq:
  "\<not> is_nan x \<Longrightarrow> \<not> is_nan y \<Longrightarrow>
    feq (fmul To_ninfinity x y) (- (fmul To_pinfinity (-x) y))"
  oops

lemma round_zero: "ROUNDFLOAT 0 = 0"
  oops

lemma sterbenz:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    (valof y)/2 \<le> valof x \<and> valof x \<le> 2*(valof y) \<Longrightarrow>
      valof x - valof y = valof (fsub rm x y)"
  oops

lemma hauser:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow>
    is_denormal (x+y) \<Longrightarrow> valof (x+y) = valof x + valof y"
  oops


(* VARIOUS *)

lemma triple_zero: "is_zero (Abs_float (s, 0 , 0))"
  oops

lemma some_nan_neq: "\<not> some_nan \<doteq> x"
  oops

lemma float_mul_comm_eq:
  "is_finite x \<Longrightarrow> is_finite y \<Longrightarrow> x * y = y * x"
  oops

lemma less_greater_equal:
  "fle x y \<Longrightarrow> fge x y \<Longrightarrow> feq x y"
  oops

end