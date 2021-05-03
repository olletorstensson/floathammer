theory Float_Tests_Poly_Reduced
imports Main
        IEEE_Floating_Point.IEEE
        IEEE_Floating_Point.IEEE_Properties
begin

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