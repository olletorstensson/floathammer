theory Float_Tests_Fixed_Reduced
imports Main
        IEEE_Floating_Point.IEEE
        IEEE_Floating_Point.IEEE_Properties
begin

(*half precision*)
type_synonym floatT = "(5,10) float"

(*single precision*)
(*type_synonym floatT = "(8,23) float"*)

(*double precision*)
(*type_synonym floatT = "(11,52) float"*)

(*quadruple precision*)
(*type_synonym floatT = "(15,112) float"*)


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