theory Float_Tests
imports Main
        IEEE_Floating_Point.IEEE
begin

ML_file \<open>smt_float.ML\<close>

(* TEST EACH LEMMA WITH THE 3/4 COMMON FP-FORMATS *)


(* CLASSIFICATION *)
(* from IEEE_properties.thy *)

lemma float_cases: "is_nan a \<or> is_infinity a \<or> is_normal a \<or> is_denormal a \<or> is_zero a"
  oops

lemma float_cases_finite: "is_nan a \<or> is_infinity a \<or> is_finite a"
  oops

lemma float_zero1: "is_zero 0"
  oops

lemma float_zero2: "is_zero (- x) \<longleftrightarrow> is_zero x"
  oops

lemma float_distinct:
  "\<not> (is_nan a \<and> is_infinity a)"
  "\<not> (is_nan a \<and> is_normal a)"
  "\<not> (is_nan a \<and> is_denormal a)"
  "\<not> (is_nan a \<and> is_zero a)"
  "\<not> (is_infinity a \<and> is_normal a)"
  "\<not> (is_infinity a \<and> is_denormal a)"
  "\<not> (is_infinity a \<and> is_zero a)"
  "\<not> (is_normal a \<and> is_denormal a)"
  "\<not> (is_denormal a \<and> is_zero a)"
  oops

lemma denormal_imp_not_zero: "is_denormal f \<Longrightarrow> \<not>is_zero f"
  oops

lemma normal_imp_not_zero: "is_normal f \<Longrightarrow> \<not>is_zero f"
  oops

lemma normal_imp_not_denormal: "is_normal f \<Longrightarrow> \<not>is_denormal f"
  oops

lemma denormal_zero: "\<not>is_denormal 0" "\<not>is_denormal minus_zero"
  oops

lemma normal_zero: "\<not>is_normal 0" "\<not>is_normal minus_zero"
  oops

lemma float_distinct_finite: "\<not> (is_nan a \<and> is_finite a)" "\<not>(is_infinity a \<and> is_finite a)"
  oops

lemma finite_infinity: "is_finite a \<Longrightarrow> \<not> is_infinity a"
  oops

lemma finite_nan: "is_finite a \<Longrightarrow> \<not> is_nan a"
  oops

lemma is_finite_nonempty: "{a. is_finite a} \<noteq> {}"
  oops

lemma is_infinity_cases:
  assumes "is_infinity x"
  obtains "x = plus_infinity" | "x = minus_infinity"
  oops

lemma is_zero_cases:
  assumes "is_zero x"
  obtains "x = 0" | "x = - 0"
  oops

lemma infinite_infinity: "\<not> is_finite plus_infinity" "\<not> is_finite minus_infinity"
  oops

lemma nan_not_finite: "is_nan x \<Longrightarrow> \<not> is_finite x"
  oops



(* COMPARISON *)
(* from IEEE_properties.thy *)

lemma float_lt:
  assumes "is_finite a" "is_finite b"
  shows "a < b \<longleftrightarrow> valof a < valof b"
  oops

lemma float_eq:
  assumes "is_finite a" "is_finite b"
  shows "a \<doteq> b \<longleftrightarrow> valof a = valof b"
  oops

lemma float_le:
  assumes "is_finite a" "is_finite b"
  shows "a \<le> b \<longleftrightarrow> valof a \<le> valof b"
  oops

lemma float_eq_refl: "a \<doteq> a \<longleftrightarrow> \<not> is_nan a"
  oops

lemma float_lt_trans: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> is_finite c \<Longrightarrow> a < b \<Longrightarrow> b < c \<Longrightarrow> a < c"
  oops

lemma float_le_less_trans: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> is_finite c \<Longrightarrow> a \<le> b \<Longrightarrow> b < c \<Longrightarrow> a < c"
  oops

lemma float_le_trans: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> is_finite c \<Longrightarrow> a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
  oops

lemma float_le_neg: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> \<not> a < b \<longleftrightarrow> b \<le> a"
  oops

lemma float_le_infinity: "\<not> is_nan a \<Longrightarrow> a \<le> plus_infinity"
  oops



(* ARITHMETIC *)
(* from IEEE_properties.thy *)

lemma minus_minus_float: "- (-f) = f" for f::"('e, 'f)float"
  oops

lemma is_normal_minus_float: "is_normal (-f) = is_normal f" for f::"('e, 'f)float"
  oops

lemma is_denormal_minus_float: "is_denormal (-f) = is_denormal f" for f::"('e, 'f)float"
  oops

lemma
  assumes "is_finite a" "is_finite b"
  shows float_plus_comm_eq: "a + b = b + a"
    and float_plus_comm: "is_finite (a + b) \<Longrightarrow> (a + b) \<doteq> (b + a)"
  oops

lemma is_zero_uminus: "is_zero (- a) \<longleftrightarrow> is_zero a"
  oops

lemma is_infinity_uminus: "is_infinity (- a) = is_infinity a"
  oops

lemma is_finite_uminus: "is_finite (- a) \<longleftrightarrow> is_finite a"
  oops

lemma is_nan_uminus: "is_nan (- a) \<longleftrightarrow> is_nan a"
  oops

lemma valof_uminus:
  assumes "is_finite a"
  shows "valof (- a) = - valof a" (is "?L = ?R")
  oops

lemma float_neg_add:
  "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> is_finite (a - b) \<Longrightarrow> valof a + valof (- b) = valof a - valof b"
  oops

lemma float_plus_minus:
  assumes "is_finite a" "is_finite b" "is_finite (a - b)"
  shows "(a + - b) \<doteq> (a - b)"
  oops

lemma float_abs: "\<not> is_nan a \<Longrightarrow> abs (- a) = abs a"
  oops

lemma valof_zero: "valof 0 = 0" "valof minus_zero = 0"
  oops

lemma val_zero: "is_zero a \<Longrightarrow> valof a = 0"
  oops


(* NON-FINITE INPUTS*)
(* from the IEEE-754 standard *)

(* remainder(x, \<infinity>) is x for finite x. *)
lemma rem_fin_inf: "is_finite x \<Longrightarrow> frem rm x plus_infinity = x"
  oops

(* squareRoot(−0) shall be −0 *)
lemma sqrt_mzero: "fsqrt rm (-0) = -0"
  oops

(* Four mutually exclusive relations are possible: less than, equal, greater than, and unordered *)
(* Every NaN shall compare unordered with everything, including itself. *)
lemma compare_cases: "flt x y \<or> feq x y \<or> fgt x y \<longleftrightarrow> \<not>(is_nan x \<or> is_nan y)"
  oops

lemma compare_unique:
  "\<not> (flt x y \<and> feq x y)"
  "\<not> (flt x y \<and> fgt x y)"
  "\<not> (flt x y \<and> (is_nan x \<or> is_nan y))"
  "\<not> (feq x y \<and> fgt x y)"
  "\<not> (feq x y \<and> (is_nan x \<or> is_nan y))"
  "\<not> (fgt x y \<and> (is_nan x \<or> is_nan y))"
  oops

(* +0 = −0 *)
lemma zero_eq_mzero: "feq 0 minus_zero"
  oops

(* Infinite operands of the same sign shall compare equal *)
lemma float_id: "\<not>(is_nan x) \<Longrightarrow> feq x x"
  oops

(* addition(\<infinity>, x), addition(x, \<infinity>), subtraction(\<infinity>, x), or subtraction(x, \<infinity>), for finite x *)
lemma fadd_inf:
  "(is_finite x \<and> is_infinity y) \<Longrightarrow> is_infinity (fadd rm x y)"
  "(is_finite x \<and> is_infinity y) \<Longrightarrow> is_infinity (fadd rm y x)"
  oops

lemma fsub_inf:
  "(is_finite x \<and> is_infinity y) \<Longrightarrow> is_infinity (fsub rm x y)"
  "(is_finite x \<and> is_infinity y) \<Longrightarrow> is_infinity (fsub rm y x)"
  oops

(* multiplication(\<infinity>, x) or multiplication(x, \<infinity>) for finite or infinite x \<noteq> 0 *)
lemma fmul_inf:
  "\<not>(is_nan x \<or> is_zero x) \<and> is_infinity y \<Longrightarrow> is_infinity (fmul rm x y)"
  "\<not>(is_nan x \<or> is_zero x) \<and> is_infinity y \<Longrightarrow> is_infinity (fmul rm y x)"
  oops

(* division(\<infinity>, x) or division(x, \<infinity>) for finite x *)
lemma fdiv_inf:
  "(is_finite x \<and> is_infinity y) \<Longrightarrow> is_zero (fdiv rm x y)"
  "(is_finite x \<and> is_infinity y) \<Longrightarrow> is_infinity (fdiv rm y x)"
  oops

(* squareRoot(+\<infinity>) *)
lemma fsqrt_inf: "fsqrt rm plus_infinity = plus_infinity"
  oops

(* For an operation with NaN inputs, if a floating-point result is to be delivered the result shall be NaN *)
lemma abs_nan: "is_nan x \<Longrightarrow> is_nan (abs x)"
  oops
lemma neg_nan: "is_nan x \<Longrightarrow> is_nan (- x)"
  oops
lemma fadd_nan: "(is_nan x \<or> is_nan y) \<Longrightarrow> is_nan (fadd rm x y)"
  oops
lemma fsub_nan: "(is_nan x \<or> is_nan y) \<Longrightarrow> is_nan (fsub rm x y)"
  oops
lemma fmul_nan: "(is_nan x \<or> is_nan y) \<Longrightarrow> is_nan (fmul rm x y)"
  oops
lemma fdiv_nan: "(is_nan x \<or> is_nan y) \<Longrightarrow> is_nan (fdiv rm x y)"
  oops
lemma fma_nan: "(is_nan x \<or> is_nan y \<or> is_nan z) \<Longrightarrow> is_nan (fmul_add rm x y z)"
  oops
lemma frem_nan: "(is_nan x \<or> is_nan y) \<Longrightarrow> is_nan (frem rm x y)"
  oops
lemma fsqrt_nan: "is_nan x \<Longrightarrow> is_nan (fsqrt rm x)"
  oops
lemma fintrnd_nan: "is_nan x \<Longrightarrow> is_nan (fintrnd rm x)"
  oops

(* x+x retains the same sign as x even when x is zero. *)
lemma zero_plus_zero:
  "fadd rm 0 0 = 0"
  "fadd rm (-0) (-0) = -0"
  oops

(* multiplication(0, \<infinity>) or multiplication(\<infinity>, 0) is NaN *)
lemma fmul_inf_zero:
  "(is_zero x \<and> is_infinity y) \<Longrightarrow> is_nan (fmul rm x y)"
  "(is_zero x \<and> is_infinity y) \<Longrightarrow> is_nan (fmul rm y x)"
  oops

(* fusedMultiplyAdd(0, \<infinity>, c) or fusedMultiplyAdd(\<infinity>, 0, c) is NaN *)
lemma fma_inf_zero:
  "(is_zero x \<and> is_infinity y) \<Longrightarrow> is_nan (fmul_add rm x y z)"
  "(is_zero x \<and> is_infinity y) \<Longrightarrow> is_nan (fmul_add rm y x z)"
  oops

(* magnitude subtraction of infinities *)
lemma inf_plus_minf:
  "is_nan (fadd rm plus_infinity minus_infinity)"
  "is_nan (fadd rm minus_infinity plus_infinity)"
  oops

lemma inf_minus_inf:
  "is_nan (fsub rm plus_infinity plus_infinity)"
  "is_nan (fsub rm minus_infinity minus_infinity)"
  oops

(* division(0, 0) or division(\<infinity>, \<infinity>) is NaN *)
lemma zero_div_zero: "is_zero x \<Longrightarrow> is_nan (fdiv rm x x)"
  oops

lemma inf_div_inf: "is_infinity x \<Longrightarrow> is_nan (fdiv rm x x)"
  oops

(* remainder(x, y), when y is zero or x is infinite is NaN *)
lemma frem_inf_zero: "(is_zero y \<or> is_infinity x) \<Longrightarrow> is_nan (frem rm x y)"
  oops

(* squareRoot if the operand is less than zero is NaN *)
lemma fsqrt_neg: "x < 0 \<Longrightarrow> is_nan (fsqrt rm x)"
  oops



(* ROUNDING *)
(* from Handbook of Floating-Point Arithmetic by J-M Muller *)

(* x \<le> y \<Longrightarrow> round(x) \<le> round(y) *)
lemma leq_round: "x \<le> y \<Longrightarrow> round rm (valof x) \<le> round rm (valof y)"
  oops

(* If y is a floating-point number, then round(y) = y *)
lemma round_id: "\<not>(is_nan x) \<Longrightarrow> feq (round rm (valof x)) x"
  oops

(* RU(a + b) = − RD(−a − b) *)
lemma round_add_eq_sub: "\<not>(is_nan x \<and> is_nan y) \<Longrightarrow> feq (fadd To_pinfinity x y) (- (fsub To_ninfinity (-x) y))"
  oops

(* RD(a \<times> b) = − RU((−a) \<times> b) *)
lemma round_mul_eq: "\<not>(is_nan x \<and> is_nan y) \<Longrightarrow> feq (fmul To_ninfinity x y) (- (fmul To_pinfinity (-x) y))"
  oops

(* Sterbenz: b/2 \<le> a \<le> 2b \<Longrightarrow> a-b is exact *)
lemma sterbenz:
  assumes "is_finite x" "is_finite y"
  shows "(valof y)/2 \<le> valof x \<and> valof x \<le> 2*(valof y) \<Longrightarrow> 
          valof x - valof y = valof (fsub rm x y)"
  oops

(* Hauser: if RN(x + y) is subnormal, then RN(x + y) = x + y exactly *)
lemma hauser: "is_denormal (x+y) \<Longrightarrow> valof (x+y) = valof x + valof y"
  oops

end