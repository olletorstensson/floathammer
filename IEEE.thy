(* Formalization of IEEE-754 Standard for binary floating-point arithmetic *)
(* Author: Lei Yu, University of Cambridge *)

(* Modifications made by Olle: roundmode, round, intround, frem *)

section ‹Specification of the IEEE standard›

theory IEEE
  imports
    "HOL-Library.Float"
    Word_Lib.Word_Lemmas
begin

typedef (overloaded) ('e::len, 'f::len) float = "UNIV::(1 word × 'e word × 'f word) set"
  by auto

setup_lifting type_definition_float

syntax "_float" :: "type ⇒ type ⇒ type" ("'(_, _') float")
text ‹parse ‹('a, 'b) float› as ('a::len, 'b::len) float.›

parse_translation ‹
  let
    fun float t u = Syntax.const @{type_syntax float} $ t $ u;
    fun len_tr u =
      (case Term_Position.strip_positions u of
        v as Free (x, _) =>
          if Lexicon.is_tid x then
            (Syntax.const @{syntax_const "_ofsort"} $ v $
              Syntax.const @{class_syntax len})
          else u
      | _ => u)
    fun len_float_tr [t, u] =
      float (len_tr t) (len_tr u)
  in
    [(@{syntax_const "_float"}, K len_float_tr)]
  end
›

subsection ‹Derived parameters for floating point formats›

definition wordlength :: "('e, 'f) float itself ⇒ nat"
  where "wordlength x = LENGTH('e) + LENGTH('f) + 1"

definition bias :: "('e, 'f) float itself ⇒ nat"
  where "bias x = 2^(LENGTH('e) - 1) - 1"

definition emax :: "('e, 'f) float itself ⇒ nat"
  where "emax x = unat(max_word::'e word)"

abbreviation fracwidth::"('e, 'f) float itself ⇒ nat" where
  "fracwidth _ ≡ LENGTH('f)"

subsection ‹Predicates for the four IEEE formats›

definition is_single :: "('e, 'f) float itself ⇒ bool"
  where "is_single x ⟷ LENGTH('e) = 8 ∧ wordlength x = 32"

definition is_double :: "('e, 'f) float itself ⇒ bool"
  where "is_double x ⟷ LENGTH('e) = 11 ∧ wordlength x = 64"

definition is_single_extended :: "('e, 'f) float itself ⇒ bool"
  where "is_single_extended x ⟷ LENGTH('e) ≥ 11 ∧ wordlength x ≥ 43"

definition is_double_extended :: "('e, 'f) float itself ⇒ bool"
  where "is_double_extended x ⟷ LENGTH('e) ≥ 15 ∧ wordlength x ≥ 79"


subsection ‹Extractors for fields›

lift_definition sign::"('e, 'f) float ⇒ nat" is
  "λ(s::1 word, _::'e word, _::'f word). unat s" .

lift_definition exponent::"('e, 'f) float ⇒ nat" is
  "λ(_, e::'e word, _). unat e" .

lift_definition fraction::"('e, 'f) float ⇒ nat" is
  "λ(_, _, f::'f word). unat f" .

abbreviation "real_of_word x ≡ real (unat x)"

lift_definition valof :: "('e, 'f) float ⇒ real"
is "λ(s, e, f).
    let x = (TYPE(('e, 'f) float)) in
    (if e = 0
     then (-1::real)^(unat s) * (2 / (2^bias x)) * (real_of_word f/2^(LENGTH('f)))
     else (-1::real)^(unat s) * ((2^(unat e)) / (2^bias x)) * (1 + real_of_word f/2^LENGTH('f)))"
  .

subsection ‹Partition of numbers into disjoint classes›

definition is_nan :: "('e, 'f) float ⇒ bool"
  where "is_nan a ⟷ exponent a = emax TYPE(('e, 'f)float) ∧ fraction a ≠ 0"

definition is_infinity :: "('e, 'f) float ⇒ bool"
  where "is_infinity a ⟷ exponent a = emax TYPE(('e, 'f)float) ∧ fraction a = 0"

definition is_normal :: "('e, 'f) float ⇒ bool"
  where "is_normal a ⟷ 0 < exponent a ∧ exponent a < emax TYPE(('e, 'f)float)"

definition is_denormal :: "('e, 'f) float ⇒ bool"
  where "is_denormal a ⟷ exponent a = 0 ∧ fraction a ≠ 0"

definition is_zero :: "('e, 'f) float ⇒ bool"
  where "is_zero a ⟷ exponent a = 0 ∧ fraction a = 0"

definition is_finite :: "('e, 'f) float ⇒ bool"
  where "is_finite a ⟷ (is_normal a ∨ is_denormal a ∨ is_zero a)"


subsection ‹Special values›

lift_definition plus_infinity :: "('e, 'f) float" ("∞") is "(0, max_word, 0)" .

lift_definition topfloat :: "('e, 'f) float" is "(0, max_word - 1, 2^LENGTH('f) - 1)" .

instantiation float::(len, len) zero begin

lift_definition zero_float :: "('e, 'f) float" is "(0, 0, 0)" .

instance proof qed

end

subsection ‹Negation operation on floating point values›

instantiation float::(len, len) uminus begin
lift_definition uminus_float :: "('e, 'f) float ⇒ ('e, 'f) float" is  "λ(s, e, f). (1 - s, e, f)" .
instance proof qed
end

abbreviation (input) "minus_zero ≡ - (0::('e, 'f)float)"
abbreviation (input) "minus_infinity ≡ - ∞"
abbreviation (input) "bottomfloat ≡ - topfloat"


subsection ‹Real number valuations›

text ‹The largest value that can be represented in floating point format.›
definition largest :: "('e, 'f) float itself ⇒ real"
  where "largest x = (2^(emax x - 1) / 2^bias x) * (2 - 1/(2^fracwidth x))"

text ‹Threshold, used for checking overflow.›
definition threshold :: "('e, 'f) float itself ⇒ real"
  where "threshold x = (2^(emax x - 1) / 2^bias x) * (2 - 1/(2^(Suc(fracwidth x))))"

text ‹Unit of least precision.›

lift_definition one_lp::"('e ,'f) float ⇒ ('e ,'f) float" is "λ(s, e, f). (0, e::'e word, 1)" .
lift_definition zero_lp::"('e ,'f) float ⇒ ('e ,'f) float" is "λ(s, e, f). (0, e::'e word, 0)" .

definition ulp :: "('e, 'f) float ⇒ real" where "ulp a = valof (one_lp a) - valof (zero_lp a)"

text ‹Enumerated type for rounding modes.›
datatype roundmode = To_nearest | float_To_zero | To_pinfinity | To_ninfinity | To_nearest_away

text ‹Characterization of best approximation from a set of abstract values.›
definition "is_closest v s x a ⟷ a ∈ s ∧ (∀b. b ∈ s ⟶ ¦v a - x¦ ≤ ¦v b - x¦)"

text ‹Best approximation with a deciding preference for multiple possibilities.›
definition "closest v p s x =
  (SOME a. is_closest v s x a ∧ ((∃b. is_closest v s x b ∧ p b) ⟶ p a))"


subsection ‹Rounding›

fun round :: "roundmode ⇒ real ⇒ ('e ,'f) float"
where
  "round To_nearest y =
   (if y ≤ - threshold TYPE(('e ,'f) float) then minus_infinity
    else if y ≥ threshold TYPE(('e ,'f) float) then plus_infinity
    else closest (valof) (λa. even (fraction a)) {a. is_finite a} y)"
| "round float_To_zero y =
   (if y < - largest TYPE(('e ,'f) float) then bottomfloat
    else if y > largest TYPE(('e ,'f) float) then topfloat
    else closest (valof) (λa. True) {a. is_finite a ∧ ¦valof a¦ ≤ ¦y¦} y)"
| "round To_pinfinity y =
   (if y < - largest TYPE(('e ,'f) float) then bottomfloat
    else if y > largest TYPE(('e ,'f) float) then plus_infinity
    else closest (valof) (λa. True) {a. is_finite a ∧ valof a ≥ y} y)"
| "round To_ninfinity y =
   (if y < - largest TYPE(('e ,'f) float) then minus_infinity
    else if y > largest TYPE(('e ,'f) float) then topfloat
    else closest (valof) (λa. True) {a. is_finite a ∧ valof a ≤ y} y)"
| "round To_nearest_away y =
   (if y ≤ - threshold TYPE(('e ,'f) float) then minus_infinity
    else if y ≥ threshold TYPE(('e ,'f) float) then plus_infinity
    else closest (valof) (λa. ¦y¦ ≤ ¦valof a¦) {a. is_finite a} y)"

text ‹Rounding to integer values in floating point format.›

definition is_integral :: "('e ,'f) float ⇒ bool"
  where "is_integral a ⟷ is_finite a ∧ (∃n::nat. ¦valof a¦ = real n)"

fun intround :: "roundmode ⇒ real ⇒ ('e ,'f) float"
where
  "intround To_nearest y =
    (if y ≤ - threshold TYPE(('e ,'f) float) then minus_infinity
     else if y ≥ threshold TYPE(('e ,'f) float) then plus_infinity
     else closest (valof) (λa. (∃n::nat. even n ∧ ¦valof a¦ = real n)) {a. is_integral a} y)"
|"intround float_To_zero y =
    (if y < - largest TYPE(('e ,'f) float) then bottomfloat
     else if y > largest TYPE(('e ,'f) float) then topfloat
     else closest (valof) (λx. True) {a. is_integral a ∧ ¦valof a¦ ≤ ¦y¦} y)"
|"intround To_pinfinity y =
    (if y < - largest TYPE(('e ,'f) float) then bottomfloat
     else if y > largest TYPE(('e ,'f) float) then plus_infinity
     else closest (valof) (λx. True) {a. is_integral a ∧ valof a ≥ y} y)"
|"intround To_ninfinity y =
    (if y < - largest TYPE(('e ,'f) float) then minus_infinity
     else if y > largest TYPE(('e ,'f) float) then topfloat
     else closest (valof) (λx. True) {a. is_integral a ∧ valof a ≥ y} y)"
|"intround To_nearest_away y =
    (if y ≤ - threshold TYPE(('e ,'f) float) then minus_infinity
     else if y ≥ threshold TYPE(('e ,'f) float) then plus_infinity
     else closest (valof) (λa. ¦y¦ ≤ ¦valof a¦) {a. is_integral a} y)"

text ‹Round, choosing between -0.0 or +0.0›

definition float_round::"roundmode ⇒ bool ⇒ real ⇒ ('e, 'f) float"
  where "float_round mode toneg r =
      (let x = round mode r in
         if is_zero x
            then if toneg
                    then minus_zero
                 else 0
         else x)"

text ‹Non-standard of NaN.›
definition some_nan :: "('e ,'f) float"
  where "some_nan = (SOME a. is_nan a)"

text ‹Coercion for signs of zero results.›
definition zerosign :: "nat ⇒ ('e ,'f) float ⇒ ('e ,'f) float"
  where "zerosign s a =
    (if is_zero a then (if s = 0 then 0 else - 0) else a)"

text ‹Remainder operation.›
definition rem :: "real ⇒ real ⇒ real"
  where "rem x y =
    (let n = closest id (λx. ∃n::nat. even n ∧ ¦x¦ = real n) {x. ∃n :: nat. ¦x¦ = real n} (x / y)
     in x - n * y)"

definition frem :: "roundmode ⇒ ('e ,'f) float ⇒ ('e ,'f) float ⇒ ('e ,'f) float"
  where "frem m a b =
    (if is_nan a ∨ is_nan b ∨ is_infinity a ∨ is_zero b then some_nan
     else if is_infinity b then a
     else zerosign (sign a) (round m (rem (valof a) (valof b))))"


subsection ‹Definitions of the arithmetic operations›

definition fintrnd :: "roundmode ⇒ ('e ,'f) float ⇒ ('e ,'f) float"
  where "fintrnd m a =
    (if is_nan a then (some_nan)
     else if is_infinity a then a
     else zerosign (sign a) (intround m (valof a)))"

definition fadd :: "roundmode ⇒ ('e ,'f) float ⇒ ('e ,'f) float ⇒ ('e ,'f) float"
  where "fadd m a b =
    (if is_nan a ∨ is_nan b ∨ (is_infinity a ∧ is_infinity b ∧ sign a ≠ sign b)
     then some_nan
     else if (is_infinity a) then a
     else if (is_infinity b) then b
     else
      zerosign
        (if is_zero a ∧ is_zero b ∧ sign a = sign b then sign a
         else if m = To_ninfinity then 1 else 0)
        (round m (valof a + valof b)))"

definition fsub :: "roundmode ⇒ ('e ,'f) float ⇒ ('e ,'f) float ⇒ ('e ,'f) float"
  where "fsub m a b =
    (if is_nan a ∨ is_nan b ∨ (is_infinity a ∧ is_infinity b ∧ sign a = sign b)
     then some_nan
     else if is_infinity a then a
     else if is_infinity b then - b
     else
      zerosign
        (if is_zero a ∧ is_zero b ∧ sign a ≠ sign b then sign a
         else if m = To_ninfinity then 1 else 0)
        (round m (valof a - valof b)))"

definition fmul :: "roundmode ⇒ ('e ,'f) float ⇒ ('e ,'f) float ⇒ ('e ,'f) float"
  where "fmul m a b =
    (if is_nan a ∨ is_nan b ∨ (is_zero a ∧ is_infinity b) ∨ (is_infinity a ∧ is_zero b)
     then some_nan
     else if is_infinity a ∨ is_infinity b
     then (if sign a = sign b then plus_infinity else minus_infinity)
     else zerosign (if sign a = sign b then 0 else 1 ) (round m (valof a * valof b)))"

definition fdiv :: "roundmode ⇒ ('e ,'f) float ⇒ ('e ,'f) float ⇒ ('e ,'f) float"
  where "fdiv m a b =
    (if is_nan a ∨ is_nan b ∨ (is_zero a ∧ is_zero b) ∨ (is_infinity a ∧ is_infinity b)
     then some_nan
     else if is_infinity a ∨ is_zero b
     then (if sign a = sign b then plus_infinity else minus_infinity)
     else if is_infinity b
     then (if sign a = sign b then 0 else - 0)
     else zerosign (if sign a = sign b then 0 else 1) (round m (valof a / valof b)))"

definition fsqrt :: "roundmode ⇒ ('e ,'f) float ⇒ ('e ,'f) float"
  where "fsqrt m a =
    (if is_nan a then some_nan
     else if is_zero a ∨ is_infinity a ∧ sign a = 0 then a
     else if sign a = 1 then some_nan
     else zerosign (sign a) (round m (sqrt (valof a))))"

definition fmul_add :: "roundmode ⇒ ('t ,'w) float ⇒ ('t ,'w) float ⇒ ('t ,'w) float ⇒ ('t ,'w) float"
  where "fmul_add mode x y z =
      (let signP = if sign x = sign y then 0 else 1 in
      let infP = is_infinity x  ∨ is_infinity y
      in
         if is_nan x ∨ is_nan y ∨ is_nan z then some_nan
         else if is_infinity x ∧ is_zero y ∨
                 is_zero x ∧ is_infinity y ∨
                 is_infinity z ∧ infP ∧ signP ≠ sign z then
            some_nan
         else if is_infinity z ∧ (sign z = 0) ∨ infP ∧ (signP = 0)
            then plus_infinity
         else if is_infinity z ∧ (sign z = 1) ∨ infP ∧ (signP = 1)
            then minus_infinity
         else
            let r1 = valof x * valof y;
                r2 = valof z
            in
              float_round mode
                (if (r1 = 0) ∧ (r2 = 0) ∧ (signP = sign z) then
                   signP = 1
                 else mode = To_ninfinity) (r1 + r2))"


subsection ‹Comparison operations›

datatype ccode = Gt | Lt | Eq | Und

definition fcompare :: "('e ,'f) float ⇒ ('e ,'f) float ⇒ ccode"
  where "fcompare a b =
    (if is_nan a ∨ is_nan b then Und
     else if is_infinity a ∧ sign a = 1
     then (if is_infinity b ∧ sign b = 1 then Eq else Lt)
     else if is_infinity a ∧ sign a = 0
     then (if is_infinity b ∧ sign b = 0 then Eq else Gt)
     else if is_infinity b ∧ sign b = 1 then Gt
     else if is_infinity b ∧ sign b = 0 then Lt
     else if valof a < valof b then Lt
     else if valof a = valof b then Eq
     else Gt)"

definition flt :: "('e ,'f) float ⇒ ('e ,'f) float ⇒ bool"
  where "flt a b ⟷ fcompare a b = Lt"

definition fle :: "('e ,'f) float ⇒ ('e ,'f) float ⇒ bool"
  where "fle a b ⟷ fcompare a b = Lt ∨ fcompare a b = Eq"

definition fgt :: "('e ,'f) float ⇒ ('e ,'f) float ⇒ bool"
  where "fgt a b ⟷ fcompare a b = Gt"

definition fge :: "('e ,'f) float ⇒ ('e ,'f) float ⇒ bool"
  where "fge a b ⟷ fcompare a b = Gt ∨ fcompare a b = Eq"

definition feq :: "('e ,'f) float ⇒ ('e ,'f) float ⇒ bool"
  where "feq a b ⟷ fcompare a b = Eq"


section ‹Specify float to be double  precision and round to even›

instantiation float :: (len, len) plus
begin

definition plus_float :: "('a, 'b) float ⇒ ('a, 'b) float ⇒ ('a, 'b) float"
  where "a + b = fadd To_nearest a b"

instance ..

end

instantiation float :: (len, len) minus
begin

definition minus_float :: "('a, 'b) float ⇒ ('a, 'b) float ⇒ ('a, 'b) float"
  where "a - b = fsub To_nearest a b"

instance ..

end

instantiation float :: (len, len) times
begin

definition times_float :: "('a, 'b) float ⇒ ('a, 'b) float ⇒ ('a, 'b) float"
  where "a * b = fmul To_nearest a b"

instance ..

end

instantiation float :: (len, len) one
begin

lift_definition one_float :: "('a, 'b) float" is "(0, 2^(LENGTH('a) - 1) - 1, 0)" .

instance ..

end

instantiation float :: (len, len) inverse
begin

definition divide_float :: "('a, 'b) float ⇒ ('a, 'b) float ⇒ ('a, 'b) float"
  where "a div b = fdiv To_nearest a b"

definition inverse_float :: "('a, 'b) float ⇒ ('a, 'b) float"
  where "inverse_float a = fdiv To_nearest 1 a"

instance ..

end

definition float_rem :: "('a, 'b) float ⇒ ('a, 'b) float ⇒ ('a, 'b) float"
  where "float_rem a b = frem To_nearest a b"

definition float_sqrt :: "('a, 'b) float ⇒ ('a, 'b) float"
  where "float_sqrt a = fsqrt To_nearest a"

definition ROUNDFLOAT ::"('a, 'b) float ⇒ ('a, 'b) float"
  where "ROUNDFLOAT a = fintrnd To_nearest a"


instantiation float :: (len, len) ord
begin

definition less_float :: "('a, 'b) float ⇒ ('a, 'b) float ⇒ bool"
  where "a < b ⟷ flt a b"

definition less_eq_float :: "('a, 'b) float ⇒ ('a, 'b) float ⇒ bool"
  where "a ≤ b ⟷ fle a b"

instance ..

end

definition float_eq :: "('a, 'b) float ⇒ ('a, 'b) float ⇒ bool"  (infixl "≐" 70)
  where "float_eq a b = feq a b"

instantiation float :: (len, len) abs
begin

definition abs_float :: "('a, 'b) float ⇒ ('a, 'b) float"
  where "abs_float a = (if sign a = 0 then a else - a)"

instance ..
end

text ‹The ‹1 + ε› property.›
definition normalizes :: "_ itself ⇒ real ⇒ bool"
  where "normalizes float_format x =
    (1/ (2::real)^(bias float_format - 1) ≤ ¦x¦ ∧ ¦x¦ < threshold float_format)"

end
