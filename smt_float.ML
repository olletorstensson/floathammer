(*  Title:      IEEE_Floating_Point/smt_float.ML
    Author:     Olle Torstensson, Uppsala University

SMT setup for floating-points.

This file provides an interpretation of floating-point related types and
constants found in IEEE_Floating_Point/IEEE.thy into SMT-LIB. The interpretation
encompasses
  - fixed format floating-point types,
  - the rounding mode type,
  - floating-point value construction from bit vector triples,
  - special floating-point values (0, infinity, and NaN),
  - rounding modes,
  - classification operations,
  - arithmetic operations,
  - comparison operations, and
  - type conversion to and from the reals.

The interpretation does NOT cover polymorphic floating-point types; variables
and constants with a floating-point type will in general need to be attached
with explicit type constraints in order to trigger the interpretation.

NB: This interpretation introduces an element of unsoundness to the
translation into SMT-LIB.

See my MSc thesis for details.
*)

structure SMT_Float: sig end =
struct

(*Determine whether a type is a floating-point type of a fixed format supported by the SMT-LIB.*)
fun is_float (Type (\<^type_name>\<open>IEEE.float\<close>, [e,f])) =
      can (apply2 Word_Lib.dest_binT) (e,f) andalso
      Word_Lib.dest_binT e > 1 andalso
      Word_Lib.dest_binT f > 0
  | is_float _ = false

(*Extract type arguments from floating-point types of fixed formats.*)
fun float_Targs (T as (Type (\<^type_name>\<open>IEEE.float\<close>, [e,f]))) =
      if is_float T then
        SOME (Word_Lib.dest_binT e, Word_Lib.dest_binT f)
      else
        NONE
  | float_Targs _ = NONE

(*True except for floating-point types of unsupported formats.*)
fun is_valid_type (T as (Type (\<^type_name>\<open>IEEE.float\<close>, _))) = is_float T
  | is_valid_type _ = true


(* SMT-LIB logic *)

(*
  SMT-LIB logics are generally too restrictive for Isabelle's problems. "ALL"
  denotes the most general logic supported by the solver, and is chosen if a
  rounding mode or supported floating-point type is encountered among the terms.
*)
fun smtlib_logic ts =
      let
        fun is_float_or_rm (Type (\<^type_name>\<open>IEEE.roundmode\<close>, _)) = true
          | is_float_or_rm T = is_float T
      in
        if exists (Term.exists_type (Term.exists_subtype is_float_or_rm)) ts then
          SOME "ALL"
        else
          NONE
      end


(* SMT-LIB built-ins *)

(*Interpret floating-point related types and constants supported by the SMT-LIB.*)
local
  
  (*SMT-LIB syntax template for parameterized sorts and functions.*)
  fun param_template s args =
  	"(_ " ^ s ^ " " ^ string_of_int (fst args) ^ " " ^ string_of_int (snd args + 1) ^ ")"

  fun float_typ T = Option.map (rpair [] o param_template "FloatingPoint") (float_Targs T)

  (*
    Generic function for interpreting floating-point constants.
    f can be used to customize the interpretation.
  *)
  fun add_float_fun f (t, s) =
    let
      val (n, _) = Term.dest_Const t
    in
      SMT_Builtin.add_builtin_fun SMTLIB_Interface.smtlibC (Term.dest_Const t, f n s)
    end

  (*Map (s, e, f) to [s, e, f].*)
  fun extract_words triple =
    let
      val ((_, s), c) = apfst Term.dest_comb (Term.dest_comb triple)
      val ((_, e), f) = apfst Term.dest_comb (Term.dest_comb c)
    in
      [s, e, f]
    end

  fun mk_floatval c [s, e, f] = Const c $ s $ e $ f
    | mk_floatval c ts = raise TERM ("bad arguments", Const c :: ts)
  
  (*Customized interpretation for Abs_float. Change type and redirect to Abs_float_dummy.*)
  fun add_floatval _ s _ T ts =
    let
      val newT =
        @{typ "1 word \<Rightarrow> 'e word \<Rightarrow> 'f word \<Rightarrow> ('e, 'f) IEEE.float"}
    in
      case (is_float (Term.body_type T), try (extract_words o hd) ts) of
        (true, SOME words) => SOME (s, 3, words, mk_floatval ("Abs_float_dummy", newT))
      | _ => NONE
    end

  (*Customized interpretation. Check whether the type is supported and add type arguments.*)
  fun add_with_Targs n s _ T ts =
    let
      val (Us, U) = Term.strip_type T
      val all_valid = forall is_valid_type (U::Us)
    in
      case (all_valid, float_Targs U) of
        (true, SOME args) =>
          SOME (param_template s args, length Us, ts, Term.list_comb o pair (Const (n, T)))
      | _ => NONE
    end

  (*Customized interpretation. Check whether the type is supported.*)
  fun add_if_fixed n s _ T ts =
    let
      val (Us, U) = Term.strip_type T
      val all_valid = forall is_valid_type (U::Us)
    in
      if all_valid then
        SOME (s, length Us, ts, Term.list_comb o pair (Const (n, T)))
      else
        NONE
    end
  
  fun arith_of_default n T =
    let
      val newT = \<^typ>\<open>IEEE.roundmode\<close> --> T
    in
      case n of
        \<^const_name>\<open>plus\<close> =>
          SOME (Const (\<^const_name>\<open>IEEE.fadd\<close>, newT))
      | \<^const_name>\<open>minus\<close> =>
          SOME (Const (\<^const_name>\<open>IEEE.fsub\<close>, newT))
      | \<^const_name>\<open>times\<close> =>
          SOME (Const (\<^const_name>\<open>IEEE.fmul\<close>, newT))
      | \<^const_name>\<open>divide\<close> =>
          SOME (Const (\<^const_name>\<open>IEEE.fdiv\<close>, newT))
      | \<^const_name>\<open>IEEE.float_sqrt\<close> =>
          SOME (Const (\<^const_name>\<open>IEEE.fsqrt\<close>, newT))
      | \<^const_name>\<open>IEEE.ROUNDFLOAT\<close> =>
          SOME (Const (\<^const_name>\<open>IEEE.fintrnd\<close>, newT))
      | _ => NONE
    end

  (*Customized interpretation. Check whether the type is supported and add rounding mode.*)
  fun add_with_rm n s _ T ts =
    let
      val mode = @{const IEEE.To_nearest}
      val (Us, U) = Term.strip_type T
      val all_valid = forall is_valid_type (U::Us)
    in
      case (all_valid, arith_of_default n T) of
        (true, SOME c) => SOME (s, length Us + 1, mode::ts, Term.list_comb o pair c)
      | _ => NONE
    end
  
  (*
    Customized interpretation for frem.
    Check whether the type is supported and remove rounding mode.
  *)
  fun add_frem _ s _ T ts =
    let
      val (Us, U) = Term.strip_type T
      val all_valid = forall is_valid_type (U::Us)
      val newT = (tl Us) ---> U
      val c = Const (\<^const_name>\<open>IEEE.float_rem\<close>, newT)
    in
      if all_valid then
        SOME (s, length Us - 1, tl ts, Term.list_comb o pair c)
      else
        NONE
    end

in

val setup_builtins =

  (*Types*)
  fold (SMT_Builtin.add_builtin_typ SMTLIB_Interface.smtlibC) [
    (\<^typ>\<open>('e::len,'f::len) float\<close>, float_typ, K (K NONE)),
    (\<^typ>\<open>roundmode\<close>, K (SOME ("RoundingMode", [])), K (K NONE))] #>
  
  (*
    General floating-point value construction.
    The type of Abs_float is changed to correspond with the rank of fp.
  *)
  add_float_fun add_floatval
    (@{const IEEE.Abs_float (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "") #>
  SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC
    (Const
     ("Abs_float_dummy",
      @{typ "1 word \<Rightarrow> 'e word \<Rightarrow> 'f word \<Rightarrow> ('e, 'f) IEEE.float"}),
     "fp") #>

  (*Special floating-point values*)
  fold (add_float_fun add_with_Targs) [
    (@{const zero_class.zero (\<open>('e,'f) float\<close>)}, "+zero"),
    (@{const IEEE.plus_infinity (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "+oo"),
    (@{const IEEE.some_nan (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "NaN")] #>

  (*Rounding modes*)
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (@{const IEEE.To_nearest}, "RNE"),
    (@{const IEEE.To_pinfinity}, "RTP"),
    (@{const IEEE.To_ninfinity}, "RTN"),
    (@{const IEEE.float_To_zero}, "RTZ"),
    (@{const IEEE.To_nearest_away}, "RNA")] #>

  (*Classification*)
  fold (add_float_fun add_if_fixed) [
    (@{const IEEE.is_zero (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isZero"),
    (@{const IEEE.is_infinity (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isInfinite"),
    (@{const IEEE.is_nan (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isNaN"),
    (@{const IEEE.is_normal (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isNormal"),
    (@{const IEEE.is_denormal (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isSubnormal")] #>

  (*Arithmetic operations*)
  fold (add_float_fun add_if_fixed) [
    (@{const abs (\<open>('e,'f) float\<close>)},"fp.abs"),
    (@{const uminus (\<open>('e,'f) float\<close>)},"fp.neg"),
    (@{const IEEE.fadd (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.add"),
    (@{const IEEE.fsub (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.sub"),
    (@{const IEEE.fmul (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.mul"),
    (@{const IEEE.fdiv (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.div"),
    (@{const IEEE.fmul_add (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.fma"),
    (@{const IEEE.fsqrt (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.sqrt"),
    (@{const IEEE.fintrnd (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.roundToIntegral"),
    (@{const IEEE.float_rem (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.rem")] #>
  (*Interpret as its rounding-mode-requiring version.*)
  fold (add_float_fun add_with_rm) [
    (@{const plus (\<open>('e,'f) float\<close>)}, ""),
    (@{const minus (\<open>('e,'f) float\<close>)}, ""),
    (@{const times (\<open>('e,'f) float\<close>)}, ""),
    (@{const divide (\<open>('e,'f) float\<close>)}, ""),
    (@{const IEEE.float_sqrt (\<open>'e::len\<close>,\<open>'f::len\<close>)}, ""),
    (@{const IEEE.ROUNDFLOAT (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "")] #>
  (*Interpret as its non-rounding-mode-requiring version.*)
  add_float_fun add_frem
    (@{const IEEE.frem (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "") #>

  (*Comparison operations*)
  fold (add_float_fun add_if_fixed) [
    (@{const less (\<open>('e,'f) float\<close>)},"fp.lt"),
    (@{const less_eq (\<open>('e,'f) float\<close>)},"fp.leq"),
    (@{const IEEE.flt (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.lt"),
    (@{const IEEE.fle (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.leq"),
    (@{const IEEE.fgt (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.gt"),
    (@{const IEEE.fge (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.geq"),
    (@{const IEEE.feq (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.eq"),
    (@{const IEEE.float_eq (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.eq")] #>

  (*Type conversion*)
  add_float_fun add_if_fixed
    (@{const IEEE.valof (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.to_real") #>
  add_float_fun add_with_Targs
    (@{const IEEE.round (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "to_fp")

end


(* Setup *)

(*Override any other logic.*)
val _ = Theory.setup (Context.theory_map (
  SMTLIB_Interface.add_logic (0, smtlib_logic) #>
  setup_builtins))

end;