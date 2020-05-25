structure SMT_Float: sig end =
struct

(* Helpers *)
(* TODO: Tidy up *)
fun is_float (Type (\<^type_name>‹IEEE.float›, [e,f])) =
      can (apply2 Word_Lib.dest_binT) (e,f) andalso
      Word_Lib.dest_binT e > 1 andalso Word_Lib.dest_binT f > 1
  | is_float _ = false

fun float_Targs (Type (\<^type_name>‹IEEE.float›, [e,f])) =
      if can (apply2 Word_Lib.dest_binT) (e,f) andalso
      Word_Lib.dest_binT e > 1 andalso Word_Lib.dest_binT f > 1 then
        SOME (Word_Lib.dest_binT e, Word_Lib.dest_binT f)
      else
        NONE
  | float_Targs _ = NONE


(* SMT-LIB logic *)
fun smtlib_logic ts =
      if exists (Term.exists_type (Term.exists_subtype is_float)) ts then
        SOME "ALL"
      else
        NONE


(* SMT-LIB built-ins *)
local

  fun typ_template args = "(_ FloatingPoint " ^ string_of_int (fst args) ^
                            " " ^ string_of_int (snd args + 1) ^ ")"

  fun float_typ T = Option.map (rpair [] o typ_template) (float_Targs T)

  fun extract_words trip =
    let
      val ((_, s), c) = apfst Term.dest_comb (Term.dest_comb trip)
      val ((_, e), f) = apfst Term.dest_comb (Term.dest_comb c)
    in
      [s, e, f]
    end

  fun mk_floatS c [s, e, f] = Const c $ s $ e $ f
    | mk_floatS c ts = raise TERM ("bad arguments", Const c :: ts)

  fun const_val _ T ts =
    if is_float (Term.body_type T) then
      SOME ("fp", 3, extract_words (hd ts), mk_floatS ("Abs_float",
        @{typ "1 word ⇒ 'e word ⇒ 'f word ⇒ ('e, 'f) IEEE.float"}))
    else
      NONE

in

val setup_builtins =

  (* Type *)
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.smtlibC
    (\<^typ>‹('e::len,'f::len) float›, float_typ, K (K NONE)) #>
  
  (* Constant values *)
  SMT_Builtin.add_builtin_fun SMTLIB_Interface.smtlibC
    (Term.dest_Const @{const Abs_float ('e,'f)}, const_val) #>
  SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC
    (Const ("Abs_float",
      @{typ "1 word ⇒ 'e word ⇒ 'f word ⇒ ('e, 'f) IEEE.float"}), "fp") #>


  (* TODO: Interpret operation only if type arguments are fixed *)

  (* Special values *)
  

  (* Classification *)
  (* TODO: Add positivity and negativity *)
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (\<^term>‹is_zero :: ('e::len, 'f::len) float ⇒ _›, "fp.isZero"),
    (\<^term>‹is_infinity :: ('e::len, 'f::len) float ⇒ _›, "fp.isInfinite"),
    (\<^term>‹is_nan :: ('e::len, 'f::len) float ⇒ _›, "fp.isNaN"),
    (\<^term>‹is_normal :: ('e::len, 'f::len) float ⇒ _›, "fp.isNormal"),
    (\<^term>‹is_denormal :: ('e::len, 'f::len) float ⇒ _›, "fp.isSubnormal")] #>

  (* Rounding modes *)
  (* TODO: Add RNA *)
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.smtlibC
    (\<^typ>‹roundmode›, K (SOME ("RoundingMode", [])), K (K NONE)) #>
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (\<^term>‹To_nearest :: roundmode›, "RNE"),
    (\<^term>‹To_pinfinity :: roundmode›, "RTP"),
    (\<^term>‹To_ninfinity :: roundmode›, "RTN"),
    (\<^term>‹float_To_zero :: roundmode›, "RTZ")] #>

  (* Arithmetic operations *)
  (* TODO: Add instantiated versions,
           Add remainder op,
           Add min and max ops,
           Check for linearity *)
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (@{const abs (‹('e,'f) float›)},"fp.abs"),
    (@{const uminus (‹('e,'f) float›)},"fp.neg")] #>
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (\<^term>‹fadd :: roundmode ⇒ ('e::len, 'f::len) float ⇒ _›, "fp.add"),
    (\<^term>‹fsub :: roundmode ⇒ ('e::len, 'f::len) float ⇒ _›, "fp.sub"),
    (\<^term>‹fmul :: roundmode ⇒ ('e::len, 'f::len) float ⇒ _›, "fp.mul"),
    (\<^term>‹fdiv :: roundmode ⇒ ('e::len, 'f::len) float ⇒ _›, "fp.div"),
    (\<^term>‹fmul_add :: roundmode ⇒ ('e::len, 'f::len) float ⇒ _›, "fp.fma"),
    (\<^term>‹fsqrt :: roundmode ⇒ ('e::len, 'f::len) float ⇒ _›, "fp.sqrt"),
    (\<^term>‹fintrnd :: roundmode ⇒ ('e::len, 'f::len) float ⇒ _›, "fp.roundToIntegral")] #>


  (* Comparison operations *)
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (\<^term>‹flt :: ('e::len, 'f::len) float ⇒ _›, "fp.lt"),
    (\<^term>‹fle :: ('e::len, 'f::len) float ⇒ _›, "fp.leq"),
    (\<^term>‹fgt :: ('e::len, 'f::len) float ⇒ _›, "fp.gt"),
    (\<^term>‹fge :: ('e::len, 'f::len) float ⇒ _›, "fp.geq"),
    (\<^term>‹feq :: ('e::len, 'f::len) float ⇒ _›, "fp.eq"),
    (\<^term>‹float_eq :: ('e::len, 'f::len) float ⇒ _›, "fp.eq")] #>
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (@{const less_eq (‹('e,'f) float›)},"fp.leq"),
    (@{const less (‹('e,'f) float›)},"fp.lt")] #>

  (* Type conversion *)
  (* Add non-real conversions *)
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (\<^term>‹valof :: ('e::len, 'f::len) float ⇒ _›, "fp.to_real")]

end


(* setup *)
(* TODO: Investigate precedence constant *)

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Interface.add_logic (11, smtlib_logic) #>
  setup_builtins))

end;
