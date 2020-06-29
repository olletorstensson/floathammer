(* TODO: Add header and helpful comments *)
structure SMT_Float: sig end =
struct

(* Helpers *)
fun is_float (Type (\<^type_name>‹IEEE.float›, [e,f])) =
      can (apply2 Word_Lib.dest_binT) (e,f) andalso
      Word_Lib.dest_binT e > 1 andalso Word_Lib.dest_binT f > 1
  | is_float _ = false

fun float_Targs (T as (Type (\<^type_name>‹IEEE.float›, [e,f]))) =
      if is_float T then
        SOME (Word_Lib.dest_binT e, Word_Lib.dest_binT f)
      else
        NONE
  | float_Targs _ = NONE

fun is_valid_type (T as (Type (\<^type_name>‹IEEE.float›, _))) = is_float T
  | is_valid_type _ = true


(* SMT-LIB logic *)
fun smtlib_logic ts =
      let
        fun is_float_or_rm (Type (\<^type_name>‹IEEE.roundmode›, _)) = true
          | is_float_or_rm T = is_float T
      in
        if exists (Term.exists_type (Term.exists_subtype is_float_or_rm)) ts then
          SOME "ALL"
        else
          NONE
      end


(* SMT-LIB built-ins *)
local

  fun sort_template s args = "(_ " ^ s ^ " " ^ string_of_int (fst args) ^
                               " " ^ string_of_int (snd args + 1) ^ ")"

  fun float_typ T =
    Option.map (rpair [] o sort_template "FloatingPoint") (float_Targs T)

  fun add_float_fun f (t, s) =
    let
      val (n, _) = Term.dest_Const t
    in
      SMT_Builtin.add_builtin_fun SMTLIB_Interface.smtlibC
        (Term.dest_Const t, f n s)
    end

  fun extract_words trip =
    let
      val ((_, s), c) = apfst Term.dest_comb (Term.dest_comb trip)
      val ((_, e), f) = apfst Term.dest_comb (Term.dest_comb c)
    in
      [s, e, f]
    end

  fun mk_floatS c [s, e, f] = Const c $ s $ e $ f
    | mk_floatS c ts = raise TERM ("bad arguments", Const c :: ts)
  
  fun add_constval _ s _ T ts =
    let
      val newT = @{typ "1 word ⇒ 'e word ⇒ 'f word ⇒ ('e, 'f) IEEE.float"}
    in
      if is_float (Term.body_type T) then
        SOME (s, 3, extract_words (hd ts), mk_floatS ("Abs_float_dummy", newT))
      else
        NONE
    end

  fun add_with_none n s _ T ts =
    let
      val (Us, U) = Term.strip_type T
      val all_valid = forall is_valid_type (U::Us)
    in
      if all_valid then
        SOME (s, length Us, ts, Term.list_comb o pair (Const (n, T)))
      else
        NONE
    end

  fun add_with_Targs n s _ T ts =
    let
      val (Us, U) = Term.strip_type T
      val all_valid = forall is_valid_type (U::Us)
    in
      case (all_valid, float_Targs U) of
        (true, SOME args) => SOME (sort_template s args, length Us, ts,
                               Term.list_comb o pair (Const (n, T)))
      | _ => NONE
    end
  
  fun from_default n T =
    let
      val newT = \<^typ>‹IEEE.roundmode› --> T
    in
      case n of
        \<^const_name>‹plus›            => SOME (Const (\<^const_name>‹IEEE.fadd›, newT))
      | \<^const_name>‹minus›           => SOME (Const (\<^const_name>‹IEEE.fsub›, newT))
      | \<^const_name>‹times›           => SOME (Const (\<^const_name>‹IEEE.fmul›, newT))
      | \<^const_name>‹divide›          => SOME (Const (\<^const_name>‹IEEE.fdiv›, newT))
      | \<^const_name>‹IEEE.float_sqrt› => SOME (Const (\<^const_name>‹IEEE.fsqrt›, newT))
      | \<^const_name>‹IEEE.ROUNDFLOAT› => SOME (Const (\<^const_name>‹IEEE.fintrnd›, newT))
      | _ => NONE
    end

  fun add_with_romo n s _ T ts =
    let
      val mode = @{const IEEE.To_nearest}
      val (Us, U) = Term.strip_type T
      val all_valid = forall is_valid_type (U::Us)
    in
      case (all_valid, from_default n T) of
        (true, SOME c) => SOME (s, length Us + 1, mode::ts, Term.list_comb o pair c)
      | _ => NONE
    end
  
  fun add_frem _ s _ T ts =
    let
      val (Us, U) = Term.strip_type T
      val all_valid = forall is_valid_type (U::Us)
      val newT = (tl Us) ---> U
      val c = Const (\<^const_name>‹IEEE.float_rem›, newT)
    in
      if all_valid then
        SOME (s, length Us - 1, tl ts, Term.list_comb o pair c)
      else
        NONE
    end

in

val setup_builtins =

  (* Floating-point Type *)
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.smtlibC
    (\<^typ>‹('e::len,'f::len) float›, float_typ, K (K NONE)) #>
  
  (* Constant values *)
  add_float_fun add_constval
    (@{const IEEE.Abs_float ('e,'f)}, "SOMETHING") #>
  SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC
    (Const ("Abs_float_dummy",
      @{typ "1 word ⇒ 'e word ⇒ 'f word ⇒ ('e, 'f) IEEE.float"}), "fp") #>

  (* Special values *)
  fold (add_float_fun add_with_Targs) [
    (@{const zero_class.zero (‹('e,'f) float›)}, "+zero"),
    (@{const IEEE.plus_infinity (‹'e::len›,‹'f::len›)}, "+oo"),
    (@{const IEEE.some_nan (‹'e::len›,‹'f::len›)}, "NaN")] #>

  (* Classification *)
  fold (add_float_fun add_with_none) [
    (@{const IEEE.is_zero (‹'e::len›,‹'f::len›)}, "fp.isZero"),
    (@{const IEEE.is_infinity (‹'e::len›,‹'f::len›)}, "fp.isInfinite"),
    (@{const IEEE.is_nan (‹'e::len›,‹'f::len›)}, "fp.isNaN"),
    (@{const IEEE.is_normal (‹'e::len›,‹'f::len›)}, "fp.isNormal"),
    (@{const IEEE.is_denormal (‹'e::len›,‹'f::len›)}, "fp.isSubnormal")] #>

  (* Rounding modes *)
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.smtlibC
    (\<^typ>‹roundmode›, K (SOME ("RoundingMode", [])), K (K NONE)) #>
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (@{const IEEE.To_nearest}, "RNE"),
    (@{const IEEE.To_pinfinity}, "RTP"),
    (@{const IEEE.To_ninfinity}, "RTN"),
    (@{const IEEE.float_To_zero}, "RTZ"),
    (@{const IEEE.To_nearest_away}, "RNA")] #>

  (* Arithmetic operations *)
  fold (add_float_fun add_with_none) [
    (@{const abs (‹('e,'f) float›)},"fp.abs"),
    (@{const uminus (‹('e,'f) float›)},"fp.neg"),
    (@{const IEEE.fadd (‹'e::len›,‹'f::len›)}, "fp.add"),
    (@{const IEEE.fsub (‹'e::len›,‹'f::len›)}, "fp.sub"),
    (@{const IEEE.fmul (‹'e::len›,‹'f::len›)}, "fp.mul"),
    (@{const IEEE.fdiv (‹'e::len›,‹'f::len›)}, "fp.div"),
    (@{const IEEE.fmul_add (‹'e::len›,‹'f::len›)}, "fp.fma"),
    (@{const IEEE.fsqrt (‹'e::len›,‹'f::len›)}, "fp.sqrt"),
    (@{const IEEE.fintrnd (‹'e::len›,‹'f::len›)}, "fp.roundToIntegral")] #>
  fold (add_float_fun add_with_romo) [
    (@{const plus (‹('e,'f) float›)}, "SOMETHING"),
    (@{const minus (‹('e,'f) float›)}, "SOMETHING"),
    (@{const times (‹('e,'f) float›)}, "SOMETHING"),
    (@{const divide (‹('e,'f) float›)}, "SOMETHING"),
    (@{const IEEE.float_sqrt (‹'e::len›,‹'f::len›)}, "SOMETHING"),
    (@{const IEEE.ROUNDFLOAT (‹'e::len›,‹'f::len›)}, "SOMETHING")] #>
  add_float_fun add_frem
    (@{const IEEE.frem (‹'e::len›,‹'f::len›)}, "SOMETHING") #>
  add_float_fun add_with_none
    (@{const IEEE.float_rem (‹'e::len›,‹'f::len›)}, "fp.rem") #>

  (* Comparison operations *)
  fold (add_float_fun add_with_none) [
    (@{const less (‹('e,'f) float›)},"fp.lt"),
    (@{const less_eq (‹('e,'f) float›)},"fp.leq"),
    (@{const IEEE.flt (‹'e::len›,‹'f::len›)}, "fp.lt"),
    (@{const IEEE.fle (‹'e::len›,‹'f::len›)}, "fp.leq"),
    (@{const IEEE.fgt (‹'e::len›,‹'f::len›)}, "fp.gt"),
    (@{const IEEE.fge (‹'e::len›,‹'f::len›)}, "fp.geq"),
    (@{const IEEE.feq (‹'e::len›,‹'f::len›)}, "fp.eq"),
    (@{const IEEE.float_eq (‹'e::len›,‹'f::len›)}, "fp.eq")] #>

  (* Type conversion *)
  add_float_fun add_with_none
    (@{const IEEE.valof (‹'e::len›,‹'f::len›)}, "fp.to_real") #>
  add_float_fun add_with_Targs
    (@{const IEEE.round (‹'e::len›,‹'f::len›)}, "to_fp")

end


(* setup *)
val _ = Theory.setup (Context.theory_map (
  SMTLIB_Interface.add_logic (0, smtlib_logic) #>
  setup_builtins))

end;
