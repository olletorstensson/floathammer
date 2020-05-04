structure SMT_Float: sig end =
struct

(* Helpers *)
fun is_float (Type (\<^type_name>‹IEEE.float›, [e,f])) =
      can (apply2 Word_Lib.dest_binT) (e,f) andalso
      Word_Lib.dest_binT e > 1 andalso Word_Lib.dest_binT f > 0
  | is_float _ = false

fun float_Targs (Type (\<^type_name>‹IEEE.float›, [e,f])) =
      if can (apply2 Word_Lib.dest_binT) (e,f) andalso
      Word_Lib.dest_binT e > 1 andalso Word_Lib.dest_binT f > 0 then
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


(* SMT-LIB and Z3 built-ins *)

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
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.smtlibC
    (\<^typ>‹('e::len,'f::len) float›, float_typ, K (K NONE)) #>

  SMT_Builtin.add_builtin_fun SMTLIB_Interface.smtlibC
    (Term.dest_Const @{const Abs_float ('e,'f)}, const_val) #>
  SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC
    (Const ("Abs_float",
      @{typ "1 word ⇒ 'e word ⇒ 'f word ⇒ ('e, 'f) IEEE.float"}), "fp")

(*Interpret operation only if type arguments are fixed*)
(*
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (@{const less (real)}, "<"),
    (@{const less_eq (real)}, "<="),
    (@{const uminus (real)}, "-"),
    (@{const plus (real)}, "+"),
    (@{const minus (real)}, "-") ] #>

  SMT_Builtin.add_builtin_fun SMTLIB_Interface.smtlibC
    (Term.dest_Const @{const times (real)}, times) #>
  SMT_Builtin.add_builtin_fun' Z3_Interface.smtlib_z3C
    (@{const times (real)}, "*") #>
  SMT_Builtin.add_builtin_fun' Z3_Interface.smtlib_z3C
    (@{const divide (real)}, "/")
*)

end


(* setup *)

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Interface.add_logic (11, smtlib_logic) #>
  setup_builtins))

end;
