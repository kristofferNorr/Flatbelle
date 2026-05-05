signature FLATBELLE_SMTLIB_INTERFACE =
sig
  val smtlibC: Flatbelle_SMT_Util.class
  val hosmtlibC: Flatbelle_SMT_Util.class
  val add_lOGic: int * (string -> term list -> string option) -> Context.generic -> Context.generic
  val del_lOGic: int * (string -> term list -> string option) -> Context.generic -> Context.generic
  
  type dtype_decls = (string * (string * (string * string) list) list) list
  type func_decl = string * (string list * string)
  val serialize: (BNF_Util.fp_kind * dtype_decls -> Buffer.T -> Buffer.T) -> (string * string) list -> string list ->
    {dtyps: (BNF_Util.fp_kind * (string * (string * (string * string) list) list)) list,
     funcs: func_decl list, lOGic: string, sorts: string list, typvars: string list} ->
    (Flatbelle_SMT_Util.role * Flatbelle_SMT_Translate.sterm) list -> string

  val translate_config: Flatbelle_SMT_Util.order -> Proof.context -> Flatbelle_SMT_Translate.config
  val role_and_index_of_assert_name: string -> Flatbelle_SMT_Util.role * int
end;

structure Flatbelle_SMTLIB_Interface: FLATBELLE_SMTLIB_INTERFACE =
struct

val hoC = ["ho"]

val smtlibC = ["smtlib"]   (* SMT-LIB 2 *)
val hosmtlibC = smtlibC @ hoC   (* possibly SMT-LIB 3 *)


(* builtins *)

local
  fun int_num _ i = SOME (string_of_int i)

  fun is_linear [t] = Flatbelle_SMT_Util.is_number t
    | is_linear [t, u] = Flatbelle_SMT_Util.is_number t orelse Flatbelle_SMT_Util.is_number u
    | is_linear _ = false

  fun times _ _ ts =
    let val mk = Term.list_comb o pair \<^Const>\<open>times \<^Type>\<open>int\<close>\<close>
    in if is_linear ts then SOME ("*", 2, ts, mk) else NONE end

in

val setup_builtins =
  fold (Flatbelle_SMT_Builtin.add_builtin_typ smtlibC) [
    (\<^typ>\<open>bool\<close>, K (SOME ("Bool", [])), K (K NONE)),
    (\<^typ>\<open>int\<close>, K (SOME ("Int", [])), int_num)] #>
  fold (Flatbelle_SMT_Builtin.add_builtin_fun' smtlibC) [
    (\<^Const>\<open>True\<close>, "true"),
    (\<^Const>\<open>False\<close>, "false"),
    (\<^Const>\<open>Not\<close>, "not"),
    (\<^Const>\<open>conj\<close>, "and"),
    (\<^Const>\<open>disj\<close>, "or"),
    (\<^Const>\<open>implies\<close>, "=>"),
    (*(\<^Const>\<open>HOL.eq \<^typ>\<open>'a\<close>\<close>, "="),  Remove this to see how to (maybe) handle poly*)
    (\<^Const>\<open>If \<^typ>\<open>'a\<close>\<close>, "ite"),
    (\<^Const>\<open>less \<^Type>\<open>int\<close>\<close>, "<"),
    (\<^Const>\<open>less_eq \<^Type>\<open>int\<close>\<close>, "<="),
    (\<^Const>\<open>uminus \<^Type>\<open>int\<close>\<close>, "-"),
    (\<^Const>\<open>plus \<^Type>\<open>int\<close>\<close>, "+"),
    (\<^Const>\<open>minus \<^Type>\<open>int\<close>\<close>, "-")] #>
  Flatbelle_SMT_Builtin.add_builtin_fun smtlibC
    (Term.dest_Const \<^Const>\<open>times \<^Type>\<open>int\<close>\<close>, times) 

end

(* serialization *)

(** lOGic **)

fun fst_int_ord ((i1, _), (i2, _)) = int_ord (i1, i2)

structure LOGics = Generic_Data
(
  type T = (int * (string -> term list -> string option)) list
  val empty = []
  fun merge data = Ord_List.merge fst_int_ord data
)

fun add_lOGic pf = LOGics.map (Ord_List.insert fst_int_ord pf)
fun del_lOGic pf = LOGics.map (Ord_List.remove fst_int_ord pf)

fun choose_lOGic ctxt prover ts =
  let
    fun choose lg [] = "Ints"
      | choose lg ((_, f) :: fs) = (case f prover ts of SOME s => lg ^ s ^ ", " ^ (choose lg fs) | NONE => choose lg fs)
  in
    (case choose "" (LOGics.get (Context.Proof ctxt)) of
      "" => "" (* for default Z3 lOGic, a subset of everything *)
    | lOGic => "(import (" ^ lOGic ^ "))\n" ^ "(open (" ^ lOGic ^ "))\n")
  end

(** serialization **)
type func_decl = string * (string list * string)

fun var i = "?v" ^ string_of_int i

fun tree_of_sterm l (Flatbelle_SMT_Translate.SVar (i, [])) = Flatbelle_SMTLIB.Sym (var (l - i - 1))
  | tree_of_sterm l (Flatbelle_SMT_Translate.SVar (i, ts)) =
      Flatbelle_SMTLIB.S (Flatbelle_SMTLIB.Sym (var (l - i - 1)) :: map (tree_of_sterm l) ts)
  | tree_of_sterm _ (Flatbelle_SMT_Translate.SConst (n, [])) = Flatbelle_SMTLIB.Sym n
  | tree_of_sterm l (Flatbelle_SMT_Translate.SConst (n, ts)) =
      Flatbelle_SMTLIB.S (Flatbelle_SMTLIB.Sym n :: map (tree_of_sterm l) ts)
  | tree_of_sterm l (Flatbelle_SMT_Translate.SQua (q, ss, pats, t)) =
      let
        val l' = l + length ss

        fun quant_name Flatbelle_SMT_Translate.SForall = "forall"
          | quant_name Flatbelle_SMT_Translate.SExists = "exists"

        fun gen_trees_of_pat keyword ps =
          [Flatbelle_SMTLIB.Key keyword, Flatbelle_SMTLIB.S (map (tree_of_sterm l') ps)]
        fun trees_of_pat (Flatbelle_SMT_Translate.SPat ps) = gen_trees_of_pat "pattern" ps
          | trees_of_pat (Flatbelle_SMT_Translate.SNoPat ps) = gen_trees_of_pat "no-pattern" ps
        fun tree_of_pats [] t = t
          | tree_of_pats pats t = Flatbelle_SMTLIB.S (Flatbelle_SMTLIB.Sym "!" :: t :: maps trees_of_pat pats)

        val vs = map_index (fn (i, ty) =>
          Flatbelle_SMTLIB.S [Flatbelle_SMTLIB.Sym (var (l + i)), Flatbelle_SMTLIB.Sym ty]) ss

        val body = t
          |> tree_of_sterm l'
          |> tree_of_pats pats
      in
        Flatbelle_SMTLIB.S [Flatbelle_SMTLIB.Sym (quant_name q), Flatbelle_SMTLIB.S vs, body]
      end

fun sctrarg (sel, typ) = "(" ^ sel ^ " " ^ typ ^ ")"
fun sctr (name, args) = enclose "(" ")" (implode_space (name :: map sctrarg args))
fun sdatatype (name, ctrs) = enclose "(" ")" (implode_space (name :: map sctr ctrs))

fun string_of_fun (f, ([], s)) = f ^ " " ^ s
  | string_of_fun (f, (ss, s)) = f ^ " (-> " ^ implode_space ss ^ " " ^ s ^ ")"

fun named_sterm s t = Flatbelle_SMTLIB.S [Flatbelle_SMTLIB.Sym "!", t, Flatbelle_SMTLIB.Key "named", Flatbelle_SMTLIB.Sym s]

val conjecture_prefix = "conjecture" (* FUDGE *)
val hypothesis_prefix = "hypothesis" (* FUDGE *)
val axiom_prefix = "a" (* matching Alethe's convention *)

fun assert_prefix_of_role Flatbelle_SMT_Util.Conjecture = conjecture_prefix
  | assert_prefix_of_role Flatbelle_SMT_Util.Hypothesis = hypothesis_prefix
  | assert_prefix_of_role Flatbelle_SMT_Util.Axiom = axiom_prefix

fun assert_name_of_role_and_index role i = assert_prefix_of_role role ^ string_of_int i

fun unprefix_axiom s =
  try (pair Flatbelle_SMT_Util.Conjecture o unprefix conjecture_prefix) s
  |> curry merge_options (try (pair Flatbelle_SMT_Util.Hypothesis o unprefix hypothesis_prefix) s)
  |> curry merge_options (try (pair Flatbelle_SMT_Util.Axiom o unprefix axiom_prefix) s)
  |> the

fun role_and_index_of_assert_name s =
  apsnd (the_default ~1 o Int.fromString) (unprefix_axiom s)

type dtype_decls = (string * (string * (string * string) list) list) list

fun sdtyp (fp, dtyps : dtype_decls) =
  Buffer.add (enclose ("(declare-" ^ BNF_FP_Util.co_prefix fp ^ "datatypes () (") "))\n"
    (space_implode "\n  " (map sdatatype dtyps)))

type func_decl = string * (string list * string)

fun serialize (sdtyp : BNF_Util.fp_kind * dtype_decls -> Buffer.T -> Buffer.T) smt_options comments
      {lOGic, sorts, dtyps, funcs, typvars} ts =
  let
    val unsat_core = member (op =) smt_options (":produce-unsat-cores", "true")
  in
    Buffer.empty
    |> fold (Buffer.add o enclose "; " "\n") comments
    |> fold (fn (k, v) => Buffer.add ("(set-option " ^ k ^ " " ^ v ^ ")\n")) smt_options
    |> Buffer.add lOGic
    |> fold (Buffer.add o enclose "(declare-type " " ())\n") (sort fast_string_ord sorts)
    |> fold (Buffer.add o enclose "(declare-type-var " ")\n") (sort fast_string_ord typvars)
    |> fold sdtyp (AList.coalesce (op =) dtyps)
    |> fold (Buffer.add o enclose "(declare-const " ")\n" o string_of_fun)
        ( funcs)
    |> fold (fn (i, (role, t)) => Buffer.add (enclose "(assert " ")\n"
        (Flatbelle_SMTLIB.str_of (named_sterm (assert_name_of_role_and_index role i) (tree_of_sterm 0 t)))))
        (map_index I ts)
    |> Buffer.add "(check-sat)\n"
    |> Buffer.add (if unsat_core then "(get-unsat-core)\n" else "(get-proof)\n")
    |> Buffer.content
  end

(* interface *)

fun translate_config order ctxt =  {
    order = order,
    lOGic = choose_lOGic ctxt,
    fp_kinds = [BNF_Util.Least_FP], \<comment> \<open>This is usually first part of an actual solver interface.\<close>
    serialize = serialize sdtyp}
              
val _ = Theory.setup (Context.theory_map
  (setup_builtins #>
   Flatbelle_SMT_Translate.add_config (smtlibC, translate_config Flatbelle_SMT_Util.First_Order) #>
   Flatbelle_SMT_Translate.add_config (hosmtlibC, translate_config Flatbelle_SMT_Util.Higher_Order)))

end;