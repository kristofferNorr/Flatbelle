(*  Title:      
    Author:     

SMT-LIB-3-style proofs: parsing and abstract syntax tree.
*)

signature FLATBELLE_SMTLIB_PROOF =
sig
  (*type and term parsers*)
  type type_parser = Flatbelle_SMTLIB.tree * typ list -> typ option
  type term_parser = Flatbelle_SMTLIB.tree * term list -> term option
  val add_type_parser: type_parser -> Context.generic -> Context.generic
  val add_term_parser: term_parser -> Context.generic -> Context.generic

end;

structure Flatbelle_SMTLIB_Proof: FLATBELLE_SMTLIB_PROOF =
struct

(* core type and term parser *)
fun core_type_parser (Flatbelle_SMTLIB.Sym "Bool", []) = SOME \<^typ>\<open>HOL.bool\<close>
  | core_type_parser (Flatbelle_SMTLIB.Sym "Int", []) = SOME \<^typ>\<open>Int.int\<close>
  | core_type_parser _ = NONE

fun mk_unary n t =
  let val T = fastype_of t
  in Const (n, T --> T) $ t end

fun mk_binary' n T U t1 t2 = Const (n, [T, T] ---> U) $ t1 $ t2

fun mk_binary n t1 t2 =
  let val T = fastype_of t1
  in mk_binary' n T T t1 t2 end

fun mk_rassoc f t ts =
  let val us = rev (t :: ts)
  in fold f (tl us) (hd us) end

fun mk_lassoc f t ts = fold (fn u1 => fn u2 => f u2 u1) ts t

fun mk_lassoc' n = mk_lassoc (mk_binary n)

fun mk_binary_pred n S t1 t2 =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
    val T =
      if T1 <> Term.dummyT then T1
      else if T2 <> Term.dummyT then T2
      else TVar (("?a", serial ()), S)
  in mk_binary' n T \<^typ>\<open>HOL.bool\<close> t1 t2 end

fun mk_less t1 t2 = mk_binary_pred \<^const_name>\<open>ord_class.less\<close> \<^sort>\<open>linorder\<close> t1 t2
fun mk_less_eq t1 t2 = mk_binary_pred \<^const_name>\<open>ord_class.less_eq\<close> \<^sort>\<open>linorder\<close> t1 t2

fun core_term_parser (Flatbelle_SMTLIB.Sym "true", _) = SOME \<^Const>\<open>True\<close>
  | core_term_parser (Flatbelle_SMTLIB.Sym "false", _) = SOME \<^Const>\<open>False\<close>
  | core_term_parser (Flatbelle_SMTLIB.Sym "not", [t]) = SOME (HOLogic.mk_not t)
  | core_term_parser (Flatbelle_SMTLIB.Sym "and", t :: ts) = SOME (mk_rassoc (curry HOLogic.mk_conj) t ts)
  | core_term_parser (Flatbelle_SMTLIB.Sym "or", t :: ts) = SOME (mk_rassoc (curry HOLogic.mk_disj) t ts)
  | core_term_parser (Flatbelle_SMTLIB.Sym "=>", [t1, t2]) = SOME (HOLogic.mk_imp (t1, t2))
  | core_term_parser (Flatbelle_SMTLIB.Sym "implies", [t1, t2]) = SOME (HOLogic.mk_imp (t1, t2))
  | core_term_parser (Flatbelle_SMTLIB.Sym "=", [t1, t2]) = SOME (HOLogic.mk_eq (t1, t2))
  | core_term_parser (Flatbelle_SMTLIB.Sym "~", [t1, t2]) = SOME (HOLogic.mk_eq (t1, t2))
  | core_term_parser (Flatbelle_SMTLIB.Sym "ite", [t1, t2, t3]) =
      let
        val T = fastype_of t2
        val c = Const (\<^const_name>\<open>HOL.If\<close>, [\<^typ>\<open>HOL.bool\<close>, T, T] ---> T)
      in SOME (c $ t1 $ t2 $ t3) end
  | core_term_parser (Flatbelle_SMTLIB.Num i, []) = SOME (HOLogic.mk_number \<^typ>\<open>Int.int\<close> i)
  | core_term_parser (Flatbelle_SMTLIB.Sym "-", [t]) = SOME (mk_unary \<^const_name>\<open>uminus_class.uminus\<close> t)
  | core_term_parser (Flatbelle_SMTLIB.Sym "~", [t]) = SOME (mk_unary \<^const_name>\<open>uminus_class.uminus\<close> t)
  | core_term_parser (Flatbelle_SMTLIB.Sym "+", t :: ts) =
      SOME (mk_lassoc' \<^const_name>\<open>plus_class.plus\<close> t ts)
  | core_term_parser (Flatbelle_SMTLIB.Sym "-", t :: ts) =
      SOME (mk_lassoc' \<^const_name>\<open>minus_class.minus\<close> t ts)
  | core_term_parser (Flatbelle_SMTLIB.Sym "*", t :: ts) =
      SOME (mk_lassoc' \<^const_name>\<open>times_class.times\<close> t ts)
  (*| core_term_parser (Flatbelle_SMTLIB.Sym "div", [t1, t2]) = SOME (mk_binary \<^const_name>\<open>z3div\<close> t1 t2)
  | core_term_parser (Flatbelle_SMTLIB.Sym "mod", [t1, t2]) = SOME (mk_binary \<^const_name>\<open>z3mod\<close> t1 t2) *)
  | core_term_parser (Flatbelle_SMTLIB.Sym "<", [t1, t2]) = SOME (mk_less t1 t2)
  | core_term_parser (Flatbelle_SMTLIB.Sym ">", [t1, t2]) = SOME (mk_less t2 t1)
  | core_term_parser (Flatbelle_SMTLIB.Sym "<=", [t1, t2]) = SOME (mk_less_eq t1 t2)
  | core_term_parser (Flatbelle_SMTLIB.Sym ">=", [t1, t2]) = SOME (mk_less_eq t2 t1)

(* custom type and term parsers *)
type type_parser = Flatbelle_SMTLIB.tree * typ list -> typ option
type term_parser = Flatbelle_SMTLIB.tree * term list -> term option

fun id_ord ((id1, _), (id2, _)) = int_ord (id1, id2)

structure Parsers = Generic_Data
(
  type T = (int * type_parser) list * (int * term_parser) list
  val empty: T = ([(serial (), core_type_parser)], [(serial (), core_term_parser)])
  fun merge ((tys1, ts1), (tys2, ts2)) =
    (Ord_List.merge id_ord (tys1, tys2), Ord_List.merge id_ord (ts1, ts2))
)

fun add_type_parser type_parser = 
  Parsers.map (apfst (Ord_List.insert id_ord (serial (), type_parser)))

fun add_term_parser term_parser = 
  Parsers.map (apsnd (Ord_List.insert id_ord (serial (), term_parser)))


end