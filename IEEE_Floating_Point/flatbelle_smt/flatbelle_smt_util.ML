(*  Title:      
    Author:     Kristoffer Norrman

General utility functions. More or less a copy of SMT_Util in HOL/Tools/SMT/smt_util.ML.
*)

signature FLATBELLE_SMT_UTIL =
sig
  (*basic combinators*)
  val repeat: ('a -> 'a option) -> 'a -> 'a
  val repeat_yield: ('a -> 'b -> ('a * 'b) option) -> 'a -> 'b -> 'a * 'b
  val map_prod: ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> ('b * 'd)

  datatype order = First_Order | Higher_Order
  datatype role = Conjecture | Hypothesis | Axiom

  (*class dictionaries*)
  type class = string list
  val basicC: class
  val string_of_class: class -> string
  type 'a dict = (class * 'a) Ord_List.T
  val dict_map_default: class * 'a -> ('a -> 'a) -> 'a dict -> 'a dict
  val dict_update: class * 'a -> 'a dict -> 'a dict
  val dict_merge: ('a * 'a -> 'a) -> 'a dict * 'a dict -> 'a dict
  val dict_lookup: 'a dict -> class -> 'a list
  val dict_get: 'a dict -> class -> 'a option

  (*types*)
  val dest_funT: int -> typ -> typ list * typ

  (*terms*)
  val dest_conj: term -> term * term
  val dest_disj: term -> term * term
  val under_quant: (term -> 'a) -> term -> 'a
  val is_number: term -> bool

  (*symbolic lists*)

  (*patterns and instantiations*)

  (*certified terms*)
  val prop_of: thm -> term
  
  (*conversions*)

end;

structure Flatbelle_SMT_Util: FLATBELLE_SMT_UTIL =
struct
(* TODO error*)
fun ftodo func = error "Flatbelle_SMT_Util - TODO: " ^ func


(* basic combinators *)

fun repeat f =
  let fun rep x = (case f x of SOME y => rep y | NONE => x)
  in rep end

fun repeat_yield f =
  let fun rep x y = (case f x y of SOME (x', y') => rep x' y' | NONE => (x, y))
  in rep end

val map_prod = Ctr_Sugar_Util.map_prod


(* order *)

datatype order = First_Order | Higher_Order


(* role *)

datatype role = Conjecture | Hypothesis | Axiom


(* class dictionaries *)

type class = string list

val basicC = []

fun string_of_class [] = "basic"
  | string_of_class cs = "basic." ^ space_implode "." cs

type 'a dict = (class * 'a) Ord_List.T

fun class_ord ((cs1, _), (cs2, _)) =
  rev_order (list_ord fast_string_ord (cs1, cs2))

fun dict_insert (cs, x) d =
  if AList.defined (op =) d cs then d
  else Ord_List.insert class_ord (cs, x) d

fun dict_map_default (cs, x) f =
  dict_insert (cs, x) #> AList.map_entry (op =) cs f

fun dict_update (e as (_, x)) = dict_map_default e (K x)

fun dict_merge val_merge = sort class_ord o AList.join (op =) (K val_merge)

fun dict_lookup d cs =
  let fun match (cs', x) = if is_prefix (op =) cs' cs then SOME x else NONE
  in map_filter match d end

fun dict_get d cs =
  (case AList.lookup (op =) d cs of
    NONE => (case cs of [] => NONE | _ => dict_get d (take (length cs - 1) cs))
  | SOME x => SOME x)


(* types *)

val dest_funT =
  let
    fun dest Ts 0 T = (rev Ts, T)
      | dest Ts i (Type ("fun", [T, U])) = dest (T::Ts) (i-1) U
      | dest _ _ T = raise TYPE ("not a function type", [T], [])
  in dest [] end


(* terms *)

fun dest_conj \<^Const_>\<open>conj for t u\<close> = (t, u)
  | dest_conj t = raise TERM ("not a conjunction", [t])

fun dest_disj \<^Const_>\<open>disj for t u\<close> = (t, u)
  | dest_disj t = raise TERM ("not a disjunction", [t])

fun under_quant f t =
  (case t of
    \<^Const_>\<open>All _ for \<open>Abs (_, _, u)\<close>\<close> => under_quant f u
  | \<^Const_>\<open>Ex _ for \<open>Abs (_, _, u)\<close>\<close> => under_quant f u
  | _ => f t)

val is_number =
  let
    fun is_num env (Const (\<^const_name>\<open>Let\<close>, _) $ t $ Abs (_, _, u)) = is_num (t :: env) u
      | is_num env (Bound i) = i < length env andalso is_num env (nth env i)
      | is_num _ t = can HOLogic.dest_number t
  in is_num [] end

(*symbolic lists*)

(*patterns and instantiations*)

(*certified terms*)

fun dest_cabs ct ctxt = ftodo "dest_cabs"

fun dest_all_cabs () = ftodo "dest_all_cabs"

fun dest_cbinder ct ctxt = ftodo "dest_cbinder"

fun dest_all_cbinders () = ftodo "dest_all_cbinders"

fun equals () = ftodo "equals"
fun mk_cequals ct cu = ftodo "mk_cequals"

val dest_prop = fn \<^Const>\<open>Trueprop for t\<close> => t | t => t
fun term_of ct = dest_prop (Thm.term_of ct)
fun prop_of thm = dest_prop (Thm.prop_of thm)



end;