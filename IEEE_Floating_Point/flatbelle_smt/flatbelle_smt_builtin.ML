(*  Title:      
    Author:     Kristoffer Norrman


*)

signature FLATBELLE_SMT_BUILTIN =
sig

  (*typs and terms*)
  datatype typ_term = Typ of typ | Term of term 
  
  (*built-in types*)
  val add_builtin_typ: Flatbelle_SMT_Util.class -> 
    typ * (typ -> (string * typ_term list) option) * (typ -> int -> string option) -> 
    Context.generic -> Context.generic
  val add_builtin_typ_ext: typ * (Proof.context -> typ -> bool) -> Context.generic ->
    Context.generic
  val dest_builtin_typ: Proof.context -> typ -> (string * typ_term list) option
  val is_builtin_typ_ext: Proof.context -> typ -> bool

  (*built-in numbers*)
  val dest_builtin_num: Proof.context -> term -> (string * typ) option
  val is_builtin_num: Proof.context -> term -> bool
  val is_builtin_num_ext: Proof.context -> term -> bool

  (*built-in functions*)
  type 'a bfun = Proof.context -> typ -> term list -> 'a
  type bfunr = string * int * term list * (term list -> term)
  val add_builtin_fun: Flatbelle_SMT_Util.class -> (string * typ) * bfunr option bfun -> 
    Context.generic -> Context.generic
  val add_builtin_fun': Flatbelle_SMT_Util.class -> term * string -> Context.generic -> Context.generic
  val add_builtin_fun_ext: (string * typ) * term list bfun -> Context.generic -> Context.generic
  val add_builtin_fun_ext': string * typ -> Context.generic -> Context.generic
  val add_builtin_fun_ext'': string -> Context.generic -> Context.generic    
  val dest_builtin_fun: Proof.context -> string * typ -> term list -> bfunr option
  val dest_builtin_eq: Proof.context -> term -> term -> bfunr option
  val dest_builtin_pred: Proof.context -> string * typ -> term list -> bfunr option
  val dest_builtin_conn: Proof.context -> string * typ -> term list -> bfunr option
  val dest_builtin: Proof.context -> string * typ -> term list -> bfunr option
  val dest_builtin_ext: Proof.context -> string * typ -> term list -> term list option
  val is_builtin_fun: Proof.context -> string * typ -> term list -> bool
  val is_builtin_fun_ext: Proof.context -> string * typ -> term list -> bool

end;

structure Flatbelle_SMT_Builtin: FLATBELLE_SMT_BUILTIN =
struct

(*typs and terms*)

datatype typ_term = Typ of typ | Term of term

(* built-in tables *)

datatype ('a, 'b) kind = Ext of 'a | Int of 'b

type ('a, 'b) ttab = ((typ * ('a, 'b) kind) Ord_List.T) Flatbelle_SMT_Util.dict

fun typ_ord ((T, _), (U, _)) =
  let
    fun tord (TVar _, Type _) = GREATER
      | tord (Type _, TVar _) = LESS
      | tord (Type (n, Ts), Type (m, Us)) =
          if n = m then list_ord tord (Ts, Us)
          else Term_Ord.typ_ord (T, U)
      | tord TU = Term_Ord.typ_ord TU
  in tord (T, U) end

fun insert_ttab cs T f =
  Flatbelle_SMT_Util.dict_map_default (cs, [])
    (Ord_List.insert typ_ord (perhaps (try Logic.varifyT_global) T, f))

fun merge_ttab ttabp = Flatbelle_SMT_Util.dict_merge (Ord_List.merge typ_ord) ttabp

fun lookup_ttab ctxt ttab T = 
  let fun match (U, _) = Sign.typ_instance (Proof_Context.theory_of ctxt) (T, U)
  in
    get_first (find_first match) 
      (Flatbelle_SMT_Util.dict_lookup ttab (Flatbelle_SMT_Config.solver_class_of ctxt))
  end

(*[A table where keys are Const-names and values ttabs]*)
type ('a, 'b) btab = ('a, 'b) ttab Symtab.table

fun insert_btab cs n T f = 
  Symtab.map_default (n, []) (insert_ttab cs T f)

fun merge_btab btabp = Symtab.join (K merge_ttab) btabp

fun lookup_btab ctxt btab (n, T) =
  (case Symtab.lookup btab n of
    NONE => NONE
  | SOME ttab => lookup_ttab ctxt ttab T)

type 'a bfun = Proof.context -> typ -> term list -> 'a

type bfunr = string * int * term list * (term list -> term)

structure Builtins = Generic_Data
(
  (*[T is a pair, one handling types (ttab), and one consts (btab).]*)
  type T = 
    (Proof.context -> typ -> bool, (*[This is ext part of ttab]*)
      (typ -> (string * typ_term list) option) * (typ -> int -> string option)) ttab * (*[This is int part of ttab]*)  
      (term list bfun, bfunr option bfun) btab (*[This is btab]*)
  val empty = ([], Symtab.empty)
  fun merge ((t1, b1), (t2, b2)) = (merge_ttab (t1, t2), merge_btab (b1, b2))
)

(*FIXME: Add filter stuff if needed.*)



(*built-in types*)

fun add_builtin_typ cs (T, f, g) = 
  Builtins.map (apfst (insert_ttab cs T (Int (f, g))))

fun add_builtin_typ_ext (T, f) = error "TODO: add_builtin_typ_ext" \<comment> \<open>Is not used here as IEEE is defined in Isabelle.\<close>

fun lookup_builtin_typ ctxt =
  lookup_ttab ctxt (fst (Builtins.get (Context.Proof ctxt)))

fun dest_builtin_typ ctxt T =
  (case lookup_builtin_typ ctxt T of
    SOME (_, Int (f, _)) => f T
  | _ => NONE)

fun is_builtin_typ_ext ctxt T = 
  (case lookup_builtin_typ ctxt T of
    SOME (_, Int (f, _)) => is_some (f T)
  | SOME (_, Ext f) => f ctxt T
  | NONE => false)

(* built-in numbers *)

fun dest_builtin_num ctxt t = 
  (case try HOLogic.dest_number t of
    NONE => NONE
  | SOME (T, i) =>
      if i < 0 then NONE else
        (case lookup_builtin_typ ctxt T of
          SOME (_, Int (_, g)) => g T i |> Option.map (rpair T)
        | _ => NONE))

fun is_builtin_num _ = error "TODO: is_builtin_num"

fun is_builtin_num_ext ctxt t = error "TODO: is_builtin_num_ext"

(*built-in functions*)

fun add_builtin_fun cs ((n, T), f) = 
  Builtins.map (apsnd (insert_btab cs n T (Int f)))

fun add_builtin_fun' cs (t, n) =
  let
    val c as (m,T) = Term.dest_Const t
    fun app U ts = Term.list_comb (Const (m, U), ts)
    fun bfun _ U ts = SOME (n, length (Term.binder_types T), ts, app U)
  in add_builtin_fun cs (c, bfun)  end

fun add_builtin_fun_ext ((n, T), f) = 
  Builtins.map (apsnd (insert_btab Flatbelle_SMT_Util.basicC n T (Ext f)))

fun add_builtin_fun_ext' c = error "TODO: add_builtin_fun_ext'"

fun add_builtin_fun_ext'' n context = error "TODO: add_builtin_fun_ext'"

fun lookup_builtin_fun ctxt =
  lookup_btab ctxt (snd (Builtins.get (Context.Proof ctxt)))

fun dest_builtin_fun ctxt (c as (_, T)) ts =
  (case lookup_builtin_fun ctxt c of
    SOME (_, Int f) => f ctxt T ts
  | _ => NONE)

fun dest_builtin_eq ctxt t u =
  let
    val aT = Term.aT \<^sort>\<open>type\<close>
    val c = (\<^const_name>\<open>HOL.eq\<close>, aT --> aT --> \<^typ>\<open>bool\<close>)
    fun mk ts = Term.list_comb (HOLogic.eq_const (Term.fastype_of (hd ts)), ts)
  in
    dest_builtin_fun ctxt c []
    |> Option.map (fn (n, i, _, _) => (n, i, [t, u], mk))
  end

(*[Used for destructing predicates and connectives.]*)
fun special_builtin_fun pred ctxt (c as (_, T)) ts =
  if pred (Term.body_type T, Term.binder_types T) then
    dest_builtin_fun ctxt c ts
  else NONE

(*[Destructing predicates]*)
fun dest_builtin_pred ctxt = 
  special_builtin_fun (equal \<^typ>\<open>bool\<close> o fst) ctxt

(*[Destructing connectives]*)
fun dest_builtin_conn ctxt =
  special_builtin_fun (forall (equal \<^typ>\<open>bool\<close>) o (op ::)) ctxt

fun dest_builtin ctxt c ts =  
  let val t = Term.list_comb (Const c, ts)
  in 
    (case dest_builtin_num ctxt t of
      SOME (n, _) => SOME (n, 0, [], K t)
    | NONE => dest_builtin_fun ctxt c ts)
  end

fun dest_builtin_fun_ext ctxt (c as (_, T)) ts = error "TODO: dest_builtin_fun_ext"

fun dest_builtin_ext ctxt c ts = error "TODO: dest_builtin_ext"

fun is_builtin_fun ctxt c ts = is_some (dest_builtin_fun ctxt c ts)

fun is_builtin_fun_ext ctxt c ts = error "TODO: is_builtin_fun_ext"

end;