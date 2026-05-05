(*  Title:      
    Author:     Kristoffer Norrman


*)

signature FLATBELLE_SMT_TRANSLATE =
sig 

  (* intermediate term structure *)
  datatype squant = SForall | SExists
  datatype 'a spattern = 
    SPat of 'a list | SNoPat of 'a list
  datatype sterm = 
    SVar of int * sterm list |
    SConst of string * sterm list |
    SQua of squant * string list * sterm spattern list * sterm
  val eta_expand: Proof.context -> int Termtab.table -> ('a * term) list -> ('a * term) list
  
  (* translation config *)
  
  type sign = {
    lOGic: string,
    sorts: string list,
    dtyps: (BNF_Util.fp_kind * (string * (string * (string * string) list) list)) list, 
    funcs: (string * (string list * string)) list, 
    typvars: string list} 
  
  type config = {
    order: Flatbelle_SMT_Util.order,
    lOGic: string -> term list -> string,
    fp_kinds: BNF_Util.fp_kind list, 
    serialize: (string * string) list -> string list -> sign -> 
      (Flatbelle_SMT_Util.role * sterm) list -> string }
  
  type replay_data = {}
  (*translation*)
  val add_config: Flatbelle_SMT_Util.class * (Proof.context -> config) -> Context.generic -> Context.generic
  val translate: Proof.context -> string -> (string * string) list -> string list ->
    ((int * Flatbelle_SMT_Util.role) * thm) list ->
    string  
end;

structure Flatbelle_SMT_Translate : FLATBELLE_SMT_TRANSLATE =
struct

(* TODO exception*)
  exception TODO of string  

(* intermediate term structure *)

datatype squant = SForall | SExists

datatype 'a spattern = 
  SPat of 'a list | SNoPat of 'a list

datatype sterm = 
  SVar of int * sterm list |
  SConst of string * sterm list |
  SQua of squant * string list * sterm spattern list * sterm

(* translation config *)

type sign = {
  lOGic: string,
  sorts: string list,
  dtyps: (BNF_Util.fp_kind * (string * (string * (string * string) list) list)) list,
  funcs: (string * (string list * string)) list,
  typvars: string list} 

type config = {
  order: Flatbelle_SMT_Util.order,
  lOGic: string -> term list -> string,
  fp_kinds: BNF_Util.fp_kind list, 
  serialize: (string * string) list -> string list -> sign -> 
    (Flatbelle_SMT_Util.role * sterm) list -> string }

type replay_data = {}

(* translation context *)

fun add_components_of_typ (Type ( s, Ts)) = 
    cons (Long_Name.base_name s) #> fold_rev add_components_of_typ Ts
  | add_components_of_typ (TFree (s, _)) = cons (perhaps (try (unprefix "'")) s)
  | add_components_of_typ _ = I;


fun suggested_name_of_typ T = space_implode "_" (add_components_of_typ T []);

fun suggested_name_of_term (Const (s, _)) = Long_Name.base_name s
  | suggested_name_of_term (Free (s, _)) = s
  | suggested_name_of_term _ = Name.uu

(* A table for type args to be decalred as (declare-type-var _ )*)
structure TypVartab = Table(type key = typ val ord = Term_Ord.typ_ord);

val empty_tr_context = (Name.context, Typtab.empty, Termtab.empty, TypVartab.empty)
val safe_suffix = "$"

fun add_typ T proper (cx as (names, typs, terms, typvars)) =
  (case Typtab.lookup typs T of
    SOME (name, _) => (name, cx)
  | NONE =>
      let 
        val sugg = Name.desymbolize (SOME true) (suggested_name_of_typ T) ^ safe_suffix
        val (name, names') = Name.variant sugg names
        val typs' = Typtab.update (T, (name, proper)) typs
      in (name, (names', typs', terms, typvars)) end)

fun add_fun t sort (cx as (names, typs, terms, typvars)) = 
  (case Termtab.lookup terms t of
    SOME (name, _) => (name, cx)
  | NONE => 
      let
        val sugg = Name.desymbolize (SOME false) (suggested_name_of_term t) ^ safe_suffix
        val (name, names') = Name.variant sugg names
        val terms' = Termtab.update (t, (name, sort)) terms
      in (name, (names', typs, terms', typvars)) end)

fun add_typ_var T proper (cx as (names, typs, terms, typvars)) =
  (case TypVartab.lookup typvars T of
    SOME (name, _) => (name, cx)
  | NONE =>
      let 
        val sugg = Name.desymbolize (SOME true) (suggested_name_of_typ T) ^ safe_suffix
        val (name, names') = Name.variant sugg names
        val typvars' = TypVartab.update (T, (name, proper)) typvars
      in (name, (names', typs, terms, typvars')) end)
  | add_typ_var T _ _ = raise TYPE ("not a TVar", [T], [])


fun sign_of lOGic dtyps (_, typs, terms, typvars) = {
  lOGic = lOGic,
  sorts = Typtab.fold (fn (_, (n, true)) => cons n | _ => I) typs [],
  dtyps = dtyps,
  funcs = Termtab.fold (fn (_, (n, SOME ss)) => cons (n,ss) | _ => I) terms [],
  typvars = TypVartab.fold (fn (_, (n, true)) => cons n | _ => I) typvars []}

fun replay_data_of ctxt ll_defs rules assms (_, typs, terms) = error "TODO: fun replay_data_of"

(* preprocessing *)

(** (co)datatype declarations **)

fun collect_co_datatypes fp_kinds (tr_context, ctxt) ts = 
  let
    val (fp_decls, ctxt') = 
      ([], ctxt)
      |> fold (Term.fold_types (Flatbelle_SMT_Datatypes.add_decls fp_kinds) o snd) ts
      |>> flat
      
    fun is_decl_typ T = exists (equal T o fst o snd) fp_decls
     
    fun add_typ' T proper =   
      (case Flatbelle_SMT_Builtin.dest_builtin_typ ctxt' T of
        SOME (n, Ts) => pair n (*FIXME: OG file had a comment about Ts for HO.*)
      | NONE => add_typ T proper)

    fun tr_select sel =
      let val T = Term.range_type (Term.fastype_of sel)
      in add_fun sel NONE ##>> add_typ' T (not (is_decl_typ T)) end
    fun tr_constr (constr, selects) = 
      add_fun constr NONE ##>> fold_map tr_select selects
    fun tr_typ (fp, (T, cases)) = 
      add_typ' T false ##>> fold_map tr_constr cases #>> pair fp
    
    val (fp_decls', tr_context') = fold_map tr_typ fp_decls tr_context
    fun add (constr, selects) = 
      Termtab.update (constr, length selects) #> 
      fold (Termtab.update o rpair 1) selects
    val funcs = fold (fold add o snd o snd) fp_decls Termtab.empty
    
  in ((funcs, fp_decls', tr_context', ctxt'), ts) end


(** eta-expand quantifiers, let expressions and built-ins *)

local 
  fun eta f T t = Abs (Name.uu, T, f (Term.incr_boundvars 1 t $ Bound 0))

  fun exp f T = eta f (Term.domain_type (Term.domain_type T))

  fun exp2 T q =
    let val U = Term.domain_type T
    in Abs (Name.uu, U, q $ eta I (Term.domain_type U) (Bound 0)) end

  fun expf k i T t =
    let val Ts = drop i (fst (Flatbelle_SMT_Util.dest_funT k T))
    in
      Term.incr_boundvars (length Ts) t
      |> fold_rev (fn i => fn u => u $ Bound i) (0 upto length Ts - 1)
      |> fold_rev (fn T => fn u => Abs (Name.uu, T, u)) Ts
    end

in

fun eta_expand ctxt funcs =
  let
    fun exp_func t T ts =
      (case Termtab.lookup funcs t of
          SOME k => Term.list_comb (t, ts) |> k <> length ts ? expf k (length ts) T
      | NONE => Term.list_comb (t, ts))
        
    fun expand ((q as Const (\<^const_name>\<open>All\<close>, _)) $ Abs a) = q $ abs_expand a 
      | expand ((q as Const (\<^const_name>\<open>All\<close>, T)) $ t) = q $ exp expand T t
      | expand (q as Const (\<^const_name>\<open>All\<close>, T)) = exp2 T q  
      | expand ((q as Const (\<^const_name>\<open>Ex\<close>, _)) $ Abs a) = q $ abs_expand a 
      | expand ((q as Const (\<^const_name>\<open>Ex\<close>, T)) $ t) = q $ exp expand T t
      | expand (q as Const (\<^const_name>\<open>Ex\<close>, T)) = exp2 T q 
      | expand (Const (\<^const_name>\<open>Let\<close>, T) $ t) = 
          let val U = Term.domain_type (Term.range_type T)
          in Abs (Name.uu, U, expand (Bound 0 $ Term.incr_boundvars 1 t)) end 
      | expand (Const (\<^const_name>\<open>Let\<close>, T)) =
          let val U = Term.domain_type (Term.range_type T)
          in Abs (Name.uu, Term.domain_type T, Abs (Name.uu, U, Bound 0 $ Bound 1)) end 
      | expand t = 
          (case Term.strip_comb t of 
            (Const (\<^const_name>\<open>Let\<close>, _), t1::t2::ts) =>
            Term.betapplys (Term.betapply (expand t2, expand t1), map expand ts)
          | (u as Const (c as (_, T)), ts) => 
              (case Flatbelle_SMT_Builtin.dest_builtin ctxt c ts of
                SOME (_, k, us, mk) =>
                  if k = length us then mk (map expand us)
                  else if k < length us then chop k (map expand us) |>> mk |> Term.list_comb
                  else expf k (length ts) T (mk (map expand us))
              | NONE => exp_func u T (map expand ts))
          | (u as Free (_, T), ts) => exp_func u T (map expand ts)
          | (Abs a, ts) => Term.list_comb (abs_expand a, map expand ts)
          | (u, ts) => Term.list_comb (u, map expand ts))
    and abs_expand (n, T, t) = Abs (n, T, expand t)
  in
    map (apsnd expand)
  end

end

(** introduce explicit applications **)

fun intro_explicit_application ctxt funcs ts = raise TODO "intro_explicit_application"

(** map HOL formulas to FOL formulas (i.e., separate formulas froms terms) **)

fun folify ctxt = raise TODO "folify"

(* translation into intermediate format *)

(** utility functions **)

val quantifier = (fn 
    \<^const_name>\<open>All\<close> => SOME SForall
  | \<^const_name>\<open>Ex\<close> => SOME SExists
  | _ => NONE)

fun typ_conv (t: typ) = Flatbelle_SMT_Builtin.Typ t
fun term_conv (t: term) = Flatbelle_SMT_Builtin.Term t

fun group_quant qname Ts (t as Const (q, _) $ Abs (_, T, u)) =
      if q = qname then group_quant qname (T :: Ts) u else (Ts, t) |>> (map typ_conv)
  | group_quant _ Ts t = (Ts, t) |>> (map typ_conv)

fun dest_pat t = raise TERM ("TODO", [t]) (* TODO: when/if we implement triggers *)

fun dest_pats t = raise TERM ("TODO", [t]) (*TODO: when/if we implement triggers *)

fun dest_trigger t = ([], t) (*TODO: when/if we implement triggers*)

fun dest_quant qn T t = quantifier qn |> Option.map (fn q =>
  let
    val (Ts, u) = group_quant qn [T] t
    val (ps, p) = dest_trigger u
  in (q, rev Ts, ps, p) end)

fun fold_map_pat f (SPat ts) = fold_map f ts #>> SPat
  | fold_map_pat f (SNoPat ts) = fold_map f ts #>> SNoPat


(** translation from Isabelle terms into SMT intermediate terms **)

(*** For Flatbelle, transT was extended to handle most terms 
     (Free, Const, $, etc). Lambda abs will gain support soon. ***)
fun intermediate order lOGic dtyps builtin ctxt ts trx = 
  let 
    val is_ho = (case order of Flatbelle_SMT_Util.Higher_Order => true | _ => false)
    fun transT (Flatbelle_SMT_Builtin.Typ (T as TFree _)) = add_typ T true
      | transT (Flatbelle_SMT_Builtin.Typ (T as TVar _)) =  (fn _ => raise TYPE ("bad SMT type!", [T], []))
      | transT (Flatbelle_SMT_Builtin.Typ (T as Type _)) = 
          (case Flatbelle_SMT_Builtin.dest_builtin_typ ctxt T of
            SOME (n, []) => pair n
          | SOME (n, Ts) =>
            fold_map transT Ts 
            #>> (fn ns => enclose "(" ")" (implode_space (n :: ns)))
          | NONE =>  add_typ T true )
     | transT (Flatbelle_SMT_Builtin.Term t) =
        (case Term.strip_comb t of
          (Const (qn, _), [Abs _]) => (* Extend to add support for lambda abs*)
            raise TERM ("quantifiers as type parameter is not allowed", [t]) (*FIXME: What about applied lambda abstractions?*)
        | (Const (c as (_, T)), ts) => 
            (case builtin ctxt c ts of
              SOME (n, _, [], _) => pair n
            | SOME (n, _, us, _) => map term_conv us  |> fold_map transT 
              #>> (fn ns => enclose "(" ")" (implode_space (n :: ns))) 
            | NONE => transC t T ts) 
        | (Free (_, T), ts) => transC t T ts 
        | _ => raise TERM ("unsupported type parameter", [t]))
      and transC t T ts =
        let val (Us, U) = Flatbelle_SMT_Util.dest_funT (length ts) T in 
          fold_map transT (Us |> (map typ_conv)) ##>> transT (typ_conv U) #-> 
            (fn Up => add_fun t (SOME Up))
        end

    fun trans t = 
      (case Term.strip_comb t of  
        (Const (qn, _), [Abs (_, T, t1)]) => 
          (case dest_quant qn T t1 of
            SOME (q, Ts, ps, b) => 
              fold_map transT Ts ##>> fold_map (fold_map_pat trans) ps ##>>
              trans b #>> (fn ((Ts', ps'), b') => SQua (q, Ts', ps', b'))
          | NONE => raise TERM ("unsupported quantifier", [t]))
      | (u as Const (c as (_, T)), ts) =>
          (case builtin ctxt c ts of
            SOME (n, _, us, _) => fold_map trans us #>> curry SConst n 
          | NONE =>  trans_applied_fun u T ts)
      | (u as Free (_, T), ts) => trans_applied_fun u T ts
      | (Bound i, ts) => pair i ##>> fold_map trans ts #>> SVar
      | _ => raise TERM ("bad SMT term", [t])) 

    and trans_applied_fun t T ts =
      let val (Us, U) = Flatbelle_SMT_Util.dest_funT (length ts) T
      in fold_map transT' (Us |> (map typ_conv)) ##>> transT' (typ_conv U) #-> (fn Up => 
            add_fun t (SOME Up) ##>> fold_map trans ts #>> SConst)
      end
    and transT' (t as (Flatbelle_SMT_Builtin.Typ (T as TFree (_,\<^sort>\<open>HOL.type\<close>))))  =  
          if is_ho then add_typ_var T true else transT t (*If we want declare poly func instead of uninterpreted.*)
      | transT' t = transT t
      
    val (us, trx') = fold_map (fn (role, t) => apfst (pair role) o trans t) ts trx
  in ((sign_of (lOGic ts) dtyps trx', us), trx')  end


(* transaltion *)

structure Configs = Generic_Data
(
  type T = (Proof.context -> config) Flatbelle_SMT_Util.dict
  val empty = []
  fun merge data = Flatbelle_SMT_Util.dict_merge fst data
)

fun add_config (cs, cfg) = Configs.map (Flatbelle_SMT_Util.dict_update (cs, cfg))

fun get_config ctxt = 
  let val cs = Flatbelle_SMT_Config.solver_class_of ctxt
  in
    (case Flatbelle_SMT_Util.dict_get (Configs.get (Context.Proof ctxt)) cs of
      SOME cfg => cfg ctxt
    | NONE => error ("error in get config, TODO: add more info"))
  end

fun translate ctxt flattener smt_options comments (ithms : ((int * Flatbelle_SMT_Util.role) * thm) list) = 
  let
    val {order, lOGic, fp_kinds, serialize} = get_config ctxt
    fun no_dtyps (tr_context, ctxt) ts = 
      ((Termtab.empty, [], tr_context, ctxt), ts)

    val ts1 = map (Flatbelle_SMT_Util.map_prod snd (Envir.beta_eta_contract o Flatbelle_SMT_Util.prop_of)) ithms
    
    val ((funcs, dtyps, tr_context, ctxt1), ts2) =
      ((empty_tr_context, ctxt), ts1)
      |-> (if null fp_kinds then no_dtyps else no_dtyps) (*collect_co_datatypes fp_kinds*)

   fun mk_trigger t = t (* TODO: as of now we do not care about defining patterns/triggers. *)
   
   fun is_binder (Const (\<^const_name>\<open>Let\<close>, _) $ _) = true
     | is_binder t = Lambda_Lifting.is_quantifier t

   val (ctxt2, (ts3, ll_defs)) = 
     ts2
     |> eta_expand ctxt1 funcs
     |> rpair ctxt1
     |-> Lambda_Lifting.lift_lambdas' NONE is_binder
     |-> (fn (ts', ll_defs) => fn ctxt' =>
       let
         val ts'' = map (pair Flatbelle_SMT_Util.Axiom o mk_trigger) ll_defs @ ts'
                    (*FIXME: since SMTLIB 3 is HO by def, this can be fixed later.*)
       in
         (ctxt', (ts'', ll_defs))
       end)
    fun builtin t = t
    
  in
    (ts3, tr_context) 
    |-> intermediate order (lOGic flattener o map snd) dtyps 
      (builtin Flatbelle_SMT_Builtin.dest_builtin) ctxt2
    |>> uncurry (serialize smt_options comments)
    |> fst
  end

end;