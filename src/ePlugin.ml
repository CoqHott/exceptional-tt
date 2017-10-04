open CErrors
open Pp
open Util
open Names
open Context
open Term
open Decl_kinds
open Libobject
open Mod_subst
open Globnames
open Proofview.Notations

(** Utilities *)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵉ")

let translate_internal_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵒ")

(** Record of translation between globals *)

type translator = ETranslate.translator

let translator : translator ref =
  Summary.ref ~name:"Effect Global Table" { ETranslate.refs = Cmap.empty; ETranslate.inds = Mindmap.empty }

type extension =
| ExtConstant of Constant.t * global_reference
| ExtInductive of MutInd.t * MutInd.t

type translator_obj =
| ExtendEffect of extension list

let extend_translator tr l =
  let open ETranslate in
  let fold accu = function
  | ExtConstant (cst, gr) -> { accu with refs = Cmap.add cst gr accu.refs }
  | ExtInductive (mind, mind') -> { accu with inds = Mindmap.add mind mind' accu.inds }
  in
  List.fold_left fold tr l

let cache_translator (_, l) = match l with
| ExtendEffect l ->
  translator := extend_translator !translator l

let load_translator _ obj = cache_translator obj
let open_translator _ obj = cache_translator obj

let subst_extension subst ext = match ext with
| ExtConstant (cst, gr) ->
  let cst' = subst_constant subst cst in
  let gr' = subst_global_reference subst gr in
  if cst' == cst && gr' == gr then ext
  else ExtConstant (cst', gr')
| ExtInductive (smind, tmind) ->
  let smind' = subst_mind subst smind in
  let tmind' = subst_mind subst tmind in
  if smind' == smind && tmind' == tmind then ext
  else ExtInductive (smind', tmind')

let subst_translator (subst, obj) = match obj with
| ExtendEffect l ->
  let l' = List.smartmap (fun e -> subst_extension subst e) l in
  if l' == l then obj else ExtendEffect l'

let in_translator : translator_obj -> obj =
  declare_object { (default_object "FORCING TRANSLATOR") with
    cache_function = cache_translator;
    load_function = load_translator;
    open_function = open_translator;
    discharge_function = (fun (_, o) -> Some o);
    classify_function = (fun o -> Substitute o);
  }

(** Tactic *)

let empty_translator = Refmap.empty

let solve_evars env sigma c =
  let evdref = ref sigma in
  let c = Typing.e_solve_evars env evdref c in
  (!evdref, c)

let declare_constant id uctx c t =
  let ce = Declare.definition_entry ~types:t ~univs:uctx c in
  let cd = Entries.DefinitionEntry ce in
  let decl = (cd, IsProof Lemma) in
  let cst_ = Declare.declare_constant id decl in
  cst_

let translate_constant translator cst ids =
  let id = match ids with
  | None -> translate_name (Nametab.basename_of_global (ConstRef cst))
  | Some [id] -> id
  | Some _ -> user_err (str "Not the right number of provided names")
  in
  (** Translate the type *)
  let env = Global.env () in
  let (typ, uctx) = Global.type_of_global_in_context env (ConstRef cst) in
  let typ = EConstr.of_constr typ in
  let sigma = Evd.from_env env in
  let (sigma, typ) = ETranslate.translate_type translator env sigma typ in
  let (sigma, typ) = solve_evars env sigma typ in
  let sigma, _ = Typing.type_of env sigma typ in
  let _uctx = Evd.evar_universe_context sigma in
  (** Define the term by tactic *)
  let (body, _) = Option.get (Global.body_of_constant cst) in
  let body = EConstr.of_constr body in
  let (sigma, body) = ETranslate.translate translator env sigma body in
  let (sigma, body) = solve_evars env sigma body in
  let evdref = ref sigma in
  let () = Typing.e_check env evdref body typ in
  let sigma = !evdref in
  let body = EConstr.to_constr sigma body in
  let typ = EConstr.to_constr sigma typ in
  let uctx = UState.context (Evd.evar_universe_context sigma) in
  let cst_ = declare_constant id uctx body typ in
  [ExtConstant (cst, ConstRef cst_)]

let sort_of_elim sigma body =
  let open Declarations in
  if List.mem Sorts.InType body.mind_kelim then
    let (sigma, s) = Evd.new_sort_variable Evd.univ_flexible sigma in
    let sigma =
      if Array.length body.mind_consnames > 1 then
        Evd.set_leq_sort Environ.empty_env sigma (Prop Pos) s
      else sigma
    in
    (sigma, mkSort s)
  else (sigma, mkProp)

let sort_of env sigma c =
  let evdref = ref sigma in
  let sort = Typing.e_sort_of env evdref c in
  (!evdref, sort)

let substl_rel_context subst ctx =
  let ctx = Vars.substl subst (it_mkProd_or_LetIn mkProp ctx) in
  let (ctx, _) = Term.decompose_prod_assum ctx in
  ctx

(********************************)
(* Discharging mutual inductive *)

module ExternInd :
sig
val process_inductive : Declarations.mutual_inductive_body -> Entries.mutual_inductive_entry
end =
struct

open Constr
open Vars
open Entries
open Declarations
open Context.Rel.Declaration

let detype_param =
  function
  | LocalAssum (Name id, p) -> id, LocalAssumEntry p
  | LocalDef (Name id, p,_) -> id, LocalDefEntry p
  | _ -> anomaly (Pp.str "Unnamed inductive local variable.")

(* Replace

     Var(y1)..Var(yq):C1..Cq |- Ij:Bj
     Var(y1)..Var(yq):C1..Cq; I1..Ip:B1..Bp |- ci : Ti

   by

     |- Ij: (y1..yq:C1..Cq)Bj
     I1..Ip:(B1 y1..yq)..(Bp y1..yq) |- ci : (y1..yq:C1..Cq)Ti[Ij:=(Ij y1..yq)]
*)

let abstract_inductive nparams inds =
(* To be sure to be the same as before, should probably be moved to process_inductive *)
  let params' = let (_,arity,_,_,_) = List.hd inds in
		let (params,_) = decompose_prod_n_assum nparams arity in
                List.map detype_param params
  in
  let ind'' =
  List.map
    (fun (a,arity,template,c,lc) ->
      let _, short_arity = decompose_prod_n_assum nparams arity in
      let shortlc =
	List.map (fun c -> snd (decompose_prod_n_assum nparams c)) lc in
      { mind_entry_typename = a;
	mind_entry_arity = short_arity;
	mind_entry_template = template;
	mind_entry_consnames = c;
	mind_entry_lc = shortlc })
    inds
  in (params',ind'')

let refresh_polymorphic_type_of_inductive (_,mip) =
  match mip.mind_arity with
  | RegularArity s -> s.mind_user_arity, false
  | TemplateArity ar ->
    let ctx = List.rev mip.mind_arity_ctxt in
      mkArity (List.rev ctx, Type ar.template_level), true

let process_inductive mib =
  let nparams = Context.Rel.length mib.mind_params_ctxt in
  let ind_univs = match mib.mind_universes with
  | Monomorphic_ind ctx -> Monomorphic_ind_entry ctx
  | Polymorphic_ind auctx ->
    let auctx = Univ.AUContext.repr auctx in
    Polymorphic_ind_entry auctx
  | Cumulative_ind cumi ->
    let auctx = Univ.ACumulativityInfo.univ_context cumi in
    let auctx = Univ.AUContext.repr auctx in
    Cumulative_ind_entry (Universes.univ_inf_ind_from_universe_context auctx)
  in
  let map mip =
    let arity, template = refresh_polymorphic_type_of_inductive (mib,mip) in
    (mip.mind_typename,
      arity, template,
      Array.to_list mip.mind_consnames,
      Array.to_list mip.mind_user_lc)
  in
  let inds = Array.map_to_list map mib.mind_packets in
  let (params', inds') = abstract_inductive nparams inds in
  let record = match mib.mind_record with
    | Some (Some (id, _, _)) -> Some (Some id)
    | Some None -> Some None
    | None -> None
  in
  { mind_entry_record = record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params';
    mind_entry_inds = inds';
    mind_entry_private = mib.mind_private;
    mind_entry_universes = ind_univs
  }

end

(** From a kernel inductive body construct an entry for the inductive. *)
let translate_inductive_aux translator env mind =
  let mind' = ExternInd.process_inductive mind in
  let mind = ETranslate.translate_inductive translator env mind mind' in
  mind

(** Register the wrapping of the inductive type and its constructors *)
let translate_inductive_defs translator ind ind_ mind mind_ =
  [ExtInductive (ind, ind_)]

let translate_inductive translator ind =
  let open Declarations in
  let env = Global.env () in
  let (mind, _) = Inductive.lookup_mind_specif env ind in
  let mind_ = translate_inductive_aux translator env mind in
  let ((_, kn), _) = Declare.declare_mind mind_ in
  let ind_ = Global.mind_of_delta_kn kn in
  let mind_ = Global.lookup_mind ind_ in
  translate_inductive_defs translator (fst ind) ind_ mind mind_

let translate gr ids =
  let gr = Nametab.global gr in
  let translator = !translator in
  let ans = match gr with
  | ConstRef cst -> translate_constant translator cst ids
  | IndRef ind -> translate_inductive translator ind
  | _ -> user_err (str "Translation not handled.")
  in
  let () = Lib.add_anonymous_leaf (in_translator (ExtendEffect ans)) in
  let msg_translate = function
  | ExtConstant (cst, gr) ->
    Feedback.msg_info (str "Global " ++ Printer.pr_global (ConstRef cst) ++
    str " has been translated as " ++ Printer.pr_global gr ++ str ".")
  | ExtInductive (smind, tmind) ->
    let mib = Global.lookup_mind smind in
    let len = Array.length mib.Declarations.mind_packets in
    let l = List.init len (fun n -> (IndRef (smind, n), IndRef (tmind, n))) in
    let pr (src, dst) =
      Feedback.msg_info (str "Global " ++ Printer.pr_global src ++
      str " has been translated as " ++ Printer.pr_global dst ++ str ".")
    in
    List.iter pr l
  in
  List.iter msg_translate ans

(*
(** Implementation in the forcing layer *)

let implement eff id typ idopt =
  let (eff, translator) = get_translator eff in
  let env = Global.env () in
  let id_ = match idopt with
  | None -> translate_name id
  | Some id -> id
  in
  let kind = Global, false, DefinitionBody Definition in
  let sigma = Evd.from_env env in
  let (typ, uctx) = Constrintern.interp_type env sigma typ in
  let sigma = Evd.from_ctx uctx in
  let (sigma, translator) = ETranslate.make_context translator env sigma in
  let (sigma, typ_) = ETranslate.translate_type translator sigma typ in
  let (sigma, _) = Typing.type_of env sigma typ_ in
  let hook _ dst =
    (** Declare the original term as an axiom *)
    let param = (None, false, (typ, Evd.evar_context_universe_context uctx), None) in
    let cb = Entries.ParameterEntry param in
    let cst = Declare.declare_constant id (cb, IsDefinition Definition) in
    (** Attach the axiom to the forcing implementation *)
    Lib.add_anonymous_leaf (in_translator (ExtendEffect (eff, [ConstRef cst, dst])))
  in
  let hook ctx = Lemmas.mk_hook hook in
  let sigma, _ = Typing.type_of env sigma typ_ in
  let () = Lemmas.start_proof_univs id_ kind sigma typ_ hook in
  ()
*)

(** Error handling *)

let pr_global = function
| VarRef id -> str "Variable " ++ Nameops.pr_id id
| ConstRef cst -> str "Constant " ++ Constant.print cst
| IndRef (ind, _) -> str "Inductive " ++ MutInd.print ind
| ConstructRef ((ind, _), _) -> str "Inductive " ++ MutInd.print ind

let _ = register_handler begin function
| ETranslate.MissingGlobal gr ->
  let ref = Nametab.shortest_qualid_of_global Id.Set.empty gr in
  str "No translation for global " ++ Libnames.pr_qualid ref ++ str "."
| ETranslate.MissingPrimitive gr ->
  let ref = pr_global gr in
  str "Missing primitive: " ++ ref ++ str "."
| _ -> raise Unhandled
end
