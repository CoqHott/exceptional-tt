open Util
open CErrors
open Context
open Rel.Declaration
open Names
open Term
open EConstr
open Declarations
open Entries
open Environ

let sign_level env evd sign =
  let fold d (lev, env) = match d with
  | LocalDef _ -> lev, push_rel d env
  | LocalAssum (_, t) ->
    let s = Retyping.get_type_of env evd (EConstr.of_constr t) in
    let s = destSort evd (Reductionops.clos_whd_flags CClosure.all env evd s) in
    let u = univ_of_sort (ESorts.kind evd s) in
    (Univ.sup u lev, push_rel d env)
  in
  fst (List.fold_right fold sign (Univ.type0m_univ, env))

let extract_level env evd min tys =
  let map ty =
    let ctx, concl = Reduction.dest_prod_assum env ty in
    sign_level env evd (LocalAssum (Anonymous, concl) :: ctx)
  in
  let sorts = List.map map tys in
  List.fold_left Univ.sup min sorts

let is_impredicative env u =
  u = Prop Null || (is_impredicative_set env && u = Prop Pos)

let is_flexible_sort evd u =
  match Univ.Universe.level u with
  | Some l -> Evd.is_flexible_level evd l
  | None -> false

let inductive_levels env sigma arities inds =
  let destarities = List.map (fun x -> x, Reduction.dest_arity env x) arities in
  let levels = List.map (fun (x,(ctx,a)) ->
    if a = Prop Null then None
    else Some (univ_of_sort a)) destarities
  in
  let map tys (arity, (ctx, du)) =
    let len = List.length tys in
    let minlev = Sorts.univ_of_sort du in
    let minlev =
      if len > 1 && not (is_impredicative env du) then
        Univ.sup minlev Univ.type0_univ
      else minlev
    in
    let minlev =
      (** Indices contribute. *)
      if Indtypes.is_indices_matter () && List.length ctx > 0 then (
        let ilev = sign_level env sigma ctx in
          Univ.sup ilev minlev)
      else minlev
    in
    let clev = extract_level env sigma minlev tys in
    (clev, minlev, len)
  in
  let cstrs_levels, min_levels, sizes = CList.split3 (List.map2 map inds destarities) in
  (* Take the transitive closure of the system of constructors *)
  (* level constraints and remove the recursive dependencies *)
  let levels' = Universes.solve_constraints_system (Array.of_list levels)
    (Array.of_list cstrs_levels) (Array.of_list min_levels)
  in
  let sigma, arities =
    CList.fold_left3 (fun (sigma, arities) cu (arity,(ctx,du)) len ->
      if is_impredicative env du then
        (** Any product is allowed here. *)
        sigma, arity :: arities
      else (** If in a predicative sort, or asked to infer the type,
               we take the max of:
               - indices (if in indices-matter mode)
               - constructors
               - Type(1) if there is more than 1 constructor
           *)
        (** Constructors contribute. *)
        let sigma =
          if Sorts.is_set du then
            if not (Evd.check_leq sigma cu Univ.type0_univ) then
              raise (Indtypes.InductiveError Indtypes.LargeNonPropInductiveNotInType)
            else sigma
          else sigma
            (* Evd.set_leq_sort env sigma (Type cu) du *)
        in
        let sigma =
          if len >= 2 && Univ.is_type0m_univ cu then
           (** "Polymorphic" type constraint and more than one constructor,
               should not land in Prop. Add constraint only if it would
               land in Prop directly (no informative arguments as well). *)
            Evd.set_leq_sort env sigma (Prop Pos) du
          else sigma
        in
        let duu = Sorts.univ_of_sort du in
        let sigma =
          if not (Univ.is_small_univ duu) && Univ.Universe.equal cu duu then
            if is_flexible_sort sigma duu && not (Evd.check_leq sigma Univ.type0_univ duu) then
              Evd.set_eq_sort env sigma (Prop Null) du
            else sigma
          else Evd.set_eq_sort env sigma (Type cu) du
        in
          (sigma, arity :: arities))
    (sigma, []) (Array.to_list levels') destarities sizes
  in
  (sigma, List.rev arities)

(** Infer the universe constraints for constructors *)
let retype_inductive env sigma params inds =
  let env = Environ.pop_rel_context (Environ.nb_rel env) env in
  let mk_arities sigma ind =
    let arity = it_mkProd_or_LetIn (EConstr.of_constr ind.mind_entry_arity) params in
    let (sigma, _) = Typing.type_of env sigma arity in
    (sigma, arity)
  in
  let (sigma, extarities) = List.fold_left_map mk_arities sigma inds in
  let fold env c ind = EConstr.push_rel (LocalAssum (Name ind.mind_entry_typename, c)) env in
  let env = List.fold_left2 fold env extarities inds in
  let env = EConstr.push_rel_context params env in
  let fold sigma ind =
    let fold sigma c =
      let (sigma, _) = Typing.type_of env sigma (EConstr.of_constr c) in
      sigma
    in
    let sigma = List.fold_left fold sigma ind.mind_entry_lc in
    (sigma, ind.mind_entry_lc)
  in
  let sigma, constructors = List.fold_left_map fold sigma inds in
  let arities = List.map (fun ind -> ind.mind_entry_arity) inds in
  let (sigma, arities) = inductive_levels env sigma arities constructors in
  let params = List.map (fun d -> EConstr.to_rel_decl sigma d) params in
  let sigma, nf = Evarutil.nf_evars_and_universes sigma in
  let map ind arity = { ind with
    mind_entry_arity = nf arity;
    mind_entry_lc = List.map nf ind.mind_entry_lc;
  } in
  let inds = List.map2 map inds arities in
  let params = Rel.map nf params in
  sigma, inds, params

open Term

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
