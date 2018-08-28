open CErrors
open Pp
open Util
open Names
open Term
open Decl_kinds
open Libobject
open Mod_subst
open Globnames

(** Utilities *)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵉ")

let ptranslate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᴿ")

let wtranslate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵂ")

let translate_param_name id =
  let id = Id.to_string id in
  Id.of_string ("param_" ^ id)

(** Record of translation between globals *)

type translator = ETranslate.translator

let empty_translator = 
  let open ETranslate in 
  let refss = Cmap.add param_cst (GlobGen (ConstRef param_cst_e))  Cmap.empty in
  let inds = Mindmap.add default_mutind (GlobGen default_mutind_e) Mindmap.empty in
  let prefs = Cmap.add param_cst (GlobGen (ConstRef param_cst_r))  Cmap.empty in
  let pinds = Mindmap.add default_mutind (GlobGen default_mutind_r) Mindmap.empty in
  {
    ETranslate.refs = refss;
    inds = inds;
    prefs = prefs;
    pinds = pinds;
    wrefs = Cmap.empty;
    winds = Mindmap.empty;
    paramrefs = Mindmap.empty;
    paraminds = Mindmap.empty;
  }

let translator : translator ref =
  Summary.ref ~name:"Effect Global Table" empty_translator

type extension_type =
| ExtEffect
| ExtParam
| ExtWeakly

type extension =
| ExtConstant of Constant.t * global_reference
| ExtInductive of MutInd.t * MutInd.t
| ExtParamInductive of MutInd.t * MutInd.t
| ExtParamConstant of MutInd.t * global_reference

type translator_obj =
| ExtendEffect of extension_type * global_reference option * extension list

let extend_constant exn cst gr map = match exn with
| None -> Cmap.add cst (ETranslate.GlobGen gr) map
| Some exn ->
  let old =
    try Cmap.find cst map
    with Not_found -> ETranslate.GlobImp Refmap.empty
  in
  match old with
  | ETranslate.GlobImp imp ->
    let imp = Refmap.add exn gr imp in
    Cmap.add cst (ETranslate.GlobImp imp) map
  | ETranslate.GlobGen _ -> assert false

let extend_inductive exn ind nind map = match exn with
| None -> Mindmap.add ind (ETranslate.GlobGen nind) map
| Some exn ->
  let old =
    try Mindmap.find ind map
    with Not_found -> ETranslate.GlobImp Refmap.empty
  in
  match old with
  | ETranslate.GlobImp imp ->
    let imp = Refmap.add exn nind imp in
    Mindmap.add ind (ETranslate.GlobImp imp) map
  | ETranslate.GlobGen _ -> assert false

let extend_translator tr knd exn l =
  let open ETranslate in
  let fold accu ext = match knd, ext with
  | ExtEffect, ExtConstant (cst, gr) ->
    { accu with refs = extend_constant exn cst gr accu.refs }
  | ExtEffect, ExtInductive (mind, mind') ->
    { accu with inds = extend_inductive exn mind mind' accu.inds }
  | ExtParam, ExtConstant (cst, gr) ->
    { accu with prefs = extend_constant exn cst gr accu.prefs }
  | ExtParam, ExtInductive (mind, mind') ->
    { accu with pinds = extend_inductive exn mind mind' accu.pinds }
  | ExtWeakly, ExtConstant (cst, gr) ->
    { accu with wrefs = extend_constant exn cst gr accu.wrefs }
  | ExtWeakly, ExtInductive (mind, mind') ->
    { accu with winds = extend_inductive exn mind mind' accu.winds }
  | ExtWeakly, ExtParamConstant (cst, gr) ->
    { accu with paramrefs = extend_inductive exn cst gr accu.paramrefs }
  | ExtWeakly, ExtParamInductive (mind, mind') ->
    { accu with paraminds = extend_inductive exn mind mind' accu.paraminds }
  | _ -> accu
  in
  List.fold_left fold tr l

let cache_translator (_, l) = match l with
| ExtendEffect (knd, exn, l) ->
  translator := extend_translator !translator knd exn l

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
(** what !!! *)
| ExtParamConstant (smind, gr) ->
  let smind' = subst_mind subst smind in
  let gr' = subst_global_reference subst gr in
  if smind' == smind && gr' == gr then ext
  else ExtParamConstant (smind', gr')
| ExtParamInductive (smind, tmind) ->
  let smind' = subst_mind subst smind in
  let tmind' = subst_mind subst tmind in
  if smind' == smind && tmind' == tmind then ext
  else ExtParamInductive (smind', tmind')

let subst_translator (subst, obj) = match obj with
| ExtendEffect (knd, exn, l) ->
  let exn' = Option.smartmap (fun gr -> subst_global_reference subst gr) exn in
  let l' = List.smartmap (fun e -> subst_extension subst e) l in
  if exn' == exn && l' == l then obj else ExtendEffect (knd, exn', l')

let in_translator : translator_obj -> obj =
  declare_object { (default_object "FORCING TRANSLATOR") with
    cache_function = cache_translator;
    load_function = load_translator;
    open_function = open_translator;
    discharge_function = (fun (_, o) -> Some o);
    classify_function = (fun o -> Substitute o);
    subst_function = subst_translator;
  }

(** Tactic *)

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

let on_one_id f ids cst = match ids with
| None -> f (Nametab.basename_of_global (ConstRef cst))
| Some [id] -> id
| Some _ -> user_err (str "Not the right number of provided names")

let translate_constant err translator cst ids =
  let id = on_one_id translate_name ids cst in
  (** Translate the type *)
  let env = Global.env () in
  let (typ, uctx) = Global.type_of_global_in_context env (ConstRef cst) in
  let typ = EConstr.of_constr typ in
  let sigma = Evd.from_env env in
  let (sigma, typ) = ETranslate.translate_type err translator env sigma typ in
  let sigma, _ = Typing.type_of env sigma typ in
  let body = Option.get (Global.body_of_constant cst) in
  let body = EConstr.of_constr body in
  let (sigma, body) = ETranslate.translate err translator env sigma body in
  let evdref = ref sigma in
  let () = Typing.e_check env evdref body typ in
  let sigma = !evdref in
  let body = EConstr.to_constr sigma body in
  let typ = EConstr.to_constr sigma typ in
  let uctx = UState.context (Evd.evar_universe_context sigma) in
  let cst_ = declare_constant id uctx body typ in
  [ExtConstant (cst, ConstRef cst_)]

(** Fix potential mismatch between the generality of parametricity and effect
    translations *)
let instantiate_error env sigma err gen c_ = match err with
| None -> (sigma, c_)
| Some err ->
  if gen then
    let (sigma, err) = Evd.fresh_global env sigma err in
    (sigma, mkApp (c_, [| err |]))
  else (sigma, c_)

let ptranslate_constant err translator cst ids =
  let id = on_one_id ptranslate_name ids cst in
  (** Translate the type *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (typ, uctx) = Global.type_of_global_in_context env (ConstRef cst) in
  let (sigma, (_, u)) = Evd.fresh_constant_instance env sigma cst in
  let typ = Vars.subst_instance_constr u typ in
  let gen, c_ =
    try ETranslate.get_instance err (Cmap.find cst translator.ETranslate.refs)
    with Not_found -> raise (ETranslate.MissingGlobal (err, ConstRef cst))
  in
  let typ = EConstr.of_constr typ in
  let (sigma, typ) = ETranslate.ptranslate_type err translator env sigma typ in
  let (sigma, c_) = Evd.fresh_global env sigma c_ in
  let (sigma, c_) = ETranslate.instantiate_error err env sigma gen (EConstr.of_constr c_) in
  let typ = EConstr.Vars.subst1 c_ typ in
  let sigma, _ = Typing.type_of env sigma typ in
  let body = Option.get (Global.body_of_constant cst) in
  let body = EConstr.of_constr body in
  let (sigma, body) = ETranslate.ptranslate err translator env sigma body in
  let evdref = ref sigma in
  let () = Typing.e_check env evdref body typ in
  let sigma = !evdref in
  let body = EConstr.to_constr sigma body in
  let typ = EConstr.to_constr sigma typ in
  let uctx = UState.context (Evd.evar_universe_context sigma) in
  let cst_ = declare_constant id uctx body typ in
  [ExtConstant (cst, ConstRef cst_)]

let primitives_from_declaration env (ind: Names.mutual_inductive) =
  let open Declarations in 
  let (mind, _) = Inductive.lookup_mind_specif env (ind, 0) in  
  let (_, projs, _) = Option.get (Option.get mind.mind_record) in
  Array.to_list projs

let translate_inductive_gen f err translator (ind, _) =
  let env = Global.env () in
  let (mind, _ as specif) = Inductive.lookup_mind_specif env (ind, 0) in

  let primitive_records = Inductive.is_primitive_record specif in 

  let mind' = EUtil.process_inductive mind in
  let mind_ = f err translator env ind mind mind' in
  let ((_, kn), _) = Declare.declare_mind mind_ in
  let ind_ = Global.mind_of_delta_kn kn in
  let extensions = 
    if primitive_records then 
      let env = Global.env () in
      let proj  = primitives_from_declaration env ind in 
      let proj_ = primitives_from_declaration env ind_ in 
      let pair = List.combine proj proj_ in
      List.map (fun (p, pe) -> ExtConstant (p, ConstRef pe)) pair
    else
      []
  in
  (ExtInductive (ind, ind_)) :: extensions

let translate_inductive err translator ind =
  translate_inductive_gen ETranslate.translate_inductive err translator ind

let ptranslate_inductive err translator ind =
  translate_inductive_gen ETranslate.ptranslate_inductive err translator ind

let msg_translate = function
| ExtConstant (cst, gr) ->
  (str "Global " ++ Printer.pr_global (ConstRef cst) ++
  str " has been translated as " ++ Printer.pr_global gr ++ str ".")
| ExtInductive (smind, tmind) ->
  let mib = Global.lookup_mind smind in
  let len = Array.length mib.Declarations.mind_packets in
  let l = List.init len (fun n -> (IndRef (smind, n), IndRef (tmind, n))) in
  let pr (src, dst) =
    (str "Global " ++ Printer.pr_global src ++
    str " has been translated as " ++ Printer.pr_global dst ++ str ".")
  in
  prlist_with_sep fnl pr l
| ExtParamInductive _ -> 
   str "Parametric inducitve extension"
| ExtParamConstant _ ->
   str "Parametric constant extension"

let translate ?exn ?names gr =
  let ids = names in
  let err = Option.map Nametab.global exn in
  let gr = Nametab.global gr in
  let translator = !translator in
  let ans = match gr with
  | ConstRef cst -> translate_constant err translator cst ids
  | IndRef ind -> translate_inductive err translator ind
  | ConstructRef _ -> user_err (str "Use the translation over the corresponding inductive type instead.")
  | VarRef _ -> user_err (str "Variable translation not handled.")
  in
  let ext = ExtendEffect (ExtEffect, err, ans) in
  let () = Lib.add_anonymous_leaf (in_translator ext) in
  let msg = prlist_with_sep fnl msg_translate ans in
  Feedback.msg_info msg

let ptranslate ?exn ?names gr =
  let ids = names in
  let err = Option.map Nametab.global exn in
  let gr = Nametab.global gr in
  let translator = !translator in
  let ans = match gr with
  | ConstRef cst -> ptranslate_constant err translator cst ids
  | IndRef ind -> ptranslate_inductive err translator ind 
  | ConstructRef _ -> user_err (str "Use the translation over the corresponding inductive type instead.")
  | VarRef _ -> user_err (str "Variable translation not handled.")
  in
  let ext = ExtendEffect (ExtParam, err, ans) in
  let () = Lib.add_anonymous_leaf (in_translator ext) in
  let msg = prlist_with_sep fnl msg_translate ans in
  Feedback.msg_info msg

(** Implementation in the forcing layer *)

let implement ?exn id typ =
  let env = Global.env () in
  let translator = !translator in
  let err = Option.map Nametab.global exn in
  let id_ = translate_name id in
  let sigma = Evd.from_env env in
  let (typ, uctx) = Constrintern.interp_type env sigma typ in
  let sigma = Evd.from_ctx uctx in
  let typ = EConstr.of_constr typ in
  let (sigma, typ) = solve_evars env sigma typ in
  let (sigma, typ_) = ETranslate.translate_type err translator env sigma typ in
  let typ = EConstr.to_constr sigma typ in
  let (sigma, _) = Typing.type_of env sigma typ_ in
  let hook _ dst =
    (** Declare the original term as an axiom *)
    let param = (None, false, (typ, Evd.evar_context_universe_context uctx), None) in
    let cb = Entries.ParameterEntry param in
    let cst = Declare.declare_constant id (cb, IsDefinition Definition) in
    (** Attach the axiom to the forcing implementation *)
    let ext = ExtendEffect (ExtEffect, err, [ExtConstant (cst, dst)]) in
    Lib.add_anonymous_leaf (in_translator ext)
  in
  let hook ctx = Lemmas.mk_hook hook in
  let sigma, _ = Typing.type_of env sigma typ_ in
  let kind = Global, false, DefinitionBody Definition in
  let () = Lemmas.start_proof_univs id_ kind sigma typ_ hook in
  ()

let pimplement ?exn gr =
  let env = Global.env () in
  let translator = !translator in
  let err = Option.map Nametab.global exn in
  let cst = match Nametab.global gr with
  | ConstRef cst -> cst
  | _ -> user_err (str "Parametricity can only be implemented for constants")
  in
  let id = Label.to_id (Constant.label cst) in
  let sigma = Evd.from_env env in
  (** Drop the context as translation doesn't care. TODO: handle this properly. *)
  let (typ, _) = Global.type_of_global_in_context env (ConstRef cst) in
  let gen, c_ =
    try ETranslate.get_instance err (Cmap.find cst translator.ETranslate.refs)
    with Not_found -> raise (ETranslate.MissingGlobal (err, ConstRef cst))
  in
  let typ = EConstr.of_constr typ in
  let (sigma, typ) = ETranslate.ptranslate_type err translator env sigma typ in
  let (sigma, c_) = Evd.fresh_global env sigma c_ in
  let (sigma, c_) = instantiate_error env sigma err gen c_ in
  let typ = EConstr.Vars.subst1 (EConstr.of_constr c_) typ in
  (** Retype for constraints *)
  let (sigma, _) = Typing.type_of env sigma typ in
  let hook _ dst =
    (** Attach the axiom to the implementation *)
    let ext = ExtendEffect (ExtParam, err, [ExtConstant (cst, dst)]) in
    Lib.add_anonymous_leaf (in_translator ext)
  in
  let hook ctx = Lemmas.mk_hook hook in
  let kind = Global, false, DefinitionBody Definition in
  let idr = ptranslate_name id in
  let () = Lemmas.start_proof_univs idr kind sigma typ hook in
  ()

(** Error handling *)

let pr_global = function
| VarRef id -> str "Variable " ++ Nameops.pr_id id
| ConstRef cst -> str "Constant " ++ Constant.print cst
| IndRef (ind, _) -> str "Inductive " ++ MutInd.print ind
| ConstructRef ((ind, _), _) -> str "Inductive " ++ MutInd.print ind

let _ = register_handler begin function
| ETranslate.MissingGlobal (eff, gr) ->
  let eff = match eff with
  | None -> str "for generic exceptions"
  | Some gr -> str "for instance" ++ spc () ++ Printer.pr_global gr
  in
  str "No translation for global " ++ Printer.pr_global gr ++ spc () ++ eff ++ str "."
| ETranslate.MissingPrimitive gr ->
  let ref = pr_global gr in
  str "Missing primitive: " ++ ref ++ str "."
| _ -> raise Unhandled
end


(** New weakly Translation *)
(** Arity check *)

let wtranslate_constant err translator cst ids =
  let id = on_one_id wtranslate_name ids cst in
  (** Translate the type *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (typ, uctx) = Global.type_of_global_in_context env (ConstRef cst) in
  let (sigma, (_, u)) = Evd. fresh_constant_instance env sigma cst in
  let typ = Vars.subst_instance_constr u typ in
  let gen, c_ =
    try ETranslate.get_instance err (Cmap.find cst translator.ETranslate.refs)
    with Not_found -> raise (ETranslate.MissingGlobal (err, ConstRef cst))
  in
  let typ = EConstr.of_constr typ in
  let (sigma, typ) = ETranslate.wtranslate_type err translator env sigma typ in
  let (sigma, c_) = Evd.fresh_global env sigma c_ in
  let (sigma, c_) = ETranslate.instantiate_error err env sigma gen (EConstr.of_constr c_) in
  let typ = EConstr.Vars.subst1 c_ typ in
  let sigma, _ = Typing.type_of env sigma typ in
  let body = Option.get (Global.body_of_constant cst) in
  let body = EConstr.of_constr body in
  let (sigma, body) = ETranslate.wtranslate err translator env sigma body in
  let evdref = ref sigma in
  let () = Typing.e_check env evdref body typ in
  let sigma = !evdref in
  let body = EConstr.to_constr sigma body in
  let typ = EConstr.to_constr sigma typ in
  let uctx = UState.context (Evd.evar_universe_context sigma) in
  let cst_ = declare_constant id uctx body typ in
  [ExtConstant (cst, ConstRef cst_)]
    
let instantiate_parametric_modality err translator (name, n) ext  =
  let env = Global.env () in
  let (mind, _ as specif) = Inductive.lookup_mind_specif env (name, 0) in

  let mind' = EUtil.process_inductive mind in
  let mind_ = ETranslate.param_mutual_inductive err translator env name mind mind' in
  let ((_, kn), _) = Declare.declare_mind mind_ in
  let ind_ = Global.mind_of_delta_kn kn in

  let env = Global.env () in
  let (sigma, params) = ETranslate.param_definition err translator env (name, ind_) mind mind' in
  let map n param =
    let open Entries in 
    let body = EConstr.to_constr sigma param in
    let uctx = UState.context (Evd.evar_universe_context sigma) in
    let ce = Declare.definition_entry  ~univs:uctx body in
    let cd = Entries.DefinitionEntry ce in
    let decl = (cd, IsProof Lemma) in
    let id = (List.nth mind'.mind_entry_inds n).mind_entry_typename in
    let id = translate_param_name id in
    let () = Feedback.msg_info (Id.print id) in
    let cst_ = Declare.declare_constant id decl in
    ExtParamConstant (name, ConstRef cst_)
  in
  let extension = List.mapi map params in
  ExtParamInductive (name, ind_) :: extension
    
let wtranslate_inductive err translator ind =
  let ext = translate_inductive_gen ETranslate.wtranslate_inductive err translator ind in 
  let param_ext = instantiate_parametric_modality err translator ind ext in
  ext @ param_ext
                          
let wtranslate ?exn ?names gr =
  let ids = names in
  let err = Option.map Nametab.global exn in
  let gr = Nametab.global gr in
  let translator = !translator in
  let ans = match gr with
  | ConstRef cst -> wtranslate_constant err translator cst ids
  | IndRef ind -> wtranslate_inductive err translator ind 
  | ConstructRef _ -> user_err (str "Use the translation over the corresponding inductive type instead.")
  | VarRef _ -> user_err (str "Variable translation not handled.")
  in
  let ext = ExtendEffect (ExtWeakly, err, ans) in
  let () = Lib.add_anonymous_leaf (in_translator ext) in
  let msg = prlist_with_sep fnl msg_translate ans in
  Feedback.msg_info msg

let wimplement ?exn gr =
  let env = Global.env () in
  let translator = !translator in
  let err = Option.map Nametab.global exn in
  let cst = match Nametab.global gr with
  | ConstRef cst -> cst
  | _ -> user_err (str "Weak parametricity can only be implemented for constants")
  in
  let id = Label.to_id (Constant.label cst) in
  let sigma = Evd.from_env env in
  let (typ, uctx) = Global.type_of_global_in_context env (ConstRef cst) in
  let (sigma, (_, u)) = Evd.fresh_constant_instance env sigma cst in
  let typ = Vars.subst_instance_constr u typ in
  let gen, c_ =
    try ETranslate.get_instance err (Cmap.find cst translator.ETranslate.refs)
    with Not_found -> raise (ETranslate.MissingGlobal (err, ConstRef cst))
  in
  let typ = EConstr.of_constr typ in
  let (sigma, typ) = ETranslate.wtranslate_type err translator env sigma typ in
  let (sigma, c_) = Evd.fresh_global env sigma c_ in
  let (sigma, c_) = instantiate_error env sigma err gen c_ in
  let typ = EConstr.Vars.subst1 (EConstr.of_constr c_) typ in
  let (sigma, _) = Typing.type_of env sigma typ in
  let hook _ dst =
    (** Attach the axiom to the implementation *)
    let ext = ExtendEffect (ExtWeakly, err, [ExtConstant (cst, dst)]) in
    Lib.add_anonymous_leaf (in_translator ext)
  in
  let hook ctx = Lemmas.mk_hook hook in
  let (sigma, _) = Typing.type_of env sigma typ in
  let kind = Global, false, DefinitionBody Definition in
  let idr = wtranslate_name id in
  let () = Lemmas.start_proof_univs idr kind sigma typ hook in
  ()

(** List translate *)

module Generic = struct
  open Libnames
  open Names
         
  let generic_translate ?exn
        (gr_list:reference list) 
        (generic: ?exn:reference -> ?names:Id.t list-> reference -> unit) =
    let fold () gr = generic ?exn gr in
    List.fold_left fold () gr_list
end
open Generic
                      
let list_translate ?exn gr_list =
  generic_translate ?exn gr_list translate
let list_ptranslate ?exn gr_list = 
  generic_translate ?exn gr_list ptranslate
let list_wtranslate ?exn gr_list = 
  generic_translate ?exn gr_list wtranslate
