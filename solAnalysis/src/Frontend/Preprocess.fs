module solAnalysis.Preprocess

open System
open System.Numerics
open Options
open MakeCfg
open Global
open Lang
open Vocab
open FuncMap

(************************************)
(************************************)
(*** Move state_var_init to Cnstr ***)
(************************************)
(************************************)

let decl_to_stmt state_var_decl =
  let (id, eop, vinfo) = state_var_decl
  match eop with
  | None -> Decl (Var (id,vinfo))
  | Some e -> Assign (Var (id,vinfo), e, vinfo.vloc)

let move_f decls func =
  if is_constructor func then (* add initializations of decls to constructors *)
    let inits = List.fold (fun acc decl -> Seq (acc, decl_to_stmt decl)) Skip decls
    let body = Seq(inits, get_body func)
    update_body body func
  else func

let move_c (cid, decls, structs, enums, funcs, cinfo) =
  (cid, decls, structs, enums, List.map (move_f decls) funcs, cinfo)

let move_p contracts = List.map move_c contracts

let move_decl_to_cnstr pgm = move_p pgm

(***********************)
(***********************)
(*** Replace TemExps ***)
(***********************)
(***********************)

let separator = "__@"

let rec hastmp_lv lv =
  match lv with
  | Var _ -> false
  | MemberAccess (e,_,_,_) -> hastmp_e e
  | IndexAccess (e,None,_) -> hastmp_e e
  | IndexAccess (e1,Some e2,_) -> hastmp_e e1 || hastmp_e e2
  | Tuple (eoplst,_) -> List.exists (fun eop -> match eop with None -> false | Some e -> hastmp_e e) eoplst

and hastmp_e e =
  match e with
  | Int _ | Real _ | Str _ -> false 
  | Lv lv -> hastmp_lv lv
  | Cast (_,e) -> hastmp_e e
  | BinOp (_,e1,e2,_) -> hastmp_e e1 || hastmp_e e2
  | UnOp (_,e,_) -> hastmp_e e
  | True | False | ETypeName _ -> false
  | AssignTemp _ | CondTemp _ | IncTemp _ | DecTemp _ | CallTemp _ -> true

and hastmp_s s =
  match s with
  | Assign (lv,e,_) -> hastmp_lv lv || hastmp_e e
  | Decl _ -> false 
  | Seq (s1,s2) -> hastmp_s s1 || hastmp_s s2
  | Call (lvop,e,pars,ethop,gasop,_,_) ->
    let b1 = match lvop with None -> false | Some lv -> hastmp_lv lv
    let b2 = hastmp_e e
    let b3 = List.exists hastmp_e pars
    let b4 = match ethop with None -> false | Some e -> hastmp_e e
    let b5 = match gasop with None -> false | Some e -> hastmp_e e
    b1 || b2 || b3 || b4 || b5
  | Skip -> false
  | If (e,s1,s2,_) -> hastmp_e e || hastmp_s s1 || hastmp_s s2
  | While (e,s) -> hastmp_e e || hastmp_s s
  | Break -> false
  | Continue -> false
  | Return (None,_) -> false
  | Return (Some e,_) -> hastmp_e e 
  | Throw -> false
  | Assume (e,_) -> hastmp_e e
  | Assert (e,_,_) -> hastmp_e e
  | Assembly _ | PlaceHolder -> false
  | Unchecked (lst,loc) -> List.exists hastmp_s lst

let hastmp_f (_,_,_,stmt,_) = hastmp_s stmt
let hastmp_c (_,_,_,_,funcs,_) = List.exists hastmp_f funcs
let hastmp_p contracts = List.exists hastmp_c contracts
let hastmp p = hastmp_p p

(* Given a exp, returns a pair of (replaced exp,new stmt) *)
let rec replace_tmpexp_e exp =
  match exp with
  | Int n -> (exp,Skip)
  | Real n -> (exp,Skip)
  | Str s -> (exp,Skip)
  | Lv lv ->
    let (lv',s) = replace_tmpexp_lv lv
    (Lv lv',s)
  | Cast (typ,e) ->
    let (e',s) = replace_tmpexp_e e
    (Cast (typ,e'),s)
  | BinOp (bop,e1,e2,einfo) ->
    let (e1',s1) = replace_tmpexp_e e1
    let (e2',s2) = replace_tmpexp_e e2
    (BinOp (bop,e1',e2',einfo), Seq (s1,s2))
  | UnOp (uop,e,typ) ->
    let (e',s) = replace_tmpexp_e e
    (UnOp (uop,e',typ), s)
  | True | False -> (exp,Skip)
  | ETypeName _ -> (exp,Skip)
  | IncTemp (Lv lv,prefix,loc) when prefix ->
    let typ = get_type_lv lv
    (Lv lv,Assign (lv, BinOp (Add,Lv lv,Int (BigInteger 1),{eloc=loc; etyp=typ; eid=0}),loc)) 
  | IncTemp (Lv lv,_,loc) -> (* postfix case *)
    let typ = get_type_lv lv
    let tmpvar = gen_tmpvar {Org = None ; Loc = None ; Typ = typ; TypeStr = typ.ToString()}
    (Lv tmpvar,Seq (Assign (tmpvar, Lv lv, loc),
                    Assign (lv, BinOp (Add,Lv lv,Int (BigInteger 1),{eloc=loc; etyp=typ; eid=0}),loc)))
  | DecTemp (Lv lv,prefix,loc) when prefix ->
    let typ = get_type_lv lv
    (Lv lv,Assign (lv, BinOp (Sub,Lv lv,Int (BigInteger 1),{eloc=loc; etyp=typ; eid=0}),loc)) 
  | DecTemp (Lv lv,_,loc) -> (* postfix case *)
    let typ = get_type_lv lv
    let tmpvar = gen_tmpvar {Org = None ; Loc = None ; Typ = typ; TypeStr = typ.ToString()}
    (Lv tmpvar,Seq (Assign (tmpvar, Lv lv, loc), Assign (lv, BinOp (Sub,Lv lv,Int (BigInteger 1),{eloc=loc; etyp=typ; eid=0}),loc)))
  | CallTemp (Lv (Var (s,_)), pars, ethop, gasop, einfo) when s.StartsWith "contract_init" ->
    let tmpvar = gen_tmpvar {Org = None ; Loc = None ; Typ = einfo.etyp; TypeStr = (einfo.etyp).ToString() }(* einfo.etyp : return type of call expression *)
    let fst_arg = Lv (Var (get_name_userdef einfo.etyp,dummy_vinfo))
    (Lv tmpvar, Call (Some tmpvar, Lv (Var ("contract_init",dummy_vinfo)), fst_arg::pars, ethop, gasop, einfo.eloc, einfo.eid))
  | CallTemp (Lv (MemberAccess (Cast (t,e),id,id_info,typ)), pars, ethop, gasop, einfo) -> (* ... := cast(y).f(33) *)
    let tmpvar = gen_tmpvar {Org = Some (Some (Cast (t,e))) ; Loc = None ; Typ = t; TypeStr = t.ToString()}
    let exp' = CallTemp (Lv (MemberAccess (Lv tmpvar,id,id_info,typ)), pars, ethop, gasop, einfo)
    let new_stmt = Assign (tmpvar, Cast (t,e), einfo.eloc)
    (exp', new_stmt)
  | CallTemp (e, pars, ethop, gasop, einfo) ->
    if is_tuple einfo.etyp then
      let rec inner genTmpVar typlst =
        match typlst with
        | [] -> []
        | hd::tl -> genTmpVar {Org = Some (Some exp); Loc = Some einfo.eloc.line; Typ = hd; TypeStr = hd.ToString()} :: inner genTmpVar tl
      let tmpvars = inner gen_tmpvar (tuple_elem_typs einfo.etyp)
      let eoplst = List.map (fun tmp -> Some (Lv tmp)) tmpvars
      let tuple = Tuple (eoplst, einfo.etyp)
      (Lv tuple, Call (Some tuple, e, pars, ethop, gasop, einfo.eloc, einfo.eid))
    else
      let tmpvar = gen_tmpvar {Org = Some(Some exp); Loc = Some einfo.eloc.line; Typ = einfo.etyp; TypeStr = (einfo.etyp).ToString()}
      (Lv tmpvar, Call (Some tmpvar, e, pars, ethop, gasop, einfo.eloc, einfo.eid))
  | CondTemp (e1,e2,e3,typ,loc) ->
    match e2,e3 with
    | Lv (Tuple (eops1,t1)), Lv (Tuple (eops2,t2)) ->
      assert (t1 = t2)
      let rec inner genTmpVar typlst =
        match typlst with
        | [] -> []
        | hd::tl -> genTmpVar {Org = Some (Some exp); Loc = None; Typ = hd; TypeStr = hd.ToString()} :: inner genTmpVar tl
      let tmpvars = inner gen_tmpvar (tuple_elem_typs t1)
      let tuple = Tuple (List.map (fun tmp -> Some (Lv tmp)) tmpvars, t1)
      (Lv tuple, Seq (Decl tuple, If (e1, Assign (tuple, e2, loc), Assign (tuple, e3, loc), dummy_ifinfo)))
    | Lv (Tuple _),_ | _, Lv (Tuple _) -> 
      assert false
      raise (Failure "replace_tmpexp_e : CondTemp")
    | _ ->
       let tmpvar = gen_tmpvar{Org = Some (Some exp); Loc = None; Typ = typ; TypeStr = typ.ToString()}
       (Lv tmpvar, Seq (Decl tmpvar, If (e1, Assign (tmpvar, e2, loc), Assign (tmpvar, e3, loc), dummy_ifinfo)))
  | AssignTemp (lv,e,loc) -> (Lv lv, Assign (lv,e,loc))
  | e -> raise (Failure ("replace_tmpexp_e : " + (to_string_exp (ToStringArg.SingleExp e))))

and replace_tmpexp_lv lv =
  match lv with
  | Var _ -> (lv,Skip)
  | MemberAccess (Cast (t,e),id,id_info,typ) ->
    let tmpvar = gen_tmpvar {Org = Some (Some (Cast (t,e))); Loc = None; Typ = t; TypeStr = t.ToString()}
    (MemberAccess (Lv tmpvar,id,id_info,typ), Assign (tmpvar, Cast (t,e), id_info.vloc))
  | MemberAccess (e,id,id_info,typ) ->
    let (e',s) = replace_tmpexp_e e 
    (MemberAccess (e',id,id_info,typ), s)
  | IndexAccess (e,None,typ) ->
    let (e',s) = replace_tmpexp_e e
    (IndexAccess (e',None,typ), s)
  | IndexAccess (e1,Some e2,typ) ->
    let (e1',s1) = replace_tmpexp_e e1
    let (e2',s2) = replace_tmpexp_e e2 
    (IndexAccess (e1',Some e2',typ), Seq (s1,s2))
  | Tuple (eoplst,typ) ->
    let (eoplst',final_s) =
      List.fold (fun (acc_lst,acc_s) eop ->
        match eop with
        | None -> (acc_lst@[None],acc_s)
        | Some e ->
          let (e',s) = replace_tmpexp_e e
          (acc_lst@[Some e'], Seq (acc_s,s))
      ) ([],Skip) eoplst
    (Tuple (eoplst',typ), final_s)

let replace_tmpexp_lvop lvop = 
  match lvop with
  | None -> (None,Skip)
  | Some lv ->
    let (lv',stmt) = replace_tmpexp_lv lv
    (Some lv',stmt)

let replace_tmpexp_eop eop =
  match eop with
  | None -> (None,Skip)
  | Some e ->
    let (e',stmt) = replace_tmpexp_e e 
    (Some e', stmt)

let has_value_gas_modifiers_old_solc exp =
  match exp with
  | CallTemp (Lv (MemberAccess (e,"gas",_,_)),_,None,None,_) -> true
  | CallTemp (Lv (MemberAccess (e,"value",_,_)),_,None,None,_) -> true
  | CallTemp (Lv (MemberAccess (e,"gas",_,_)),_,_,_,_) -> 
    assert false
    raise (Failure "has_value_gas_modifiers_old_solc")
  | CallTemp (Lv (MemberAccess (e,"value",_,_)),_,_,_,_) -> 
    assert false
    raise (Failure "has_value_gas_modifiers_old_solc")
  | _ -> false

(* e.g., given f.gas(10).value(5).gas(3) , return f *)
let rec remove_value_gas_modifiers exp =
  match exp with
  | CallTemp (Lv (MemberAccess (e,"gas",_,_)),_,_,_,_) -> remove_value_gas_modifiers e (* remove gas modifier chains, e.g., e.gas(10)(arg) => e(arg) *)
  | CallTemp (Lv (MemberAccess (e,"value",_,_)),_,_,_,_) -> remove_value_gas_modifiers e (* remove value modifier chains *)
  | _ -> exp 

(* get outer-most argument of gas modifier *)
let rec get_gasop exp =
  match exp with
  (* | Lv (MemberAccess (e,"call",_,_)) when is_address (get_type_exp e) -> Int BatBig_int.zero *) 
  | CallTemp (Lv (MemberAccess (e,"gas",_,_)),args,_,_,_) ->
    assert (List.length args = 1) 
    Some (List.head args)
  | CallTemp (Lv (MemberAccess (e,"value",_,_)),_,_,_,_) -> get_gasop e
  | _ -> None

(* get outer-most argument of value modifier *)
let rec get_valueop exp =
  match exp with
  (* | Lv (MemberAccess (e,"call",_,_)) when is_address (get_type_exp e) -> Int BatBig_int.zero *)
  | CallTemp (Lv (MemberAccess (e,"gas",_,_)),_,_,_,_) -> get_valueop e
  | CallTemp (Lv (MemberAccess (e,"value",_,_)),args,_,_,_) ->
    assert (List.length args = 1)
    Some (List.head args)
  | _ -> None

let desugar_tuple (lv,e,loc) =
  match lv,e with
  | Tuple (eops1,_), Lv (Tuple (eops2,_)) ->
    List.fold2 (fun acc eop1 eop2 ->
      match eop1,eop2 with
      | Some (Lv lv'), Some e' -> Seq (acc, Assign (lv',e',loc))
      | None, Some e' -> acc
      | _ -> assert false; raise (Failure "desugar_tuple")
    ) Skip eops1 eops2
  | _ -> Assign (lv,e,loc)

let rec replace_tmpexp_s stmt =
  match stmt with
  (* E.g., (bool success, ) := msg.sender.call.value(..)(..) *)
  | Assign (lv, CallTemp (e,pars,ethop,gasop,einfo), loc) ->
    Call (Some lv, e, pars, ethop, gasop, loc, einfo.eid)
  | Assign (lv,e,loc) ->
    let (lv',new_stmt1) = replace_tmpexp_lv lv 
    let (e',new_stmt2) = replace_tmpexp_e e 
    let assigns = desugar_tuple (lv',e',loc)
    Seq (Seq (new_stmt1,new_stmt2), assigns)
  | Decl lv -> stmt
  | Seq (s1,s2) -> Seq (replace_tmpexp_s s1, replace_tmpexp_s s2)

  | Call (lvop,e,pars,_,_,loc,site) when has_value_gas_modifiers_old_solc e ->
    assert (no_eth_gas_modifiers stmt) (* ethop = gasop = None *)
    let ethop = get_valueop e 
    let gasop = get_gasop e 
    let e' = remove_value_gas_modifiers e 
    let (lvop',s1) = replace_tmpexp_lvop lvop 
    let (e'',s2) = replace_tmpexp_e e' 
    Seq (Seq (s1,s2), Call (lvop',e'',pars,ethop,gasop,loc,site))

  | Call (lvop,e,pars,ethop,gasop,loc,site) ->
    let (lvop',s1) = replace_tmpexp_lvop lvop 
    let (e',s2) = replace_tmpexp_e e 
    let (pars',s3) =
      List.fold (fun (acc_params,acc_stmt) par ->
        let (par',s) = replace_tmpexp_e par 
        (acc_params@[par'], Seq (acc_stmt,s))
      ) ([],Skip) pars
    let (ethop',s4) = replace_tmpexp_eop ethop
    let (gasop',s5) = replace_tmpexp_eop gasop 
    Seq (s1, Seq (s2, Seq (s3, Seq (s4, Seq (s5, Call (lvop',e',pars',ethop',gasop',loc,site))))))
  | Skip -> stmt
  | If (e,s1,s2,i) ->
    let (e',new_stmt) = replace_tmpexp_e e 
    Seq (new_stmt, If (e', replace_tmpexp_s s1, replace_tmpexp_s s2, i))
  | While (e,s) ->
    let (e',new_stmt) = replace_tmpexp_e e
    Seq (new_stmt, While (e', Seq(replace_tmpexp_s s,new_stmt)))
  | Break -> stmt
  | Continue -> stmt
  | Return (None,_) -> stmt
  | Return (Some (CallTemp (e,pars,ethop,gasop,einfo)),loc) when is_void einfo.etyp ->
    let s1 = Call (None, e, pars, ethop, gasop, loc, einfo.eid)
    let s2 = Return (None, loc)
    Seq (s1,s2)
  | Return (Some e,loc_ret) ->
    let (e',new_stmt) = replace_tmpexp_e e
    (match e',new_stmt with
     | Lv (Tuple ([],_)), Call (Some (Tuple ([],_)),e,args,ethop,gasop,loc,site) -> (* "return f()"; where f() returns void. *)
       Seq (Call (None,e,args,ethop,gasop,loc,site), Return (None,loc_ret))
     | _ -> Seq (new_stmt, Return (Some e',loc_ret)))
  | Throw -> stmt
  | Assume (e,loc) ->
    let (e',new_stmt) = replace_tmpexp_e e
    Seq (new_stmt, Assume (e',loc))
  | Assert (e,vtyp,loc) ->
    let (e',new_stmt) = replace_tmpexp_e e
    Seq (new_stmt, Assert (e',vtyp,loc))
  | Assembly _ -> stmt
  | PlaceHolder -> stmt
  | Unchecked (lst,loc) ->
    let lst' = List.map replace_tmpexp_s lst
    Unchecked (lst',loc)

let replace_tmpexp_f func =
  let (id, pars, ret_params, stmt, finfo) = func
  (id, pars, ret_params, replace_tmpexp_s stmt, finfo)

let replace_tmpexp_c contract =
  let (id, decls, structs, enums, funcs, cinfo) = contract
  (id, decls, structs, enums, List.map replace_tmpexp_f funcs, cinfo)

let replace_tmpexp_p pgm = List.map replace_tmpexp_c pgm

let rec loop f pgm =
  let pgm' = f pgm
  if not (hastmp pgm') then pgm'
  else loop f pgm'

let replace_tmpexp pgm = loop replace_tmpexp_p pgm

(******************)
(******************)
(** Remove Skips **)
(******************)
(******************)

let rec rmskip_s s =
  match s with
  | Seq (Skip,s) -> rmskip_s s
  | Seq (s,Skip) -> rmskip_s s
  | Seq (s1,s2) -> Seq (rmskip_s s1,rmskip_s s2)
  | If (e,s1,s2,i) -> If (e, rmskip_s s1, rmskip_s s2, i)
  | While (e,s) -> While (e,rmskip_s s)
  | Unchecked (lst,loc) -> Unchecked (List.map rmskip_s lst, loc)
  | _ -> s

let rmskip_f (fid, pars, ret_params, stmt, finfo) = (fid, pars, ret_params, rmskip_s stmt, finfo)
let rmskip_c (cid, decls, structs, enums, funcs, cinfo) = (cid, decls, structs, enums, List.map rmskip_f funcs, cinfo) 
let rmskip_p contracts = List.map rmskip_c contracts
let rmskip p = p |> rmskip_p |> rmskip_p |> rmskip_p

(*******************************)
(*******************************)
(** Normalize many variations **)
(*******************************)
(*******************************)

let rec norm_s ret_params stmt =
  match stmt with
  | Seq (s1,s2) -> Seq (norm_s ret_params s1, norm_s ret_params s2)
  | If (e,s1,s2,i) -> If (e, norm_s ret_params s1, norm_s ret_params s2, i)
  | While (e,s) -> While (e, norm_s ret_params s)
  | Call (lvop,
          Lv (MemberAccess (Lv (IndexAccess _) as arr, fname, fname_info, typ)),
          exps, ethop, gasop, loc, site) ->
    let tmp = gen_tmpvar {Org = Some (Some arr); Loc = None; Typ = (get_type_exp arr); TypeStr = (get_type_exp arr).ToString()}
    let assign = Assign (tmp, arr, loc) 
    let e' = Lv (MemberAccess (Lv tmp, fname, fname_info, typ))
    let call = Call (lvop, e', exps, ethop, gasop, loc, site)
    Seq (assign, call)
  | Return (None,loc) -> stmt
  | Return (Some (Lv (Tuple ([],_))),loc) -> Return (None,loc) (* return (); => return; *)
  | Return (Some (Lv (Var _)), loc) -> stmt
  | Return (Some e,loc) ->
    let lv = params_to_lv ret_params
    let assign = Assign (lv, e, loc)
    let ret_stmt = Return (Some (Lv lv), loc)
    Seq (assign, ret_stmt)
  | _ -> stmt

let norm_f func =
  let ret = get_ret_params func
  let stmt = get_body func
  let stmt' = norm_s ret stmt
  update_body stmt' func

let norm_c (cid, decls, structs, enums, funcs, cinfo) = (cid, decls, structs, enums, List.map norm_f funcs, cinfo) 
let norm_p contracts = List.map norm_c contracts
let normalize p = norm_p p

(***********************************)
(***********************************)
(** Handling Using-for-Directives **)
(***********************************)
(***********************************)

let find_matching_lib_name lib_funcs callee_name arg_typs =
  let matching_func =
    List.find (fun f ->
      let param_typs = get_param_types f
      String.Equals (get_fname f, callee_name) &&
      List.length arg_typs = List.length param_typs && (* should be checked first before checking convertibility *)
      List.forall2 FuncMap.is_implicitly_convertible arg_typs param_typs
    ) lib_funcs
  (get_finfo matching_func).scope_s

let rec ufd_s lst lib_funcs stmt =
  let lib_names = List.map fst lst
  match stmt with
  | Call (lvop,Lv (MemberAccess (e,fname,fname_info,typ)),args,ethop,gasop,loc,site) 
    when List.contains fname (List.map get_fname lib_funcs) (* e.g., (a+b).add(c) when using SafeMath *)
         && not (List.contains (to_string_exp (ToStringArg.SingleExp e)) lib_names) (* e.g., SafeMath.add (a,b) should not be changed. *) -> 
    let e_typ = get_type_exp e
    let lst' = List.filter (fun (_,t) -> t = e_typ || t = Void) lst (* "Void" is for the case of "using libname for *". *)
    let cand_lib_names = List.map fst lst'
    (match List.length cand_lib_names with
     | 0 -> stmt (* no using for syntax *)
     | _ ->
       let arg_typs = List.map get_type_exp (e::args) (* move the receiver to the first argument *)
       let lib_funcs' = List.filter (fun f -> List.contains (get_finfo f).scope_s cand_lib_names) lib_funcs
       let lib_name = find_matching_lib_name lib_funcs' fname arg_typs (* from libs, using fname and arg_typs, find corresponding library name *)
       let lib_typ = Contract lib_name
       let lib_var = Lv (Var (lib_name, mk_vinfo {Loc = None; TypeStr=Some "contract"; Typ = Some lib_typ; Org = None}))
       Call (lvop,Lv (MemberAccess (lib_var,fname,fname_info,typ)),e::args,ethop,gasop,loc,site))
  | Call _ -> stmt 
  | Assign _ -> stmt
  | Decl _ -> stmt
  | Skip -> stmt
  | Seq (s1,s2) -> Seq (ufd_s lst lib_funcs s1, ufd_s lst lib_funcs s2)
  | If (e,s1,s2,i) -> If (e, ufd_s lst lib_funcs s1, ufd_s lst lib_funcs s2, i)
  | While (e,s) -> While (e, ufd_s lst lib_funcs s)
  | Break | Continue | Return _ | Throw 
  | Assume _ | Assert _ | Assembly _ | PlaceHolder -> stmt
  | Unchecked (blk,loc) ->
    let blk' = List.map (ufd_s lst lib_funcs) blk
    Unchecked (blk',loc)

let ufd_f lst lib_funcs (fid, pars, ret_params, stmt, finfo) = (fid, pars, ret_params, ufd_s lst lib_funcs stmt, finfo)

let ufd_c pgm (cid, decls, structs, enums, funcs, cinfo) =
  let lib_names = List.map fst cinfo.lib_typ_lst
  let libs = List.map (find_contract_id pgm) lib_names
  let lib_funcs = List.fold (fun acc lib -> acc @ (get_funcs lib)) [] libs
  (cid, decls, structs, enums, List.map (ufd_f cinfo.lib_typ_lst lib_funcs) funcs, cinfo)

let ufd_p contracts = List.map (ufd_c contracts) contracts
let ufd p = ufd_p p (* abbreviation for using for directives *) 

let prop_libs_c parents c=  (* propagete parents => c *)
  List.fold (fun acc parent ->
    let libs_parent = (get_cinfo parent).lib_typ_lst 
    let acc_info = get_cinfo acc
    let libs' = Set.toList (Set.union (Set.ofList libs_parent) (Set.ofList acc_info.lib_typ_lst))
    update_cinfo {acc_info with lib_typ_lst = libs'} acc 
  ) c parents

let prop_libs_p p =
  List.map (fun c ->
    let nids_of_parents = get_inherit_order c
    let parents = List.tail (List.map (find_contract_nid p) nids_of_parents)
    prop_libs_c parents c 
  ) p

let propagate_libtyp pgm = prop_libs_p pgm

let replace_lib_calls pgm =
  pgm |> propagate_libtyp |> ufd

(****************************************)
(****************************************)
(** Add a prefix (i.e., library name)  **)
(** for the function calls in library. **)
(****************************************)
(****************************************)

(* e.g., https://etherscan.io/address/0x3f354b0c5c5a554fcfcb7bac6b25a104da7a9fce#code *)
let rec add_libname_s lib stmt =
  match stmt with
  | Seq (s1,s2) -> Seq (add_libname_s lib s1, add_libname_s lib s2)  
  | If (e,s1,s2,i) -> If (e, add_libname_s lib s1, add_libname_s lib s2, i)
  | Call (lvop,Lv (Var (v,vinfo)),args,ethop,gasop,loc,site) ->
    let libvar = Lv (Var (lib, mk_vinfo {Loc = None; TypeStr=Some "contract"; Typ = Some (Contract lib); Org = None}))
    Call (lvop, Lv (MemberAccess (libvar, v, vinfo, vinfo.vtyp)), args, ethop, gasop, loc, site)
  | While (e,s) -> While (e, add_libname_s lib s)
  | _ -> stmt 

let add_libname_f lib f =
  let old_stmt = get_body f 
  let new_stmt = add_libname_s lib old_stmt 
  update_body new_stmt f

let add_libname_c c =
  let libname = get_cname c 
  let old_funcs = get_funcs c 
  let new_funcs = List.map (add_libname_f libname) old_funcs 
  update_funcs new_funcs c 

let add_libname_p contracts =
  List.map (fun c ->
    if is_library_kind c then add_libname_c c
    else c
  ) contracts

let add_libname_fcalls_in_lib p = add_libname_p p

(*****************************)
(*****************************)
(** Merge into one contract **)
(*****************************)
(*****************************)

let find_next_contracts : contract list -> id -> contract list= fun lst target ->
  let names = List.map get_cname lst
  let target_idx = match List.tryFindIndex ((=)target) names with Some idx -> idx | None -> failwith "find_next_contracts"
  List.mapi (fun i c -> if i > target_idx then Some c else None) lst |> List.choose id


let add_func f ((cid,decls,structs,enums,funcs,cinfo) as contract) = 
  let b = List.exists (equal_sig f) funcs || (get_finfo f).is_constructor
  (* Do not copy *)
  (* 1. if functions are constructors, and  *)
  (* 2. if functions with the same signatures are already exist in the contract *)
  if b then contract
  else
    let old_finfo = get_finfo f 
    let new_finfo = {old_finfo with scope = cinfo.numid; scope_s = cid} 
    let new_f = update_finfo new_finfo f
    (cid, decls, structs, enums, funcs@[new_f], cinfo)

let add_func2 _from _to =
  let funcs = get_funcs _from 
  List.fold (fun acc f -> add_func f acc) _to funcs

let equal_gdecl (id1,_,_) (id2,_,_) = String.Equals (id1, id2)

let add_decl cand contract =
  let (cid,decls,structs,enums,funcs,cinfo) = contract 
  (cid, decls@[cand], structs, enums, funcs, cinfo)

let add_decl2 _from _to =
  let decls = get_decls _from 
  List.fold (fun acc d -> add_decl d acc ) _to decls

let add_enum _from _to =
  (* Duplicated (i.e., already declared) enums by inheritance will be rejected by solc, so just copy enums. *)
  let enums1 = get_enums _from
  let enums2 = get_enums _to 
  update_enums (enums1 @ enums2) _to

let add_struct _from _to =
  (* Similarly, duplicated (i.e., already declared) structures by inheritance will be rejected by solc, so just copy structures. *)
  let structs1 = get_structs _from 
  let structs2 = get_structs _to
  update_structs (structs1 @ structs2) _to

let add_cnstr_mod_call' _from _to =
  assert (is_constructor _from && is_constructor _to)
  let modcall_from = List.rev (get_finfo _from).mod_list2
  let modcall_to = (get_finfo _to).mod_list2 
  (* duplicated consturctor modifier invocation is error in solc >= 0.5.0,
   * but perform deduplication for compatibility with solc <= 0.4.26 *)
  let modcall_to' =
    List.fold (fun acc m ->
      let b = List.exists (fun (x,_,_) -> x = triple_fst m) acc
      if b then acc else m::acc
    ) modcall_to modcall_from
  let finfo_to = get_finfo _to 
  let finfo_to' = {finfo_to with mod_list2 = modcall_to'}
  update_finfo finfo_to' _to

let add_cnstr_mod_call _from _to =
  let funcs = get_funcs _to 
  let funcs' =
     List.map (fun f ->
       if is_constructor f then add_cnstr_mod_call' (get_cnstr _from) (get_cnstr _to) else f
     ) funcs
  update_funcs funcs' _to

let copy_c parents c =
  let c' =
    List.fold (fun acc parent ->
      acc |> add_func2 parent |> add_decl2 parent |> add_enum parent
          |> add_struct parent |> add_cnstr_mod_call parent
    ) c parents
  (* reorder constructor modifier invocations according to inheritance order *)
  let funcs = get_funcs c'
  let funcs' =
    List.map (fun f ->
      if is_constructor f then
        let finfo = get_finfo f
        let cnstr_mod_calls = finfo.mod_list2
        let cnstr_mod_calls' =
          (* recursive constructor calls are removed, as we iterate over parents. e.g., contract A { constructor (uint n) A (5) ... } *)
          List.fold (fun acc parent ->
            let matching = List.filter (fun (x,_,_) -> get_cname parent = x) cnstr_mod_calls 
            assert (List.length matching = 1 || List.length matching = 0) 
            if List.length matching = 1 then acc @ [List.head matching]
            else acc @ [(get_cname parent, [], dummy_loc)]
          ) [] (List.rev parents) (* reverse to put parent's mod on the front. *)
        let finfo' = {finfo with mod_list2 = cnstr_mod_calls'}
        update_finfo finfo' f
      else f
    ) funcs
  update_funcs funcs' c'



let rec rs_s family cur_cname stmt =
  match stmt with
  | Assign _ -> stmt
  | Decl _ -> stmt
  | Seq (s1,s2) -> Seq (rs_s family cur_cname s1, rs_s family cur_cname s2)
  | Call (lvop, Lv (MemberAccess (Lv (Var (x,xinfo)),id,id_info,typ)), args, ethop, gasop, loc, site)
    when String.Equals (x, "super") ->
    let arg_typs = List.map get_type_exp args
    let supers = find_next_contracts family cur_cname
    let matched_parent =
      List.find (fun super ->
        let funcs = get_funcs super
        List.exists (fun f ->
          let (id',typs') = get_fsig f
          if String.Equals (id, id') && List.length arg_typs = List.length typs' then
            List.forall2 FuncMap.is_implicitly_convertible arg_typs typs'
          else false 
        ) funcs 
      ) supers 
    let matched_parent_name = get_cname matched_parent
    Call (lvop, Lv (MemberAccess (Lv (Var (matched_parent_name,xinfo)),id,id_info,typ)), args, ethop, gasop, loc, site)
  | Call _ -> stmt
  | Skip -> stmt
  | If (e,s1,s2,i) -> If (e, rs_s family cur_cname s1, rs_s family cur_cname s2, i)
  | While (e,s) -> While (e, rs_s family cur_cname s)
  | _ -> stmt

let rs_f final_inherit cur_cname f =
  let old_body = get_body f 
  let new_body = rs_s final_inherit cur_cname old_body 
  update_body new_body f

let rs_c final_inherit c =
  let cur_cname = get_cname c
  let old_funcs = get_funcs c
  let new_funcs = List.map (rs_f final_inherit cur_cname) old_funcs
  update_funcs new_funcs c 

let rs_p pgm  =
  let main = get_main_contract pgm
  let nids_of_parents = get_inherit_order main
  let final_inherit = List.map (find_contract_nid pgm) nids_of_parents 
  let family_names = List.map get_cname final_inherit
  List.fold (fun acc c ->
    if List.contains (get_cname c) family_names then
      let c' = rs_c final_inherit c 
      modify_contract c' acc
    else acc
  ) pgm pgm

let replace_super pgm = rs_p pgm 

(**********************)
(**********************)
(** Generate getters **)
(**********************)
(**********************)

let get_public_state_vars c =
  let decls = get_decls c 
  let decls' = List.filter (fun (_,_,vinfo) -> vinfo.vvis = Public) decls 
  List.map (fun (v,_,vinfo) -> (v,vinfo)) decls'


(******************************)
(******************************)
(** Inline Constructor Calls **)
(******************************)
(******************************)

let rec has_cnstr_calls_s cnstrs stmt =
  match stmt with
  | Assign _ -> false
  | Seq (s1,s2) -> has_cnstr_calls_s cnstrs s1 || has_cnstr_calls_s cnstrs s2
  | Decl _ -> false
  | Call (None,Lv (Var (f,_)),_,_,_,_,_) when List.contains f (List.map get_fname cnstrs) -> true
  | Call _ -> false
  | Skip -> false
  | Assume _ -> false
  | While (_,s) -> has_cnstr_calls_s cnstrs s
  | If (_,s1,s2,_) -> has_cnstr_calls_s cnstrs s1 || has_cnstr_calls_s cnstrs s2
  | Continue | Break | Return _ | Throw | Assert _ | Assembly _ | PlaceHolder -> false
  | Unchecked (slst,_) -> List.exists (has_cnstr_calls_s cnstrs) slst

let has_cnstr_calls_f cnstrs f =
  if is_constructor f then
    has_cnstr_calls_s cnstrs (get_body f)
  else false

let has_cnstr_calls_c cnstrs c = List.exists (has_cnstr_calls_f cnstrs) (get_funcs c)
let has_cnstr_calls_p p = 
  let cnstrs = List.map get_cnstr p 
  List.exists (has_cnstr_calls_c cnstrs) p
let has_cnstr_calls p = has_cnstr_calls_p p

let bind_params loc pars args =
  try
    List.fold2 (fun acc (x,xinfo) arg -> 
      Seq (acc, Assign (Var (x,xinfo), arg, loc))
    ) Skip pars args
  with | :? System.ArgumentException -> Skip

let rec replace_ph mod_body body =
  match mod_body with
  | PlaceHolder -> body
  | Seq (s1,s2) -> Seq (replace_ph s1 body, replace_ph s2 body)
  | While (e,s) -> While (e, replace_ph s body)
  | If(e,s1,s2,i) -> If (e, replace_ph s1 body, replace_ph s2 body, i)
  | _ -> mod_body

let inline_mod_calls_f funcs f =
  let body = get_body f 
  let mods = List.rev (get_finfo f).mod_list
  let body' =
    List.fold(fun acc m ->
      let mod_def = List.find (fun f -> get_fname f = triple_fst m) funcs 
      let binding = bind_params (triple_third m) (get_params mod_def) (triple_snd m)
      let mod_body = get_body mod_def
      Seq (binding, replace_ph mod_body acc)
    ) body mods
  update_body body' f

let inline_cnstr_calls_f cnstrs f =
  if not (is_constructor f) then
    assert (List.length ((get_finfo f).mod_list2) = 0)
    f
  else
    let body = get_body f
    let mods = List.rev (get_finfo f).mod_list2
    let body' =
      List.fold (fun acc m ->
        let cnstr = List.find (fun f -> get_fname f = triple_fst m) cnstrs
        let binding = bind_params (triple_third m) (get_params cnstr) (triple_snd m)
        let cbody = get_body cnstr 
        Seq (Seq (binding, cbody), acc)
      ) body mods
    update_body body' f

let inline_mods_c cnstrs c =
  let funcs = get_funcs c
  let funcs' = List.map (inline_mod_calls_f funcs) funcs 
  let funcs'' = List.map (inline_cnstr_calls_f cnstrs) funcs'
  update_funcs funcs'' c

let inline_mod_calls pgm =
  let cnstrs = List.map get_cnstr pgm
  List.map (inline_mods_c cnstrs) pgm

(************************************)
(************************************)
(** return variable initialization **)
(************************************)
(************************************)

let add_retvar_init_f f =
  let ret_params = get_ret_params f
  let new_stmt =
    List.fold (fun acc (x,xinfo) ->
      let s = Decl (Var (x,xinfo))
      if is_skip acc then s
      else Seq (acc,s)
    ) Skip ret_params
  let body = get_body f
  let new_body = if is_skip new_stmt then body else Seq (new_stmt,body)
  update_body new_body f  

let add_retvar_init_c c =
  let funcs = get_funcs c
  let funcs = List.map add_retvar_init_f funcs
  update_funcs funcs c

let add_retvar_init_p contracts =
  List.map (fun c ->
   if String.Equals ((get_cinfo c).ckind, "library") then c (* for optimization, do not introduce additional stmt for lib functions. *)
   else add_retvar_init_c c
  ) contracts 

let add_retvar_init p = add_retvar_init_p p


(*******************************)
(*******************************)
(*** return stmt at the exit ***)
(*******************************)
(*******************************)

let mutable id = 0
let newid() = 
  id <- id + 1
  id


let add_ret_s f s =
  try
    let lv = params_to_lv (get_ret_params f)
    Seq (s, Return (Some (Lv lv), dummy_loc))
  with
    NoParameters -> Seq (s, Return (None, dummy_loc))

let add_ret_f f = update_body (add_ret_s f (get_body f)) f
let add_ret_c c = update_funcs (List.map (add_ret_f) (get_funcs c)) c
let add_ret pgm = List.map add_ret_c pgm

(***********************)
(***********************)
(** Variable Renaming **)
(***********************)
(***********************)

let do_not_rename (id: string,vinfo) =
  id.StartsWith tmpvar
  || id.StartsWith Translator.param_name (* ghost ret param names are already unique *)
  || vinfo.refid = -1 (* some built-in variables do not have reference id, thus we assign '-1' *)

let rec rename_lv enums lv =
  match lv with
  | Var (id,vinfo) ->
    if do_not_rename (id,vinfo) then lv
    else Var (id (*+ separator + (string vinfo.refid)*), vinfo)
  | MemberAccess (Lv (Var (x,xt)),id,id_info,typ)
    when is_enum typ && List.contains x (List.map fst enums) ->
    let assoc key lst =
      match List.tryFind (fun (k, _) -> k = key) lst with
      | Some (_, v) -> v
      | None -> failwith "Key not found"
    let members = assoc x enums
    let idx = remove_some (List.tryFindIndex ((=) id) members)
    MemberAccess (Lv (Var (x,xt)),id + "__idx" + (string idx), id_info,typ)
  | MemberAccess (Lv (MemberAccess (e,fname,finfo,typ1)),"selector",sinfo,typ2) ->
    MemberAccess (Lv (MemberAccess (rename_e enums e,fname,finfo,typ1)),"selector",sinfo,typ2)
  | MemberAccess (e,id,id_info,typ) ->
    let id' =
      if do_not_rename (id,id_info) then id
      else id(* + separator + (string id_info.refid) *)
    MemberAccess (rename_e enums e, id', id_info, typ)
  | IndexAccess (e,None,_) -> raise (Failure "rename_lv enums1")
  | IndexAccess (e1,Some e2,typ) -> IndexAccess (rename_e enums e1, Some (rename_e enums e2), typ)
  | Tuple (eoplst,typ) ->
    let eoplst' = 
      List.map (fun eop ->
        match eop with
        | None -> None
        | Some e -> Some (rename_e enums e)
      ) eoplst
    Tuple (eoplst',typ)

and rename_e enums exp =
  match exp with
  | Int _ | Real _ | Str _ -> exp
  | Lv lv ->
    if List.contains (to_string_lv (ToStringArg.Singlelv lv)) Lang.keyword_vars then Lv lv
    else Lv (rename_lv enums lv)
  | Cast (typ,e) -> Cast (typ,rename_e enums e)
  | BinOp (bop,e1,e2,einfo) -> BinOp (bop, rename_e enums e1, rename_e enums e2, einfo)
  | UnOp (uop,e,typ) -> UnOp (uop, rename_e enums e, typ)
  | True | False | ETypeName _ -> exp
  | IncTemp _ | DecTemp _ -> failwith "rename_e enums1"
  | CallTemp (_,_,_,_,einfo) -> failwith ("rename_e enums2: " + to_string_exp (ToStringArg.SingleExp exp) + "@" + (string einfo.eloc.line))
  | CondTemp (_,_,_,_,loc) -> failwith ("rename_e enums3: " + to_string_exp (ToStringArg.SingleExp exp) + "@" + (string loc.line))
  | AssignTemp (_,_,loc) -> failwith ("rename_e enums4: " + to_string_exp (ToStringArg.SingleExp exp) + "@" + (string loc.line))

let rec rename_s cnames enums stmt =
  match stmt with
  | Assign (lv,exp,loc) -> Assign (rename_lv enums lv, rename_e enums exp, loc)
  | Decl lv -> Decl (rename_lv enums lv)
  | Seq (s1,s2) -> Seq (rename_s cnames enums s1, rename_s cnames enums s2)
  | Call (lvop, e, exps, ethop, gasop, loc, site) ->
    let lvop' =
      (match lvop with
       | None -> lvop
       | Some lv -> Some (rename_lv enums lv))
    let e' =
      (match e with
       | e when List.contains (to_string_exp (ToStringArg.SingleExp e)) built_in_funcs -> e
       | Lv (Var (fname,info)) -> e
       | Lv (MemberAccess (Lv (Var (prefix,prefix_info)) as arr, fname, fname_info, typ)) ->
         if List.contains prefix cnames || String.Equals (prefix, "super") then e
         else Lv (MemberAccess (rename_e enums arr, fname, fname_info, typ))
       | _ -> e (* raise (Failure ("rename_s (preprocess.ml) : unexpected fname syntax - " ^ (to_string_stmt stmt))) *)) 
    let exps' =
      if to_string_exp (ToStringArg.SingleExp e) = "struct_init" (* Rule: the first arg is struct name *)
         || to_string_exp (ToStringArg.SingleExp e) = "struct_init2"
        then (List.head exps)::(List.map (rename_e enums) (List.tail exps))
      else List.map (rename_e enums) exps
    let ethop' = match ethop with None -> ethop | Some e -> Some (rename_e enums e) 
    let gasop' = match gasop with None -> gasop | Some e -> Some (rename_e enums e)
    Call (lvop', e', exps', ethop', gasop', loc, site)
  | Skip -> Skip
  | If (e,s1,s2,i) -> If (rename_e enums e, rename_s cnames enums s1, rename_s cnames enums s2, i)
  | While (e,s) -> While (rename_e enums e, rename_s cnames enums s)
  | Break | Continue | Return (None,_) -> stmt
  | Return (Some e,loc) -> Return (Some (rename_e enums e), loc)
  | Throw -> Throw
  | Assume (e,loc) -> Assume (rename_e enums e, loc)
  | Assert (e,vtyp,loc) -> Assert (rename_e enums e, vtyp, loc)
  | Assembly (lst,loc) ->
    Assembly (List.map (fun (x,refid) -> (x (*+  separator + (string refid)*), refid)) lst, loc)
  | PlaceHolder -> PlaceHolder
  | Unchecked (slst,loc) ->
    let slst' = List.map (rename_s cnames enums) slst
    Unchecked (slst',loc)

let rename_param (id, vinfo) =
  if (string id).StartsWith Translator.param_name then (id,vinfo)
  else (id (*+ separator + (string vinfo.refid)*), vinfo)

let rename_f cnames enums (fid, pars, ret_params, stmt, finfo) =
  (fid, List.map rename_param pars, List.map rename_param ret_params, rename_s cnames enums stmt, finfo)

let rename_d decl =
  match decl with
  | (id,None,vinfo) -> (id (*+ separator + (string vinfo.refid)*), None, vinfo)
  | (id,Some e,vinfo) -> (id (*+ separator + (string vinfo.refid)*), Some e, vinfo)

let rename_st (sname, members) =
  let members' = List.map (fun (v,vinfo) -> (v (*+ separator + (string vinfo.refid)*), vinfo)) members
  (sname, members')

let rename_c cnames (cid, decls, structs, enums, funcs, cinfo) =
  (cid, List.map rename_d decls, List.map rename_st structs, enums, List.map (rename_f cnames enums) funcs, cinfo)

let rename_p p =
  let cnames = get_cnames p
  List.map (rename_c cnames) p

let rename pgm = rename_p pgm

let tuple_assign lv exp loc =
  match lv, exp with
  | Tuple (eops1, typ1), Lv (Tuple (eops2, _)) when List.length eops1 <> List.length eops2 ->
    match List.head eops1 with
    | Some _ ->
      let (eops1' , _) = list_fold (fun e (acc, acc_index) -> 
        if acc_index = 0 then (acc@[None], acc_index) else (acc, acc_index - 1) ) eops2 (eops1, List.length eops1)
      Assign (Tuple (eops1', typ1), exp, loc)
    | None ->
      let eops1' = List.tail eops1
      let (eops1'', _) = list_fold (fun e (acc, acc_index) ->
        if acc_index = 0 then (acc, acc_index) else (None::acc, acc_index - 1)) eops2 (eops1', (List.length eops2) - (List.length eops1'))
      Assign (Tuple (eops1'', typ1), exp, loc)

    (* (bool success, ) = recipient.call.value(amountToWithdraw)("");
     * => (succcess, ) := Tmp
     * => success := Tmp *)
  | Tuple ([Some (Lv lv1);None],_), Lv lv2 -> Assign (lv1, Lv lv2, loc)
  | _ -> Assign (lv, exp, loc)

let rec tuple_s stmt =
  match stmt with
  | Assign (lv,exp,loc) -> tuple_assign lv exp loc
  | Decl (Tuple (eops,_)) ->
    List.fold (fun acc eop ->
      match eop with
      | None -> acc
      | Some (Lv lv) -> Seq (acc, Decl lv)
      | Some _ -> assert false; failwith "tuple_s"
    ) Skip eops
  | Seq (s1,s2) -> Seq (tuple_s s1, tuple_s s2) 
  | If (e,s1,s2,i) -> If (e, tuple_s s1, tuple_s s2, i)
  | While (e,s) -> While (e, tuple_s s)
  | _ -> stmt

let tuple_f f = update_body (tuple_s (get_body f)) f
let tuple_c c = update_funcs (List.map tuple_f (get_funcs c)) c

let extend_tuple pgm = List.map tuple_c pgm

(*************)
(*************)
(** Casting **)
(*************)
(*************)

let rec cast_lv lv =
  match lv with
  | Var _ -> lv
  | MemberAccess (e,x,xinfo,typ) -> MemberAccess (cast_e e, x, xinfo, typ)
  | IndexAccess (e,None,typ) -> IndexAccess (cast_e e, None, typ)
  | IndexAccess (e1,Some e2,typ) ->
    let expected_idx_typ = domain_typ (get_type_exp e1)
    let idx_typ = get_type_exp e2
    let e1' = cast_e e1
    let e2' = if expected_idx_typ = idx_typ then cast_e e2 else Cast (expected_idx_typ, cast_e e2)
    IndexAccess (e1', Some e2', typ)
  | Tuple (eoplst,typ) ->
    let eoplst' = List.map (fun eop -> match eop with Some e -> Some (cast_e e) | None -> None) eoplst
    Tuple (eoplst',typ)

and cast_e exp =
  match exp with
  | Int _ | Real _ | Str _ -> exp
  | Lv lv -> Lv (cast_lv lv)
  | Cast (typ,e) -> Cast (typ, cast_e e)
  | BinOp (bop,e1,e2,einfo) ->
    let t1 = get_type_exp e1
    let t2 = get_type_exp e2
    let ctyp = common_typ e1 e2
    let e1' = if t1 = ctyp then cast_e e1 else Cast (ctyp, cast_e e1)
    let e2' = if t2 = ctyp then cast_e e2 else Cast (ctyp, cast_e e2)
    BinOp (bop, e1', e2', einfo)
  | UnOp (uop,e,typ) -> UnOp (uop, cast_e e, typ)
  | True | False -> exp 
  | ETypeName _ -> exp
  | IncTemp _ | DecTemp _ | CallTemp _
  | CondTemp _ | AssignTemp _ -> failwith "cast_e" 

and cast_s stmt =
  match stmt with
  | Assign (lv,e,loc) ->
    let lv_typ = get_type_lv lv
    let e_typ = get_type_exp e
    let lv' = cast_lv lv
    let e' = if lv_typ = e_typ then cast_e e else Cast (lv_typ, cast_e e)
    Assign (lv', e', loc)
  | Decl lv -> stmt
  | Seq (s1,s2) -> Seq (cast_s s1, cast_s s2)
  | Call (lvop,e,elst,ethop,gasop,loc,site) ->
    let lvop' = match lvop with Some lv -> Some (cast_lv lv) | None -> None
    let e' = cast_e e
    let elst' = List.map cast_e elst
    let ethop' = match ethop with Some e -> Some (cast_e e) | None -> None
    let gasop' = match gasop with Some e -> Some (cast_e e) | None -> None
    Call (lvop', e', elst', ethop', gasop', loc, site)
  | Skip -> stmt
  | If (e1,s1,s2,i) -> If (cast_e e1, cast_s s1, cast_s s2, i)
  | While (e,s) -> While (cast_e e, cast_s s)
  | Break | Continue -> stmt
  | Return _ | Throw -> stmt
  | Assume (e,loc) -> Assume (cast_e e, loc) 
  | Assert (e,vtyp,loc) -> Assert (cast_e e, vtyp, loc)
  | Assembly _ | PlaceHolder -> stmt
  | Unchecked (slst,loc) -> Unchecked (List.map cast_s slst, loc)

let cast_f f = update_body (cast_s (get_body f)) f
let cast_c c = update_funcs (List.map cast_f (get_funcs c)) c

let cast pgm = List.map cast_c pgm

(***************************************************************)
(**** Add guards for arithmetic operations (solv >= 0.8.0), ****)
(**** division (non-zero), array access (length > 0)        ****)
(***************************************************************)

(* Reference for division: https://github.com/Z3Prover/z3/issues/2843 *)
type Add_io_dz_e_arg = {
  String: string option
  Exp: exp}

type Add_io_dz_lv_arg = {
  String: string option
  Lv: lv
}

let rec add_io_dz_e {String = mode; Exp = exp} =
  let mode = defaultArg mode "all"
  assert (mode = "all" || mode = "io" || mode = "dz") 
  match exp with
  | Int _ | Real _ | Str _ -> []
  | Lv lv -> add_io_dz_lv {String = Some mode; Lv = lv}
  | Cast (_,e) -> add_io_dz_e {String = Some mode; Exp = e}
  | BinOp (Add,e1,e2,einfo)
    when Options.solc_ver.StartsWith "0.8" && (mode ="all" || mode = "io") -> 
    (mk_ge (mk_add e1 e2) e1, einfo.eloc) :: ((add_io_dz_e {String = Some mode; Exp = e1}) @ (add_io_dz_e {String = Some mode; Exp = e2}))

  | BinOp (Sub,e1,e2,einfo)
    when Options.solc_ver.StartsWith "0.8" && (mode ="all" || mode = "io") ->
    (mk_ge e1 e2, einfo.eloc) :: ((add_io_dz_e {String = Some mode; Exp = e1}) @ (add_io_dz_e {String = Some mode; Exp = e2}))

  | BinOp (Mul,e1,e2,einfo)
    when Options.solc_ver.StartsWith "0.8" && (mode ="all" || mode = "io") ->
    let zero = mk_eq e1 (Int (BigInteger 0))
    let not_zero = mk_neq e1 (Int (BigInteger 0))
    let mul_div = mk_div exp e1
    (mk_or zero (mk_and not_zero (mk_eq mul_div e2)), einfo.eloc) :: ((add_io_dz_e {String = Some mode; Exp = e1}) @ (add_io_dz_e {String = Some mode; Exp = e2}))

  | BinOp (Div,e1,e2,einfo) when (mode ="all" || mode = "dz") ->
    (mk_neq e2 (Int (BigInteger 0)), einfo.eloc) :: ((add_io_dz_e {String = Some mode; Exp = e1}) @ (add_io_dz_e {String = Some mode; Exp = e2}))

  | BinOp (_,e1,e2,_) -> (add_io_dz_e {String = Some mode; Exp = e1}) @ (add_io_dz_e {String = Some mode; Exp = e2})
  | UnOp (_,e,_) -> add_io_dz_e {String = Some mode; Exp = e}
  | True | False | ETypeName _ -> []
  | IncTemp _ | DecTemp _ | CallTemp _
  | CondTemp _ | AssignTemp _ -> failwith "add_io_dz_e"

and add_io_dz_lv {String = mode; Lv = lv} =
  let mode = defaultArg mode "all"
  assert (mode = "all" || mode = "io" || mode = "dz")
  match lv with
  | Var _ -> []
  | MemberAccess (e,_,_,_) -> add_io_dz_e {String = Some mode; Exp = e}
  | IndexAccess (e,None,t) -> add_io_dz_e {String = Some mode; Exp = e}
  | IndexAccess (e1,Some e2,t) -> (add_io_dz_e {String = Some mode; Exp = e1}) @ (add_io_dz_e {String = Some mode; Exp = e2})
  | Tuple (eops,_) ->
    List.fold (fun acc eop ->
      match eop with
      | None -> acc
      | Some e -> acc @ (add_io_dz_e {String = Some mode; Exp = e})
    ) [] eops

(* vaa: valid array access  *)
(* E.g., arr[i] => arr.length > i *)
let rec add_vaa_e exp =
  match exp with
  | Int _ | Real _ | Str _ -> []
  | Lv lv -> add_vaa_lv lv
  | Cast (_,e) -> add_vaa_e e
  | BinOp (_,e1,e2,_) -> (add_vaa_e e1) @ (add_vaa_e e2)
  | UnOp (_,e,_) -> add_vaa_e e
  | True | False | ETypeName _ -> []
  | IncTemp _ | DecTemp _ | CallTemp _
  | CondTemp _ | AssignTemp _ -> failwith "add_vaa_e"

and add_vaa_lv lv =
  match lv with
  | Var _ -> []
  | MemberAccess (e,_,_,_) -> add_vaa_e e
  | IndexAccess (e,None,t) -> add_vaa_e e
  | IndexAccess (e1,Some e2,t) ->
    if is_array (get_type_exp e1) then
      ((mk_gt (mk_member_access e1 ("length", EType (UInt 256))) e2), dummy_loc)
      ::((add_vaa_e e1) @ (add_vaa_e e2))
    else
      (add_vaa_e e1) @ (add_vaa_e e2)
  | Tuple (eops,_) ->
    List.fold (fun acc eop ->
      match eop with
      | None -> acc
      | Some e -> acc @ (add_vaa_e e)
    ) [] eops

let rec add_assert stmt =
  let mode = "io" 
  let vultyp = "io"
  match stmt with
  | Assign (lv,e,loc) ->
    let lst = (add_io_dz_lv {String = Some mode; Lv = lv}) @ (add_io_dz_e {String = Some mode; Exp = e})
    List.fold (fun acc (x,l) -> Seq (Assert (x, vultyp, l), acc)) stmt lst
  | Decl lv -> stmt
  | Seq (s1,s2) -> Seq (add_assert s1, add_assert s2)
  | Call (lvop,e,args,ethop,gasop,loc,site) ->
    let lvop_lst = match lvop with None -> [] | Some lv -> (add_io_dz_lv {String = Some mode; Lv = lv}) 
    let e_lst = (add_io_dz_e {String = Some mode; Exp = e})
    let args_lst = List.fold (fun acc e' -> acc @ (add_io_dz_e {String = Some mode; Exp = e})) [] args 
    let ethop_lst = match ethop with None -> [] | Some e -> (add_io_dz_e {String = Some mode; Exp = e})
    let gasop_lst = match gasop with None -> [] | Some e -> (add_io_dz_e {String = Some mode; Exp = e})
    let lst = lvop_lst @ e_lst @ args_lst @ ethop_lst @ gasop_lst
    List.fold (fun acc (x,l) -> Seq (Assert (x, vultyp, l), acc)) stmt lst
  | Skip -> stmt

  | If (e,s1,s2,i) ->
    let lst = add_io_dz_e {String = Some mode; Exp = e}
    if List.length lst = 0 then
      If (e, add_assert s1, add_assert s2, i)
    else
      let s' = List.fold (fun acc (x,l) -> Seq (Assert (x, vultyp, l), acc)) Skip lst
      Seq (s', If (e, add_assert s1, add_assert s2, i))

  | While (e,s) ->
    let lst = add_io_dz_e {String = Some mode; Exp = e}
    if List.length lst = 0 then
      While (e, add_assert s)
    else
      let s' = List.fold (fun acc (x,l) -> Seq (Assert (x, vultyp, l), acc)) Skip lst
      Seq (s', While (e, add_assert s))

  | Break | Continue -> stmt
  | Return (None,_) -> stmt
  | Return (Some e,_) ->
    let lst = add_io_dz_e {String = Some mode; Exp = e}
    List.fold (fun acc (x,l) -> Seq (Assert (x, vultyp, l), acc)) stmt lst
  | Throw -> stmt
  | Assume (e,loc) ->
    let lst = add_io_dz_e {String = Some mode; Exp = e}
    List.fold (fun acc (x,l) -> Seq (Assert (x, vultyp, l), acc)) stmt lst
  | Assert (e,"default",loc) ->
    let lst = add_io_dz_e {String = Some mode; Exp = e}
    List.fold (fun acc (x,l) -> Seq (Assert (x, vultyp, l), acc)) stmt lst
  | Assert (e,_,loc) -> stmt (* automatically inserted assertion *)
  | Assembly _ | PlaceHolder -> stmt
  | Unchecked (slst,loc) -> failwith "add_assert"

type Add_assume_s_arg = {
  String: string option
  Stmt: stmt
}
let rec add_assume_s {String = mode; Stmt = stmt} =
  let mode = defaultArg mode "all"
  assert (mode = "all" || mode = "io" || mode = "dz") 
  match stmt with
  | Assign (lv,e,loc) ->
    let lst = (add_io_dz_lv {String = Some mode; Lv = lv}) @ (add_io_dz_e {String = Some mode; Exp = e}) @ (add_vaa_lv lv) @ (add_vaa_e e)
    List.fold (fun acc (x,_) -> Seq (acc, Assume (x, dummy_loc))) stmt lst
  | Decl lv -> stmt
  | Seq (s1,s2) -> Seq (add_assume_s {String = Some mode; Stmt = s1}, add_assume_s {String = Some mode; Stmt = s2})
  | Call (lvop,e,args,ethop,gasop,loc,site) ->
    let lvop_lst = match lvop with None -> [] | Some lv -> (add_io_dz_lv {String = Some mode; Lv = lv}) @ (add_vaa_lv lv)
    let e_lst = (add_io_dz_e {String = Some mode; Exp = e}) @ (add_vaa_e e)
    let args_lst = List.fold (fun acc e' -> acc @ (add_io_dz_e {String = Some mode; Exp = e}) @ (add_vaa_e e')) [] args
    let ethop_lst = match ethop with None -> [] | Some e -> (add_io_dz_e {String = Some mode; Exp = e})@ (add_vaa_e e)
    let gasop_lst = match gasop with None -> [] | Some e -> (add_io_dz_e {String = Some mode; Exp = e}) @ (add_vaa_e e)
    let lst = lvop_lst @ e_lst @ args_lst @ ethop_lst @ gasop_lst
    List.fold (fun acc (x,_) -> Seq (acc, Assume (x, dummy_loc))) stmt lst
  | Skip -> stmt

  | If (e,s1,s2,i) ->
    let lst = (add_io_dz_e {String = Some mode; Exp = e}) @ (add_vaa_e e)
    if List.length lst = 0 then (* just for readability of IL *)
      If (e, add_assume_s {String = Some mode; Stmt = s1}, add_assume_s {String = Some mode; Stmt = s2}, i)
    else
      let s' = List.fold (fun acc (x,_) -> Seq (acc, Assume (x, dummy_loc))) Skip lst 
      If (e, Seq (s', add_assume_s {String = Some mode; Stmt = s1}), Seq (s', add_assume_s {String = Some mode; Stmt = s2}), i)

  | While (e,s) ->
    let lst = (add_io_dz_e{String = Some mode; Exp = e}) @ (add_vaa_e e)
    if List.length lst = 0 then (* just for readability of IL *)
      While (e, add_assume_s {String = Some mode; Stmt = s})
    else
      let s' = List.fold (fun acc (x,_) -> Seq (acc, Assume (x, dummy_loc))) Skip lst 
      Seq (While (e, Seq (s', add_assume_s {String = Some mode; Stmt = s})), s')

  | Break | Continue -> stmt
  | Return _ | Throw -> stmt
  | Assume (e,loc) ->
    let lst = (add_io_dz_e {String = Some mode; Exp = e}) @ (add_vaa_e e)
    List.fold (fun acc (x,_) -> Seq (acc, Assume (x, dummy_loc))) stmt lst
  | Assert (e,"default",loc) ->
    let lst = (add_io_dz_e {String = Some mode; Exp = e}) @ (add_vaa_e e)
    List.fold (fun acc (x,_) -> Seq (acc, Assume (x, dummy_loc))) stmt lst
  | Assert (e,_,loc) -> stmt (* automatically inserted assertion *)
  | Assembly _ | PlaceHolder -> stmt
  | Unchecked (slst,loc) ->
    let rec inner slst = 
      match slst with
      | [] -> []
      | hd::tl -> add_assume_s{String = Some "dz"; Stmt = hd} :: inner tl
    let slst = inner slst |> List.map add_assert
    List.fold (fun acc s -> if is_skip acc then s else Seq (acc,s)) Skip slst

let add_assume_f f = update_body (add_assume_s {String = None; Stmt = (get_body f)}) f
let add_assume_c c = update_funcs (List.map add_assume_f (get_funcs c)) c
let add_assume pgm = List.map add_assume_c pgm

(*****************************)
(**** Desugar struct_init ****)
(*****************************)

let rec fold_left2 lv loc (acc: stmt) members values =
  match members, values with
  | [], [] -> acc
  | [], h2::t2 -> invalidArg "preprocess" "desugar struct init" 
  | h1::t1, [] ->
    if is_mapping (get_type_var2 h1) then
      let lv' = MemberAccess (Lv lv, fst h1, snd h1, get_type_var2 h1)
      let stmt' = Decl lv'
      let stmt'' = if is_skip acc then stmt' else Seq (acc,stmt')
      fold_left2 lv loc stmt'' t1 []
    else invalidArg "preprocess" "desugar struct init" 
  | h1::t1, h2::t2 ->
    if is_mapping (get_type_var2 h1) then
      let lv' = MemberAccess (Lv lv, fst h1, snd h1, get_type_var2 h1)
      let stmt' = Decl lv'
      let stmt'' = if is_skip acc then stmt' else Seq (acc,stmt')
      fold_left2 lv loc stmt'' t1 (h2::t2)
    else
      let lv' = MemberAccess (Lv lv, fst h1, snd h1, get_type_var2 h1)
      let stmt' = Assign (lv', h2, loc)
      let stmt'' = if is_skip acc then stmt' else Seq (acc,stmt')
      fold_left2 lv loc stmt'' t1 t2

let rec dsg cname smap stmt =
  match stmt with
  | Assign _ | Decl _ -> stmt
  | Seq (s1,s2) -> Seq (dsg cname smap s1, dsg cname smap s2)
  | Call (Some lv, Lv (Var ("struct_init",_)), args, ethop, gasop, loc, site) ->
    let (struct_exp, member_values) = (List.head args, List.tail args)
    (* Types of type-name-expressions are their type-names. E.g., typeOf (StructName) => ContractName.StructName *)
    (* see the implementation in frontend/translator.ml *)
    let members = StructMap.find (get_name_userdef (get_type_exp struct_exp)) smap
    fold_left2 lv loc Skip members member_values
  | Call (Some lv, Lv (Var ("struct_init2",_)), args,ethop, gasop, loc, site) ->
    let (args1, args2) = List.splitAt ((List.length args / 2) + 1) args
    let (struct_exp, member_names, member_values) = (List.head args1, List.tail args1, args2)
    let org_members = StructMap.find (get_name_userdef (get_type_exp struct_exp)) smap
    let find_matching_member mname member_lst = List.find (fun (name',_) -> (string name').StartsWith (to_string_exp mname)) member_lst
    let members = List.map (fun name -> ToStringArg.SingleExp name) member_names |> List.map (fun name -> find_matching_member name org_members)
    fold_left2 lv loc Skip members member_values
  | Call _ -> stmt
  | Skip -> stmt
  | If (e,s1,s2,i) -> If (e, dsg cname smap s1, dsg cname smap s2, i)
  | While (e,s) -> While (e, dsg cname smap s)
  | Break | Continue -> stmt
  | Return _ | Throw -> stmt
  | Assume _ | Assert _ | Assembly _ | PlaceHolder -> stmt
  | Unchecked (lst,loc) ->
    let lst' = List.map (dsg cname smap) lst
    List.fold (fun acc s -> if is_skip acc then s else Seq (acc,s)) Skip lst'

let desugar_struct_f cname smap f = update_body (dsg cname smap (get_body f)) f

let desugar_struct_c smap c =
  let cname = get_cname c
  update_funcs (List.map (desugar_struct_f cname smap) (get_funcs c)) c

let desugar_struct pgm =
  let smap = StructMap.mk_smap pgm
  List.map (desugar_struct_c smap) pgm

let copy_p pgm =
  List.fold(fun acc c ->
    (* when copying contracts to some contracts, consider parents in the original program. *)
    (* let bases = Global.get_full_base_contracts p c in *)
    let base_names_of_main = List.map get_cname (Global.get_full_base_contracts pgm (get_main_contract pgm))
    if not (List.contains (get_cname c) base_names_of_main) then
      let bases = Global.get_full_base_contracts pgm c 
      let parents = find_next_contracts  bases (get_cname c)
      let c' = copy_c parents c
      let acc' = modify_contract c' acc
      acc'
    else
      let bases = Global.get_full_base_contracts pgm (get_main_contract pgm)
      let parents = find_next_contracts bases (get_cname c)
      let c' = copy_c parents c
      let acc' = modify_contract c' acc
      acc'
  ) pgm pgm

let copy pgm = copy_p pgm

let call_extern rcv loc =
    Call (None, Lv (Var ("@extern", dummy_vinfo)), [rcv], None, None, loc, -1)

let is_pseudo_stmt_node : node -> cfg -> bool = fun n g ->
    let stmt = find_stmt n g 
    match stmt with
    | Assign (lv,e,_) ->
        Set.exists (fun x -> let (s : string) = fst x in s.StartsWith("@")) (Set.union (var_lv lv) (var_exp e))
    | Assume (e,_) ->
        Set.exists (fun x -> let (s : string) = fst x in s.StartsWith("@")) (var_exp e)
    | _ -> false 

(**************************************************)
(*** Desugar built-in functions that send money ***)
(**************************************************)

let rec convert_call_s : id list -> FuncMap.t -> stmt -> stmt = fun cnames fmap stmt ->
    match stmt with
    | Assign _ | Decl _ -> stmt
    | Seq (s1,s2) -> Seq (convert_call_s cnames fmap s1, convert_call_s cnames fmap s2)
    | Call (lvop, Lv (MemberAccess (e,"call",_,_)), args, Some eth, gasop, loc, id) when is_address (get_type_exp e) ->
        let balance_info = mk_vinfo {Loc=None; TypeStr=Some "uint256"; Typ= Some (EType (UInt 256)); Org=None}
        let this_info = mk_vinfo {Loc=None; TypeStr=Some "contract"; Typ=Some (Contract main_contract); Org=None} 
        let this = Cast (EType Address, Lv (Var ("this", this_info))) 
        let this_balance = MemberAccess (this,"balance", balance_info, EType (UInt 256)) 
        let rcv_balance = MemberAccess (e, "balance", balance_info, EType (UInt 256)) 

        let invest_map = Var ("@Invest", mk_vinfo {Loc=None; TypeStr=Some "mapping"; Typ=Some (Mapping (Address, EType (UInt 256))); Org=None})
        let rcv_invest = IndexAccess (Lv invest_map, Some e, EType (UInt 256)) 

        let eth' =
            match eth with
            | BinOp (Mul, Lv v1, Lv (Var (v,_)), _) when v.StartsWith("sellPrice") -> Lv v1
            | _ -> eth 
        let invest_sum = Var ("@Invest_sum", mk_vinfo {Loc=None; TypeStr=Some "uint256"; Typ=Some (EType (UInt 256)); Org=None}) 
        let trust_map = Var ("@TU", mk_vinfo {Loc=None; TypeStr=Some "mapping"; Typ=Some (Mapping (Address, EType Bool)); Org=None}) 
        let not_trusted = mk_eq (Lv (IndexAccess (Lv trust_map, Some e, EType Bool))) False 
        let invest_sum_stmt = If (not_trusted, Assign (invest_sum, mk_sub (Lv invest_sum) eth', dummy_loc), Skip, dummy_ifinfo) 

        let cond1 = mk_ge (Lv this_balance) eth 
        let cond2 = mk_ge (mk_add (Lv rcv_balance) eth) (Lv rcv_balance) 
        let true_b = Seq (Assign (this_balance, mk_sub (Lv this_balance) eth, dummy_loc), Assign (rcv_balance, mk_add (Lv rcv_balance) eth, dummy_loc)) 
        let true_b = Seq (true_b, Assign (rcv_invest, mk_sub (Lv rcv_invest) eth, dummy_loc)) 
        let true_b = Seq (true_b, invest_sum_stmt) 
        let true_b = Seq (true_b, call_extern e loc) 
        (* let true_b = Seq (call_extern e loc, true_b) in *)

        let true_b = Seq (stmt, true_b) 
        let false_b = Skip 
        let true_b, false_b =
            (match lvop with
            | None -> true_b, false_b
            | Some (Tuple (Some (Lv (Var v))::_,_))
            | Some (Var v) -> Seq (true_b, Assign (Var v, True, dummy_loc)), Seq (false_b, Assign (Var v, False, dummy_loc))
            | _  -> failwith "Assertion failed") 
        let if_stmt = If (mk_and cond1 cond2, true_b, false_b, dummy_ifinfo) 
        if_stmt

    | Call (lvop,Lv (MemberAccess (e,instr,_,_)),args, _, _, loc, _) when is_address (get_type_exp e) && List.contains instr ["send"; "transfer"] ->
        if not (no_eth_gas_modifiers stmt) then failwith "Assertion failed"
        if not (List.length args = 1) then failwith "Assertion failed"
        let eth = List.head args 
        let balance_info = mk_vinfo {Loc=None; TypeStr=Some "uint256"; Typ= Some (EType (UInt 256)); Org=None} 
        let this_info = mk_vinfo {Loc=None; TypeStr=Some "contract"; Typ= Some (Contract main_contract); Org=None} 
        let this = Cast (EType Address, Lv (Var ("this", this_info))) 
        let this_balance = MemberAccess (this,"balance", balance_info, EType (UInt 256)) 
        let rcv_balance = MemberAccess (e, "balance", balance_info, EType (UInt 256)) 

        let invest_map = Var ("@Invest", mk_vinfo {Loc=None; TypeStr= Some "mapping"; Typ= Some (Mapping (Address, EType (UInt 256))); Org=None})
        let rcv_invest = IndexAccess (Lv invest_map, Some e, EType (UInt 256)) 

        let eth' =
            match eth with
            | BinOp (Mul, Lv v1, Lv (Var (v,_)), _) when v.StartsWith("sellPrice") -> Lv v1
            | _ -> eth 
        let invest_sum = Var ("@Invest_sum", mk_vinfo {Loc=None; TypeStr=Some "uint256"; Typ= Some (EType (UInt 256)); Org=None})
        let trust_map = Var ("@TU", mk_vinfo {Loc=None; TypeStr=Some "mapping"; Typ= Some (Mapping (Address, EType Bool)); Org=None})
        let not_trusted = mk_eq (Lv (IndexAccess (Lv trust_map, Some e, EType Bool))) False 
        let invest_sum_stmt = If (not_trusted, Assign (invest_sum, mk_sub (Lv invest_sum) eth', dummy_loc), Skip, dummy_ifinfo) 

        let cond1 = mk_ge (Lv this_balance) eth 
        let cond2 = mk_ge (mk_add (Lv rcv_balance) eth) (Lv rcv_balance) 
        let true_b = Seq (Assign (this_balance, mk_sub (Lv this_balance) eth, dummy_loc), Assign (rcv_balance, mk_add (Lv rcv_balance) eth, dummy_loc)) 
        let true_b = Seq (true_b, Assign (rcv_invest, mk_sub (Lv rcv_invest) eth, dummy_loc)) 
        let true_b = Seq (true_b, invest_sum_stmt) 
        let true_b = Seq (stmt, true_b) 
        let false_b =
            if instr = "transfer" then Throw
            else if instr = "send" then
                (match lvop with
                | None -> Skip
                | Some lv -> Assign (lv, False, dummy_loc))
            else failwith "Assertion failed"
        let if_stmt = If (mk_and cond1 cond2, true_b, false_b, dummy_ifinfo) 
        (match instr with
        | "transfer" -> if_stmt
        | "send" -> if_stmt
        | _ -> failwith "Assertion failed")

        (* built-in functions *)
    | Call (lvop,e,args,ethop,gasop,loc,_) when FuncMap.is_undef e (List.map get_type_exp args) fmap -> stmt

        (* internal call *)
    | Call (lvop,e,args,ethop,gasop,loc,_) when is_internal_call fmap cnames stmt -> stmt

        (* external calls *)
    | Call (lvop,e,args,ethop,gasop,loc,_) ->
        let rcv = match e with Lv (MemberAccess (rcv,_,_,_)) -> rcv | _ -> failwith "Assertion failed" 
        let callees = FuncMap.find_matching_funcs "" e (List.map get_type_exp args) cnames fmap
        if Set.forall is_view_pure_f callees then stmt (* non-modifiable calls are considered to be harmless *)
        else Seq (stmt, call_extern rcv loc)

    | Skip -> stmt
    | If (e,s1,s2,i) -> If (e, convert_call_s cnames fmap s1, convert_call_s cnames fmap s2, i)
    | While (e,s) -> While (e, convert_call_s cnames fmap s)
    | Break | Continue | Return _ | Throw
    | Assume _ | Assert _ | Assembly _ | PlaceHolder -> stmt
    | Unchecked (lst,loc) ->
        let lst' = List.map (convert_call_s cnames fmap) lst 
        Unchecked (lst',loc)

let do_all_f cnames fmap func =
    let body = get_body func 
    let body = convert_call_s cnames fmap body 
    let body = if is_constructor func then body else body 
    update_body body func

let do_all_c cnames fmap c =
    let funcs = get_funcs c 
    let funcs' = List.map (do_all_f cnames fmap) funcs 
    update_funcs funcs' c

let do_all cnames fmap p = List.map (do_all_c cnames fmap) p

let run pgm =
    let pgm = copy pgm  |> inline_mod_calls |> move_decl_to_cnstr
            |> replace_tmpexp |> normalize |> rmskip |> replace_lib_calls
            |> add_libname_fcalls_in_lib |> rmskip
            |> replace_super |> rmskip |> rename |> add_retvar_init
            |> extend_tuple  |> add_assume |> desugar_struct |> rmskip
    let fmap = FuncMap.mk_fmap pgm
    let cnames = get_cnames pgm
    do_all cnames fmap pgm
