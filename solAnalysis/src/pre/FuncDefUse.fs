module solAnalysis.FuncDefUse

open Lang
open Vocab
open FuncMap
open MakeCfg

type t = Map<fkey, value>
and du_map = t
and value = def_set * use_set * use_set_assume 
and def_set = id Set
and use_set = id Set
and use_set_assume = id Set

let mem = Map.containsKey
let empty = Map.empty
let bindings = Map.toList
let find x m =
  match Map.tryFind x m with
  | Some value -> value
  | None -> (Set.empty, Set.empty, Set.empty)

let find_def_set x m = let (fst, _, _) = find x m in fst
let find_use_set x m = let (_, snd, _) = find x m in snd
let find_use_set_assume x m = let (_, _, trd) = find x m in trd

let add_def x defs m =
  Map.add x (Set.union defs (find_def_set x m), find_use_set x m, find_use_set_assume x m) m

let add_use x uses m =
  Map.add x (find_def_set x m, Set.union uses (find_use_set x m), find_use_set_assume x m) m

let add_use_assume x uses m =
  Map.add x (find_def_set x m, find_use_set x m, Set.union uses (find_use_set_assume x m)) m

let to_string map =
  let to_string_x (cid,fid,typs) = cid + "," + fid + "," + String.string_of_list (to_string_typ, typs, "(", ")", ",")
  let to_string_y y = String.string_of_set (id, y, "{", "}", ", ") 
  "{" + "\n" +
  Map.fold (fun acc x (d,u,a) -> 
    acc + to_string_x x + " ->\n" +
    "  " + "DEF: " + to_string_y d + "\n" +
    "  " + "USE: " + to_string_y u + "\n" +
    "  " + "USE_ASSUME: " + to_string_y a + "\n" 
  ) "" map
  + "}"

let eq m1 m2 = (to_string m1) = (to_string m2)

let rec get_def_set_lv lv =
  match lv with
  | Var (id,vinfo) -> Set.singleton id
  | MemberAccess (e,"length",info,_) -> Set.singleton "@L"
  | MemberAccess (e,"balance",info,_) ->
    let _ = assert (info.vtyp = EType (UInt 256)) 
    let _ = assert (is_address (get_type_exp e))
    Set.singleton "@B"
  | MemberAccess (e,x,xinfo,_) -> Set.singleton x
  (* | MemberAccess (Lv lv,x,xinfo,_) -> get_def_set_lv lv *)
  | IndexAccess (Lv lv,_,_) -> get_def_set_lv lv
  | IndexAccess (Cast (_, Lv lv),_,_) -> get_def_set_lv lv
  | Tuple (eops,_) ->
    List.fold (fun acc eop ->
      match eop with
      | Some (Lv lv) -> Set.union (get_def_set_lv lv) acc
      | None -> acc
      | _ -> failwith "get_defs_lv"
    ) Set.empty eops
  | _ -> failwith "get_defs_lv"

let get_def_set_lvop lvop =
  match lvop with
  | None -> Set.empty
  | Some lv -> get_def_set_lv lv

let get_use_set_exp exp = Set.map fst (var_exp exp)

let get_use_set_exps exps =
  List.fold (fun acc e ->
    let uses = get_use_set_exp e 
    Set.union uses acc
  ) Set.empty exps

type alias_map = Map<id, id Set>

let find_alias x m = 
    match Map.tryFind x m with 
    | Some value -> value
    | None -> Set.empty

let handle_built_in_funcs (lvop,f,args) =
  match lvop with
  | None ->
    (match f with
     | "revert" -> (Set.empty, Set.empty)
     | "selfdestruct" -> (Set.empty, get_use_set_exps args)
     | "suicide" -> (Set.empty, get_use_set_exps args)
     | "delete" ->
        let _ = assert (List.length args = 1) 
        let exp = List.head args 
        let defs = match exp with Lv lv -> get_def_set_lv lv | _ -> failwith "FuncDefUse: handle_built_in_funcs"
        (defs, Set.difference (get_use_set_exp exp) defs)
     | _ -> failwith ("handle_built_in_funcs: " + f))
  | Some lv -> (* lv is in 'Var' pattern *)
    (match f with
     | "keccak256" | "sha3" | "sha256" | "ripemd160"
     | "ecrecover" | "addmod" | "blockhash" ->
        (get_def_set_lv lv, get_use_set_exps args)
     | _ -> failwith ("handle_built_in_funcs: " + f))

let handle_undefs fmap (lvop,exp,args) loc =
  match exp with
  | Lv (Var (f,_)) when List.contains f built_in_funcs ->
    handle_built_in_funcs (lvop,f,args)
  | _ -> (get_def_set_lvop lvop, get_use_set_exps args)

let update_du_n : id list -> FuncMap.t -> cfg -> fkey -> Node.t -> t * alias_map -> t * alias_map = 
  fun cnames fmap g fkey n (du_map, aliasMap) ->
    let (cname,_,_) = g.signature 
    let stmt = find_stmt n g 
    match stmt with
    | Assign (lv,Lv e,_) when is_struct (get_type_lv lv) ->
      let defs, aliases = get_def_set_lv lv, get_def_set_lv e 
      let uses =
        let lv_use = Set.difference (Set.map fst (var_lv lv)) (get_def_set_lv lv) 
        Set.union lv_use (Set.map fst (var_exp (Lv e))) 
      let du_map = add_def fkey defs du_map 
      let du_map = add_use fkey uses du_map 
      let aliasMap = Set.fold (fun acc d -> 
        Map.add d (Set.union aliases (find_alias d acc)) acc) aliasMap defs
      (du_map, aliasMap)
    | Assign (lv,_,_) when is_struct (get_type_lv lv) -> failwith "update_du_n"
    | Assign (lv,e,_) ->
      let defs = get_def_set_lv lv
      let defs = Set.fold (fun acc d -> Set.union (find_alias d aliasMap) acc) defs defs
      let uses =
        let lv_use = Set.difference (Set.map fst (var_lv lv)) (get_def_set_lv lv) 
        Set.union lv_use (Set.map fst (var_exp e)) 
      let du_map = add_def fkey defs du_map 
      let du_map = add_use fkey uses du_map 
      (du_map, aliasMap)
    | Decl lv -> (add_def fkey (get_def_set_lv lv) du_map, aliasMap)
    | Call (lvop,e,args,_,_,loc,_) when is_undef_call fmap stmt ->
      let (defs,uses) = handle_undefs fmap (lvop,e,args) loc 
      let du_map = add_def fkey defs du_map 
      let du_map = add_use fkey uses du_map 
      (du_map, aliasMap)

    | Call _ when is_external_call stmt ->
      (* the anlysis here aims to identify def-use by direct usage in code *)
      (du_map, aliasMap)

    | Call (lvop,e,args,_,_,loc,_) -> (* normal calls *)
      (* Find def set *)
      let init_defs = match lvop with Some lv -> get_def_set_lv lv | None -> Set.empty 
      let callees = FuncMap.find_matching_funcs cname e (List.map get_type_exp args) cnames fmap 
      let defs =
        Set.fold (fun acc callee ->
          Set.union (find_def_set (get_fkey callee) du_map) acc
        ) init_defs callees
      (* Find use set *)
      let init_uses1 =
        (match lvop with
        | Some lv ->
          let all = Set.map fst (var_lv lv) 
          Set.difference all (get_def_set_lv lv)
        | None -> Set.empty) 
      let init_uses2 =
        List.fold(fun acc e ->
          let use_ids = Set.map fst (var_exp e) 
          Set.union use_ids acc
        ) Set.empty args 
      let init_uses = Set.union init_uses1 init_uses2 
      let uses =
        Set.fold (fun acc callee ->
          Set.union (find_use_set (get_fkey callee) du_map) acc
        ) init_uses callees
      (* Find use_assume set *)
      let uses_assume =
        Set.fold (fun acc callee ->
          Set.union (find_use_set_assume (get_fkey callee) du_map) acc
        ) Set.empty callees
      (du_map |> add_def fkey defs |> add_use fkey uses |> add_use_assume fkey uses_assume,
      aliasMap)
    | Assembly (lst,_) ->
      let defs = Set.map fst (Set.ofList lst) (* conservative result *)
      let uses = defs 
      (du_map |> add_def fkey defs |> add_use fkey uses, aliasMap)
    | Skip -> (du_map, aliasMap)
    | Return (None,_) -> (du_map, aliasMap)
    | Return (Some e,_) ->
      let uses = Set.map fst (var_exp e) 
      (add_use fkey uses du_map, aliasMap)
    | Throw -> (du_map, aliasMap)
    | Assume (e,_) ->
      let uses = Set.map fst (var_exp e) 
      (du_map |> add_use fkey uses |> add_use_assume fkey uses,
      aliasMap)
    | Assert (e,_,_) ->
      let uses = Set.map fst (var_exp e) 
      (add_use fkey uses du_map, aliasMap)
    | PlaceHolder -> (du_map, aliasMap) (* this case is encountered for the modifier case *)
    | If _ | Seq _ | While _ | Break | Continue | Unchecked _ -> failwith "update_du_n"

let onestep cnames fmap fkey (du_map, alias_map) =
  let f = FuncMap.find fkey fmap 
  let g = get_cfg f 
  let nodes = nodes_of g 
  List.fold (fun (acc_du_map, acc_alias_map) n ->
    update_du_n cnames fmap g fkey n (acc_du_map, acc_alias_map)
  ) (du_map, alias_map) nodes

let onestep_f cnames fmap fkeys (du_map, alias_map) =
  Set.fold (fun (acc_du_map, acc_alias_map) fkey ->
    onestep cnames fmap fkey (acc_du_map, acc_alias_map)
  ) (du_map,alias_map) fkeys

let rec fix_fsum cnames fmap fkeys (du_map,alias_map) =
  let du_map', alias_map' = onestep_f cnames fmap fkeys (du_map,alias_map) 
  if eq du_map' du_map then du_map'
  else fix_fsum cnames fmap fkeys (du_map',alias_map')

let compute cnames fmap =
  let lst = Map.toList fmap 
  let fkeys = List.map fst lst |> Set.ofList
  let res = fix_fsum cnames fmap fkeys (empty, Map.empty) 
  res