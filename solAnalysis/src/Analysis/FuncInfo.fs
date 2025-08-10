namespace solAnalysis

open solAnalysis
open Typedef
open Global
open Lang

/// Information obtained as a result of an analysis.
type FuncInfo = {
  FuncSpec : FuncSpec
  // Variables tainted by the constructor. Read-only for non-constructor funcs.
  ConstrTainted : Set<Variable>
  // Variables defined (i.e. SSTORE) by this function.
  Defs : Set<Variable>
  // Variables used (i.e. SLOAD) by this function.
  Uses : Set<Variable>
  // Mapping key constraints inferred from the function.
  MapKeyConstrs : mapKeyConstraint array
  // Privilege constraints inferred from the function.
  PrivilegeConstrs : privilegeConstraint
}

module FuncInfo =
  let mutable index = bigint.Zero

  let init func constrTainted =
    { FuncSpec = func
      ConstrTainted = constrTainted
      Defs = Set.empty
      Uses = Set.empty 
      MapKeyConstrs = [||] 
      PrivilegeConstrs = PrivilegeConstraint.init }

  let print funcInfo =
    let name = FuncSpec.getName funcInfo.FuncSpec
    let ownerStr = if funcInfo.FuncSpec.OnlyOwner then " (onlyOwner)" else ""
    let defStr = Set.map Variable.toString funcInfo.Defs |> String.concat ", "
    let useStr = Set.map Variable.toString funcInfo.Uses |> String.concat ", "
    printfn "%s:%s Def = { %s }, Use = { %s }" name ownerStr defStr useStr

  let getGlobalVariables gvars =
    let gvars' = gvars |> List.map (fun (name, typ) ->
      let newtyp = 
        match typ with
        | Mapping _ | Mapping2 _ -> MapVar (name, index, 0I)
        | Array _ -> ArrayVar (name, index, 0I)
        | _ -> Singleton (name, index) 
      index <- index + 1I
      (name, newtyp))
    gvars'

  let getGlobalAddresses gvars = 
    gvars |> List.filter (fun (id, typ) ->
        match typ with
        | EType t -> (match t with | Address -> true | _ -> false)
        | _ -> false ) |> List.map (fun (name, _) -> name)

  let rec checkStmt stmt taintedAddr =
    match stmt with
    | Seq (s1, s2) -> checkStmt s1 taintedAddr || checkStmt s2 taintedAddr
    | If (e, s1, s2, _) ->
      match e with 
      | BinOp (Eq, Lv (MemberAccess(Lv (Var ("msg", _)), _, _, _)), Lv (Var (name, _)), _) ->
        if taintedAddr |> Set.exists (fun x -> x = name) then true
        else false
      | BinOp (Eq, Lv (Var (name, _)), Lv (MemberAccess(Lv (Var ("msg", _)), _, _, _)), _) ->
        if taintedAddr |> Set.exists (fun x -> x = name) then true
        else false
      | _ -> false
    | _ -> false

  let checkonlyOwner stmt constrTainted gvars =
    let addrs = getGlobalAddresses gvars
    let taintedAddr = constrTainted 
                      |> Set.filter (fun addr -> List.exists (
                        fun s ->
                          match addr with
                          | Singleton (name, _) -> name = s
                          | ArrayVar (name, _, _) -> name = s
                          | MapVar (name, _, _) -> name = s) addrs)
                      |> Set.map (
                        fun x -> 
                          match x with
                          | Singleton (name, _) -> name
                          | ArrayVar (name, _, _) -> name
                          | MapVar (name, _, _) -> name)
    if checkStmt stmt taintedAddr then true else false

  let getConstrInfo constrFunc mainFuncs defuse constrTainted gvars =
    match Map.tryFind constrFunc.Name defuse with
    | None -> 
      { FuncSpec = constrFunc; ConstrTainted = Set.empty; Defs = Set.empty; Uses = Set.empty; MapKeyConstrs = [||]; PrivilegeConstrs = PrivilegeConstraint.init }
    | Some defuse ->
      let (defs, uses, use_assumes) = defuse 
      let defs = defs |> List.map snd |> Set.ofList
      let uses = uses |> List.map snd |> Set.ofList
      let stmt = mainFuncs |> List.find (fun f -> get_fname f = constrFunc.Name) |> get_stmts
      if (checkonlyOwner stmt constrTainted gvars) then
        let func = FuncSpec.updateOnlyOwner constrFunc
        { FuncSpec = func; ConstrTainted = Set.empty; Defs = defs; Uses = uses; MapKeyConstrs = [||]; PrivilegeConstrs = PrivilegeConstraint.init }
      else
        { FuncSpec = constrFunc; ConstrTainted = Set.empty; Defs = defs; Uses = uses; MapKeyConstrs = [||]; PrivilegeConstrs = PrivilegeConstraint.init }

  let getFuncInfos glb constrTainted constrFunc normalFuncs mainFuncs mapkeyconstrs privilegeconstrs =
    let gvars = getGlobalVariables glb.gvars
    let gvarIdList = gvars |> List.map (fun (name, _) -> name)
    let defuse = glb.f_defuse |> Map.toList |> List.map (fun ((cname, fname, t), (defs, uses, use_assumes))->
        let defs = Set.filter (fun x -> List.contains x gvarIdList) defs |> Set.toList
                  |> List.map (fun x -> (x, List.find (fun (name, _) -> name = x) gvars |> snd))
        let uses = Set.filter (fun x -> List.contains x gvarIdList) uses |> Set.toList
                  |> List.map (fun x -> (x, List.find (fun (name, _) -> name = x) gvars |> snd))
        let use_assumes = use_assumes |> Set.toList
        (fname, (defs, uses, use_assumes)))

    let defuse' = defuse |> List.fold ( fun acc (fname, (d, u, u')) ->
                    match Map.tryFind fname acc with
                    | Some (defs, uses, use_assumes) ->
                      let defs = defs @ d 
                      let uses = uses @ u
                      let use_assumes = u' @ use_assumes
                      Map.add fname (defs, uses, use_assumes) acc
                    | None -> Map.add fname (d, u, u') acc
                  ) Map.empty

    let funcInfos = normalFuncs |> List.map (fun func ->
      let defuse = defuse' |> Map.find func.Name
      let (defs, uses, use_assumes) = defuse 
      let defs = defs |> List.map snd |> Set.ofList
      let uses = uses |> List.map snd |> Set.ofList
      let stmt = mainFuncs |> List.find (fun f -> get_fname f = func.Name) |> get_stmts
      let mapkeyconstrs = 
        match Array.tryFind (fun (fname, x) -> fname = func.Name) mapkeyconstrs with
        | Some (_, x) -> x
        | None -> [||]
      let privilegeconstrs =
        match Array.tryFind (fun (fname, x) -> fname = func.Name) privilegeconstrs with
        | Some (_, x) -> x
        | None -> PrivilegeConstraint.init
      if (checkonlyOwner stmt constrTainted glb.gvars) then
        let func = FuncSpec.updateOnlyOwner func
        { FuncSpec = func; ConstrTainted = constrTainted; Defs = defs; Uses = uses; MapKeyConstrs = mapkeyconstrs; PrivilegeConstrs = privilegeconstrs }
      else
        { FuncSpec = func; ConstrTainted = constrTainted; Defs = defs; Uses = uses; MapKeyConstrs = mapkeyconstrs; PrivilegeConstrs = privilegeconstrs })
    let constrInfo = getConstrInfo constrFunc mainFuncs defuse' constrTainted glb.gvars
    (constrInfo, funcInfos)