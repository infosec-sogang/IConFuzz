namespace solAnalysis

open Lang
open FuncDefUse
open FuncMap
open Options
open Global

type SizeType =
  | FixedSize of int
  | UnfixedSize

module SizeType =
  let UNFIXED_ARRAY_INIT_LEN = 2

  let parse sizeStr =
    if sizeStr = "" then UnfixedSize else FixedSize (int sizeStr)

  let decideLen = function
    | FixedSize n -> n
    | UnfixedSize -> UNFIXED_ARRAY_INIT_LEN

/// Represents the type as a compile-time fixed size or a dynamic size.
type ArgType =
  | Int of ByteWidth: int
  | UInt of ByteWidth : int
  | Address
  | Bool
  | Byte
  | String
  | Array of (SizeType * ArgType)

type ArgSpec = {
  Name : string
  /// Original string that specifies type. Needed for ABI encoding interface.
  TypeStr : string
  /// Represents the type of element.
  Kind : ArgType
}

module ArgSpec =
  let UInt256 = {Name = "Pay"; TypeStr = "uint256"; Kind = ArgType.UInt 32 }

type FuncKind =
  | Constructor
  | Fallback
  | Normal

module FuncKind =

  let ofString = function
    | "constructor" -> Constructor
    | "fallback" -> Fallback
    | "function" -> Normal
    | _ -> failwith "Invalid function kind string"

type FuncSpec = {
  Name: string
  Kind: FuncKind
  Payable: bool
  OnlyOwner: bool
  ArgSpecs: ArgSpec array
}

module FuncSpec =

  // Note that we handle TX ether value as an argument, as well.

  let initConstructor payable args =
    { Name = "constructor"
      Kind = Constructor
      Payable = payable
      OnlyOwner = false
      ArgSpecs = Array.append [| ArgSpec.UInt256 |] args }

  let DEFAULT_CONSTURCTOR = initConstructor false [| |]

  let initFallback payable =
    { Name = "fallback"
      Kind = Fallback
      Payable = payable
      OnlyOwner = false
      ArgSpecs = [| ArgSpec.UInt256 |] }

  let init name kind payable args =
    { Name = name
      Kind = kind
      Payable = payable
      OnlyOwner = false
      ArgSpecs = Array.append [| ArgSpec.UInt256 |] args }

  let initDummy kind =
    { Name = ""
      Kind = kind
      Payable = false
      OnlyOwner = false
      ArgSpecs = [| ArgSpec.UInt256; ArgSpec.UInt256 |] }

  let getName func =
    if func.Name <> "" then sprintf "%s" func.Name else sprintf "unknown"
  
  let updateOnlyOwner func = { func with OnlyOwner = true }
  
  let rec vtypeToArgtype (typ: Lang.typ) = 
    match typ with 
    | EType t -> 
        match t with
        | elem_typ.SInt t -> ArgType.Int t
        | elem_typ.UInt t -> ArgType.UInt (t/8)
        | elem_typ.Address -> ArgType.Address
        | elem_typ.Bool -> ArgType.Bool
        | elem_typ.Bytes t -> ArgType.Array (FixedSize t, ArgType.Byte)
        | elem_typ.String -> ArgType.String
        | elem_typ.DBytes -> ArgType.Array (UnfixedSize, ArgType.Byte)
    | typ.Array (t, s) -> ArgType.Array (match s with | Some s -> (FixedSize s,vtypeToArgtype t) | None -> (UnfixedSize, vtypeToArgtype t))
    | Contract _ -> ArgType.Address
    | _ -> failwithf "Invalid type %A" typ

  let getNormalFuncs funcs =
    funcs |> List.filter (fun (_, _, _, _, finfo) -> finfo.is_constructor = false && finfo.is_modifier = false) 
    |> List.filter (fun (_, _, _, _, finfo) -> (finfo.fvis <> Internal && finfo.fvis <> Private)) 
    |> List.map (fun (id, parList, retparList, stmt, finfo) ->
      let onlyOwner = false
      let argList = parList |> List.map (fun (id, vinfo) -> {Name = id; TypeStr = vinfo.typestr; Kind = (vtypeToArgtype vinfo.vtyp)})
      let argList = [{Name = "Pay"; TypeStr = "uint256"; Kind = ArgType.UInt 32}] @ argList
      let funcKind = if (string id).Contains "fallback" then FuncKind.Fallback else FuncKind.Normal
      { Name = id
        Kind = funcKind
        Payable = finfo.is_payable
        OnlyOwner = onlyOwner
        ArgSpecs = argList |> Array.ofList })

  let getConstructFunc funcs mainCont =
    match Lang.find_func mainCont funcs with
    | None -> 
      { Name = mainCont
        Kind = Constructor
        Payable = false
        OnlyOwner = false
        ArgSpecs = [| ArgSpec.UInt256 |] }
    | Some constructFunc ->
      let id, parList, retparList, stmt, finfo = constructFunc
      let onlyOwner = finfo.mod_list |> List.exists (fun (id, _, _) -> id = "onlyOwner")
      let argList = parList |> List.map (fun (id, vinfo: vinfo) -> {Name = id; TypeStr = vinfo.typestr; Kind = (vtypeToArgtype vinfo.vtyp)})
      let argList = [{Name = "Pay"; TypeStr = "uint256"; Kind = ArgType.UInt 32}] @ argList
      { Name = id 
        Kind = Constructor
        Payable = finfo.is_payable
        OnlyOwner = false
        ArgSpecs = argList |> Array.ofList 
      }

  let rec AnalyzeConstructorTainted stmt defs uses gvars =
    let defs' = defs |> List.map (fun (name, _) -> name)
    let constrTainted = 
      stmt |> List.fold ( 
        fun acc (s: string) ->
        if s.Contains(" = ") then 
          let l = s.Split(" = ") |> List.ofArray |> List.head
          let r = s.Split(" = ") |> List.ofArray |> List.tail
          if List.isEmpty (List.filter (fun (x: string) -> (r.ToString()).Contains(x)) uses) then acc
          else 
            let defs' = defs' |> List.filter (fun (x: string) -> (l.ToString()).Contains(x)) 
                              |> List.filter (fun (x: string) ->
                                let t = snd (List.find (fun (name, _) -> name = x) gvars)
                                not (Lang.is_string t)
                                )                
            acc @ defs'
        else acc
      ) [] 
    constrTainted

  let AnalyzeConstructor glb gvars =
    let funckeys = glb.f_defuse |> Map.filter (fun (cname, fname , _ ) _ -> cname = Options.main_contract) |> Map.toList |> List.map fst
    if List.isEmpty funckeys then Set.empty
    else
      let mainfuncs = Map.filter (fun keys _ -> List.contains keys funckeys) glb.fmap |> Map.toList |> List.map snd
      let gvarsIdList = gvars |> List.map (fun (name, _) -> name)
      match Lang.find_func Options.main_contract mainfuncs with
      | None -> Set.empty
      | Some (id, parList, retparList, stmt, finfo) ->
        let stmt' = (Lang.to_string_stmt (ToStringArg.SingleStmt stmt)).Split(';') |> List.ofArray
        let defuse = glb.f_defuse |> Map.toList |> List.map (fun ((cname, fname, t), (defs, uses, _))->
            let defs = Set.filter (fun x -> List.contains x gvarsIdList) defs |> Set.toList
                      |> List.map (fun x -> (x, List.find (fun (name, _) -> name = x) gvars |> snd))
            let uses = Set.filter (fun x -> not (List.contains x gvarsIdList)) uses |> Set.toList
            (fname, (defs, uses))) |> List.filter (fun (fname, _) -> fname = id) |> List.head
        let (_, (defs, uses)) = defuse
        let constructorTaintedSet = (AnalyzeConstructorTainted stmt' defs uses glb.gvars) |> Set.ofList
        let constructorTainted = gvars |> List.filter (fun (s, _) -> Set.contains s constructorTaintedSet) |> List.map snd |> Set.ofList
        constructorTainted

  let getFuncSpecs funcs =  (* Not support analysis without main contract names at this time *)
    let mainName = Options.main_contract
    if mainName = "" then failwith "Main contract not specified" 
    let funckeys = funcs.f_defuse |> Map.filter (fun (cname, _ , _ ) _ -> cname = mainName) |> Map.toList |> List.map fst
    let mainfuncs = Map.filter (fun keys _ -> List.contains keys funckeys) funcs.fmap |> Map.toList |> List.map snd
    let constructFunc = getConstructFunc mainfuncs mainName
    let normalFuncs = getNormalFuncs mainfuncs
    (constructFunc, normalFuncs)


type ContractSpec = {
  Constructor : FuncSpec
  NormalFunctions : FuncSpec array
}

module ContractSpec =

  let make constructor normalFuncs =
    { Constructor = constructor; NormalFunctions = normalFuncs }