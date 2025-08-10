module solAnalysis.TopLevel

open System.IO
open System.Text
open Translator
open Solc
open Global
open Options
open Typedef 

type Sequence = string list
let mutable funcInfoMap = Map.empty

// Return the list of function pairs (f, g) that can have any def-use chain.
let enumerateDUChains funcs =
  let folder acc g =
    List.fold (fun acc' f ->
      let gInfo = Map.find g funcInfoMap
      let fInfo = Map.find f funcInfoMap
      let fDefs, gUses = fInfo.Defs, gInfo.Uses
      let interSect = Set.intersect fDefs gUses
      if Set.isEmpty interSect then acc' else Set.add (f, g) acc'
    ) acc funcs
  List.fold folder Set.empty funcs

// Return the list of the function pairs and their constraints if they have any.
let private enumerateMapKeyConstraints funcs =
  let folder acc g =
    List.fold (fun acc' f ->
      let gInfo = Map.find g funcInfoMap
      let fInfo = Map.find f funcInfoMap
      let fICs, gICs = fInfo.MapKeyConstrs, gInfo.MapKeyConstrs
      let interSect = 
        Array.choose (fun fIC ->
          Array.tryPick (fun gIC ->
            if fIC.MappingId = gIC.MappingId && (not (Array.isEmpty fIC.DefKeys) && not (Array.isEmpty gIC.UseKeys))
            then Some {MappingId = fIC.MappingId; DefKeys = fIC.DefKeys; UseKeys = gIC.UseKeys} else None) gICs) fICs
      if Array.isEmpty interSect then acc'
      else Set.add (f, g, interSect) acc'
    ) acc funcs
  List.fold folder Set.empty funcs

// Return the list of the function pairs and their constraints if they have any.
let private enumeratePrivilegeConstraints funcs =
  let folder acc g =
    List.fold (fun acc' f ->
      let gInfo = Map.find g funcInfoMap
      let fInfo = Map.find f funcInfoMap
      let fAC, gAC = fInfo.PrivilegeConstrs, gInfo.PrivilegeConstrs
      let interSect = 
        let e = fAC.Defs |> Array.exists (fun (defsv, defarg) -> gAC.Uses |> Array.exists (fun (usesv, usearg, _) -> defsv = usesv))
        if e then Some (fAC, gAC) else None
      if Option.isNone interSect then acc' else Set.add (f, g, (Option.get interSect)) acc'
    ) acc funcs
  List.fold folder Set.empty funcs

let private initializeWorkList funcInfos =
  let defs = List.filter (fun i -> not (Set.isEmpty i.Defs)) funcInfos
  let defOnlys, defAndUses = List.partition (fun i -> Set.isEmpty i.Uses) defs
  (defOnlys @ defAndUses)
  |> List.map (fun fInfo -> FuncSpec.getName fInfo.FuncSpec)

// Return the set of def-use chains found in the given sequence 'funcSeq'.
let evalDUChain (funcSeq: Sequence): Set<DUChain> =
  let folder (accChains, accDefMap) f =
    let funcInfo = Map.find f funcInfoMap
    let defs = funcInfo.Defs
    let uses = funcInfo.Uses
    let chooser useVar =
      match Map.tryFind useVar accDefMap with
      | None -> None
      | Some defFunc -> Some (defFunc, useVar, f)
    let accChains = Set.union accChains (Set.choose chooser uses)
    // Approximate that 'f' always updates 'defs', to avoid too long sequence.
    let folder acc defVar = Map.add defVar f acc
    let accDefMap = Set.fold folder accDefMap defs
    (accChains, accDefMap)
  List.fold folder (Set.empty, Map.empty) funcSeq |> fst

// From the function sequences 'seqs', find and return the first sequence that
// can yield a new def-use chain not found in 'accChains'. If none of the 'seqs'
// can yield a new def-use chain, return an empty list.
let rec private findDUChainGain accChains seqs =
  match seqs with
  | hdSeq :: tlSeqs ->
    let duChains = evalDUChain hdSeq
    if Set.isEmpty (Set.difference duChains accChains)
    then findDUChainGain accChains tlSeqs
    else (Set.union accChains duChains, [hdSeq])
  | [] -> (accChains, [])

// Tests if s1 is a prefix of s2.
let rec private isPrefix s1 s2 =
  match s1, s2 with
  | [], _ -> true
  | _, [] -> false
  | h1 :: t1, h2 :: t2 -> if h1 = h2 then isPrefix t1 t2 else false

// Tests if s1 is a sub-sequence of s2.
let rec private isSubSeq s1 s2 =
  match s2 with
  | [] -> false
  | _ :: t2 -> if isPrefix s1 s2 then true else isSubSeq s1 t2

let rec private pruneWorkList = function
  | [] -> []
  | headSeq :: tailSeqs ->
    if List.exists (fun s -> isSubSeq headSeq s) tailSeqs then
      printfn "Pruning out %A" headSeq
      pruneWorkList tailSeqs // Drop headSeq.
    else
      let filter tailSeq =
        if isSubSeq tailSeq headSeq then printfn "Pruning out %A" tailSeq; false
        else true
      headSeq :: pruneWorkList (List.filter filter tailSeqs)

let rec private buildLoop (accChains, accSeqs) works =
  match works with
  | [] -> accSeqs
  | candidate :: tailWorks ->
    let allFuncNames = Map.keys funcInfoMap
    let appends = List.map (fun f -> candidate @ [f]) allFuncNames
    let accChains, promisings = findDUChainGain accChains appends
    let accSeqs = if not (List.isEmpty promisings) then accSeqs
                  else candidate :: accSeqs // Add if no more room to improve.
    let newWorks = pruneWorkList (promisings @ tailWorks)
    buildLoop (accChains, accSeqs) newWorks

let storeCumulativeByteSize lines =
    let _, lst = 
        List.fold (fun (accEol, accLst) cur ->
            let eol = (Encoding.UTF8.GetByteCount (cur: string)) + 1
            let accEol' = eol + accEol
            (accEol', accLst @ [accEol'])
        ) (0, []) lines
    lst

let preProcess opt =
    let lines = opt.Input |> File.ReadAllLines |> Array.toList
    let lst = storeCumulativeByteSize lines
    end_of_lines.Value <- lst
    let json_ast = Solc.get_json_ast opt
    let pgm = Translator.run json_ast
    let pgm = Preprocess.run pgm
    let pgm = MakeCfg.run pgm
    let pgm = Inline.run pgm
    let glb = Global.make_global_info pgm lines
    (pgm, glb, lines)

let run opt =
    Options.main_contract <- opt.Main
    Options.solc_ver <- opt.Solv
    let (pgm, glb, lines)= preProcess opt 
    let mainFuncs = pgm |> Lang.get_main_contract |> Lang.get_funcs
    let constrFunc, normalFuncs = FuncSpec.getFuncSpecs glb
    let constructorTainted = FuncSpec.AnalyzeConstructor glb (FuncInfo.getGlobalVariables glb.gvars)
    let mapKeyConstraints = MappingKeyConstraint.getMapKeyConstraints normalFuncs mainFuncs glb.gvars
    let privConstraints = PrivilegeConstraint.getPrivilegeConstraints mainFuncs glb
    let constrInfo, funcInfos = FuncInfo.getFuncInfos glb constructorTainted constrFunc normalFuncs mainFuncs mapKeyConstraints privConstraints
    let normalFuncs = List.map (fun info -> info.FuncSpec) funcInfos
    let contractSpec = ContractSpec.make constrFunc (Array.ofList normalFuncs)
    let folder accMap info = Map.add (FuncSpec.getName info.FuncSpec) info accMap
    funcInfoMap <- List.fold folder Map.empty funcInfos
    let initWorks = initializeWorkList funcInfos
    let funcs = List.map (fun fInfo -> FuncSpec.getName fInfo.FuncSpec) funcInfos

    printfn"\n=================== < Function Information  > ===================\n"
    let _ = FuncInfo.print constrInfo
    let taintStr = Set.map Variable.toString constructorTainted |> String.concat ", "
    printfn "Constructor tainted: { %s }" taintStr
    let _ = List.map (fun info -> FuncInfo.print info) funcInfos
    // Now, decide transaction sequence order with the analysis result.
    printfn "\n====================== < Def - Use Chain > ======================\n"
    let duchains = enumerateDUChains funcs
    printfn "(%d def-use chains)" (Set.count duchains)
    let _ = Set.iter (fun seq -> printfn "%A" seq) duchains
    printfn "\n============= < Mapping-Key Def - Use Constraints > =============\n"
    let mapKeyChains = enumerateMapKeyConstraints funcs
    printfn "(%d mapping-key def-use constraints)" (Set.count mapKeyChains)
    let _ = Set.iter (fun (f, g, _) -> 
        printfn "\n\"%s\" -> \"%s\"" f g) mapKeyChains
    printfn "\n=============== < Privilege Def - Use Constraints > ===============\n"
    let privChains = enumeratePrivilegeConstraints funcs
    printfn "(%d privilege constraints)" (Set.count privChains)
    let _ = Set.iter (fun (f, g, _) -> printfn "\"%s\" -> \"%s\"" f g) privChains
    printfn "\n==================== < Candidate Sequences > ====================\n"
    let initWorksList = initWorks |> List.map (fun f -> [f])
    let seqs = buildLoop (Set.empty, []) initWorksList
    printfn "(%d candidate sequences)" (List.length seqs)
    List.iter (fun seq -> printfn "%A" seq) seqs
    printfn "\n=================================================================\n"
    (contractSpec, seqs, duchains, mapKeyChains, privChains)