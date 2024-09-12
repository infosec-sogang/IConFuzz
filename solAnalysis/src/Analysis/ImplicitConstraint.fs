namespace solAnalysis

open System
open solAnalysis
open Global
open Lang
open Options

type key = string array

type ImplicitConstraint = {
    MappingId : string
    DefKeys : key array
    UseKeys : key array
}

module ImplicitConstraint =
    
    let isGlobalVar id gvars =
        gvars |> List.exists (fun (name, _) -> name = id)

    let rec private UpdateDefKey constraints defMaps =
        let updateConstraints = constraints |> Array.map (fun c ->
            let matchingSetEntry = defMaps |> List.tryFind (fun (id, _) -> id = c.MappingId)
            match matchingSetEntry with
            | Some (_, keys) -> { c with DefKeys = Array.append c.DefKeys keys }
            | None -> c )
        let newConstraints = 
            defMaps |> List.filter (fun (id, _) -> not (Array.exists (fun c -> c.MappingId = id) constraints)) |> List.toArray
                    |> Array.map (fun (id, keys) -> {MappingId = id; DefKeys = keys; UseKeys = [||] })
        Array.append updateConstraints newConstraints |> Array.distinct

    let rec private UpdateUseKey constraints useMaps =
        let updateConstraints = constraints |> Array.map (fun c ->
            let matchingSetEntry = useMaps |> List.tryFind (fun (id, _) -> id = c.MappingId)
            match matchingSetEntry with
            | Some (_, keys) -> { c with UseKeys = Array.append c.UseKeys keys }
            | None -> c )
        let newConstraints = 
            useMaps |> List.filter (fun (id, _) -> not (Array.exists (fun c -> c.MappingId = id) constraints)) |> List.toArray
                    |> Array.map (fun (id, keys) -> {MappingId = id; DefKeys = [||]; UseKeys = keys })
        Array.append updateConstraints newConstraints |> Array.distinct
    
    let rec private appendExpToKeyArray keys exp : string array =
        match exp with
        | Lv (Var (id, vinfo)) -> Array.append keys [| id |]
        | Lv (IndexAccess (e1, Some e2, typ)) -> 
            //TODO: Implement this
            appendExpToKeyArray (appendExpToKeyArray keys e1) e2
        | Lv (MemberAccess (e, id, typ, vinfo)) -> 
            match id with
            | "sender" -> Array.append keys [| "msg.sender" |]
            | _ -> keys
        | Cast (_, e) -> appendExpToKeyArray keys e
        | BinOp (_, e1, e2, _) -> appendExpToKeyArray (appendExpToKeyArray keys e1) e2
        | UnOp (_, e, _) -> appendExpToKeyArray keys e
        | IncTemp (e, _, _) -> appendExpToKeyArray keys e
        | DecTemp (e, _, _) -> appendExpToKeyArray keys e
        | CallTemp (e, elist, _, _, _) -> 
            let updateKeys = appendExpToKeyArray keys e
            elist |> List.fold (fun acc e -> appendExpToKeyArray acc e) updateKeys
        | CondTemp (e, e1, e2, _, _) -> 
            appendExpToKeyArray (appendExpToKeyArray (appendExpToKeyArray keys e) e1) e2
        | AssignTemp (lv, e, _) -> appendExpToKeyArray (appendExpToKeyArray keys (Lv lv)) e
        | _ -> keys

    and findMappingVariablesInLv lv gvars : (string * key array) list =
        match lv with
        | IndexAccess (e1, Some e2, typ) ->
            match e1 with
            | Lv (Var (id, vinfo)) ->
                if isGlobalVar id gvars then
                    let mappingId = id
                    let keys = [(appendExpToKeyArray [||] e2)] |> List.toArray |> Array.distinct
                    [(mappingId, keys)]
                else []
            | Lv (IndexAccess(e1', Some e2', typ')) ->
                match e1' with
                | Lv (Var (id, vinfo)) ->
                    if isGlobalVar id gvars then
                        let mappingId = id
                        let keys = [(appendExpToKeyArray (appendExpToKeyArray [||] e2') e2)] |> List.toArray |> Array.distinct
                        [(mappingId, keys)]
                    else []
                | _ -> []
            | _ -> []
        | Tuple (elst, typ) ->
            let elst' = elst |> List.choose (fun e -> match e with | Some e -> Some e | None -> None) 
            List.fold (fun acc e -> acc @ findMappingVariablesInExp e gvars) [] elst'
        | _ -> []

    and findMappingVariablesInExp exp gvars : (string * key array) list =
        match exp with
        | Lv lv -> findMappingVariablesInLv lv gvars
        | Cast (_, e) -> findMappingVariablesInExp e gvars
        | BinOp (_, e1, e2, _) -> (findMappingVariablesInExp e1 gvars) @ (findMappingVariablesInExp e2 gvars)
        | UnOp (_, e, _) -> findMappingVariablesInExp e gvars
        | IncTemp (e, _, _) -> findMappingVariablesInExp e gvars
        | DecTemp (e, _, _) -> findMappingVariablesInExp e gvars
        | CallTemp (e, elist, _, _, _) -> 
            let updateKeys = findMappingVariablesInExp e gvars
            elist |> List.fold (fun acc e -> acc @ (findMappingVariablesInExp e gvars)) updateKeys
        | CondTemp (e, e1, e2, _, _) ->
            (findMappingVariablesInExp e gvars) @ (findMappingVariablesInExp e1 gvars) @ (findMappingVariablesInExp e2 gvars)
        | AssignTemp (lv, e, _) -> (findMappingVariablesInLv lv gvars) @ (findMappingVariablesInExp e gvars)
        | _ -> []
        

    let rec private findMappingVariablesInStmt implicitConstraints stmt gvars =
        match stmt with
        | Assign (lv,e,_) -> 
            let defMappings = findMappingVariablesInLv lv gvars
            let useMappings = findMappingVariablesInExp e gvars
            if defMappings.Length >0 && useMappings.Length >0 then
                let updatedConstraints = UpdateDefKey implicitConstraints defMappings
                UpdateUseKey updatedConstraints useMappings
            else if defMappings.Length >0 then
                UpdateDefKey implicitConstraints defMappings
            else if useMappings.Length >0 then
                UpdateUseKey implicitConstraints useMappings
            else implicitConstraints
        | Seq (s1,s2) ->
            let updatedConstraints = findMappingVariablesInStmt implicitConstraints s1 gvars
            findMappingVariablesInStmt updatedConstraints s2 gvars
        | Call (None, e, exps, ethop, gasop, _, _) ->
            let useMappings = findMappingVariablesInExp e gvars
            let useMappings = exps |> List.fold (fun acc e -> acc @ (findMappingVariablesInExp e gvars)) useMappings
            if useMappings.Length >0 then
                UpdateUseKey implicitConstraints useMappings
            else implicitConstraints
        | Call (Some lv, e, exps, ethop, gasop, _, _) ->
            let useMappings = findMappingVariablesInLv lv gvars
            let useMappings = useMappings@(findMappingVariablesInExp e gvars)
            let useMappings = exps |> List.fold (fun acc e -> acc @ (findMappingVariablesInExp e gvars)) useMappings
            if useMappings.Length >0 then
                UpdateUseKey implicitConstraints useMappings
            else implicitConstraints
        | If (e,s1,s2,_) ->
            let useMappings = findMappingVariablesInExp e gvars
            let updatedConstraints = UpdateUseKey implicitConstraints useMappings
            let updatedConstraints = findMappingVariablesInStmt updatedConstraints s1 gvars
            findMappingVariablesInStmt updatedConstraints s2 gvars
        | While (e,s) ->
            let useMappings = findMappingVariablesInExp e gvars
            let updatedConstraints = UpdateUseKey implicitConstraints useMappings
            findMappingVariablesInStmt updatedConstraints s gvars
        | Return (Some e,_) ->
            let useMappings = findMappingVariablesInExp e gvars
            if useMappings.Length >0 then
                UpdateUseKey implicitConstraints useMappings
            else implicitConstraints
        | Assume (e,_) ->
            let useMappings = findMappingVariablesInExp e gvars
            if useMappings.Length >0 then
                UpdateUseKey implicitConstraints useMappings
            else implicitConstraints
        | Assert (e,_,_) ->
            let useMappings = findMappingVariablesInExp e gvars
            if useMappings.Length >0 then
                UpdateUseKey implicitConstraints useMappings
            else implicitConstraints
        | _ -> implicitConstraints

    let private filterWithArgs pars constraints =
        constraints 
        |> Array.map (fun c->
            let defKeys = c.DefKeys
                        |> Array.map (fun k -> Array.filter (fun s -> pars |> List.exists (fun p -> p = s || s = "msg.sender")) k)
            let useKeys = c.UseKeys
                        |> Array.map (fun k -> Array.filter (fun s -> pars |> List.exists (fun p -> p = s || s = "msg.sender")) k)
            {MappingId = c.MappingId; DefKeys = defKeys; UseKeys= useKeys}
        )

    let private mergeMappings constraints =
        constraints |> Array.groupBy (fun c -> c.MappingId)      
                    |> Array.map (fun (id, mappings) ->
                        let defKeys = mappings 
                                    |> Array.collect (fun c -> c.DefKeys) 
                                    |> Array.filter (fun k -> k.Length > 0)
                                    |> Array.distinct
                        let useKeys = mappings 
                                    |> Array.collect (fun c -> c.UseKeys) 
                                    |> Array.filter (fun k -> k.Length > 0)
                                    |> Array.distinct
                        {MappingId = id; DefKeys = defKeys; UseKeys = useKeys})               

    let getImplicitConstraints (funcSpecs: FuncSpec list) (mainFuncs: func list) gvars =
        let folder acc func =
            let fname = get_fname func
            let stmt = Lang.get_body func
            let pars = get_params func |> List.map (fun (id, vinfo) -> id) 
            let constraints = findMappingVariablesInStmt [||] stmt gvars |> filterWithArgs pars |> mergeMappings
            Array.append acc [|(fname, constraints)|] 
        List.fold folder [||] mainFuncs.[1..]