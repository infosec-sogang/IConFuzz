namespace solAnalysis

open System
open solAnalysis
open Typedef
open Global
open Lang
open Options
open FuncDefUse

type privilegeConstraint = {
    Defs : DefPair array
    Uses : UseTriple array
}
and DefPair = string * string
and UseTriple = string * string * bool

module PrivilegeConstraint =
    let mutable index = bigint.Zero

    let mutable DEFPAIRS = [||]
    let mutable USETRIPLES = [||]
    let mutable STATEADDRSPAIR = Set.empty

    let init = {Defs = [||]; Uses = [||]}

    let getGlobalAddrs gvars =
        gvars |> List.filter ( fun (name, typ) ->
            match typ with
            | EType Address -> true
            | _ -> false) |> List.map (fun (name, typ) ->
                let newtyp = 
                    match typ with
                    | Mapping _ | Mapping2 _ -> MapVar (name, index, 0I)
                    | Array _ -> ArrayVar (name, index, 0I)
                    | _ -> Singleton (name, index) 
                index <- index + 1I
                (name, newtyp))

    let notGlobalVars (id: string) gvars =
        List.exists (fun ((name: string), _) -> id = name) gvars |> not

    let rec findPrivConstrsInStmt stmt pars def_state_addrs use_state_addrs =
        let filter (var: string) set' = Set.toList set' |> List.exists (fun (name: string) -> var = name)
        match stmt with
        | Assign (lv, e, _) ->
            let useSet = get_use_set_exp e |> Set.filter (fun x -> filter x (Set.union pars def_state_addrs))
            let defSet = get_def_set_lv lv |> Set.filter (fun x -> filter x def_state_addrs)
            STATEADDRSPAIR <- 
                let useSA = get_use_set_exp e |> Set.filter (fun x -> filter x use_state_addrs)
                defSet |> Set.fold (fun acc x -> Set.union acc (Set.map (fun y -> (x, y)) useSA)) Set.empty
            let def_pairs = defSet |> Set.fold (fun acc x -> Set.union acc (Set.map (fun y -> (x, y)) useSet)) Set.empty |> Set.toArray
            DEFPAIRS <- Array.append DEFPAIRS def_pairs
        | Seq (s1, s2) ->
            let _ = findPrivConstrsInStmt s1 pars def_state_addrs use_state_addrs
            findPrivConstrsInStmt s2 pars def_state_addrs use_state_addrs
        | If (BinOp (op, e1, e2, _), s1, s2, _) ->
            let vars = Set.union (get_use_set_exp e1) (get_use_set_exp e2)
            let uses = vars |> Set.filter (fun x -> filter x use_state_addrs)
            let useArgs = vars |> Set.filter (fun x -> filter x pars)
            match op with
            | Eq -> 
                let bools = is_skip_in_stmt s1 || is_throw_in_stmt s2
                let use_triples = uses |> Set.fold (fun acc x -> Set.union acc (Set.map (fun y -> (x, y, bools)) useArgs)) Set.empty |> Set.toArray
                USETRIPLES <- Array.append USETRIPLES use_triples
            | NEq -> 
                let bools = is_skip_in_stmt s2 || is_throw_in_stmt s1
                let use_triples = uses |> Set.fold (fun acc x -> Set.union acc (Set.map (fun y -> (x, y, bools)) useArgs)) Set.empty |> Set.toArray
                USETRIPLES <- Array.append USETRIPLES use_triples
            | _ -> ()
        | While (e, s) ->
            findPrivConstrsInStmt s pars def_state_addrs use_state_addrs
        | _ -> ()
        
    let rec private findPrivConstrs fname stmt pars glb =
        let globalAddrs = getGlobalAddrs glb.gvars
        let funcDefsList =  glb.f_defuse 
                            |> Map.toList |> List.filter (fun ((_, fname', _), _) -> fname = fname')
                            |> List.map (fun ((_, fname', t), (defs, uses, _))->
                            let defs = defs |> Set.filter (fun x -> 
                                                match List.tryFind (fun (name, _) -> name = x) globalAddrs with
                                                | Some _ -> true | None -> false) |> Set.toList
                                            |> List.map (fun x -> (x, List.find (fun (name, _) -> name = x) globalAddrs |> snd))
                            let uses = uses |> Set.filter (fun x -> 
                                                match List.tryFind (fun (name, _) -> name = x) globalAddrs with
                                                | Some _ -> true | None -> false) |> Set.toList
                                            |> List.map (fun x -> (x, List.find (fun (name, _) -> name = x) globalAddrs |> snd))
                            (fname, defs, uses))

        let def_state_addrs =
            match List.tryFind (fun (fname', _, _) -> fname = fname') funcDefsList with
            | Some (_, defs, _) -> defs |> List.map fst |> Set.ofList
            | None -> Set.empty
        let use_state_addrs =
            match List.tryFind (fun (fname', _, _) -> fname = fname') funcDefsList with
            | Some (_, _, uses) -> uses |> List.map fst |> Set.ofList
            | None -> Set.empty

        let filter arr = arr |> Set.ofArray |> Set.toArray
        let _ = findPrivConstrsInStmt stmt pars def_state_addrs use_state_addrs
        let _ =
            if not (Set.isEmpty def_state_addrs) && Array.isEmpty DEFPAIRS && not (Array.isEmpty USETRIPLES) then
                let candidates = USETRIPLES |> Set.ofArray |> Set.filter (fun (x, y, b) -> b)
                if not (Set.isEmpty candidates) then
                    let defs = def_state_addrs|> Set.fold (
                        fun acc x -> Set.union acc (Set.fold (
                            fun acc (x', y', _) -> 
                                if Set.contains (x, x') STATEADDRSPAIR 
                                then Set.add (x, y') acc else acc) Set.empty candidates)) Set.empty |> Set.toArray
                    DEFPAIRS <- Array.append DEFPAIRS defs
        {Defs = filter DEFPAIRS; Uses = filter USETRIPLES}

    let getPrivilegeConstraints (mainFuncs:func list) glb =
        let folder acc func =
            DEFPAIRS <- [||]
            USETRIPLES <- [||]
            let fname, stmt = get_fname func, get_body func
            let pars = get_params func |> List.filter (fun (id, vinfo) -> vinfo.typestr = "address" ) 
                        |> List.map (fun (id, vinfo) -> id) |> List.append ["msg.sender"]
                        |> List.filter (fun id -> notGlobalVars id glb.gvars) |> Set.ofList
            let constraints = findPrivConstrs fname stmt pars glb
            Array.append acc [|(fname, constraints)|]
            
        List.fold folder [||] mainFuncs.[1..]