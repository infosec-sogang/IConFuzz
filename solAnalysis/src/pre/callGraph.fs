module solAnalysis.CallGraph

open System
open Lang
open Vocab
open FuncMap

type edge = fkey * fkey

let to_string_edge (k1,k2) = to_string_fkey k1 + " -> " + to_string_fkey k2
let to_string_edges edges = String.string_of_set(to_string_edge, edges, first="[", last="]", sep=",\n")
let print_edges edges = printfn "%s\n" (to_string_edges edges)

let edges_n : id list -> FuncMap.t -> func -> Node.t -> edge Set -> edge Set = fun cnames fmap curf node edges ->
    let stmt = find_stmt node (Lang.get_cfg curf) 
    match stmt with
    | Call (_,Lv (Var ("contract_init",_)),args,_,_,_,_) ->
        let cnstr_exp, cnstr_args = List.head args, List.tail args
        if not (List.contains (to_string_exp (SingleExp cnstr_exp)) cnames) then failwith "Assertion failed" 
        let callees = FuncMap.find_matching_funcs (to_string_exp (SingleExp cnstr_exp)) cnstr_exp (List.map get_type_exp cnstr_args) cnames fmap
        if not (Set.count callees = 1) then failwith "Assertion failed" 
        let callee = Set.minElement callees 
        Set.add (get_fkey curf, get_fkey callee) edges
    | Call (lvop,e,args,ethop,gasop,loc,_) (* built-in functions *)
        when FuncMap.is_undef e (List.map get_type_exp args) fmap ->
        edges
    | Call (_,e,args,_,_,loc,_) -> (* static or object calls *)
        let caller_cname = (get_finfo curf).scope_s 
        let callees = FuncMap.find_matching_funcs caller_cname e (List.map get_type_exp args) cnames fmap 
        Set.fold (fun acc callee ->
            Set.add (get_fkey curf, get_fkey callee) acc
        ) edges callees 
    | _ -> edges

let rec edges_s : id list -> FuncMap.t -> func -> stmt -> edge Set -> edge Set = fun cnames fmap curf stmt edges ->
    match stmt with
    | Assign _ | Decl _ -> edges
    | Seq (s1,s2) -> edges |> edges_s cnames fmap curf s1 |> edges_s cnames fmap curf s2
    | Call (lvop,e,args,ethop,gasop,loc,_) (* built-in functions *)
        when FuncMap.is_undef e (List.map get_type_exp args) fmap -> edges
    | Call (_,e,args,_,_,loc,_) -> (* static or object calls *)
        let caller_cname = (get_finfo curf).scope_s 
        let callees = FuncMap.find_matching_funcs caller_cname e (List.map get_type_exp args) cnames fmap 
        Set.fold (fun acc callee ->
            Set.add (get_fkey curf, get_fkey callee) acc
            ) edges callees 
    | Skip -> edges
    | If (e,s1,s2,i) -> edges |> edges_s cnames fmap curf s1 |> edges_s cnames fmap curf s2
    | While (e,s) -> edges_s cnames fmap curf s edges
    | Break | Continue | Return _
    | Throw | Assume _ | Assert _
    | Assembly _ | PlaceHolder -> edges
    | Unchecked (lst,_) -> list_fold (edges_s cnames fmap curf) lst edges

type Edges =
    static member edges_f(cnames, fmap, f, edges, ?inlined_cfg) = 
        let inlined_cfg = defaultArg inlined_cfg true
        if inlined_cfg then
            let nodes = nodes_of (get_cfg f) 
            list_fold (edges_n cnames fmap f) nodes edges
        else
            edges_s cnames fmap f (get_body f) edges

    static member partial_edges_f(cnames, fmap, inlined_cfg) = fun f edges ->
        Edges.edges_f(cnames, fmap, f, edges, inlined_cfg)

    static member edges_c(cnames, fmap, c, edges, ?inlined_cfg) = 
        let inlined_cfg = defaultArg inlined_cfg true
        list_fold (Edges.partial_edges_f(cnames, fmap, inlined_cfg)) (get_funcs c) edges

    static member partial_edges_c(cnames, fmap, inlined_cfg) = fun c edges ->
        Edges.edges_c(cnames, fmap, c, edges, inlined_cfg)

    static member edges_p(cnames, fmap, p, ?inlined_cfg) =
        let inlined_cfg = defaultArg inlined_cfg true
        list_fold (Edges.partial_edges_c(cnames, fmap, inlined_cfg)) p Set.empty

    static member collect_call_edges(cnames, fmap, p, ?inlined_cfg) =
        let inlined_cfg = defaultArg inlined_cfg true
        Edges.edges_p(cnames, fmap, p, inlined_cfg)

let init_callees : pgm -> fkey Set = fun p ->
    let main = get_main_contract p in
    let funcs = List.filter (fun f -> (get_finfo f).fvis = Public || (get_finfo f).fvis = External || is_constructor f) (get_funcs main) in
    Set.ofList (List.map get_fkey funcs)

let onestep_callees : fkey Set -> edge Set -> fkey Set = fun callees edges ->
    Set.fold (fun acc (k1,k2) ->
        if Set.contains k1 callees then Set.add k2 acc
        else acc
    ) callees edges 

let onestep_callers : fkey Set -> edge Set -> fkey Set = fun callers edges ->
    Set.fold (fun acc (k1,k2) ->
        if Set.contains k2 callers then Set.add k1 acc
        else acc
    )  callers edges

let rec fix f : fkey Set -> edge Set -> fkey Set = fun fkeys edges ->
    let next = f fkeys edges 
    if Set.isSubset next fkeys then next
    else fix f next edges

let transitive_callees : fkey Set -> edge Set -> fkey Set = fun init edges -> 
    fix onestep_callees init edges

let transitive_callers : fkey Set -> edge Set -> fkey Set = fun init edges -> 
    fix onestep_callers init edges

let compute_reachable_funcs : id list -> FuncMap.t -> pgm -> fkey Set = fun cnames fmap p -> 
    transitive_callees (init_callees p) (Edges.collect_call_edges(cnames, fmap, p))

let rm_unreach_c : fkey Set -> contract -> contract = fun reachable c ->
    let funcs = get_funcs c 
    let funcs' = List.filter (fun f -> Set.contains (get_fkey f) reachable) funcs 
    update_funcs funcs' c

let remove_unreachable_funcs : pgm -> pgm = fun p ->
    let cnames = get_cnames p 
    let fmap = FuncMap.mk_fmap p 
    let all = get_all_fkeys p 
    let reachable = compute_reachable_funcs cnames fmap p 
    let p' = List.map (rm_unreach_c reachable) p 
    System.Console.Error.WriteLine(("- all funcs : " + string (Set.count all)));
    System.Console.Error.WriteLine(("- reachable : " + string (Set.count reachable)));
    if Options.debug = "log" then System.Console.Error.WriteLine(String.string_of_set(to_string_fkey, reachable, sep=", "));
    p'