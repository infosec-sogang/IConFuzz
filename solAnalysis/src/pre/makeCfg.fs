module solAnalysis.MakeCfg

open System
open System.Numerics
open System.Collections.Generic
open Microsoft.FSharp.Collections
open Lang
open FuncMap
open Options

let nodesof : cfg -> node list = fun g ->
    G.fold_vertex (fun l x -> x :: l) [] g.graph

let add_node : node -> cfg -> cfg = fun n g ->
    {g with graph = G.add_vertex g.graph n}

let remove_node : node -> cfg -> cfg = fun n g ->
    {
        g with
            graph = G.remove_vertex g.graph n;
            stmt_map = Map.remove n g.stmt_map;
            outpreds_of_lh = Set.remove n g.outpreds_of_lh;
            lh_set = Set.remove n g.lh_set;
            lx_set = Set.remove n g.lx_set;
            continue_set = Set.remove n g.continue_set;
            break_set = Set.remove n g.break_set;
    }

(* unconditionally add edges *)
let add_edge : node -> node -> cfg -> cfg = fun n1 n2 g ->
    let g = add_node n1 g
    let g = add_node n2 g
    {g with graph = G.add_edge g.graph n1 n2}

let remove_edge : node -> node -> cfg -> cfg = fun n1 n2 g ->
    {g with graph = G.remove_edge g.graph n1 n2}

let fold_node f g acc = G.fold_vertex f acc g.graph
let fold_edges f g acc = G.fold_edges f acc g.graph

let find_stmt : node -> cfg -> stmt = fun n g ->
    try if n = Node.ENTRY || n = Node.EXIT then Skip
        else g.stmt_map[n]
    with _ -> raise (Failure ("No stmt found in the given node " + Node.to_string n))

let is_undef_call : FuncMap.t -> stmt -> bool = fun fmap stmt ->
    match stmt with
    | _ when is_external_call stmt -> false
    | Call (lvop,e,args,ethop,gasop,loc,_) when FuncMap.is_undef e (List.map get_type_exp args) fmap -> true
    | _ -> false

let is_internal_call : FuncMap.t -> id list -> stmt -> bool = fun fmap cnames stmt ->
    match stmt with
    | _ when is_external_call stmt -> false
    | Call (lvop,e,args,ethop,gasop,loc,_) when is_undef_call fmap stmt -> false
    | Call (_,Lv (Var (f,_)),_,_,_,_,_) -> true
    | Call (_,Lv (MemberAccess (Lv (Var (x,_)),_,_,_)),_,_,_,_,_) when List.contains x cnames -> true
    | _ -> false

let is_internal_call_node : FuncMap.t -> id list -> node -> cfg -> bool = fun fmap cnames n g ->
    is_internal_call fmap cnames (find_stmt n g)

let is_external_call_node : node -> cfg -> bool = fun n g ->
    is_external_call (find_stmt n g)

let add_stmt : node -> stmt -> cfg -> cfg = fun n s g ->
    {g with stmt_map = g.stmt_map.Add(n,s)}

let add_node_stmt : node -> stmt -> cfg -> cfg = fun n s g ->
    g |> add_node n |> add_stmt n s

let pred : node -> cfg -> node list = fun n g ->
    G.pred g.graph n

let succ : node -> cfg -> node list = fun n g ->
    G.succ g.graph n

let rec has_break_cont : stmt -> bool = fun s ->
    match s with
    | Assign _ | Decl _ -> false
    | Seq (s1,s2) -> has_break_cont s1 || has_break_cont s2
    | Call _ -> false
    | Skip -> false
    | If (e,s1,s2,_) -> has_break_cont s1 || has_break_cont s2
    | While _ -> false (* must consider outer loop only. *)
    | Break | Continue -> true
    | Return _ | Throw -> false
    | Assume _ | Assert _ | Assembly _ -> false
    | PlaceHolder -> failwith "Assertion failed"
    | Unchecked (lst,_) -> failwith "Assertion failed"

let rec trans : stmt -> node option -> node option -> (node * cfg) -> (node * cfg) = fun stmt lhop lxop (n,g) -> (* lhop : header of dominant loop, lxop : exit of dominant loop, n: interface node *)
    match stmt with
    | Seq (s,While (e,s')) when has_break_cont s ->
        (* do-while with 'Break' or 'Continue' in loop-body *)
        let lh: node = Node.make ()
        let lx: node = Node.make ()
        let (n1,g1) = trans s (Some lh) (Some lx) (n,g)
        let g2 = g1 |> add_node_stmt lh Skip |> add_edge n1 lh
        let (n3,g3) = trans (Assume (e, dummy_loc)) (Some lh) (Some lx) (lh,g2)
        let (n4,g4) = trans s' (Some lh) (Some lx) (n3,g3)
        let g5 = add_edge n4 lh g4
        let (n6,g6) = trans (Assume (UnOp (LNot,e,EType Bool), dummy_loc)) lhop lxop (lh,g5)
        let g7 = g6 |> add_node_stmt lx Skip |> add_edge n6 lx
        let preds_of_lh = Set.ofList (pred lh g2)
        if not (Set.contains n1 preds_of_lh) then failwith "Assertion failed"
        let g8 = {g7 with outpreds_of_lh = Set.union preds_of_lh g7.outpreds_of_lh; lh_set = Set.add lh g7.lh_set; lx_set = Set.add lx g7.lx_set}
        (lx, g8)
    | Seq (s1,s2) ->
        trans s2 lhop lxop (trans s1 lhop lxop (n,g))
    | If (e,s1,s2,_) ->
        let loc = match e with BinOp (_,_,_,einfo) -> einfo.eloc | _ -> dummy_loc
        let (tn,g1) = trans (Assume (e, loc)) lhop lxop (n,g)  (* tn: true branch assume node *)
        let (tbn,g2) = trans s1 lhop lxop (tn,g1)
        let (fn,g3) = trans (Assume (UnOp (LNot,e,EType Bool), loc)) lhop lxop (n,g2)  (* fn: false branch assume node *)
        let (fbn,g4) = trans s2 lhop lxop (fn,g3)
        let join : node = Node.make ()
        let g5 = g4 |> add_node_stmt join Skip |> add_edge tbn join |> add_edge fbn join
        (join, g5)
    | While (e,s) ->
        let lh: node = Node.make ()
        let lx: node = Node.make ()  (* node id : lh + 1 *)
        let g1 = g |> add_node_stmt lh Skip |> add_edge n lh
        let (n2,g2) = trans (Assume (e,dummy_loc)) (Some lh) (Some lx) (lh,g1) (* node id : lh + 2 *)
        let (n3,g3) = trans s (Some lh) (Some lx) (n2,g2)
        let g4 = add_edge n3 lh g3
        let (n5,g5) = trans (Assume (UnOp (LNot,e,EType Bool), dummy_loc)) lhop lxop (lh,g4)
        let g6 = g5 |> add_node_stmt lx Skip |> add_edge n5 lx
        let g7 = {g6 with outpreds_of_lh = Set.add n g6.outpreds_of_lh; lh_set = Set.add lh g6.lh_set; lx_set = Set.add lx g6.lx_set;}
        (lx, g7)
    | Break ->
        let lx = (match lxop with Some lx -> lx | None -> raise (Failure "Loop exit should exist"))
        let n' : node = Node.make ()
        let g' = g |> add_node_stmt n' Skip |> add_edge n n' |> add_edge n' lx
        (n', {g' with break_set = Set.add n' g'.break_set})
    | Continue ->
        let lh = (match lhop with Some lh -> lh | None -> raise (Failure "Loop header should exist"))
        let n' : node = Node.make ()
        let g' = g |> add_node_stmt n' Skip |> add_edge n n' |> add_edge n' lh
        (n', {g' with continue_set = Set.add n' g'.continue_set})
    | Return (eop,_) ->
        let n' : node = Node.make ()
        (Node.exit, g |> add_node_stmt n' stmt |> add_edge n n' |> add_edge n' Node.exit)
    | Assume (BinOp (LAnd,e1,e2,_), loc) ->
        let (n1,g1) = trans (Assume (e1,loc)) lhop lxop (n,g)
        let (n2,g2) = trans (Assume (e2,loc)) lhop lxop (n1,g1)
        (n2,g2)
    | Assume (BinOp (LOr,e1,e2,einfo), loc) ->
        let (n1,g1) = trans (Assume (e1,loc)) lhop lxop (n,g)
        let neg = Assume (BinOp (LAnd, UnOp (LNot,e1,EType Bool), e2, einfo), loc)
        let (n2,g2) = trans neg lhop lxop (n,g1) (* should be n, not n1 *)
        let join : node = Node.make ()
        (join, g2 |> add_node_stmt join Skip |> add_edge n1 join |> add_edge n2 join)
    | Assume (UnOp (LNot, UnOp (LNot,e,t1), t2), loc) -> (* !!e -> e *)
        let stmt' = Assume (e,loc)
        trans stmt' lhop lxop (n,g)
    | Assume (UnOp (LNot, BinOp (LAnd,e1,e2,einfo), t), loc) -> (* !(e1 && e2) -> !e1 || !e2 *)
        if not (is_bool t) then failwith "Assertion failed"
        let stmt' = Assume (BinOp (LOr, UnOp (LNot,e1,t), UnOp (LNot,e2,t), einfo), loc)
        trans stmt' lhop lxop (n,g)
    | Assume (UnOp (LNot, BinOp (LOr,e1,e2,einfo), t), loc) -> (* !(e1 || e2) -> !e1 && !e2 *)
        if not (is_bool t) then failwith "Assertion failed"
        let stmt' = Assume (BinOp (LAnd, UnOp (LNot,e1,t), UnOp (LNot,e2,t), einfo), loc)
        trans stmt' lhop lxop (n,g)
    | Assume (e,loc) -> (* assumed to be an atomic predicate *)
        let n' : node = Node.make ()
        let g' = g |> add_node_stmt n' stmt |> add_edge n n'
        (n',g')
    | Assert (e,_,loc) -> (* assumed to be an atomic predicate *)
        let n' : node = Node.make ()
        let g' = g |> add_node_stmt n' stmt |> add_edge n n'
        (n',g')
    | _ ->
        let n' : node = Node.make ()
        let g' = g |> add_node_stmt n' stmt |> add_edge n n'
        (n',g')

(* disconnect edges starting from
 * either of
 * an exit, exception (throw or revert), continue, break *)
let disconnect : cfg -> cfg = fun g ->
    fold_edges (fun acc (n1, n2)  ->
    if Node.equal n1 Node.exit then
        remove_edge n1 n2 acc
    elif not (acc.graph.Nodes.Contains n1) then
        remove_edge n1 n2 acc
    elif not (acc.graph.Nodes.Contains n2) then
        remove_edge n1 n2 acc  
    elif is_exception_node n1 acc then
        acc |> remove_edge n1 n2 |> add_edge n1 Node.exit (* normalize so that every function has exit node at the end. *)
    elif is_continue_node n1 acc && not (is_loophead n2 acc) then
        remove_edge n1 n2 acc
    elif is_break_node n1 acc && not (is_loopexit n2 acc) then
        remove_edge n1 n2 acc
    else acc
    ) g g

let remove_unreach : cfg -> cfg = fun g ->
    let onestep g nodes = Set.fold (fun acc n -> Set.union (Set.ofList (succ n g)) acc) nodes nodes
    let reachable = Vocab.fix (onestep g) (Set.singleton Node.entry)
    fold_node (fun acc n ->
        if Set.contains n reachable then acc
        else remove_node n acc
    ) g g

(* remove spurious loopheader *)
let inspect_lh : cfg -> cfg = fun g ->
    fold_node (fun acc n ->
        if is_loophead n acc then
            if List.length (pred n acc) = 1 then (* only precondition exists *)
                {acc with lh_set = Set.remove n acc.lh_set}
            elif List.length (pred n acc) >= 2 then acc
            else raise (Failure "should not exist")
        else acc
    ) g g

let convert : stmt -> cfg = fun stmt ->
    let (n,g) = trans stmt None None (Node.entry, Lang.empty_cfg) 
    g |> add_edge n Node.exit |> disconnect |> remove_unreach |> inspect_lh |> disconnect

let run : pgm -> pgm = fun pgm ->
    List.map (fun contract ->
        let funcs = get_funcs contract
        let funcs' =
            List.map (fun func ->
                let body = get_body func
                let g = convert body
                let g = {g with signature = get_fkey func}
                update_finfo {(get_finfo func) with cfg = g} func
            ) funcs
        update_funcs funcs' contract
    ) pgm
