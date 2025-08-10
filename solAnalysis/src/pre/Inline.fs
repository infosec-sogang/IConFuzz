module solAnalysis.Inline

open Lang
open MakeCfg
open Vocab
open FuncMap
open Options

let mutable inline_cnt = 0
let update_inline_cnt () = inline_cnt <- inline_cnt + 1
let inline_label () = "__inline" + (string inline_cnt)

let rec msg_lv lv =
  match lv with
  | Var x -> lv
  | MemberAccess (e,x,xinfo,typ) -> MemberAccess (msg_e e, x, xinfo, typ)
  | IndexAccess (e,None,_) -> failwith "msg_lv"
  | IndexAccess (e1,Some e2,typ) -> IndexAccess (msg_e e1, Some (msg_e e2), typ)
  | Tuple (eoplst,typ) ->
    eoplst
    |> List.map (fun eop -> match eop with None -> None | Some e -> Some (msg_e e))
    |> (fun eoplst' -> Tuple (eoplst',typ))

and msg_e exp =
  match exp with
  | Int _ | Real _ | Str _ -> exp
  | Lv lv when to_string_lv (ToStringArg.Singlelv lv) = "msg.sender" -> Lv (Var ca)
  | Lv lv -> Lv (msg_lv lv)
  | Cast (t,e) -> Cast (t, msg_e e)
  | BinOp (bop,e1,e2,einfo) -> BinOp (bop, msg_e e1, msg_e e2, einfo)
  | UnOp (uop,e,t) -> UnOp (uop, msg_e e, t)
  | True | False | ETypeName _ -> exp
  | _ -> failwith ("msg_e : " + to_string_exp (ToStringArg.SingleExp exp))

let rec msg_s stmt =
  match stmt with
  | Assign (lv,e,loc) -> Assign (msg_lv lv, msg_e e, loc)
  | Decl lv -> Decl (msg_lv lv)
  | Seq (s1,s2) -> Seq (msg_s s1, msg_s s2)
  | Call (lvop, e, args, ethop, gasop, loc, id) ->
    let lvop' = match lvop with None -> lvop | Some lv -> Some (msg_lv lv)
    let e' = msg_e e
    let args' = List.map msg_e args
    let ethop' = match ethop with None -> ethop | Some e -> Some (msg_e e)
    let gasop' = match gasop with None -> gasop | Some e -> Some (msg_e e)
    Call (lvop', e', args', ethop', gasop', loc, id)
  | Skip -> stmt
  | If (e,s1,s2,i) -> If (msg_e e, msg_s s1, msg_s s2, i)
  | While (e,s) -> While (msg_e e, msg_s s)
  | Break | Continue -> stmt
  | Return (eop,loc) ->
    let eop' = match eop with None -> eop | Some e -> Some (msg_e e)
    Return (eop',loc)
  | Throw -> stmt
  | Assume (e,loc) -> Assume (msg_e e, loc)
  | Assert (e,vtyp,loc) -> Assert (msg_e e, vtyp, loc)
  | Assembly _ | PlaceHolder -> stmt
  | Unchecked _ -> failwith "msg_s"

let replace_msg g =
  fold_node (fun acc n ->
    if Set.contains n acc.extern_set then
      add_node_stmt n (msg_s (find_stmt n acc)) acc
    else acc
  ) g g

(* after inlining, there may exist exception node somewhere in the middle. *)
let connect_exception_to_exit g =
  fold_edges (fun acc (n1, n2) ->
    if is_exception_node n1 acc then acc |> remove_edge n1 n2 |> add_edge n1 Node.exit
    else acc
  ) g g

let postprocess g = g |> connect_exception_to_exit |> remove_unreach |> replace_msg

let rename_stmt' callee gvars cnames stmt =
  let lab = inline_label ()
  match stmt with
  | Return (None,_) -> Skip
  | Return (Some e,loc) ->
    let ret_params = get_ret_params callee
    let lv = params_to_lv ret_params
    Assign (rename_lv lab gvars lv, rename_e lab gvars e, loc)
  | If _ | Seq _ | While _
  | Break | Continue | Unchecked _ -> failwith "rename_stmt"
  | _ -> rename_stmt lab gvars cnames stmt

let replace_node target (new_node,new_stmt) g =
  let preds = pred target g
  let succs = succ target g
  let g = remove_node target g
  let g = add_node_stmt new_node new_stmt g
  let g = List.fold (fun acc p -> add_edge p new_node acc) g preds
  let g = List.fold (fun acc s -> add_edge new_node s acc) g succs
  g

let copy_node callee gvars cnames node g =
  if is_entry node then g else
  if is_exit node then g
  else
    let copied_node = Node.make () 
    let copied_stmt = rename_stmt' callee gvars cnames (find_stmt node g)
    let g' = replace_node node (copied_node, copied_stmt) g
    { g' with outpreds_of_lh = if Set.contains node g.outpreds_of_lh then Set.add copied_node g'.outpreds_of_lh else g'.outpreds_of_lh;
              lh_set = if Set.contains node g.lh_set then Set.add copied_node g'.lh_set else g'.lh_set;
              lx_set = if Set.contains node g.lx_set then Set.add copied_node g'.lx_set else g'.lx_set;
              continue_set = if Set.contains node g.continue_set then Set.add copied_node g'.continue_set else g'.continue_set;
              break_set = if Set.contains node g.break_set then Set.add copied_node g'.break_set else g'.break_set;
              extern_set = if Set.contains node g.extern_set then Set.add copied_node g'.extern_set else g'.extern_set
    }

(* returns (entry_node * exit_node * copied graph) *)
let mk_cfg_copy callee gvars cnames g =
  let nodes = nodes_of g
  let g = List.fold (fun g' n -> copy_node callee gvars cnames n g') g nodes
  let entry_node = Node.make ()
  let exit_node = Node.make ()
  let g = replace_node Node.entry (entry_node,Skip) g
  let g = replace_node Node.exit (exit_node,Skip) g
  (entry_node, exit_node, g)

let is_uint_assign_node n g =
  match find_stmt n g with
  | Assign (lv,_,_) when is_uintkind (get_type_lv lv) -> true
  | _ -> false

let inline_n gvars cnames fmap caller n g =
  let stmt = find_stmt n g
  match stmt with
  | Call (lvop,e,args,_,_,loc,_)
    when FuncMap.is_undef e (List.map get_type_exp args) fmap -> (* built-in functions *)
    (false, g)

  | Call (lvop,Lv (Var ("@extern",_)),args,_,_,loc,_) when (get_fname caller) = "@extern" ->
    let g = replace_node n (n,Skip) g
    (true, g)

  | Call (lvop,e,args,_,_,loc,_) when is_internal_call fmap cnames stmt ->
    let cname = (get_finfo caller).scope_s 
    let callees = FuncMap.find_matching_funcs cname e (List.map get_type_exp args) cnames fmap
    let _ = assert (Set.count callees = 1)
    let callee = Set.minElement callees
    let size_of g =
      fold_node (fun acc n ->
        if not (Preprocess.is_pseudo_stmt_node n g) && is_uint_assign_node n g then acc + 1
        else if is_internal_call_node fmap cnames n g then acc+1
        else acc
      ) g 0
    let excessive = size_of (get_cfg callee) > 5 || has_loop (get_cfg callee)
    (false, g)
  | Call _ -> (false, g) (* object call *)
  | _ -> (false, g)

let inline_f b gvars cnames fmap f =
  if b && not (get_fname f = "@extern") then (false, f)
  else
    let g = get_cfg f
    let nodes = nodes_of g
    let (changed, g') =
      List.fold (fun (acc_changed, acc_g) n ->
        let (new_changed, new_g) = inline_n gvars cnames fmap f n acc_g in
        (acc_changed || new_changed, new_g)
      ) (false,g) nodes
    let g'' = postprocess g'
    (changed, update_cfg f g'') (* cfg is updated whenever inlining is conducted. *)

let inline_c b gvars cnames fmap c = 
        let funcs = get_funcs c
        let (changed, funcs) =
            List.fold (fun (acc_changed, acc_funcs) f ->
            let (changed', f') = inline_f b gvars cnames fmap f
            (acc_changed || changed', acc_funcs @ [f'])
            ) (false,[]) funcs
        (changed, update_funcs funcs c)

(* inline once *)
let inline_p b p =
    let gvars = get_gvars p
    let fmap = FuncMap.mk_fmap p
    let cnames = get_cnames p
    let base_names,_ = Global.get_basenames p
    List.fold (fun (acc_changed, acc_p) c ->
      let (changed', c') = (* currently, inline only main and its parent (to handle 'super' keyword) contracts *)
        if List.contains (get_cname c) base_names then inline_c b gvars cnames fmap c else (false, c)
      (acc_changed || changed', acc_p@[c'])
    ) (false,[]) p

let is_target_node cnames fmap n g =
  let stmt = find_stmt n g
  match stmt with
  | Call (lvop,e,args,_,_,loc,_) when (FuncMap.is_undef e (List.map get_type_exp args) fmap) -> false
  | Call _ -> is_internal_call fmap cnames stmt
  | _ -> false

let remove_call_f cnames fmap f =
  let g = get_cfg f
  let g' =
    fold_node (fun acc n ->
      if is_target_node cnames fmap n acc then add_node_stmt n Throw acc
      else acc
    ) g g
  in
  let g'' = postprocess g'
  (update_cfg f g'')

let remove_call_c cnames fmap c =
  let funcs' = List.map (remove_call_f cnames fmap) (get_funcs c)
  update_funcs funcs' c

let remove_call_p p =
  let cnames = get_cnames p
  let fmap = FuncMap.mk_fmap p
  List.map (remove_call_c cnames fmap) p

let rec inline_ntimes b n p =
  assert (n>=0)
  if n=0 then p
    // if !Options.mode="exploit" && not b then remove_call_p p
    // else p
  else
    let (changed,p') = inline_p b p
    if not changed then p'
    else inline_ntimes b (n-1) p'

let run pgm = 
    pgm |> inline_ntimes true Options.inline_depth (* finitize @extern first *)
        |> inline_ntimes false Options.inline_depth