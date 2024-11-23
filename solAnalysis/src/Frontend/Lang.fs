module solAnalysis.Lang

open System
open System.Numerics
open System.Collections.Generic
open Microsoft.FSharp.Collections
open Options
open Vocab

module Node =
  type t = ENTRY | EXIT | Node of int

  let equal n1 n2 =
    match n1, n2 with
    | ENTRY, ENTRY -> true
    | EXIT, EXIT -> true
    | Node i1, Node i2 -> i1 = i2
    | _, _ -> false

  let hash = hash

  let compare = compare

  let entry = ENTRY
  let exit = EXIT

  let mutable nid = 0

  let make () = 
    nid <- nid + 1; 
    Node nid

  let to_string n =
    match n with
    | ENTRY -> "ENTRY"
    | EXIT -> "EXIT"
    | Node i -> i.ToString()

type node = Node.t

module G = 
    open Node
    type node = Node.t 
    type edge = node * node
    type Graph = {
        Nodes : Set<node>
        Edges : Set<edge>
    }

    let empty = { Nodes = Set.empty; Edges = Set.empty }
    let add_vertex g n = 
        let nodes' = Set.add n g.Nodes
        { g with Nodes = nodes' }

    let remove_vertex g n = 
        let nodes' = Set.remove n g.Nodes
        { g with Nodes = nodes' }

    let add_edge g n1 n2 = 
        let edge = (n1, n2)
        let edges' = Set.add edge g.Edges
        { g with Edges = edges' }

    let remove_edge g n1 n2 = 
        let edge = (n1, n2)
        let edges' = Set.remove edge g.Edges
        { g with Edges = edges' }
        

    let fold_vertex f acc graph = Set.fold f acc graph.Nodes
    let fold_edges f acc graph = Set.fold f acc graph.Edges

    let pred g n = 
        let visited = new HashSet<node> ()
        let predecessors = new HashSet<node> ()
        let rec dfs cur =
            if not (visited.Contains(cur)) then
                visited.Add(cur) |> ignore
                let cand = 
                    g.Edges
                    |> Set.filter (fun (_, v) -> v = cur)
                    |> Set.map fst
                for f in cand do
                    if f <> n then 
                        predecessors.Add(f) |> ignore
                        dfs f

        for ns in g.Nodes do
            if ns <> n then
                dfs ns
        
        predecessors |> Seq.toList

    let succ g n = 
        let visited = new HashSet<node> ()
        let successors = new HashSet<node> ()
        let rec dfs cur =
            if not (visited.Contains(cur)) then
                visited.Add(cur) |> ignore
                let cand = 
                    g.Edges
                    |> Set.filter (fun (v, _) -> v = cur)
                    |> Set.map snd
                for t in cand do
                    if t <> n then 
                        successors.Add(t) |> ignore
                        dfs t
                        
        for ns in g.Nodes do
            if ns <> n then
                dfs ns
        
        successors |> Seq.toList



let trans_node = Node.Node 0
let extern_node = Node.Node (-1)

(********************)
(********************)
(***** language *****)
(********************)
(********************)
type pgm = contract list
and contract = id * state_var_decl list * structure list * enum list * func list * cinfo

and state_var_decl = id * exp option * vinfo

and structure = id * var_decl list
and var_decl = id * vinfo

and enum = id * enum_mem list
and enum_mem = id

and func = id * param list * ret_param list * stmt * finfo
and param = id * vinfo
and ret_param = id * vinfo

and fsig = id * typ list
and fkey = id * id * typ list
and func_decl = id * var list * var list 
and visibility = Public | Internal | External | Private

and var = id * typ

and vultyp = string

and stmt =
    | Assign of lv * exp * loc
    | Decl of lv
    | Seq of stmt * stmt
    | Call of lv option * exp * exp list *
            exp option * exp option * (* ether, gas *)
            loc * int (* loc, call-site (AST id) *)
    | Skip
    | If of exp * stmt * stmt * ifinfo
    | While of exp * stmt
    | Break
    | Continue
    | Return of exp option * loc
    | Throw
    | Assume of exp * loc
    | Assert of exp * vultyp * loc (* used to check safety conditions *)
    | Assembly of (id * int) list * loc
    | PlaceHolder (* _ *)
    | Unchecked of stmt list * loc (* unchecked block *)

and exp =
    | Int of BigInteger
    | Real of float 
    | Str of string
    | Lv of lv
    | Cast of typ * exp
    | BinOp of bop * exp * exp * einfo
    | UnOp of uop * exp * typ
    | True | False
    | ETypeName of elem_typ 
    | IncTemp of exp * bool * loc 
    | DecTemp of exp * bool * loc
    | CallTemp of exp * exp list * exp option * exp option * einfo
    | CondTemp of exp * exp * exp * typ * loc
    | AssignTemp of lv * exp * loc

and bop =
    | Add | Sub | Mul | Div | Mod | Exponent
    | GEq | Gt | LEq | Lt | LAnd | LOr | Eq | NEq
    | ShiftL | ShiftR | BXor | BAnd | BOr

and uop =
    | Pos | Neg | LNot | BNot

and lv =
    | Var of (id * vinfo)
    | MemberAccess of exp * id * vinfo * typ (* exp.id / vinfo is for id *)
    | IndexAccess of exp * exp option * typ (* exp[exp?] *)
    | Tuple of exp option list * typ (* [a, b, c, d, ] *)

and id = string
and line = int

and loc = {
    line          : line
    finish_line   : line
    offset        : int
    len           : int
}

and cinfo = {
    numid         : int
    inherit_order : int list
    lib_typ_lst   : (id * typ) list
    ckind         : string
}

and vinfo = {
    typestr       : string
    vloc          : loc
    is_gvar       : bool
    vtyp          : typ
    vvis          : visibility
    vid           : int
    refid         : int
    vscope        : int
    storage       : string
    flag          : bool
    org           : exp option
}

and einfo = {
    eloc          : loc
    etyp          : typ
    eid           : int
}

and ifinfo = {
    if_loc        : loc
    if_tloc       : loc
    if_floc       : loc option
}

and mod_call = id * exp list * loc
and state_mutability = Payable | NonPayable | View | Pure

and finfo = {
    is_constructor    : bool
    is_payable        : bool
    is_modifier       : bool
    mod_list          : mod_call list
    mod_list2         : mod_call list
    param_loc         : loc
    ret_param_loc     : loc
    fvis              : visibility
    mutability        : state_mutability
    fid               : int
    floc              : loc
    scope             : int
    scope_s           : id
    org_scope_s       : id
    cfg               : cfg
}

and cfg = {
    graph             : G.Graph
    outpreds_of_lh    : Set<node>
    lh_set            : Set<node> 
    lx_set            : Set<node>
    continue_set      : Set<node>
    break_set         : Set<node>
    extern_set        : Set<node>
    basic_paths       : Set<node list>
    stmt_map          : Map<node, stmt>
    signature         : fkey
}

and typ =
    | ConstInt
    | ConstString
    | ConstReal
    | EType of elem_typ
    | Mapping of elem_typ * typ
    | Mapping2 of typ * typ
    | Array of typ * int option (* type, (size)? *)
    | Contract of id
    | Struct of id list
    | Enum of id
    | TupleType of typ list
    | Void (* dummy type *)

and elem_typ =
    | Address
    | Bool
    | String
    | UInt of int
    | SInt of int
    | Bytes of int 
    | DBytes  

and ToStringArg =
    | Report of bool
    | SingleExp of exp
    | Singlelv of lv
    | SingleExpOpt of exp option
    | SingleStmt of stmt
    | Singlecontract of contract
    | ReportandExp of bool * exp
    | ReportandLv of bool * lv
    | ReportandExpOpt of bool * exp option
    | ReportandIdandExpOpt of bool * id * exp option
    | ReportandStmt of bool * stmt

let dummy_loc = { line = -1; finish_line = -1; offset = -1; len = -1 }

type MkLocArg = {
    Line : int option
    FinishLine : int option
    Offset : int option
    Len : int option
    }

type MkVinfoArg = {
    Loc : loc option
    TypeStr : string option
    Typ : typ option
    Org : exp option option
    }

let mk_loc {Line = line; FinishLine = finishLine; Offset = offset; Len = len} = 
    let (line, finishLine, offset, len) = (defaultArg line -1, defaultArg finishLine -1, defaultArg offset -1, defaultArg len -1)
    let finishLine = max line finishLine
    { line = line; finish_line = finishLine; offset = offset; len = len }

let mk_vinfo {Loc = loc; TypeStr = typstr; Typ = typ; Org = org} =
    let (loc, typstr, typ, org) = (defaultArg loc dummy_loc, defaultArg typstr "", defaultArg typ Void, defaultArg org None)
    {typestr = typstr; vloc = loc; is_gvar = false; vtyp = typ; vvis = Private; vid = -1; refid = -1; vscope = -1; storage = ""; flag = false; org = org}

let dummy_vinfo = {typestr = ""; vloc = dummy_loc; is_gvar = false; vtyp = Void; vvis = Private; vid = -1; refid = -1; vscope = 1; storage = ""; flag = false; org = None}

let dummy_ifinfo = { if_loc = dummy_loc; if_tloc = dummy_loc; if_floc = Some dummy_loc }

let empty_cfg = {
  graph           = G.empty
  outpreds_of_lh  = Set.empty
  lh_set          = Set.empty
  lx_set          = Set.empty
  continue_set    = Set.empty
  break_set       = Set.empty
  extern_set      = Set.empty
  basic_paths     = Set.empty
  stmt_map        = Map.empty
  signature       = ("Dummy","Dummy",[])
}

let find_stmt n g = 
    if n = Node.ENTRY || n = Node.EXIT then Skip
    else
        match Map.tryFind n g.stmt_map with
        | Some s -> s
        | None -> failwith ("No stmt found in the given node" + (Node.to_string n))

let nodes_of g =
    G.fold_vertex (fun acc node -> node::acc) [] g.graph

let has_loop g =
    not (g.lh_set.Count = 0)

let find_contract_id pgm id =
    List.find (fun (cid, _, _, _, _, _) -> cid = id) pgm

let find_contract_nid pgm nid =
    List.find (fun (_,_,_,_,_,cinfo) -> nid = cinfo.numid) pgm

let find_func fname funcs =
    List.tryFind (fun (fid,_,_,_,_) -> fid = fname) funcs
    
let get_main_contract pgm =
    let main = main_contract
    if main = "" then List.last pgm
    else
        try find_contract_id pgm main
        with _ -> failwith ("main contract name mathcing failed")

let get_cname   cont = 
    let (cid, _, _, _, _, _) = cont
    cid
 
let get_decls   cont = 
    let (_,decls,_,_,_,_) = cont
    decls

let get_structs cont = 
    let (_,_,structs,_,_,_) = cont
    structs

let get_enums   cont = 
    let (_,_,_,enums,_,_) = cont
    enums

let get_funcs cont = 
    let (_,_,_,_,funcs,_) = cont
    funcs

let get_cinfo cont = 
    let (_,_,_,_,_,cinfo) = cont
    cinfo

let get_all_structs pgm =
    List.fold (fun acc c -> (get_structs c) @ acc) [] pgm 

let get_cnames  pgm =
    List.map get_cname pgm

let get_gvars_c c =
    get_decls c |> List.map (fun (x,_,vinfo) -> (x,vinfo.vtyp))

let get_gvars pgm =
    get_main_contract pgm  |> get_decls |> List.map (fun (x,_,vinfo) -> (x,vinfo.vtyp))

let get_libnames pgm =
    List.filter (fun c -> (get_cinfo c).ckind = "library") pgm
    |> List.map get_cname

let get_numid cont = 
    let (_,_,_,_,_,cinfo) = cont
    cinfo.numid

let get_fname func =
    let (fname,_,_,_,_) = func
    fname

let is_payable func =
    let (_,_,_,_,finfo) = func
    finfo.is_payable

let get_fnames cont =
    let (_,_,_,_,funcs,_) = cont
    List.map get_fname funcs

let get_cnstr cont =
    let (_,_,_,_,funcs,_) = cont
    let lst = List.filter (fun (_,_,_,_,finfo) -> finfo.is_constructor) funcs
    assert (List.length lst = 1)
    List.head lst

let gen_func fname par ret_params stmt finfo =
    (fname, par, ret_params, stmt, finfo)

let update_cinfo cinfo cont =
    let (cid,decls,structs,enums,funcs,_) = cont
    (cid,decls,structs,enums,funcs,cinfo)

let update_enums enums cont =
    let (cid,decls,structs,_,funcs,cinfo) = cont
    (cid,decls,structs,enums,funcs,cinfo)

let update_structs structs cont =
    let (cid,decls,_,enums,funcs,cinfo) = cont
    (cid,decls,structs,enums,funcs,cinfo)

let update_funcs funcs cont =
    let (cid,decls,structs,enums,_,cinfo) = cont
    (cid,decls,structs,enums,funcs,cinfo)

(* include itself *)
let get_inherit_order cont =
    let (_,_,_,_,_,cinfo) = cont
    cinfo.inherit_order

let is_library_kind cont =
    let (_,_,_,_,_,cinfo) = cont
    cinfo.ckind = "library"

let is_interface_kind cont =
    let (_,_,_,_,_,cinfo) = cont
    cinfo.ckind = "interface"

let is_contract_kind cont =
    let (_,_,_,_,_,cinfo) = cont
    cinfo.ckind = "contract"

let get_stmts func =
    let (_,_,_,stmt,_) = func
    stmt

let get_finfo func =
    let (_,_,_,_,finfo) = func
    finfo

let get_mod_calls func =
    let (_,_,_,_,finfo) = func
    finfo.mod_list

let get_vis func = 
    (get_finfo func).fvis

let is_public = function 
  | Public -> true | _ -> false

let is_external = function
  | External -> true | _ -> false

let is_internal = function 
  | Internal -> true | _ -> false

let is_private = function
  | Private -> true | _ -> false

let is_public_func func =
    is_public (get_vis func)

let is_external_func func =
    is_external (get_vis func)

let is_internal_func func =
    is_internal (get_vis func)

let is_private_func func =
    is_private (get_vis func)

let get_mutability func =
    (get_finfo func).mutability

let is_view_pure_f func =
  let mut = get_mutability func in
  mut = View || mut = Pure

let update_finfo finfo func =
    let (fname,par,ret_params,stmt,_) = func
    (fname, par, ret_params, stmt, finfo)

let is_constructor func =
    (get_finfo func).is_constructor

let is_modifier func =
    (get_finfo func).is_modifier

let get_body func =
    let (_,_,_,stmt,_) = func
    stmt

let update_body stmt func =
    let (fname,par,ret_params,_,finfo) = func
    (fname, par, ret_params, stmt, finfo)

let update_fname id func =
    let (_,par,ret_params,stmt,finfo) = func
    (id, par, ret_params, stmt, finfo)

let modify_contract cont pgm =
    let cname = get_cname cont 
    List.map (fun c' -> if cname = get_cname c' then cont else c') pgm

let get_cfg func =
    (get_finfo func).cfg

let update_cfg func cfg =
    let finfo = get_finfo func
    update_finfo {finfo with cfg = cfg} func

let is_outer_pred_of_lh node cfg =
    cfg.outpreds_of_lh.Contains node

let is_loophead node cfg =
    cfg.lh_set.Contains node

let is_loopexit node cfg =
    cfg.lx_set.Contains node

let is_continue_node node cfg =
    cfg.continue_set.Contains node

let is_break_node node cfg =
    cfg.break_set.Contains node

let is_callnode node cfg =
    match find_stmt node cfg with
    | Call _ -> true
    | _ -> false

let extcall = Call (None, Lv (Var ("@extern", dummy_vinfo)), [], None, None, dummy_loc, -1)

let is_external_call stmt =
    match stmt with
    | Call (_,Lv (Var ("@extern",_)),_,_,_,_,_) -> true
    | _ -> false

let is_extern_log_stmt stmt =
    match stmt with
    | Call (_,Lv (Var ("@extern_log",_)),_,_,_,_,_) -> true
    | _ -> false

let is_extern_log_node node cfg =
    match find_stmt node cfg with
    | Call (_,Lv (Var ("@extern_log",_)),_,_,_,_,_) -> true
    | _ -> false

let get_fname_extern_log_stmt stmt =
    match stmt with
    | Call (_,Lv (Var ("@extern_log",_)),Lv (Var (fname,_))::args,_,_,_,_) -> fname
    | _ -> assert false; exit 1

let get_fname_extern_log_node node cfg =
    match find_stmt node cfg with
    | Call (_,Lv (Var ("@extern_log",_)),Lv (Var (fname,_))::args,_,_,_,_) -> fname
    | _ -> assert false; exit 1

let is_skip_node node cfg =
    match find_stmt node cfg with
    | Skip -> true
    | _ -> false

let is_exception_node node cfg =
    match find_stmt node cfg with
    | Throw -> true
    | Call (lvop, Lv (Var ("revert",_)),args,_,_,_,_) -> true
    | _ -> false

let is_assign_node node cfg =
    match find_stmt node cfg with
    | Assign _ -> true
    | _ -> false

let is_entry node =
    match node with
    | Node.ENTRY -> true
    | _ -> false

let is_exit node =
    match node with
    | Node.EXIT -> true
    | _ -> false

let is_uintkind typ =
    match typ with
    | EType (UInt _) -> true
    | _ -> false

let is_uint256 typ =
  match typ with
  | EType (UInt 256) -> true
  | _ -> false

let is_sintkind typ =
    match typ with
    | EType (SInt _) -> true
    | _ -> false

let is_mapping typ =
    match typ with
    | Mapping _ -> true
    | _ -> false

let is_mapping2 typ =
    match typ with
    | Mapping2 _ -> true
    | _ -> false

let is_usual_mapping typ =
    match typ with
    | Mapping (Address, EType (UInt 256)) -> true
    | _ -> false

let is_usual_allowance typ =
    match typ with
    | Mapping (Address, Mapping (Address, EType (UInt 256))) -> true
    | _ -> false

let is_bool typ =
    match typ with
    | EType Bool -> true
    | _ -> false

let is_address typ =
    match typ with
    | EType Address -> true
    | _ -> false

let is_array typ =
    match typ with
    | Array _ -> true
    | _ -> false

let is_static_array typ =
    match typ with
    | Array (_,Some _) -> true
    | _ -> false

let get_array_size typ =
    match typ with
    | Array (_,Some n) -> Some n
    | Array (_,None) -> None
    | _ -> raise (Failure "get_array_size")

let is_dynamic_array typ =
    match typ with
    | Array (_,None) -> true
    | _ -> false

let is_struct typ =
    match typ with
    | Struct _ -> true
    | _ -> false

let is_contract typ =
    match typ with
    | Contract _ -> true
    | _ -> false

let is_enum typ =
    match typ with
    | Enum _ -> true
    | _ -> false

let is_elemtyp typ =
    match typ with
    | EType _ -> true
    | _ -> false

let is_dbytes typ =
    match typ with
    | EType DBytes -> true
    | _ -> false

let is_bytes typ =
    match typ with
    | EType (Bytes _) -> true
    | _ -> false

let is_bytekind typ =
    is_dbytes typ || is_bytes typ

let is_const_int typ =
    match typ with
    | ConstInt -> true
    | _ -> false

let is_uintkind_or_constint typ =
    is_uintkind typ || is_const_int typ

let is_const_string typ =
    match typ with
    | ConstString -> true
    | _ -> false

let is_string typ =
    match typ with
    | EType String -> true
    | _ -> false

let is_tuple typ =
    match typ with
    | TupleType _ -> true
    | _ -> false

let is_void typ =
    match typ with
    | Void -> true
    | _ -> false

let domain_typ typ =
    match typ with
    | Array _ -> EType (UInt 256) 
    | Mapping (et,_) -> EType et
    | Mapping2 (t,_) -> t
    | EType DBytes -> EType (UInt 256)
    | EType (Bytes _) -> EType (UInt 256)
    | _ -> failwith "domain_typ"

let range_typ typ =
    match typ with
    | Array (t,_) -> t
    | Mapping (_,t) -> t
    | Mapping2 (_,t) -> t
    | EType DBytes -> EType (Bytes 1)
    | EType (Bytes _) -> EType (Bytes 1)
    | _ -> failwith "range_typ"

let tuple_elem_typs typ =
    match typ with
    | TupleType lst -> lst
    | _ -> failwith "tuple_elem_typs"

let get_bytes_size typ =
    match typ with
    | EType (Bytes n) -> n
    | _ -> failwith "get_bytes_size"

let exp_to_lv exp =
    match exp with
    | Lv lv -> lv
    | _ -> raise (Failure "exp_to_lv")

let get_name_userdef typ =
    match typ with
    | Struct lst -> String.string_of_list (Vocab.id, lst, "", "", ".")
    | Enum s -> s
    | Contract s -> s
    | _ -> raise (Failure "get_name_userdef")

let get_type_var var =
    snd var

let get_type_var2 (_, vinfo) =
    vinfo.vtyp

let get_type_lv lv =
    match lv with
    | Var (_,vinfo) -> vinfo.vtyp
    | MemberAccess (_,_,_,typ) -> typ 
    | IndexAccess (_,_,typ) -> typ 
    | Tuple (_, typ) -> typ

let get_type_exp exp =
    match exp with
    | Int _ -> ConstInt
    | Real _ -> ConstReal
    | Str _ -> ConstString
    | Lv lv -> get_type_lv lv 
    | Cast (typ,_) -> typ
    | BinOp (_,_,_,einfo) -> einfo.etyp
    | UnOp (_,_,typ) -> typ
    | True | False -> EType Bool
    | ETypeName etyp -> EType etyp
    | _ -> raise (Failure "get_type_exp")

let get_type_array_elem typ =
    match typ with
    | Array (t,_) -> t
    | _ -> raise (Failure "get_type_array_elem")

let get_int exp =
    match exp with
    | Int n -> int n
    | _ -> raise (Failure "get_int")

let get_bigint exp =
    match exp with
    | Int n -> n
    | _ -> raise (Failure "get_bigint")

let big_lt = (<)
let big_neg = BigInteger.Negate
let big_ge = (>=)
let big_pow n1 n2 = BigInteger.Pow (int n1, int n2)

let rec bit_unsigned_of_int n bit =
    assert (bit <= 256)
    if big_lt n (big_pow 2 bit) then bit
    else bit_unsigned_of_int n (bit+8)

let rec bit_signed_of_int n bit =
    assert (bit <= 256)
    if big_ge n (big_neg (big_pow 2 (bit-1))) && big_lt n (big_pow 2 (bit-1)) then bit
    else bit_signed_of_int n (bit+8)

let is_supported_mapping typ =
    match typ with
    | Mapping (Address, EType Address)
    | Mapping (Address, EType (UInt _))
    | Mapping (Address, EType Bool)
    | Mapping (UInt _, EType Address)
    | Mapping (UInt _, EType (UInt _))
    | Mapping (Address, Mapping (Address, EType (UInt _))) -> true
    | Mapping _ -> false
    | _ -> assert false; exit 1

let is_skip stmt =
    match stmt with
    | Skip -> true
    | _ -> false

let rec is_skip_in_stmt stmt =
    match stmt with
    | Skip -> true
    | Seq (s1, s2) -> is_skip_in_stmt s1 || is_skip_in_stmt s2
    | While (_, s) -> is_skip_in_stmt s
    | _ -> false

let rec is_throw_in_stmt stmt =
    match stmt with
    | Throw -> true
    | Seq (s1, s2) -> is_throw_in_stmt s1 || is_throw_in_stmt s2
    | While (_ ,s) -> is_throw_in_stmt s
    | _ -> false

let get_params (_,par,_,_,_) = par
let get_param_vars (_,par,_,_,_) = List.map (fun (v,vinfo)-> (v,vinfo.vtyp)) par
let get_param_types (_,par,_,_,_) = List.map (fun p -> (snd p).vtyp) par
let get_ret_params (_,_,ret_params,_,_) = ret_params
let get_ret_param_types (_,_,ret_params,_,_) = List.map (fun p -> (snd p).vtyp) ret_params 

let get_fsig func =  (get_fname func, get_param_types func)

let equal_sig f1 f2 =
    let (sig1, sig2) = (get_fsig f1, get_fsig f2) 
    try sig1 = sig2 with | _ -> false

let get_fkey f = ((get_finfo f).scope_s, get_fname f, get_param_types f)

let get_func_decl func =
    let (fname,par,ret_params,_,_) = func
    (fname, List.map (fun (x,xinfo) -> (x,xinfo.vtyp)) par, List.map (fun (x,xinfo) -> (x,xinfo.vtyp)) ret_params)

let get_all_fkeys_c cont =
    get_funcs cont |> List.map get_fkey |> Set.ofList

let get_all_fkeys pgm =
    pgm |> List.fold (fun acc c -> Set.union (get_all_fkeys_c c) acc) Set.empty 

(******************************)
(******************************)
(***** Tostring Functions *****)
(******************************)
(******************************)

let rec to_string_exp arg =
    let rec to_string_exp_inner report exp =
        match exp with
        | Int n -> n.ToString()
        | Real n -> n.ToString()
        | Str s ->
            if Options.cfg then "\\\"" + s.Replace("\n", "") + "\\\""
            else "\"" + s.Replace("\n", "") + "\""
        | Lv lv -> to_string_lv (ToStringArg.ReportandLv (report, lv))
        | Cast (typ, e) -> to_string_typ typ + "(" + to_string_exp_inner report e + ")"
        | BinOp (bop, e1, e2, _) -> "(" + to_string_exp_inner report e1 + " " + to_string_bop bop + " " + to_string_exp_inner report e2 + ")"
        | UnOp (uop,e,_) -> "(" + to_string_uop uop + to_string_exp_inner report e + ")" 
        | True -> "true"
        | False -> "false"
        | ETypeName etyp -> to_string_etyp etyp
        | IncTemp (e,prefix,_) -> 
            if prefix then "++" + to_string_exp_inner false e
            else to_string_exp_inner false e + "++"
        | DecTemp (e,prefix,_) ->
            if prefix then "--" + to_string_exp_inner false e
            else to_string_exp_inner false e + "--"
        | CondTemp (e1,e2,e3,_,_) -> 
            "(" + to_string_exp_inner false e1 + " ? " + to_string_exp_inner false e2 + " : " + to_string_exp_inner false e3 + ")"
        | AssignTemp (lv,e,_) -> 
            "(" + to_string_lv (ToStringArg.Singlelv lv) + " = " + to_string_exp_inner false e + ")"
        | CallTemp (e,args,ethop,gasop,_) ->
            to_string_exp_inner report e +
            (match ethop with None -> "" | Some e -> ".value(" + to_string_exp_inner report e + ")") +
            (match gasop with None -> "" | Some e -> ".gas(" + to_string_exp_inner report e + ")") +
            (String.string_of_list ((to_string_exp_inner report), args, "(", ")", ", "))
    match arg with
    | SingleExp e -> to_string_exp_inner false e
    | ReportandExp (report, e) -> to_string_exp_inner report e
    | SingleExpOpt e -> 
        match e with
        | Some e -> to_string_exp_inner false e
        | None -> " "
    | _ ->
        raise (Failure "to_string_exp")
    
and to_string_exp_opt arg =
    let rec to_string_exp_opt_inner report exp =
        match exp with
        | Some e -> to_string_exp (ToStringArg.ReportandExp (report, e))
        | None -> " "
    match arg with
    | SingleExpOpt e -> to_string_exp_opt_inner false e
    | ReportandExpOpt (report, e) -> to_string_exp_opt_inner report e
    | _ -> raise (Failure "to_string_exp_opt")

and to_string_bop bop =
    match bop with
    | Add -> "+" | Sub -> "-" 
    | Mul -> "*" | Div -> "/" 
    | Mod -> "%" | Exponent -> "**"
    | GEq -> ">=" | Gt -> ">"  
    | LEq -> "<=" | Lt -> "<"
    | LAnd -> "&&" | LOr -> "||"
    | Eq -> "==" | NEq -> "!="
    | ShiftL -> "<<" | ShiftR -> ">>" 
    | BXor -> "^" | BAnd -> "&" 
    | BOr -> "|"

and to_string_uop uop =
    match uop with
    | Pos -> "+"
    | Neg -> "-"
    | LNot -> "!"
    | BNot -> "~"

and to_string_lv (arg: ToStringArg) =
    let to_string_lv_inner report lv =
        match lv with
        | Var (x,xinfo) -> if not report then x else x + to_string_vinfo_org (ToStringArg.ReportandIdandExpOpt (report, x, xinfo.org))
        | MemberAccess (e,x,xinfo,_) -> (to_string_exp (ToStringArg.ReportandExp (report, e))) + "." + (if not report then x else x + to_string_vinfo_org (ToStringArg.ReportandIdandExpOpt (report, x, xinfo.org)))
        | IndexAccess (e,None,_) -> to_string_exp (ToStringArg.ReportandExp (report, e)) + "[]"
        | IndexAccess (e1,Some e2,_) -> to_string_exp (ToStringArg.ReportandExp (report, e1)) + "[" + to_string_exp (ToStringArg.ReportandExp(report, e2)) + "]"
        | Tuple (elst, t) ->
            let expOptList lst = lst |> List.map (fun e -> ToStringArg.SingleExpOpt e) 
            let elst' = expOptList elst
            if is_array t then
                String.string_of_list((to_string_exp_opt), elst', "[", "]", ", ")
            else String.string_of_list((to_string_exp_opt), elst', "(", ")", ", ")
    match arg with
    | Singlelv lv -> to_string_lv_inner false lv
    | ReportandLv (report, lv) -> to_string_lv_inner report lv
    | _ -> raise (Failure "to_string_lv")

and to_string_vinfo_org (args: ToStringArg) =
    let to_string_vinfo_org_inner report (x: id) (org: exp option) =
        match org with
        | None -> x
        | Some e -> to_string_exp (ToStringArg.ReportandExp (report, e))
    match args with
    | ReportandIdandExpOpt (report, x, org) -> to_string_vinfo_org_inner report x org
    | _ -> raise (Failure "to_string_vinfo_org")


and to_string_typ typ =
    match typ with
    | ConstInt -> "int_const"
    | ConstReal -> "rational_const"
    | ConstString -> "literal_string"
    | EType etyp -> to_string_etyp etyp
    | Mapping (etyp,typ) -> "mapping" + "(" + to_string_etyp etyp + " => " + to_string_typ typ + ")"
    | Mapping2 (t1,t2) -> "mapping2" + "(" + to_string_typ t1 + " => " + to_string_typ t2 + ")"
    | Array (typ,None) -> to_string_typ typ + "[]"
    | Array (typ,Some n) -> to_string_typ typ + "[" + n.ToString() + "]"
    | Void -> "void"
    (* add 'contract ' or 'struct ' for compatibility with Translator.trans_str_to_typeName *)
    | Contract id -> "contract " + id
    | Struct lst -> "struct " + String.string_of_list(Vocab.id, lst, "", "", ".")
    | Enum id -> id
    | TupleType typs -> "Tuple" + String.string_of_list(to_string_typ, typs, "(", ")", ", ")

and to_string_etyp elem_typ =
    match elem_typ with
    | Address -> "address"
    | Bool -> "bool"
    | String -> "string"
    | UInt n -> "uint" + n.ToString()
    | SInt n -> "int" + n.ToString()
    | Bytes n -> "bytes" + n.ToString()
    | DBytes -> "dbytes" 

and to_string_stmt arg =
    let rec to_string_stmt_inner report stmt =
        match stmt with
        | Assign (lv,e,_) -> to_string_lv (ToStringArg.ReportandLv (report, lv)) + " = " + to_string_exp (ToStringArg.ReportandExp (report, e)) + ";"
        | Decl lv -> to_string_typ (get_type_lv lv) + " " + to_string_lv (ToStringArg.Singlelv lv) + ";"
        | Seq (s1,s2) -> to_string_stmt_inner report s1 + "" + "\n" + "    " + to_string_stmt_inner report s2
        | Call (None, e, exps, ethop, gasop, _, _) ->
            let expOptList lst = lst |> List.map (fun e -> ToStringArg.SingleExp e) 
            let exps' = expOptList exps
            to_string_exp (ToStringArg.ReportandExp (report, e)) +
            (match ethop with None -> "" | Some e -> ".value(" + to_string_exp (ToStringArg.ReportandExp (report, e)) + ")") +
            (match gasop with None -> "" | Some e -> ".gas(" + to_string_exp (ToStringArg.ReportandExp (report, e)) + ")") +
            String.string_of_list((to_string_exp), exps', "(", ")", ", ") + ";"
        | Call (Some lv, e, exps, ethop, gasop, _, _) ->
            let expOptList lst = lst |> List.map (fun e -> ToStringArg.SingleExp e)
            let exps' = expOptList exps
            if report && (to_string_lv (ToStringArg.Singlelv lv)).StartsWith "Tmp" then to_string_lv (ToStringArg.ReportandLv (report, lv))
            else
                to_string_lv (ToStringArg.ReportandLv (report, lv)) + " = " + to_string_exp (ToStringArg.ReportandExp (report, e)) +
                (match ethop with None -> "" | Some e -> ".value(" + to_string_exp (ToStringArg.ReportandExp (report, e)) + ")") +
                (match gasop with None -> "" | Some e -> ".gas(" + to_string_exp (ToStringArg.ReportandExp (report, e)) + ")") +
                String.string_of_list((to_string_exp), exps', "(", ")", ", ") + ";"
        | Skip -> "skip;"
        | If (e,s1,s2,_) ->
            "if" + "(" + to_string_exp (ToStringArg.ReportandExp (report, e)) + ")" + "{ " + to_string_stmt_inner report s1 + " }" + " " +
            "else" + "{ " + to_string_stmt_inner report s2 +  " }"
        | While (e,s) -> "while" + "(" + to_string_exp (ToStringArg.ReportandExp (report, e)) + ")" + "{" + to_string_stmt_inner report s + "}"
        | Break -> "break;"
        | Continue -> "continue;"
        | Return (None,_) -> "return;"
        | Return (Some e,_) -> "return " + to_string_exp (ToStringArg.ReportandExp (report, e)) + ";"
        | Throw -> "throw;"
        | Assume (e,_) -> "assume" + "(" + to_string_exp (ToStringArg.ReportandExp (report, e)) + ")" + ";"
        | Assert (e,_,_) -> "assert" + "(" + to_string_exp (ToStringArg.ReportandExp (report, e)) + ")" + ";"
        | Assembly (lst,_) ->
            let fst_to_id (t: (id * int)) = match t with | (x, _ ) -> x
            "assembly" + String.string_of_list ((fst_to_id), lst , "{" , "}" , ", ")  + ";"
        | PlaceHolder -> "_;"
        | Unchecked (lst,_) ->
            "unchecked {" + "\n" +
            (List.fold (fun acc s ->
                if acc = "" then "    " + to_string_stmt_inner report s
                else acc + "\n" + "    " + to_string_stmt_inner report s
            ) "" lst) + "\n" + "}"
    match arg with
    | SingleStmt s -> to_string_stmt_inner false s
    | ReportandStmt (report, s) -> to_string_stmt_inner report s
    | _ -> raise (Failure "to_string_stmt")
    
and to_string_func (id, par, ret_params, stmt, finfo) =
    "function" + " " + id + " " + to_string_params par +
    (if List.length finfo.mod_list2 > 0 then " " + to_string_mods finfo.mod_list2 else "") +
    (if List.length finfo.mod_list > 0 then " " + to_string_mods finfo.mod_list else "") +
    " " + "returns" + " " + to_string_params ret_params +
    " " + to_string_vis finfo.fvis +
    " " + (if finfo.is_payable then "payable" else "") + " " + "{" + "\n" +
    "    " + to_string_stmt stmt + "\n" + "  " + "}" + "\n"
 
and to_string_param (id, vinfo) = to_string_typ vinfo.vtyp + " " + id
and to_string_params par = String.string_of_list (to_string_param, par, "(", ")", ", ")
and to_string_exps (exps: exp list) =
    let expList lst = lst |> List.map (fun e -> ToStringArg.SingleExp e) 
    let exps' = expList exps
    String.string_of_list (to_string_exp, exps', "(", ")", ", ")
and to_string_mod (mod': mod_call) = 
    match mod' with
    | (id, exps, loc) -> if List.length exps = 0 then id else id + to_string_exps exps
and to_string_mods mods = String.string_of_list(to_string_mod, mods, "", "", " ")
and to_string_vis vis =
    match vis with
    | Public -> "public"
    | Internal -> "internal"
    | External -> "external"
    | Private -> "private"

let to_string_state_var_decl decl =
    match decl with
    | (id,None,vinfo) -> to_string_typ vinfo.vtyp + " " + id + ";"
    | (id,Some e,vinfo) ->
        match e with
        | SingleExpOpt None -> to_string_typ vinfo.vtyp + " " + id + ";"
        | _ -> to_string_typ vinfo.vtyp + " " + id + " = " + to_string_exp e + ";"

let to_string_var_decl = to_string_param

let to_string_structure (id,decls) =
  "struct" + " " + id + "{" + "\n" +
  (String.string_of_list (to_string_var_decl, decls , "    " , ";" , ";\n    ")) +
  "\n" + "  " + "}" + "\n"

let to_string_enum (id,mems) =
  "enum" + " " + id + (String.string_of_list (Vocab.id, mems, " {", "}", ", "))

let to_string_contract (id, decls, structs, enums, func_defs, _) =
    "contract" + " " + id + "{" + "\n" +
    (   if decls = [] then ""  
        else String.string_of_list (to_string_state_var_decl, decls, "  ", "\n\n", "\n  ")) +
    (   if structs = [] then ""
        else String.string_of_list (to_string_structure, structs, "  ", "\n\n", "\n  ")) +
    (   if enums = [] then ""
        else String.string_of_list (to_string_enum, enums, "  ", "\n\n", "\n  ")) +
        String.string_of_list (to_string_func, func_defs, "  ", "\n", "\n  ") + "}"

let to_string_pgm contracts =
    String.string_of_list (to_string_contract, contracts, "", "", "\n\n" )

let to_string_fsig (fname,typs) =
    fname + "," + String.string_of_list (to_string_typ, typs, "{", "}", ", ")

let to_string_fkey (cname,fname,typs) =
    "(" + cname + ", " + fname + ", " + (String.string_of_list (to_string_typ, typs, "[", "]", ", ")) + ")"

let to_string_fkey2 (cname,fname,typs) =
    "(" + cname + ", " + fname + ", " + (String.string_of_list (to_string_typ, typs, "[", "]", "_")) + ")"

let to_string_cfg name cfg =
    "digraph " + name + "{" + "\n" + "{" + "\n" + 
    "node [shape=box]" + "\n" +
    G.fold_vertex (fun acc v ->
        let str_v = Node.to_string v
        let stmt =  ToStringArg.SingleStmt (find_stmt v cfg) |> to_string_stmt
        let colored = 
            if is_loophead v cfg then " style=filled color=grey shape=oval" else
            if is_loopexit v cfg then " style=filled color=grey shape=diamond" else
            if is_callnode v cfg then " style=filled color=yellow" 
            else ""
        acc.ToString() + str_v + " [label=\"" + str_v + ": " + stmt + "\"" + colored + "]" + "\n"
    ) "" cfg.graph +
    "}" + "\n" +
    G.fold_edges (fun acc (v1, v2) ->
        acc + Node.to_string v1 + " -> " + Node.to_string v2 + "\n"
    ) "" cfg.graph 
    + "}" + "\n\n"

let to_string_cfg_f func = to_string_cfg (get_fname func) (get_cfg func)

let to_string_cfg_c contract =
    List.fold (fun acc f -> acc + to_string_cfg_f f) "" (get_funcs contract)

let to_string_cfg_p pgm =
    List.fold (fun acc c -> acc + to_string_cfg_c c) "" pgm

let to_string_path path =
    String.string_of_list (Node.to_string, path, "[", "]", " -> ")

let to_string_paths paths =
    String.string_of_set(to_string_path, paths, "{", "}", ",\n")

let print_path path =
    printfn "%s" (to_string_path path)

let print_paths paths =
    printfn "%s" (to_string_paths paths) 

(******************************)
(******************************)
(***** Built-in Functions *****)
(******************************)
(******************************)

let is_require exp =
    match exp with
    | Lv (Var ("require",_)) -> true
    | _ -> false

let is_assert exp =
    match exp with
    | Lv (Var ("assert",_)) -> true
    | _ -> false

let is_revert exp =
    match exp with
    | Lv (Var ("revert",_)) -> true
    | _ -> false

(***********************)
(***********************)
(***** Other Utils *****)
(***********************)
(***********************)

let rec replace_exp exp target replacement =
    match exp with
    | Int _ | Real _ | Str _ -> exp
    | Lv lv when exp = target -> replacement
    | Lv lv -> exp
    | Cast (typ,e) -> Cast (typ, replace_exp e target replacement)
    | BinOp (bop,e1,e2,einfo) -> BinOp (bop, replace_exp e1 target replacement, replace_exp e2 target replacement, einfo)
    | UnOp (uop,e,typ) -> UnOp (uop, replace_exp e target replacement, typ)
    | True | False -> exp
    | ETypeName _ -> exp
    | AssignTemp _
    | CondTemp _
    | IncTemp _
    | DecTemp _
    | CallTemp _ -> raise (Failure "replace_exp")

let equal_typ t1 t2 = t1 = t2

exception NoParameters

let params_to_lv par =
    if (List.length par = 1) then
        let (x,vinfo) = List.head par
        Var (x,vinfo) else 
    if (List.length par > 1) then
        let eops = List.map (fun (x,vinfo) -> Some (Lv (Var (x,vinfo)))) par 
        let tuple_typ = TupleType (List.map (fun (_,vinfo) -> vinfo.vtyp) par) 
        Tuple (eops,tuple_typ)
    else
        raise NoParameters

let args_to_exp args =
    if (List.length args = 1) then
        List.head args else
    if (List.length args > 1) then
        let eops = List.map (fun e -> Some e) args in
        let tuple_typ = TupleType (List.map get_type_exp args) in
        Lv (Tuple (eops,tuple_typ))
    else
        raise NoParameters

let keyword_vars =
    ["block.coinbase"; "block.difficulty"; "block.gaslimit"; 
    "block.number"; "block.timestamp"; "now";
    "msg.data"; "msg.data.length"; "msg.sender"; "msg.value"; "msg.gas"; "msg.sig";
    "this"; "tx.gasprice"; "tx.origin"]

let blk_keyword_vars =
    ["block.coinbase"; "block.difficulty"; "block.gaslimit"; "block.number"; "block.timestamp"; "now"]

let is_balance_keyword lv =
    match lv with
    | MemberAccess (e,id,_,_)
        when (is_address (get_type_exp e) || is_contract (get_type_exp e))
            && String.Equals (id, "balance")
        -> true
    | _ -> false

let init_funcs = ["array_init"; "dbytes_init"; "string_init"; "contract_init"; "struct_init"; "struct_init2"]

(* suicide is disallowed since solc 0.5.0 *)
let built_in_funcs =
    ["abi.encode"; "abi.decode"; "abi.encodePacked"; "abi.encodeWithSignature"; "abi.encodeWithSelector";
    "revert"; "keccak256"; "sha3"; "sha256"; "ripemd160"; "delete"; 
    "selfdestruct"; "suicide"; "ecrecover"; "addmod";
    "blockhash"; "block.blockhash"]

let max_256bit =
    let pow = BigInteger.Pow (BigInteger(2), 256) in
    let one = 1
    BigInteger.Subtract(pow, one)

let rec var_lv lv = 
    match lv with
    | Var (x,xinfo) -> Set.singleton (x,xinfo.vtyp)
    | MemberAccess (e,x,xinfo,_) -> Set.add (x,xinfo.vtyp) (var_exp e)
    | IndexAccess (e1,Some e2,_) -> Set.union (var_exp e1) (var_exp e2)
    | IndexAccess (e,None,_) -> var_exp e
    | Tuple (eops,_) ->
    List.fold (fun acc eop ->
        match eop with
        | None -> acc
        | Some e -> Set.union (var_exp e) acc
    ) Set.empty eops

and var_exp exp =
    match exp with
    | Int _ | Real _ | Str _ -> Set.empty
    | Lv lv ->
        let lv' = ToStringArg.Singlelv lv
        if  List.contains (to_string_lv lv') keyword_vars then
            Set.singleton (to_string_lv lv', get_type_lv lv)
        else var_lv lv
    | Cast (_,e) -> var_exp e
    | BinOp (_,e1,e2,_) -> Set.union (var_exp e1) (var_exp e2)
    | UnOp (_,e,_) -> var_exp e
    | True | False -> Set.empty
    | ETypeName _ -> Set.empty
    | _ -> failwith "var_exp: temp expressions encountered"

module OrderedType = 
    type t = BigInteger 
    let compare = BigInteger.Compare


module BigIntSet = 
    type t = Set<BigInteger>
    let empty = Set.empty
    let union = Set.union
    let singleton = Set.singleton
    let add = Set.add

let rec int_lv lv = 
    match lv with
    | Var _ -> BigIntSet.empty
    | MemberAccess (e,_,_,_) -> int_exp e
    | IndexAccess (e1,Some e2,_) -> BigIntSet.union (int_exp e1) (int_exp e2)
    | IndexAccess (e,None,_) -> int_exp e
    | Tuple (eops,_) ->
        List.fold (fun acc eop ->
            match eop with
            | None -> acc
            | Some e -> BigIntSet.union (int_exp e) acc
        ) BigIntSet.empty eops

and int_exp exp =
    match exp with
    | Int n -> BigIntSet.singleton n
    | Real _ | Str _ -> BigIntSet.empty
    | Lv lv -> int_lv lv
    | Cast (_,e) -> int_exp e
    | BinOp (_,e1,e2,_) -> BigIntSet.union (int_exp e1) (int_exp e2)
    | UnOp (_,e,_) -> int_exp e
    | True | False -> BigIntSet.empty
    | ETypeName _ -> BigIntSet.empty
    | _ -> failwith "int_exp: temp expressions encountered"


let preceding_typ t1 t2 =
    if t1=t2 then t1
    else
       (match t1,t2 with
        | EType String, ConstString -> t1
        | EType (UInt n1), EType (UInt n2) -> EType (UInt (max n1 n2))
        | EType (SInt n1), EType (SInt n2) -> EType (SInt (max n1 n2))
        | EType (SInt n1), EType (UInt n2) when n1>n2 -> t1
        | EType (SInt n1), EType (UInt n2) when n1<=n2 -> raise (Failure "preceding_typ : intX1 and uintX2 are not convertible if X1<=X2")
        | EType (UInt n1), EType (SInt n2) when n1<n2 -> t2
        | EType (UInt n1), EType (SInt n2) when n1>=n2 -> t1
        | ConstInt, EType Address -> t2
        | EType Address, ConstInt -> t1
        | Contract s, ConstInt -> t1 
        | EType Address, Contract s -> t1
        | Contract s, EType Address -> t2
        | EType (Bytes _), ConstInt -> t1
        | ConstInt, EType (Bytes _) -> t2
        | Array (t1,None), Array (t2, Some n) when t1=t2 -> Array (t1,None)
        | Contract id1, Contract id2 -> t2
        | ConstString, EType (Bytes _) -> t2
        | ConstString, EType DBytes -> t2
        | EType (Bytes _), ConstString -> t1
        | EType DBytes, ConstString -> t1
        | t1,t2 -> raise (Failure ("preceding_typ : " + (to_string_typ t1) + " vs. " + (to_string_typ t2))))

(* currently, casting is performed in the vc generation step. *)
let rec folding exp =
  match exp with
    | Int n -> Int n
    | BinOp (Add,Int n1,Int n2,einfo) -> Int (BigInteger.Add (n1, n2))
    | BinOp (Sub,Int n1,Int n2,einfo) -> Int (BigInteger.Subtract (n1, n2))
    | BinOp (Mul,Int n1,Int n2,einfo) -> Int (BigInteger.Multiply (n1, n2))
    | BinOp (Div,Int n1,Int n2,einfo) -> Int (BigInteger.Divide (n1, n2))
    | BinOp (Mod,Int n1,Int n2,einfo) -> Int (n1 % n2)
    | BinOp (Exponent,Int n1,Int n2,einfo) -> Int (BigInteger.Pow (n1, int n2))
    | BinOp (bop,e1,e2,einfo) -> BinOp (bop, folding e1, folding e2, einfo) 
    | _ -> failwith "folding"

let rec constant_folding exp =
    let exp' = folding exp 
    let exp1 = ToStringArg.SingleExp exp
    let exp2 = ToStringArg.SingleExp exp'
    if String.Equals ((to_string_exp exp1), (to_string_exp exp2)) then exp'
    else constant_folding exp'

let common_typ e1 e2 =
    let t1, t2 = get_type_exp e1, get_type_exp e2 
    if t1 = t2 then t1 
    else
    (match t1,t2 with
    | ConstInt, EType (UInt n) ->
        let n' = bit_unsigned_of_int (get_bigint (constant_folding e1)) 8 in
        EType (UInt (max n n'))
    | EType (UInt n), ConstInt ->
        let n' = bit_unsigned_of_int (get_bigint (constant_folding e2)) 8 in
        EType (UInt (max n n'))
    | ConstInt, EType (SInt n) ->
        let n' = bit_signed_of_int (get_bigint (constant_folding e1)) 8 in
        EType (SInt (max n n'))
    | EType (SInt n), ConstInt ->
        let n' = bit_signed_of_int (get_bigint (constant_folding e2)) 8 in
        EType (SInt (max n n'))
    | _ -> preceding_typ t1 t2)


let mk_einfo t = {eloc=dummy_loc; etyp=t; eid=(-1)}

let mk_finfo c =
    {is_constructor = false;
    is_payable = false;
    is_modifier = false;
    mod_list = [];
    mod_list2 = []; (* modifier by inheritance *)
    param_loc = dummy_loc;
    ret_param_loc = dummy_loc;
    fvis = Public;
    mutability = NonPayable;
    fid = (-1);
    floc = dummy_loc;
    scope = (get_cinfo c).numid;
    scope_s = get_cname c;
    org_scope_s = get_cname c;
    cfg = empty_cfg}

let mk_index_access e1 e2 =
    let _ = assert (is_usual_mapping (get_type_exp e1) || is_usual_allowance (get_type_exp e1)) in
    let _ = assert (is_address (get_type_exp e2)) in
    Lv (IndexAccess (e1, Some e2, range_typ (get_type_exp e1)))

let mk_member_access exp var =
    let (x, t) = var
    let vinfo' = {Loc = Some dummy_loc; TypeStr = Some "uint256"; Typ = Some t; Org = None} |> mk_vinfo
    Lv (MemberAccess (exp, x, vinfo', t))

let mk_eq   e1 e2 =
    BinOp (Eq, e1, e2, mk_einfo (EType Bool))

let mk_neq  e1 e2 =
    BinOp (NEq, e1, e2, mk_einfo (EType Bool)) 

let mk_ge   e1 e2 =
    BinOp (GEq, e1, e2, mk_einfo (EType Bool))

let mk_gt   e1 e2 = 
    BinOp (Gt, e1, e2, mk_einfo (EType Bool))

let mk_and  e1 e2 =
    assert (is_bool (get_type_exp e1)) 
    assert (is_bool (get_type_exp e2))
    BinOp (LAnd, e1, e2, mk_einfo (EType Bool))

let mk_or   e1 e2 =
    assert (is_bool (get_type_exp e1)) 
    assert (is_bool (get_type_exp e2))
    BinOp (LOr, e1, e2, mk_einfo (EType Bool))

let mk_add  e1 e2 =
    BinOp (Add, e1, e2, mk_einfo (common_typ e1 e2))

let mk_sub  e1 e2 =
    BinOp (Sub, e1, e2, mk_einfo (common_typ e1 e2))

let mk_mul  e1 e2 =
    BinOp (Mul, e1, e2, mk_einfo (common_typ e1 e2))

let mk_div  e1 e2 =
    BinOp (Div, e1, e2, mk_einfo (common_typ e1 e2))

let mk_not e =
    UnOp (LNot, e, EType Bool)

(* rename local variables  with given labels *)
let rec rename_lv lab gvars lv =
    match lv with
    | Var (x,xinfo) ->
        if List.contains (x,xinfo.vtyp) gvars then lv
        else if List.contains x ["@TU"; "@Invest"; "@Invest_sum"; "@extern_called"; "@CA"] then lv
        else Var (x + lab, xinfo)
    | MemberAccess (e,x,xinfo,typ) when is_enum typ -> lv
    | MemberAccess (e,x,xinfo,typ) -> MemberAccess (rename_e lab gvars e, x, xinfo, typ)
    | IndexAccess (e,None,_) -> failwith "rename_lv"
    | IndexAccess (e1,Some e2,typ) -> IndexAccess (rename_e lab gvars e1, Some (rename_e lab gvars e2), typ)
    | Tuple (eoplst,typ) ->
    let eoplst' =
        List.map (fun eop ->
        match eop with
        | None -> None
        | Some e -> Some (rename_e lab gvars e)
        ) eoplst
    in
    Tuple (eoplst',typ)

and rename_e lab gvars exp =
    match exp with
    | Int _ | Real _ | Str _ -> exp
    | Lv lv ->
        let lv' = ToStringArg.Singlelv lv
        if List.contains (to_string_lv lv') keyword_vars || to_string_lv lv' = "abi" then exp
        else Lv (rename_lv lab gvars lv)
    | Cast (typ,e) -> Cast (typ, rename_e lab gvars e)
    | BinOp (bop,e1,e2,einfo) ->
    BinOp (bop, rename_e lab gvars e1, rename_e lab gvars e2, einfo)
    | UnOp (uop,e,typ) -> UnOp (uop, rename_e lab gvars e, typ)
    | True | False -> exp
    | ETypeName _ -> exp
    | IncTemp _ | DecTemp _ | CallTemp _ | CondTemp _ | AssignTemp _ -> failwith "rename_e"

let rec rename_stmt lab gvars cnames stmt =
    match stmt with
    | Assign (lv,e,loc) ->  Assign (rename_lv lab gvars lv, rename_e lab gvars e, loc)
    | Decl lv -> Decl (rename_lv lab gvars lv)
    | Call (lvop, (Lv (Var ("@extern_log",_)) as e), args,ethop,gasop,loc,site) ->
        let args' = (List.head args)::(List.map (rename_e lab gvars) (List.tail args))
        Call (lvop,e,args',ethop,gasop,loc,site)
    | Call (lvop,e,args,ethop,gasop,loc,site) ->
        let lvop' = match lvop with None -> lvop | Some lv -> Some (rename_lv lab gvars lv)
        let e' =
            match e with (* rename only for contract object cases *)
            | Lv (MemberAccess (Lv (Var (x,xinfo)) as obj, fname, fname_info, typ)) ->
            if List.contains x cnames || x = "super" then e (* static call *)
            else Lv (MemberAccess (rename_e lab gvars obj, fname, fname_info, typ))
            | _ -> e (* built-in functions, static call without prefixes *)
  
        let args' =
            let e' = ToStringArg.SingleExp e
            if to_string_exp e' = "struct_init" || to_string_exp e' = "contract_init" then
                (* the first arg is struct/contract name; see preprocess.ml *)
                (List.head args)::(List.map (rename_e lab gvars) (List.tail args))
            else List.map (rename_e lab gvars) args
        let ethop' = match ethop with None -> ethop | Some e -> Some (rename_e lab gvars e) 
        let gasop' = match gasop with None -> gasop | Some e -> Some (rename_e lab gvars e)
        Call (lvop',e',args',ethop',gasop',loc,site)
    | Skip -> stmt
    | Return (None,_) -> stmt
    | Return (Some e,loc) -> Return (Some (rename_e lab gvars e), loc)
    | Throw -> stmt
    | Assume (e,loc) -> Assume (rename_e lab gvars e, loc)
    | Assert (e,vtyp,loc) -> Assert (rename_e lab gvars e, vtyp, loc)
    | Assembly (lst,loc) ->
        let gnames = List.map fst gvars in
        let lst' =
            List.map (fun (x,refid) ->
            if List.contains x gnames then (x,refid)
            else (x + lab, refid)
            ) lst
        Assembly (lst',loc)
    | If (e,s1,s2,i) -> If (rename_e lab gvars e, rename_stmt lab gvars cnames s1, rename_stmt lab gvars cnames s2, i)
    | Seq (s1,s2) -> Seq (rename_stmt lab gvars cnames s1, rename_stmt lab gvars cnames s2)
    | While (e,s) -> While (rename_e lab gvars e, rename_stmt lab gvars cnames s)
    | Break | Continue | PlaceHolder -> stmt
    | Unchecked (lst,loc) ->
        let lst' = List.map (rename_stmt lab gvars cnames) lst in
        Unchecked (lst', loc)

let no_eth_gas_modifiers stmt =
    match stmt with
    | Call (_,_,_,None,None,_,_) -> true
    | Call _ -> false
    | _ -> failwith "no_eth_gas_modifiers"

let mutable tmpvar_cnt = 0
let tmpvar = "Tmp"

type GenTmpVarArg = {
    Org: exp option option
    Loc: int option
    Typ: typ
    TypeStr: string
}

let gen_tmpvar {Org = org; Loc = loc; Typ = typ; TypeStr = typestr} =
    let (org, loc) = (defaultArg org None, defaultArg loc -1)
    tmpvar_cnt <- tmpvar_cnt + 1
    let loc' = {Line = Some loc; FinishLine = Some loc; Offset = None; Len = None} |> mk_loc 
    let vinfo' = {MkVinfoArg.Loc = Some loc'; MkVinfoArg.TypeStr = Some typestr; MkVinfoArg.Typ = Some typ; MkVinfoArg.Org = Some org} |> mk_vinfo
    Var (tmpvar + (tmpvar_cnt.ToString()), vinfo')


let ca = (* used in exploit mode *)
    let mk_vinfo_pars1 = {MkVinfoArg.Loc = None; TypeStr = Some "address"; Typ = Some (EType Address); Org = None}
    let msg_sender = Lv (Var ("msg.sender", (mk_vinfo mk_vinfo_pars1)))
    let mk_vinfo_pars2 = {MkVinfoArg.Loc = None; TypeStr = Some "address"; Typ = Some (EType Address); Org = Some (Some msg_sender)}
    ("@CA", mk_vinfo mk_vinfo_pars2)

let transform pgm =
    pgm |> List.map (fun (s, idExpVInfoList, structures, enums, fnameIdVInfoList, cinfo) ->
        let s' = string s
        let idExpVInfoList' = idExpVInfoList |> List.map (fun (id, exp, vinfo) ->
            let (id', exp') = (string id, Some (ToStringArg.SingleExpOpt exp))
            (id', exp', vinfo)
        )
        let structures' = structures |> List.map (fun (id, fields) ->
            let id' = string id
            let fields' = fields |> List.map (fun (id, vinfo) -> 
                let id' = string id
                (id', vinfo)
            )
            (id', fields')
        )
        let enums' = enums |> List.map (fun (id, members) ->
            let id' = string id 
            let members' = members |> List.map (fun id -> string id)
            (id', members')
        )
        let fnameIdVInfoList' = fnameIdVInfoList |> List.map (fun (fname, idVInfoList, pars, stmt, finfo) ->
            let fname' = string fname
            let idVInfoList' = idVInfoList |> List.map (fun (id, vinfo) ->
                let id' = string id
                (id', vinfo)
            )
            let pars' = pars |> List.map (fun (id, vinfo) ->
                let id' = string id
                (id', vinfo)
            )
            let stmt' = ToStringArg.SingleStmt stmt
            (fname', idVInfoList', pars', stmt', finfo)
        )
        (s', idExpVInfoList', structures', enums', fnameIdVInfoList', cinfo)
    )