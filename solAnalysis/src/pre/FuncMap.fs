module solAnalysis.FuncMap

open System.Collections.Generic
open FSharp.Data
open Lang
open Vocab
open Options


let rec is_implicitly_convertible my_typ comp_typ =
  if my_typ = comp_typ then true
  else
    (match my_typ, comp_typ with
     | ConstInt, EType (UInt n) -> true
     | ConstInt, Struct _ -> false
     | EType (UInt n1), EType (UInt n2) -> n1<=n2 
     | ConstInt, EType (SInt n) -> true
     | EType (SInt n1), EType (SInt n2) -> n1<=n2
     | EType (SInt _), EType (UInt _) -> false (* negative numbers cannot be unsigned numbers *) 
     | ConstInt, EType Address -> true
     | ConstInt, EType String -> false
     | ConstInt, Array _ -> false
     | Contract _, EType Address ->
       (* true for 0.4x, false for later versions *)
       if Options.solc_ver.StartsWith "0.4" then true
       else false
     | Contract _, EType (Bytes _) -> false
     | Contract _, EType DBytes -> false
     | ConstString, EType (Bytes _) -> true
     | ConstString, EType DBytes -> true
     | ConstString, EType String -> true
     | ConstString, Array (EType String, _) -> false
     | ConstString, Array (EType DBytes, _) -> false
     | ConstString, EType (UInt _) -> false
     | ConstString, Contract _ -> false
     | ConstString, EType Address -> false
     | EType String, EType DBytes -> false
     | EType String, EType (Bytes _) -> false
     | EType String, Struct _ -> false
     | Struct _, EType String -> false
     | EType DBytes, EType String -> false
     | EType (Bytes n1), EType (Bytes n2) -> n1<=n2
     | EType (Bytes _), EType String -> false
     | EType (Bytes _), EType DBytes -> false
     | EType (Bytes _), Contract _ -> false
     | EType DBytes, EType (Bytes _) -> false
     | EType DBytes, EType Address -> false
     | EType Address, Contract _ -> false
     | EType Address, Enum _ -> false 
     | EType (UInt n), EType Address ->
       if Options.solc_ver.StartsWith "0.4" then
         if n<=160 then true else false
       else false
     | EType Address, EType (UInt n) -> false 
     | EType (SInt n), EType Address -> false 
     | EType Address, EType (SInt n) -> false
     | EType Address, Array _ -> false
     | Array _, EType Address -> false
     | EType (UInt  _), EType String -> false
     | EType String, EType (UInt _) -> false
     | EType DBytes, EType (UInt _) -> false
     | Array (t1, Some n1), Array (t2, Some n2) when n1=n2 -> is_implicitly_convertible t1 t2
     | Array (t1, None), Array (t2, None) -> is_implicitly_convertible t1 t2
     | Array _, Array _ -> false
     | Struct lst1, Struct lst2 ->
       if not (List.length lst1 = List.length lst2) then false
       else List.forall2 (fun i1 i2 -> i1=i2) lst1 lst2
     | Contract _, EType (UInt _) -> false 
     | EType (Bytes _), Struct _ -> false
     | Struct _, EType (UInt _) -> false
     | Struct _, EType (SInt _) -> false
     | EType (UInt _), Struct _ -> false
     | EType (UInt _), Contract _ -> false
     | Enum id1, Enum id2 -> String.Equals (id1, id2)
     | Enum _, EType Address -> false
     | Struct _, EType Address -> false
     | Contract c1, Contract c2 -> true
     | EType (UInt n1), EType (SInt n2) -> n1 < n2
     | ConstInt, EType (Bytes _) -> true
     | EType (UInt _), EType DBytes -> false
     | EType (UInt _), EType (Bytes _) -> false
     | EType (Bytes _), EType (UInt _) -> false
     | EType (Bytes _), EType Address -> false
     | EType Address, EType (Bytes _)-> false
     | EType Address, EType DBytes -> false 
     | EType _, Array _ -> false
     | Array _, EType _ -> false
     | EType Bool, EType Address -> false
     | EType Address, EType Bool -> false
     | EType Bool, EType String -> false 
     | EType String, EType Bool -> false
     | EType Bool, EType (UInt _) -> false
     | EType (UInt _), EType Bool -> false
     | EType Bool, EType (Bytes _) -> false
     | EType (Bytes _), EType Bool -> false
     | EType Bool, EType DBytes -> false
     | EType DBytes, EType Bool -> false
     | EType String, EType Address -> false
     | EType Address, EType String -> false
     | Struct _, EType (Bytes _) -> false
     | EType DBytes, Enum _ -> false
     | Struct _, Array _ -> false
     | EType (SInt _), Struct _ -> false
     | _ -> failwith ("is_implicitly_convertible : " + to_string_typ my_typ + " vs. " + to_string_typ comp_typ))

exception FunctionNotFound of string * string

type cname = id
type fname = id
type FuncMapKey = (cname * fname * typ list)
type t = Map<FuncMapKey, func>

let empty = Map.empty
let add = Map.add
let mem = Map.containsKey
let fold = Map.fold
let foldi f state map =
  let mutable index = 0
  Map.fold (fun acc key value ->
      let result = f index key value acc
      index <- index + 1
      result
  ) state map
let merge m1 m2 =
  let addWithIndex index key value acc = add key value acc
  foldi addWithIndex m2 m1
let dom m = Set.ofSeq (Map.keys m)
let make_key cid fid arg_typs = (cid,fid,arg_typs) 

let find_weak (cid,fid,arg_typs) map =
  let addIfMatch index (cid',fid',typs') v acc =
    if String.Equals (fid, fid') && List.length arg_typs = List.length typs' && List.forall2 is_implicitly_convertible arg_typs typs'
    then Set.add v acc
    else acc
  foldi addIfMatch Set.empty map
  
let find (cid,fid,arg_typs) map =
  let funcs =
    foldi (fun index (cid',fid',typs') v acc ->
      if String.Equals (cid, cid') &&
         String.Equals (fid, fid') &&
         List.length arg_typs = List.length typs' && (* should be checked first before checking convertibility *)
         List.forall2 is_implicitly_convertible arg_typs typs'
      then Set.add v acc
      else acc
    ) Set.empty map
  if Set.count funcs = 1 then Set.minElement funcs else
  if Set.count funcs = 0 then raise (FunctionNotFound (cid,fid))
  else
    raise (Failure "FunctionMap-find")

let to_string map =
  let to_string_x (cid,fid,typs) = cid + "," + fid + "," + String.string_of_list(to_string_typ, typs, "(", ")", ",")
  let to_string_y y = string ((get_finfo y).fid) 
  "{" + "\n" +
  foldi (fun index x y acc -> 
    acc + to_string_x x + " -> " + to_string_y y + "\n"
  ) "" map
  + "}"

let mk_fmap_c (cname,_,_,_,funcs,_) fmap =
  List.fold(fun acc f ->
    let (fid,typs) = get_fsig f
    add (cname,fid,typs) f acc
  ) fmap funcs

let mk_fmap_p contracts =
  List.fold (fun acc contract ->
    mk_fmap_c contract acc 
  ) empty contracts

let mk_fmap  pgm = mk_fmap_p pgm

let is_undef e arg_typs fmap = 
  match e with
  | Lv (Var (fname,_)) 
  | Lv (MemberAccess (_,fname,_,_)) ->
    let fs = find_weak (make_key "DUMMY" fname arg_typs) fmap 
    Set.isEmpty fs 
  | _ -> failwith ("is_undef : " + to_string_exp (ToStringArg.SingleExp e))
                  
let rec find_matching_funcs : id -> exp -> typ list -> id list -> t -> func Set = 
  fun cname e arg_typs cnames fmap ->
    match e with
    | Lv (Var (fname,_)) ->
      Set.singleton (find (make_key cname fname arg_typs) fmap)
    | Lv (MemberAccess (Lv (Var (prefix,_)),fname,_,_)) ->
      if List.contains prefix cnames then (* static call *)
        Set.singleton (find (make_key prefix fname arg_typs) fmap)
      else (* method call *)
        find_weak (make_key "DUMMY" fname arg_typs) fmap
    | Lv (MemberAccess (_,fname,_,_)) ->
      find_weak (make_key "DUMMY" fname arg_typs) fmap
    | _ -> failwith ("find_matching_funcs : " + to_string_exp (ToStringArg.SingleExp e))

let find_func_with_cname cname fmap =
  fmap
  |> Map.filter (fun (cname, _, _) _ -> cname = cname)
  |> Map.toList
  |> List.map snd