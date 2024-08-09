module solAnalysis.Vocab
(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)
(** Vocabularies *)

let (<<<) f g = fun x -> f (g x)
let (>>>) f g = fun x -> g (f x)
// let ($>) x f = match x with Some s -> f s | None -> None
let (&>) x f = match x with Some s -> Some (f s) | None -> None
let (@) l1 l2 = List.append l1 l2
let id x = x
let flip f = fun y x -> f x y
let cond c f g x = if c then f x else g x
let opt c f x = if c then f x else x
let tuple x = (x, x)

let domof m = Map.fold (fun set k _ -> Set.add k set) Set.empty m

// (** This applies [List.fold_left], but the argument type is the same with
//     [PSet.fold].  *)
let list_fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b = 
  fun f list init -> 
  List.fold (flip f) init list

let list_fold2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c = 
  fun f list1 list2 init ->
  let f' acc a b = f a b acc 
  List.fold2 f' init list1 list2

let list_rev : 'a list -> 'a list = 
  fun l ->
  let rec list_rev_rec l1 l2 =
    match l1 with
    | [] -> l2
    | a :: b -> list_rev_rec b (a :: l2) in
  list_rev_rec l []

let append_opt : 'a option -> 'a list -> 'a list = 
  fun x l ->
  match x with None -> l | Some x -> x::l

let find_opt : 'a -> Map<'a, 'b> -> 'b option = 
  fun k m ->
  Map.tryFind k m

let find_def : 'a -> Map<'a,'b> -> 'b -> 'b =
  fun k m def ->
  try Map.find k m with _ -> def

let link_by_sep sep s acc = if acc = "" then s else acc + sep + s

type String =
  static member string_of_list(string_of_v, lst, ?first, ?last, ?sep) =
    let f = defaultArg first "["
    let l = defaultArg last "]"
    let s = defaultArg sep ";"
    let add_string_of_v v acc = link_by_sep s (string_of_v v) acc
    f + list_fold add_string_of_v lst "" + l 
  
  static member string_of_set(string_of_v, set, ?first, ?last, ?sep) =
    let f = defaultArg first "{"
    let l = defaultArg last "}"
    let s = defaultArg sep ","
    let add_string_of_v acc v = link_by_sep s (string_of_v v) acc
    f + Set.fold add_string_of_v "" set + l

  static member string_of_map(string_of_k, string_of_v, map, ?first, ?last, ?sep, ?indent) =
    let f = defaultArg first "{"
    let l = defaultArg last "}"
    let s = defaultArg sep ",\n"
    let i = defaultArg indent ""
    let add_string_of_k_v k v acc = 
      let str = string_of_k k + " -> " + string_of_v v 
      link_by_sep (s+i) str acc
    if Map.isEmpty map then "empty"
    else i + f + Map.fold add_string_of_k_v "" map + l

let i2s = string

let list2set l = list_fold Set.add l Set.empty
let set2list s = Set.fold (fun l x -> x::l) [] s

let set_union_small_big small big = Set.union small big

// (* fixpoint operator for set *)
let rec fix : ('a Set -> 'a Set) -> 'a Set -> 'a Set = 
  fun f init ->
  let next = f init in
    if Set.isSubset next init then init
    else fix f next

// (****************************************)
// (*** End of Implementation from ROPAS ***)
// (****************************************)

let remove_some : 'a option -> 'a = 
  fun x ->
  match x with
  | Some x -> x
  | None -> failwith "None value encountered"

let triple_fst (a,b,c) = a
let triple_snd (a,b,c) = b
let triple_third (a,b,c) = c

let zfill num str =
  if num > String.length str then String.replicate (num - str.Length) "0" + str
  else str

let replace_str : string -> string -> string -> string = 
  fun str sub rep ->
  let index = str.IndexOf(sub)
  if index = -1 then failwith "Substring not found"
  else str.Remove(index, sub.Length).Insert(index,rep)

exception NotImplemented

let rec compare_lst cmp lst1 lst2 =
  match lst1, lst2 with
  | [], [] -> 0
  | [], h::t -> -1
  | h::t, [] -> 1
  | h1::t1, h2::t2 ->
    if cmp h1 h2 = 0 then compare_lst cmp t1 t2
    else cmp h1 h2
