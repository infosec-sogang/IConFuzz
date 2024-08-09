module solAnalysis.StructMap

open FSharp.Data
open System.Collections.Generic
open Lang
open Vocab

type t = Map<struct_id, members>
and smap = t
and struct_id = string (* "Defined Contract Name"."Struct Name" *)
and members = var_decl list

let add = Map.add
let empty = Map.empty

let mk_smap_c  smap c =
  let structs = get_structs c
  List.fold (fun acc s -> add (fst s) (snd s) acc) smap structs

let mk_smap  contracts = List.fold mk_smap_c empty contracts

let find sname smap =
    try Map.find sname smap
    with
    | :? KeyNotFoundException -> failwith "structMap_find"

let to_string smap =
    let folder acc x ylst =
        acc + x + " -> " + String.string_of_list (to_string_var_decl, ylst, "[","]",",") + "\n"
    Map.fold folder "" smap

