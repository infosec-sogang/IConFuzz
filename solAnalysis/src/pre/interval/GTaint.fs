module solAnalysis.GTaint

open Lang
open Vocab

(* aims to track from what global variables may be affected *)
type t = var Set

let bot = Set.empty
let is_bot = Set.isEmpty

let le v1 v2 = Set.isSubset v1 v2
let meet v1 v2 = Set.intersect v1 v2
let join v1 v2 = Set.union v1 v2
let widen v1 v2 = join v1 v2 (* domain is finite *)

let singleton = Set.singleton 


let to_string set = 
    let f = fun x -> fst x |> id 
    String.string_of_set (f, set, "{", "}", ",")