module solAnalysis.ItvDom

open System
open System.Collections.Generic
open Itv
open GTaint
open Lang
open Vocab

module Loc = 
  type t = id * typ

  let compare (id1,t1) (id2,t2) = String.Compare (id1, id2)
  let of_var id t = (id,t)
  let typ_of (id,t) = t
  let to_string (id,t) = id

module Val = 
  type t = Itv.t * GTaint.t * BTaint.t

  let itv_of (a,_,_) = a
  let gtaint_of (_,b,_) = b
  let btaint_of (_,_,c) = c

  let of_itv itv = (itv, GTaint.bot, BTaint.bot)

  let update_itv a' (a,b,c) = (a',b,c) 
  let update_gtaint b' (a,b,c) = (a,b',c)
  let update_btaint c' (a,b,c) = (a,b,c')

  let bot = (Itv.bot, GTaint.bot, BTaint.bot) 

  let le    (a1,b1,c1) (a2,b2,c2) = Itv.le a1 a2 && GTaint.le b1 b2 && BTaint.le c1 c2 
  let meet  (a1,b1,c1) (a2,b2,c2) = (Itv.meet a1 a2, GTaint.meet b1 b2, BTaint.meet c1 c2)
  let join  (a1,b1,c1) (a2,b2,c2) = (Itv.join a1 a2, GTaint.join b1 b2, BTaint.join c1 c2)
  let widen (a1,b1,c1) (a2,b2,c2) = (Itv.widen a1 a2, GTaint.widen b1 b2, BTaint.widen c1 c2)

  let to_string v =
    "(" + Itv.to_string (itv_of v) + ", " + GTaint.to_string (gtaint_of v) + ", " + BTaint.to_string (btaint_of v) + ")"

module Mem = 
  type t = Map<Loc.t, Val.t>

  let bot = Map.empty

  let find x s = match Map.tryFind x s with Some v -> v | None -> Val.bot
    
  let find2 x s = match Map.tryFind x s with Some v -> v | None -> (Itv.top, GTaint.bot, BTaint.bot) (* for linearization purpose, taint values will not be used *) 
  
  let filter = Map.filter

  let map f map =
        map |> Map.fold (fun acc key value -> Map.add key (f key value) acc) Map.empty
  
  // let map = Map.mapi
  let keySet map = map |> Map.keys |> Set.ofSeq
  let merge mergeFunction map1 map2 =
      let folder key value acc =
        match Map.tryFind key map1, Map.tryFind key map2 with
          | Some v1, Some v2 -> Map.add key (mergeFunction key (Some v1) (Some v2)) acc
          | Some v1, None -> Map.add key (mergeFunction key (Some v1) None) acc
          | None, Some v2 -> Map.add key (mergeFunction key None (Some v2)) acc
          | None, None -> acc

      let keys = Set.union (keySet map1) (keySet map2)
      Set.fold (fun acc key -> folder key (Map.find key map1) acc) Map.empty keys

  let update = Map.add
  let weak_update x v m =
    let v' = Val.join (find x m) v
    update x v' m

  let meet mem1 mem2 =
    let meet' key opt_d1 opt_d2 = 
      match opt_d1,opt_d2 with
      | None,_ 
      | _,None -> None
      | Some v1,Some v2 -> Some (Val.meet v1 v2)
    merge meet' mem1 mem2

  let join mem1 mem2 =
    let join' key opt_d1 opt_d2 = 
      match opt_d1,opt_d2 with
      | None,None -> None
      | None,Some v
      | Some v,None -> Some v
      | Some v1,Some v2 -> Some (Val.join v1 v2)
    merge join' mem1 mem2

  let widen mem1 mem2 =
    let widen' key opt_d1 opt_d2 =
      match opt_d1,opt_d2 with
      | None,None -> None
      | None,Some v
      | Some v,None -> Some v
      | Some v1,Some v2 -> Some (Val.widen v1 v2) 
    merge widen' mem1 mem2

  let le mem1 mem2 =
    if mem1 = mem2 then true else
      let enum1 = Map.toSeq mem1 
      let enum2 = Map.toSeq mem2 
      let enum1' = enum1.GetEnumerator()
      let enum2' = enum2.GetEnumerator()
      let enumGet (e: IEnumerator<'a * 'b>) = if e.MoveNext() then Some e.Current else None
      let rec loop : (Loc.t * Val.t) option -> (Loc.t * Val.t) option -> bool = fun e1 e2 ->
        match e1,e2 with
        | Some (k1,v1),Some (k2,v2) ->
          let c = Loc.compare k1 k2 
          if c=0 then
            if Val.le v1 v2 then loop (enumGet enum1') (enumGet enum2') else false
          else if c<0 then

            if Val.le v1 Val.bot then loop (enumGet enum1') e2 else false
          else
            loop e1 (enumGet enum2')
        | Some (_,v),None ->
          if Val.le v Val.bot then loop (enumGet enum1') e2 
          else false 
        | None,Some _ -> true
        | None,None -> true
      in
      loop (enumGet enum1') (enumGet enum2')

  let fold = map
  let foldi f state map =
    let mutable index = 0
    Map.fold (fun acc key value ->
        let result = f index key value acc
        index <- index + 1
        result
    ) state map

  // let to_string mem =
  //   "{" + "\n" +
  //   foldi (fun x  y acc -> 
  //     acc + (Loc.to_string x) + " -> " + Val.to_string y + "\n"
  //   ) "" mem
  //   + "}"
  