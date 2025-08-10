module solAnalysis.Typedef

open solAnalysis

let MAX_UINT64 = System.Numerics.BigInteger.Pow(2I, 64) - 1I
let MAX_UINT256 = System.Numerics.BigInteger.Pow(2I, 256) - 1I

// Code address.
type Addr = uint64

module Addr =

  let toString (addr: Addr) = sprintf "0x%x" addr

  let ofBigInt (i: bigint) =
    if i > MAX_UINT64 then
      printfn "[WARNING] Addr.ofBigInt(0x%s)" (i.ToString("X"))
    uint64 (i &&& MAX_UINT64)
    
// State variables.
type Variable =
  | Singleton of name: string * bigint
  | ArrayVar of name: string * id: bigint * offset: bigint
  | MapVar of name: string * id: bigint * offset: bigint

module Variable =

  let toString = function
    | Singleton (name, addr) -> name  + "(" + addr.ToString() + ")"
    | ArrayVar (n, i, o) ->
      let arrPart = n + "(" + i.ToString() + ")"
      let offPart = if o = 0I then "" else ".off_" + o.ToString()
      arrPart + offPart
    | MapVar (n, i, o) ->
      let mapPart = n + "(" + i.ToString() + ")"
      let offPart = if o = 0I then "" else ".off_" + o.ToString()
      mapPart + offPart

type DUChain = string * Variable * string // Def function * Var * Use function.

module DUChain =

  let toString (chain: DUChain) =
    let defFunc, var, useFunc = chain
    sprintf "%s -- (%s) --> %s" defFunc (Variable.toString var) useFunc
