module IConFuzz.ABI

open FSharp.Data
open FSharp.Data.JsonExtensions
open solAnalysis

let rec private parseArgKind (str: string) =
  if str.Contains("[") && str.Contains("]") then
    let idxOpen = str.LastIndexOf("[")
    let idxClose = str.LastIndexOf("]")
    let sizeStr = str.[(idxOpen + 1) .. (idxClose - 1)].Trim()
    let size = SizeType.parse sizeStr
    let remainStr = str.[ .. (idxOpen - 1)] + str.[(idxClose + 1) .. ]
    Array (size, parseArgKind remainStr)
  elif str = "int" then Int 32
  elif str.StartsWith("int") then Int (int str.[3..] / 8)
  elif str = "uint" then UInt 32
  elif str.StartsWith("uint") then UInt (int str.[4..] / 8)
  elif str = "bytes" then Array (UnfixedSize, Byte)
  elif str.StartsWith("bytes") then Array (FixedSize (int str.[5..]), Byte)
  elif str = "address" then Address
  elif str = "bool" then Bool
  elif str = "function" then Array (FixedSize 24, Byte)
  elif str = "string" then String
  else failwithf "Unimplemented type string : %s" str

let private parsePayable (json: JsonValue) =
  json?stateMutability.AsString() = "payable"

let private parseArgs (json: JsonValue) =
  json?inputs.AsArray()
  |> Array.map (fun (i: JsonValue) -> (i?``type``.AsString(), i?name.AsString()))
  |> Array.map (fun (id, str) -> {Name = id; TypeStr = str; Kind = parseArgKind str }) //TODO

let private parseConstructor (funcJsons: JsonValue list) =
  let isConstr (fJson: JsonValue) = fJson?``type``.AsString() = "constructor"
  match List.tryFind isConstr funcJsons with
  | None -> FuncSpec.DEFAULT_CONSTURCTOR // Constructor may have been omitted.
  | Some json -> FuncSpec.initConstructor (parsePayable json) (parseArgs json)

let private tryParseFunc (fJson: JsonValue) =
  let typ = fJson?``type``.AsString()
  if typ = "fallback" then // Empty signature array and no argument.
    let payable = parsePayable fJson
    Some (FuncSpec.initFallback payable)
  elif typ = "function" then
    let name = fJson?name.AsString()
    let payable = parsePayable fJson
    let args = parseArgs fJson
    Some (FuncSpec.init name Normal payable args)
  else None

let parse abiFile =
  let abiStr = System.IO.File.ReadAllText(abiFile)
  let abiJson = JsonValue.Parse(abiStr)
  let fJsons = [ for v in abiJson -> v ]
  let constructor = parseConstructor fJsons
  let normalFuncs = List.choose tryParseFunc fJsons |> Array.ofList
  ContractSpec.make constructor normalFuncs