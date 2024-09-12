module Smartian.RandomFuzz

open Config
open Utils
open BytesUtils
open solAnalysis
open solAnalysis.TopLevel

let private MUTATE_MAX_POW = 7
let private ARITH_MAX = 35
let private DEPENDENCY_PRESERVATION_RATE = 90

// Evaluate def - use chain
let private dependencyPreservation =
  if random.Next(100) < DEPENDENCY_PRESERVATION_RATE then true else false

let private filterFuncImplicitChains argName implicitChains =
  let defFuncs = implicitChains 
                |> Set.filter (fun (f, g, ics) -> 
                    let filteredIcs = ics |> Array.filter (fun ic -> ic.UseKeys |> Array.filter (Array.exists (fun k -> k = argName)) |> Array.isEmpty |> not)
                    not (Array.isEmpty filteredIcs)) 
                |> Set.map (fun (f, g, ics) -> 
                    let filteredIcs = ics |> Array.filter (fun ic -> ic.UseKeys |> Array.filter (Array.exists (fun k -> k = argName)) |> Array.isEmpty |> not)
                                          |> Array.map (fun ic -> { ic with UseKeys = ic.UseKeys |> Array.filter (fun k -> Array.contains argName k) })
                    (f, filteredIcs)) |> Set.fold (fun acc (k, v) -> Map.add k v acc) Map.empty
  let useFuncs = implicitChains 
                |> Set.filter (fun (f, g, ics) ->
                let filteredIcs = ics |> Array.filter (fun ic -> ic.DefKeys |> Array.filter (Array.exists (fun k -> k = argName)) |> Array.isEmpty |> not)
                not (Array.isEmpty filteredIcs)) 
                |> Set.map (fun (f, g, ics) -> 
                    let filteredIcs = ics |> Array.filter (fun ic -> ic.DefKeys |> Array.filter (Array.exists (fun k -> k = argName)) |> Array.isEmpty |> not)
                                          |> Array.map (fun ic -> { ic with DefKeys = ic.DefKeys |> Array.filter (fun k -> Array.contains argName k) })
                    (g, filteredIcs)) |> Set.fold (fun acc (k, v) -> Map.add k v acc) Map.empty
  (defFuncs, useFuncs)

let private filterTxsWithImplicitChains seed func argName txIdx implicitChains =
  let defs, uses = filterFuncImplicitChains argName implicitChains
  let defTxs = if txIdx = 1 then [||] else seed.Transactions.[0 .. txIdx - 1]
  let useTxs = if txIdx = (Array.length seed.Transactions) - 1 then [||] else seed.Transactions.[txIdx + 1 ..]
  let defTxs = defTxs |> Array.mapi (fun i tx -> 
    if (Map. containsKey tx.FuncSpec.Name defs) && i <> 0 then Some (i, Map.find tx.FuncSpec.Name defs) else None) |> Array.choose id
  let useTxs = useTxs |> Array.mapi (fun i tx -> 
    if (Map. containsKey tx.FuncSpec.Name uses) && i <> 0 then Some (i, Map.find tx.FuncSpec.Name uses) else None) |> Array.choose id
  (defTxs, useTxs)

let private isImplicitDependent seed func argName txIdx implicitChains =
  let defTxs, useTxs = filterTxsWithImplicitChains seed func argName txIdx implicitChains
  if Array.length defTxs = 0 && Array.length useTxs = 0 then false else true

let private evaluateSeedDUChain seed newSeed = 
  let txs = seed.Transactions |> Array.map (fun tx -> tx.FuncSpec.Name) |> Array.toList
  let newTxs = newSeed.Transactions |> Array.map (fun tx -> tx.FuncSpec.Name) |> Array.toList
  // Compare the def-use chains of the two seeds (except the deploying transaction).
  let chains = evalDUChain txs.[1..]
  let newChains = evalDUChain newTxs.[1..]
  if (Set.count chains) <= (Set.count newChains) then true
  else false

// Mutable variables for statistics management.
let mutable private recentExecNums: Queue<int> = Queue.empty
let mutable private recentNewPathNums: Queue<int> = Queue.empty

let updateStatus execN newPathN =
  let recentExecNums' = if Queue.size recentExecNums > CHECK_LAST_N_ROUND
                        then Queue.drop recentExecNums
                        else recentExecNums
  recentExecNums <- Queue.enqueue recentExecNums' execN
  let recentNewPathNums' = if Queue.size recentNewPathNums > CHECK_LAST_N_ROUND
                           then Queue.drop recentNewPathNums
                           else recentNewPathNums
  recentNewPathNums <- Queue.enqueue recentNewPathNums' newPathN

let evaluateEfficiency () =
  let execNum = List.sum (Queue.elements recentExecNums)
  let newPathNum = List.sum (Queue.elements recentNewPathNums)
  if execNum = 0 then 1.0 else float newPathNum / float execNum

(*** Transaction-level mutations ***)

let private insertTransaction contSpec seed =
  let funcSpecs = contSpec.NormalFunctions
  let funcSpec = funcSpecs.[ random.Next(funcSpecs.Length) ]
  let newTx = Transaction.init funcSpec
  let txNum = Seed.getTransactionCount seed
  // Avoid inserting in front of the deploying transaction.
  let insertIdx = random.Next(1, txNum)
  Seed.insertTransactionAt seed insertIdx newTx

let private shuffleTransaction duchains seed =
  let txNum = Seed.getTransactionCount seed
  if txNum < 3 then seed
  else // Avoid shuffling with the deploying transaction. 
    match randomSelect (List.ofSeq { 1 .. (txNum - 1) }) 2 with
    | [idx1; idx2] -> 
      let newSeed = Seed.swapTransactions seed idx1 idx2 
      if evaluateSeedDUChain seed newSeed then newSeed
      else if dependencyPreservation then seed else newSeed
    | _ -> failwith "Unreachable"

let private removeTransaction duchains seed =
  let txNum = Seed.getTransactionCount seed
  if txNum < 3 then seed
  else
    // Avoid removing the deploying transaction.
    let removeIdx = random.Next(1, txNum)
    let newSeed = Seed.removeTransactionAt seed removeIdx
    if evaluateSeedDUChain seed newSeed then newSeed
    else if dependencyPreservation then seed else newSeed

let private findArgIdx tx key =
  let args = tx.Args 
  let argIdx = Array.tryFindIndex (fun arg -> arg.Spec.Name = key) args
  match argIdx with
  | Some idx -> idx
  | None -> -1

let makeKeyAsSame seed defIdx useIdx keyIdx1 keyIdx2 =
  let defTx, useTx = seed.Transactions.[defIdx], seed.Transactions.[useIdx]
  let newTxs = Array.copy seed.Transactions
  match keyIdx1, keyIdx2 with
  | -1, -1 -> 
    let newSender = Sender.pick()
    let newDefTx, newUseTx = { defTx with Sender = newSender }, { useTx with Sender = newSender }
    newTxs.[defIdx] <- newDefTx
    newTxs.[useIdx] <- newUseTx
    { seed with Transactions = newTxs }
  | -1, _ -> 
    let newSender = Sender.pick()
    let newBytes = Address.contractOf newSender |> Address.toBytes LE
    let newDefTx = { defTx with Sender = newSender }
    let newArgs = Arg.setNewAddressArgs useTx.Args keyIdx2 newBytes
    let newUseTx = { useTx with Args = newArgs }
    newTxs.[defIdx] <- newDefTx
    newTxs.[useIdx] <- newUseTx
    { seed with Transactions = newTxs }
  | _, -1 ->
    let newSender = Sender.pick()
    let newBytes = Address.contractOf newSender |> Address.toBytes LE
    let newUseTx = { useTx with Sender = newSender }
    let newArgs = Arg.setNewAddressArgs defTx.Args keyIdx1 newBytes
    let newDefTx = { defTx with Args = newArgs }
    newTxs.[defIdx] <- newDefTx
    newTxs.[useIdx] <- newUseTx
    { seed with Transactions = newTxs }
  | _, _ ->
    let newBytes = Address.pickInteresting() |> Address.toBytes LE
    let newArgs1 = Arg.setNewAddressArgs defTx.Args keyIdx1 newBytes
    let newArgs2 = Arg.setNewAddressArgs useTx.Args keyIdx2 newBytes
    let newDefTx, newUseTx = { defTx with Args = newArgs1 }, { useTx with Args = newArgs2 }
    newTxs.[defIdx] <- newDefTx
    newTxs.[useIdx] <- newUseTx
    { seed with Transactions = newTxs }

let private makeAddressesAsSame seed defIdx useIdx (defKey: key) (useKey: key) =
  let defTx, useTx = seed.Transactions.[defIdx], seed.Transactions.[useIdx]
  match Array.length defKey with
  | 2 -> // mapping[key1][key2]
    let defKey1, defKey2 = defKey.[0], defKey.[1]
    let useKey1, useKey2 = useKey.[0], useKey.[1]
    let defIdx1, defIdx2 = findArgIdx defTx defKey1, findArgIdx defTx defKey2
    let useIdx1, useIdx2 = findArgIdx useTx useKey1, findArgIdx useTx useKey2
    let newSeed = makeKeyAsSame seed defIdx useIdx defIdx1 useIdx1 
    makeKeyAsSame newSeed defIdx useIdx defIdx2 useIdx2
  | 1 -> // mapping[key]
    let defIdx1, useIdx1 = findArgIdx defTx defKey.[0], findArgIdx useTx useKey.[0]
    makeKeyAsSame seed defIdx useIdx defIdx1 useIdx1
  | _ -> failwith "not supported"

let private mutateMappingKeys seed defTxIdx useTxIdx mutateArg opt ics =
  let txs = seed.Transactions
  let defTx, useTx = txs.[defTxIdx], txs.[useTxIdx]
  let iclen = Array.length ics
  let ic = ics.[random.Next(iclen)]
  match opt with
  | 0 ->
    let defKeys = ic.DefKeys |> Array.filter (Array.exists (fun k -> k = mutateArg))
    let selectedDefKey = defKeys.[random.Next(Array.length defKeys)]
    let useKey = ic.UseKeys.[random.Next(Array.length ic.UseKeys)]
    makeAddressesAsSame seed defTxIdx useTxIdx selectedDefKey useKey
  | 1 ->
    let useKeys = ic.UseKeys |> Array.filter (Array.exists (fun k -> k = mutateArg))
    let selectedUseKey = useKeys.[random.Next(Array.length useKeys)]
    let defKey = ic.DefKeys.[random.Next(Array.length ic.DefKeys)]
    makeAddressesAsSame seed defTxIdx useTxIdx defKey selectedUseKey
  | _ -> failwith "Invalid mutation code"

let private mutateAddresswithConstraints seed func argName txIdx implicitChains =
  let defTxs, useTxs = filterTxsWithImplicitChains seed func argName txIdx implicitChains
  let defTxNum, useTxNum = Array.length defTxs, Array.length useTxs
  match defTxNum, useTxNum with
  | 0, 0 -> seed
  | 0, _ -> 
    let selectedIdx = random.Next(useTxNum)
    let idx2, ics = useTxs.[selectedIdx]
    mutateMappingKeys seed txIdx idx2 argName 0 ics
  | _, 0 ->
    let selectedIdx = random.Next(defTxNum)
    let idx2, ics = defTxs.[selectedIdx]
    mutateMappingKeys seed idx2 txIdx argName 1 ics
  | _, _ ->
    match random.Next(2) with
    | 0 -> 
      let selectedIdx = random.Next(useTxNum)
      let idx2, ics = useTxs.[selectedIdx]
      mutateMappingKeys seed txIdx idx2 argName 0 ics
    | 1 ->
      let selectedIdx = random.Next(defTxNum)
      let idx2, ics = defTxs.[selectedIdx]
      mutateMappingKeys seed idx2 txIdx argName 1 ics
    | _ -> failwith "Invalid mutation code"

let private mutateTransactionSender seed implicitChains =
  let txNum = Seed.getTransactionCount seed
  // Avoid mutating the sender of the deploying transaction.
  let mutIdx = random.Next(1, txNum)
  if mutIdx = 0 then Seed.mutateTranasctionSenderAt seed mutIdx
  else
    let func = seed.Transactions.[mutIdx].FuncSpec.Name
    if isImplicitDependent seed func "msg.sender" mutIdx implicitChains then
      if dependencyPreservation then (mutateAddresswithConstraints seed func "msg.sender" mutIdx implicitChains) |> Seed.fixDeployTransaction
      else Seed.mutateTranasctionSenderAt seed mutIdx
    else Seed.mutateTranasctionSenderAt seed mutIdx

(*** Argument mutation. ***)

let private flipBit elem =
  let bytePos = random.Next(Element.getByteLen elem)
  let bitPos = random.Next(8)
  Element.flipBitAt elem bytePos bitPos

let private randomByte elem =
  let i = random.Next(Element.getByteLen elem)
  let newByte = allBytes.[random.Next(allBytes.Length)]
  Element.updateByteAt elem i newByte

let private arithMutate elem =
  let i = random.Next(Element.getByteLen elem)
  let curVal = Element.getByteValAt elem i |> ByteVal.getConcreteByte |> uint32
  let delta = uint32 (1 + random.Next(ARITH_MAX))
  let newVal = if random.Next(2) = 0 then curVal + delta else curVal - delta
  let newByte = byte (newVal &&& 0xffu)
  Element.updateByteAt elem i newByte

let private BOUNADRY_BYTES =
  [| 0uy; 1uy; 0x3fuy; 0x40uy; 0x41uy; 0x7fuy; 0x80uy; 0x81uy; 0xffuy;|]

let private pickBoundaryByte () =
  BOUNADRY_BYTES.[random.Next(BOUNADRY_BYTES.Length)]

let private tryInterestingByte elem =
  let i = random.Next(Element.getByteLen elem)
  let newByte = pickBoundaryByte ()
  Element.updateByteAt elem i newByte

// TODO: Cleanup
let private pickBoundaryIntBytes width =
  if width < 2 then failwithf "Invalid width: %d" width
  let ZEROS = Array.create (width - 2) 0uy
  let MASKS = Array.create (width - 2) 0xFFuy
  match random.Next(9) with
  | 0 -> Array.concat [ [| 0x00uy |]; ZEROS; [|0x00uy|] ] // 0000 .. 0000
  | 1 -> Array.concat [ [| 0x00uy |]; ZEROS; [|0x01uy|] ] // 0000 .. 0001
  | 2 -> Array.concat [ [| 0x3Fuy |]; MASKS; [|0xFFuy|] ] // 3FFF .. FFFF
  | 3 -> Array.concat [ [| 0x40uy |]; ZEROS; [|0x00uy|] ] // 4000 .. 0000
  | 4 -> Array.concat [ [| 0x40uy |]; ZEROS; [|0x01uy|] ] // 4000 .. 0001
  | 5 -> Array.concat [ [| 0x7Fuy |]; MASKS; [|0xFFuy|] ] // 7FFF .. FFFF
  | 6 -> Array.concat [ [| 0x80uy |]; ZEROS; [|0x00uy|] ] // 8000 .. 0000
  | 7 -> Array.concat [ [| 0x80uy |]; ZEROS; [|0x01uy|] ] // 8000 .. 0001
  | 8 -> Array.concat [ [| 0xFFuy |]; MASKS; [|0xFFuy|] ] // FFFF .. FFFF
  | _ -> failwith "Invalid mutation code"
  |> Array.rev // Since we use little endian for integer types.

let private pickInterestingElemBytes elemType =
  match elemType with
  | Int width | UInt width ->
    if width = 1 then [| pickBoundaryByte () |]
    else pickBoundaryIntBytes width
  | Address -> Address.pickInteresting() |> Address.toBytes LE
  | Bool -> [| 0uy |]
  | Byte -> [| pickBoundaryByte() |]
  | String -> [| 0x41uy; 0x42uy; 0x43uy; 0uy |]
  | Array _ -> failwith "Array type not allowed for an element"

let private tryInterestingElem elem =
  let newBytes = pickInterestingElemBytes elem.ElemType
  let newByteVals = Array.map ByteVal.newByteVal newBytes
  { elem with ByteVals = newByteVals }

let private mutateAddressTypeArg seed arg txIdx elem implicitChains =
  let func = (Seed.getCurTransaction seed).FuncSpec.Name
  let argName = arg.Spec.Name
  if isImplicitDependent seed func argName txIdx implicitChains then
    if dependencyPreservation then (mutateAddresswithConstraints seed func argName txIdx implicitChains) |> Seed.fixDeployTransaction
    else
      let newElem = tryInterestingElem elem
      Seed.setCurElem seed newElem |> Seed.fixDeployTransaction
  else
    let newElem = tryInterestingElem elem
    Seed.setCurElem seed newElem |> Seed.fixDeployTransaction
  
let private mutateElem elem =
  match random.Next(5) with
  // Type-unaware mutations.
  | 0 -> flipBit elem
  | 1 -> randomByte elem
  | 2 -> arithMutate elem
  | 3 -> tryInterestingByte elem
  // Type-aware mutation.
  | 4 -> tryInterestingElem elem
  | _ -> failwith "Invalid mutation code"

let private mutateArrayLength seed arg =
  let elems =
    match arg.Spec.Kind with
    // Do not support dimension >= 2 to mutate for now.
    | Array (_, Array _) -> failwith "Unsupported array"
    | Array (size, elemTyp) ->
      match size with
      | FixedSize _ -> arg.Elems
      | UnfixedSize -> 
        let curSize = Array.length arg.Elems 
        let newSize = random.Next(1, 5)
        match elemTyp with
        | Address -> 
          Array.init newSize (
            fun _ -> 
            let bytes = Address.pickInteresting() |> Address.toBytes LE
            let byteVals = Array.map ByteVal.newByteVal bytes
            { ElemType = Address
              ByteVals = byteVals
              MaxLength = 20
              ByteCursor = 0 }
          )
        | _ -> Array.init newSize (fun _ -> Element.ZERO)
    | _ -> failwith "Invalid array type"
  let newArg = { arg with Elems = elems }
  let newTx = Transaction.setCurArg (Seed.getCurTransaction seed) newArg
  Seed.setCurTransaction seed newTx

let private mutateTransactionArg seed implicitChains =
  let arg = Seed.getCurArg seed
  let curElem = Seed.getCurElem seed
  let newElem = mutateElem curElem
  if seed.TXCursor = 0 then Seed.setCurElem seed newElem |> Seed.fixDeployTransaction
  else
    match curElem.ElemType with
    | Array (_, elemTyp) ->
      match elemTyp with
      | Array _ -> 
        let newElem = mutateElem curElem
        Seed.setCurElem seed newElem |> Seed.fixDeployTransaction
      | Address -> 
        if random.Next(100) < 90 then 
          if dependencyPreservation then mutateAddressTypeArg seed arg seed.TXCursor curElem implicitChains
          else
            let newElem = mutateElem curElem
            Seed.setCurElem seed newElem |> Seed.fixDeployTransaction
        else mutateArrayLength seed arg
      | _ -> 
        if random.Next(100) < 90 then
          let newElem = mutateElem curElem
          Seed.setCurElem seed newElem |> Seed.fixDeployTransaction
        else mutateArrayLength seed arg
    | Address -> mutateAddressTypeArg seed arg seed.TXCursor curElem implicitChains
    | _ ->
      let newElem = mutateElem curElem
      Seed.setCurElem seed newElem |> Seed.fixDeployTransaction

let private mutateSeed contSpec duchains implicitChains seed =
  if not (Seed.isInputCursorValid seed) then
    // If all the transactions in the seed have no argument.
    match random.Next(4) with
    | 0 -> insertTransaction contSpec seed
    | 1 -> shuffleTransaction duchains seed
    | 2 -> removeTransaction duchains seed
    | 3 -> mutateTransactionSender seed implicitChains
    | _ -> failwith "Invalid mutation code"
  else
    let seed = Seed.shuffleCursor seed
    match random.Next(16) with
    | 0 -> insertTransaction contSpec seed
    | 1 -> shuffleTransaction duchains seed
    | 2 -> removeTransaction duchains seed
    | 3 -> mutateTransactionSender seed implicitChains
    | _ -> mutateTransactionArg seed implicitChains

let rec private repRandMutateAux contSpec duchains implicitChains seed depth depthLimit accumSeed =
  if depth >= depthLimit then accumSeed else
    let accumSeed = mutateSeed contSpec duchains implicitChains accumSeed
    repRandMutateAux contSpec duchains implicitChains seed (depth + 1) depthLimit accumSeed

let private repRandMutate contSpec duchains implicitChains seed =
  let mutateN = 1 <<< (random.Next(MUTATE_MAX_POW))
  repRandMutateAux contSpec duchains implicitChains seed 0 mutateN seed
  |> Seed.resetCursor
  |> Seed.resetBlockData

let run seed opt contSpec duchains implicitChains =
  List.init Config.RAND_FUZZ_TRY_PER_SEED (fun _ -> repRandMutate contSpec duchains implicitChains seed)
  |> List.filter (TCManage.evalAndSave opt)