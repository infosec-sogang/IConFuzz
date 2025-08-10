module IConFuzz.RandomFuzz

open Config
open Utils
open BytesUtils
open solAnalysis
open solAnalysis.TopLevel
open Options

let private MUTATE_MAX_POW = 7
let private ARITH_MAX = 35
let private DEPENDENCY_PRESERVATION_RATE = 90


// Evaluate def - use chain
let private dependencyPreservation =
  if random.Next(100) < DEPENDENCY_PRESERVATION_RATE then true else false

let private constraintsRate (opt: FuzzOption) =
  if opt.NoMapKeyConstrs then 0
  elif opt.NoPrivConstrs then 100
  else 50

let private filterFuncsByMapKeyCons argName mapKeyChains =
  let defFuncs = mapKeyChains
                |> Set.filter (fun (f, g, mcs) -> 
                    let filteredMcs = mcs |> Array.filter (fun mc -> mc.UseKeys |> Array.filter (Array.exists (fun k -> k = argName)) |> Array.isEmpty |> not)
                    not (Array.isEmpty filteredMcs)) 
                |> Set.map (fun (f, g, mcs) -> 
                    let filteredMcs = mcs |> Array.filter (fun mc -> mc.UseKeys |> Array.filter (Array.exists (fun k -> k = argName)) |> Array.isEmpty |> not)
                                          |> Array.map (fun mc -> { mc with UseKeys = mc.UseKeys |> Array.filter (fun k -> Array.contains argName k) })
                    (f, filteredMcs)) |> Set.fold (fun acc (k, v) -> Map.add k v acc) Map.empty
  let useFuncs = mapKeyChains
                |> Set.filter (fun (f, g, mcs) ->
                let filteredMcs = mcs |> Array.filter (fun mc -> mc.DefKeys |> Array.filter (Array.exists (fun k -> k = argName)) |> Array.isEmpty |> not)
                not (Array.isEmpty filteredMcs)) 
                |> Set.map (fun (f, g, mcs) -> 
                    let filteredMcs = mcs |> Array.filter (fun mc -> mc.DefKeys |> Array.filter (Array.exists (fun k -> k = argName)) |> Array.isEmpty |> not)
                                          |> Array.map (fun mc -> { mc with DefKeys = mc.DefKeys |> Array.filter (fun k -> Array.contains argName k) })
                    (g, filteredMcs)) |> Set.fold (fun acc (k, v) -> Map.add k v acc) Map.empty
  (defFuncs, useFuncs)

let private filterFuncsByPrivCons argName privChains =
  let filteredChains = privChains
                      |> Set.filter (fun (f, g, (defPC, usePC)) -> (Array.exists (fun (x, y, b) -> y = argName) usePC.Uses))
  let defFuncs = filteredChains |> Set.map (fun (f, g, (defAC, useAC)) -> (f, defAC)) 
                  |> Set.fold (fun acc (k, v) -> Map.add k v acc) Map.empty
  let useFuncs = filteredChains |> Set.map (fun (f, g, (defAC, useAC)) -> (g, useAC)) 
                  |> Set.fold (fun acc (k, v) -> Map.add k v acc) Map.empty
  (defFuncs, useFuncs)

let private filterTxsWithMapKeyChains seed func argName txIdx mapKeyChains =
  let defs, uses = filterFuncsByMapKeyCons argName mapKeyChains
  let defTxs = if txIdx = 1 then [||] else seed.Transactions.[0 .. txIdx - 1]
  let useTxs = if txIdx = (Array.length seed.Transactions) - 1 then [||] else seed.Transactions.[txIdx + 1 ..]
  let defTxs = defTxs |> Array.mapi (fun i tx -> 
    if (Map. containsKey tx.FuncSpec.Name defs) && i <> 0 then Some (i, Map.find tx.FuncSpec.Name defs) else None) |> Array.choose id
  let useTxs = useTxs |> Array.mapi (fun i tx -> 
    if (Map. containsKey tx.FuncSpec.Name uses) && i <> 0 then Some (i, Map.find tx.FuncSpec.Name uses) else None) |> Array.choose id
  (defTxs, useTxs)

let private filterTxsWithPrivChains seed func argName txIdx privChains =
  let defs, uses = filterFuncsByPrivCons argName privChains
  let defTxs = if txIdx = 1 then [||] else seed.Transactions.[0 .. txIdx - 1]
  let useTxs = if txIdx = (Array.length seed.Transactions) - 1 then [||] else seed.Transactions.[txIdx + 1 ..]
  let defTxs = defTxs |> Array.mapi (fun i tx -> 
    if (Map. containsKey tx.FuncSpec.Name defs) && i <> 0 then Some (i, Map.find tx.FuncSpec.Name defs) else None) |> Array.choose id
  let useTxs = useTxs |> Array.mapi (fun i tx ->
    if (Map. containsKey tx.FuncSpec.Name uses) && i <> 0 then Some (i, Map.find tx.FuncSpec.Name uses) else None) |> Array.choose id
  (defTxs, useTxs)

let private isMapKeyConstraints seed func argName txIdx mapKeyChains =
  let defTxs, useTxs = filterTxsWithMapKeyChains seed func argName txIdx mapKeyChains
  if Array.length defTxs = 0 && Array.length useTxs = 0 then false else true

let private isPrivilegeConstraints seed func argName txIdx privChains =
  let defTxs, useTxs = filterTxsWithPrivChains seed func argName txIdx privChains
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

let makeKeyAsDifferent seed defIdx useIdx keyIdx1 keyIdx2 =
  let defTx, useTx = seed.Transactions.[defIdx], seed.Transactions.[useIdx]
  let newTxs = Array.copy seed.Transactions
  match keyIdx1, keyIdx2 with
  | -1, -1 -> 
    let (newSender1, newSender2) = Sender.picktwo()
    let newDefTx, newUseTx = { defTx with Sender = newSender1 }, { useTx with Sender = newSender2 }
    newTxs.[defIdx] <- newDefTx
    newTxs.[useIdx] <- newUseTx
    { seed with Transactions = newTxs }
  | -1, _ -> 
    let (newSender1, newSender2) = Sender.picktwo()
    let newDefTx = { defTx with Sender = newSender1 }
    let newBytes = Address.contractOf newSender2 |> Address.toBytes LE
    let newArgs = Arg.setNewAddressArgs useTx.Args keyIdx2 newBytes
    let newUseTx = { useTx with Args = newArgs }
    newTxs.[defIdx] <- newDefTx
    newTxs.[useIdx] <- newUseTx
    { seed with Transactions = newTxs }
  | _, -1 ->
    let (newSender1, newSender2) = Sender.picktwo()
    let newBytes = Address.contractOf newSender1 |> Address.toBytes LE
    let newUseTx = { useTx with Sender = newSender2 }
    let newArgs = Arg.setNewAddressArgs defTx.Args keyIdx1 newBytes
    let newDefTx = { defTx with Args = newArgs }
    newTxs.[defIdx] <- newDefTx
    newTxs.[useIdx] <- newUseTx
    { seed with Transactions = newTxs }
  | _, _ ->
    let (newSender1, newSender2) = Sender.picktwo()
    let newBytes1 = Address.contractOf newSender1 |> Address.toBytes LE
    let newBytes2 = Address.contractOf newSender2 |> Address.toBytes LE
    let newArgs1 = Arg.setNewAddressArgs defTx.Args keyIdx1 newBytes1
    let newArgs2 = Arg.setNewAddressArgs useTx.Args keyIdx2 newBytes2
    let newDefTx, newUseTx = { defTx with Args = newArgs1 }, { useTx with Args = newArgs2 }
    newTxs.[defIdx] <- newDefTx
    newTxs.[useIdx] <- newUseTx
    { seed with Transactions = newTxs }

let private makeMappingAddressesAsSame seed defIdx useIdx (defKey: key) (useKey: key) =
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
    makeMappingAddressesAsSame seed defTxIdx useTxIdx selectedDefKey useKey
  | 1 ->
    let useKeys = ic.UseKeys |> Array.filter (Array.exists (fun k -> k = mutateArg))
    let selectedUseKey = useKeys.[random.Next(Array.length useKeys)]
    let defKey = ic.DefKeys.[random.Next(Array.length ic.DefKeys)]
    makeMappingAddressesAsSame seed defTxIdx useTxIdx defKey selectedUseKey
  | _ -> failwith "Invalid mutation code"

let private mutateAddresswithMapKeyCons seed func argName txIdx mapKeyChains =
  let defTxs, useTxs = filterTxsWithMapKeyChains seed func argName txIdx mapKeyChains
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

let private mutateAddressWithOption seed defIdx useIdx defArg useArg opt =
  let defTx, useTx = seed.Transactions.[defIdx], seed.Transactions.[useIdx]
  let defArgIdx, useArgIdx = findArgIdx defTx defArg, findArgIdx useTx useArg
  match opt with
  | true -> makeKeyAsSame seed defIdx useIdx defArgIdx useArgIdx
  | false -> makeKeyAsDifferent seed defIdx useIdx defArgIdx useArgIdx

let private mutateAddressByPrivCons seed defTxIdx useTxIdx argName privChains =
  let txs = seed.Transactions
  let defTx, useTx = txs.[defTxIdx], txs.[useTxIdx]
  let chain = privChains |> Set.filter (fun (f, g, (defAC, useAC)) -> f = defTx.FuncSpec.Name && g = useTx.FuncSpec.Name) |> Set.toList
  if List.length chain = 0 then seed
  else
    let _, _, (defAC, useAC) = chain.[random.Next(List.length chain)]
    let defArg = 
      let candidates = Array.filter (fun (x, y) -> if y = argName then true else false) defAC.Defs
      defAC.Defs.[random.Next(Array.length candidates)] |> snd
    let useArg, opt = 
      let candidates = Array.filter (fun (x, y, b) -> if y = argName then true else false) useAC.Uses
      let _, arg, opt = useAC.Uses.[random.Next(Array.length useAC.Uses)] 
      (arg, opt)
    mutateAddressWithOption seed defTxIdx useTxIdx defArg useArg opt

let private mutateAddresswithPrivCons seed func argName txIdx privChains =
  let defTxs, useTxs = filterTxsWithPrivChains seed func argName txIdx privChains
  let defTxNum, useTxNum = Array.length defTxs, Array.length useTxs
  match defTxNum, useTxNum with
  | 0, 0 -> seed
  | 0, _ -> // No def transaction with address constraints.
    let selectedIdx = random.Next(useTxNum)
    let idx2, uses = useTxs.[selectedIdx]
    mutateAddressByPrivCons seed txIdx idx2 argName privChains
  | _, 0 -> // Mutate the address of the def transaction.
    let selectedIdx = random.Next(defTxNum)
    let idx2, defs = defTxs.[selectedIdx]
    mutateAddressByPrivCons seed idx2 txIdx argName privChains
  | _, _ -> // Mutate the address of either the def or use transaction.
    match random.Next(2) with
    | 0 -> 
      let selectedIdx = random.Next(useTxNum)
      let idx2, uses = useTxs.[selectedIdx]
      mutateAddressByPrivCons seed txIdx idx2 argName privChains
    | 1 ->
      let selectedIdx = random.Next(defTxNum)
      let idx2, defs = defTxs.[selectedIdx]
      mutateAddressByPrivCons seed idx2 txIdx argName privChains
    | _ -> failwith "Invalid mutation code"

let mutateTransactionSender opt seed mapKeyChains privChains =
  let txNum = Seed.getTransactionCount seed
  // Avoid mutating the sender of the deploying transaction.
  let mutIdx = random.Next(1, txNum)
  if mutIdx = 0 then Seed.mutateTransactionSenderAt seed mutIdx
  else
    let func = seed.Transactions.[mutIdx].FuncSpec.Name
    if opt.NoConstrs || (not dependencyPreservation) then
      Seed.mutateTransactionSenderAt seed mutIdx // Disable constraints, mutate the sender directly.
    else
      let isMC = isMapKeyConstraints seed func "msg.sender" mutIdx mapKeyChains
      let isPC = isPrivilegeConstraints seed func "msg.sender" mutIdx privChains

      let mutateAddressWithMC chains =
        (mutateAddresswithMapKeyCons seed func "msg.sender" mutIdx chains) |> Seed.fixDeployTransaction

      let mutateAddressWithPC chains =
        (mutateAddresswithPrivCons seed func "msg.sender" mutIdx chains) |> Seed.fixDeployTransaction

      match (isMC, isPC) with
      | (true, true) ->
        // Check for mapping-key constraints
        if random.Next(100) < constraintsRate opt then mutateAddressWithMC mapKeyChains
        else mutateAddressWithPC privChains
      | (true, false) ->
        if not opt.NoMapKeyConstrs then mutateAddressWithMC mapKeyChains
        else Seed.mutateTransactionSenderAt seed mutIdx
      | (false, true) ->
        if not opt.NoPrivConstrs then mutateAddressWithPC privChains
        else Seed.mutateTransactionSenderAt seed mutIdx
      | (false, false) ->
        Seed.mutateTransactionSenderAt seed mutIdx // No constraints, mutate the sender directly.

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

let private mutateAddressTypeArg opt seed arg txIdx curelem mapKeyChains privChains =
  let func = (Seed.getCurTransaction seed).FuncSpec.Name
  let argName = arg.Spec.Name
  let mutate elem =
    let newElem = tryInterestingElem elem
    Seed.setCurElem seed newElem |> Seed.fixDeployTransaction

  if opt.NoConstrs || (not dependencyPreservation) then mutate curelem
  else
    let isMC = isMapKeyConstraints seed func argName txIdx mapKeyChains
    let isPC = isPrivilegeConstraints seed func argName txIdx privChains

    let mutateAddressWithMC chains =
      (mutateAddresswithMapKeyCons seed func argName txIdx chains) |> Seed.fixDeployTransaction

    let mutateAddressWithPC chains =
      (mutateAddresswithPrivCons seed func argName txIdx chains) |> Seed.fixDeployTransaction

    match (isMC, isPC) with
    | (true, true) ->
      if random.Next(100) < constraintsRate opt then mutateAddressWithMC mapKeyChains
      else mutateAddressWithPC privChains
    | (true, false) ->
      if opt.NoMapKeyConstrs then mutate curelem
      else mutateAddressWithMC mapKeyChains
    | (false, true) ->
      if opt.NoPrivConstrs then mutate curelem
      else mutateAddressWithPC privChains
    | _ -> mutate curelem

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

let private mutateTransactionArg opt seed mapKeyChains privChains =
  let arg = Seed.getCurArg seed
  let curElem = Seed.getCurElem seed
  let newElem = mutateElem curElem
  let txIdx = seed.TXCursor
  if txIdx = 0 then Seed.setCurElem seed newElem |> Seed.fixDeployTransaction
  else
    let mutate elem =
      let newElem = mutateElem elem
      Seed.setCurElem seed newElem |> Seed.fixDeployTransaction

    match curElem.ElemType with
    | Array (_, elemTyp) ->
      match elemTyp with
      | Array _ -> mutate curElem
      | Address -> 
        // Mutate the address type argument or the array length (90% chance)
        if random.Next(100) < 90 then 
          mutateAddressTypeArg opt seed arg txIdx curElem mapKeyChains privChains
        else mutateArrayLength seed arg
      | _ -> 
        if random.Next(100) < 90 then mutate curElem
        else mutateArrayLength seed arg
    | Address -> mutateAddressTypeArg opt seed arg txIdx curElem mapKeyChains privChains
    | _ ->
      let newElem = mutateElem curElem
      Seed.setCurElem seed newElem |> Seed.fixDeployTransaction

let private mutateSeed opt contSpec duchains mapKeyChains privChains seed =
  if not (Seed.isInputCursorValid seed) then
    // If all the transactions in the seed have no argument.
    match random.Next(5) with
    | 0 -> insertTransaction contSpec seed
    | 1 -> shuffleTransaction duchains seed
    | 2 -> removeTransaction duchains seed
    | 3 -> mutateTransactionSender opt seed mapKeyChains privChains
    | _ -> failwith "Invalid mutation code"
  else
    let seed = Seed.shuffleCursor seed
    match random.Next(16) with
    | 0 -> insertTransaction contSpec seed
    | 1 -> shuffleTransaction duchains seed
    | 2 -> removeTransaction duchains seed
    | 3 -> mutateTransactionSender opt seed mapKeyChains privChains
    | _ -> mutateTransactionArg opt seed mapKeyChains privChains

let rec private repRandMutateAux opt contSpec duchains mapKeyChains privChains seed depth depthLimit accumSeed =
  if depth >= depthLimit then accumSeed else
    let accumSeed = mutateSeed opt contSpec duchains mapKeyChains privChains accumSeed
    repRandMutateAux opt contSpec duchains mapKeyChains privChains seed (depth + 1) depthLimit accumSeed

let private repRandMutate opt contSpec duchains mapKeyChains privChains seed =
  let mutateN = 1 <<< (random.Next(MUTATE_MAX_POW))
  repRandMutateAux opt contSpec duchains mapKeyChains privChains seed 0 mutateN seed
  |> Seed.resetCursor
  |> Seed.resetBlockData

let run seed opt contSpec duchains mapKeyChains privChains =
  List.init Config.RAND_FUZZ_TRY_PER_SEED (fun _ -> repRandMutate opt contSpec duchains mapKeyChains privChains seed)
  |> List.filter (TCManage.evalAndSave opt)