module Smartian.Executor

open System.IO
open System.Numerics
open System.Collections.Generic
open Nethermind.Dirichlet.Numerics
open Nethermind.Core.Test.Builders
open Nethermind.Core.Specs
open Nethermind.Evm
open Nethermind.Evm.Test
open Nethermind.Evm.Tracing
open Nethermind.Logging
open Nethermind.Store
open Config
open BytesUtils
open Options

type BugType =
  | AssertionFailure of BugClass * int
  | ArbitraryWrite of BugClass * int
  | BlockstateDependency of BugClass * int
  | BlockstateDependencySFuzz of BugClass * int
  | BlockstateDependencyILF of BugClass * int
  | BlockstateDependencyMythril of BugClass * int
  | BlockstateDependencyManticore of BugClass * int
  | ControlHijack of BugClass * int
  | EtherLeak of BugClass * string * int
  | EtherLeakStrict of BugClass * string * int
  | IntegerBug of BugClass * int
  | IntegerBugSFuzz of BugClass * int
  | IntegerBugMythril of BugClass * int
  | IntegerBugManticore of BugClass * int
  | MishandledException of BugClass * int
  | MishandledExceptionSFuzz of BugClass * int
  | MishandledExceptionILF of BugClass * int
  | MishandledExceptionMythril of BugClass * int
  | MishandledExceptionManticore of BugClass * int
  | MultipleSend of BugClass * int
  | Reentrancy of BugClass * int
  | ReentrancySFuzz of BugClass * int
  | ReentrancyILF of BugClass * int
  | ReentrancyMythril of BugClass * int
  | ReentrancyManticore of BugClass * int
  | SuicidalContract of BugClass * string * int
  | SuicidalContractStrict of BugClass * string * int
  | TransactionOriginUse of BugClass * int
  | FreezingEther of BugClass * int
  | RequirementViolation of BugClass * int

type Env = {
  State : StateProvider
  SpecProvider: MainNetSpecProvider
  VM : VirtualMachine
  TxProcessor : TransactionProcessor
}

type Feedback = {
  CovGain : bool
  DUGain : bool
  // PC, Op, Oprnd1, Oprnd2.
  CmpList : (uint64 * string * bigint * bigint) list
  // BugType * index of buggy TX.
  BugSet : Set<(BugType * int)>
}

// Set of edge hashes.
let mutable accumDeployEdges = SortedSet<int>()
let mutable accumRuntimeEdges = SortedSet<int>()
// Set of program counters.
let mutable accumRuntimeInstrs = SortedSet<int>()
// Set of (Def PC * Use PC * Storage Index)
let mutable accumDUChains = SortedSet<struct(int * int * UInt256)>()
// Set of (BugClass * PC)
let mutable accumBugs = Set.empty

let mutable deployFailCount = 0

let mutable receivedEther = false
let mutable useDelegateCall = false
let mutable canSendEther = false

let mutable private targCode = [||]
let mutable private smartianAgentCode = [||]
let mutable private sFuzzAgentCode = [||]

let initialize targetPath =
  targCode <- File.ReadAllText(targetPath) |> hexStrToBytes
  let srcDir = Directory.GetParent(__SOURCE_DIRECTORY__).FullName
  let smartianAgentPath = Path.Join(srcDir, "Agent/AttackerContract.bin")
  smartianAgentCode <- File.ReadAllText(smartianAgentPath) |> hexStrToBytes
  let sFuzzAgentPath = Path.Join(srcDir, "Agent/SFuzzContract.bin")
  sFuzzAgentCode <- File.ReadAllText(sFuzzAgentPath) |> hexStrToBytes

let private initTestingEnv () =
  let logger = LimboLogs.Instance
  let codeDb = new StateDb()
  let stateDb = new StateDb()
  let state = StateProvider(stateDb, codeDb, logger)
  let storage = StorageProvider(stateDb, state, logger)
  let spec = MainNetSpecProvider.Instance
  let blockHash = TestBlockhashProvider()
  let vm = VirtualMachine(state, storage, blockHash, spec, logger)
  let processor = TransactionProcessor(spec, state, storage, vm, logger)
  state.Commit(spec.GenesisSpec)
  { State = state
    SpecProvider = spec
    VM = vm
    TxProcessor = processor }

let private runTx env from ``to`` code reqAddr value data timestamp blocknum =
  let processor = env.TxProcessor
  let tracer = CallOutputTracer()
  let block = Build.A.Block.WithTimestamp(UInt256(timestamp: int64))
                           .WithNumber(blocknum)
                           .WithGasLimit(BLOCK_GASLIMIT)
                           .WithBeneficiary(Address.MINER)
                           .TestObject
  let tx = Nethermind.Core.Transaction(SenderAddress = from,
                                       To = ``to``,
                                       Init = code,
                                       DeployAddress = reqAddr,
                                       Value = value,
                                       Data = data,
                                       GasLimit = TX_GASLIMIT,
                                       GasPrice = UInt256 (TX_GASPRICE: int64))
  processor.Execute(tx, block.Header, tracer)
  tracer.StatusCode

let private deploy env deployer addr code value data timestamp blocknum =
  let code = Array.append code data
  let status = runTx env deployer null code addr value [| |] timestamp blocknum
  if status <> StatusCode.Success then deployFailCount <- deployFailCount + 1

let private setupAgent env deployer addr agentCode =
  let timestamp = DEFAULT_TIMESTAMP
  let blocknum = DEFAULT_BLOCKNUM
  deploy env deployer addr agentCode (UInt256 0L) [||] timestamp blocknum

let private setupEntity env tc entity =
  let state = env.State
  let vm = env.VM
  let specProvider = env.SpecProvider
  let targDeployer = tc.TargetDeployer
  let deployTx = tc.DeployTx
  let spec = specProvider.GetSpec(deployTx.Blocknum)
  match entity.Agent with
  | NoAgent ->
    state.CreateAccount(entity.Account, &entity.Balance)
    if targDeployer <> entity.Account then vm.RegisterUser(entity.Account)
  | SFuzzAgent contAddr ->
    let zero = UInt256(0I)
    state.CreateAccount(entity.Account, &zero)
    setupAgent env entity.Account contAddr sFuzzAgentCode
    state.AddToBalance(contAddr, &entity.Balance, spec)
    // sFuzz doesn't distinguish deployer and user.
  | SmartianAgent contAddr ->
    let zero = UInt256(0I)
    state.CreateAccount(entity.Account, &zero)
    setupAgent env entity.Account contAddr smartianAgentCode
    state.AddToBalance(contAddr, &entity.Balance, spec)
    if targDeployer <> contAddr then vm.RegisterUser(contAddr)

let private setupTarget env initEther deployer addr tx =
  let vm = env.VM
  let value = tx.Value
  let data = tx.Data
  let timestamp = tx.Timestamp
  let blocknum = tx.Blocknum
  vm.IsDeployingTarget <- true
  deploy env deployer addr targCode value data timestamp blocknum
  if initEther > 0I && env.State.GetState(addr) <> null then
    let initEtherU256 = UInt256 initEther
    let spec = env.SpecProvider.GetSpec(blocknum)
    env.State.AddToBalance(addr, &initEtherU256, spec)
  vm.IsDeployingTarget <- false
  vm.TargetContractAddr <- addr
  vm.TargetOwnerAddr <- deployer

let toBugType bugClass fname pc =
  match bugClass with
  | BugClass.AssertionFailure -> BugType.AssertionFailure (bugClass, pc)
  | BugClass.ArbitraryWrite -> BugType.ArbitraryWrite (bugClass, pc)
  | BugClass.BlockstateDependency -> BugType.BlockstateDependency (bugClass, pc)
  | BugClass.BlockstateDependencySFuzz -> BugType.BlockstateDependencySFuzz (bugClass, pc)
  | BugClass.BlockstateDependencyILF -> BugType.BlockstateDependencyILF (bugClass, pc)
  | BugClass.BlockstateDependencyMythril -> BugType.BlockstateDependencyMythril (bugClass, pc)
  | BugClass.BlockstateDependencyManticore -> BugType.BlockstateDependencyManticore (bugClass, pc)
  | BugClass.ControlHijack -> BugType.ControlHijack (bugClass, pc)
  | BugClass.EtherLeak -> BugType.EtherLeak (bugClass, fname, pc)
  | BugClass.EtherLeakStrict -> BugType.EtherLeakStrict (bugClass, fname, pc)
  | BugClass.IntegerBug -> BugType.IntegerBug (bugClass, pc)
  | BugClass.IntegerBugSFuzz -> BugType.IntegerBugSFuzz (bugClass, pc)
  | BugClass.IntegerBugMythril -> BugType.IntegerBugMythril (bugClass, pc)
  | BugClass.IntegerBugManticore -> BugType.IntegerBugManticore (bugClass, pc)
  | BugClass.MishandledException -> BugType.MishandledException (bugClass, pc)
  | BugClass.MishandledExceptionSFuzz -> BugType.MishandledExceptionSFuzz (bugClass, pc)
  | BugClass.MishandledExceptionILF -> BugType.MishandledExceptionILF (bugClass, pc)
  | BugClass.MishandledExceptionMythril -> BugType.MishandledExceptionMythril (bugClass, pc)
  | BugClass.MishandledExceptionManticore -> BugType.MishandledExceptionManticore (bugClass, pc)
  | BugClass.MultipleSend -> BugType.MultipleSend (bugClass, pc)
  | BugClass.Reentrancy -> BugType.Reentrancy (bugClass, pc)
  | BugClass.ReentrancySFuzz -> BugType.ReentrancySFuzz (bugClass, pc)
  | BugClass.ReentrancyILF ->BugType. ReentrancyILF (bugClass, pc)
  | BugClass.ReentrancyMythril -> BugType.ReentrancyMythril (bugClass, pc)
  | BugClass.ReentrancyManticore -> BugType.ReentrancyManticore (bugClass, pc)
  | BugClass.SuicidalContract -> BugType.SuicidalContract (bugClass, fname, pc)
  | BugClass.SuicidalContractStrict -> BugType.SuicidalContractStrict (bugClass, fname, pc)
  | BugClass.TransactionOriginUse -> BugType.TransactionOriginUse (bugClass, pc)
  | BugClass.FreezingEther -> BugType.FreezingEther (bugClass, pc)
  | BugClass.RequirementViolation -> BugType.RequirementViolation (bugClass, pc)

let classOfBug bug = 
  match bug with
  | BugType.AssertionFailure (bugclass, pc) | BugType.ArbitraryWrite (bugclass, pc) | BugType.BlockstateDependency (bugclass, pc)
  | BugType.BlockstateDependencySFuzz (bugclass, pc) | BugType.BlockstateDependencyILF (bugclass, pc) | BugType.BlockstateDependencyMythril (bugclass, pc)
  | BugType.BlockstateDependencyManticore (bugclass, pc) | BugType.ControlHijack (bugclass, pc) | BugType.EtherLeak (bugclass, _, pc)
  | BugType.EtherLeakStrict (bugclass, _, pc) | BugType.IntegerBug (bugclass, pc) | BugType.IntegerBugSFuzz (bugclass, pc)
  | BugType.IntegerBugMythril (bugclass, pc) | BugType.IntegerBugManticore (bugclass, pc) | BugType.MishandledException (bugclass, pc)
  | BugType.MishandledExceptionSFuzz (bugclass, pc) | BugType.MishandledExceptionILF (bugclass, pc) | BugType.MishandledExceptionMythril (bugclass, pc)
  | BugType.MishandledExceptionManticore (bugclass, pc) | BugType.MultipleSend (bugclass, pc) | BugType.Reentrancy (bugclass, pc)
  | BugType.ReentrancySFuzz (bugclass, pc) | BugType.ReentrancyILF (bugclass, pc) | BugType.ReentrancyMythril (bugclass, pc)
  | BugType.ReentrancyManticore (bugclass, pc) | BugType.SuicidalContract (bugclass, _, pc) | BugType.SuicidalContractStrict (bugclass, _, pc)
  | BugType.TransactionOriginUse (bugclass, pc) | BugType.FreezingEther (bugclass, pc) | BugType.RequirementViolation (bugclass, pc) -> bugclass

let pcOfBug bug =
  match bug with
  | BugType.AssertionFailure (bugclass, pc) | BugType.ArbitraryWrite (bugclass, pc) | BugType.BlockstateDependency (bugclass, pc)
  | BugType.BlockstateDependencySFuzz (bugclass, pc) | BugType.BlockstateDependencyILF (bugclass, pc) | BugType.BlockstateDependencyMythril (bugclass, pc)
  | BugType.BlockstateDependencyManticore (bugclass, pc) | BugType.ControlHijack (bugclass, pc) | BugType.EtherLeak (bugclass, _, pc)
  | BugType.EtherLeakStrict (bugclass, _, pc) | BugType.IntegerBug (bugclass, pc) | BugType.IntegerBugSFuzz (bugclass, pc)
  | BugType.IntegerBugMythril (bugclass, pc) | BugType.IntegerBugManticore (bugclass, pc) | BugType.MishandledException (bugclass, pc)
  | BugType.MishandledExceptionSFuzz (bugclass, pc) | BugType.MishandledExceptionILF (bugclass, pc) | BugType.MishandledExceptionMythril (bugclass, pc)
  | BugType.MishandledExceptionManticore (bugclass, pc) | BugType.MultipleSend (bugclass, pc) | BugType.Reentrancy (bugclass, pc)
  | BugType.ReentrancySFuzz (bugclass, pc) | BugType.ReentrancyILF (bugclass, pc) | BugType.ReentrancyMythril (bugclass, pc)
  | BugType.ReentrancyManticore (bugclass, pc) | BugType.SuicidalContract (bugclass, _, pc) | BugType.SuicidalContractStrict (bugclass, _, pc)
  | BugType.TransactionOriginUse (bugclass, pc) | BugType.FreezingEther (bugclass, pc) | BugType.RequirementViolation (bugclass, pc) -> pc

let private sendTx env isAcc hadDepTx isRedirect tx =
  let vm = env.VM
  vm.ResetPerTx()
  vm.HadDeployerTx <- hadDepTx
  vm.IsRedirected <- isRedirect
  runTx env tx.From tx.To null null tx.Value tx.Data tx.Timestamp tx.Blocknum
  |> ignore
  if isAcc then
    accumDeployEdges.UnionWith(vm.VisitedDeployEdges)
    accumRuntimeEdges.UnionWith(vm.VisitedRuntimeEdges)
    accumRuntimeInstrs.UnionWith(vm.VisitedRuntimeInstrs)
    accumDUChains.UnionWith(vm.DefUseChainSet)
    accumBugs <- Set.ofSeq vm.BugSet
                 |> Set.map (fun struct (bugClass, pc) -> toBugType bugClass tx.Function pc)
                 |> Set.union accumBugs

// Check if a non-deployer user obtains ether by sending this TX. We check the
// new balance against both the initial balance and balance before this TX. This
// is to make sure that the user is actively (not passively) gaining ether.

let private checkEtherLeak env isAcc sender isDepTx hadDepTx initBal prevBal userPrevBals tx =
  let updatedBal = env.State.GetBalance(sender)
  let senderEtherGained = updatedBal > initBal && updatedBal > prevBal
  let otherEtherGained = List.exists (
    fun addr ->
      let updatedBal = env.State.GetBalance(addr)
      let prevBal = Map.find (Address.toStr addr) userPrevBals
      updatedBal > initBal && updatedBal > prevBal) Address.USER_CONTRACTS
  let bugPC = env.VM.BugOracle.LastEtherSendPC
  // If there was any previous TX from the deployer, the contract ownership
  // could have been transferred legitimately. Therefore, we report an EL bug
  // with less confidence in such cases.
  // If an untrusted user other than the sender (not the owner) gets the ether,
  // then we report an EL bug with less confidence.
  if isAcc && not isDepTx then
    if senderEtherGained then
      if hadDepTx then accumBugs <- Set.add (toBugType BugClass.EtherLeak tx.Function bugPC) accumBugs
      else accumBugs <- Set.add (toBugType BugClass.EtherLeakStrict tx.Function bugPC) accumBugs
    elif otherEtherGained then
      if isAcc && not isDepTx then accumBugs <- Set.add (toBugType BugClass.EtherLeak tx.Function bugPC) accumBugs

let private processTx env tc isAcc (accNewBugs, hadDepTx) i tx =
  // Since we removed the foremost deploying transaction, sould +1 to the index.
  let i = i + 1
  let sender = tx.From
  let isDepTx = (sender = tc.TargetDeployer)
  let hadDepTx = hadDepTx || isDepTx
  let initBal, isRedirect =
    match List.tryFind (fun e -> Entity.getSender e = sender) tc.Entities with
    | Some entity -> (entity.Balance, Entity.isTXRedirected tx.To entity)
    | None -> failwithf "Invalid sender: %s" (Address.toStr sender)
  let prevBal = env.State.GetBalance(sender)
  let prevBugs = accumBugs
  let userPrevBals = List.fold (fun acc user -> Map.add (Address.toStr user) (env.State.GetBalance(user)) acc) Map.empty Address.USER_CONTRACTS
  sendTx env isAcc hadDepTx isRedirect tx
  checkEtherLeak env isAcc sender isDepTx hadDepTx initBal prevBal userPrevBals tx
  let accNewBugs = Set.difference accumBugs prevBugs
                |> Set.map (fun bug -> (bug, i))
                |> Set.union accNewBugs
  (accNewBugs, hadDepTx)

let private filterBugs checkOptional useOthersOracle bugs =
  let shouldSkip (bug, ith) =
    let bugtype = classOfBug bug
    if not checkOptional && BugClassHelper.isOptional bugtype then true
    elif not useOthersOracle && BugClassHelper.isFromOtherTools bugtype then true
    else false
  Set.filter (not << shouldSkip) bugs

/// Execute a seed (= transaction list) on EVM and return feedback.
let execute tc isAcc initEther traceDU checkOptional useOthersOracle =
  let env = initTestingEnv ()
  List.iter (setupEntity env tc) tc.Entities
  setupTarget env initEther tc.TargetDeployer tc.TargetContract tc.DeployTx
  env.VM.TraceDU <- traceDU
  let oldDeployEdgeCount = accumDeployEdges.Count
  let oldRuntimeEdgeCount = accumRuntimeEdges.Count
  let oldDUChainCount = accumDUChains.Count
  let bugs = List.foldi (processTx env tc isAcc) (Set.empty, false) tc.Txs
             |> fst |> filterBugs checkOptional useOthersOracle
  let deployCovGain = accumDeployEdges.Count > oldDeployEdgeCount
  let runtimeCovGain = accumRuntimeEdges.Count > oldRuntimeEdgeCount
  let covGain = deployCovGain || runtimeCovGain
  let duGain = accumDUChains.Count > oldDUChainCount
  let conv struct (pc, op, oprnd1, oprnd2) = (uint64 pc, op, oprnd1, oprnd2)
  let cmpList = List.map conv (List.ofSeq env.VM.CmpList)
  let contractBalance = env.State.GetBalance(Address.TARG_CONTRACT)
  receivedEther <- receivedEther || contractBalance > (UInt256 0L)
  useDelegateCall <- useDelegateCall || env.VM.BugOracle.UseDelegateCall
  canSendEther <- canSendEther || env.VM.BugOracle.SendEtherIndependently
  { CovGain = covGain
    DUGain = duGain
    CmpList = cmpList
    BugSet = bugs }

(*** Statistics ***)

let mutable totalExecutions = 0
let mutable phaseExecutions = 0

let getTotalExecutions () = totalExecutions
let getPhaseExecutions () = phaseExecutions
let resetPhaseExecutions () = phaseExecutions <- 0

(*** Resource scheduling ***)

let mutable allowedExecutions = 0
let allocateResource n = allowedExecutions <- n
let isExhausted () = allowedExecutions <= 0
let incrExecutionCount () =
  allowedExecutions <- allowedExecutions - 1
  totalExecutions <- totalExecutions + 1
  phaseExecutions <- phaseExecutions + 1

let private parseBranchInfo tryVal cmp =
  let addr, opStr, (oprnd1: bigint), (oprnd2: bigint)= cmp
  let dist = oprnd1 - oprnd2
  let brType =
    match opStr with
    | "==" -> Equality
    | "!=" -> Equality
    | ">=s" -> SignedSize
    | ">s" -> SignedSize
    | "<=s" -> SignedSize
    | "<s" -> SignedSize
    | ">=u" -> UnsignedSize
    | ">u" -> UnsignedSize
    | "<=u" -> UnsignedSize
    | "<u" -> UnsignedSize
    | _ -> failwithf "Unimplemented operation string : %s" opStr
  { InstAddr = addr
    BrType = brType
    TryVal = tryVal
    OpSize = 32
    Oprnd1 = oprnd1
    Oprnd2 = oprnd2
    Distance = dist }

let rec private parseBranchInfoAtAux tryVal targPoint accMap cmpList =
  match cmpList with
  | [] -> None
  | headCmp :: tailCmpList ->
    let addr, opStr, oprnd1, oprnd2 = headCmp
    // Caution : we count first visit as '1', instead of '0'.
    let count = if Map.containsKey addr accMap then Map.find addr accMap else 1
    if (addr, count) = (targPoint.Addr, targPoint.Idx) then
      Some (parseBranchInfo tryVal headCmp)
    else
      let newMap = Map.add addr (count + 1) accMap
      parseBranchInfoAtAux tryVal targPoint newMap tailCmpList

let private parseBranchInfoAt tryVal targPoint cmpList =
  parseBranchInfoAtAux tryVal targPoint Map.empty cmpList

let private parseBranchTrace tryVal cmpList =
  List.map (parseBranchInfo tryVal) cmpList

(*** Tracer execute functions ***)

let private runEVM opt seed isAcc =
  incrExecutionCount ()
  let tc = Seed.concretize seed
  let initEther = opt.InitEther
  let traceDU = opt.DynamicDFA
  let checkOptional = opt.CheckOptionalBugs
  let useOthersOracle = opt.UseOthersOracle
  execute tc isAcc initEther traceDU checkOptional useOthersOracle

(*** Top-level executor functions ***)

let getCoverage opt seed =
  let f = runEVM opt seed true
  f.CovGain, f.DUGain, f.BugSet

let getBranchTrace opt seed tryVal =
  let f = runEVM opt seed false
  parseBranchTrace tryVal f.CmpList

let getBranchInfoAt opt seed tryVal targPoint =
  let f = runEVM opt seed false
  parseBranchInfoAt tryVal targPoint f.CmpList
