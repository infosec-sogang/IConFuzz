module IConFuzz.Fuzz

open solAnalysis
open System.Diagnostics
open Utils
open Config
open Options
open Solc

exception BuildError

let mutable program_file = ""

let private makeSingletonSeeds contSpec =
  let constrSpec = contSpec.Constructor
  let funcSpecs = contSpec.NormalFunctions |> Array.toList
  List.map (fun funcSpec -> Seed.init constrSpec [| funcSpec |]) funcSpecs

let private sequenceToSeed contSpec seq =
  let constrSpec = contSpec.Constructor
  let funcSpecs = contSpec.NormalFunctions
  let findSpec s = Array.find (fun spec -> FuncSpec.getName spec = s) funcSpecs
  let funcSpecs = List.map findSpec seq |> List.toArray
  Seed.init constrSpec funcSpecs

let private initializeWithoutDFA opt =
  let contSpec = ABI.parse opt.ABIPath
  (contSpec, makeSingletonSeeds contSpec, Set.empty, Set.empty, Set.empty)

let private initializeWithDFA (opt: FuzzOption) =
  let prog = program_file
  let outdir, mainContract, solv, cfg = opt.OutDir, opt.MainContract, opt.SolcVersion, false
  let opt' = { Input = prog; OutDir = outdir; Solv = solv; Main = mainContract; Cfg = cfg }
  let contSpec, seqs, duchains, mapKeyChains, privChains = TopLevel.run opt'
  if List.isEmpty seqs // No DU chain at all.
  then (contSpec, makeSingletonSeeds contSpec, duchains, mapKeyChains, privChains)
  else (contSpec, List.map (sequenceToSeed contSpec) seqs, duchains, mapKeyChains, privChains)


/// Allocate testing resource for each strategy (grey-box concolic testing and
/// random fuzz testing). Resource is managed through 'the number of allowed
/// program execution'. If the number of instrumented program execution exceeds
/// the specified number, the strategy will be switched.
let private allocResource () =
  let concolicEff = GreyConcolic.evaluateEfficiency ()
  let randFuzzEff = RandomFuzz.evaluateEfficiency ()
  let concolicRatio = concolicEff / (concolicEff + randFuzzEff)
  // Bound alloc ratio with 'MinResourceAlloc', to avoid extreme biasing
  let concolicRatio = max MIN_RESOURCE_RATIO (min MAX_RESOURCE_RATIO concolicRatio)
  let randFuzzRatio = 1.0 - concolicRatio
  let totalBudget = EXEC_BUDGET_PER_ROUND
  let greyConcBudget = int (float totalBudget * concolicRatio)
  let randFuzzBudget = int (float totalBudget * randFuzzRatio)
  if greyConcBudget < 0 || randFuzzBudget < 0 then (200, 200)
  else (greyConcBudget, randFuzzBudget)

let private printNewSeeds newSeeds =
  let count = List.length newSeeds
  let concolicStr = String.concat "========\n" (List.map Seed.toString newSeeds)
  log "Generated %d seeds for grey-box concolic : [ %s ]" count concolicStr

let private rewindCursors seed =
  Array.collect Seed.rewindByteCursors (Array.ofList seed)
  |> Array.toList

let rec private greyConcolicLoop opt concQ randQ =
  if Executor.isExhausted () || ConcolicQueue.isEmpty concQ then (concQ, randQ)
  else let seed, concQ = ConcolicQueue.dequeue concQ
       if opt.Verbosity >= 3 then
         log "Grey-box concolic on seed : %s" (Seed.toString seed)
       let newSeeds = GreyConcolic.run seed opt
       // Move cursors of newly generated seeds.
       let rewindedSeeds = rewindCursors newSeeds
       // Also generate seeds by just stepping the cursor of original seed.
       let steppedSeeds = Seed.stepByteCursor seed
       let concQ = List.fold ConcolicQueue.enqueue concQ rewindedSeeds
       let concQ = List.fold ConcolicQueue.enqueue concQ steppedSeeds
       // Note that 'Stepped' seeds are not enqueued for random fuzzing.
       let randQ = List.fold RandFuzzQueue.enqueue randQ newSeeds
       if opt.Verbosity >= 4 then printNewSeeds (rewindedSeeds @ steppedSeeds)
       greyConcolicLoop opt concQ randQ

let private repeatGreyConcolic opt concQ randQ concolicBudget =
  if opt.Verbosity >= 2 then log "Grey-box concoclic testing phase starts"
  Executor.allocateResource concolicBudget
  Executor.resetPhaseExecutions ()
  let tcNumBefore = TCManage.getTestCaseCount ()
  let concQ, randQ = greyConcolicLoop opt concQ randQ
  let tcNumAfter = TCManage.getTestCaseCount ()
  let concolicExecNum = Executor.getPhaseExecutions ()
  let concolicNewTCNum = tcNumAfter - tcNumBefore
  GreyConcolic.updateStatus concolicExecNum concolicNewTCNum
  (concQ, randQ)

let rec private randFuzzLoop opt contSpec duchains mapKeyChains privChains concQ randQ =
  // Random fuzzing seeds are involatile, so don't have to check emptiness.
  if Executor.isExhausted () then (concQ, randQ)
  else let seed, randQ = RandFuzzQueue.fetch randQ
       if opt.Verbosity >= 3 then
         log "Random fuzzing on seed : %s" (Seed.toString seed)
       let newSeeds = RandomFuzz.run seed opt contSpec duchains mapKeyChains privChains
       let rewindedSeeds = rewindCursors newSeeds
       let concQ = List.fold ConcolicQueue.enqueue concQ rewindedSeeds
       let randQ = List.fold RandFuzzQueue.enqueue randQ newSeeds
       if opt.Verbosity >= 4 then printNewSeeds rewindedSeeds
       randFuzzLoop opt contSpec duchains mapKeyChains privChains concQ randQ

let private repeatRandFuzz opt contSpec duchains mapKeyChains privChains concQ randQ randFuzzBudget =
  if opt.Verbosity >= 2 then log "Random fuzzing phase starts"
  Executor.allocateResource randFuzzBudget
  Executor.resetPhaseExecutions ()
  let tcNumBefore = TCManage.getTestCaseCount ()
  let concQ, randQ = randFuzzLoop opt contSpec duchains mapKeyChains privChains concQ randQ
  let tcNumAfter = TCManage.getTestCaseCount ()
  let randExecNum = Executor.getPhaseExecutions ()
  let randNewTCNum = tcNumAfter - tcNumBefore
  RandomFuzz.updateStatus randExecNum randNewTCNum
  (concQ, randQ)

let rec private fuzzLoop opt contSpec duchains mapKeyChains privChains concQ randQ =
  let concolicBudget, randFuzzBudget = allocResource ()
  let concQSize = ConcolicQueue.size concQ
  let randQSize = RandFuzzQueue.size randQ
  if opt.Verbosity >= 2 then
    log "Concolic budget: %d, Rand budget: %d" concolicBudget randFuzzBudget
    log "Concolic queue size: %d, Random Queue size: %d" concQSize randQSize
  // Perform grey-box concolic testing
  let concQ, randQ = repeatGreyConcolic opt concQ randQ concolicBudget
  // Perform random fuzzing
  let concQ, randQ = repeatRandFuzz opt contSpec duchains mapKeyChains privChains concQ randQ randFuzzBudget
  fuzzLoop opt contSpec duchains mapKeyChains privChains concQ randQ

let private fuzzingTimer opt = async {
  let timespan = System.TimeSpan (0, 0, 0, opt.Timelimit)
  System.Threading.Thread.Sleep (timespan)
  printLine "Fuzzing timeout expired."
  if opt.CheckOptionalBugs then TCManage.checkFreezingEtherBug ()
  log "===== Statistics ====="
  TCManage.printStatistics ()
  log "Done, clean up and exit..."
  exit (0)
}

let private prepareBinAbi inputPath solv mainc =
  let proc = runProcess "bash" (sprintf "%s %s %s %s" "./scripts/build.sh" inputPath solv mainc)
  proc.WaitForExit()
  if proc.ExitCode <> 0 then raise BuildError

let run args =
  let opt = parseFuzzOption args
  assertFileExists opt.ProgPath
  if opt.SolcVersion <> "" then prepareBinAbi opt.ProgPath opt.SolcVersion opt.MainContract
  else prepareBinAbi opt.ProgPath (decide opt.ProgPath) opt.MainContract
  let fileName = opt.ProgPath.Split('/') |> Array.last |> fun f -> f.Replace(".sol", "")
  program_file <- opt.ProgPath
  let opt = {
    opt with
      ProgPath = (sprintf "tmp/bin/%s.bin" fileName);
      ABIPath = (sprintf "tmp/abi/%s.abi" fileName)
  }
  log "Fuzz target : %s" opt.ProgPath
  log "Fuzzing starts at %s" (startTime.ToString("hh:mm:ss"))
  log "Time limit : %d s" opt.Timelimit
  Async.Start (fuzzingTimer opt)
  createDirectoryIfNotExists opt.OutDir
  TCManage.initialize opt.OutDir opt.TargetBugs
  Executor.initialize opt.ProgPath

  // let contSpec, initSeeds = initializeWithoutDFA opt
  let contSpec, initSeeds, duchains, mapKeyChains, privChains =  if opt.DynamicDFA then initializeWithDFA opt
                                                                      else initializeWithoutDFA opt
  let concQ = List.fold ConcolicQueue.enqueue ConcolicQueue.empty initSeeds
  let randQ = List.fold RandFuzzQueue.enqueue (RandFuzzQueue.init ()) initSeeds
  log "Start main fuzzing phase"
  fuzzLoop opt contSpec duchains mapKeyChains privChains concQ randQ
