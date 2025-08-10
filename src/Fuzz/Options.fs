module IConFuzz.Options

open Argu
open Utils
open System.Numerics
open Nethermind.Evm

type FuzzerCLI =
  | [<AltCommandLine("-p")>] [<Unique>] Program of path: string
  | [<AltCommandLine("-v")>] [<Unique>] Verbose of int
  | [<AltCommandLine("-t")>] [<Mandatory>] [<Unique>] Timelimit of sec: int
  | [<AltCommandLine("-o")>] [<Mandatory>] [<Unique>] OutputDir of path: string
  | [<AltCommandLine("-b")>] [<Unique>] TargetBug of typeAndAddress: string
  | [<AltCommandLine("-m")>] [<Mandatory>] [<Unique>] MainContract of string
  | [<AltCommandLine("-s")>] [<Unique>] SolcVersion of string
  | [<Unique>] NoDDFA
  | [<Unique>] CheckOptionalBugs
  | [<Unique>] UseOthersOracle
  | [<Unique>] InitEther of amount: BigInteger
with
  interface IArgParserTemplate with
    member s.Usage =
      match s with
      | Program _ -> "Target source file for test case generation with fuzzing."
      | Verbose _ -> "Verbosity level to control debug messages."
      | Timelimit _ -> "Timeout for fuzz testing (in seconds)."
      | OutputDir _ -> "Directory to store testcase outputs."
      | MainContract _ -> "Name of the main contract of the target source file."
      | SolcVersion _ -> "Solc version specified by user."
      | NoDDFA -> "Disable dynamic data-flow analysis during the fuzzing."
      | CheckOptionalBugs ->
        "Detect optional bugs (e.g. requirement violation) disabled by default."
      | UseOthersOracle ->
        "Report bugs using other tools' oracles as well.\n\
        Currently we support (BD/IB/ME/RE) X (sFuzz/ILF/Mythril/MANTICORE)."
      | InitEther _ -> "Initialize the target contract to have initial ether"
      | TargetBug _ ->
        "Target bugs to detect (pairs of bug type and location)\n\
        Ex) -b \"IB:6cb/6cf,EL:transferTo\"\n\
        Note that depending on bug type, location string format differs"

type FuzzOption = {
  Verbosity         : int
  OutDir            : string
  Timelimit         : int
  ProgPath          : string
  ABIPath           : string
  MainContract      : string
  SolcVersion       : string
  DynamicDFA        : bool
  CheckOptionalBugs : bool
  UseOthersOracle   : bool
  InitEther         : BigInteger
  TargetBugs        : (BugClass * string) array
}

let parseFuzzOption (args: string array) =
  let cmdPrefix = "dotnet IConFuzz.dll fuzz"
  let parser = ArgumentParser.Create<FuzzerCLI> (programName = cmdPrefix)
  let r = try parser.Parse(args) with
          :? Argu.ArguParseException -> printLine (parser.PrintUsage()); exit 1
  let targetBugStr = r.GetResult (<@ TargetBug @>, defaultValue = "")
  let targetBugs =
    targetBugStr.Split [|','|]
    |> Array.collect (fun target ->
      let tokens = target.Split [|':'; '/'|]
      let bug = BugClassHelper.toBugClass tokens.[0]
      Array.map (fun location -> (bug, location)) tokens.[1..])
  { Verbosity = r.GetResult (<@ Verbose @>, defaultValue = 1)
    OutDir = r.GetResult (<@ OutputDir @>)
    Timelimit = r.GetResult (<@ Timelimit @>)
    ProgPath = r.GetResult (<@ Program @>)
    ABIPath = ""
    MainContract = r.GetResult(<@ MainContract @>)
    SolcVersion = r.GetResult(<@ SolcVersion @>, defaultValue="")
    DynamicDFA = not (r.Contains(<@ NoDDFA @>)) // Enabled by default.
    CheckOptionalBugs = r.Contains(<@ CheckOptionalBugs @>)
    UseOthersOracle = r.Contains(<@ UseOthersOracle @>)
    InitEther = r.GetResult (<@ InitEther @>, defaultValue = 100000000000000000000I) // default: 100 ether
    TargetBugs = targetBugs }