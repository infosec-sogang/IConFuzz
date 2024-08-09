module solAnalysis.Options

open Argu


type AnalysisCLI = 
    | [<AltCommandLine("-i")>] [<Mandatory>] [<Unique>] Input of string
    | [<AltCommandLine("-o")>] [<Unique>] OutputDir of string
    | [<AltCommandLine("-v")>] [<Unique>] Solv of string
    | [<AltCommandLine("-m")>] [<Unique>] Main of string
    | [<AltCommandLine("-c")>] [<Unique>] Cfg

    with
        interface IArgParserTemplate with
            member s.Usage =
                match s with
                | Input _ -> "Target solidity file for analysis."
                | OutputDir _ -> "Output directory for analysis results."
                | Solv _ -> "Solidity version."
                | Main _ -> "Main contract name."
                | Cfg -> "Show control flow graph."

type AnalysisOptions = { 
    Input       : string
    OutDir      : string
    Solv        : string
    Main        : string 
    Cfg         : bool
}
let mutable main_contract = ""
let mutable cfg = false
let mutable solc_ver = ""
let mutable mode = "verify"
let mutable debug = ""
let mutable inline_depth = 0

let parseOption (args: string array) =
    let cmdPrefix = "dotnet run -input" 
    let parser = ArgumentParser.Create<AnalysisCLI> (programName = cmdPrefix)
    let r = try parser.Parse(args) with 
            :? Argu.ArguParseException -> printfn "%s" (parser.PrintUsage()); exit 1
    main_contract <- r.GetResult (<@ Main @>, defaultValue = "")
    solc_ver <- r.GetResult (<@ Solv @>, defaultValue = "")
    cfg <- r.Contains (<@ Cfg @>)
    { Input = r.GetResult (<@ Input @>)
      OutDir = r.GetResult (<@ OutputDir @>, defaultValue = "")
      Solv = r.GetResult (<@ Solv @>, defaultValue = "")
      Main = r.GetResult (<@ Main @>, defaultValue = "")
      Cfg = r.Contains (<@ Cfg @>)
    }