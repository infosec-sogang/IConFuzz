module solAnalysis.RunProcess

open System
open System.Diagnostics
open System.IO

let runProcess cmd args =
    let startInfo = ProcessStartInfo(
        FileName = cmd,
        Arguments = args,
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        UseShellExecute = false,
        CreateNoWindow = true
    )
    let proc = new Process(StartInfo = startInfo)
    proc.Start() |> ignore 
    proc