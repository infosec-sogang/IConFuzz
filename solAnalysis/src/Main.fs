module solAnalysis.Main

open Options


let printUsage () =
    printfn "Usage: dotnet run --input <sol> <options..>"
    exit 0

[<EntryPoint>]
let main argv =
  if argv.Length = 0 then printUsage ()
  let opt = Options.parseOption argv |> TopLevel.run |> ignore
  0