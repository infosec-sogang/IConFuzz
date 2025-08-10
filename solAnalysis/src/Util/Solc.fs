module solAnalysis.Solc

open RunProcess
open Options
open System
open FSharp.Data
open FSharp.Data.JsonExtensions

exception CompilationError
exception UnsupportedSolc

let solv_lst = 
    ["0.4.16"; "0.4.17"; "0.4.18"; "0.4.19"; "0.4.20"; "0.4.21"; "0.4.23"; "0.4.24"; "0.4.25"; "0.4.26";
   "0.5.0"; "0.5.1"; "0.5.2"; "0.5.3"; "0.5.4"; "0.5.5"; "0.5.6"; "0.5.7"; "0.5.8"; "0.5.9"; "0.5.10";
   "0.5.11"; "0.5.12"; "0.5.13"; "0.5.14"; "0.5.15"; "0.5.16"; "0.5.17";
   "0.6.0"; "0.6.1"; "0.6.2"; "0.6.3"; "0.6.4"; "0.6.5"; "0.6.6"; "0.6.7"; "0.6.8"; "0.6.9"; "0.6.10"; "0.6.11"; "0.6.12";
   "0.7.0"; "0.7.1"; "0.7.2"; "0.7.3"; "0.7.4"; "0.7.5"; "0.7.6";
   "0.8.0"; "0.8.1"; "0.8.2"; "0.8.3"; "0.8.4"; "0.8.5"; "0.8.6"; "0.8.7"; "0.8.8"; "0.8.9"; "0.8.10"]

let get_solc (solv: string) =
    if solv = "" then "solc"
    else if solv = "0.5.0" then "solc_0.5.1" (* solc_0.5.0 --ast-compact-json produces a solc error. *)
    else if solv.StartsWith "0.4" && not (List.contains solv solv_lst) then "solc_0.4.25"
    else if List.contains solv solv_lst then "solc_" + solv (* e.g., solc_0.4.25 *)
    else raise UnsupportedSolc

let get_json_ast opt = 
    let rec get_json_ast_inner file solcs =
        match solcs with
        | [] -> raise CompilationError
        | solc::tailseq ->
            let solc = ".solc/" + solc
            let proc = runProcess solc (sprintf "--ast-compact-json %s" file)
            try 
                let buf = proc.StandardOutput
                for _ in 1 .. 4 do buf.ReadLine() |> ignore
                let json = buf.ReadToEnd()
                proc.WaitForExit()
                match proc.ExitCode with
                | 0 -> 
                    let json_ast = JsonValue.Parse(json)
                    json_ast
                | _ -> get_json_ast_inner file tailseq
            with
                | e ->
                    proc.WaitForExit()
                    match proc.ExitCode with
                    | n when n <> 0 -> get_json_ast_inner file tailseq
                    | _ -> raise e
     
    let solc = get_solc opt.Solv
    let solcs = if solc.StartsWith("solc_0.4.1") then [solc; "solc_0.4.25"] else [solc]
    get_json_ast_inner opt.Input solcs