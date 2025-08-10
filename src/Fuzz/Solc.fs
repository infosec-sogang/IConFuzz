module IConFuzz.Solc

open System.IO
open Utils

exception UnsupportedSolc

let solv_lst = ["0.4.16"; "0.4.17"; "0.4.18"; "0.4.19"; "0.4.20"; "0.4.21"; "0.4.23"; "0.4.24"; "0.4.25"; "0.4.26";
"0.5.0"; "0.5.1"; "0.5.2"; "0.5.3"; "0.5.4"; "0.5.5"; "0.5.6"; "0.5.7"; "0.5.8"; "0.5.9"; "0.5.10";
"0.5.11"; "0.5.12"; "0.5.13"; "0.5.14"; "0.5.15"; "0.5.16"; "0.5.17";
"0.6.0"; "0.6.1"; "0.6.2"; "0.6.3"; "0.6.4"; "0.6.5"; "0.6.6"; "0.6.7"; "0.6.8"; "0.6.9"; "0.6.10"; "0.6.11"; "0.6.12";
"0.7.0"; "0.7.1"; "0.7.2"; "0.7.3"; "0.7.4"; "0.7.5"; "0.7.6";
"0.8.0"; "0.8.1"; "0.8.2"; "0.8.3"; "0.8.4"; "0.8.5"; "0.8.6"; "0.8.7"; "0.8.8"; "0.8.9"; "0.8.10"; "0.8.11"; "0.8.12";
"0.8.13"; "0.8.14"; "0.8.15"; "0.8.16"; "0.8.17"; "0.8.18"; "0.8.19"; "0.8.20"; "0.8.21"; "0.8.22"; "0.8.23";
"0.8.24"; "0.8.25"; "0.8.26"]

let findMaxVersion (versionConstraint: string) =
    solv_lst
    |> List.filter (fun v -> System.Version.Parse(v) < System.Version.Parse(versionConstraint))
    |> List.maxBy System.Version.Parse

let findMinVersion (versionConstraint: string) =
    solv_lst
    |> List.filter (fun v -> System.Version.Parse(v) > System.Version.Parse(versionConstraint))
    |> List.minBy System.Version.Parse

// Extract a solc version from the solidity file given
let extractVersion (inputPath: string) =
    let lines = File.ReadAllLines(inputPath)
    let extractVersionFromLine (line: string) =
      if line.Contains("pragma solidity") then
        let parts = line.Split(' ')
        let version = parts.[parts.Length - 1].Replace(";", "").Trim()
        if version.StartsWith("^") then version.Substring(1)
        elif version.StartsWith(">=") || version.StartsWith("<=") then version.Substring(2)
        elif version.StartsWith("<") then findMaxVersion (version.Substring 1)
        elif version.StartsWith(">") then findMinVersion (version.Substring 1)
        else version
      else
        ""
  
    lines
    |> Array.tryPick (fun line ->
      let version = extractVersionFromLine(line)
      if version <> "" then Some(version) else None)
    |> function
      | Some(version) -> version
      | None -> "" // Return empty string if version not specified.


let rec findCompilableSolc lst inputPath =
    match lst with
    | hd::tl -> 
        let proc = runProcess ("./.solc/solc_" + hd) inputPath
        proc.WaitForExit()
        match proc.ExitCode with
        | 0 -> hd
        | _ -> findCompilableSolc tl inputPath
    | _ -> raise UnsupportedSolc

let resolveSolc (solv: string) (inputPath: string) =
    if solv = "0.5.0" then "0.5.1"
    elif solv.StartsWith("0.4") && not (List.contains solv solv_lst) then "0.4.25"
    elif List.contains solv solv_lst then findCompilableSolc (solv::solv_lst) inputPath
    else
        findCompilableSolc solv_lst inputPath
    
let decide (inputPath: string) : string  = 
    resolveSolc (extractVersion inputPath) inputPath
    