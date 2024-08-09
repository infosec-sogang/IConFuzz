module solAnalysis.Translator

open FSharp.Data
open FSharp.Data.JsonExtensions
open System
open System.Numerics
open System.Globalization
open Vocab
open Lang
open Options

let end_of_lines = ref [-1]

let get_first_part (input: string) : string =
    input.Split([| ' ' |], System.StringSplitOptions.RemoveEmptyEntries)
    |> Array.head

let line_indicator : int list -> int -> int = 
    fun lst byte ->
    List.fold (fun (set,line) cur ->
        if not set && byte < cur then (true,line)
        else if set then (set,line)
        else (set,line+1)
    ) (false,1) lst
    |> (fun (_,n) -> n)

let get_loc : JsonValue -> loc = 
    fun json ->
    let seq = (json?src.AsString()).Split ':'
    let offset,len = int (Seq.item 0 seq), int (Seq.item 0 seq)
    {
        line = line_indicator end_of_lines.Value offset;
        finish_line = line_indicator end_of_lines.Value (offset+ len);
        offset = offset;
        len = len
    }

let get_id : JsonValue -> int = 
    fun json -> json?id.AsInteger()

(* a list of elementary type names *)
let type_list = ["address"; "bool"; "int"; "uint"; "byte"; "fixed"; "ufixed"; "bytes"; "string"]

(**********************)
(**********************)
(***** Translator *****)
(**********************)
(**********************)
(* nodeType: X *)
let rec trans_typeName (json: JsonValue) : (string *typ) = 
    let node_typ = json?nodeType
    match node_typ with
    | JsonValue.String "ElementaryTypeName" ->
        let typ = json?typeDescriptions?typeString.AsString()
        (get_first_part typ, EType (trans_elementaryTypeName typ))
    | JsonValue.String "Mapping" -> 
        let typ = json?typeDescriptions?typeString.AsString()
        let key = trans_elementaryTypeName typ
        let value = json?valueType |> trans_typeName
        (get_first_part typ, Mapping (key, snd value))
    | JsonValue.String "ArrayTypeName" ->
        let typ = json?typeDescriptions?typeString.AsString()
        let baseT = json?baseType |> trans_typeName 
        let length = json?length 
        match length with
        | JsonValue.Null -> (get_first_part typ, Array (snd baseT,None))
        | len -> (get_first_part typ, Array (snd baseT,Some (get_int (trans_expression len))))
    | JsonValue.String "UserDefinedTypeName" -> 
        let type_string = json?typeDescriptons?typeString.AsString()
        (get_first_part type_string, trans_str_to_typeName type_string)
    | JsonValue.String s -> raise (Failure ("Unsupported: trans_typeName " + s))
    | _ -> raise (Failure "Unsupported: trans_typeName")

and trans_struct_type : string -> typ = 
    fun str ->
    if not (str.StartsWith("struct")) then failwith "Assertion failed"
    let str' = str.Replace(" pointer", "")
    let final = str'.Replace("struct ", "") (* struct ContractName.StructName => ContractName.StructName *)
    let parts = final.Split '.'(* ContractName.StructName => (ContractName, StructName) *)
    Struct [parts.[0]; parts.[1]]

and trans_enum_type : string -> typ = 
    fun str ->
    if not (str.StartsWith("enum")) then failwith "Assertion failed"
    let str' = str.Replace(" pointer", "")
    let final = str'.Replace("enum ", "") (* struct tmp.tmp1 => tmp.tmp1 *)
    let parts = final.Split '.'(*tmp.tmp1 => (tmp, tmp1) || tmp1 => ("", tmp1) *)
    Enum parts.[1]

and trans_mapping : string -> typ =
    fun str ->
    if not (str.Contains("mapping")) then failwith "Assertion failed"
    else
        let index = str.IndexOf(" => ")
        let part1 = str.Substring(0, index)
        let part2 = str.Substring(index + 4)
        let left' = part1.Substring(8)
        let right' = part2.Substring(0, part2.Length - 1)
        let key = trans_elementaryTypeName left' 
        let value = trans_str_to_typeName right' 
        Mapping (key, value)

and trans_array : string -> typ =
    fun str ->
    let str = str.Trim()
    let left, right =
        match str.LastIndexOf('[') with
        | -1 -> failwith "Invalid format"
        | idx -> str.Substring(0, idx), str.Substring(idx + 1)
    let size, _ =
        match right.IndexOf(']') with
        | -1 -> failwith "Invalid format"
        | idx -> right.Substring(0, idx), right.Substring(idx + 1)
    let t = trans_str_to_typeName left 
    let arr_size = try Some (int size) with _ -> None
    Array (t, arr_size)

and trans_lib_type : string -> typ = 
    fun str ->
    if not (str.Contains("contract")) && not (str.Contains("library")) then failwith "Assertion failed"
    let str = str.Replace("contract ", "")
    let name = str.Replace("library ", "")
    Contract name

and trans_function_returns : string -> typ = 
    fun str ->
    if not (str.Contains("function")) || not (str.Contains("returns (")) then failwith "Assertion failed"
    let parts = str.Split "returns ("
    let returns_typ = parts.[1].Substring(0, parts.[1].Length - 1)
    if returns_typ.Contains(",") then trans_tuple ("tuple(" + returns_typ + ")")
    else trans_str_to_typeName returns_typ 

and trans_tuple : string -> typ = 
    fun str ->
    if not (str.Contains("tuple")) then failwith "Assertion failed"
    let str' = if str.Length >= 7 then str.Substring(6, str.Length - 7) else ""
    if str' = "" then failwith "Assertion failed"
    let strs = str'.Split ','
    TupleType (List.map trans_str_to_typeName (List.ofArray strs))

and trans_str_to_typeName : string -> typ =
    fun str ->
    let str' = if str.Contains("type(") then (if str.Length >= 6 then str.Substring(5, str.Length - 6) else "") else str
    let str' = str'.Replace(" storage ", " ")
    let str' = str'.Replace(" ref", "")
    let str'' = str'.Replace(" memory","")
    let final = str''.Replace(" calldata", "")
    let final = final.Replace(" super ", "")
    match final with
    | _ when final.Replace(" pointer", "").EndsWith("]") -> trans_array final
    | _ when final.Contains("function") -> trans_function_returns final
    | _ when final.StartsWith("contract") || final.StartsWith("library") -> trans_lib_type final
    | _ when final.Contains("mapping") -> trans_mapping final
    | _ when final.Contains("tuple") -> trans_tuple final
    | _ when final.StartsWith("struct") -> trans_struct_type final
    | _ when final.Contains("enum") -> trans_enum_type final
    | _ when final.Contains("int_const") -> ConstInt
    | _ when final.Contains("rational_const") -> ConstReal
    | _ when final.Contains("literal_string") -> ConstString
    | "address payable" -> EType Address
    | _ when List.exists (fun (e:string) -> final.StartsWith(e)) type_list -> EType (trans_elementaryTypeName final)
    | _ -> Void

(*
and trans_str_to_typeName : string -> typ =
fun str ->
if BatString.exists str "[" then
let _ = assert
else if BatString.exists str "function" then transn_function_returns str
else if BatString.starts_with str "contract" || BatString.starts_with str "library" then trans_lib_type str
else if BatString.starts_with str "mapping" -> trans_mapping str
else if BatString.starts_with str "tuple"
else Void
*)
and trans_typeName_Descriptions : JsonValue -> (string * typ) =
    fun json ->
    let tmp = try Some (json?typeName |> trans_typeName) with _ -> None
    match tmp with
    | Some t -> t
    | None ->
    try
        let type_string = json?typeDescriptions?typeString.AsString()
        (get_first_part type_string, trans_str_to_typeName type_string)
    with _ -> ("", Void)

(* nodeType: O *)
and trans_elementaryTypeName : string -> elem_typ  =
    fun str ->
    match str with
    | s when s.Contains("string") -> String
    | "address" -> Address
    | "bool" -> Bool
    | s when s.StartsWith("uint") ->
        let n_str = s.Substring(4)
        if String.IsNullOrEmpty(n_str) then UInt 256
        else UInt (int n_str)
    | s when s.StartsWith("int") ->
        let n_str = s.Substring(3)
        if String.IsNullOrEmpty(n_str) then SInt 256
        else SInt (int n_str)
    | "byte" -> Bytes 1
    | s when s.StartsWith("bytes") ->
        let n_str = s.Substring(5)
        if String.IsNullOrEmpty(n_str) || n_str.Contains(" ") then DBytes
        else Bytes (int n_str)
    (* currently, (u)fixed point numbers are unstable in Solidity. *)
    | "fixed" -> raise (Failure "Unsupported: fixed") 
    | "ufixed" -> raise (Failure "Unsupported: ufixed")
    | s -> raise (Failure ("Unsupported: trans_elementraryTypeName-" + s))

(* nodeType: X *)
and trans_expression : JsonValue -> exp  =
    fun json ->
    let typ = trans_typeName_Descriptions json
    let node_typ = json?nodeType
    let loc = get_loc json
    let nid = get_id json
    match node_typ with
    | JsonValue.String "BinaryOperation" ->
        let left = json?leftExpression |> trans_expression
        let right = json?rightExpression |> trans_expression
        match json?operator.AsString() with
        | "+" -> BinOp (Add, left, right, {eloc=loc; etyp=(snd typ); eid=nid})        | "-" -> BinOp (Sub, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "*" ->
            match left,right with
            | Int n1, Real n2 -> Int (BigInteger (float n1 * n2))
            | Real n1, Int n2 -> Int (BigInteger (n1 * float n2))
            | Real n1, BinOp (Exponent, Int n2, Int n3, _) -> Int (BigInteger (n1 * (float (BigInteger.Pow(n2,int n3)))))
            | _ -> BinOp (Mul, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "/" -> BinOp (Div, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "%" -> BinOp (Mod, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "**" -> BinOp (Exponent, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | ">=" -> BinOp (GEq, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | ">" -> BinOp (Gt, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "<=" -> BinOp (LEq, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "<" -> BinOp (Lt, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "&&" -> BinOp (LAnd, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "||" -> BinOp (LOr, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "==" -> BinOp (Eq, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "!=" -> BinOp (NEq, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "<<" -> BinOp (ShiftL, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | ">>" -> BinOp (ShiftR, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "^" -> BinOp (BXor, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "&" -> BinOp (BAnd, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | "|" -> BinOp (BOr, left, right, {eloc=loc; etyp=(snd typ); eid=nid})
        | _ -> raise (Failure "Unsupported: trans_expression1")
    | JsonValue.String "Identifier" ->  
        try
            let vname = json?name.AsString()
            let typstr, typ = trans_typeName_Descriptions json 
            let vinfo = (* the information is not exact at the moment, but will be updated in the preprocessing. *){   
                typestr = typstr;
                vloc = loc;
                is_gvar = false;
                vtyp = typ;
                vvis = Private; 
                vid = (try json?id.AsInteger() with _ -> failwith "Assertion failed");
                refid = (try json?referencedDeclaration.AsInteger() with _ -> failwith "Assertion failed");
                vscope = -1;
                storage = "";
                flag = false; (* should be marked as false *)
                org = Some (Lv (Var (vname, mk_vinfo {Loc=None; TypeStr=Some typstr; Typ=Some typ; Org=None})))
            } 
            Lv (Var (vname,vinfo))
        with _ -> failwith "Assertion failed"
    | JsonValue.String "MemberAccess" -> 
        try
        let exp = json?expression |> trans_expression 
        let id = json?memberName.AsString()
        let typstr, typ = trans_typeName_Descriptions json
        let id_info = {
            dummy_vinfo with
                refid = (try json?referencedDeclaration.AsInteger() with _ -> -1);
                vtyp = typ;
                org = Some (Lv (Var (id, mk_vinfo {Loc=None; TypeStr=Some typstr; Typ=Some typ; Org=None})))
            }
        Lv (MemberAccess (exp,id,id_info, typ))
        with _ -> failwith "Assertion failed"
    | JsonValue.String "IndexAccess" ->
        let base_ = json?baseExpression |> trans_expression
        let idx = try json?indexExpression |> trans_expression with _ -> raise (Failure "indexExpression may be null: trans_expression")
        Lv (IndexAccess (base_,Some idx,snd typ))
    | JsonValue.String "Literal" ->
        match json?kind with
        | JsonValue.String "number" ->
            let st = json?subdenomination.AsString()
            let factor =
                match json?subdenomination with
                | JsonValue.Null -> 1.
                | _ when st = "wei" -> 1. 
                | _ when st = "szabo" -> 1e12
                | _ when st = "finney" -> 1e15
                | _ when st = "ether" -> 1e18
                | _ when st = "seconds" -> 1.
                | _ when st = "minutes" -> 60.
                | _ when st = "hours" -> 3600.
                | _ when st = "days" -> 86400. (* 24*3600 *)
                | _ when st = "weeks" -> 604800. (* 7*24*3600 *)
                | _ when st = "years" -> 31536000. (* 365 * 86400 *)
                | _ when st = "gwei" -> 1e9
                | _ -> failwith "Assertion failed"
            let str = json?value.AsString() 
            match (snd typ) with
            (* float_of_string "0xffffffffffffffffffffffff0000000000000000000000000000000000000000" loses precision *)
            (* Thus, directly convert into BatBig_int *)
            | ConstInt ->
                match json?subdenomination with
                | JsonValue.Null when not (str.Contains("e")) ->
                    if str.StartsWith("0x") then
                        let value = BigInteger.Parse(str.[2..], System.Globalization.NumberStyles.HexNumber)
                        Cast (EType Address, Int (value))
                    else if str.Contains(".") then
                        let value = float str
                        Int (BigInteger (value * factor))
                    else
                        Int (BigInteger.Parse(str))
                | _ ->
                    if str.StartsWith("0x") then
                        let value = BigInteger.Parse(str.[2..], System.Globalization.NumberStyles.HexNumber)
                        Cast (EType Address, Int (value * (BigInteger factor)))
                    else
                        let value = float str
                        Int (BigInteger (value * factor)) (* e.g., 0.00001 ether *)
            | EType Address ->
                let value = 
                    if str.StartsWith("0x") then
                        BigInteger.Parse(str.[2..], System.Globalization.NumberStyles.HexNumber)
                    else 
                        try BigInteger.Parse(str) with _ -> BigInteger (float str)
                Cast (EType Address, Int (value * (BigInteger factor)))
            | ConstReal ->
                let value = float str
                Real (value * factor)
            | _ -> failwith "Assertion failed"
        | JsonValue.String "bool" ->
            let b = json?value.AsString()
            match b with
            | "true" -> True
            | "false" -> False
            | _ -> failwith "Assertion failed"
        | JsonValue.String "string" ->
            let s = try json?value.AsString() with _ -> json?hexValue.AsString()
            Str s
        | JsonValue.String "hexString" ->
            let s = json?hexValue.AsString() 
            Str s
        | JsonValue.String s -> raise (Failure ("Unsupported: trans_expression2 - " + s + " : line " + string loc.line))
        | _ -> failwith "Assertion failed"
    | JsonValue.String "FunctionCall" ->
        match json?kind with
        | JsonValue.String "functionCall" when json?expression?nodeType = JsonValue.String "FunctionCallOptions" ->
            let json' = json?expression
            if not (json'?nodeType.AsString() = "FunctionCallOptions") then failwith "Assertion failed"
            let args = json?arguments |> trans_functionCallArguments (* should be be json, not json' *)
            let exp = json'?expression |> trans_expression (* for the rest, should be json', not json *)
            let opnames =
                match json'?names with
                | JsonValue.Array items -> List.map (fun e -> JsonExtensions.AsString e) (Array.toList items) 
                | _ -> []
            let ops =
                match json'?options with
                | JsonValue.Array items -> List.map trans_expression (Array.toList items)
                | _ -> []
            if not (List.length opnames = List.length ops) then failwith "Assertion failed"
            if not (List.length opnames <= 2 && List.length ops <= 2) then failwith "Assertion failed"
            let ethop = match List.tryFindIndex (fun e -> e = "value") opnames with Some n -> Some (List.item n ops) | None -> None
            let gasop = match List.tryFindIndex (fun e -> e = "gas") opnames with Some n -> Some (List.item n ops) | None -> None
            CallTemp (exp, args, ethop, gasop, {eloc=loc; etyp=(snd typ); eid=nid})
        | JsonValue.String "functionCall" ->
            let exp = json?expression |> trans_expression 
            let args = json?arguments |> trans_functionCallArguments 
            CallTemp (exp,args,None,None,{eloc=loc; etyp=(snd typ); eid=nid})
        | JsonValue.String "typeConversion" ->
            let arg = 
                match json.TryGetProperty "arguments" with
                | Some (JsonValue.Array items) -> items |> Array.toList
                | _ -> []
            if not (List.length arg = 1) then failwith "Assertion failed"
            let exp = trans_expression (List.head arg)
            Cast (snd typ, exp)
        | JsonValue.String "structConstructorCall" ->
            let exp = json?expression |> trans_expression 
            let args = json?arguments |> trans_functionCallArguments
            let names = 
                match json?names with
                | JsonValue.Array items -> Array.toList items
                | _ -> []
            if List.length names = 0 then (* member names are not given *) 
                CallTemp (Lv (Var ("struct_init",dummy_vinfo)), exp::args, None, None, {eloc=loc; etyp=(snd typ); eid=nid})
            else
                let args_names = List.map (fun name -> Lv (Var (JsonExtensions.AsString name, dummy_vinfo))) names 
                CallTemp (Lv (Var ("struct_init2",dummy_vinfo)), exp::args_names@args, None, None, {eloc=loc; etyp=(snd typ); eid=nid})
        | JsonValue.String s -> raise (Failure ("Unsupported: trans_expression3-"+s))
        | _ -> failwith "Assertion failed"
    | JsonValue.String "UnaryOperation" ->
        let sub = json?subExpression |> trans_expression
        match json?operator with
        | JsonValue.String "+" -> UnOp (Pos,sub,snd typ)
        | JsonValue.String "-" -> UnOp (Neg,sub,snd typ) 
        | JsonValue.String "!" -> UnOp (LNot,sub,snd typ)
        | JsonValue.String "~" -> UnOp (BNot,sub,snd typ)
        | JsonValue.String "++" ->
            let pre = json?prefix.AsBoolean()
            IncTemp (sub,pre,loc)
        | JsonValue.String "--" ->
            let pre = json?prefix.AsBoolean()
            DecTemp (sub,pre,loc)
        | _ -> raise (Failure "Unsupported: trans_expression4")
    | JsonValue.String "TupleExpression" ->
        let tuples = 
            match json?components with
            | JsonValue.Array items -> Array.toList items
            | _ -> []
        if is_array (snd typ) then Lv (Tuple ((List.map (fun e -> try Some (trans_expression e) with _ -> None) tuples), (snd typ))) else
        if List.length tuples = 1 then trans_expression (List.head tuples)
        else Lv (Tuple ((List.map (fun e -> try Some (trans_expression e) with _ -> None) tuples), (snd typ)))
    | JsonValue.String "Conditional" -> (* cond ? t : f *)
        let cond = json?condition |> trans_expression
        let t = json?trueExpression |> trans_expression
        let f = json?falseExpression |> trans_expression
        CondTemp (cond,t,f,(snd typ),loc)
    | JsonValue.String "NewExpression" ->
        if is_array (snd typ) then Lv (Var ("array_init",dummy_vinfo)) else
        if is_contract (snd typ) then Lv (Var ("contract_init_"+get_name_userdef (snd typ),dummy_vinfo)) else
        if is_struct (snd typ) then Lv (Var ("struct_init_"+get_name_userdef (snd typ), dummy_vinfo)) else
        if is_enum (snd typ) then Lv (Var ("enum_init_"+get_name_userdef (snd typ), dummy_vinfo)) else
        if is_dbytes (snd typ) then Lv (Var ("dbytes_init",dummy_vinfo)) else
        if is_string (snd typ) then Lv (Var ("string_init",dummy_vinfo))
        else raise (Failure "NewExpression")
    | JsonValue.String "Assignment" ->
        let lv = json?leftHandSide|> trans_expression |> exp_to_lv
        let exp = json?rightHandSide |> trans_expression 
        let typ = json?leftHandSide |> trans_typeName_Descriptions
        let op = json?operator
        match op with
        | JsonValue.String "=" -> AssignTemp (lv, exp, loc)
        | JsonValue.String "+=" -> AssignTemp (lv, BinOp (Add,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "-=" -> AssignTemp (lv, BinOp (Sub,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "*=" -> AssignTemp (lv, BinOp (Mul,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "/=" -> AssignTemp (lv, BinOp (Div,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "%=" -> AssignTemp (lv, BinOp (Mod,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "|=" -> AssignTemp (lv, BinOp (BOr,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "^=" -> AssignTemp (lv, BinOp (BXor,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "&=" -> AssignTemp (lv, BinOp (BAnd,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "<<=" -> AssignTemp (lv, BinOp (ShiftL,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String ">>=" -> AssignTemp (lv, BinOp (ShiftR,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | _ -> raise (Failure " Unsupported: trans_expression5")
    | JsonValue.String "ElementaryTypeNameExpression" ->
        (* json AST from solc is slightly differnt per version. *)
        try
            let etyp = json?typeName.AsString() |> trans_elementaryTypeName
            ETypeName etyp
        with _ ->
            let etyp = json?typeName?name.AsString() |> trans_elementaryTypeName 
            ETypeName etyp
    | JsonValue.String s -> failwith ("trans_expression6-" + s + "@" + string loc.line)
    | _ -> failwith "Unsupported: trans_expression7"

(* nodeType: X *)  
and trans_functionCallArguments : JsonValue -> exp list =
    fun json ->
    match json with 
    | JsonValue.Array l ->
        List.fold (fun acc j -> acc @ [(trans_expression j)]) [] (Array.toList l)
    | JsonValue.Null -> [] (* no arguments: `Null, not `List [] *)
    | _ -> failwith "Assertion failed"

(* nodeType : O *)
and trans_expressionStatement : JsonValue -> stmt =
    fun json ->
    if not (json?nodeType = JsonValue.String "ExpressionStatement") then failwith "Assertion failed" 
    let json' = json?expression
    let loc = get_loc json' 
    let nid = get_id json' 
    match json'?nodeType with
    | JsonValue.String "FunctionCall" ->
        match json'?kind with
        | JsonValue.String "functionCall" when json'?expression?nodeType.AsString() = "FunctionCallOptions" ->
            let json'' = json'?expression
            if not (json''?nodeType.AsString() = "FunctionCallOptions") then failwith "Assertion failed"
            let args = json'?arguments |> trans_functionCallArguments (* should be be json', not json'' *)
            let exp = json''?expression |> trans_expression (* for the rest, should be json'', not json' *)
            let opnames =
                match json''?names with
                | JsonValue.Array items -> List.map (fun e -> JsonExtensions.AsString e) (Array.toList items) 
                | _ -> []
            let ops =
                match json''?options with
                | JsonValue.Array items -> List.map trans_expression (Array.toList items)
                | _ -> []
            if not (List.length opnames = List.length ops) then failwith "Assertion failed"
            if not (List.length opnames <= 2 && List.length ops <= 2) then failwith "Assertion failed"
            let ethop = match List.tryFindIndex (fun e -> e = "value") opnames with Some n -> Some (List.item n ops) | None -> None
            let gasop = match List.tryFindIndex (fun e -> e = "gas") opnames with Some n -> Some (List.item n ops) | None -> None
            Call (None, exp, args, ethop, gasop, get_loc json', json'?id.AsInteger())
        | JsonValue.String "functionCall" ->
            let exp = json'?expression |> trans_expression (* function name *)
            let args = json'?arguments |> trans_functionCallArguments
            (* Call (None, exp, args) *)
            (* Built-in function checkers. Lists need to be updated. *)
            if is_require exp then
                (assert (List.length args = 1 || List.length args = 2);
                If (List.head args, Skip, Throw, {if_loc=loc;if_tloc=loc; if_floc=Some loc}))
            else if is_assert exp then
                (assert (List.length args = 1);
                Seq (Assert (List.head args, "default", get_loc json'),
                    If (List.head args, Skip, Throw, dummy_ifinfo)))
            else Call (None, exp, args, None, None, get_loc json', json'?id.AsInteger()) (* normal case *) 
        | _ -> raise (Failure "Unsupported: trans_expressionStatement1")
    | JsonValue.String "Assignment" ->
        let lv = json'?leftHandSide |> trans_expression |> exp_to_lv 
        let exp = json'?rightHandSide |> trans_expression 
        let typ = json'?leftHandSide |> trans_typeName_Descriptions 
        let op = json'?operator
        match op with
        | JsonValue.String "=" -> Assign (lv, exp, loc)
        | JsonValue.String "+=" -> Assign (lv, BinOp (Add,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "-=" -> Assign (lv, BinOp (Sub,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "*=" -> Assign (lv, BinOp (Mul,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "/=" -> Assign (lv, BinOp (Div,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "%=" -> Assign (lv, BinOp (Mod,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "|=" -> Assign (lv, BinOp (BOr,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "^=" -> Assign (lv, BinOp (BXor,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "&=" -> Assign (lv, BinOp (BAnd,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String "<<=" -> Assign (lv, BinOp (ShiftL,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | JsonValue.String ">>=" -> Assign (lv, BinOp (ShiftR,Lv lv,exp, {eloc=loc; etyp=(snd typ); eid=nid}), loc)
        | _ -> raise (Failure " Unsupported: trans_expressionStatement2")
    | JsonValue.String "UnaryOperation" ->
        let op = json'?operator
        match op with 
        | JsonValue.String "++" ->
            let sub = json'?subExpression |> trans_expression 
            let lv = exp_to_lv sub
            Assign (lv, BinOp (Add,Lv lv,Int (BigInteger 1),{eloc=loc; etyp=get_type_lv lv; eid=nid}), loc)
        | JsonValue.String "--" ->
            let sub = json'?subExpression |> trans_expression 
            let lv = exp_to_lv sub
            Assign (lv, BinOp (Sub,Lv lv,Int (BigInteger 1),{eloc=loc; etyp=get_type_lv lv; eid=nid}), loc)
        | JsonValue.String "delete" ->
            let sub = json'?subExpression |> trans_expression 
            let lv = Var ("delete",dummy_vinfo)
            Call (None, Lv lv, [sub], None, None, loc, nid)
        | JsonValue.String s -> raise (Failure ("Unsupported Unary Op: " + s))
        | _ -> failwith "Assertion failed"
    | JsonValue.String "Identifier" -> Skip
    | JsonValue.String "BinaryOperation" -> Skip
    | JsonValue.String "IndexAccess" -> Skip
    | JsonValue.String "Conditional" -> (* cond ? t : f *)
        let cond = json'?condition |> trans_expression 
        (* since json generated by solc does not have proper structure,
        * this additional manipulation step should be forced. *)
        let t = JsonValue.Record [|("expression", json'?trueExpression); ("nodeType", JsonValue.String "ExpressionStatement")|] |> trans_expressionStatement
        let f = JsonValue.Record [|("expression", json'?falseExpression); ("nodeType", JsonValue.String "ExpressionStatement")|] |> trans_expressionStatement
        If (cond, t, f, dummy_ifinfo)
    | JsonValue.String "TupleExpression" -> Skip
    | JsonValue.String "FunctionCallOptions" -> Skip (* e.g., "msg.sender.call{value: msg.value-amountEth};" does nothing. E.g., '("")' should be appended. *)
    | JsonValue.String s -> raise (Failure ("Unsupported: trans_expressionStatement3 - " + s + " : line " + string loc.line))
    | _ -> failwith "Assertion failed"

(* nodeType: X *)
let trans_visibility : JsonValue -> visibility =
    fun json ->
    match json with
    | JsonValue.String "public" -> Public 
    | JsonValue.String "internal" -> Internal
    | JsonValue.String "external" -> External
    | JsonValue.String "private" -> Private
    | _ -> raise (Failure "trans_visibility")

(* nodeType : O *)
let trans_variable_declaration : JsonValue -> var_decl =
    fun json ->
    if not (json?nodeType.AsString() = "VariableDeclaration") then failwith "Assertion failed"
    let vname = json?name.AsString()
    let typstr, typ = trans_typeName_Descriptions json
    let vinfo =
        { 
            typestr = typstr;
            vloc = json |> get_loc;
            is_gvar = json?stateVariable.AsBoolean()
            vtyp = typ;
            vvis = json?visibility |> trans_visibility;
            vid = (try json?id.AsInteger() with _ -> failwith "Assertion failed");
            refid = (try json?id.AsInteger() with _ -> failwith "Assertion failed"); (* for the declarations, assign themselves. *)
            vscope = (try json?scope.AsInteger() with _ -> failwith "Assertion failed");
            storage = (try json?storageLocation.AsString() with _ -> failwith "Assertion failed");
            flag = true; (* true only for variable declarations *)
            org = Some (Lv (Var (vname, mk_vinfo {Loc=None; TypeStr=Some typstr; Typ=Some typ; Org=None})))
        }
    (vname,vinfo)

let rec trans_yul_exp : (string * int) list -> int -> JsonValue -> (id * int) list =
    fun ref ast_id json ->
    let node_typ = json?nodeType
    match node_typ with
    | JsonValue.String "YulIdentifier" ->
        let name = json?name.AsString()
        (* Locals in assembly block do not have references in external blocks. Thus, assign assembly block's AST id. *)
        let refid = 
            match List.tryFind (fun (k, v) -> k = json?src.AsString()) ref with
            | Some (_, v) -> v
            | None -> ast_id
        [(name, refid)]
    | JsonValue.String "YulLiteral" -> []
    | JsonValue.String "YulFunctionCall" ->
        (* let fname = json |> Json.value_of "functionName" |> Json.value_of "name" |> Json.to_string in *)
        let args = 
            match json?arguments with
            | JsonValue.Array items -> Array.toList items
            | _ -> []
        let args = List.fold (fun acc arg -> acc @ (trans_yul_exp ref ast_id arg)) [] args
        args
    | _ -> failwith "trans_yul_exp"

let rec trans_yul_stmt : JsonValue -> (string * int) list -> int -> (id * int) list =
    fun json ref ast_id ->
    let node_typ = json?nodeType
    match node_typ with
    | JsonValue.String "YulVariableDeclaration" ->
        let lhs = 
            match json?variables with
            | JsonValue.Array items -> Array.toList items
            | _ -> []
        let lhs =
            List.map (fun j ->
                let name = j?name.AsString()
                (* let _ = print_endline name in
                let _ = print_endline (j |> Json.value_of "src" |> Json.to_string) in
                let _ = print_endline (Vocab.string_of_list (fun (src,refid) -> src ^ " : " ^ string_of_int refid) ref) in *)
                (* Locals in assembly block do not have references in external blocks. Thus, assign assembly block's AST id. *)
                let refid = 
                    match List.tryFind (fun (k, v) -> k = json?src.AsString()) ref with
                    | Some (_, v) -> v
                    | None -> ast_id
                (name,refid)
            ) lhs
        let rhs = json?value |> trans_yul_exp ref ast_id 
        rhs@lhs
    | JsonValue.String "YulAssignment" ->
        let lhs = 
            match json?variableNames with
            | JsonValue.Array items -> Array.toList items
            | _ -> []
        let lhs =
            List.map (fun j ->
                let name = j?name.AsString()
                let refid = 
                    match List.tryFind (fun (k, v) -> k = json?src.AsString()) ref with
                    | Some (_, v) -> v
                    | None -> ast_id
                (name,refid)
            ) lhs 
        let rhs = json?value |> trans_yul_exp ref ast_id in
        rhs@lhs
    | JsonValue.String "YulExpressionStatement" ->
        json?expression |> trans_yul_exp ref ast_id
    | JsonValue.String "YulForLoop" ->
        let condition = json?condition |> trans_yul_exp ref ast_id 
        let pre = 
            match json?pre?statements with
            | JsonValue.Array items -> Array.toList items
            | _ -> []
        let pre = List.fold (fun acc j -> acc @ (trans_yul_stmt j ref ast_id)) [] pre 
        let post = 
            match json?post?statements with
            | JsonValue.Array items -> Array.toList items
            | _ -> []
        let post = List.fold (fun acc j -> acc @ (trans_yul_stmt j ref ast_id)) [] post 
        let body = 
            match json?body?statements with
            | JsonValue.Array items -> Array.toList items
            | _ -> []
        let body = List.fold (fun acc j -> acc @ (trans_yul_stmt j ref ast_id)) [] body 
        condition @ pre @ post @ body
        (* let _ = print_endline (Vocab.string_of_list fst s) in
        let _ = assert false in *)
    | JsonValue.String "YulIf" ->
        let condition = json?condition |> trans_yul_exp ref ast_id 
        let body = 
            match json?body?statements with
            | JsonValue.Array items -> Array.toList items
            | _ -> []
        let body = List.fold (fun acc j -> acc @ (trans_yul_stmt j ref ast_id)) [] body 
        condition @ body
    | JsonValue.String s -> failwith ("trans_yul_stmt : " + s + " @ line " + string (get_loc json).line)
    | _ -> failwith "Assertion failed"

let trans_yul_block : JsonValue -> (id * int) list =
    fun json ->
    if not (json?nodeType.AsString() = "InlineAssembly") then failwith "Assertion failed"
    let ext_refs = 
        match json?externalReferences with
        | JsonValue.Array items -> Array.toList items
        | _ -> []
    let ext_refs =
        List.map (fun er ->
        (er?src.AsString(),  er?declaration.AsInteger())
        ) ext_refs
    let ast_id = json?id.AsInteger()
    let j = json?AST
    if not (j?nodeType.AsString() = "YulBlock") then failwith "Assertion failed"
    let statements = 
        match j?statements with
        | JsonValue.Array items -> Array.toList items
        | _ -> []
    List.fold (fun acc j' ->
        acc @ (trans_yul_stmt j' ext_refs ast_id)
    ) [] statements


let param_cnt = ref 0
let param_name = "Param"
let gen_param_name () =
    param_cnt.Value <- param_cnt.Value + 1;
    param_name + (string param_cnt.Value)

(* nodeType: O *)
let trans_parameterList : JsonValue -> param list =
    fun json ->
    if not (json?nodeType.AsString() = "ParameterList") then failwith "Assertion failed"
    let parameters = (* 0 parameters => `List [] *)
        match json?parameters with
        | JsonValue.Array items -> Array.toList items
        | _ -> []
    let reversed_params =
        List.fold (fun acc j ->
        let (vname,vinfo) = trans_variable_declaration j
        let vname = if vname = "" then gen_param_name () else vname in
        (vname, vinfo)::acc
        ) [] parameters
    let parms = List.rev reversed_params
    parms

(* nodeType : X *)
let rec trans_statement : JsonValue -> stmt =
    fun json ->
    let node_typ = json?nodeType
    let loc = get_loc json
    match node_typ with
    | JsonValue.String "VariableDeclarationStatement" -> (* declaration := initialValue *)
        let decl = 
            match json?declarations with
            | JsonValue.Array items -> Array.toList items
            | _ -> []
        if not (List.length decl > 0) then failwith "Assertion failed"
        let lv = 
            if List.length decl = 1 then   (* uint a; *)
                let var_decl = List.head decl 
                let (vname,vinfo) = trans_variable_declaration var_decl 
                Var (vname,vinfo) 
            else  (* (a, b, c); *)
                let elst = 
                    List.map (fun v -> 
                    try
                        let (vname,vinfo) = trans_variable_declaration v 
                        Some (Lv (Var (vname, vinfo)))
                    with _ -> 
                        None
                    ) decl
                Tuple (elst, Void)
        match json?initialValue with
        | JsonValue.Null -> Decl lv
        | exp -> Assign (lv, trans_expression exp, loc)
    | JsonValue.String "ExpressionStatement" -> trans_expressionStatement json
    | JsonValue.String "PlaceholderStatement" -> PlaceHolder
    | JsonValue.String "ForStatement" ->
        let init = try json?initializationExpression |> trans_statement with _ -> Skip  (* for ( ;cond;a++) *)
        let cond = try json?condition |> trans_expression with _ -> True  (* for (init; ;a++) *)
        let body_wo_last = json?body |> trans_statement 
        let body_last = try json?loopExpression |> trans_statement with _ -> Skip  (* for (init;cond; ) *)
        let body = Seq (body_wo_last,body_last) 
        Seq (init,While (cond,body))
    | JsonValue.String "WhileStatement" ->
        let cond = json?condition |> trans_expression 
        let body = json?body |> trans_statement 
        While (cond,body)
    | JsonValue.String "DoWhileStatement" ->
        let cond = json?condition |> trans_expression 
        let body = json?body |> trans_statement 
        Seq (body, While (cond,body))
    | JsonValue.String "IfStatement" ->
        let cond = json?condition |> trans_expression 
        let tbody, tloc = json?trueBody |> trans_statement, json?trueBody |> get_loc 
        let fbody, floc =
            match json?falseBody with
            | JsonValue.Null -> (Skip, None)
            | fb -> (trans_statement fb, Some (get_loc fb)) 
        let ifinfo = {if_loc = loc; if_tloc = tloc; if_floc = floc} 
        If (cond, tbody, fbody, ifinfo)

    | JsonValue.String "Return" ->
        match json?expression with
        | JsonValue.Null -> Return (None, loc)
        | exp -> Return (Some (trans_expression exp), loc)
    | JsonValue.String "Throw" -> Throw
    | JsonValue.String "Block" -> trans_block json
    | JsonValue.String "EmitStatement" -> Skip
    | JsonValue.String "Break" -> Break
    | JsonValue.String "Continue" -> Continue
    | JsonValue.String "InlineAssembly" ->
        try
            let ext_refs = 
                match json?externalReferences with
                | JsonValue.Array items -> Array.toList items
                | _ -> []
            let var_refid_pairs =
                List.map (fun j ->
                    match j with
                    | JsonValue.Record [|(s,j')|] -> (s, j'?declaration.AsInteger())
                    | _ -> raise (Failure "InlineAssembly")
                ) ext_refs 
            Assembly (var_refid_pairs, loc)
        with _ ->
        let var_refid_pairs = trans_yul_block json
        Assembly (var_refid_pairs, loc)
    | JsonValue.String "UncheckedBlock" ->
        let slst = 
            match json?declarations with
            | JsonValue.Array items -> List.map trans_statement (Array.toList items)
            | _ -> []
        Unchecked (slst,loc)
    | JsonValue.String "TryStatement" ->
        let json' = json?externalCall
        if not (json'?nodeType.AsString() = "FunctionCall") then failwith "Assertion failed"
        let extern_call = trans_expression json' 
        if not (match extern_call with CallTemp _ -> true | _ -> false) then failwith "Assertion failed"
        let clauses = 
            match json?clauses with
            | JsonValue.Array items -> Array.toList items
            | _ -> []
        let rec f i lst =
            match lst with
            | [] -> Throw
            | j::tl when i=0 -> (* try *)
                if not (j?nodeType.AsString() = "TryCatchClause") then failwith "Assertion failed"
                let parms = j?parameters |> trans_parameterList 
                let lv = params_to_lv parms 
                let assign = Assign (lv, extern_call, loc) 
                let stmt = trans_block (j?block) 
                If (Lv (gen_tmpvar {Org=None;Loc=None;Typ=EType Bool;TypeStr="bool"}), Seq (assign, stmt), f (i+1) tl, dummy_ifinfo)
            | j::tl -> (* catch *)
                let stmt = trans_block (j?block) 
                If (Lv (gen_tmpvar {Org=None;Loc=None;Typ=EType Bool;TypeStr="bool"}), stmt, f (i+1) tl, dummy_ifinfo)
        f 0 clauses

    | JsonValue.String s -> raise (Failure ("Unsupported: trans_statement - " + s + " : line " + string loc.line))
    | _ -> failwith "Assertion failed"

(* nodeType : O *)
and trans_block : JsonValue -> stmt =
    fun json ->
    if not (json?nodeType.AsString() = "Block") then failwith "Assertion failed"
    let statements = 
        match json?statements with
        | JsonValue.Array items -> Array.toList items
        | _ -> []
    List.fold (fun acc j ->
        let new_stmt = trans_statement j 
        Seq (acc, new_stmt)
    ) Skip statements 

(* usual: defined modifiers appear as invocations *)
(* unusual: consturctor invocations appear as modifiers *)
let is_usual_modifier: string list -> JsonValue -> bool =
    fun cnames json ->
    if not (json?nodeType.AsString() = "ModifierInvocation") then failwith "Assertion failed"
    let modname = json?modifierName?name.AsString()
    not (List.contains modname cnames)

(* nodeType: O *)
let trans_modifierInvocation : JsonValue -> mod_call =
    fun json ->
    if not (json?nodeType.AsString() = "ModifierInvocation") then failwith "Assertion failed"
    let name = json?modifierName?name.AsString()
    let args = json?arguments |> trans_functionCallArguments 
    let loc = get_loc json 
    (name, args, loc)

(* generate Constructor call *)
let trans_inheritanceSpecifier : JsonValue -> mod_call =
    fun json ->
    if not (json?nodeType.AsString() = "InheritanceSpecifier") then failwith "Assertion failed"
    let name = json?baseName?name.AsString() 
    let args = json?arguments |> trans_functionCallArguments 
    let loc = get_loc json 
    (name, args, loc)

let resolve_cnstr_calls : mod_call list -> mod_call list ->
                            mod_call list =
                                fun inherit_calls mod_calls ->
    (* In solc 0.4x, mod_calls has the priority over the inherit_calls. *)
    (* In recent solc, specifying arguments for both places is an error. *)
    (* E.g.,
    * Inherit: A(5) B(3), Mod: A(8) C(7) => B(3) A(8) C(7) *)
    let combined = inherit_calls @ mod_calls
    let combined = List.rev combined (* rev list to give the priority to mod_calls *)
    List.fold (fun acc m ->
        let b = List.exists (fun (x,_,_) -> x = triple_fst m) acc in
        if b then acc
        else m::acc
    ) [] combined

let trans_isConstructor : JsonValue -> bool =
    fun j ->
    if not (j?nodeType.AsString() = "FunctionDefinition") then failwith "Assertion failed"
    try
        j?isConstructor.AsBoolean() (* solc 0.4x *)
    with _ -> (* solc 0.5x *)
        match j?kind with
        | JsonValue.String "constructor" -> true
        | JsonValue.String "function" -> false
        | JsonValue.String "fallback" -> false
        | JsonValue.String "receive" -> false
        | JsonValue.String s -> failwith ("trans_isConstructor: " + s)
        | _ -> failwith "Assertion failed"

let trans_fname : JsonValue -> bool -> string -> string =
    fun j is_constructor cid ->
    if not (j?nodeType.AsString() = "FunctionDefinition") then failwith "Assertion failed"
    try
        match j?kind with (* solc 0.5x *)
        | JsonValue.String "constructor" -> cid
        | JsonValue.String "function" -> j?name.AsString()
        | JsonValue.String "fallback" -> "fallback"
        | JsonValue.String "receive" -> "@receive" (* solc 0.6x *)
        | JsonValue.String s -> failwith ("trans_fname : " + s)
        | _ -> failwith "Assertion failed"
    with _ -> (* solc 0.4x *)
        let fname = j?name.AsString()
        let fname = if is_constructor then cid else if fname = "" then "fallback" else fname 
        fname

let trans_payable : JsonValue -> bool =
    fun j ->
    if not (j?nodeType.AsString() = "FunctionDefinition") then failwith "Assertion failed"
    try
        j?payable.AsBoolean() (* 0.4x *)
    with _ -> (* 0.5x *)
        match j?stateMutability with
        | JsonValue.String "payable" -> true
        | JsonValue.String "nonpayable" -> false
        | JsonValue.String "view" -> false
        | JsonValue.String "pure" -> false
        | _ -> failwith "stateMutability"

let trans_mutability : JsonValue -> state_mutability =
    fun j ->
    if not (j?nodeType.AsString() = "FunctionDefinition") then failwith "Assertion failed"
    match j?stateMutability with
    | JsonValue.String "payable" -> Payable
    | JsonValue.String "nonpayable" -> NonPayable
    | JsonValue.String "view" -> View
    | JsonValue.String "pure" -> Pure
    | _ -> failwith "stateMutability"

(* nodeType : O *)
let trans_contractDefinition : string list -> JsonValue -> contract =
    fun cnames json ->
    let cid = json?name.AsString()
    let contract_parts = 
        match json?nodes with
        | JsonValue.Array items -> Array.toList items
        | _ -> []
    let cinfo =
        { numid = json?id.AsInteger();
        inherit_order = List.map JsonExtensions.AsInteger (match json?linearizedBaseContracts with JsonValue.Array items -> Array.toList items | _ -> []);
        lib_typ_lst = [];
        ckind = json?contractKind.AsString()
        } 
    let base_contracts =  (* A is B,C,D => base_contracts : [B; C; D] *)
        match json?baseContracts with
        | JsonValue.Array items -> Array.toList items
        | _ -> []
    let cnstr_calls_inherit =
        List.fold (fun acc bas ->
        let cnstr_call = trans_inheritanceSpecifier bas
        if List.length (triple_snd cnstr_call) > 0 then
            acc @ [cnstr_call] (* constructors are called starting from parents *)
        else acc
        ) [] base_contracts 
    let (cid, gvar_decls, structs, enums, func_defs, cinfo) =
        List.fold (fun (cid, gvar_decls, structs, enums, func_defs, cinfo) j ->
        let node_typ = j?nodeType
        match node_typ with
        | JsonValue.String "VariableDeclaration" ->
            let (vname,vinfo) = trans_variable_declaration j 
            let expop =
                match j?value with
                | JsonValue.Null -> None
                | exp -> Some (trans_expression exp)
            let decl = (vname, expop, vinfo) 
            (cid, decl::gvar_decls, structs, enums, func_defs, cinfo)
        | JsonValue.String "EventDefinition" -> (* Event is modeled as a function with internal visibility and a skip body *)
            let fname = j?name.AsString()
            let parms = j?parameters |> trans_parameterList 
            let finfo = { 
                is_constructor = false;
                is_payable = false;
                is_modifier = false;
                mod_list = [];
                mod_list2 = [];
                param_loc = dummy_loc;
                ret_param_loc = dummy_loc;
                fvis = Internal;
                mutability = Pure; (* event can be considered as pure *)
                fid = j?id.AsInteger()
                floc = get_loc j;
                scope = cinfo.numid;
                scope_s = cid; (* to be filled by preprocessor *)
                org_scope_s = cid;
                cfg = empty_cfg
            } 
            let stmt = Skip
            let func = (fname,parms,[],stmt,finfo) 
            (cid, gvar_decls, structs, enums, func::func_defs, cinfo)
        | JsonValue.String "EnumDefinition" ->
            let name = j?name.AsString()
            let members = List.map (fun j' -> j'?name.AsString()) (match j?members with JsonValue.Array items -> Array.toList items | _ -> []) 
            let enum = (name,members) 
            (cid, gvar_decls, structs, enums@[enum], func_defs, cinfo)
        | JsonValue.String "StructDefinition" ->
            let name = j?canonicalName.AsString()
            let decls = List.map trans_variable_declaration (match j?members with JsonValue.Array items -> Array.toList items | _ -> []) 
            let structure = (name,decls) 
            (cid, gvar_decls, structure::structs, enums, func_defs, cinfo)
        | JsonValue.String "UsingForDirective" -> 
            let lib_name = j?libraryName?name.AsString()
            let typ = trans_typeName_Descriptions j 
            let cinfo = {cinfo with lib_typ_lst = (lib_name,(snd typ))::cinfo.lib_typ_lst} 
            (cid, gvar_decls, structs, enums, func_defs, cinfo)
        | JsonValue.String "FunctionDefinition" ->
            let is_constructor = trans_isConstructor j 
            let fname = trans_fname j is_constructor cid 
            let parms = j?parameters |> trans_parameterList 
            let ret_params = j?returnParameters |> trans_parameterList 
            let stmt =
                if j?implemented.AsBoolean() then j?body |> trans_block
                else Skip (* function without definitions *)
            let modifiers = match j?modifiers with JsonValue.Array items -> Array.toList items | _ -> [] (* OnlyOwner 같은 Modifier 를 뜻함 *)
            (* executed in the order of usual mod call => constructor mod call *)
            let mod_calls =
                List.fold (fun acc j' ->
                    if is_usual_modifier cnames j' then acc @ [(trans_modifierInvocation j')]
                    else acc
                ) [] modifiers
            let cnstr_calls_mod =
                List.fold (fun acc j' ->
                    if not (is_usual_modifier cnames j') then acc @ [(trans_modifierInvocation j')]
                    else acc
                ) [] modifiers
            let cnstr_calls = resolve_cnstr_calls cnstr_calls_inherit cnstr_calls_mod 
            let finfo = { 
                is_constructor = is_constructor;
                is_payable = trans_payable j;
                is_modifier = false;
                mod_list = mod_calls;
                mod_list2 = if is_constructor then cnstr_calls else [];
                param_loc = j?parameters |> get_loc;
                ret_param_loc = j?returnParameters |> get_loc;
                fvis = j?visibility |> trans_visibility;
                mutability = trans_mutability j;
                fid = j?id.AsInteger()
                floc = get_loc j;
                scope = cinfo.numid;
                scope_s = cid;
                org_scope_s = cid;
                cfg = empty_cfg 
            }            
            let func = (fname, parms, ret_params, stmt, finfo)
            (cid, gvar_decls, structs, enums, func::func_defs, cinfo)
        | JsonValue.String "ModifierDefinition" ->
            let fname = j?name.AsString()
            let parms = j?parameters |> trans_parameterList
            let finfo = { 
                is_constructor = false;
                is_payable = false;
                is_modifier = true;
                mod_list = []; (* no modifier invocations in modifier definition *)
                mod_list2 = []; (* same as above *)
                param_loc = dummy_loc;
                ret_param_loc = dummy_loc;
                fvis = j?visibility |> trans_visibility;
                mutability = NonPayable; (* field does not exist *)
                fid = j?id.AsInteger();
                floc = get_loc j;
                scope = cinfo.numid;
                scope_s = cid;
                org_scope_s = cid;
                cfg = empty_cfg
            }
            let stmt = j?body |> trans_block 
            let func = (fname, parms, [], stmt, finfo) 
            (cid, gvar_decls, structs, enums, func::func_defs, cinfo)
        | _ -> raise (Failure "Unsupported : trans_contractDefinition")
        ) (cid, [], [], [], [], cinfo) contract_parts 
    let (gvar_decls, func_defs) = (List.rev gvar_decls, List.rev func_defs) 
    let b = List.exists (fun (_,_,_,_,finfo) -> finfo.is_constructor) func_defs 
    if b then 
        (cid, gvar_decls, structs, enums, func_defs, cinfo)
    else
        (* make a new constructor if does not exist *)
        let fname = cid
        let parms = []
        let cnstr_calls = resolve_cnstr_calls cnstr_calls_inherit [] 
        let finfo = {
            is_constructor = true;
            is_payable = false;
            is_modifier = false;
            mod_list = []; mod_list2 = cnstr_calls;
            param_loc = dummy_loc; ret_param_loc = dummy_loc;
            fvis = Public; fid = (-1);
            mutability = NonPayable;
            floc = dummy_loc;
            scope = cinfo.numid; scope_s = cid; org_scope_s = cid; cfg = empty_cfg}
        let cnstr = (fname, parms, [], Skip, finfo) 
        (cid, gvar_decls, structs, enums, cnstr::func_defs, cinfo) 

let rec print_debug lst =
    match lst with
    | [] -> ()
    | hd :: tl -> printfn "%s" hd; print_debug tl

let translate : JsonValue -> pgm =
    fun json ->
    if not (json?nodeType.AsString() = "SourceUnit") then failwith "Assertion failed"
    let l = (* 0 nodes => `List [] *) 
        match json?nodes with
        | JsonValue.Array items -> Array.toList items
        | _ -> []
    let l' = List.filter (fun j -> j?nodeType.AsString() = "ContractDefinition") l 
    let cnames = List.map (fun json -> json?name.AsString()) l' 
    List.fold (fun acc j ->
        let node_typ = j?nodeType
        match node_typ with
        | JsonValue.String "ContractDefinition" -> acc @ [trans_contractDefinition cnames j]
        | _ -> acc (* Skip PragmaDirectve, and ImportDirective *)
    ) [] l

let run json = translate json