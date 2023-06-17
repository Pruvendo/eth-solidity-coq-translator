Require Import UtilityFunctions.
Require Import IntoFuncs.
Require Import IntoLedger.
Require Import StringHelpers.
Require Import Coq.Lists.List.
Require Import Io.All.
Require Import System.All.
Require Import ListString.All.
Require Import String.
Open Scope string_scope.
Require Import CoqJson.Json.
Import ListNotations.
Import C.Notations.
Import JsonNotations.
Local Open Scope json_scope.
Delimit Scope json_scope with json.
Require Import Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Numbers.NatInt.NZLog.
Require Import CoqJson.Parser.




(* ast get by path *)
Definition dict_of_ast(js:json) :=
let fix search_ast j := 
match j with 
| json_list l => fold_left app (map search_ast l) nil
| json_map m => match (j --> "nodeType"!) with 
                | "ast" => [(j --> "path"!, j --> "ast"?)]
                | _ => let fix iter m :=
                        match m with 
                        | empty => []
                        | mapkv k v m' => app(search_ast v)(iter m')
                        end in
                        iter m
                end
| _ => nil
end
in
json_map (list_to_map (search_ast js))
.
(* abi get by path *)
Definition dict_of_abi(js:json) :=
let fix search_ast j := 
match j with 
| json_list l => fold_left app (map search_ast l) nil
| json_map m => match (j --> "nodeType"!) with 
                | "abi" => [(j --> "path"!, j --> "abi"?)]
                | _ => let fix iter m :=
                        match m with 
                        | empty => []
                        | mapkv k v m' => app(search_ast v)(iter m')
                        end in
                        iter m
                end
| _ => nil
end
in
json_map (list_to_map (search_ast js))
.


Fixpoint getlistContr'(j: json): list (string * (list (string * string ))*json) :=
match j with
| json_data s => []
| json_list l =>    match l with
                    | nil => []
                    | _ =>  let fix concatenationWithNum (l: list json)(num: nat) : list (string  * (list (string * string ))* json):= 
                                  match l with 
                                  | a :: b => app(getlistContr' a )(concatenationWithNum (b)(num - 1))
                                  | nil => []
                                  end
                                    in concatenationWithNum l (List.length l)
                    end
| json_map m => match getString(json_get(inl "nodeType")(json_map m)) with
                    | "ContractDefinition" => let fix iter (contrName:string) (m: key_map) (wholeContractJson:json): list (string  * (list (string * string )) * json):=
                                              match m with 
                                              | empty => []
                                              | mapkv k v m' => 
                                                match k with 
                                                | "name" => iter (getString' v) m' wholeContractJson
                                                | "nodes" => let members := get_contract_members v  in
                                                            (* (* есть ли поля вообще?  *)
                                                                if Nat.eqb (List.length members) 0 
                                                                then nil (*тогда не нужен*)
                                                                (*                 вот тут поля собираем *)
                                                                else *)
                                                                [(contrName,  members, wholeContractJson)]
                                                | _ => iter contrName m' wholeContractJson
                                                end 
                                              end in 
                                                iter "" m j
                    | _ => let fix iter' m :=
                                    match m with 
                                    | empty => []
                                    | mapkv k v m' => app(iter'(m'))(getlistContr'  v)
                                    end in
                                    iter' m
                    end
end
.

Fixpoint import (sourceUnit: json): list string:= 
match sourceUnit with 
| json_data _ => nil
| json_list l => fold_left app (map import l) nil
| json_map m => match ((json_map m) --> "nodeType"!) with
                | "ImportDirective" => [((json_map m) --> "absolutePath"!)]
                | _ => let fix iter m :=
                        match m with 
                        | empty => nil
                        | mapkv k v m' => app (import v) (iter m')
                        end in
                        iter m
                end   
end.


(* get list of static variables with path *)
Fixpoint getStaticWithFile (j:json): list (string * (list (string * string))):= 
match j with 
| json_data s => nil
| json_list l => fold_left app (map getStaticWithFile l) nil
| json_map m => 
                match ((json_map m) --> "abi"??)  with 
                | Some abi => match (abi --> "data" ??) with 
                                | Some (json_list vars) => [( ((json_map m) --> "path"!), map (fun var => (var --> "name"!, var --> "type"! )) vars)]
                                | _ => nil
                                end
                | None => let fix iter' m :=
                                match m with 
                                | empty => nil
                                | mapkv k v m' => app(getStaticWithFile(v))(iter'(m'))
                                end in
                                (iter' m)
                end
end
.


(* path and static *)
Definition listVarStaticByContract(js:json): list ((string) * (list (string * string))) := getStaticWithFile js.



Definition getInheritanceContracts (contract: json): list string := 
let inheritanceSpecs := 
match (contract --> "baseContracts"?) with 
| json_list l => map (fun inheritanceSpec => ((inheritanceSpec--> "baseName"?)--> "name"!)) l
| _ => nil 
end in
inheritanceSpecs
.



Definition get_struct_members(j: json): (list (string * string )) :=
let variable_declarations := 
    get_json_with_nodetype "VariableDeclaration" j 
in
let variable_declarations := 
    filter (fun dec => (dec--> "constant"!) =? "true" ) variable_declarations 
in 
let record_nodes := 
    map (fun dec => ((dec--> "name"!),(dec--> "typeDescriptions"?--> "typeString"!)) ) variable_declarations 
in
record_nodes.

Definition get_structure_list (contract_definition: json) : list (string * (list (string * string))):=
let structures := get_json_with_nodetype "StructDefinition" contract_definition in
map 
(
    fun structure =>
        let variable_declarations := get_json_with_nodetype "VariableDeclaration" structure
        in
        let record_nodes := map (fun dec => ((dec--> "name"!),(dec--> "typeDescriptions"?--> "typeString"!)) ) variable_declarations 
        in
        let name := structure--> "name"! in 
        (name, record_nodes)
)
structures.


Definition get_list_const(j: json): (list (string * string * string )) :=
    let getValue(j:json) : string :=
        match j with 
        | json_map m => 
            match ((json_map m)--> "nodeType"!) with 
            | "Literal" => 
                ((json_map m)--> "value"!) ++ 
                if not ((((json_map m)--> "subdenomination"!) =? "null") || (((json_map m)--> "subdenomination"!) =? "")) 
                then " " ++ ((json_map m)--> "subdenomination"!) 
                else ""
            | _ => ""
            end
        | _ => ""
        end   
    in
    let variable_declarations := 
        get_json_with_nodetype "VariableDeclaration" j 
    in
    let variable_declarations := 
        filter (fun dec => (dec--> "constant"!) =? "true" ) variable_declarations 
    in 
    let record_nodes := 
        map (fun dec => ((dec--> "name"!),(dec--> "typeDescriptions"?--> "typeString"!), getValue(dec--> "value"?)) )variable_declarations 
    in
    let manually_added_consts :=
        let require_calls := 
            filter 
            (
                fun func_call_json => 
                (func_call_json --> "expression"? --> "name"!) =? "require"
            )
            (get_json_with_nodetype "FunctionCall" j) 
        in
        let const_ids :=
            map 
            (
                fun req_call_json =>
                    match (req_call_json --> "arguments"?) with 
                    | json_list (cons _ (cons head nil)) =>
                        let original_string_Id := head --> "typeDescriptions"? --> "typeIdentifier"!
                        in
                        original_string_Id
                    | _ => ""
                    end
            )
            require_calls
        in
        let const_ids := drop_duplicate const_ids String.eqb in
        let consts_with_num := 
            fold_left 
            (
                fun acc el => 
                match acc with 
                | cons (name, type, num) rest =>  if el =? "" then acc else (cons (el, "N", S num) acc)
                | nil => if el =? "" then nil else [(el, "N", 101%nat)]
                end
            ) 
            const_ids 
            nil
        in
        let consts_with_num := map (fun const => let '(name, type, num) := const in (name, type, writeNat num)) consts_with_num
        in
        consts_with_num
    in
app
manually_added_consts
record_nodes.

Definition str2t(s:string) := 
let fix of_string (s : string)(acc: LString.t) : LString.t :=
  match s with
  | "" => acc
  | String c s0 => of_string s0 (c :: acc) 
  end in
  rev'(of_string s nil)nil.




Definition Main
    (path_to_src: string)
    (abi_term: json)
    (ast_term: json)
    (contract_kind_json:json): list((*path*) string * (*text*) string) :=
let absolute_path := (ast_term--> "absolutePath"!) in
let nodes :=
    let nodes := 
        match (ast_term --> "nodes"?) with 
        | json_list l => l
        | _ => nil
        end 
        in
    sort 
    (
        fun x y => 
        not ((not ((x--> "nodeType"!) =? "ImportDirective")) && (((y--> "nodeType"!) =? "ImportDirective")))        
    ) 
    nodes
    in
let header :=
    (
        \n"Require Import UrsusEnvironment.Solidity.current.Environment." ++
        \n"Require Import UrsusEnvironment.Solidity.current.LocalGenerator."++
        \n"Require Import UrsusQC.CommonQCEnvironment."++
        \n"Require Import UrsusContractCreator.UrsusFieldUtils."
        
        (* ++ \n"Opaque address." *)
    )
in 
let import_declaration(import_directive: json) := 
    let file := (import_directive --> "absolutePath"!) in 
    let file := replaceWith[(path_to_src,"");(".sol", ""); ("/", ".")] file in
    let file := match file with | String "."%char tail => tail | _ => file end in
    \n"Require Import " ++ file ++ "."
in

let pragma_directive (pragma: json) : string := 
    match (pragma --> "literals"?) with 
    | json_list l => 
        let list_literals := map (fun element => match element with json_data s => s | _ => "" end) l 
        in
        let literals := String.concat "" list_literals
        in
        let literals := 
            replaceWith 
            [
                ("AbiHeader","AbiHeader ");
                ("ton-solidity","ton-solidity ")
            ] 
            literals
        in
        let statement := \n"#[pragma = " ++ """" ++ literals ++";"++ """" ++ "]"
        in
        (* statement *)
        ""
    | _ => "(* error pragma_directive *)"
    end

in
let structure_declaration(struct_definition: json) := 
    let structure_name := (struct_definition --> "canonicalName"!) in 
    let fields := get_struct_members (struct_definition--> "members"?) in
    let structure_name := replaceWith [(".", "_ι_")] structure_name in
    \n"Definition "++structure_name++"L: list Type := "++
    "["++
        String.concat ";" 
        (map 
        (
            fun field => 
            let '(name, type) := field in 
            \n"  ("++(xtype false type)++") : Type" )
        fields)++
    \n"]."++
    
    \n"Inductive "++structure_name++"Fields :="++
    String.concat "" 
    (map 
    (fun field => 
        let '(name, type) := field in 
        \n"| "++structure_name++"_ι_"++name++"  (*"++type++"*)" )
    fields)++
    \n"."++

    \n"LocalGeneratePruvendoRecord "++structure_name++"L "++structure_name++"Fields."++
    \n"Opaque "++structure_name++"LRecord." 
in 

let contract_declaration(contract_definition: json) :=
    let contract_name := contract_definition --> "name"! in
    let contract_kind := contract_definition --> "contractKind"! in
    let contract_fields := 
        let constract_fields_handler fields := 
        map 
        (
            fun field => 
                let '(name, type) := field 
                in
                (* FIXME *)
                let new_type := 
                    if (isInStr "interface" type) || (isInStr "contract" type)
                    then "address"
                    else type
                in
                (name, new_type)
        )   
        fields
        in
        let fields := get_contract_members (contract_definition --> "nodes"?)
        in
        constract_fields_handler 
        fields
    in
    let list_of_sending_out := 
        let list_of_contract_info := 
            map
            (
                fun typejson =>
                (typejson --> "name"!)
            )
            (get_json_with_nodetype "UserDefinedTypeName" contract_definition)
        in
        let list_of_contract_info :=
            filter 
            (fun contract => not (contract =? contract_name))
            list_of_contract_info
        in
        drop_duplicate list_of_contract_info String.eqb 
    in
    
    let list_of_structures := 
        let list_of_structures := 
            get_structure_list contract_definition 
        in
        let sorted_list_of_structures := 
            sort 
            (
                fun struct1 struct2 =>
                    let '(name1, fields1) := struct1 in 
                    let '(name2, fields2) := struct2 in 
                    fold_left (fun acc el => acc || (not (isInStr name1 (snd el)))) fields2 false
            )
            list_of_structures
        in
        sorted_list_of_structures
    in
    let list_of_constants := get_list_const contract_definition in
    let list_of_types_local_variables := (filter (fun name_type => let '(_, type) := name_type in not (type=?"tuple()")  )(handle_LocalState_list contract_definition)) in
    let inheritance_list := (getInheritanceContracts contract_definition) in
    let list_of_static_var := 
        match (abi_term --> "data" ??) with 
        | Some (json_list vars) => map (fun var => (var --> "name"!, var --> "type"! )) vars
        | _ => nil
        end 
    in
    let function_declarations := 
        FuncsFile 
        (* contract_name *)
        (* path *) 
        contract_definition
        (* list_of_import_contract_with_path *)
        (*app list_of_const_in_this_contract list_of_imported_const*) (*list_of_constants*) 
        (* callOptionExchange *)
    in
    \n"Module "++contract_name++"."++
    \n"#[translation = on]"++
    \n"#[quickchick = on]"++
    \n"#[language = solidity]"++
    \n"#[Contract = "++contract_name++"Contract]"++
    \n"Contract "++contract_name++" ;"++
    \n"Sends To (*need fix*) (*"++ 
    (
        String.concat 
        ", "
        list_of_sending_out    
    )
    ++"*) ; "++
    
    \n"(* Inherits  "++
    (   
        String.concat ", "
        (
            map 
            (
                fun definition =>
                definition ++ " (*" ++ (contract_kind_json --> definition!) ++ "*)"
            )
            (filter (fun definition => not (contract_kind_json --> definition! =? "interface")  ) inheritance_list)
        )
    )
    ++" ; *)"++
    \n"Types "++ 
    (
        String.concat ""
        (map 
        (
            fun structure => 
                let '(structure_name, structure_fields):= structure in 
                let structure_name := (replaceWith [(contract_name++".","");(".","_ι_")]structure_name)in 
                \n"Record " ++ structure_name ++ " := {"++
                (String.concat 
                ";"
                (map
                (
                    fun structure_field => 
                        let '(name, type):= structure_field in 
                        let type := replaceWith[(contract_name++".", "")] type in
                        \n"    " (*++ structure_name ++ "_ι_"*) ++ name++" : " ++ (xtype true type)
                )
                structure_fields 
                ))++
                \n"}"
        )
        list_of_structures)
    )++";"++
    \n"Constants "++
    (String.concat ""
    (
        map 
        (
            fun const => 
            let '(name, type, value):= const in
            \n"Definition " ++ name ++ " : " ++ type ++ " := "++ value
        )
    list_of_constants))++
    ";"++

    \n"Record Contract := {"++
    ( 
        match contract_fields with 
        | nil => "__:uint8;"
        | _ =>  String.concat ";"
            (
                map 
                (
                    fun field => 
                    let '(field_name, field_type) := field in
                    let field_type := replaceWith[(contract_name++".", "")] field_type in 
                    \n"    "++
                    (strOrNot (isInList field_name (map fst list_of_static_var)) "#[static] ") ++
                    field_name ++ ":" ++ 
                    (xtype true field_type) 
                )
                contract_fields
            )
        end
    )++
    \n"}."++
    (* \n"Transparent address."++ *)
    \n"SetUrsusOptions."++
    (* \n"Context `{intFunRec_gen boolean address}."++ *)
    \n"UseLocal Definition _ := ["++
    String.concat ";" 
    (map 
    (
        fun type_of_ledger_tree => 
            let '(name, type) := type_of_ledger_tree in 
            let type := replaceWith[(contract_name++".", "")] type in
            \n"    " ++ (xtype false type)
    )
    list_of_types_local_variables)++
    \n"]."++ 
    (
        String.concat ""
        (map 
        (
            fun structure => 
                let '(structure_name, structure_fields):= structure in 
                \n"Local Open Scope ursus_scope_" ++ structure_name ++ "."
        )
        list_of_structures)
    ) ++ 
    function_declarations++
    \n"EndContract Implements "++
    (
        String.concat ", "
        (
            map 
            (
                fun definition =>
                definition ++ " (*" ++ (contract_kind_json --> definition!) ++ "*)"
            )
            (filter (fun definition => (contract_kind_json --> definition! =? "interface")  ) inheritance_list)
            
        )
    )
    ++ "."++
    \n"End "++contract_name++"."
in 

let interface_declaration(interface_definition: json):string := 
    let interface_name := interface_definition --> "name"! in
    \n"Interfaces."++
    \n"SetUrsusOptions."++
    \n"MakeInterface Class "++interface_name++" :="++
    \n"{ "++
    \n""++
    (interface_signatures interface_definition) 
    ++
    \n"}."++
    \n"EndInterfaces."
in
(* finally *)
let final_file := 
    header ++
    (String.concat 
    ""
    (
        map 
        (fun node => 
            match (node--> "nodeType"!) with 
            | "ContractDefinition" => 
                match (node--> "contractKind"!) with 
                | "interface" => interface_declaration node 
                | _ => contract_declaration node
                end
            | "PragmaDirective" => pragma_directive node
            | "ImportDirective" => import_declaration node 
            | "StructDefinition" => structure_declaration node
            | _ => EmptyString
            end
        )
        nodes
    ))
in
let ledger_file :=
(String.concat 
""
(
    map 
    (fun node => 
        match (node --> "nodeType"!) with 
        | "ContractDefinition" => 
            match (node --> "contractKind"!) with 
            | "contract" => 
                let list_of_types_local_variables := 
                (
                    filter 
                    (fun name_type => let '(_, type) := name_type in not (type=?"tuple()")  )
                    (handle_LocalState_list node)
                ) 
                in
                LedgerFile (list_of_types_local_variables)
            | _ => ""
            end
        | _ => EmptyString
        end
    )
    nodes
))
in
(* let final_path := replaceWith [ (path_to_src, "translated/") ; ("//","/"); (".sol", ".v")] absolute_path in  *)
[
    ( replaceWith[(".sol", "_LocalState.sol")] absolute_path , ledger_file);
    ( absolute_path, final_file)
]
.


Fixpoint t2strPlusRev' (t : LString.t)(acc: string) : string :=
match t with
| tail :: body => t2strPlusRev' body ( String tail acc)
| [] => acc
end.

Local Open Scope char.

Definition primary_processing(fileName: LString.t)(json_ast: LString.t): LString.t:=
let fix refactoring 
    (json_ast: LString.t)
    (fileName: LString.t)
    (acc:LString.t)
    (state: ascii)
    (collectedAbsolutePath: LString.t):=
    (* 0 - means searching needed pattern*)
    (* 1 - means collecting absolutePath *)
    (* 2 - means collecting needed json*)
match json_ast with 
| "["::"010"::" "::" "::"{"::"010"::" "::" "::" "::" "::""""::"a"::"b"::"s"::"o"::"l"::"u"::"t"::"e"::"P"::"a"::"t"::"h"::""""::":" :: body => 
    refactoring
    body 
    (fileName)
    (":"::""""::"h"::"t"::"a"::"P"::"e"::"t"::"u"::"l"::"o"::"s"::"b"::"a"::""""::" "::" "::" "::" "::"010":: "{"::" "::" ":: acc)
    ("1")
    (nil)
| """" :: "," :: body => 
    match state with 
    | "1" => 
        if isInStr (t2str fileName) (t2strPlusRev' collectedAbsolutePath "")
        then refactoring body nil ("," :: """" :: acc) ("2") (collectedAbsolutePath)
        else refactoring body fileName nil "0" nil
    | "2" => refactoring body nil (","::""""::acc) state collectedAbsolutePath  
    | _ => refactoring body fileName (nil)(state)(nil)
    end 
| "010"::" " :: " " :: "}" :: "010" :: "," :: "010" ::" " :: " " :: "{"::"010" :: " "::" "::" "::" "::""""::"a"::"b"::"s"::"o"::"l"::"u"::"t"::"e"::"P"::"a"::"t"::"h"::""""::":" :: body =>
    match state with 
    | "0" => 
        refactoring
        body 
        (fileName)
        (":"::""""::"h"::"t"::"a"::"P"::"e"::"t"::"u"::"l"::"o"::"s"::"b"::"a"::""""::" "::" "::" "::" "::"010":: "{"::" "::" ":: "010"::"["::
        acc)
        ("1")
        (nil)
    | "2" => "}"::" "::" "::acc
    | _ => refactoring body fileName (nil)(state)(nil)
    end
| " "::" "::"}"::"010"::"010"::"]"::"010"::nil =>
    match state with 
    | "2" => "}" :: " " :: " " :: acc
    | _ => nil
    end
| head :: body => 
    match state with 
    | "1" => refactoring body fileName (head::acc)(state)(head::collectedAbsolutePath)
    | "2" => refactoring body nil (head::acc) state collectedAbsolutePath
    | _ => refactoring body fileName (nil)(state)(nil)
    end
| nil => nil
end in
let json_ast := rev' (refactoring json_ast fileName nil "0" nil) nil in 
match json_ast with 
| "[" :: body => body 
| json_ast => json_ast
end
.



Definition get_contractkind_json(json_ast: LString.t): json :=
let fix iterate (json_ast: LString.t) (acc:LString.t)(skip:bool)(mapping: key_map):json :=
    match json_ast with
    | """"::"c"::"o"::"n"::"t"::"r"::"a"::"c"::"t"::"K"::"i"::"n"::"d" ::"""":: tail => 
            iterate 
            (tail) 
            (""""::"d"::"n"::"i"::"K"::"t"::"c"::"a"::"r"::"t"::"n"::"o"::"c"::""""::"{"::acc)
            (false)
            (mapping)
            
    | """"::"n"::"o"::"d"::"e"::"T"::"y"::"p"::"e"::""""::":"::" "::""""::"C"::"o"::"n"::"t"::"r"::"a"::"c"::"t"::"D"::"e"::"f"::"i"::"n"::"i"::"t"::"i"::"o"::"n"::""""::tail =>
            let js: @key_map json := 
                let acc := "}"::""""::"n"::"o"::"i"::"t"::"i"::"n"::"i"::"f"::"e"::"D"::"t"::"c"::"a"::"r"::"t"::"n"::"o"::"C"::""""::":"::""""::"e"::"p"::"y"::"T"::"e"::"d"::"o"::"n"::""""::acc in
                let LStr :=  (rev' acc nil ) in 
                let '(LStr, depth) := reconfigure LStr nil nil 0 0 in 
                let Str :=  t2strPlusRev' LStr ""%string in 
                let ast_term := pars' Str depth depth in
                let key: string := ast_term-->("name"%string)! in 
                let value: json := ast_term-->("contractKind"%string)? in
                mapkv (key) (value) mapping
            in
            iterate 
            (tail) 
            (nil)
            (true)
            (js)
    | head :: tail => 
        if skip 
        then iterate tail nil true mapping 
        else iterate tail (head::acc) false mapping
    | nil => json_map mapping
    end
    in
iterate json_ast nil true empty
.


Definition get_last_item_from_path(path: LString.t):= 
    (* need handle from end *)
let path := rev' path nil in 
let fix get_last (path': LString.t) (acc: LString.t) :=    
    match path' with 
    | "/" :: body => "/"::acc
    | "n"::"o"::"s"::"j"::"."::"t"::"s"::"a"::"."::body => get_last body ("."::"s"::"o"::"l"::nil)
    | head :: body => get_last body (head::acc)
    | nil => nil
    end
    in 
get_last path nil
.
Local Close Scope char.


Fixpoint drop_last {X:Type} (l:list X):=
match l with 
| tail :: nil => nil 
| nil => nil 
| tail :: body => tail :: drop_last body
end    
.
(* Fixpoint create_folders (originalpath : string) (paths_of_contract : list string) (log: string) : C.t System.effect Datatypes.unit:=
match paths_of_contract with 
| tail :: body =>   let path := 
                        replace_few_things [originalpath][""]
                        (String.concat "/" (map fileNameToCorrectPath (split_string tail "/")))  in 
                    (* let command := "mkdir translated/Contracts/" ++ path in 
                    let! _ := System.system (LString.s command ) in *)
                    let folder := String.concat "/" (drop_last(split_string path "/")) in
                    let command := "mkdir -p translated" ++ folder in 
                    let! _ := System.log (LString.s folder) in
                    let! _ := System.system (LString.s  command) in
                    create_folders originalpath body log
| nil => System.log (LString.s log)
end    
. *)

Fixpoint imperative (originalpath : string) (files:list (string * string))(output_path: option string) (log: string) : C.t System.effect Datatypes.unit:=
match files with 
| tail :: body => let '(name, text):= tail in
                    let! some1 := System.log (LString.s ("original name is ->" ++ name)) in
                    (* let! some2 := System.log (LString.s ("original path is ->" ++ originalpath)) in *)
                    let name := (replace_few_things [originalpath][""] name) in 
                    let folder := String.concat "/" (drop_last(split_string name "/")) in
                    let folder := replaceWith[("//", "/")] folder in
                    let command := "mkdir -p translated/"++ folder in 
                    (* let! some3 := 
                        match output_path with 
                        | Some _ => System.log (str2t text)  
                        | None => (System.log nil)
                        end in
                    let! some4 := 
                        match output_path with 
                        | Some apth => (System.log (str2t apth)) 
                        | None => System.log (LString.s command)
                        end in *)
                    let! some5 := 
                        match output_path with 
                        | Some _ => (System.system nil) 
                        | None => System.system (LString.s command) 
                        end in
                    let path_for_saving := 
                        match output_path with 
                        | Some output_path => 
                            LString.s output_path
                        | None => 
                            (LString.s ("translated/" ++ (replaceWith [(".sol", ".v")] name)))
                        end
                    in
                    let! some6 := 
                        System.write_file 
                            path_for_saving
                            (str2t ("(*" ++ originalpath ++ "*)" ++ \n"" ++ text)) in
                    imperative originalpath body output_path log
| nil => System.log (LString.s log)
end
.

Definition translator (argv : list LString.t): 
    C.t System.effect Datatypes.unit :=
match argv with
| [ _ ; path_to_ast; path_to_abi; path_to_src; output_path] =>
    let path_to_src := t2str path_to_src in
    let! ast_LString := System.read_file path_to_ast in
    let! abi_LString := System.read_file path_to_abi in
    let! some1 := System.log (path_to_ast)  in
    match ast_LString with
    | Some ast_LString =>
        let ast_LString: LString.t := 
            let file_name := (get_last_item_from_path path_to_ast) in
            primary_processing file_name ast_LString in
        let ast_LString: LString.t := 
            match ast_LString with 
            | "010"%char ::" "%char :: " "%char :: body => body  
            | " "%char :: " "%char :: body => body  
            | _ => ast_LString
            end
        in
        let '(ast_LString, ast_depth) := reconfigure ast_LString nil nil 0 0 in 
        let ast_LString :=  t2strPlusRev' ast_LString "" in 
        let ast_term := pars' ast_LString  ast_depth ast_depth in 
        let abi_term := 
            match abi_LString with 
            | Some abi_LString => 
                let '(abi_LString, abi_depth) := reconfigure abi_LString nil nil 0 0 in 
                let abi_LString :=  t2strPlusRev' abi_LString "" in 
                let abi_term := pars' abi_LString abi_depth abi_depth in
                abi_term
            | _ => { }
            end
        in 
        let list_of_file := (* actually one is needed one*)
            Main path_to_src abi_term ast_term {}
        in
        let! some2 := 
            imperative path_to_src list_of_file (Some (t2str output_path)) "" 
        in
        System.log (LString.s "") 
    | _ => System.log  (LString.s "Cannot read the files.1"%string)
    end
| [ _ ; path_to_ast0; path_to_abi0; path_to_src0] =>
    let path_to_src := t2str path_to_src0 in
    let! ast_LString := System.read_file path_to_ast0 in
    let! abi_LString := System.read_file path_to_abi0 in
    match ast_LString with
    | Some ast_LString =>
        let ast_LString_for_contractkinds := ast_LString in
        (*let ast_LString: LString.t := 
            primary_processing (get_last_item_from_path path_to_ast0) ast_LString in
        let ast_LString: LString.t := 
            match ast_LString with 
            | "010"%char ::" "%char :: " "%char :: body => body  
            | " "%char :: " "%char :: body => body  
            | _ => ast_LString
            end
        in *)
        let '(ast_LString, ast_depth) := reconfigure ast_LString nil nil 0 0 in 
        let ast_LString :=  t2strPlusRev' ast_LString "" in 
        let ast_term := pars' ast_LString  ast_depth ast_depth in 
        
        let abi_term := 
            match abi_LString with 
            | Some abi_LString => 
                let '(abi_LString, abi_depth) := reconfigure abi_LString nil nil 0 0 in 
                let abi_LString :=  t2strPlusRev' abi_LString "" in 
                let abi_term := pars' abi_LString abi_depth abi_depth in
                abi_term
            | _ => { }
            end
        in 
        let list_of_file := (*basically one*)
            Main path_to_src abi_term ast_term (get_contractkind_json ast_LString_for_contractkinds)
        in
        
        let! some3 := imperative path_to_src list_of_file None "" in
        (* let '(json_LStringt, depth ) := (reconfigure (c' )[][] 0 0) in 
        let json_string :=  t2strPlusRev' json_LStringt "" in 
        let js := pars' (json_string) depth depth in 
        let! _ := imperative originalpath (main js originalpath) "saved into translated/" in *)
        System.log (LString.s "") 
    | _ => 
        let! log := System.log  (LString.s "Cannot read the files.2"%string) in
        let! log := System.log  (path_to_src0) in 
        let! log := System.log  (path_to_abi0) in 
        System.log  (path_to_ast0)
    end
| _ => System.log (LString.s "Expected a parameter.")
end.


Definition translate := Extraction.launch translator.
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extraction "main" translate. 
