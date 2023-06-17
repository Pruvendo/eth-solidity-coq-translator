Require Import StringHelpers.
Require Import Coq.Lists.List.
Require Import Io.All.
Require Import System.All.
Require Import ListString.All.
Require Import String.
Require CoqJson.KeyMaps.
Require Import Coq.Bool.Bool.
Open Scope string_scope.
Require Import Bool.

Require Import CoqJson.Json.

Import ListNotations.
Import C.Notations.
Import JsonNotations.

Local Open Scope json_scope.
Delimit Scope json_scope with json.
Require Import Ascii.

Require Import Coq.Init.Nat.



(* Definition range (n:nat):list nat:=
let fix range' (n i : nat) :=
match n with 
| S n' => i :: (range' n' (S i))
| O => nil
end  in
range' n 0
. *)

Fixpoint isInList(arg: string)(ls: list string): bool :=
match ls with 
| head :: body => if arg =? head 
                    then true 
                    else isInList(arg)(body)
| nil => false
end  
.



Notation "'\n' a" := (String "010"%char a)(at level 0).


Definition getJSON(o: option json): json :=
  match o with
    | Some a => a
    | None => { }
  end.

Definition getString(o: option json): string :=
  match getJSON(o) with
  | json_data s => s
  | _ => ""
  end.

Definition getString'(j : json): string := 
match j with 
| json_data s => s
| _ => ""
end  
.
Definition getMap(j: json) := 
match j with 
| json_map m => m
| _ => empty
end  
.



Fixpoint t2str (t : LString.t): string :=
match t with 
| tail :: body => (String tail "")++t2str(body)
| nil => ""
end    
.


(* Definition enumerate {A}(l:list A): list (nat*A):=
  let fix enumerate' {A}(len: nat)(l:list A): list (nat*A):=
let n:= (List.length l)-1 in 
match l with 
| tail :: body => pair(len- n)(tail)::enumerate'(len)(body)
| nil => nil
end  in
enumerate'((List.length l)-1)l 
. *)

(* Compute enumerate ["";"1"]. *)

Fixpoint handle_struct_name (name :string) : string :=
match name with  
| String "."%char tail => "_ι_" ++ (handle_struct_name tail) 
| String head tail => String head (handle_struct_name tail)
| EmptyString => EmptyString
end
.

Definition strOrNot(fl:bool)(str: string): string :=  if fl then str else "".

Fixpoint replace'(old: string)(new: string) (s:string) (acc: string):=
match s with 
| String head body => let lenO := length old in 
                      let lenA := length acc in
                      if old =? substring 0 lenO acc
                      then replace' (old)(new)(body)(String (head)(new ++ substring lenO (lenA) acc))
                      else (replace' (old) (new) (body) (String (head) acc))
| EmptyString => let lenO := length old in 
                  let lenA := length acc in
                  if old =? substring (0) lenO acc
                  then  new ++ substring (lenO)(lenA) acc 
                  else  acc
end  
.

Definition replace(old: string)(new: string) (s:string) := 
  let out := string_rev (replace' (string_rev old) (string_rev new) s "") in out.

Definition replace_or_nothing(old: string)(new:string)(s: string):=
  let out := string_rev (replace' (string_rev old) (string_rev new) s "") in
  if out =? s  then "" else out
.


Definition not (b: bool):=
match b with
| true => false
| false => true
end  
.
Fixpoint list_to_map(l: list (string * json)): key_map := 
match l with 
| tail :: body => mapkv (fst tail) (snd tail) (list_to_map body)
| nil => empty
end.
Fixpoint replace_few_things (old: list string) (new: list string) (s:string): string :=
match old, new  with 
| tail' :: body', tail'' :: body'' => let newS := replace tail' tail'' s in replace_few_things (body') (body'') (newS)
| nil,nil => s
| _, _ => ""
end
.

Fixpoint replaceWith(oldAndNew: list(string*string))(s:string):string :=
match oldAndNew with 
| tail :: body => let newS:= replace (fst tail)(snd tail) s in replaceWith body newS
| nil => s
end
.

Definition isInStr (it: string)(s: string): bool := not(s =? replace(it)("")(s)).

Fixpoint split_string' (s: string) (p: string) n : list string :=
match n with
| O => []
| S n' => 
if (string_dec s "") then [] else
if (string_dec p "") then (substring 0 1 s)::
                          (split_string' (substring 1 ((String.length s) - 1) s) p n') else
let i := index 0 p s in
match i with
| None => [s]
| Some k => let ss := substring 0 k s in
            let a  := k + (String.length p) in
            let s' := substring a ((String.length s) - a) s in
            ss::(split_string' s' p n')
end
end.

Definition split_string s p := split_string' s p (String.length s). 


Definition simpleType :=  replaceWith [("string","string");("uint256","uint256");("uint128","uint128");("uint128","uint128");
("uint64","uint64");("uint32","uint32");("uint16","uint16");("uint8","uint8");
("uint","uint");("bool","boolean");("cell","TvmCell");("TvmCell","TvmCell");("TvmSlice","TvmSlice"); 
(* ("bytes4","(XList XUInteger8)"); *)
("bytes","bytes");("TvmBuilder","TvmBuilder")].


Definition xtype(resolve_name:bool)(type:string):string :=
let type := replaceWith [("type(","(");("tuple()", "");("("," ( "); (")"," ) "); (",", " , ");(".", "_ι_");(",", "**"); ("  ", " ") ] type in
let splittedType := split_string type " " in
let fix handle_splittedType (typeSeq: list string)(context_stack: list string)(acc: string) := 
match typeSeq with 
| head :: body => 
      match head with
      | "contract" => handle_splittedType(body)("contract"::context_stack)(acc)
      | "struct" => handle_splittedType(body)("struct"::context_stack)(acc)
      | "library" => handle_splittedType(body)("library"::context_stack)(acc)
      | "=>" => handle_splittedType(body)(context_stack)(acc ++ " )(" )
      | "mapping" => handle_splittedType(body)(context_stack)(acc ++ " mapping " )
      | "optional" => handle_splittedType(body)(context_stack)(acc ++ " optional " )
      | "int_const" => handle_splittedType(body)("int_const"::context_stack)(acc)
      | "(" => match context_stack with
              | "tuple" :: body' => handle_splittedType(body)(context_stack)(acc++ " " ++ head )
              | _ => handle_splittedType(body)(context_stack)(acc ++ " "++ head )
              end
      | "tuple" => handle_splittedType(body)("tuple"::context_stack)(acc)
      | ")" =>  match context_stack with
                | "tuple" :: body' => handle_splittedType(body)(body')(acc ++ " "++ head )
                | _ => handle_splittedType(body)(context_stack)(acc ++ " "++ head )
                end
      | "**" => handle_splittedType(body)(context_stack)(acc ++ " ** " ++ " ")        
      | _ =>  let isArray := isInStr "[]" head in 
              let head := replaceWith [("[]","")] head in 
              (* fixme double unnecessary replace to ι  *)
              let head := 
                last (split_string head "_ι_") head in
              match context_stack with
                  | "int_const" :: body' => handle_splittedType(body)(body')(acc ++ " " ++ head)
                  | "contract"  :: body' => handle_splittedType(body)(body')(acc ++ "("++ (if resolve_name then "_ResolveName" ++ " "++ """" ++ head ++  """" else (head++"LRecord")) ++ (strOrNot isArray "[]") ++ ")")
                  | "struct"    :: body' => handle_splittedType(body)(body')(acc ++ "("++ (if resolve_name then "_ResolveName" ++ " "++ """" ++ head ++  """" else (head++"LRecord")) ++ (strOrNot isArray "[]") ++ ")")
                  | "library"   :: body' => handle_splittedType(body)(body')(acc ++ "("++ (if resolve_name then "_ResolveName" ++ " "++ """" ++ head ++  """" else (head++"LRecord")) ++ (strOrNot isArray "[]") ++ ")")
                  | _ => 
                      let head := simpleType head in
                      handle_splittedType(body)(context_stack)(acc ++ " " ++ head++(strOrNot isArray "[]"))
                  end
      end
| nil => acc 
(* ++ ""++String.concat "," context_stack ++ "" *)
end
in 
handle_splittedType splittedType nil ""  
.


Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := (natToDigit (n mod 10)) ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
end.

Definition writeNat (n : nat) : string :=
  writeNatAux n n "".

Definition drop_duplicate{A}(ls : list A)(eq: A -> A -> bool) :list A:=
  let fix drop_dupl (ls : list A)(eq: A -> A -> bool)(acc:list A) :=
  let fix isInList (a: A)(l: list A):bool := 
    match l with 
    | tail' :: body' =>  if eq tail' a then true else isInList a body'
    | nil => false
    end
  in
  match ls with
  | tail :: body => 
    if isInList tail acc 
    then drop_dupl body eq acc 
    else drop_dupl body eq (app acc [tail])
  | nil => acc
  end    
  in
drop_dupl ls eq nil
.

Notation "b '-->' something '!'  " := (getString(json_get(inl something )(b))) (at level 500, left associativity).
Notation "b '-->' something '?'  " := (getJSON(json_get(inl something )(b))) (at level 500, left associativity).
Notation "b '-->' something '??'  " := ((json_get(inl something )(b))) (at level 500, left associativity).


Arguments app {_} (l l')%list_scope.

Fixpoint get_json_with_nodetype(nodetype:string)(j: json): list json :=
let fix iter' m :=
    match m with 
    | empty => []
    | mapkv k v m' => app (get_json_with_nodetype nodetype v) (iter' m')
    end 
in    
match j with
  | json_data s => []
  | json_list l => fold_left app (map (get_json_with_nodetype nodetype) l) nil 
  | json_map m => 
                match( j --> "nodeType"!) with
                | s => 
                    if s =? nodetype 
                    then [j]
                    else iter' m
                end
end
.

(* MAIN PART*)
(* TODO rewrite with "get_json_with_nodetype" *)
Definition LocalState_list(j:json): ((list (string * string ))):=
let fix variableDeclaration(j:json): list(string*string):=
  match j with 
  | json_list l => fold_left app (map variableDeclaration l) nil 
  | json_map m => let name := ( j --> "name"! ) in 
                  let type := ( j --> "typeDescriptions"?  --> "typeString"! ) in
                  [(name, type)]
  | _ => nil
end in
let fix json2types (j: json) : list (string * string) :=
  let fix iter m :=
    match m with 
    | empty => []
    | mapkv k v m' => app (json2types v)(iter m')
    end 
  in
match j with
| json_data s => []
| json_list l => fold_left app (map json2types l) nil
| json_map m => 
  match ((json_map m) --> "nodeType"!) with 
  | "FunctionCall" => 
    rev_append
    (
      match ((json_map m) --> "expression"? --> "memberName"!) with 
      | "store" => [("","optional(TvmBuilder)")]
      | "loadUnsigned" =>
        (let args := ((json_map m) --> "arguments"?) in
        let args := match args with | json_list l => l | _ => nil end in
        let args := map (fun arg => "uint"++((arg --> "value"!)) ) args in
        [("","optional ("++String.concat "," (app args ["TvmSlice"]) ++ ")")])
      | "decode" => 
          let args := ((json_map m) --> "arguments"?) in
          let args := match args with json_list l => l | _ => nil end in
          let arg_types_list :=  map (fun arg => (arg --> "typeDescriptions"? --> "typeString"!)) args in
          [("" ,"optional(" ++ String.concat " , " (app arg_types_list ["TvmSlice"])++")");
          ("" ,"(" ++ (String.concat " , " arg_types_list) ++ ")")]
      | "delMax" => 
          let needed_type := ((json_map m) --> "expression"? --> "expression"? --> "typeDescriptions"? --> "typeString"! ) in
          let transformed_type := replaceWith[("mapping(", "tuple("); ("=>",", ")]needed_type in
          [("" ,transformed_type)]
      | _ => nil
      end
    )
    (
      let fix iter' m :=
        match m with 
        | empty => []
        | mapkv "expression" v m' => app (json2types v) (iter' m')
        | mapkv _ _ m' => (iter' m')
        end 
      in
      iter' m
    )
  | "VariableDeclarationStatement" => 
    let declarations := ((json_map m) --> "declarations"?) in
    app (variableDeclaration declarations) (iter m)
  | "FunctionDefinition" => 
    app
    (let parameters := (json_map m)-->"parameters"? -->"parameters"? in
    let parameters := match parameters with | json_list l => l | _ => nil end in
    let parameter_types := map (fun parameter => ("",parameter -->"typeDescriptions"? --> "typeString"!)) parameters in
    let return_parameters := (json_map m)-->"returnParameters"? -->"parameters"? in
    let return_parameters := match return_parameters with | json_list l => l | _ => nil end in
    let return_parameters_types := map (fun parameter => (parameter -->"typeDescriptions"? --> "typeString"!)) return_parameters in
    ("", "tuple("++(String.concat "," return_parameters_types) ++ ")"):: parameter_types )
    (
      let fix iter' m :=
        match m with 
        | empty => []
        | mapkv "body" v m' => app (json2types v) (iter' m')
        | mapkv _ _ m' => (iter' m')
        end 
      in
      iter' m
    )
  | _ => (iter m)
  end
end in
(json2types j)
.

Definition handle_LocalState_list(contractJson:json) := 
  drop_duplicate (LocalState_list contractJson) (fun x y => (snd x) =? (snd y)).

Definition get_list_of_func_calls (function_definition_json: json) : list string := 
  let identifiers := 
    let tmp := 
      filter 
      (fun indent => isInStr "function" ((indent --> "typeDescriptions"?) --> "typeString"!))
      (get_json_with_nodetype "Identifier" function_definition_json) 
    in
    map (fun ident => (ident --> "name"!)) tmp
  in
  let member_accessors :=
    let tmp := 
    filter 
    (fun accessor => isInStr "function" ((accessor --> "typeDescriptions"?) --> "typeString"!))
    (get_json_with_nodetype "MemberAccess" function_definition_json) 
    in 
    map (fun accessor => (accessor --> "memberName"!)) tmp
  in
  let modifiers :=
    map
    (
      fun modifier =>
      ((modifier --> "modifierName"?) --> "name"!)
    )
    (get_json_with_nodetype "ModifierInvocation" function_definition_json )
  in
  let returns :=
    let tmp := filter (fun return' => (return' --> "expression"!) =? "null") (get_json_with_nodetype "Return" function_definition_json) in
    map
    (fun _ => "return")
    tmp
  in
app identifiers (app member_accessors (app modifiers returns)).


(* https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html *)
Fixpoint insert{A} (leb: A -> A -> bool) (i : A) (l : list A) :=
  match l with
  | [] => [i]
  | h :: t => if (leb i h) then i :: h :: t else h :: insert leb i t
  end.
Fixpoint sort{A} (leb: A -> A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t => insert leb h (sort leb t)
  end.



(* name, arg, returnParameters, modifiers, visibility, lice, body *)
Definition get_list_function_contract_json(contract_json:json): list (string * 
                                                                      list (string * string) * 
                                                                      list (string * string) * 
                                                                      list (string * list (json)) * 
                                                                      (list string) * 
                                                                      bool * 
                                                                      json) :=

  let list_contract_definition_json := 
    get_json_with_nodetype "ContractDefinition" contract_json 
  in
  let transformed_list_contract_definition_json := 
    map
    (
      fun contract_definition_json =>
        let functions := 
          let list_function_definition := 
            get_json_with_nodetype "FunctionDefinition" contract_definition_json 
          in
          let transformed_list_function_definition := 
          map
          (
            fun function_definition_json =>
              let name := 
                let name := function_definition_json --> "name"! 
                in
                if name =? ""
                then function_definition_json --> "kind"! 
                else name 
              in
              let parameters := 
                  let parameters_json := 
                    function_definition_json --> "parameters"? --> "parameters"? 
                  in
                  let parameter_list := 
                    match parameters_json with | json_list l => l | _ => nil end 
                  in
                  map 
                  (
                    fun parameter =>
                      (parameter-->"name"!, parameter -->"typeDescriptions"? --> "typeString"!)
                  )
                  parameter_list
              in
              let return_parameters := 
                  let return_parameters_json := 
                    function_definition_json --> "returnParameters"? --> "parameters"? 
                  in
                  let return_parameter_list := 
                    match return_parameters_json with | json_list l => l | _ => nil end 
                  in
                  map 
                  (
                    fun parameter =>
                      (parameter-->"name"!, parameter -->"typeDescriptions"? --> "typeString"!)
                  )
                  return_parameter_list
              in
              let modifiers := 
                  let modifiers_list := 
                    get_json_with_nodetype "ModifierInvocation" function_definition_json 
                  in
                  map 
                  (
                    fun modifier =>
                      let name := modifier --> "modifierName"? --> "name"!
                      in
                      let arguments_list := 
                        match (modifier --> "arguments"?) with | json_list l => l | _ => nil end 
                      in
                      (* let arguments := 
                      map 
                      (
                        fun argument => 
                          (argument --> "name"!, argument--> "typeDescriptions"? --> "typeString"!)
                      ) 
                      arguments_list
                      in  *)
                      (name, arguments_list)
                  )
                  modifiers_list
              in
              let function_properties :=  
                app 
                (
                  let stateMutability := function_definition_json --> "stateMutability"! 
                  in
                  if stateMutability =? ""
                  then nil
                  else [stateMutability]
                )
                (
                  let visibility := function_definition_json --> "visibility"! in
                  if visibility =? ""
                  then nil
                  else [visibility]
                )
              in
              let function_calls :=
                get_list_of_func_calls function_definition_json
              in
              let body := 
                function_definition_json --> "body"?
              in
              let lice := 
                (isInList "require" function_calls) || (isInList "selfdestruct" function_calls) ||
                (isInList "return" function_calls) ||  (isInList "get" function_calls)
              in
              (name, parameters, return_parameters, modifiers, function_properties, lice, body)
          )
          list_function_definition
          in
          transformed_list_function_definition
        in
        let contract_function_modifiers :=
            let modifiers := 
                get_json_with_nodetype "ModifierDefinition" contract_definition_json 
            in
            map
            (
              fun modifier_json =>
              (* name, arg, returnParameters, modifiers, visibility, lice, body *)
                let name := modifier_json --> "name"! 
                in
                let parameters := 
                  let parameters_json := 
                    modifier_json --> "parameters"? --> "parameters"? 
                  in
                  let parameter_list := 
                    match parameters_json with | json_list l => l | _ => nil end 
                  in
                  map 
                  (
                    fun parameter =>
                      (parameter-->"name"!, parameter -->"typeDescriptions"? --> "typeString"!)
                  )
                  parameter_list
                in
                let body := 
                    modifier_json --> "body"? 
                in 
                let return_parameters := 
                    match (body --> "statements"?) with 
                    | json_list nil => [("modifier", "pre")]
                    | json_list (head::rest) => 
                        match (head --> "nodeType"!) with 
                        | "PlaceholderStatement" => 
                            [("modifier", "post")]
                        | _ => 
                            [("modifier", "pre")]
                        end
                    | _ => [("modifier", "pre")]
                    end
                in 
                let modifiers := nil 
                in 
                let function_properties := nil 
                in 
                let lice := true
                in
                (name, parameters, return_parameters, modifiers, function_properties, lice, body)
            )
            modifiers
        in
        let list_modifiers_functions :=
          sort
          (
            fun func1 func2 =>
              let '(name1, _, _, _, _, _, _) := func1 in
              let '(_, _, _, modifiers2, _, _, body2) := func2 in
              let list_func_calls: list string := (get_list_of_func_calls body2) in
              let modifiers2_names: list string := 
                  map (fun modifier => let '(name, args):= modifier in name) modifiers2
              in
              (isInList name1 modifiers2_names) || (isInList name1 list_func_calls)
          )
          (app contract_function_modifiers functions)
        in
        list_modifiers_functions
    )
    list_contract_definition_json
    in
  let transformed_function_list := 
    hd nil transformed_list_contract_definition_json
  in
  transformed_function_list
.



Definition interface_signatures(contract_json:json) := 
let contract_kind := contract_json --> "contractKind"! in
match contract_kind with 
| "interface" =>
  let nodes := contract_json --> "nodes"? in 
  let nodes := match nodes with | json_list l => l | _ => nil end in
  let nodes := 
    map 
    (
      fun node => 
        match (node --> "nodeType"!) with 
        | "FunctionDefinition" =>
          (
            let name := node --> "name"! in
            let parameters := node --> "parameters"? --> "parameters"? in
            let parameters := match parameters with | json_list l => l | _ => nil end in
            let is_empty_parameters := match parameters with | nil => true | _ => false end in
            let parameters :=
              map 
              (
                fun parameter =>
                  let name := parameter --> "name"! in
                  let is_indexed := parameter --> "indexed"! =? "true" in
                  let type := parameter --> "typeDescriptions"? --> "typeString"! in
                  "( " ++ (if is_indexed then "(* indexed *)" else "") ++ type ++ ")"
              )
              parameters
            in

            let return_parameters := node --> "returnParameters"? --> "parameters"? in
            let return_parameters := match return_parameters with | json_list l => l | _ => nil end in
            let is_empty_return_parameters := match parameters with | nil => true | _ => false end in
            let return_parameters :=
              map 
              (
                fun parameter =>
                  let name := parameter --> "name"! in
                  let type := parameter --> "typeDescriptions"? --> "typeString"! in
                  "(" ++ type ++ ")"
              )
              return_parameters
            in
            \n"    " ++ name ++ " : " ++ 
            (String.concat " -> " parameters) ++
            (if is_empty_parameters then "" else " -> ") ++
            "( UExpression ("++
            (
              if is_empty_return_parameters 
              then "PhantomType" 
              else (String.concat " ** " return_parameters)
            ) ++
            ") false)"
          )
        | _ => " (* error: this nodeType isn't uncluded to translator*)"
        end
    )
    nodes
  in
  String.concat ";" nodes
| _ => 
  "(* error contractKind isn't interface *)"
end
.


Fixpoint get_contract_members (j:json): list(string*string) :=
match j with
| json_data s' => nil
| json_list l => fold_left app (map get_contract_members l) nil
| json_map m' => 
    match getString(json_get(inl "nodeType")(json_map m')) with
    | "VariableDeclaration" => 
      if ((json_map m')-->"constant"!) =? "true"
      then nil
      else [((json_map m')--> "name"!, (json_map m')--> "typeDescriptions"? --> "typeString"!)]
    | _ => nil
    end
end.