Require Import String.
Require Import List. 
Require Import Bool. 
Require Import CoqJson.Json.
Require Import CoqJson.KeyMaps.
Require Import Ascii.
Require Import UtilityFunctions.
Require Import Notations.

Import ListNotations.
Import BoolNotations. 


Inductive Expression : Set := 
| assignment (operator: string)(left_expression right_expression: Expression)(lice: bool) : Expression
| identifier (name: string)(lice: bool) : Expression
| function_call (args: list Expression) (expression: Expression) (kind: string) (return_type:string) (lice: bool) : Expression
| function_call_options (meta_data: list (string * Expression)) (expression: Expression)(lice: bool) : Expression
| member_access (object: Expression) (member: string)(lice: bool) : Expression
| send_message (contract address function_name: string) (args: list Expression) (meta_data: list (string * Expression))
| if_then_else (cond true_body false_body : Expression)(cond_lice lice_then lice_else: bool) : Expression
| if_then (cond true_body : Expression)(cond_lice lice_then: bool) : Expression
| conditional (cond true_body false_body : Expression)(lice: bool) : Expression
| block (statements: list Expression)(lice: bool) : Expression
| tuple (components: list Expression)(lice: bool) : Expression
| type_name (name: string)(lice: bool) : Expression
| return_expression (expression: Expression) (lice:bool): Expression
| variable_declaration (names: list (string*string)) (initial_values: Expression)(lice: bool) : Expression
| foreach_loop (range_declaration: list string) (range_expression body: Expression)(lice: bool) : Expression
| for_loop (condition initialization_expression loop_expression body: Expression)(lice: bool) : Expression
| literal (value kind subdenomination: string)(lice: bool) : Expression
| index_access (object index_expr: Expression)(lice: bool) : Expression
| unary_operation (operator: string) (is_prefix: bool) (sub_expression: Expression)(lice: bool) : Expression
| binary_operation (operator: string) (left_expression right_expression: Expression)(lice: bool) : Expression
| do_while (condition body: Expression)(lice: bool) : Expression
| while_loop (condition body: Expression)(lice: bool) : Expression
| repeat_loop (condition body: Expression)(lice: bool) : Expression
| break(lice: bool) : Expression
| empty_expression: Expression
.


Fixpoint ast_to_expression (lice_identifiers: list string) (ast: json): (Expression * bool) :=
match ast with 
| json_map m => 
    match (ast --> "nodeType"!) with
    | "ExpressionStatement" => 
        let fix iter (m: key_map): Expression * bool := 
            match m with 
            | empty => (empty_expression, false)
            | mapkv "expression" v m' =>
                ast_to_expression lice_identifiers v
            | mapkv _ _ m' =>
                iter m'
            end 
        in
        iter m

    | "Conditional" =>
        let fix iter (m:key_map) (cond false_expression: (Expression * bool)): (Expression * bool) :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "condition" v m' => 
                iter m' (ast_to_expression lice_identifiers v) false_expression
            | mapkv "falseExpression" v m' => 
                iter m' cond (ast_to_expression lice_identifiers v)
            | mapkv "trueExpression" v m' =>
                let (true_expr, true_expr_lice) := (ast_to_expression lice_identifiers v)
                in
                let (cond_expr, cond_expr_lice) := cond
                in
                let (false_expr, false_expr_lice) := false_expression
                in
                (conditional cond_expr true_expr false_expr (true_expr_lice || cond_expr_lice || false_expr_lice), (true_expr_lice || cond_expr_lice || false_expr_lice))
            | mapkv _ _ m' => iter m' cond false_expression
            end 
        in
        iter m (empty_expression, false) (empty_expression, false)

    | "Block" =>
        let fix iter (m:key_map): (Expression * bool) :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "statements" v m' => 
                match v with
                | json_list nil => (block nil false, false) 
                | json_list l => 
                    let expr_lices := (map (ast_to_expression lice_identifiers) l)
                    in
                    let expressions := map (fun expr_lice => let '(expr, lice) := expr_lice in expr) expr_lices 
                    in
                    let lice_block := map (fun expr_lice => let '(expr, lice) := expr_lice in lice) expr_lices 
                    in
                    let lice := (fold_left (fun acc el => acc || el) lice_block false)
                    in
                    (* for replacing (block [block...block]) cases to block [not_block...not_block] case*)
                    let reduced_by_block_expressions := 
                        fold_left
                        (
                            fun acc el =>
                                let old_expressions := acc 
                                in
                                let expression := el 
                                in
                                match expression with 
                                | block expressions lice => app old_expressions expressions
                                | empty_expression => old_expressions
                                | _ => app old_expressions [expression]
                                end
                        )
                        nil
                        expressions
                    in
                    (block reduced_by_block_expressions lice, lice)
                | _ => (block nil false, false) 
                end
            | mapkv _ _ m' => 
                iter m'
            end
        in
        iter m
    
    | "TupleExpression" =>
        let fix iter (m:key_map): (Expression * bool) :=
            match m with 
            | empty => (empty_expression, false) 
            | mapkv "components" v m' =>  
                match v with
                | json_list nil => (empty_expression, false)  
                | json_list l => 
                    let components_lices := (map (ast_to_expression lice_identifiers) l)
                    in
                    let components := map (fun component_lice => let '(component, lice) := component_lice in component) components_lices
                    in
                    let lices := map (fun component_lice => let '(component, lice) := component_lice in lice) components_lices
                    in
                    let lice := (fold_left (fun acc el => acc || el) lices false)
                    in
                    (tuple components lice, lice)
                | _ => (empty_expression, false) 
                end
            | mapkv _ _ m' => 
                iter m'
            end 
        in
        iter m

    | "FunctionCallOptions" =>
        let fix iter m (expression: Expression * bool) (names: list string): (Expression * bool)  := 
            match m with 
            | empty => (empty_expression, false) 
            | mapkv "expression" v m' => 
                let names :=  
                    match ((json_map m')--> "names"?) with 
                    | json_list l => map (fun data_name => match data_name with json_data name => name | _ => "_" end ) l
                    | _  => nil
                    end 
                in 
                iter m' (ast_to_expression lice_identifiers v) names
            | mapkv "options" v m' => 
                let options_lices := 
                    match v with 
                    | json_list l => map (ast_to_expression lice_identifiers) l
                    | _ => nil
                    end
                in
                let options := map (fun opt_lice => let '(opt, lice):= opt_lice in opt) options_lices
                in
                let lices := map (fun opt_lice => let '(opt, lice):= opt_lice in lice) options_lices 
                in
                let '(expression, expr_lice) := expression
                in
                let lice := (fold_left (fun acc el => acc || el) lices false) 
                in
                let names_and_options : list (string * (Expression)) := combine names options 
                in
                (function_call_options names_and_options expression (expr_lice||lice), (expr_lice||lice))
            | mapkv _ _ m' => iter m' expression names 
            end
        in
        iter m (empty_expression, false) nil

    | "ElementaryTypeName" =>
        let fix iter (m: key_map): (Expression * bool) :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "name" v m' => (type_name (getString' v) false, false)
            | mapkv _ _ m' => iter m'
            end 
        in
        iter m

    | "ElementaryTypeNameExpression" =>
        let fix iter (m: key_map): (Expression * bool) :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "typeName" v m' =>
                let name := (v-->"name"!) in
                (type_name name false, false)
            | mapkv _ _ m' => iter m'
            end 
        in
        iter m
    
    | "Return" =>
        let fix iter (m: key_map): (Expression*bool) :=
        match m with 
        | empty => (empty_expression, false)
        | mapkv "expression" v m' => 
            let returned_object_lice := (ast_to_expression lice_identifiers v)
            in
            let is_null := (getString' v) =? "null"
            in
            let '(object, lice) := returned_object_lice 
            in
            (return_expression object (lice || is_null), (lice || is_null))
        | mapkv _ _ m' => iter m'
        end in
        iter m

    | "VariableDeclarationStatement" =>
        let fix iter (m: key_map) (declarations: list (string*string)): (Expression * bool) :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "declarations" v m' => 
                let declarations := 
                    match v with
                    | json_list list_declarations => 
                            map 
                            (
                                fun declaration => 
                                    let name := declaration --> "name"! 
                                    in
                                    let type := declaration --> "typeDescriptions"? --> "typeString"! 
                                    in
                                    (name, type)
                            ) 
                            list_declarations
                    | _ => nil
                    end 
                in
                iter m' declarations
            | mapkv "initialValue" v m' => 
                let (values, lice) := (ast_to_expression lice_identifiers v)
                in
                (variable_declaration declarations values lice, lice)
          | mapkv _ _ m' => iter m' declarations
          end 
        in
        iter m nil

    | "ForEachStatement" =>
        let fix iter (m: key_map)(body: Expression * bool)(range_declaration: list string): Expression * bool:=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "body" v m' => 
                let body := ast_to_expression lice_identifiers v
                in
                iter m' body range_declaration
            | mapkv "rangeDeclaration" v m' =>  
                let declarations := 
                    match (v --> "declarations"?) with 
                    | json_list declarations => 
                        map 
                        (fun dec => (dec --> "name"!))
                        declarations
                    | _ => nil
                    end
                in
                iter m' body declarations
            | mapkv "rangeExpression" v m' => 
                let range_expression_lice := ast_to_expression lice_identifiers v
                in
                let '(range_expression, range_lice) := range_expression_lice 
                in
                let '(body, body_lice) := body 
                in
                (foreach_loop range_declaration range_expression body (range_lice || body_lice), (range_lice || body_lice))
            | mapkv _ _ m' => iter m' body range_declaration
            end 
        in 
        iter m (empty_expression, false) nil

    | "ForStatement" =>
        let fix iter (m: key_map)(condition initializationExpression body: Expression * bool): Expression * bool :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "body" v m' => 
                iter m' condition initializationExpression (ast_to_expression lice_identifiers v)
            | mapkv "condition" v m' => 
                iter m' (ast_to_expression lice_identifiers v) initializationExpression body
            | mapkv "initializationExpression" v m' => 
                iter m' condition (ast_to_expression lice_identifiers v) body
            | mapkv "loopExpression" v m' => 
                let '(loop, loop_lice) := ast_to_expression lice_identifiers v
                in 
                let '(initializationExpression, init_lice) := initializationExpression 
                in
                let '(body, body_loop) := body
                in
                let '(condition, condition_lice) := condition 
                in
                let lice := (body_loop || init_lice || loop_lice || condition_lice)
                in
                (for_loop condition initializationExpression loop body lice, lice)
                
            | mapkv _ _ m' => iter m' condition initializationExpression body
            end 
        in
        iter m (empty_expression, false) (empty_expression, false) (empty_expression, false)

    | "Break" => (break true, true)
    | "Literal" =>
        
        let kind := ((json_map m)--> "kind"!) in
        let subdenomination := ((json_map m) --> "subdenomination"!) in
        match kind with 
        | "string" => 
            let value := ((json_map m)--> "typeDescriptions"? --> "typeIdentifier"!) in
            (literal value kind subdenomination false, false)
        | _ => 
            let value := ((json_map m)--> "value"!) in
            (literal value kind subdenomination false, false)
        end
    | "IndexAccess" =>
        let fix iter (m: key_map) (base: Expression * bool): (Expression * bool) :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "baseExpression" v m' => 
                let base := ast_to_expression lice_identifiers v 
                in
                iter m' base
            | mapkv "indexExpression" v m' => 
                let '(index_expression, index_lice) := ast_to_expression lice_identifiers v
                in
                let '(base, base_lice) := base
                in
                let lice := base_lice || index_lice
                in
                (index_access base index_expression lice, lice)
            | mapkv _ _ m' => iter m' base
            end 
        in
        iter m (empty_expression, false)
    
    | "MemberAccess" =>
        let fix iter m : (Expression * bool) :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "expression" v m' =>  
                let '(object, object_lice) := ast_to_expression lice_identifiers v in 
                
                let type_of_object := 
                    (* "struct CrowdFund.Campaign memory" *)
                    let type := v --> "typeDescriptions"? --> "typeString"!
                    in
                    let type_id := v --> "typeDescriptions"? --> "typeIdentifier"!
                    in
                    (* "struct;CrowdFund.Campaign;memory" *)
                    let splitted_type := split_string type " "
                    in
                    if (String.eqb (hd "" splitted_type) "struct") && (prefix "t_struct$" type_id)
                    then 
                        (* "CrowdFund.Campaign" *)
                        let full_struct_type := hd "" (tl (splitted_type))
                        in
                        let splitted_struct_type := split_string full_struct_type "."
                        in
                        let struct_type := last splitted_struct_type ""
                        in
                        if String.eqb struct_type ""
                        then ""
                        else (struct_type ++ "_ι_")
                    else ""
                in
                let member_name := type_of_object ++ ((json_map m') --> "memberName"!) in                
                let lice := 
                    let is_func := isInStr "function" (((json_map m') --> "typeDescriptions"?) --> "typeString"!)
                    in
                    if is_func
                    then isInList member_name lice_identifiers
                    else false
                in
                (member_access object member_name (lice || object_lice), (lice || object_lice))
            | mapkv _ _ m' => iter m'
            end 
        in
        iter m

    | "FunctionCall" =>
        let fix iter (m:key_map) (args: list (Expression * bool))(kind: string): Expression * bool :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "arguments" v m' =>
                let kind := ((json_map m') --> "kind"!) in
                let args := 
                    match v with 
                    | json_list l =>
                        map (ast_to_expression lice_identifiers) l
                    | _ => nil
                    end
                in
                iter m' args kind
            | mapkv "expression" v m' =>
                let args_lices := args in
                let args := map (fun arg_lice => let '(arg, lice):= arg_lice in arg) args_lices
                in
                let lices := map (fun arg_lice => let '(arg, lice):= arg_lice in lice) args_lices
                in
                let lice := (fold_left (fun acc el => acc || el) lices false) 
                in
                let '(expr, lice_expr) := (ast_to_expression lice_identifiers v)
                in
                let type := 
                    (json_map m') --> "typeDescriptions"? --> "typeString"!
                in
                let is_send_operation := 
                    let type := (v --> "expression"? --> "typeDescriptions"? --> "typeString"!)
                    in
                    (isInStr "interface" type) || (isInStr "contract" type)
                in
                if is_send_operation
                then
                    let contract := replaceWith [("interface",""); ("contract", ""); (" ", "")] (v --> "expression"? --> "typeDescriptions"? --> "typeString"!)
                    in
                    let address := (v --> "expression"? --> "name"!)
                    in
                    let function_name := (v --> "memberName"!)
                    in
                    let args := args 
                    in
                    let meta_data := 
                        (* {InternalMessageParamsLRecord} *)
                        [("flag", (literal "0" "int" "" false))]
                    in
                    (send_message contract address function_name args meta_data, lice)
                else
                    (function_call args expr kind type (lice || lice_expr), (lice || lice_expr))
            | mapkv _ _ m' => iter m' args kind
            end 
        in
        iter m nil EmptyString

        | "IfStatement" => 
            let fix iter (m: key_map)(condition false_body: Expression * bool) : Expression * bool :=
                match m with 
                | empty => (empty_expression, false)
                | mapkv "condition" v m' => 
                    let condition := ast_to_expression lice_identifiers v
                    in
                    (iter m' condition false_body)
                | mapkv "falseBody" v m' =>  
                    let false_body := 
                        if getString' v =? "null" 
                        then (empty_expression, false)
                        else ast_to_expression lice_identifiers v
                    in 
                    (iter m' condition false_body) 
                | mapkv "trueBody" v m' =>  
                    let is_false_body_empty := match false_body:(Expression * bool) with | pair empty_expression lice => true | _=> false end in
                    let '(true_body, lice_then) := ast_to_expression lice_identifiers v in
                    let '(false_body, lice_else) := false_body in
                    let '(condition, cond_lice) := condition
                    in
                    if is_false_body_empty
                    then (if_then condition true_body cond_lice lice_then, cond_lice || lice_then || lice_else)
                    else (if_then_else condition true_body false_body cond_lice lice_then lice_else, cond_lice || lice_then)
                | mapkv _ _ m' => (iter m' condition false_body)
                end 
            in
            iter m (empty_expression,false) (empty_expression,false)

    | "Identifier" => 
        let name := (json_map m)--> "name"!
        in
        let type := (json_map m)--> "typeDescriptions"? --> "typeString"!
        in
        let lice := (isInStr "function" type) && (isInList name lice_identifiers)
        in   
        (identifier name lice, lice)

    | "UnaryOperation" => 
        let fix iter (m: key_map)(is_prefix: bool) (operator: string): (Expression * bool) :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "operator" v m' => 
                let operator := (getString' v)  in
                iter m' is_prefix operator
            | mapkv "prefix" v m' => 
                iter m' ("true" =? (getString' v)) operator
            | mapkv "subExpression" v m' => 
                let '(sub_expression, sub_expr_lice) := (ast_to_expression lice_identifiers v)
                in
                (unary_operation operator is_prefix sub_expression sub_expr_lice, sub_expr_lice)
            | mapkv _ _ m' => iter m' is_prefix operator
        end in
        iter m false ""
    | "BinaryOperation" => 
        let fix iter m  (operator :string)(left_expression: Expression * bool): (Expression * bool) :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "leftExpression" v m' =>  
                let left_expression := ast_to_expression lice_identifiers  v 
                in 
                let operator := (json_map m)--> "operator"! 
                in
                (iter m' operator left_expression)                                
            | mapkv "rightExpression" v m' => 
                let '(rightExpression, right_lice) := ast_to_expression lice_identifiers v 
                in
                let '(left_expression, left_lice) := left_expression 
                in
                (binary_operation operator left_expression rightExpression (left_lice || right_lice), (left_lice || right_lice))
            | mapkv _ _ m' => iter m' operator left_expression
            end 
        in
        iter m "" (empty_expression, false)

    | "Assignment" => 
        let fix iter (m: key_map)(operator: string)(left_expression: Expression * bool) : (Expression * bool) :=
        match m with 
        | empty => (empty_expression, false)
        | mapkv "leftHandSide" v m' =>  
            let operator := (json_map m)--> "operator"! in
            let left_expression := ast_to_expression lice_identifiers v in
            (iter m' operator left_expression)
        | mapkv "rightHandSide" v m' => 
            let '(right_expression, right_lice) := (ast_to_expression lice_identifiers v)
            in
            let '(left_expression, left_lice) := left_expression
            in
            (assignment operator left_expression right_expression (left_lice || right_lice), (left_lice || right_lice))
        | mapkv _ _ m' => iter m' operator left_expression
        end in
        iter m "" (empty_expression, false)
    | "DoWhileStatement" => 
        let fix iter (m: key_map) (body:(Expression * bool)): (Expression * bool) :=
            match m with 
            | empty => (empty_expression, false)
            | mapkv "body" v m' => 
                let body := ast_to_expression lice_identifiers v
                in
                iter m' body
            | mapkv "condition" v m' => 
                let '(condition, cond_lice) := ast_to_expression lice_identifiers v
                in
                let '(body, body_lice) := body
                in
                (do_while condition body (cond_lice || body_lice), (cond_lice || body_lice))
            | mapkv _ _ m' => iter m' body
            end 
        in
        iter m (empty_expression, false)
    
    | "RepeatStatement" =>
        let fix iter (m: key_map) (body:(Expression * bool)): (Expression * bool) :=
        match m with 
        | empty => (empty_expression, false)
        | mapkv "body" v m' => 
            let body := ast_to_expression lice_identifiers v
            in
            iter m' body
        | mapkv "condition" v m' => 
            let '(condition, cond_lice) := ast_to_expression lice_identifiers v
            in
            let '(body, body_lice) := body 
            in
            (repeat_loop condition body (cond_lice || body_lice), (cond_lice || body_lice))
        | mapkv _ _ m' => iter m' body
        end 
        in
        iter m (empty_expression, false)
        | "WhileStatement" => 
        let fix iter (m: key_map) (body:(Expression * bool)): (Expression * bool) :=
        match m with 
        | empty => (empty_expression, false)
        | mapkv "body" v m' => 
            let body := ast_to_expression lice_identifiers v
            in
            iter m' body
        | mapkv "condition" v m' => 
            let '(condition, cond_lice) := ast_to_expression lice_identifiers v
            in
            let '(body, body_lice) := body 
            in
            (while_loop condition body (cond_lice || body_lice), (cond_lice || body_lice))
        | mapkv _ _ m' => iter m' body
        end 
        in
        iter m (empty_expression, false)
    | "PlaceholderStatement" => (empty_expression, false)
    | _ => (empty_expression, false)
    end
| _ => (empty_expression, false)
end.

Definition key_word_wrapper (identifier:string):string := 
match identifier with 
| String "_"%char _ => "{" ++ identifier ++ "}"
| "id" => "{id}"
| "value" => "{value}"
| "f1" => "{f1}"
| "f2" => "{f2}"
| "condition" => "{condition}"
| "require" => "require_"
| "revert" => "revert_"
(* | "_duration" => "{_duration}" *)
| _ => identifier
end
.

Definition state := bool (* refine *) * string (* indent *) * bool (* is_last *) * string (* return_param *).
Fixpoint print_expression (expression: Expression) (s:state): string := 
let '(refine, indent, is_last, return_param_name) := s in
match expression with 
| assignment operator left_expression right_expression lice =>
    (if refine then (\n""++indent++":://  ") else "") ++ 
    (print_expression left_expression (false, indent, false, return_param_name)) ++ 
    (
        match operator with 
        | "=" => ":="
        | _ => operator
        end
    ) ++ 
    (print_expression right_expression (false, indent, false, return_param_name)) ++
    (if refine then (if is_last then " |" else "")++"." else "")
| identifier name lice =>
    key_word_wrapper name
| function_call args expression kind type lice =>
    let list_printed_args := 
        (String.concat ", " (map (fun arg => print_expression arg (false, indent, false, return_param_name)) args))
    in
    let expression_string := (print_expression expression (false, indent, false, return_param_name))
    in
    (if refine then (\n""++indent++":://  ") else "") ++ 
    (match kind with 
    | "structConstructorCall" => 
        "["++
        list_printed_args ++
        "]"
    | "typeConversion" =>
        (if (isInStr "contract" type) && (not (isInStr "int" type))
        then ""
        else expression_string) ++
        "("++
        list_printed_args ++
        ")"

    | _ =>
        expression_string ++ 
        "(" ++ list_printed_args ++ ")"
    end) ++
    (if refine then (if is_last then " |" else "")++"." else "") 
| function_call_options meta_data expression lice => 
    (if refine then (\n""++indent++":://  ") else "") ++ 
    print_expression expression (false, indent, false, return_param_name) ++
    "(* {" ++ 
    (String.concat (", "++\n"") (map (fun data => let '(name, data) := data in name ++ " : "++ print_expression data (false, indent, false, return_param_name)) meta_data)) ++ 
    "} *)" ++
    (if refine then (if is_last then " |" else "")++"." else "")
| member_access object member lice => 
    (if refine then (\n""++indent++":://  ") else "") ++ 
    print_expression object (false, indent, false, return_param_name) ++
    "->" ++
    member ++
    (if refine then (if is_last then " |" else "")++"." else "")
| send_message contract address function_name args meta_data => 
    (if refine then (\n""++indent++":://  ") else "") ++ 
    "send " ++ contract ++ "." ++ function_name ++
    "(" ++ 
    (String.concat", " (map (fun arg => print_expression arg (false, indent, false, return_param_name)) args)) ++
    ") => "++address++" with {InternalMessageParamsLRecord} [$ " ++
    (String.concat 
    "; " 
    (
        map 
        (
            fun data => let '(name, expr):= data 
            in 
            print_expression expr (false, indent, false, return_param_name) ++ "⇒" ++ "{Message_ι_" ++name++"}" 
        ) 
        meta_data
    )) ++ "$]" ++
    (if refine then (if is_last then " |" else "") ++ "." else "")
| if_then_else cond true_body false_body cond_lice lice_then lice_else =>
    (if refine then (\n""++indent++":://  ") else "") ++ 
    "if (" ++ print_expression cond (false, indent, false, return_param_name) ++ ") then { {_:UExpression _ "++(if lice_then then "true" else "false")++" } } else { {_:UExpression _ "++(if lice_else then "true" else "false")++"} } " ++
    (if refine then (if is_last then " |" else "")++"." else "")++
    print_expression true_body (true, indent, false, return_param_name) ++
    print_expression false_body (true, indent, false, return_param_name)
| if_then cond true_body cond_lice lice_then =>
    (if refine then (\n""++indent++":://  ") else "") ++ 
    "if (" ++ (print_expression cond (false, indent, false, return_param_name)) ++ ") then { { _ : UExpression _ "++(if lice_then then "true" else "false")++"} } " ++
    (if refine then (if is_last then " |" else "")++"." else "") ++
    print_expression true_body (true, indent, false, return_param_name)
| conditional cond true_body false_body lice => 
    (* (if refine then (\n""++indent++":://  ") else "") ++  *)
    print_expression cond (false, indent, false, return_param_name) ++ 
    " ? " ++
    print_expression true_body (false, indent, false, return_param_name) ++ 
    " : " ++
    print_expression false_body (false, indent, false, return_param_name) 
    (* ++  *)
    (* (if refine then "." else "") *)
| block statements lice => 
    let fix reduce (list_statements: list Expression): string := 
        match list_statements with 
        | statement :: nil => 
            print_expression statement (true, indent++"    ", true, return_param_name)
        | statement :: rest_statements => 
            (print_expression statement (true, indent++"    ", false, return_param_name)) ++ 
            (reduce rest_statements)
        | nil => ""
        end
    in
    (* filter doesn't work here *)
    let fix filter_empty (list_statements: list Expression): list Expression := 
        match list_statements with 
        | nil => nil 
        | head :: rest => 
            match head with 
            | empty_expression => filter_empty rest
            | _ => head :: (filter_empty rest)
            end
        end
    in
    (if refine then \n""++ indent ++ "{" else "") ++
    (reduce ( (*filter_empty*) statements)) ++
    (if refine then \n""++ indent ++ "}" else "")
| tuple components lice => 
    match components with 
    | component :: nil => print_expression component (false, indent, false, return_param_name)
    | _ =>
        "[" ++
        String.concat ", " (map (fun component => print_expression component (false, indent, false, return_param_name)) components) ++
        "]"
    end
| type_name name lice => 
    name
| return_expression expression lice =>
    (if refine then (\n""++indent++":://  ") else "") ++
    (
        let return_object := print_expression expression (false, indent, false, return_param_name) 
        in
        if return_object =? ""
        then "exit_ {}"
        else (return_param_name ++ " " ++ return_object)
    ) ++ 
    (if refine then (if is_last then " |" else "")++"." else "")
| variable_declaration names initial_values lice =>
    (if refine then (\n""++indent++":://  ") else "") ++
    (
        match names with 
        | head :: nil =>
            let '(name, type) :=  head 
            in
            "var " ++ name ++ " : " ++ (xtype false type)
        | _ =>
            "var (" ++
            String.concat ", " (map (fun var => let '(name, type):= var in name ++ ":" ++ (xtype false type)) names) ++
            ")"
        end
    ) ++
    (
        let values := (print_expression initial_values (false, indent, false, return_param_name))
        in
        if (replaceWith [(" ", "")] values) =? ""
        then ""
        else (" := " ++ values)
    ) ++
    (if refine then ";_|." else "")
| foreach_loop range_declaration range_expression body lice =>
    (if refine then (\n""++indent++":://  ") else "") ++
    "for ( [" ++ String.concat ", " range_declaration ++ "] in " ++ 
    print_expression range_expression (false, indent, false, return_param_name) ++ ")" ++
    (if refine then (if is_last then " |" else "")++"." else "") ++
    print_expression body (true, indent, false, return_param_name)
| for_loop condition initialization_expression loop_expression body lice =>
    (if refine then (\n""++indent++":://  ") else "") ++
    "for (" ++ 
    (print_expression initialization_expression (false, indent, false, return_param_name)) ++ " , " ++
    (print_expression condition (false, indent, false, return_param_name)) ++ " , " ++
    (print_expression loop_expression (false, indent, false, return_param_name)) ++
    ") do { {_:UExpression _  "++(if lice then "true" else "false")++" } }  " ++
    (if refine then (if is_last then " |" else "")++"." else "") ++
    print_expression body (true, indent, false, return_param_name)
| literal value kind subdenomination lice =>
    match kind with 
    | "string" => value
    | _ => "{"++value++ "}"
    end
| index_access object index_expr lice =>
    print_expression object (false, indent, false, return_param_name) ++ "[["++ print_expression index_expr (false, indent, false, return_param_name) ++"]]"
| unary_operation operator is_prefix sub_expression lice => 
    let sub_expression_string := print_expression sub_expression (false, indent, false, return_param_name) 
    in
    (if refine then (\n""++indent++":://  ") else "") ++
    "(" ++ 
    (
        if is_prefix 
        then operator ++ " "++ sub_expression_string 
        else sub_expression_string ++ " " ++ operator
    ) ++
    ")" ++
    (if refine then (if is_last then " |" else "") ++ "." else "")
| binary_operation operator left_expression right_expression lice =>
    "(" ++
    print_expression left_expression (false, indent, false, return_param_name) ++ " " ++
    operator ++ " " ++
    print_expression right_expression (false, indent, false, return_param_name) ++ 
    ")"

| do_while condition body lice =>
    (if refine then (\n""++indent++":://  ") else "") ++
    "do while (" ++ print_expression condition (false, indent, false, return_param_name) ++ ") { {_:UExpression _  "++(if lice then "true" else "false")++"} }"++
    (if refine then (if is_last then " |" else "")++"." else "") ++
    print_expression body (true, indent, false, return_param_name)
    
| while_loop condition body lice =>
    (if refine then (\n""++indent++":://  ") else "") ++
    "while (" ++ print_expression condition (false, indent, false, return_param_name) ++ ") do { {_:UExpression _  "++(if lice then "true" else "false")++"} }" ++
    (if refine then (if is_last then " |" else "")++"." else "") ++
    
    print_expression body (true, indent, false, return_param_name)
    
| repeat_loop condition body lice =>
    (if refine then (\n""++indent++":://  ") else "") ++
    "repeat (" ++ print_expression condition (false, indent, false, return_param_name) ++ ") do { {_:UExpression _  "++(if lice then "true" else "false")++"} }" ++
    (if refine then (if is_last then " |" else "")++"." else "") ++
    
    print_expression body (true, indent, false, return_param_name)
    
| break lice=> 
    (if refine then (\n""++indent++":://  ") else "") ++
    "break_ " ++
    (if refine then (if is_last then " |" else "")++"." else "")
| empty_expression => "(* empty_expression *)"
end
.
