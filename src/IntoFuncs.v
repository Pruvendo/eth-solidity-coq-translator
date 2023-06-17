Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import ListString.All.
Require Import StringHelpers.
Require Import String.
Require Import Bool.
Require Import CoqJson.Json.
Require Import CoqJson.KeyMaps.
Require Import Ascii.
Require Import UtilityFunctions.
Require Import ProgramScheme.
Import ListNotations.
Import C.Notations.
Import JsonNotations.
Local Open Scope string_scope.
Local Open Scope json_scope.
Local Open Scope type_scope.
Delimit Scope json_scope with json.

Definition FuncsFile (contract_json: json): string := 
    let sorted_list_of_functions := get_list_function_contract_json contract_json
    in
    let '(code_listing, require_true_list) := (
        fold_left
        (
            fun acc el => 
                let '(code_listing, require_true_list) := acc 
                in
                let '(  name, 
                        args, 
                        returns, 
                        modifier, 
                        visibility, 
                        (* TODO remove lice*) _, 
                        body) := el 
                in
                let '(expression_body, lice) := ast_to_expression require_true_list body 
                in
                let lice := 
                    match modifier with 
                    | nil => lice 
                    | _ => true 
                    end 
                in
                let return_name := 
                    match returns with 
                    | param :: nil => 
                        let '(name, type) := param in 
                        if name =? ""
                        then "_result"
                        else name
                    | _ => "_result" 
                    end
                in
                let return_type :=
                    let type_list :=
                        map 
                        (
                            fun param =>
                                let '(name, type) := param in 
                                type
                        )
                        returns
                    in
                    let type := 
                        match type_list with
                        | nil => "PhantomType"
                        | _ =>
                            "(" ++ (String.concat " ** " type_list) ++ ")"
                        end 
                    in
                    "UExpression " ++ type ++ " " ++ (if (lice:bool) then "true" else "false") 
                in

                let body_listing := 
                    let indent := "" 
                    in
                    print_expression expression_body (true, indent, false, (return_name ++ " :="))
                in
                let new_func_listing := 
                    let isModifier := 
                        match returns with 
                        | [("modifier", _)] => true 
                        | _ => false 
                        end
                    in
                    let is_pre := 
                        match returns with 
                        | [("modifier", "pre")] => true 
                        | _ => false 
                        end
                    in
                    let attributes := 
                        if (return_type =? "UExpression PhantomType true") || (return_type =? "UExpression PhantomType false")
                        then 
                        "#[" ++ 
                        (String.concat ", "  visibility) ++ 
                        "]"
                        else
                        "#[" ++ 
                        (String.concat ", " (app visibility [" returns=" ++ return_name])) ++ 
                        "]"
                            
                    in
                    \n""++ 
                    (attributes ++ \n"Ursus ") ++
                    "Definition " ++ name ++ " " ++
                    ( 
                        String.concat
                        " "
                        (
                            map 
                            (
                                fun arg => 
                                let '(arg_name, arg_type):= arg 
                                in 
                                "(" ++ arg_name ++ " : " ++ (xtype false arg_type) ++")"
                            )
                            args
                        )
                        ++ 
                        ": " ++ 
                        (if isModifier then "UExpression PhantomType " ++ (if (lice:bool) then "true" else "false")  
                        else return_type)  ++ "." 
                    ) ++
                    (
                        String.concat 
                        ""
                        (
                            map 
                            (
                                fun modifier =>
                                    let '(modifierName, list_json_args) := modifier 
                                    in
                                    let is_pre := true 
                                    in
                                    let modifier_call_listing := modifierName ++ 
                                    "(" ++
                                    (String.concat ", "
                                        (
                                            map 
                                            (
                                                fun arg_json =>
                                                    let '(arg_expr, lice) := ast_to_expression require_true_list arg_json 
                                                    in
                                                    print_expression arg_expr (false, "", false, (return_name ++ " :="))
                                            )
                                            list_json_args
                                        )
                                    ) ++
                                    ")"
                                    in
                                    if is_pre
                                    then \n"::// "++modifier_call_listing++" ; {_} |."
                                    else \n"::// {_} ; "++modifier_call_listing++" |."
                            ) 
                            modifier
                        )
                    ) ++
                    body_listing ++
                    (* \n"(*" ++
                    (String.concat ", " (get_list_of_func_calls body)) ++
                    "*)" ++ *)
                    \n"return." ++
                    \n"Defined." ++
                    \n"Sync."  
                in
                (code_listing ++ new_func_listing, if lice then (cons name require_true_list) else require_true_list)
        )
        sorted_list_of_functions
        ("", [  "require";
                "revert";
                "store";
                "loadUnsigned";
                "storeUnsigned";
                "decode";
                "exit";
                "get"])
    ) 
    in
    code_listing
.

