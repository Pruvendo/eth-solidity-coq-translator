Require Import UtilityFunctions.
Require Import Coq.Lists.List.
Require Import String.
Require Import Coq.Bool.Bool.

Require Import Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.Numbers.NatInt.NZLog.
Require Import Coq.Numbers.NatInt.NZPow.

Open Scope string_scope.
Import ListNotations.
Local Open Scope json_scope.
Delimit Scope json_scope with json.

 
Fixpoint up_to_root{X} (leafs: list X)(start_marker:bool)(acc:list bool):list (bool) := 
match leafs with 
| nil => acc 
| cons head tail => up_to_root tail (not start_marker) (cons start_marker acc)
end
.

(* Compute up_to_root (range 10) true nil. *)

Inductive Tree (A : Type) : Type :=
| Tree_Leaf : A -> Tree A 
| Tree_Wrapper : Tree A -> Tree A 
| Tree_Node : Tree A -> Tree A -> Tree A.
Arguments Tree_Leaf {_} el.
Arguments Tree_Node {_} t1 t2.
Arguments Tree_Wrapper {_} t1.

Fixpoint treelist_to_treelist{A}(list_tree: list (Tree A))(acc:list (Tree A)): list (Tree A) := 
match list_tree with 
| nil => acc
| head :: nil => cons (Tree_Wrapper head) acc
| head1:: head2:: nil => cons (Tree_Node head1 head2)  acc 
| head1::head2::tail => treelist_to_treelist(tail)(cons (Tree_Node head1 head2)  acc)
end  
. 
(* ((log2 n) + (if Nat.eqb (2 ^ log2 n) n then 0 else 1 )) *)

Fixpoint treelist_to_tree{A} (level:nat)(list_tree: list (Tree A)): option (Tree A) :=
let upper_list := treelist_to_treelist list_tree nil in
match level with 
| O => head upper_list
| S n' => treelist_to_tree n' upper_list
end
.

(* Definition x :=  (range 10). *)
(* Definition list_tree_x := map (fun x => Tree_Leaf ("_x")) x. *)

(* Definition tree_x := treelist_to_tree (List.length list_tree_x) list_tree_x. *)

Fixpoint print_each_treeleaves(prefix_handler: string -> string -> string)(prefix:string)(tree: Tree string):string:=
match tree with 
| Tree_Leaf item => (prefix_handler item prefix)
| Tree_Wrapper item => print_each_treeleaves prefix_handler (prefix) item
| Tree_Node l r => 
  (print_each_treeleaves prefix_handler (prefix++"0") l) ++ 
  (print_each_treeleaves prefix_handler (prefix++"1") r)
end
.

Fixpoint print_each_pathleaves(last:string) (prefix:list string)(tree: Tree string):list ((list string)*string):=
match tree with 
| Tree_Leaf item => [((rev' (last::prefix)), item)]
| Tree_Wrapper item => print_each_pathleaves last (prefix) item
| Tree_Node l r => 
  app (print_each_pathleaves (last++"0")(last :: prefix) l)
  (print_each_pathleaves (last++"1")(last :: prefix) r)
end
.

Fixpoint list_connections (prefix:string)(tree: Tree string): list (string*(string*string)):=
  match tree with 
| Tree_Leaf item => 
  (* \n(prefix ++ item) *)
  nil
| Tree_Wrapper t => 
  (*(prefix, prefix ++ "_") ::*) (list_connections (prefix) t)
| Tree_Node l r => 
  (prefix, (prefix ++ "0",prefix ++ "1")) ::
  (app (list_connections (prefix++"0") l) 
  (list_connections (prefix++"1") r))
  end 
.

(* Compute match tree_x with None => "" | Some tree_x => print_each_treeleaves (fun x y  => \n""++ y ++ x)"" tree_x end. *)

Definition sample_LocalState_types := map (xtype true)
  [
    "uint256"; 
    "uint128"; 
    "(mapping int uint256)";
    "(mapping int uint)";
    "TvmSlice";
    "TvmBuilder";
    "TvmCell";
    "address";
    "(mapping address uint)";
    "(mapping TvmBuilder uint)";
    "(mapping uint uint)"
    ]
.


Definition LocalFields_sample (type:string)(bin_num_str:string) := 
\n"Inductive  LocalFields"++bin_num_str++"I := | ι"++bin_num_str++"0 | ι"++bin_num_str++"1 .
Definition LocalState"++bin_num_str++"L := [( XHMap (string*nat) ("++type++")) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState"++bin_num_str++"L LocalFields"++bin_num_str++"I . 
Opaque     LocalState"++bin_num_str++"LRecord .".

Definition LocalFields_connection (from:string)(to1:string) (to2:string) := 
\n"
Inductive  LocalFields"++from++"I := | ι"++to1++" | ι"++to2++" . 
Definition LocalState"++from++"L := [ LocalState"++to1++"LRecord ; LocalState"++to2++"LRecord ] . 
GlobalGeneratePruvendoRecord LocalState"++from++"L LocalFields"++from++"I . 
Opaque     LocalState"++from++"LRecord . "  
.
Definition from_to1_to2 (from:string)(to1:string) (to2:string) := 
  "LocalState"++from ++ "LRecord " ++ 
  "LocalState"++to1 ++ "LRecord " ++  
  "LocalState"++to2 ++ "LRecord ".

Definition Instance_template(path:list string)(type:string) :=
  let ident := last path "" in
  let string_path := String.concat "" 
    (
      map 
      (
        fun way =>
        if way =? ""
        then ""
        else (\n"eapply TransEmbedded. eapply (_ ι"++way++"). ")
      )
      path
    ) 
  in
\n"#[global, program] Instance LocalStateField"++ident++" : LocalStateField ("++type++").
Next Obligation."++
string_path ++
" 
eapply (LocalState"++ident++"LEmbeddedType ι"++ident++"1). 
Defined.
Next Obligation. "++
string_path ++
"
eapply (LocalState"++ident++"LEmbeddedType ι"++ident++"0). 
Defined.
Fail Next Obligation.
#[local]
Remove Hints LocalStateField"++ident++" : typeclass_instances. "
.
Definition LocalState_file (LocalState_types: list string) (contract_name:string):string := 
  let header := 
    \n"Require Import UrsusEnvironment.Solidity.current.Environment." ++
    \n"Require Import UrsusEnvironment.Solidity.current.LocalGenerator."++
    \n"Require Import "++contract_name++"."++
    \n"Import "++contract_name++"."
  in
  let LocalStateTree(types:list string) := 
    let leaves := map (fun type => Tree_Leaf type) types in 
    let tree := treelist_to_tree (List.length leaves) leaves in 
    tree
  in
  let list_leaves_types_string:= 
    match (LocalStateTree LocalState_types) with 
    | None => "" 
    | Some lst => 

      let list_connection := (rev' (list_connections "" lst)) in
      (print_each_treeleaves LocalFields_sample "" lst) ++
      String.concat \n"" (map (fun connection => let '(from, (to1, to2)) := connection in LocalFields_connection from to1 to2 ) list_connection) ++
      \n"Transparent "++
      String.concat \n"" (map (fun connection => let '(from, (to1, to2)) := connection in from_to1_to2 from to1 to2 ) list_connection) ++
      "." ++
      \n"Notation LocalStateField := (LocalStateField XHMap LocalStateLRecord)."++
      let list_list_path := rev' (print_each_pathleaves "" nil lst) in
      String.concat \n"" 
        (
          map 
          (
            fun item => 
              let '(path, type) := item in
              Instance_template path type
            )
          list_list_path
        )
      
    end
  in
  header ++
  list_leaves_types_string
  
.
(* Compute LocalState_file sample_LocalState_types "Elector". *)

Definition LedgerFile (handledLocalState':list (string * string)) := 
let LocalState_types := map snd handledLocalState' in
LocalState_file LocalState_types "ModuleName".
