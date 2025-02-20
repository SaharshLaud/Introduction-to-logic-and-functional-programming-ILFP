(* ILFP Assignment 5: Terms, Substitutions and Unifiers*)
(* Saharsh Laud 2024MCS2002*)

(* Representing symbol and signature*)
type symbol = string;;
type signature = (symbol * int) list;;

(* Tree data type*)
type tree = V of string | C of { node: symbol ; children: tree list };;

(* Helper function*)
let rec member x s = match s with
    [] -> false
  | y::ys -> if x = y then true else member x ys
;;


(* 1. Checking signature validity*)
let check_sig sig_list =
  let symb_check s =
    let rec dupli_check lst = match lst with
        [] -> false
      | x::xs -> member x xs || dupli_check xs
    in
    not (dupli_check s)
  in
  let ar_check ar =
    List.fold_left (fun bag arity -> bag && arity >= 0) true ar
  in
  let symbols = List.map fst sig_list in
  let arities = List.map snd sig_list in
  symb_check symbols && ar_check arities
;;
(* Testing check_sig function*)
let sig1 = [("f", 2); ("g", 1); ("h", 0)];;  (* Valid signature*)
let result1 = check_sig sig1;;
let sig2 = [("f", 2); ("g", 1); ("f", 0)];;  (* InValid signature - Duplicates*)
let result2 = check_sig sig2;;
let sig3 = [("f", 2); ("g", -1); ("h", 0)];; (* Valid signature - Negative arity*)
let result3 = check_sig sig3;; 
let sig4 = [];;                              (* Valid signature*)
let result4 = check_sig sig4;;   

(* 2. Checking well-formed tree.*)
let rec wftree sig_list t =
  if check_sig sig_list then  
    match t with
      V var -> true
    | C {node; children} ->
        member (node, List.length children) sig_list
        && List.fold_left (fun bag child -> bag && wftree sig_list child) true children
  else
    false  (* Invalid signature*)
;;
(* Testing wftree function*)
let t1 = C { node = "f"; children = [V "x"; C {node = "g"; children = [V "y"]}] };;
let t2 = C { node = "f"; children = [V "x"] };;
let t3 = C { node = "h"; children = [] };;
let sig1 = [("f", 2); ("g", 1); ("h", 0)];;
let sig2 = [("f", 2); ("g", 1); ("f", 0)];;
let wf1 = wftree sig1 t1;;  (* t1 is well-formed tree as per signature sig1*)
let wf2 = wftree sig1 t2;;  (* t1 is well-formed tree as per signature sig1 as wrong arity for f*)
let wf3 = wftree sig1 t3;;  (* t3 is well-formed tree as per signature sig1*)
let wf4 = wftree sig2 t1;;  (* check_sig InValid signature due to duplicates*)

(* 3. Finding Height, size and number of variables in tree.*)
(* ht function: returns the height of the tree starting from 0*)
let rec ht t = match t with
    V _ -> 0
  | C {node = _; children} ->
      if children = [] then 0
      else 1 + List.fold_left max 0 (List.map ht children)
;;

(* size function: returns the size of the tree*)
let rec size t = match t with 
    V _ -> 1
  | C {node = _; children} ->
      1 + List.fold_left (+) 0 (List.map size children)
;;

(* vars function: returns the set of variables in the tree*)
let rec vars t = match t with
    V var -> [var]
  | C {node = _; children} ->
      List.fold_left (fun bag child -> bag @ vars child) [] children
;; 
(* Testing the functions*)
let t1 = C { node = "f"; children = [V "x"; C {node = "g"; children = [V "y"]}] };;
let t2 = C { node = "f"; children = [V "x"] };;
let t3 = C { node = "h"; children = [] };;
let height1 = ht t1;; 
let height2 = ht t2;; 
let height3 = ht t3;; 
let size1 = size t1;; 
let size2 = size t2;; 
let size3 = size t3;; 
let vars1 = vars t1;; 
let vars2 = vars t2;; 
let vars3 = vars t3;; 

(* 4. Finding Mirror image of tree t.*)
let rec mirror t = match t with 
    V var -> V var
  | C {node; children} ->
      C {node; children = List.rev (List.map mirror children)}
;; 
(* Testing mirror function*)
let t1 = C { node = "f"; children = [V "x"; C {node = "g"; children = [V "y"]}] };;
let t2 = C { node = "f"; children = [V "x"] };;
let t3 = C { node = "h"; children = [] };;
let mirror1 = mirror t1;;
let mirror2 = mirror t2;;
let mirror3 = mirror t3;;

(* 5. Representation for substitutions as a table.*)
type substitution = (string * tree) list;;

let valid_subst s =
  let rec has_dupli lst = match lst with
      [] -> false
    | x::xs -> member x xs || has_dupli xs
  in
  let vars = List.map fst s in
  not (has_dupli vars)
;;   
(* Testing valid_subst function*)
let sub1 = [("x", V "y"); ("y", C {node = "f"; children = []})];;
let result1 = valid_subst sub1;;
let sub2 = [("x", V "y"); ("x", C {node = "g"; children = []})];;
let result2 = valid_subst sub2;;

(* 6. Applying substitution s to a tree t.*)
(* Helper function to find a substitution for a variable*)
let rec find_subst var s = match s with
    [] -> V var 
  | (v, t)::rest -> if v = var then t else find_subst var rest
;;

(* Apply substitution to a tree*)
exception INVALID_SUBSTITUTION;;

let rec subst t s =
  if not (valid_subst s) then
    raise INVALID_SUBSTITUTION
  else
    match t with
      V var -> find_subst var s  (* Replace variable using helper function*)
    | C {node; children} ->
        C {node; children = List.map (fun child -> subst child s) children}  (* Apply recursively to children*)
;;

(* Testing subst function*)
let subst1 = [("x", V "y"); ("y", C { node = "f"; children = [] })] ;;
let t1 = C { node = "g"; children = [V "x"; C { node = "h"; children = [V "y"] }] };; 
let result = subst t1 subst1 ;;
let sub2 = [("x", V "y"); ("x", C {node = "f"; children = []})];;
let t2 = C {node = "g"; children = [V "x"; V "z"]};;
let result2 = subst t2 sub2;;  

(* 7. Finding Composition of substitutions*)
(* Helper function to check if a variable occurs in a term*)
let rec occurs x term = match term with
    V y -> x = y
  | C {node; children} -> List.exists (occurs x) children
;;

(* Function to compose two substitutions*)
let compose s1 s2 =
  let rec merge s1 s2 acc = match (s1, s2) with
      ([], []) -> List.rev acc
    | ([], l) -> List.rev acc @ l
    | (l, []) -> List.rev acc @ l
    | ((v1, t1) :: rest1, (v2, t2) :: rest2) ->
        if occurs v2 t1 then
          merge rest1 rest2 ((v1, subst t1 [(v2, t2)]) :: acc)
        else
          merge rest1 rest2 ((v1, t1) :: acc)
  in
  merge s1 s2 [];;
(* Testing compose function*) 
let subst1 = [("x", V "y"); ("y", C {node = "f"; children = []})];;
let subst2 = [("y", V "z"); ("z", C {node = "g"; children = []})];; 
let test1 = compose subst1 subst2;; 
let test2 = compose subst2 subst1;;

(* 8. MGU function to unify two trees*)
exception NOT_UNIFIABLE;;

let mgu t1 t2 = 
  let rec unify_pairs s = match s with
      [] -> []
    | (a, b) :: rest ->
        let current_uni = unify_pair (a, b) in 
        let rest_uni = unify_pairs rest in
        current_uni @ rest_uni

  and unify_pair (l, r) = match (l, r) with
      (* Case 1: Both are variables*)
      (V v1, V v2) -> 
        if v1 = v2 then [] 
        else [(v1, r)]
      
      (* Case 2: One side is a variable, the other a constant*)
    | (V v, t) | (t, V v) ->
        if occurs v t then raise NOT_UNIFIABLE
        else [(v, t)]
             
      (* Case 3: Both terms are constants with the same name and lists of children that need to be unified*) 
    | (C { node = f1; children = l1 }, C { node = f2; children = l2 }) ->
        if (f1 <> f2) || (List.length l1 <> List.length l2) then
          raise NOT_UNIFIABLE
        else
          unify_pairs (List.combine l1 l2)
  in 
  unify_pair (t1, t2);;
(* Testing mgu function*)
(* 8 Test cases for mgu*)
(* Test case 1: Simple unification between variable and constant*) 
let test1 =
  let t1 = V "x" in
  let t2 = C {node = "a"; children = []} in
  mgu t1 t2  
;; 


(* Test Case 2: Conflict in variable assignments, expecting a valid unifier*)
let test2 =
  let t1 = C { node = "f"; children = [V "x"; V "y"] } in
  let t2 = C { node = "f"; children = [C { node = "a"; children = [] }; V "y"] } in
  mgu t1 t2 
;; 


(* Test Case 3: Mismatched function symbols, expecting NOT_UNIFIABLE exception*)
let test3() =
  let t1 = C { node = "f"; children = [V "x"] } in
  let t2 = C { node = "g"; children = [V "y"] } in
  mgu t1 t2  
;; 


(* Test Case 4: Unifying nested terms with variables*)
let test4 =
  let t1 = C { node = "f"; children = [V "x"; C { node = "g"; children = [V "y"] }] } in
  let t2 = C { node = "f"; children = [C { node = "a"; children = [] }; C { node = "g"; children = [V "z"] }] } in
  mgu t1 t2
;; 


(* Test Case 5: Unifying a variable with a nested structure*)
let test5 =
  let t1 = V "x" in
  let t2 = C { node = "f"; children = [V "y"; C { node = "g"; children = [] }] } in
  mgu t1 t2
;; 

(* Test Case 6: Unifying a variable with an empty tree*)
let test6 =
  let t1 = V "x" in
  let t2 = C { node = "f"; children = [] } in
  mgu t1 t2  
;;


(* Test Case 7: Unifying two trees with incompatible children*)
let test7 =
  let t1 = C { node = "f"; children = [C { node = "a"; children = [] }; C { node = "g"; children = [] }] } in
  let t2 = C { node = "f"; children = [C { node = "h"; children = [] }; V "y"] } in
  mgu t1 t2
;; 


(* Test Case 8: Unifying terms with multiple variables*)
let test8 =
  let t1 = C { node = "h"; children = [V "x"; V "y"] } in
  let t2 = C { node = "h"; children = [C { node = "a"; children = [] }; V "z"] } in
  mgu t1 t2 
;; 


(* 9. Check if  mgu (t, u) = mgu (mirror u, mirror t).*) 
let all_exists list1 list2 =
  List.for_all (fun x -> List.exists (fun y -> x = y) list2) list1

let mgu_check =
  let t = C { node = "f"; children = [V "x"; C { node = "g"; children = [] }] } in
  let u = C { node = "f"; children = [C { node = "h"; children = [] }; V "y"] } in
  let mgu1 = mgu t u in
  let mgu2 = mgu (mirror u) (mirror t) in
  (* Check if both lists are equal regardless of order*)
  all_exists mgu1 mgu2 && all_exists mgu2 mgu1
;;
mgu_check;; 