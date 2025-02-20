(* ILFP Assignment: Toy Prolog Interpreter *)
(* Saharsh Laud 2024MCS2002 *)

(* Data Types *) 
type symbol = string;;
type predicate = string;;
type variable = string;;
type constant = string;;

(* Term Type*)
type term =
    V of variable
  | C of { node: symbol; children: term list }
  | Node of predicate * (term list)
;;

type atomic_formula = Node of predicate * (term list);;

type clause =
    Fact of atomic_formula
  | Rule of atomic_formula * atomic_formula list
;;

type goal = atomic_formula list;;
type program = clause list;;

exception NOT_UNIFIABLE;;

(* Helper Functions *) 
let rec member x s = match s with
    [] -> false
  | y::ys -> if x = y then true else member x ys
;;

(* Occurs Check *)
let rec occurs x t = match t with
    V y -> x = y
  | C _ -> false
  | Node (_, terms) -> List.exists (occurs x) terms
;;

(* Substitution Functions *)
let rec find_subst var s = match s with
    [] -> V var
  | (v, t)::rest -> if v = var then t else find_subst var rest
;;

let rec subst term s = match term with
    V var -> find_subst var s
  | C { node; children } ->
      C { node; children = List.map (fun child -> subst child s) children }
  | Node (pred, terms) ->
      Node (pred, List.map (fun term -> subst term s) terms)
;;

(* Most General Unifier (MGU) *)
let rec mgu t1 t2 =
  let rec unify_pairs pairs = match pairs with
      [] -> []
    | (a, b) :: rest ->
        let s = unify_pair (a, b) in
        let s_rest = unify_pairs (List.map (fun (x, y) -> (subst x s, subst y s)) rest) in
        s @ s_rest

  and unify_pair (t1, t2) = match (t1, t2) with
      (V v1, V v2) -> if v1 = v2 then [] else [(v1, t2)]
    | (V v, term) | (term, V v) ->
        if occurs v term then raise NOT_UNIFIABLE else [(v, term)]
    | (C { node = f1; children = terms1 }, C { node = f2; children = terms2 }) ->
        if f1 = f2 && List.length terms1 = List.length terms2 then
          unify_pairs (List.combine terms1 terms2)
        else
          raise NOT_UNIFIABLE
    | (C _, Node _) | (Node _, C _) -> raise NOT_UNIFIABLE 
    | (Node (p1, terms1), Node (p2, terms2)) ->
        if p1 = p2 && List.length terms1 = List.length terms2 then
          unify_pairs (List.combine terms1 terms2)
        else
          raise NOT_UNIFIABLE
  in
  unify_pair (t1, t2)
;;

(* Composition of Substitutions *)
let compose s1 s2 =
  let app = List.map (fun (v, t) -> (v, subst t s2)) s1 in
  let filt = List.filter (fun (v, _) -> not (List.exists (fun (v', _) -> v = v') app)) s2 in
  app @ filt
;;

(* Prolog Interpreter Functions *)

(* Helper function to apply substitution to atomic_formula *)
let subst_atomic_formula af u = match af with
    Node (p, terms) -> Node (p, List.map (fun t -> subst t u) terms)
;;

(* Prolog Interpreter Functions *)
let rec resolve prog g s depth =
  if depth > 100 then [] (* recursion depth limit *)
  else match g with
      [] -> [s] (* Return solution list *)
    | curr_goal :: rest ->
        let rec try_clauses = function
            [] -> []
          | cl :: rem ->
              let solutions = match cl with
                  Fact h ->
                    (try 
                       let Node (p1, terms1) = curr_goal in
                       let Node (p2, terms2) = h in
                       if p1 = p2 then
                         let u = mgu (C { node = p1; children = terms1 }) (C { node = p2; children = terms2 }) in
                         let new_s = compose u s in
                         let new_goals = List.map (fun g -> subst_atomic_formula g u) rest in
                         resolve prog new_goals new_s (depth + 1)
                       else []
                     with NOT_UNIFIABLE -> [])
                | Rule (h, b) ->
                    (try
                       let Node (p1, terms1) = curr_goal in
                       let Node (p2, terms2) = h in
                       if p1 = p2 then
                         let u = mgu (C { node = p1; children = terms1 }) (C { node = p2; children = terms2 }) in
                         let new_s = compose u s in
                         let new_goals = List.map (fun g -> subst_atomic_formula g u) (b @ rest) in
                         resolve prog new_goals new_s (depth + 1)
                       else []
                     with NOT_UNIFIABLE -> [])
              in
              solutions @ try_clauses rem
        in
        try_clauses prog
;;

(* Main Query Function *)
let query prog g = resolve prog g [] 0;;

(* Helper functions for constructing terms and formulas *)
let fact pred args = Fact (Node (pred, args));;
let rule pred args body = Rule (Node (pred, args), body);;
let v x = V x;;
let c s = C { node = s; children = [] };;
let f n args = C { node = n; children = args };;
let pred n args = Node (n, args);;

(* Testing Function *)
let rec print_term = function
    V x -> Printf.printf "%s" x
  | C { node; children } ->
      if children = [] then Printf.printf "%s" node
      else (
        Printf.printf "%s(" node;
        let rec print_args = function
            [] -> ()
          | [t] -> print_term t
          | t :: ts -> print_term t; Printf.printf ", "; print_args ts
        in
        print_args children;
        Printf.printf ")"
      )
  | Node (pred, args) ->
      Printf.printf "%s(" pred;
      let rec print_args = function
          [] -> ()
        | [t] -> print_term t
        | t :: ts -> print_term t; Printf.printf ", "; print_args ts
      in
      print_args args;
      Printf.printf ")"
;;


let rec print_subst subst = match subst with
    [] -> ()
  | (var, term) :: rest ->
      Printf.printf "%s = " var;
      print_term term;
      Printf.printf "; ";
      print_subst rest
;;

(* Helper function to check if a query has variables *) 
let rec has_variables = function
    [] -> false
  | Node (_, terms) :: rest ->
      List.exists (function V _ -> true | _ -> false) terms || has_variables rest
;;

let get_query_variables = function
    Node (_, terms) ->
      List.fold_left (fun acc term -> match term with
            V var -> var :: acc
          | _ -> acc
        ) [] terms
;;

let filter_relevant_bindings query_vars subst = List.filter (fun (var, _) -> List.mem var query_vars) subst;;

(* Recursively resolve a term based on the substitution list *)
let rec fully_resolve term subst = match term with
    V var -> 
      (match find_subst var subst with
         V v when v = var -> term  (* No further substitution *)
       | V v -> fully_resolve (V v) subst
       | resolved_term -> fully_resolve resolved_term subst)
  | C { node; children } -> 
      C { node; children = List.map (fun child -> fully_resolve child subst) children }
  | Node (pred, terms) -> 
      Node (pred, List.map (fun t -> fully_resolve t subst) terms)
;;

let rec print_subst query subst =
  let query_vars = List.concat (List.map get_query_variables query) in
  let relevant_bindings = filter_relevant_bindings query_vars subst in
  let rec print_bindings = function
      [] -> ()
    | [(var, term)] -> 
        Printf.printf "%s = " var; 
        print_term (fully_resolve term subst)
    | (var, term) :: rest ->
        Printf.printf "%s = " var; 
        print_term (fully_resolve term subst); 
        Printf.printf ", "; 
        print_bindings rest
  in
  print_bindings relevant_bindings;
  Printf.printf ".\n"
;;

let rec print_results results query =
  let has_vars = has_variables query in
  match results with
    [] -> Printf.printf "false.\n"
  | _ ->
      if has_vars then
        List.iter (fun s -> print_subst query s) results
      else
        Printf.printf "true.\n"
;;

(* Testing Prolog Family Program *)
let family_prog = [
  (* Facts *)
  fact "male" [c "saharsh"];       (* male(saharsh). *)
  fact "male" [c "mukesh"];        (* male(mukesh). *)
  fact "male" [c "vanshidhar"];    (* male(vanshidhar). *)
  fact "female" [c "anvesha"];     (* female(anvesha). *)
  fact "female" [c "mansi"];       (* female(mansi). *)
  fact "female" [c "urmila"];      (* female(urmila). *)
  fact "parent" [c "mukesh"; c "saharsh"];     (* parent(mukesh, saharsh). *)
  fact "parent" [c "mansi"; c "saharsh"];      (* parent(mansi, saharsh). *)
  fact "parent" [c "mukesh"; c "anvesha"];     (* parent(mukesh, anvesha). *)
  fact "parent" [c "mansi"; c "anvesha"];      (* parent(mansi, anvesha). *)
  fact "parent" [c "vanshidhar"; c "mukesh"];  (* parent(vanshidhar, mukesh). *)
  fact "parent" [c "urmila"; c "mukesh"];      (* parent(urmila, mukesh). *)
  fact "different" [c "saharsh"; c "anvesha"]; (* different(saharsh, anvesha). *)
  fact "different" [c "anvesha"; c "saharsh"]; (* different(anvesha, saharsh). *)

  (* Rules *) 
  (* mother(M, C) :- female(M), parent(M, C). *) 
  rule "mother" [v "M"; v "C"] [pred "female" [v "M"]; pred "parent" [v "M"; v "C"]];
  
  (* father(F, C) :- male(F), parent(F, C). *)
  rule "father" [v "F"; v "C"] [pred "male" [v "F"]; pred "parent" [v "F"; v "C"]];
  
  (* daughter(D, P) :- female(D), parent(P, D). *)
  rule "daughter" [v "D"; v "P"] [pred "female" [v "D"]; pred "parent" [v "P"; v "D"]];
  
  (* grandparent(GP, GC) :- parent(GP, P), parent(P, GC). *)
  rule "grandparent" [v "GP"; v "GC"] [pred "parent" [v "GP"; v "P"]; pred "parent" [v "P"; v "GC"]]; 
  
  (* grandmother(GM, GC) :- female(GM), grandparent(GM, GC). *)
  rule "grandmother" [v "GM"; v "GC"] [ pred "female" [v "GM"]; pred "grandparent" [v "GM"; v "GC"]];
  
  (* sibling(X, Y) :- parent(P, X), parent(P, Y), different(X, Y). *)
  rule "sibling" [v "X"; v "Y"] [pred "parent" [v "P"; v "X"]; pred "parent" [v "P"; v "Y"]; pred "different" [v "X"; v "Y"]];
  
  (* brother(X, Y) :- male(X), sibling(X, Y). *)
  rule "brother" [v "X"; v "Y"] [pred "male" [v "X"]; pred "sibling" [v "X"; v "Y"]]; 
  
  (* son(C, P) :- male(C), parent(P, C). *)
  rule "son" [v "C"; v "P"] [pred "male" [v "C"]; pred "parent" [v "P"; v "C"]]; 
  
  (* grandfather(GF, GC) :- male(GF), parent(GF, P), parent(P, GC). *)
  rule "grandfather" [v "GF"; v "GC"] [pred "male" [v "GF"]; pred "parent" [v "GF"; v "P"]; pred "parent" [v "P"; v "GC"]] 
];;

(* Executing query examples *)
let () =
  (* Basic relationship queries *)
  Printf.printf "?- sibling(anvesha, saharsh).\n";
  print_results (query family_prog [pred "sibling" [c "anvesha"; c "saharsh"]]) 
    [pred "sibling" [c "anvesha"; c "saharsh"]];

  Printf.printf "\n?- brother(saharsh, anvesha).\n";
  print_results (query family_prog [pred "brother" [c "saharsh"; c "anvesha"]])
    [pred "brother" [c "saharsh"; c "anvesha"]];

  Printf.printf "\n?- grandfather(GF, saharsh).\n";
  print_results (query family_prog [pred "grandfather" [v "GF"; c "saharsh"]])
    [pred "grandfather" [v "GF"; c "saharsh"]];

  Printf.printf "\n?- son(Child, mukesh).\n";
  print_results (query family_prog [pred "son" [v "Child"; c "mukesh"]])
    [pred "son" [v "Child"; c "mukesh"]];

  Printf.printf "\n?- mother(M, saharsh).\n";
  print_results (query family_prog [pred "mother" [v "M"; c "saharsh"]])
    [pred "mother" [v "M"; c "saharsh"]];

  Printf.printf "\n?- father(F, anvesha).\n";
  print_results (query family_prog [pred "father" [v "F"; c "anvesha"]])
    [pred "father" [v "F"; c "anvesha"]];

  Printf.printf "\n?- daughter(D, mukesh).\n";
  print_results (query family_prog [pred "daughter" [v "D"; c "mukesh"]])
    [pred "daughter" [v "D"; c "mukesh"]];

  Printf.printf "\n?- grandmother(GM, saharsh).\n";
  print_results (query family_prog [pred "grandmother" [v "GM"; c "saharsh"]])
    [pred "grandmother" [v "GM"; c "saharsh"]];

  (* Queries with variables *)
  Printf.printf "\n?- sibling(X, Y).\n";
  print_results (query family_prog [pred "sibling" [v "X"; v "Y"]])
    [pred "sibling" [v "X"; v "Y"]];

  Printf.printf "\n?- parent(P, Child).\n";
  print_results (query family_prog [pred "parent" [v "P"; v "Child"]])
    [pred "parent" [v "P"; v "Child"]];

  (* Testing specific relationships *)
  Printf.printf "\n?- grandparent(vanshidhar, GC).\n";
  print_results (query family_prog [pred "grandparent" [c "vanshidhar"; v "GC"]])
    [pred "grandparent" [c "vanshidhar"; v "GC"]];

  Printf.printf "\n?- mother(mansi, Child).\n";
  print_results (query family_prog [pred "mother" [c "mansi"; v "Child"]])
    [pred "mother" [c "mansi"; v "Child"]];

  (* Testing false queries *)
  Printf.printf "\n?- father(mansi, saharsh).\n";
  print_results (query family_prog [pred "father" [c "mansi"; c "saharsh"]])
    [pred "father" [c "mansi"; c "saharsh"]];
;;