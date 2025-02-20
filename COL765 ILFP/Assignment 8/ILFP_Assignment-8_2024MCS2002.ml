(* ILFP Assignment 8: CBN Closure Machine and Krivine Machine *)
(* Saharsh Laud 2024MCS2002 *)

(* Type definitions *)
type expr = 
  | Var of string
  | App of expr * expr
  | Lam of string * expr

(* Fresh variable generation *)
let make_fresh_var x =
  let count = ref 0 in
  count := !count + 1;
  x ^ (string_of_int !count)
;;

let rec contains x lst = match lst with
    [] -> false
  | h :: t -> if h = x then true else contains x t
;;

(* Get free variables*)
let rec get_free_vars expr = match expr with
    Var x -> [x]
  | App(e1, e2) -> 
      let vars1 = get_free_vars e1 in
      let vars2 = get_free_vars e2 in
      vars1 @ vars2
  | Lam(x, e) -> 
      let vars = get_free_vars e in
      let rec remove_var lst =
        match lst with
        | [] -> []
        | h :: t -> if h = x then remove_var t else h :: remove_var t
      in remove_var vars
;;

(* Substitution *)
let rec subst x v expr = match expr with
    Var y -> if x = y then v else Var y
  | App(e1, e2) -> App(subst x v e1, subst x v e2)
  | Lam(y, e) ->
      if x = y then Lam(y, e)  (* Variable is bound *)
      else
        let free = get_free_vars v in
        if not (contains y free) then
          Lam(y, subst x v e)
        else
          let fresh = make_fresh_var y in
          Lam(fresh, subst x v (subst y (Var fresh) e))
;;

(* Environment is just a list of pairs *)
type env = (string * closure) list
and closure = Clos of expr * env
;;

(* Stack is a simple list *)
type stack = closure list;;

(* Machine state *)
type state = {term: expr; env: env; stack: stack};;

(* Simple environment lookup *)
let rec lookup x env = match env with
    [] -> Clos(Var x, [])  (* Free variable *)
  | (y, cl) :: rest -> if x = y then cl else lookup x rest
;;

(* Krivine machine step *)
let step state = match state.term with
    App(t1, t2) ->
      Some {
        term = t1;
        env = state.env;
        stack = Clos(t2, state.env) :: state.stack
      }
  | Var x ->
      let Clos(t, env') = lookup x state.env in
      Some {
        term = t;
        env = env';
        stack = state.stack
      }
  | Lam(x, t) ->
      match state.stack with
        [] -> None
      | cl :: rest ->
          Some {
            term = t;
            env = (x, cl) :: state.env;
            stack = rest
          }
;;

(* Evaluate *)
let rec eval state steps =
  if steps = 0 then state
  else
    match step state with
      None -> state
    | Some new_state -> eval new_state (steps - 1)
;;

(* Unload *)
let rec unload state =
  let rec convert_closure (Clos(t, env)) = match t with
      Var x ->
        (match lookup x env with
           Clos(Var y, []) -> Var y
         | cl -> convert_closure cl)
        
    | App(t1, t2) ->
        App(convert_closure (Clos(t1, env)),
            convert_closure (Clos(t2, env)))
          
    | Lam(x, t) ->
        (* remove from environment *)
        let rec remove_from_env env x = match env with
            [] -> []
          | (y, cl) :: rest ->
              if x = y then rest
              else (y, cl) :: remove_from_env rest x
        in
        let env' = remove_from_env env x in
        Lam(x, convert_closure (Clos(t, env')))
  in
  let term = convert_closure (Clos(state.term, state.env)) in
  (* Apply remaining stack *)
  let rec apply_stack term stack = match stack with
      [] -> term
    | cl :: rest -> apply_stack (App(term, convert_closure cl)) rest
  in
  apply_stack term state.stack
;;

(* Main evaluate function *)
let evaluate term =
  let initial_state = {
    term = term;
    env = [];
    stack = []
  } in
  let final_state = eval initial_state 100 in
  unload final_state
;;

(* printing *)
let rec string_of_expr expr = match expr with
    Var x -> x
  | App(t1, t2) -> "(" ^ string_of_expr t1 ^ " " ^ string_of_expr t2 ^ ")"
  | Lam(x, t) -> "(λ" ^ x ^ "." ^ string_of_expr t ^ ")"
;;

(* Test function *)
let test expr =
  print_endline ("Input:  " ^ string_of_expr expr);
  let result = evaluate expr in
  print_endline ("Output: " ^ string_of_expr result);
  print_endline ""
;;

(* Common lambda terms *)
let true_term = Lam("t", Lam("f", Var "t"));;
let false_term = Lam("t", Lam("f", Var "f"));;
let if_term = Lam("c", Lam("t", Lam("f", App(App(Var "c", Var "t"), Var "f"))));;

(* Church pairs *)
let pair = Lam("x", Lam("y", Lam("f", App(App(Var "f", Var "x"), Var "y"))));;
let fst = Lam("p", App(Var "p", true_term));;
let snd = Lam("p", App(Var "p", false_term));;

(* Additional church numerals and operations *)
let zero = Lam("s", Lam("z", Var "z"));;
let one = Lam("s", Lam("z", App(Var "s", Var "z")));;
let two = Lam("s", Lam("z", App(Var "s", App(Var "s", Var "z"))));;

let succ = Lam("n", Lam("s", Lam("z", App(Var "s", App(App(Var "n", Var "s"), Var "z")))));;

let plus = Lam("m", Lam("n", Lam("s", Lam("z", App(App(Var "m", Var "s"), App(App(Var "n", Var "s"), Var "z"))))));;

(* Y combinator for recursion *)
let y_comb = Lam("f", App(Lam("x", App(Var "f", App(Var "x", Var "x"))),
                          Lam("x", App(Var "f", App(Var "x", Var "x")))))
;;

(* Combined test suite *)
let run_all_tests () =
  let tests = [
    (* Identity *)
    App(Lam("x", Var "x"), Var "y");
    
    (* K combinator *)
    App(App(Lam("x", Lam("y", Var "x")), Var "a"), Var "b");
    
    (* Open term *)
    App(Lam("x", App(Var "x", Var "y")), Var "z");
    
    (* If true *)
    App(App(App(if_term, true_term), Var "x"), Var "y");
    
    (* Pair first *)
    App(fst, App(App(pair, Var "a"), Var "b"));
    
    (* Pair second *)
    App(snd, App(App(pair, Var "a"), Var "b"));
    
    (* Self application *)
    App(Lam("x", App(Var "x", Var "x")), Var "y");

    (* Basic reduction *)
    App(Lam("x", Var "x"), Var "y");
    
    (* K combinator (repeated) *)
    App(App(Lam("x", Lam("y", Var "x")), Var "a"), Var "b");
    
    (* S combinator *)
    App(App(App(
        Lam("x", Lam("y", Lam("z", App(App(Var "x", Var "z"), App(Var "y", Var "z"))))), Var "a"), Var "b"), Var "c");
    
    (* Church numerals *)
    App(App(plus, one), one);  (* 1 + 1 *)
    App(succ, zero);           (* succ(0) *)
    
    (* Complex applications *)
    App(App(App(if_term, true_term), Var "x"), Var "y");
    App(fst, App(App(pair, Var "a"), Var "b"));
    App(snd, App(App(pair, Var "a"), Var "b"));
    
    (* Multiple variable occurrences *)
    App(Lam("x", App(App(Var "x", Var "y"), Var "x")), Var "z");
    
    (* Nested lambdas *)
    App(Lam("x", Lam("y", App(Var "x", App(Var "y", Var "x")))), Var "a");
    
    (* Free variables *)
    App(Lam("x", App(Var "x", Var "free")), Var "y");
    
    (* Self application (repeated) *)
    App(Lam("x", App(App(Var "x", Var "x"), Var "x")), Var "y");
    
    (* Y combinator application *)
    App(y_comb, Lam("f", Var "x"))
  ] in
  List.iter test tests
;;
(* Run all tests *)
let () = run_all_tests ();;