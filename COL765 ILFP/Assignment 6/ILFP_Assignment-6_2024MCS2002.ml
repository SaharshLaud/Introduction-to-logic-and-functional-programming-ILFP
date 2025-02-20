(* ILFP Assignment 6: Propositional Resolution Engine*)
(* Saharsh Laud 2024MCS2002*)

(* Define an OCaml data type to represent the structure of 
   a legitimate Horn Clause propositional program.*)
(* atom:    simple, indivisible proposition
   head:    single proposition
   body:    sequence of propositions
   clause:  fact which has only head or rule which has head & body
   program: sequence of clauses
   goal:    sequence of propositions
*)
type atom = string;;
type term = Atom of atom;; 

type head = term;;
type body = term list;;
type clause = Fact of head | Rule of head * body;; 
type program = clause list;;
type goal = term list;;

(* Function to resolve a goal using backtracking*)
let rec resolve prog g resolved = match g with 
    [] -> Some []  (* No more subgoals so goal is satisfied*)
  | sg :: rest -> if List.exists (fun x -> x = sg) resolved then 
        None  (* skip already resolved goals*)
      else
        let rec rslv_curr = function 
            [] -> None  (* no clause matched so backtrack *)
          | cl :: rem -> match cl with 
              Fact h -> 
                if unify sg h then 
                  resolve prog rest (sg :: resolved)  (* subgoal resolved*)
                else 
                  rslv_curr rem  (* next clause*)
            | Rule (h, b) -> 
                if unify sg h then 
                  resolve prog (b @ rest) (sg :: resolved)  (* replace subgoal with rule body*)
                else 
                  rslv_curr rem  (* next clause*)
        in 
        rslv_curr prog

(* Unification logic to match atoms *)
and unify t1 t2 = match t1, t2 with 
    Atom a1, Atom a2 -> a1 = a2 (* atoms must match exactly*)
;;

(* Executes the program on the given goal *)
let exec prog g = match resolve prog g [] with  (* Pass empty list for resolved goals initially*)
    Some _ -> Printf.printf "Goal satisfied" 
  | None -> Printf.printf "Goal not satisfied"
;;

(* Helper functions to define facts and rules*)
let fact s = Fact (Atom s);;
let rule h b = Rule (h, b);;

(* Test cases*)
(* Test case 1: Dog is an animal *)
(* satisfied *)
let prog1 = [fact "animal(dog)"];;
let goal1 = [Atom "animal(dog)"];;
exec prog1 goal1;;

(* Test case 2: Romeo loves Juliet *)
(* satisfied *)
let prog2 = [fact "loves(romeo,juliet)"];;
let goal2 = [Atom "loves(romeo,juliet)"];;
exec prog2 goal2;;

(* Test case 3: All mammals are animals, and dogs are mammals *)
(* satisfied *)
let prog3 = [fact "mammal(dog)"; rule (Atom "animal(dog)") [Atom "mammal(dog)"]];;  (* If dog is a mammal, dog is an animal *) 
let goal3 = [Atom "animal(dog)"];;
exec prog3 goal3;;

(* Test case 4: Juliet loves Paris *)
(* satisfied *)
let prog4 = [fact "loves(juliet,paris)"];;
let goal4 = [Atom "loves(juliet,paris)"];;
exec prog4 goal4;;

(* Test case 5: All birds are animals, penguins are birds but cannot fly *)
(* satisfied *)
let prog5 = [fact "bird(penguin)"; rule (Atom "cannot_fly(penguin)") [Atom "bird(penguin)"]];;  (* If penguin is a bird, penguin cannot fly *)
let goal5 = [Atom "cannot_fly(penguin)"];;
exec prog5 goal5;;

(* Test case 6: A bird is an animal, but we ask if it’s a mammal *)
(* not satisfied *)
let prog6 = [fact "animal(bird)"];;
let goal6 = [Atom "mammal(bird)"];;
exec prog6 goal6;;

(* Test case 7: Romeo loves Juliet, but we ask if Juliet loves Paris *)
(* not satisfied *)
let prog7 = [fact "loves(romeo,juliet)"];;
let goal7 = [Atom "loves(juliet,paris)"];;
exec prog7 goal7;;

(* Test case 8: Basic terms A, B, C *)
(* satisfied *)
let prog8 = [fact "A";                  (* A is a fact *)
             rule (Atom "B") [Atom "A"]; (* B :- A *)
             rule (Atom "C") [Atom "B"]  (* C :- B *)
            ];;
let goal8 = [Atom "C"];;
exec prog8 goal8;;