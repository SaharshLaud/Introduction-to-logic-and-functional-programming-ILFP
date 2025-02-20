(* ILFP Assignment 3: A simple boolean evaluator and compiler*)
(* Saharsh Laud 2024MCS2002 *)

(* 1. Define a boolean expression language given by the data type expb *)
(* Unary operators take one and binary operator takes two boolean 
expressions as arguments and produces a new boolean expression. *)
type expb = T 
          | F
          | Not of expb
          | And of expb * expb
          | Or of expb * expb
          | Imply of expb * expb
          | Iff of expb * expb
;; 
(* Test case - *)
let b0 = T;;
let b1 = F;;
let b2 = Not(T);;
let b3 = And(T, F);;
let b4 = Or(T, F);;
let b5 = Imply(T, F);;
let b6 = Iff(T, T);;
let b7 = Or(And(T, F), Not(F));;
    
(* 2. Extend the definitional interpreter evalb to provide a standard 
semantics to all these boolean expressions. *)
let rec evalb expr = match expr with
    T -> true
  | F -> false
  | Not(e) -> not (evalb e)
  | And(e1, e2) -> (evalb e1) && (evalb e2)
  | Or(e1, e2) -> (evalb e1) || (evalb e2)
  | Imply(e1, e2) -> (not (evalb e1)) || (evalb e2)
  | Iff(e1, e2) -> (evalb e1) = (evalb e2)
;;
(* Test case - *)
evalb b0;;
evalb b1;;
evalb b2;;
evalb b3;;
evalb b4;;
evalb b5;;
evalb b6;;
evalb b7;;

(* Outputs -
# evalb b0 ;;
- : bool = true
# evalb b1 ;;
- : bool = false
# evalb b2 ;;
- : bool = false
# evalb b3 ;;
- : bool = false
# evalb b4 ;;
- : bool = true
# evalb b5 ;;
- : bool = false
# evalb b6 ;;
- : bool = true
# evalb b7 ;;
- : bool = true
*)

(* 3. Define a data type opcodeb to encode operations on the booleans *)
type opcodeb = CONST of bool | NOT | AND | OR | IMPLY | IFF;;

(* 4. Define the function compileb to generate code for boolean expressions 
in terms of the opcodes. *)
let rec compileb e = match e with
    T -> [CONST true]
  | F -> [CONST false]
  | Not e1 -> (compileb e1) @ [NOT]
  | And (e1, e2) -> (compileb e1) @ (compileb e2) @ [AND]
  | Or (e1, e2) -> (compileb e1) @ (compileb e2) @ [OR]
  | Imply (e1, e2) -> (compileb e1) @ (compileb e2) @ [IMPLY]
  | Iff (e1, e2) -> (compileb e1) @ (compileb e2) @ [IFF]
;;
(* Test case - *)
compileb b0;;
compileb b1;;
compileb b2;;
compileb b3;;
compileb b4;;
compileb b5;;
compileb b6;;
compileb b7;;

(* Output - 
# compileb b0 ;;
- : opcodeb list = [CONST true]
# compileb b1 ;;
- : opcodeb list = [CONST false]
# compileb b2 ;;
- : opcodeb list = [CONST true; NOT]
# compileb b3 ;;
- : opcodeb list = [CONST true; CONST false; AND]
# compileb b4 ;;
- : opcodeb list = [CONST true; CONST false; OR]
# compileb b5 ;;
- : opcodeb list = [CONST true; CONST false; IMPLY]
# compileb b6 ;;
- : opcodeb list = [CONST true; CONST true; IFF]
# compileb b7 ;;
- : opcodeb list = [CONST true; CONST false; AND; CONST false; NOT; OR]
*)

(* 5. Adapt the definition of the stack machine execution to define stkmcb *)
exception Stuck

let rec stkmcb s code = match code with
    [] -> s
  | CONST b :: code' -> stkmcb (b :: s) code'
  | NOT :: code' -> (match s with
      | b :: s' -> stkmcb ((not b) :: s') code'
      | _ -> raise Stuck)
  | AND :: code' -> (match s with
      | b2 :: b1 :: s' -> stkmcb ((b1 && b2) :: s') code'
      | _ -> raise Stuck)
  | OR :: code' -> (match s with
      | b2 :: b1 :: s' -> stkmcb ((b1 || b2) :: s') code'
      | _ -> raise Stuck)
  | IMPLY :: code' -> (match s with
      | b2 :: b1 :: s' -> stkmcb ((not b1 || b2) :: s') code'
      | _ -> raise Stuck)
  | IFF :: code' -> (match s with
      | b2 :: b1 :: s' -> stkmcb ((b1 = b2) :: s') code'
      | _ -> raise Stuck)
;;

(* Test case - *)
let calculate_b e = List.hd (stkmcb [] (compileb e));;
calculate_b b0;;
calculate_b b1;;
calculate_b b2;;
calculate_b b3;;
calculate_b b4;;
calculate_b b5;;
calculate_b b6;;
calculate_b b7;;

(* Output - 
# calculate_b b0 ;;
- : bool = true
# calculate_b b1 ;;
- : bool = false
# calculate_b b2 ;;
- : bool = false
# calculate_b b3 ;;
- : bool = false
# calculate_b b4 ;;
- : bool = true
# calculate_b b5 ;;
- : bool = false
# calculate_b b6 ;;
- : bool = true
# calculate_b b7 ;;
- : bool = true
*)

(* 6. State the theorems for the correctness of the implementation *)
(* Correctness of the compiler and execution of the stack machine wrt the standard
reference semantics given by the definitional interpreter evalb
for all e: expb,
calculate_b e = evalb e*)
(* Soundness Theorem:
For all boolean expressions e: expb and all boolean values b: bool, 
if stkmcb [] (compileb e) = [b], then evalb e = b.
   
Completeness Theorem:
For all boolean expressions e: expb and all boolean values b: bool, 
if evalb e = b, then stkmcb [] (compileb e) = [b].
*)

(* 7. Bonus:  Prove these theorems *)
(* Proof of Soundness:
We will prove the soundness theorem by structural induction on the boolean expression e.
Base cases:
Case e = T: stkmcb [] (compileb T) = [CONST true] = [true], and evalb T = true.
Case e = F: stkmcb [] (compileb F) = [CONST false] = [false], and evalb F = false.

Inductive cases:
   1. Case e = Not e1:
      By the inductive hypothesis, if stkmcb [] (compileb e1) = [b1], then evalb e1 = b1.
      stkmcb [] (compileb (Not e1)) = stkmcb [] ((compileb e1) @ [NOT]) = stkmcb [b1] [NOT] = [not b1].
      evalb (Not e1) = not (evalb e1) = not b1.
      Therefore, stkmcb [] (compileb (Not e1)) = [not b1] = [evalb (Not e1)].
   
   2. Case e = And (e1, e2):
      By the inductive hypothesis, if stkmcb [] (compileb e1) = [b1] and 
      stkmcb [] (compileb e2) = [b2], then evalb e1 = b1 and evalb e2 = b2.
      stkmcb [] (compileb (And (e1, e2))) = stkmcb [] ((compileb e1) @ (compileb e2) @ [AND]) 
      = stkmcb [b2; b1] [AND] = [b1 && b2].
      evalb (And (e1, e2)) = (evalb e1) && (evalb e2) = b1 && b2.
      Therefore, stkmcb [] (compileb (And (e1, e2))) = [b1 && b2] = [evalb (And (e1, e2))].
Cases for Or, Imply, and Iff are similar.
     
The inductive step holds for all cases, and the base cases are also verified. 
Therefore, the soundness theorem is proved.
*)
(* Proof of Completeness:
We will prove the completeness theorem by structural induction on the boolean expression e.
Base cases:
Case e = T: evalb T = true, and stkmcb [] (compileb T) = [CONST true] = [true].
Case e = F: evalb F = false, and stkmcb [] (compileb F) = [CONST false] = [false].

Inductive cases:
   1. Case e = Not e1:
      By the inductive hypothesis, if evalb e1 = b1, then stkmcb [] (compileb e1) = [b1].
      evalb (Not e1) = not (evalb e1) = not b1.
      stkmcb [] (compileb (Not e1)) = stkmcb [] ((compileb e1) @ [NOT]) 
      = stkmcb [b1] [NOT] = [not b1] = [evalb (Not e1)].
   
   2. Case e = And (e1, e2):
      By the inductive hypothesis, if evalb e1 = b1 and evalb e2 = b2, 
      then stkmcb [] (compileb e1) = [b1] and stkmcb [] (compileb e2) = [b2].
      evalb (And (e1, e2)) = (evalb e1) && (evalb e2) = b1 && b2.
      stkmcb [] (compileb (And (e1, e2))) = stkmcb [] ((compileb e1) @ (compileb e2) @ [AND]) 
      = stkmcb [b2; b1] [AND] = [b1 && b2] = [evalb (And (e1, e2))].
Cases for Or, Imply, and Iff are similar.

The inductive step holds for all cases, and the base cases are also verified. 
Therefore, the completeness theorem is proved.
*)