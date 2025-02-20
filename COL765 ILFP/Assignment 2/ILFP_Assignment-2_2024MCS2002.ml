(* ILFP Assignment 2: Vectors represented using lists *)
(* Saharsh Laud 2024MCS2002 *)

(* Type vector as a float list *)
type vector = float list;;

(* Exception DimError *)
exception DimError;;
                  
(* 1. Zero function *)
let zero (n : int) : vector = 
  if n <=0 then
    raise (DimError) 
  else
    List.init n (fun _ -> 0.0) 
;;
(* Test case -
# zero 5 ;;
- : vector = [0.; 0.; 0.; 0.; 0.]
*)
  
(* 2. Unit vectors *)
(* Unit vectors have one component 1.0 correspoding 
   to the direction the unit vector represents.*)
let unit_vector (n : int) (i : int) : vector =
  if n <= 0 || i < 0 || i >= n then
    raise (DimError)
  else
    List.init n (fun j -> if j = i then 1.0 else 0.0)
;;
(* Test case -
# unit_vector 3 0 ;;
- : vector = [1.; 0.; 0.]
# unit_vector 3 1 ;;
- : vector = [0.; 1.; 0.]
# unit_vector 3 2 ;;
- : vector = [0.; 0.; 1.]
# unit_vector 3 3 ;;
Exception: DimError.
*)
                                                      
(* 3. Dimensions function *)
let dim (v : vector) : int =
  List.length(v)
;;
(* Test cases - 
# dim [1.0; 2.0; 3.0] ;;
- : int = 3
# dim [2.2;4.67;3.33;9.8] ;;
- : int = 4
# dim [] ;;
- : int = 0
*)

(* 4. Opposite function *)
let opp (v : vector) : vector =
  List.map (fun x -> -.x) v
;;
(* Test cases -
# opp [] ;;
- : vector = []
# opp [1.0;9.8;3.14] ;;
- : vector = [-1.; -9.8; -3.14]
# opp [4.4;6.7;8.8;9.1;30.5;57.981] ;;
- : vector = [-4.4; -6.7; -8.8; -9.1; -30.5; -57.981]
*)

(* 5. Addition function *)
let rec addv (v1 : vector) (v2 : vector) : vector =
  match v1, v2 with
    [], [] -> []
  | x1::xs1, x2::xs2 -> (x1 +. x2) :: addv xs1 xs2
  | _ -> raise (DimError)
;;
(* Test cases -
# addv [1.0;2.0] [3.0;4.0]
- : vector = [4.; 6.]
# addv [22.3;55.4;76.011] [13.40;12.6;5.0234] ;;
- : vector = [35.7; 68.; 81.0343999999999909]
# addv [22.0;4.0] [21.56] ;;
Exception: DimError.
*)

(* Testing various laws of vector addition *)
let v1 = [1.0;2.0;3.0];;
let v2 = [4.0;5.0;6.0];;
let v3 = [7.0;8.0;9.0];;
let zero_vector = zero 3;;

(* Commutativity *)
let commutest = (addv v1 v2 = addv v2 v1);;
(* val commutest : bool = true *)

(* Associativity *)
let assoctest = (addv (addv v1 v2) v3 = addv v1 (addv v2 v3));;
(* val assoctest : bool = true *)

(* Identity *)
let idtest = (addv v1 zero_vector = v1);;
(* val idtest : bool = true *)

(* Inverse *)
let invtest = (addv v1 (opp v1) = zero_vector);;
(* val invtest : bool = true *)

(* 6. Subtraction function *)
let subv (v1 : vector) (v2 : vector) : vector =
  addv v1 (opp v2)
;;
(* Test cases -
# subv [4.0;5.0;6.0] [1.0;2.0;3.0] ;;
- : vector = [3.; 3.; 3.]
# subv [1.0;22.0;34.92;43.0] [1.0;35.5] ;;
Exception: DimError.
# subv [10.5;21.44] [56.2;20.3] ;;
- : vector = [-45.7; 1.14000000000000057];;
*)

(* 7. Scalar Multiplication *)
(* Define the scalarmult function using List.map *)
let scalarmult (c : float) (v : vector) : vector =
  List.map (fun x -> c *. x) v
;;
(* Test cases -
# scalarmult 6.0 [1.0;2.0;3.0] ;;
- : vector = [6.; 12.; 18.]
# scalarmult 3.0 [] ;;
- : vector = []
*)

(* Testing that scalar multiplication distributes over vector addition
   i.e. c*(v1+v2) = cv1 + cv2 *)
let v1 = [1.0;2.0;3.0];;
let v2 = [4.0;5.0;6.0];;
let c = 2.0;;
let lhs = scalarmult c (addv v1 v2);; 
(* val lhs : vector = [10.; 14.; 18.] *)
let rhs = addv (scalarmult c v1) (scalarmult c v2);;
(* val rhs : vector = [10.; 14.; 18.] *) 
let disttest = (lhs = rhs);;
(* val disttest : bool = true *) 

(* 8. Dot Product *)
let rec dotprod (v1 : vector) (v2 : vector) : float =
  match v1, v2 with
    [], [] -> 0.0
  | x1::xs1, x2::xs2 -> (x1 *. x2) +. dotprod xs1 xs2
  | _ -> raise (DimError)
;;
(* Test case -
# dotprod [1.0;2.0;3.0] [4.0;5.0;6.0] ;;
- : float = 32.
*)
(* Testing that dot product is commutative *)
let v1 = [1.0;2.0;3.0];;
let v2 = [4.0;5.0;6.0];;
let dotcommutest = (dotprod v1 v2 = dotprod v2 v1);;
(* val dotcommutest : bool = true *)

(* 9. Vector Magnitude *)
let norm (v : vector) : float =
  sqrt (List.fold_left (fun acc x -> acc +. (x *. x)) 0.0 v)
;;
(* Test case -
# norm [3.0;4.0] ;;
- : float = 5.
# norm [] ;;
- : float = 0.
# norm [-9.23;6.55] ;;
- : float = 11.3179238378776876
# norm (zero 3) ;;
- : float = 0.
# norm [-7.0] ;;
- : float = 7.
# norm (unit_vector 3 0) ;;
- : float = 1.
*)
(* 10. Normalize vector *)
let normalise (v : vector) : vector =
  let mg = norm v in
  if mg = 0.0 then
    raise (DimError)
  else
    List.map (fun x -> x /. mg) v
;;
(* Test cases -
# normalise [3.0;4.0] ;;
- : vector = [0.6; 0.8]
# normalise [0.0;0.0] ;;
Exception: DimError.
# normalise [0.6;0.8] ;;
- : vector = [0.6; 0.8]
# norm [0.6;0.8] ;;
- : float = 1.
# normalise [-5.0;10.5] ;;
- : vector = [-0.429933580392347747; 0.902860518823930258]
# normalise [3.3;5.7;6.8;13.011] ;;
- : vector =
[0.205089195200413688; 0.354244973527987339; 0.422608038594791846;
 0.808610763258358345]
# normalise [44.3] ;;
- : vector = [1.]
*)

(* 11. Parallel vectors v1 = c*v2 *)
(* First we check for dimensions match then,
   Find magnitude of both vectors then,
   checks for zero vectors then,
   find the scaling factor and check for parallel
*)
   
let parallel (v1 : vector) (v2 : vector) : bool =
  if dim v1 <> dim v2 then
    raise (DimError)
  else
    let nv1 = norm v1 in
    let nv2 = norm v2 in
    if nv1 = 0.0 && nv2 = 0.0 then
      true
    else if nv1 = 0.0 || nv2 = 0.0 then
      false  
    else
      let sv2 = scalarmult (nv1 /. nv2) v2 in
      v1 = sv2 || v1 = opp sv2
;;
(* Test cases - 
# parallel [1.0;2.0] [16.0;32.0] ;;
- : bool = true
# parallel (zero 3) (zero 3) ;;
- : bool = true
# parallel [33.0;45.776;123.3463;32.243] [13.3;53.34] ;;
Exception: DimError.
# parallel [4.5;6.7] (zero 2) ;;
- : bool = false
# parallel [5.0] [7.0] ;;
- : bool = true
# parallel [3.0;4.0] [-3.0;4.0] ;;
- : bool = false
# parallel [3.0;4.0] (opp [3.0;4.0]) ;;
- : bool = true
*)

(* 12. Cross Product *)
(* Cross product of two vectors v1 = (x1;y1;z1) and v2 = (x2;y2;z2) is,
   v1 x v2 = ((y1z2-z1y2),(z1x2-x1z2),(x1y2-y1x2))
   We first do dimension check and then perform above operation for
   each component x,y, and z.
   The failwith is used to handle the mismatch cases so that 
   we dont get the warning for pattern matching not exhaustive cases.
*) 
let crossprod (v1 : vector) (v2 : vector) : vector = 
  let x1, y1, z1 = match v1 with
      [x1; y1; z1] -> (x1, y1, z1)
    | _ -> raise (DimError)
  in
  let x2, y2, z2 = match v2 with
      [x2; y2; z2] -> (x2, y2, z2)
    | _ -> raise (DimError)
  in
  [
    (y1 *. z2) -. (z1 *. y2);  (* x-component *)
    (z1 *. x2) -. (x1 *. z2);  (* y-component *)
    (x1 *. y2) -. (y1 *. x2)   (* z-component *)
  ]
;;
(* Test cases -
# crossprod [1.0;2.0] [3.0;4.0] ;;
Exception: DimError.
# crossprod [1.0;2.0;6.4] [3.0;4.0] ;;
Exception: DimError.
# crossprod [1.0;2.0;3.0] [4.0;5.0;6.0] ;;
- : vector = [-3.; 6.; -3.]
# crossprod (unit_vector 3 0) (unit_vector 3 1) ;;
- : vector = [0.; 0.; 1.]
# crossprod [-5.0;4.6;-3.9] [3.4;2.2;7.1] ;;
- : vector = [41.2399999999999949; 22.240000000000002; -26.64]
*)

(* Testing various laws of cross product *)
let v1 = [1.0;2.0;3.0];;
let v2 = [4.0;5.0;6.0];; 
let v3 = [7.0;8.0;9.0];;
(* Anti-commutativity *)
(* crossprod(v1,v2) = opp(crossprod(v2,v1)) *)
let cross1 = crossprod v1 v2;;
let cross2 = opp (crossprod v2 v1);;
let acmtest = (cross1 = cross2);;
(* val acmtest : bool = true *) 

(* Distributivity over vector addition *)
(* crossprod(v1, (v2+v3)) = crossprod(v1,v2) + crossprod(v1,v3) *) 
let cross1 = crossprod v1 (addv v2 v3);;
let cross2 = addv (crossprod v1 v2) (crossprod v1 v3);;
let disttest = (cross1 = cross2);;
(* val disttest : bool = true *) 

(* Cross with zero vector *)
(* crossprod(v,zero) = zero *)
let v = [1.0;2.0;3.0];;
let zv = zero 3;; 
let cross1 = crossprod v zv;;
let ans = zero 3;;
let crosszerotest = (cross1 = ans);; 
(* val crosszerotest : bool = true *) 
 
(* Bonus Tasks *)
(* 13. Box Product *)
let boxprod (v1 : vector) (v2 : vector) (v3 : vector) : float =
  let cross = crossprod v2 v3 in
  dotprod v1 cross
;;
(* Test case - 
# boxprod [1.0;2.0;3.0] [4.0;5.0;6.0] [7.0;8.0;9.0] ;;
- : float = 0.
# boxprod [1.0; 0.0; 0.0] [0.0; 2.0; 0.0] [0.0; 0.0; 3.0] ;;
- : float = 6.
# boxprod (zero 3) [1.0;2.0;3.0] [4.0;5.0;6.0] ;;
- : float = 0.
*)
              
(* 14. Rotate vector along new axis *)
(* We can express vector v as linear combination of basis vectors.
   For this we will just have to find projection of v along all the 
   basis vectors. v = c1b1 + c2b2 + c3b3....
   v = [4.0; 3.0];;
   b1 = [1.0; 0.0];;
   b2 = [0.0; 1.0];;
   basis = [b1; b2];;
   Projection onto b1 :- dotprod(v,b1)/ magnitude b1 this gives c1
   Projection onto b2 :- dotprod(v,b2)/ magnitude b2 this gives c2
   Map function changes each basis vector bi to cibi
   
  We can check if n vectors are linearly independent if they are orthogonal i.e.
   dotprod(vi,vj) = 0 for all pairs of vectors.
  Here since the question mentions n linearly independent vectors we are assuming the 
   given basis vectors are linearly independent.
*)
let rotate (v : vector) (basis : vector list) : vector =
  if List.length v <> List.length basis then
    raise (DimError)
  else
    List.map (fun vi ->
        let numerator = dotprod v vi in
        let denominator = norm vi in
        numerator /. denominator
      ) basis
;;
(* Test case - *)
let v = [3.0; 4.0; 5.0];;
let basis = [[0.0; 1.0; 0.0]; [-1.0; 0.0; 0.0]; [0.0; 0.0; 1.0]];; 
rotate v basis;;
(* - : vector = [4.; -3.; 5.]  rotated 90 degrees*)
