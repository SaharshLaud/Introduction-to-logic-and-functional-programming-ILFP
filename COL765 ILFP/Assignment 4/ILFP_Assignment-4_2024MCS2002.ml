(* ILFP Assignment 4: Representing finite sets*)
(* Saharsh Laud 2024MCS2002*)

(* The SIGNATURE (or module type) is specified as:*)
module type SET = 
sig 
  type 'a set
  val emptyset : 'a set 
  val makeset : 'a list -> 'a set  (* Function to create a set*)
  val member : 'a  -> 'a set -> bool
  val subset : 'a set -> 'a set -> bool
  val equalsets: 'a set -> 'a set -> bool
  val union :  'a set -> 'a set -> 'a set 
  val inter : 'a set -> 'a set -> 'a set 
  val diff : 'a set -> 'a set -> 'a set 
  val product : ('a set) -> ('b set) -> ('a * 'b) set 
  val power : 'a set -> ('a set) set 
  val to_list : 'a set -> 'a list (* Function that converts set to list*)
end;;

(* Implementation of SET module*)
module Set : SET = struct
  type 'a set = Set of 'a list

  (* Function to remove duplicates*)
  let rec rem_dupli s = match s with
      [] -> []
    | x :: xs -> x :: (rem_dupli (List.filter (fun y -> y <> x) xs)) 

  (* Empty set*)
  let emptyset = Set []
  
  (* Create set from list*)
  let makeset lst = Set (rem_dupli lst)

  (* Member Function*)
  let rec member x (Set s) = match s with
      [] -> false
    | y :: ys -> if x = y then true else member x (Set ys)
  
  (* Subset function*)
  let rec subset (Set s1) (Set s2) = match s1 with
      [] -> true
    | x :: xs -> member x (Set s2) && subset (Set xs) (Set s2)
                   
  (* Equal sets Function*)
  let equalsets (Set s1) (Set s2) = 
    subset (Set s1) (Set s2) && subset (Set s2) (Set s1)
  
  (* Union Function*)
  let union (Set s1) (Set s2) =
    Set (rem_dupli (s1 @ s2))
  
  (* Intersection Function*)
  let inter (Set s1) (Set s2) = Set (rem_dupli (List.filter (fun x -> member x (Set s2)) s1))
  
  (* Difference Function*)
  let diff (Set s1) (Set s2) = Set (rem_dupli (List.filter (fun x -> not (member x (Set s2))) s1))
  
  (* Product Function*)    
  let product (Set s1) (Set s2) =
    let prod = 
      List.fold_left (fun bag x1 -> 
          bag @ List.map (fun x2 -> (x1, x2)) s2) [] s1
    in
    Set prod
  
  (* Power set function for sets*)
  let rec power (Set s) = match s with
      [] -> Set [Set []]
    | x :: xs ->
        let Set p = power (Set xs) in
        Set (p @ List.map (fun (Set s') -> Set (x :: s')) p)
      
  (* Set to list conversion function*)   
  let to_list (Set s) = s 
end;;

(* 1. Testing working and representational invariant*)
(* Creating sets using makeset*)
let s1 = Set.makeset [1;2;3];;  (* Use makeset to create sets*)
let s2 = Set.makeset [2;3;3];;  
let s3 = Set.emptyset;; (* Empty set created using emptyset*)
let s4 = Set.makeset [1;3;2];;
let s5 = Set.makeset [4;3;2];;
let s6 = Set.makeset [1;3;2;2];; 
let k1 = Set.makeset [1; 2];;
let k2 = Set.makeset ['a'; 'b'];;

(* Testing emptyset*)
assert (s3 = Set.emptyset);;  (* Compare to emptyset from the module*)

(* Testing member function*)
assert (Set.member 1 s1 = true);;  (* true as 1 is in s1*)
assert (Set.member 4 s1 = false);;  (* false as 4 is not in s1*)
assert (Set.member 3 s3 = false);;  (* false as  empty set has no members*)
                                    
(* Testing Subset*)
assert (Set.subset s2 s1 = true);; (* s2 is subset of s1*)
assert (Set.subset s1 s2 = false);; (* s1 is not a subset of s2*)
assert (Set.subset s3 s1 = true);; (* Empty set is a subset of every set*)
                                   
(* Testing Equal sets*)
assert (Set.equalsets s1 s6 = true);; (* s1 is equal to s6 set*)
assert (Set.equalsets s2 s3 = false);; (* s2 is not equal to s3 set*)
                                       
(* Testing Union*)                                       
let u = Set.union s1 s5;;
assert (Set.equalsets u (Set.makeset [1;2;3;4]));;
Set.to_list u;;

(* Test intersection*)
let common = Set.inter s1 s2;;
assert (Set.equalsets common (Set.makeset [2;3]));;
Set.to_list common;;

(* Test difference*)
let d = Set.diff s1 s2;;
assert (Set.equalsets d (Set.makeset [1]));;
Set.to_list d;;  

(* Test cross product*)
let prod = Set.product k1 k2;; 
(* Extract and display the underlying list from set*)
Set.to_list prod;;  

(* Test power set*)
let pow = Set.power k1;;
assert (Set.member (Set.makeset []) pow);;
assert (Set.member (Set.makeset [1]) pow);;
assert (Set.member (Set.makeset [2]) pow);;
assert (Set.member (Set.makeset [1;2]) pow);; 


(* 2. Testing equational laws of sets*)
(* Commutative Laws:*)
let a = Set.makeset [1;2;3];;
let b = Set.makeset [2;3;4];;
assert (Set.equalsets (Set.union a b) (Set.union b a));;
assert (Set.equalsets (Set.inter a b) (Set.inter b a));;
(* Proof: s1 n s2 = s2 n s1
   Assume:  x ∈ s1 n s2
   By definition of intersection: x ∈ s1 and  x ∈ s2
   So it implies that  x ∈ s2 and  x ∈ s1 
   Hence, x ∈ s2 n s1 // By definition of intersection
   Thus, if x ∈ s1 n s2 then x ∈ s2 n s1  -->  s1 n s2  ⊆  s2  n s1

   Assume:  x ∈ s2 n s1
   By definition of intersection: x ∈ s2 and  x ∈ s1
   So it implies that  x ∈ s1 and  x ∈ s2
   Hence, x ∈ s2 n s1 // By definition of intersection
   Thus, if x ∈ s2 n s1 then x ∈ s1 n s2  --> s2 n s1  ⊆  s1 n s2 
  
   So by antisymmetry of subset: s1 n s2 ⊆ s2 n s1 and s2 n s1 ⊆ s1 n s2 
   Therefore: s1 n s2 = s2 n s1
*)
(* Associative Laws:*)
let a = Set.makeset [1;2];;
let b = Set.makeset [2;3];;
let c = Set.makeset [3;4];;
assert (Set.equalsets (Set.union (Set.union a b) c) (Set.union a (Set.union b c)));;
assert (Set.equalsets (Set.inter (Set.inter a b) c) (Set.inter a (Set.inter b c)));;

(* Distributive Laws:*)
let a = Set.makeset [1;2];;
let b = Set.makeset [2;3];; 
let c = Set.makeset [3;4];;
assert (Set.equalsets (Set.inter a (Set.union b c)) (Set.union (Set.inter a b) (Set.inter a c)));;
assert (Set.equalsets (Set.union a (Set.inter b c)) (Set.inter (Set.union a b) (Set.union a c)));;

(* Idempotent Laws:*)
let a = Set.makeset [1;2;3];;
assert (Set.equalsets (Set.union a a) a);;
assert (Set.equalsets (Set.inter a a) a);;

(* Identity Laws:*)
let a = Set.makeset [1;2;3];;
let empty = Set.emptyset;;
assert (Set.equalsets (Set.union a empty) a);;
assert (Set.equalsets (Set.inter a empty) empty);;
(* Proof: S n 0 = 0 = 0 n S
   Assume:  x ∈ S n 0 
   By definition of intersection: Assume:  x ∈ S and  Assume:  x ∈ 0 
   But empty set 0 has no members so x ∈ 0  is always false so there 
   cannot be any x ∈ S as well because x is in their intersection. 
   So x ∈ S n 0 is always false and there is no element in S n 0 .
   So it implies, s n 0 ⊆ 0 
   
   Assume x ∈ 0 
   Since 0 has no elements there is no such x. 
   Hence vacuously 0 ⊆ S n 0
   
   So S n 0 ⊆ 0  and  0 ⊆ S n 0
   Thus S n 0 = 0 = 0 n S // Commutativity of intersection.
*)
(* Difference laws*)
let a = Set.makeset [1;2;3];;
let b = Set.makeset [2;3];;
assert (Set.equalsets (Set.diff a a) empty);;   (* A - A = emptyset*)
assert (Set.equalsets (Set.diff a empty) a);;   (* A - emptyset = A*) 

(* Empty set laws*)
let a = Set.makeset [1;2;3];;
let empty = Set.emptyset;;
assert (Set.equalsets (Set.inter a empty) empty);;  (* Annihilation: A intersection emptyset = emptyset*)
assert (Set.equalsets (Set.diff a empty) a);;  (* A - emptyset = A*)
assert (Set.equalsets (Set.diff empty a) empty);;  (* emptyset - A = emptyset*) 

(* Subset laws*)
let a = Set.makeset [1;2];;
let b = Set.makeset [1;2;3];;
let c = Set.makeset [1;2;3;4];;
let d = Set.makeset [1;2];;
let empty = Set.emptyset;;
assert (Set.subset a a);;  (* Reflexivity*) 
assert (Set.subset a d && Set.subset d a);;  (* Antisymmetry*)
assert (Set.subset a b && Set.subset b c && Set.subset a c);;  (* Transitivity*) 
(* Proof: s1 ⊆ s2 and s2 ⊆ s1 then  s1 = s2
   Assume s1⊆ s2 and s2 ⊆ s1
   By definition of subset: 
   If x ∈ s1 then x ∈ s2  // s1 ⊆ s2
   If x ∈ s2 then x ∈ s1  // s2 ⊆ s1
   So every element in s1 is in s2 and every element in s2 is in s1
   So it follows that x s1 if and only if x s2 // Antisymmetry of subset
   Thus, s1 = s2
*)
(* Membership laws*)
let a = Set.makeset [1;2;3];;
let b = Set.makeset [3;4];;
let u = Set.union a b;;
let i = Set.inter a b;;
(* Membership and Union: If x belongs to A union B, then x in A or x in B*)
assert (Set.member 1 u && (Set.member 1 a || Set.member 1 b));;  
assert (Set.member 4 u && (Set.member 4 a || Set.member 4 b));;
(* Membership and Intersection: If x belongs to A intersection B, then x in A and x in B*)
assert (Set.member 3 i && (Set.member 3 a && Set.member 3 b));;  (* 3 belongs to A intersection B*)

(* 3. Analysis of efficiency of the operations.*)
(*
1. emptyset:  Takes constant time (O(1)) since it just creates and empty set.
2. makeset:   Takes quadratic time (O(n^2)) where n: length of set because it 
              creates a set by removing duplicates. For each element the filter function
              is called and it traverses the rest of list to filter out the duplicates.
3. member:    Takes linear time (O(n)) where n: length of 1st set because it performs 
              linear search through the set until the element is found or set ends.
4. subset:    Takes O(nxm) time where n: length of 1st set; m: length of 2nd set,
              because For each element in the first set, we check membership in the second set, 
              which takes O(m) time so for n elements its O(nxm). 
              If same size sets then it will be quadratic time in length of sets.
5. equalsets: Takes O(nxm) time where n: length of 1st set; m: length of 2nd set,
              because it calls subset operation 2 times so time taken depends on time taken
              by subset operation which is O(nxm).
6. union:     Takes quadratic time (O(n+m)^2) where n: length of 1st set; m: length of 2nd set,
              because the concatenation of two lists using append takes O(n+m) time but then we
              have to maintain the representational invariant also so we remove the duplicates on 
              this union list which will take O((n+m)^2)) and this will become dominant term.
7. inter:     Takes O(nxm) time where n: length of 1st set; m: length of 2nd set,
              because it filters for each element in the first set, it checks membership in the 
              second set, which takes O(m) time so for n elements its O(nxm). 
8. diff:      Takes O(nxm) time where n: length of 1st set; m: length of 2nd set, because it 
              filters for each element in the first set, it checks membership in the second 
              set and then excludes such members, which takes O(m) time so for n elements its O(nxm). 
9. product:   Takes O(nxm) time where n: length of 1st set; m: length of 2nd set,
              because for each element in the first set, it creates a pair with element in the 
              second set, which takes O(m) time so for n elements its O(nxm) pairs. 
10. power:    Takes exponential time (O(n*(2^n))) where n: length of 1st set because we need to process
              each element of the set while creating a subset whether to take it or not and there are 
              2^n such subsets possible.
11. to_list:  Takes constant time (O(1)) since it just underlying list in our set representation.
*) 

(* 4. What if duplicates were allowed? *)
(* Easier/No change:-
   emptyset: No change since it just gives an empty set.
   makeset: It would be easier since we dont need to remove duplicates which took quadratic time.
   member: Member would be easier in case when an element has duplicates since we can stop after 
           finding just the first occurence.
   union:  Union would be easier since we dont have to apply the function for removing duplicates
           which resulted in quadratic time so the time would be reduced to linear time since we just
           need to append one list at end of another. 
   product: No change as it only creates pairs so having duplicates just increases number of pairs.
*)
(* Harder:-
   subset: It becomes harder because earlier we had to just check if elements are present or not but
           now if A is subset of B then we need to count and check that for every element in A, it 
           appears atleast as many times in B
   equalsets: It also becomes harder because now we have to check that if x is in set A and appears k times
              then x must be in set B and also appears k times in B. So keeping count of appearance makes 
              it harder.
   inter: It becomes difficult as we need to keep count of occurences and then in intersection set keep 
          the minimum count for an element common to both the sets.
   diff: It becomes difficult because we need to reduce count of element in set A according to their 
         occurences in set B.
   power: Although the overall time complexity still is exponential but the operation becomes harder to
          process because due to duplicates many subsets become redundant in the powerset.
*)
   
  