(*COMP302*)
(*Assignment 4*)
(*Fall 2017*)
(*Kallandria Blasko*)

(* Q1: A Rose by any Other Name Would Smell as Sweet *)

type 'a rose_tree = Node of 'a * ('a rose_tree) list

(* Find with exceptions *)

exception BackTrack 

(* Q1.1 write a function that finds an element of the tree using backtracking with exceptions *)

(*function returns exception: BackTrack on failure to find, returns Some a if it finds what you are looking for*)
let rec find_e (p : 'a -> bool) (t : 'a rose_tree) : 'a option=  (* Function with exceptions *)
match t with
| Node(a, [])->if p a then Some a else raise BackTrack
| Node(a, h::t)->if p a then Some a else try find_e p h with BackTrack -> let x =Node(a,t) in find_e p x

(* Q1.1: write this function and it helper functions *)
(*This function uses find_e as a helper. If the exception BackTrack is raised then it returns None*)
let find (p : 'a -> bool)  (t : 'a rose_tree) : 'a option =
  try find_e p t with BackTrack -> None

(* Find with failure continuations *)
let rec find_k (p : 'a -> bool) (t : 'a rose_tree) (k : unit -> 'a option) : 'a option =
match t with 
(*If not found then k () which returns None*)
| Node(a, [])-> if p a then Some a else k ()
(*IF you find the element, return it. Otherwise call find_k on the head rose_tree. The continuation is called on the rest*) 
| Node(a, h::t)-> if p a then Some a else let x =Node(a,t) in find_k p h (fun () -> find_k p x k)

(* Q1.2: write this function and it helper functions *)
let find' (p : 'a -> bool)  (t : 'a rose_tree) : 'a option = (*  call find_k with the appropriate inital continuation *)
find_k p t (fun () -> None)

(* Find all with continuations *)

let rec find_all_k  (p : 'a -> bool) (t : 'a rose_tree) (k : 'a list -> 'b) : 'b =
match t with
(*if you find it then add it to the continuation, otherwise call k []*)
| Node(a, [])-> if p a then k (a::[]) else k []
(*check in the the rosetree at the head of the list and check all the rosetrees in the tail*)
(*if element is found then add it to the continuation, if not then leave it*)
| Node(a, (Node(x,xs))::t)->  
	find_all_k p (Node(a,t)) 
	(fun b -> find_all_k p (Node(x,xs)) 
		(fun c ->if p a then k (c@(a::b)) else k (c@b)))


(* Q1.3: write this function and it helper functions *)
let find_all p t = find_all_k p t (fun l -> l)

(* An example to use *)

let example = Node (7, [ Node (1, [])
                         ; Node (2, [Node (16, [])])
                         ; Node (4, [])
                         ; Node (9, [])
                         ; Node (11, [])
                         ; Node (15, [])
                         ])

let is_big x =  x > 10


(* Q2 : Rational Numbers Two Ways *)

type fraction = int * int

module type Arith =
  sig
    type t
    val epsilon : t             (* A suitable tiny value, like epsilon_float for floats *)

    val plus : t -> t -> t      (* Addition *)
    val minus : t -> t -> t     (* Substraction *)
    val prod : t -> t -> t      (* Multiplication *)
    val div : t -> t -> t       (* Division *)
    val abs : t -> t            (* Absolute value *)
    val lt : t -> t -> bool     (* < *)
    val le : t -> t -> bool     (* <= *)
    val gt : t -> t -> bool     (* > *)
    val ge : t -> t -> bool     (* >= *)
    val eq : t -> t -> bool     (* = *)
    val from_fraction : fraction -> t (* conversion from a fraction type *)
    val to_string : t -> string        (* generate a string *)
  end

module FloatArith : Arith =
struct
  type t = float
  let epsilon = epsilon_float
  let from_fraction (num, den) = float_of_int num /. float_of_int den

  let plus = (+.)
  let minus = (-.)
  let prod = ( *. )
  let div = ( /. )
  let abs = abs_float
  let lt = (<)
  let le = (<=)
  let gt = (>)
  let ge = (>=)
  let eq = (=)
  let to_string x = string_of_float x
end

(* Q2.1: Implement the Arith module using rational numbers (t = fraction) *)

 module FractionArith : (Arith with type t = fraction) = 
 struct 
 	type t = fraction
 	let epsilon = (1,10000000)
 	(*use cross-multiplication*)
 	let plus (a,b) (c,d) = ((a*d) + (b*c), b*d)
 	let minus (a,b) (c,d) = ((a*d) - (b*c), b*d)
 	(*multiply numerators and denominators*)
 	let prod (a,b) (c,d) = (a*c,b*d)
 	(*flip the bottom fraction and multiply*)
 	let div (a,b) (c,d) = prod (a,b) (d,c)
 	let abs (a,b) = (abs a, abs b)
 	let lt (a,b) (c,d)= if (((float_of_int a)/.(float_of_int b)) < ((float_of_int c)/.(float_of_int d))) then true
 						else false 
 	let le (a,b) (c,d)=if (((float_of_int a)/.(float_of_int b)) <= ((float_of_int c)/.(float_of_int d))) then true
 						else false 
 	let gt (a,b) (c,d) = if (((float_of_int a)/.(float_of_int b)) > ((float_of_int c)/.(float_of_int d))) then true
 						else false 
 	let ge (a,b) (c,d)= if (((float_of_int a)/.(float_of_int b)) >= ((float_of_int c)/.(float_of_int d))) then true
 						else false 
 	let eq (a,b) (c,d)=if (((float_of_int a)/.(float_of_int b)) == ((float_of_int c)/.(float_of_int d))) then true
 						else false 
 	let to_string (a,b) = (string_of_int a)^"/"^(string_of_int b)
 	let from_fraction (a,b)= (a,b)
 end

module type NewtonSolver =
  sig
    type t

    val square_root : t -> t
  end

(* Q2.2: Implement a function that approximates the square root using  the Newton-Raphson method *)

module Newton (A : Arith) : (NewtonSolver with type t = A.t) = 
struct 
	type t=A.t
	let square_root t = 
		let rec findroot x acc = 
		(*check if difference is less than episilon, if so then return acc*)
		if A.le (A.minus x (A.prod acc acc)) A.epsilon then acc 
		(*if difference is not yet big enough then do (x/acc + acc)/2*)
		else findroot x (A.div (A.plus (A.div x acc) acc) (A.from_fraction (2,1)))
	in findroot t (A.from_fraction (1,1))
end

(* Examples *)

(* module FloatNewton = Newton (FloatArith) *)
(* module RationalNewton = Newton (FractionArith) *)

(* let sqrt2 = FloatNewton.square_root (FloatArith.from_fraction (2, 1)) *)
(* let sqrt2_r = RationalNewton.square_root (FractionArith.from_fraction (2, 1)) *)

(* Q3 : Real Real Numbers, for Real! *)

type 'a stream = { head : 'a  ; tail : unit -> 'a stream}

let rec nth z = function
  | 0 -> z.head
  | n -> nth (z.tail()) (n - 1)

let rec constant x = {head = x ; tail = fun () -> constant x }

(* Some examples *)

let sqrt2 =
  {head = 1 ; tail = fun () -> constant 2} (* 1,2,2,2,2... *)

let golden_ratio = constant 1   (* 1,1,1,1,1,1 *)

let rec take n z =
  if n = 1 then [z.head]
  else z.head::(take (n-1) (z.tail()))

(*just a helper function that gets the last element of a list*)
 let rec last l = match l with
 | x::[] -> x 
 | _::xs -> last xs

(* Q3.1: implement the function q as explained in the pdf *)
let rec q z n = 
if n=0 then 1
else 
	(*if n=1 then x0*)
	if n=1 then (last(take (n+1) z))
	(*else x(n)*q(n-1) + q(n-2)*)
	else ((last(take (n+1) z))*(q z (n-1)) + (q z (n-2)))

(* Q3.2: implement the function r as in the notes *)
let rec r z n = 
if n=0 then (float_of_int(last(take 1 z)))
else 
	(*avoids the case of adding infinity, adds 0 instead*)
	if ((((q z (n-1))*(q z n)))==0) then (0.0+.(r z (n-1))) 
	(*if it is not 0 then add the next term*)
	else ((((-1.0)**float_of_int(n-1))/.(float_of_int((q z (n-1))*(q z n))))+.(r z (n-1)))

(* Q3.3: implement the error function *)
(*computes the bound for the error given the function in the assignment*)
let error z n = 1.0/.(float_of_int((q z n)*((q z n) + (q z (n-1)))))

(* Q3.4: implement a function that computes a rational approximation of a real number *)
(*finds n s.t. approx is less than the bound of z with n-term approximation*)
let rec rathelper z approx n = match (approx <= error z n) with
|true -> n 
|false -> rathelper z approx (n+1)

(*uses the n found in rathelper to compute the rational number using r*)
let rat_of_real z approx = r z (rathelper z approx 1)

let real_of_int n = { head = n ; tail = fun () -> constant 0}

(* Q3.5: implement a function that computes the real representation of a rational number   *)
let rec real_of_rat r = 
(*if r - the integer part of r is too small then tail is 0*)
if ((r-.(floor r))<epsilon_float) then
{head = int_of_float(floor r); 
 tail = (fun () -> constant 0)
}
(*else the tail is real_of_rat 1/(r-it's integer part)*)
else 
{head = int_of_float(floor r);
tail = (fun () -> real_of_rat (1.0/.(r-.(floor r))))
}


(* Examples *)

(* Approximations of the  irrational numbers we have *)

(* let sqrt_2_rat = rat_of_real sqrt2 1.e-5 *)
(* let golden_ratio_rat = rat_of_real golden_ratio 1.e-5 *)

(* To test the representation of rationals we can try this *)
(* let to_real_and_back n = rat_of_real (real_of_rat n) 0.0001 *)

(* e1 should be very close to 10 (it is exactly 10 in the model solution) *)
(* let e1 = to_real_and_back 10.0 *)

(* this is the float approximation of pi, not the real number pi *)
(* let not_pi = 2. *. acos 0. *)

(* This should share the same 4 decimals with not_pi *)
(* let not_pi' = to_real_and_back not_pi *)
