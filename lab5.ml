open List;;
exception NOT_UNIFIABLE;;
type symbol = Symbol of string;;
type variable =Variable of  string;;
type term = V of variable | Node of symbol * (term list);;
let rec check_sig l = match l with
[] -> true
| x::xs -> let checkarr x = match x with
                (a, b) -> if b >= 0 then true else false
            in
            let rec finder x xs = match (x,xs) with 
            	((sym, n),[]) -> false
            	| ((sym1,n1),(sym2,n2)::b) -> if sym1 = sym2 then true else (finder x b)
            in
            if (checkarr x = true)&&(finder x xs = false) then check_sig xs
            else false;;
let rec foldr f e l = match l with
    [] -> e
    | (x::xs) -> f x (foldr f e xs);;
let rec wfterm signature thisterm = match thisterm with
 V somvar-> true
| Node (sym, l) -> let rec find ele num lis = match lis with 
						[] -> false
						| (symthis, nint)::xs -> if ((symthis = sym)&&(nint = num)) then true else (find ele num xs)
					in
					let insidefold a b = (wfterm signature a)&&(b) in 
					if ((find sym (List.length l) signature)=false) then false else (foldr insidefold true l);;
let rec ht thisterm = match thisterm with
| V somvar -> 0
| Node (sym, []) -> 0
| Node (sym, l) -> let maxi a b = max (ht a) b in 
					1 + (foldr maxi 0 l);;
let rec size thisterm = match thisterm with
| V str -> 0
| Node (sym, l) -> let addi a b = (size a) + b in 
					1+ (foldr addi 0 l);;
let rec vars thisterm = match thisterm with
| V somvar -> [V somvar]
| Node (sym, l) -> let listor a b = match a with
						V str -> a::b
						| Node (sym1, l1) -> (vars a)@b in 
					let rec removedupli thisli = match thisli with
						| [] -> []
						| x::xs -> let thisf a b = if (a= x) then true else b in 
									if (foldr thisf false xs) then (removedupli xs) else (x::(removedupli xs)) in 
					removedupli (foldr listor [] l);;
type sigma = Sigma of (variable * term) list;;
type compose = Compose of sigma list;;
let rec subst sigma thisterm = match thisterm with
Node (sym, []) -> Node (sym, [])
| V somvar -> let rec finder thisitem l = match l with
					[] -> V thisitem
					|(a,b)::xs -> if (thisitem=a) then b else (finder thisitem xs) in 
				let listor sigm = match sigm with
				Sigma l -> l in 
				finder somvar (listor sigma) 
| Node (sym, l) -> Node (sym, List.map (subst sigma) l);;
let rec composition compose = match compose with 
Compose [] -> Sigma []
| Compose [x] -> x
| Compose (x::xs) -> let finfu x y= match (x,y) with 
					(Sigma a, Sigma b) ->let rec substituter a othersigma = match a with
											[] -> []
											| (v, t)::xs -> (v, subst othersigma t)::(substituter xs othersigma) in 
										let tempsigmaalist = substituter a (Sigma b) in 
										let rec adder l1 l2 = match l2 with 
											[] -> l1
											| (v, t)::xs -> let rec finder v l1 = match l1 with
															[] -> false
															| (v2, t2)::xs -> if (v2=v) then true else (finder v xs) in 
															if (finder v l1) then (adder l1 xs) else (adder (l1@[(v,t)]) xs)
										in 
										Sigma (adder tempsigmaalist b) in
					finfu x (composition (Compose xs));;
 let rec mgu t1 t2 = match (t1,t2) with
 (V x1, V x2) ->if (x1=x2) then (Sigma []) else ( Sigma [(x1, t2)])
| (V x, Node (Symbol s, [])) -> Sigma [(x, t2)]
| (Node (Symbol s, []), V x) -> Sigma [(x, t1)]
| (V x, Node (Symbol s, l)) -> let varlist = vars t2 in 
								let rec finder a l = match l with
								 	[] -> false
								 	| x::xs -> if (x=a) then true else (finder a xs) in 
								if (finder t1 varlist)=false then (Sigma [(x, t2)]) else raise NOT_UNIFIABLE
 | (Node (Symbol s, l), V x) -> let varlist = vars t1 in 
								let rec finder a l = match l with
								 	[] -> false
								 	| x::xs -> if (x=a) then true else (finder a xs) in 
								if (finder t2 varlist)=false then (Sigma [(x, t1)]) else raise NOT_UNIFIABLE
| (Node (Symbol s1, []), Node (Symbol s2, l)) -> if (s1=s2)&&(l=[]) then (Sigma []) else raise NOT_UNIFIABLE
| (Node (Symbol s1, l1), Node (Symbol s2, l2)) -> if (List.length l1)!=(List.length l2) then raise NOT_UNIFIABLE else
													let cunify m1 m2 siga = composition (Compose [siga;(mgu (subst siga m1) (subst siga m2))]) in 
													let rec iteratelist l1 l2 sigb = match (l1,l2) with
														([],[]) -> sigb 
														| (x1::xs1, x2::xs2) -> iteratelist xs1 xs2 (cunify x1 x2 sigb)
														| _ -> raise NOT_UNIFIABLE in 
													iteratelist l1 l2 (Sigma []);;

(* Signatures *)

(* 
# exception NOT_UNIFIABLE
# type symbol = Symbol of string
# type variable = Variable of string
# type term = V of variable | Node of symbol * term list
# val check_sig : ('a * int) list -> bool = <fun>
# val foldr : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b = <fun>
# val wfterm : (symbol * int) list -> term -> bool = <fun>
# val ht : term -> int = <fun>
# val size : term -> int = <fun>
# val vars : term -> term list = <fun>
# type sigma = Sigma of (variable * term) list
# type compose = Compose of sigma list
# val subst : sigma -> term -> term = <fun>
# val composition : compose -> sigma = <fun>
# val mgu : term -> term -> sigma = <fun>
composition function is used to compose multiple sigmas
 *)

 