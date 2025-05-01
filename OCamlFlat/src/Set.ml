(*
 * Set.ml
 *
 * This file is part of the OCamlFLAT library
 *
 * LEAFS project (partially supported by the OCaml Software Foundation) [2020/21]
 * FACTOR project (partially supported by the Tezos Foundation) [2019/20]
 *
 * NOVA LINCS - NOVA Laboratory for Computer Science and Informatics
 * Dept. de Informatica, FCT, Universidade Nova de Lisboa.
 *
 * This software is distributed under the terms of the GPLv3 license.
 * See the included LICENSE file for details.
 *
 *  Written by Artur Miguel Dias (amd)
 *)

(*
 * ChangeLog:
 *
 * mar/2022 (amd) - More functions; stable ordering.
 * may/2021 (amd) - New projection functions; new fixed point function.
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlatSupport.ml".
 *)

(*
 * Description: Polymorphic sets. Naive implementation.
 *
 * TODO: Improve the implementation or move to the functorized sets of
 * the ocaml standard library.
 *)
 
#define OPAQUE_SET 1

module type SetSig =
sig

#if OPAQUE_SET = 1
	type 'a t (* opaque *)
#else
	type 'a t = 'a list
#endif

	val make : 'a list -> 'a t
	val toList : 'a t -> 'a list
	val empty : 'a t
	
	val makeSorted : 'a list -> 'a t
	val sort: 'a t -> 'a t

	val isEmpty : 'a t -> bool
	val size : 'a t -> int
	val compare_sizes: 'a t -> 'b t -> int
	val compare_size_with : 'a t -> int -> int
	val cons : 'a -> 'a t -> 'a t
	val hd : 'a t -> 'a
	val tl : 'a t -> 'a t
	val cut : 'a t -> 'a * 'a t
	val match_ : 'a t -> (unit -> 'b) -> ('a -> 'a t -> 'b) -> 'b
	val nth : 'a t -> int -> 'a
	val nth_opt : 'a t -> int -> 'a option
	val init : int -> (int -> 'a) -> 'a t
	val flatten : 'a t t -> 'a t
	
	val iter : ('a -> unit) -> 'a t -> unit
	val iteri : (int -> 'a -> unit) -> 'a t -> unit
	val map : ('a -> 'b) -> 'a t -> 'b t
	val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
	val flatMap : ('a -> 'b t) -> 'a t -> 'b t
	val flat_map : ('a -> 'b t) -> 'a t -> 'b t
	val fold_left: ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
	val fold_right: ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
	val fold_left_s: ('a t -> 'b -> 'a t) -> 'a t -> 'b t -> 'a t
	val fold_right_s: ('a -> 'b t -> 'b t) -> 'a t -> 'b t -> 'b t

	val for_all : ('a -> bool) -> 'a t -> bool
	val exists : ('a -> bool) -> 'a t -> bool
	val belongs : 'a -> 'a t -> bool
	val subset : 'a t -> 'a t -> bool
	val equals : 'a t -> 'a t -> bool
	
	val find : ('a -> bool) -> 'a t -> 'a
	val find_opt : ('a -> bool) -> 'a t -> 'a option
	val filter : ('a -> bool) -> 'a t -> 'a t

	val fmap : ('a -> bool) -> ('a -> 'b) -> 'a t -> 'b t
	val mapf : ('a -> 'b) -> ('b -> bool) -> 'a t -> 'b t
	
	val partition : ('a -> bool) -> 'a t -> 'a t * 'a t
	
	val split : ('a * 'b) t -> 'a t * 'b t
	val combine : 'a t -> 'b t -> ('a * 'b) t

	val add : 'a -> 'a t -> 'a t
	val remove : 'a -> 'a t -> 'a t
	val inter : 'a t -> 'a t -> 'a t
	val diff : 'a t -> 'a t -> 'a t
	val union : 'a t -> 'a t -> 'a t
	val unionUnsafe : 'a t -> 'a t -> 'a t

	val product : 'a t -> 'b t -> ('a * 'b) t
	val star : 'a list t -> int -> 'a list t
	val allDistinct : ('a -> 'b) -> 'a t -> bool
	val hasDuplicates : 'a t -> bool
	val validate : 'a list -> string -> 'a t
	val fixedPoint : ('a -> 'a) -> 'a ->'a
	val historicalFixedPoint : ('a t -> 'a t) -> ('a t) -> 'a t
	val historicalFixedPointTracing : ('a t -> 'a t) -> ('a t) -> 'a t list
	
	val proj3_1 : ('a * 'b * 'c) t -> 'a t
	val proj3_2 : ('a * 'b * 'c) t -> 'b t
	val proj3_3 : ('a * 'b * 'c) t -> 'c t
	val proj3_12 : ('a * 'b * 'c) t -> ('a * 'b) t
	val proj3_23 : ('a * 'b * 'c) t -> ('b * 'c) t
	
	val test: unit -> int list list
end

module Set : SetSig =
struct
	type 'a t = 'a list
	let delX (v :'a) = List.filter (fun x -> x <> v)

	let rec make (l: 'a list): 'a t =
		match l with
		| [] -> []
		| x::xs -> x::make (delX x xs)
	let toList (s: 'a t): 'a list = s
	let empty: 'a t = []
	
	let makeSorted (l: 'a list): 'a t = List.sort_uniq compare l
	let sort (s: 'a t): 'a list = List.sort compare s

	let isEmpty (s: 'a t): bool = s = []
	let size: 'a t -> int = List.length
	let compare_sizes: 'a t -> 'b t -> int = List.compare_lengths
	let compare_size_with: 'a t -> int -> int = List.compare_length_with
(* cons: add 'x' at the begin if 'x' is new in 's' *)
	let cons (v :'a) (s: 'a t): 'a t = if List.mem v s then s else v::s
(* add: add 'x' at the end if 'x' is new in 's' *)
	let add (v :'a) (s: 'a t): 'a t = if List.mem v s then s else s@[v]
	let hd: 'a t -> 'a = List.hd
	let tl: 'a t -> 'a t = List.tl
	let cut (s: 'a t) = (List.hd s, List.tl s)
	let match_ s e n = if isEmpty s then e () else n (hd s) (tl s)
	let nth: 'a t -> int -> 'a = List.nth
	let nth_opt: 'a t -> int -> 'a option = List.nth_opt
	let init: int -> (int -> 'a) -> 'a t = List.init
	let flatten (ss: 'a t t): 'a t = make (List.flatten ss)
	
	let iter: ('a -> unit) -> 'a t -> unit = List.iter	
	let iteri: (int -> 'a -> unit) -> 'a t -> unit = List.iteri	
	let map (f: 'a -> 'b) (s: 'a t): 'b t = make (List.map f s)
	let mapi (f: int -> 'a -> 'b) (s: 'a t): 'b t = make (List.mapi f s)
	let flatMap (f: 'a -> 'b t) (s: 'a t): 'b t = flatten (List.map f s)
	let flat_map: ('a -> 'b t) -> 'a t -> 'b t = flatMap
	let fold_left: ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a = List.fold_left
	let fold_right: ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b = List.fold_right
	let fold_left_s f u (s: 'a t): 'b t = make (List.fold_left f u s)
	let fold_right_s f u (s: 'a t): 'b t = make (List.fold_right f u s)
	
	let for_all: ('a -> bool) -> 'a t -> bool = List.for_all
	let exists: ('a -> bool) -> 'a t -> bool = List.exists
(* The following three functions use the equality '=' and may not work well for sets of sets *)
	let belongs: 'a -> 'a t -> bool = List.mem
	let subset (s1: 'a t) (s2: 'a t): bool = List.for_all (fun v -> belongs v s2) s1
	let equals (s1: 'a t) (s2: 'a t): bool = compare_sizes s1 s2 = 0 && subset s1 s2

	let find: ('a -> bool) -> 'a t -> 'a = List.find
	let find_opt: ('a -> bool) -> 'a t -> 'a option = List.find_opt	
	let filter: ('a -> bool) -> 'a t -> 'a t = List.filter	(* already distinct *)
	
	(* let fmap (f: 'a -> bool) (m: 'a -> 'b) (s: 'a t) = map m (filter f s) SLOW *)
	let fmap (f: 'a -> bool) (m: 'a -> 'b) (s: 'a t) =
		let rec  fmapX s accu =
			match s with
			| [] -> accu
			| x::xs -> if f x then fmapX xs (m x::accu) else fmapX xs accu
		in
		List.rev (fmapX s [])

	let mapf (m: 'a -> 'b) (f: 'b -> bool) (s: 'a t) =
		let rec  mapfX s accu =
			match s with
			| [] -> accu
			| x::xs -> let r = m x in
						if f r then mapfX xs (r::accu) else mapfX xs accu
		in
		List.rev (mapfX s [])

(*
let rev_filter t ~f =
  let rec find ~f accu = function
    | [] -> accu
    | x :: l -> if f x then find ~f (x :: accu) l else find ~f accu l
  in
  find ~f [] t
;;
*)
	
	let partition: ('a -> bool) -> 'a t -> 'a t * 'a t = List.partition	(* already distinct *)
	
	let split (s: ('a * 'b) t): 'a t * 'b t = let (a, b) = List.split s in (make a, make b)
	let combine: 'a t -> 'b t -> ('a * 'b) t = List.combine
	
	let remove: 'a -> 'a t -> 'a t = delX
	let inter (s1: 'a t) (s2: 'a t): 'a t = List.filter (fun v -> belongs v s2) s1
	let diff (s1: 'a t) (s2: 'a t): 'a t = List.filter (fun v -> not (belongs v s2)) s1
(* union: join s1 with the new elements of s2 *)
	let union (s1: 'a t) (s2: 'a t): 'a t = s1 @ (diff s2 s1)
(* pre: inter s1 s2 = [] *)
	let unionUnsafe (s1: 'a t) (s2: 'a t): 'a t = s1 @ s2

	let product (s1: 'a t) (s2: 'b t): ('a * 'b) t =
		flatMap (fun x -> List.map (fun y -> (x,y)) s2) s1	(* already distinct *)
	let starOne (s: 'a list t) (n: int) (l: 'a t): 'a list t = (* private auxiliary *)
		let z = n - (List.length l) in
		let sel = filter (fun k -> List.length k <= z) s in
			map (fun k -> k @ l) sel
	let rec fixedPoint (f: 'a -> 'a) (x: 'a): 'a =
		let next = f x in
			if x = next then x
			else fixedPoint f next
	let star (s: 'a list t) (n: int): 'a list t =
		fixedPoint (fun v -> union v (flatMap (starOne v n) s)) [[]]

	let allDistinct f (s: 'a t): bool = size s = size (map f s)
	let hasDuplicates (s: 'a t): bool = size s <> size (make s)
	let validate (l: 'a list) (culprit: string): 'a t =
		if hasDuplicates l
			then Error.error culprit "Repetitions in set" empty
			else make l

	let rec acumFixedPoint (f: 'a t -> 'a t) (v: 'a t): 'a t =
		let next = union v (f v) in
			if v = next then v
			else acumFixedPoint f next

	let historicalFixedPoint (f: 'a t -> 'a t) (v: 'a t): 'a t =
		let rec historicalFixedPointX (f: 'a t -> 'a t) (v: 'a t) (acum: 'a t): 'a t =
			let next = f v in
			let newAcum = union v acum in
			if acum = newAcum then v
			else historicalFixedPointX f next newAcum
		in
			historicalFixedPointX f v empty

	let historicalFixedPointTracing (f: 'a t -> 'a t) (v: 'a t): 'a t list =
		let rec historicalFixedPointX (f: 'a t -> 'a t) (v: 'a t) (acum: 'a t) (trace: 'a t list): 'a t list =
			let next = f v in
			let newTrace = trace@[next] in
			let newAcum = union v acum in
			if acum = newAcum then trace
			else historicalFixedPointX f next newAcum newTrace
		in
			historicalFixedPointX f v empty [v]

	let proj3_1 s3 = map (fun (a,_,_) -> a) s3
	let proj3_2 s3 = map (fun (_,b,_) -> b) s3
	let proj3_3 s3 = map (fun (_,_,c) -> c) s3
	let proj3_12 s3 = map (fun (a,b,_) -> (a,b)) s3
	let proj3_23 s3 = map (fun (_,b,c) -> (b,c)) s3

	let test (): int list list =	(* Set.test () *)
		toList (star (make[ [1]; [2;3]]) 4)
end

module type UPSetSig = (* unordered pair set *)
sig
	type 'a t
	val make : ('a * 'a) list -> 'a t
	val toList : 'a t -> ('a * 'a) list
	val empty : 'a t
	val size : 'a t -> int
	val belongs : 'a * 'a -> 'a t -> bool
	val union : 'a t -> 'a t -> 'a t
	val add : 'a * 'a -> 'a t -> 'a t
	val inter : 'a t -> 'a t -> 'a t
	val diff : 'a t -> 'a t -> 'a t
	val subset : 'a t -> 'a t -> bool
	val map : ('a * 'a -> 'b * 'b) -> 'a t -> 'b t
	val filter : ('a * 'a -> bool) -> 'a t -> ('a * 'a) Set.t
	val for_all : ('a * 'a -> bool) -> 'a t -> bool
	val exists : ('a * 'a -> bool) -> 'a t -> bool
	val exists : ('a * 'a -> bool) -> 'a t -> bool
	val flatten : 'a t t -> 'a t
	val flatMap : ('a -> 'b t) -> 'a t -> 'b t
	val iter : ('a * 'a -> unit) -> 'a t -> unit
	val partition : ('a * 'a -> bool) -> 'a t -> ('a * 'a) Set.t * ('a * 'a) Set.t
	val combinations : 'a t -> 'b t -> ('a * 'b) t
	val star : 'a list t -> int -> 'a list t
	val allDistinct : ('a * 'a -> 'b) -> 'a t -> bool
	val hasDuplicates : 'a t -> bool
	val validate : ('a * 'a) list -> string -> 'a t
	val test: unit -> (int * int) list
end

module UPSet : UPSetSig =
struct
	type 'a t = ('a*'a) Set.t

	(* invariant: a < b for all pairs (a,b) *)
	let ord (a,b) = if a < b then (a, b)		(* keep *)
					else if b < a then (b, a)	(* swap *)
					else Error.fatal "UPSet.ord" (* error *)

	let make (l: ('a*'a) list): 'a t =
		let l1 = List.filter (fun (a,b) -> a <> b) l in
		let l2 = List.map ord l1 in
			Set.make l2
	let toList (s: 'a t): ('a*'a) list = Set.toList s

	let empty: 'a t = Set.empty
	let size (s: 'a t): int = Set.size s
	let belongs (v: 'a*'a) (s: 'a t): bool = Set.belongs (ord v) s
	let union (s1: 'a t) (s2: 'a t): 'a t = Set.union s1 s2
	let add (v: 'a*'a) (s: 'a t): 'a t = Set.add (ord v) s
	let inter (s1: 'a t) (s2: 'a t): 'a t = Set.inter s1 s2
	let diff (s1: 'a t) (s2: 'a t): 'a t = Set.diff s1 s2
	let subset (s1: 'a t) (s2: 'a t): bool = Set.subset s1 s2

	let map f (s: 'a t) = make (Set.toList (Set.map f s))
	let filter f (s: 'a t) = Set.filter f s
	let for_all f (s: 'a t) = Set.for_all f s
	let exists f (s: 'a t) = Set.exists f s
	let flatten (ss: 'a t t) = Error.fatal "UPSet.flatten"
	let flatMap f (s: 'a t) = Error.fatal "UPSet.flatMap"
	let iter f (s: 'a t) = Set.iter f s
	let partition f (s: 'a t) = Set.partition f s
	let combinations (s1: 'a t) (s2: 'b t): ('a * 'b) t = Error.fatal "UPSet.combinations"
	let star (s: 'a list t) (n: int): 'a list t = Error.fatal "UPSet.star"

	let allDistinct f (s: 'a t) = Set.allDistinct f s
	let hasDuplicates (s: 'a t): bool = Set.hasDuplicates s
	let validate (l: ('a*'a) list) (culprit: string): 'a t = Error.fatal "UPSet.validate"
	let test () =	(* UPSet.test () *)
		toList (make [(1,1);(1,2);(2,2);(3,2);(3,2);(2,3)])
end


