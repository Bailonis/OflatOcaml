# 1 "src/OCamlFlat.ml"
(*
 * OCamlFlat.ml
 *
 * This file is part of the OCamlFLAT library
 *
 * LEAFS project (partially supported by the OCaml Software Foundation) [2020/21]
 * FACTOR project (partially supported by the Tezos Foundation) [2019/20]
 *
 * NOVA LINCS - NOVA Laboratory for Computer Science and Informatics
 * Dept. de Informatica, FCT, Universidade Nova de Lisboa.
 *
 *
 * This software is distributed under the terms of the GPLv3 license.
 * See the included LICENSE file for details.
 *
 *  Written by Artur Miguel Dias (amd)
 *)

(*
 * ChangeLog:
 *
 * feb/2021 (amd) - New module.
 *)

let ocamlFlatVersion = "1.0"
# 1 "src/Configuration.ml"
(*
 * Configuration.ml
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
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlatSupport.ml".
 *)

module type ConfigurationSig =
sig
	val diagnosticsOn : unit -> bool
end

module Configuration : ConfigurationSig =
struct
	let automaticDiagnostics = ref true

	let diagnosticsOn () = !automaticDiagnostics
end
# 1 "src/Error.ml"
(*
 * Error.ml
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
 * jan/2024 (amd) - Error groupings and support for setting of viewer.
 * jul/2021 (amd) - Simplified module.
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlatSupport.ml".
 *)

(*
 * Description: Supports a log of errors. Probably, a text-based application
 * will use the error log differently from a graphical-based application.
 * The errors are handled in a imperative style to simplify the signature of
 * many functions - this modules implements a kind of error log monad.
 *)


module ErrorViewer =
struct
	let errorViewer: (string -> unit) ref =
		ref print_string

	let quietViewer (_: string): unit =
		()

	let defaultViewer (mesg: string): unit =
		print_string mesg

	let setViewer (f: string -> unit): unit =
		errorViewer := f

	let adjust (mesg: string) =
		let len = String.length mesg in
		let last = if len > 0 then mesg.[len-1] else ' ' in
			if len = 0 then
				"EMPTY MESG"
			else if last = '.' then
				mesg ^ "\n"
			else
				mesg ^ ".\n"

	let view (mesg: string): unit =
		if Configuration.diagnosticsOn () then
			!errorViewer (adjust mesg)
		
	let fatal (mesg: string) =
		view ("FATAL ERROR - " ^ mesg);
		failwith mesg

	let warning (mesg: string) =
		view ("WARNING - " ^ mesg);
end


module ErrorGrouping =
struct
	open ErrorViewer

	let gouping: bool ref =
		ref false

	let errors: string list ref =
		ref []

	let startGroup (): unit =
		gouping := true;
		errors := []

	let makeMesg (culprit: string) (str: string) =
		if !gouping || culprit = "" || culprit = "_" then " - " ^ str ^ "\n"
		else culprit ^ " - " ^ str ^ "\n"

	let error (culprit: string) (str: string) (res: 'a): 'a =
		let mesg = makeMesg culprit str in
			(if !gouping then
				errors := !errors @ [mesg]
			else
				view mesg);
			res

	let endGroup (expectedKind: string) (name: string): bool =
		gouping := false;
		if !errors = [] then
			true
		else
			let mesg =
				  "--------------------------\n"
				^ expectedKind^" \""^name^ "\" has errors:\n"
				^ String.concat "" !errors
				^ "--------------------------\n"
			in view mesg;
			errors := [];
			false

	let get (): string list =
		!errors
end

module Error =
struct
	open ErrorViewer
	open ErrorGrouping

	let quietViewer = quietViewer
	let defaultViewer = defaultViewer
	let setViewer = setViewer

	let startGroup = startGroup
	let error = error
	let endGroup = endGroup
	let get = get
		
	let fatal = fatal
	let warning = warning
end
# 1 "src/Set.ml"
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
 

# 36 "src/Set.ml"
module type SetSig =
sig

	
# 40 "src/Set.ml"
 type 'a t (* opaque *)

	
# 45 "src/Set.ml"
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


# 1 "src/BasicTypes.ml"
(*
 * BasicTypes.ml
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
 * apr/2022 (amd) - The type 'symbol' is now opaque type an can be internally
 *						represented using a char or a string. Required several changes
 *						all over the code of several modules.
 * mar/2021 (amd) - New types 'property', 'properties'.
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlatSupport.ml".
 *)

(*
 * Description: Some types and constants used across all the modules.
 *)


# 36 "src/BasicTypes.ml"
module type SymbolOpaqueSig =
sig

	
# 40 "src/BasicTypes.ml"
 type symbol (* opaque *)

	
# 48 "src/BasicTypes.ml"
 type symbolX = string
	
# 50 "src/BasicTypes.ml"
 val char2symb : char -> symbol
	val symb2char : symbol -> char
	val str2symb : string -> symbol
	val symb2str : symbol -> string

	val symbolTypeName : string
	val symbDisplayQuote: string
	
	val symbI : symbolX -> symbol
	val symbX : symbol -> symbolX
end

module SymbolOpaque : SymbolOpaqueSig =
struct
	
# 77 "src/BasicTypes.ml"
 type symbol = string
	type symbolX = string

	let char2symb c: symbol = Char.escaped c
	let symb2char s: char = if String.length s > 0 then String.get s 0 else '?'
	let str2symb s: symbol = s
	let symb2str s: string = s

	let symbolTypeName = "string"
	let symbDisplayQuote = "\"" 

	
# 89 "src/BasicTypes.ml"
 (* Internalize/Externalize *)
	let symbI (x: symbolX): symbol = x
	let symbX (s: symbol): symbolX = s
end

module Symbol =
struct
	include SymbolOpaque

	type 'a set = 'a Set.t
	
	type symbols = symbol set

	let symb (s: string): symbol  = str2symb s

	let epsilon: symbol = symb "~" (* used for representing the empty transitions *)
	let dollar: symbol = symb "$"
	let empty: symbol = symb "B"

	let str2symbX (s: string): symbolX = symbX (str2symb s)
	let symbX2str (s: symbolX): string = symb2str (symbI s)

	let symbolsI (ss: symbolX list): symbols = Set.make (List.map symbI ss)
	let symbolsX (ss: symbols): symbolX list = List.map symbX (Set.toList ss)

	(* Display *)
	let listD f l = "[" ^ (String.concat "; " (List.map f l)) ^ "]"
	let symbD (s: symbol): string = symbDisplayQuote ^ (symb2str s) ^ symbDisplayQuote
	let symbXD (s: symbolX): string = symbDisplayQuote ^ (symbX2str s) ^ symbDisplayQuote
	let symbolsXD (l: symbolX list): string = listD symbXD l
	let symbolsD (s: symbols): string = listD symbD (Set.toList s)
end

module Variable =
struct
	open Symbol
	
	type variable = symbol
	type variableX = symbolX
	type variables = variable set
	
	let draftVar: variable = symb "_"
end

module BString =
struct
	open Symbol

	type strings = string set
	
	(* Display *)
	let strD (s: string): string = "\"" ^ s ^ "\""
	let stringsD (l: string list) = listD strD l
end

module Word =
struct
	open Symbol
	
	type word = symbol list
	type wordX = symbolX list
	type words = word set

	let wordX2word = List.map symbI
	let word2wordX = List.map symbX
	
	let str2word (s: string): word =
		List.init (String.length s) (fun i -> char2symb s.[i])
	let word (s: string): word = str2word s

	let word2str (w: word): string =
		let strs = List.map symb2str w in
			String.concat "" strs
		
	let symbols (s: string): symbols = Set.make (word s)

	(* Internalize/Externalize *)
	let wordI = str2word
	let wordX = word2str
	let wordsI (ss: string list): words = Set.make (List.map str2word ss)
	let wordsX (ws: words): string list = List.map word2str (Set.toList ws)
end

module type StateOpaqueSig =
sig
	open Symbol
	
	type state = string (* will be opaque *)
	type states = state set
	
	val state2str : state -> string
	val str2state : string -> state
	val state : string -> state
	val draftState: state
end

module StateOpaque: StateOpaqueSig =
struct
	open Symbol
	
	type state = string
	type states = state set

	let state2str (s: state): string = s
	let str2state (s: string): state = s
	let state (s: string): state = str2state s

	let draftState: state = state "_"
	
	(* Display *)
	let stateXD (s: state): string = "\"" ^ (state2str s) ^ "\""
	let statesXD (l: state list) = listD stateXD l
end

module State =
struct
	include StateOpaque
	open Symbol
	
	(* Display *)
	let stateXD (s: state): string = "\"" ^ (state2str s) ^ "\""
	let statesXD (l: state list) = listD stateXD l
end

module Property =
struct
	open Symbol
	
	type property = string
	type properties = property set
end

module Path =
struct
	open Symbol
	
	type 'config path = 'config list
	type 'configX pathX = 'configX list

	let pathX (configX: 'config -> 'configX) (p: 'config path): 'configX pathX =
		List.map configX p
end

module Trail =
struct
	open Symbol
	
	type 'config trail = 'config set list
	type 'configX trailX = 'configX list list

	let trailX (configX: 'config -> 'configX) (t: 'config trail): 'configX trailX =
		List.map (fun cs -> List.map configX (Set.toList cs)) t
end

module Direction =
struct
	type direction = L | S | R

(*	
	let direction2string (dir: direction): string =
		List.assoc dir [(L,"L");(S,"S");(R,"R")]
	let string2direction (dirS: string) : direction =
		List.assoc dirS [("L",L);("S",S);("R",S)]
	let char2direction (dirC: char) : direction =
		List.assoc dirC [('L',L);('S',S);('R',S)]
	let charIsDirection (dirC: char) : bool =
		List.mem dirC ['L'; 'S'; 'R'] *)
		
	let allDirections =
		Set.make [L; S; R]
	let isDirX (dirX: string): bool =
		List.mem dirX ["L"; "S"; "R"]
	let dirI (dirX: string): direction =
		List.assoc dirX [("L",L);("S",S);("R",R)]
	let dirX (dir: direction): string =
		List.assoc dir [(L,"L");(S,"S");(R,"R")]
end

module ToScreen =
struct
	open Word
	
	let pairS (a: string) (b: string): string =
		"(" ^ a ^ ", " ^ b ^ ")"
		
	let wordS (w: word): string = 
		wordX w
		
	let listS (l: string list): string =
		"[" ^ String.concat ", " l ^ "]"
		
	let setS (s: string Set.t): string =
		"{" ^ String.concat ", " (Set.toList s) ^ "}"

	let confsS (confS: 'config -> string) (c: 'config Set.t): string =
		setS (Set.map confS c)
end

module BasicTypes =
struct
	include Symbol
	include Variable
	include BString
	include Word
	include State
	include Property
	include Path
	include Trail
	include Direction
	include ToScreen
end
# 1 "src/Util.ml"
(*
 * Util.ml
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
 * may/2021 (amd) - Lots of miscellaneous new stuff.
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlatSupport.ml".
 *)

(*
 * Description: Miscellaneous utility functions. 
 *
 * TODO: Check if this is the right place for some of this functions.
 *)
 
open BasicTypes

module IdGenerator =
struct
	let current = ref 0

	let reset () =
		current := 0

	let gen (s: string) =
		let res = Printf.sprintf "%s%02d" s (!current) in
			current := !current+1;
			res
	
	let genVar (s: string) =
		"<"  ^ gen s ^ ">"
end

module type RuntimeControlSig =
sig
	val start: unit -> unit
	val update: int -> unit
	val giveUp: unit -> bool
	val stats: unit -> bool * int * float
end

module RuntimeControl : RuntimeControlSig =
struct
	let _CONFIGS_ALLOWANCE = 50000
	let _TIME_ALLOWANCE = 10.0
	
	let timeStart = ref 0.0
	let exactResult = ref false
	let runconfigs = ref 0
	let runtime = ref 0.0		(* in seconds *)

	let start () =
		timeStart := Sys.time();
		exactResult := true;
		runconfigs := 0;
		runtime := 0.0

	let update n =
		runconfigs := !runconfigs + n;
		runtime := Sys.time() -. !timeStart;
		if false then
			Printf.printf "(%d, %d, %f, [%d])\n" n !runconfigs !runtime ((Gc.quick_stat()).Gc.heap_words)

	let giveUp () =
		if !runtime > _TIME_ALLOWANCE || !runconfigs > _CONFIGS_ALLOWANCE then begin
			exactResult := false;
			true
		end
		else
			false

	let stats () =
		(!exactResult, !runconfigs, !runtime)
end

(*
ORIGINAL

	let giveUp n =	
		runconfigs := !runconfigs + n;
		runtime := Sys.time() -. !timeStart;
		(*Printf.printf "(%6d, %f)\n" !configs !time;*)
		if !runtime > _TIME_ALLOWANCE || !runconfigs > _CONFIGS_ALLOWANCE then begin
			exactResult := false;
			true
		end
		else
			false


*)

module UtilStrings =
struct
	let stripChars (s: string) (cs: string): string =
		let len = String.length s in
		let j = ref 0 in
		let res = Bytes.create len in
			for i = 0 to len-1 do
				if not (String.contains cs s.[i]) then begin
					Bytes.set res !j s.[i];
					j := !j + 1
				end
			done;
			Bytes.to_string (Bytes.sub res 0 !j)

	let stripHead (s: string): string =
		let len = String.length s in
		let n = ref 0 in
		let skip = ref (-1) in
		let j = ref 0 in
		let res = Bytes.create len in
			for i = 1 to len-1 do
				if !skip < 0 then begin
					if s.[i] = '\t' then
						n := !n + 1
					else
						skip := 0
				end;
				if !skip >= 0 then begin
					if !skip > 0 && s.[i] = '\t' then
						skip := !skip - 1
					else begin
						if s.[i] = '\n' then
							skip := !n
						else ();
						Bytes.set res !j s.[i];
						j := !j + 1
					end
				end
			done;
			Bytes.to_string (Bytes.sub res 0 !j)

	let capitalize (s: string): string =
		let l = String.split_on_char ' ' s in
		let l = List.map String.capitalize_ascii l in
			String.concat "" l
	
	let rec wrap (s: string) (width: int): string =
		let cut =
			if (String.length s) < width then
				0
			else
				let last = min width (String.length s - 1) in
				let cut = try String.rindex_from s last ' ' with _ -> 0 in
				if cut = 0 then
					try String.index_from s last ' ' with _ -> 0
				else
					cut
		in
			if cut = 0 then
				s
			else
				let head = String.sub s 0 cut in
				let tail = String.sub s (cut+1) (String.length s - cut - 1) in
					head ^ "\n" ^ wrap tail width
end

module UtilOps =
struct
	let flatMap (f: 'a -> 'b list) (l: 'a list): 'b list =
		List.flatten (List.map f l)

	let addAll (symb: 'a) (ll: 'a list list): 'a list list =
		List.map (fun l -> symb::l) ll

	let concatAll (w: 'a list) (ll: 'a list list): 'a list list =
		List.map (fun l -> w@l) ll

	let distrib2 (f: 'a -> 'b -> 'c) ((a: 'a), (b: 'b)): 'c =
		f a b

	let rec fixedPoint (f: 'a -> 'a) (x: 'a): 'a =
		let next = f x in
			if x = next then x
			else fixedPoint f next
	
	let indexOf (e: 'a) (l: 'a list): int =
		let rec index e l n =
			match l with
				[] -> -1
				|x::xs -> if e = x then n else index e xs (n+1)
		in
			index e l 0
end

module UtilFiles =
struct
	let loadFile (filename: string): string =
		try
			let ic = open_in filename in
			let n = in_channel_length ic in
			let s = Bytes.create n in
				really_input ic s 0 n;
				close_in ic;
				Bytes.to_string s
		with
			Sys_error str ->
				Error.error "FileReader" str ""


	let rec print (l: string list): unit =
		match l with
		| [] -> ()
		| x::xs -> print_string x; print xs

	let println (l: string list): unit =
		print l ;
		print_newline()

	let sep (): unit =
		println ["------------------------------------------------"]

	let header (str: string): unit =
		sep ();
		println [str]

	let printAlphabet (a: symbols): unit =
		Set.iter (fun x -> print [symb2str x; ", "]) a;
		println []

	let printStates (st:states): unit =
		Set.iter (fun x -> print [state2str x; ", "]) st;
		println []

	let printTransition (a:string) (b:symbol) (c:string): unit =
		println ["("; a; ", "; symb2str b; ", "; c; ")"]

	let printWord (w:word): unit =
		println ["'"; word2str w; "'"]

	let printWords (s: words): unit =
		Set.iter printWord s
		
	let printString (s: string): unit =
		println ["'"; s; "'"]

	let printStrings (s: strings): unit =
		Set.iter printString s
		
	let show (s: string): unit =
		print_string ("|" ^ s ^ "|\n")
		
	let handleHomeDir (s: string): string =
		match String.length s with
		| 0 ->
			""
		| 1 ->
			if s = "~" then Sys.getenv("HOME") else s
		| n ->
			if s.[0] = '~' then
				if s.[1] = '/' then
					Sys.getenv("HOME") ^ String.sub s 1 (n - 1)
				else
					"/home/" ^ String.sub s 1 (n - 1)
			else s
end

module Util =
struct
	include UtilStrings
	include UtilOps
	include UtilFiles

	let testing active moduleName =
		let forceActive = false in
		let regularActive = (active && try ignore (Sys.getenv("TESTING")); true with _ -> false) in
		let active = forceActive || regularActive in
			if active then
				header ("### Testing \"" ^ moduleName ^ "\" ###");
			active
end

module UtilTests : sig end =
struct
	let active = false

	let test0 () =
		Util.println [Util.loadFile "examples/fa_abc.json"]

	let test1 () =
		let a = word2str [symb "e";symb "r";symb "t"] in
		let b = word2str [symb "4";symb "5";symb "y"] in
			Util.println [a; b]

	let runAll : unit =
		if Util.testing active "Util" then begin
			test0 ();
			test1 ()
		end
end
# 1 "src/Scanner.ml"
(*
 * Scanner.ml
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
 * jan/2021 (amd) - Initial version, for the JSon parser.
 *)

(*
 * Description: Simple lexical analyzer that assumes that the tokens are
 * the individual non-blank characters. The function getToken is available
 * to handle the rare cases where we need a multi-char token. This module is
 * suitable for the three parsers defined in the OCamlFLAT library.
 * The tokens are handled in a imperative style to simplify the signature of
 * of the client parsing functions.
 *)

module CharType =
struct
	let isBlank (c: char): bool =
		c = ' ' || c = '\t' || c = '\n' || c = '\r'

	let isAlpha (c: char): bool =
		'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z'

	let isDigit (c: char): bool =
		'0' <= c && c <= '9'

	let isAlphaNum (c: char): bool =
		isAlpha c || isDigit c

	let isId (c: char): bool =
		isAlpha c || isDigit c || c = '_'

	let asStr (c: char): string =
		Char.escaped c

	let strQuoted (s: string): string =
		"'" ^ s ^ "'"

	let asStrQuoted (c: char): string =
		strQuoted (Char.escaped c)
end

module ScannerPrivate =
struct
	open CharType

	let parserName = ref ""
	let inputString = ref ""
	let inputStringLength = ref 0
	let inputStringPosition = ref 0

	let expecting (exp: string) (got: char): 'a =
		let g = if got = ' ' then "'EOL'" else "'" ^ asStr got ^ "'" in
		let mesg ="Expecting " ^ exp ^ ", got " ^ g in
			Error.error !parserName mesg ();
			raise Not_found

	let invalid (str: string): 'a =
		Error.error !parserName str ();
		raise Not_found

	let isInside (): bool =
		!inputStringPosition < !inputStringLength

	let slice (from: int): string =
		let len = !inputStringPosition - from in
			String.sub !inputString from len

	let start (name: string) (s: string): unit =
		parserName := name;
		inputString := s;
		inputStringLength := String.length s;
		inputStringPosition := 0

	let skip (): unit =
		inputStringPosition := !inputStringPosition + 1

	let current (): char =
		String.get !inputString !inputStringPosition

	let skipWhile good =
		while isInside () && good (current ()) do skip() done

	let skipBlanks (): unit =
		skipWhile isBlank

	let peek (): char =
		skipBlanks ();
		if isInside () then
			current ()
		else
			' '

	let get (): char =
		let res = peek() in
			skip();
			res

	let getToken (good: char -> bool): string =
		let start = !inputStringPosition in
			skipWhile good;
			slice start
	
	let getId (): string =
		getToken isId

	let getUntil (ch: char): string =
		getToken (fun c -> c <> ch)

	let getChar (e: char): char =
		if peek() = e then
			get ()
		else
			expecting (asStrQuoted e) (peek())

	let getOne (l: char list): char =
		let rec charListAsStr (l: char list): string =
			match l with
			| [] -> ""
			| [x] -> asStrQuoted x
			| [x; y] -> asStrQuoted x  ^ " or " ^ asStrQuoted y
			| x::xs -> asStrQuoted x ^ ", " ^ charListAsStr xs
		in	
			if List.mem (peek()) l then
				get ()
			else
				expecting (charListAsStr l) (peek())

	let getAlpha (): char =
		if isAlpha (peek()) then
			get ()
		else
			expecting "alphabetic" (peek())

	let getInt (): int =
		let digits = getToken isDigit in
			if digits = "" then
				expecting "integer" (peek())
			else
				int_of_string digits					

	let getCharInt (): char * int =
		let a = getAlpha () in
			if isDigit (current ()) then
				(a, getInt ())
			else
				(a, -1)
	
	let getDelim (a: char) (b: char): string =
		let _ = getChar a in
		let res = getToken (fun c -> c <> b) in
			if peek () = b then (
				skip ();
				res
			)
			else
				expecting ("closing " ^ asStrQuoted b) (peek ())

	let rec checkStr (str: string) (i: int): bool =
		if String.length str = i then true
		else if str.[i] <> current () then false
		else (skip (); checkStr str (i+1))

	let getStr (str: string): unit =
		if (peek ()) = ' ' || not (checkStr str 0) then
			expecting (strQuoted str) (peek ())		

	let expecting0 (exp: string): 'a =
		expecting exp (peek ())

	let rubbish (str: string): 'a =
		invalid ("Rubbish [" ^ asStrQuoted (peek ()) ^ "] " ^ str)
end


module Scanner =
struct
	open ScannerPrivate

	let expecting = expecting  (* discontinued *)
	let invalid = invalid

	let start = start
	let skip = skip
	let peek = peek
	let curr = peek  (* discontinued *)
	let get = get
	let getId = getId
	let getUntil = getUntil

	let getChar = getChar
	let getOne = getOne
	let getAlpha = getAlpha
	let getInt = getInt
	let getCharInt = getCharInt
	let getDelim = getDelim
	let getStr = getStr

	let expecting0 = expecting0
	let rubbish = rubbish
end
# 1 "src/JSon.ml"
(*
 * JSon.ml
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
 * apr/2022 (amd) - Added the "make" family of functions. Required several changes
 *						all over the code of several modules.
 * may/2021 (amd) - Added a second parser, for OCaml values syntax. The output
 *                  is regular JSon.
 * jan/2021 (amd) - Added a very simple recursive descent parser for JSon.
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlatSupport.ml".
 *)

(*
 * Description: Very simple JSon parser, plus some JSon handling functions.
 *)

open BasicTypes

(*
module type JSonSig =
sig
	type t =
		| JNull
		| JString of string
		| JAssoc of (string * t) list
		| JList of t list

	val parse : string -> t
	val parseOon : string -> t
	val fromFile : string -> t

	val toStringN : int -> t -> string
	val toString : t -> string
	val show : t -> unit
	val remove : t -> string list -> t

	val isNull : t -> bool
	val hasField : t -> string -> bool
	val getField: string -> t -> t
	
	val fieldSymbol : t -> string -> symbol
(*	val fieldSymbolList : t -> string -> symbol list *)
	val fieldSymbolSet : t -> string -> symbols
	
	val fieldString : t -> string -> string
(*	val fieldStringList : t -> string -> string list *)
	val fieldStringSet : t -> string -> strings

	val fieldState : t -> string -> state
(*	val fieldStateList : t -> string -> state list *)
	val fieldStateSet : t -> string -> states
	
	val fieldBool : t -> string -> bool

(*	val fieldTriplesList : t -> string -> (state * symbol * state) list *)
	val fieldTriplesSet : t -> string -> (state * symbol * state) set

(*	val fieldQuintupletsList : t -> string -> (state * symbol * symbol * state * symbol set) list *)
	val fieldQuintupletsSet : t -> string -> (state * symbol * symbol * state * word) set


	val fieldTMTransitionSet : t -> string -> (state * symbol * state * symbol * direction) set
	
	val append: t -> t -> t
	
	val makeSymbol : symbol -> t
	val makeSymbolSet : symbols -> t
	val makeString : string -> t
	val makeStringSet : strings -> t
	val makeState : state -> t
	val makeStateSet : states -> t
	val makeBool : bool -> t
    val makeTriplesSet : (state * symbol * state) set -> t
    val makeQuintupletsSet : (state * symbol * symbol * state * word) set -> t
	val makeTMTransitionsSet : (state * symbol * state * symbol * direction) set -> t
	val makeAssoc : (string * t) list -> t
end
*)

module JSon =
struct
	open Scanner

	type t =
		| JNull
		| JString of string
		| JAssoc of (string * t) list
		| JList of t list

	let parseString delim =
		skip(); (* skip quotation mark *)		
		let tk = getUntil delim in
			match peek () with
			| x when x = delim -> skip(); tk
			| _ -> expecting0 ("closing '" ^ (Char.escaped delim) ^ "'")
				
	let parseWord () =
		getId ()

	let parseLabel () =
		match curr() with
			| '"' -> parseString '"'
			| 'a'..'z' -> parseWord ()
			| err -> expecting "'STRING' or '}'" err

	let checkEOF () =
		match curr() with
			| ' ' -> ()
			| err -> expecting "'EOF'" err


	module JSonParsing = (* JSon syntax *)
	struct
		let rec parsePair () =
			let label = parseLabel () in
				match curr() with
					| ':' -> skip(); (label, parseJSon ())
					| err -> expecting "':'" err

		and parseAssocCont () =
			let p = parsePair () in
				match curr() with
					| ',' -> skip(); p::parseAssocCont ()
					| '}' -> skip(); [p]
					| err -> expecting "',' or '}'" err

		and parseAssoc () =
			skip();	(* skip { *)
			match curr() with
				| '}' -> skip(); []
				| ' ' -> expecting "'}' or 'STRING'" ' '
				| _ -> parseAssocCont ()

		and parseListCont () =
			let j = parseJSon () in
				match curr() with
					| ',' -> skip(); j::parseListCont ()
					| ']' -> skip(); [j]
					| err -> expecting "',' or ']'" err

		and parseList () =
			skip();	(* skip [ *)
			match curr() with
				| ']' -> skip(); []
				| ' ' -> expecting "']' or 'JSON'" ' '
				| _ -> parseListCont ()

		and parseJSon s =
			match curr() with
				| '"' -> JString (parseString '"')
				| '[' -> JList (parseList ())
				| '{' -> JAssoc (parseAssoc ())
				| err -> expecting "'JSON'" err

		let parse s =
			Scanner.start "JSon" s;
			try
				let j = parseJSon () in
					checkEOF (); j
			with Not_found ->
				JNull
	end

	module OCamlValueParsing = (* OCaml value syntax *)
	struct
		let rec parsePair () =
			let label = parseLabel () in
				match curr() with
					| '=' -> skip(); (label, parseOon ())
					| err -> expecting "'='" err

		and parseAssocCont () =
			let p = parsePair () in
				match curr() with
					| ';' -> skip(); p::parseAssocCont ()
					| '}' -> skip(); [p]
					| err -> expecting "';' or '}'" err

		and parseAssoc () =
			skip();	(* skip { *)
			match curr() with
				| '}' -> skip(); []
				| ' ' -> expecting "'}' or 'STRING'" ' '
				| _ -> parseAssocCont ()

		and parseListCont () =
			let j = parseOon () in
				match curr() with
					| ';' -> skip(); j::parseListCont ()
					| ']' -> skip(); [j]
					| err -> expecting "';' or ']'" err

		and parseList () =
			skip();	(* skip [ *)
			match curr() with
				| ']' -> skip(); []
				| ' ' -> expecting "']' or 'Oon'" ' '
				| _ -> parseListCont ()

		and parseTupleCont () =
			let j = parseOon () in
				match curr() with
					| ',' -> skip(); j::parseTupleCont ()
					| ')' -> skip(); [j]
					| err -> expecting "',' or ')'" err

		and parseTuple () =
			skip();	(* skip [ *)
			match curr() with
				| ')' -> skip(); []
				| ' ' -> expecting "')' or 'Oon'" ' '
				| _ -> parseTupleCont ()

		and parseOon s =
			match curr() with
				| '"' -> JString (parseString '"')
				| '\''-> JString (parseString '\'')
				| '[' -> JList (parseList ())
				| '(' -> JList (parseTuple ())
				| '{' -> JAssoc (parseAssoc ())
				| err -> expecting "'OON'" err
				
		let parse s =
			Scanner.start "OON" s;
			try
				let j = parseOon () in
					checkEOF (); j
			with Not_found ->
				JNull
	end

	let parse s =
	    JSonParsing.parse s

	let parseOon s =
		OCamlValueParsing.parse s

	let fromFile filename =
		let txt = Util.loadFile filename in
			if txt = "" then JNull
			else parse txt

(* PRETTY PRINT *)
	let tab n =
		String.make n '\t'

	let isComplex j =
		match j with
		| JList l -> true
		| JAssoc l -> true
		| _ -> false

	let rec textual (tab1: int) (tab2: int) (j: t) : string =
		tab tab1
		^
		match j with
		| JNull ->
			"null"
		| JString s ->
				"\"" ^ s ^ "\""
		| JList l when List.exists isComplex l ->
				let elems = List.map (textual (tab2+1) (tab2+1)) l in (
						"[\n"
						^ String.concat (",\n") elems ^ "\n"
						^ tab tab2 ^ "]"
					)
		| JList l ->
				let elems = List.map (textual 0 0) l in
					("[" ^ String.concat ", " elems ^ "]")
		| JAssoc [] ->
				"{}"
		| JAssoc l ->
				let field (s,j) = tab (tab2+1) ^ s ^ " : " ^ textual 0 (tab2+1) j in
					let elems = List.map field l in (
						"{\n"
						^ String.concat ",\n" elems ^ "\n"
						^ tab tab2 ^ "}"
					)

	let rec textualOCaml (tab1: int) (tab2: int) (j: t) : string =
		tab tab1
		^
		match j with
		| JNull ->
			"null"
		| JString s ->
				"\"" ^ s ^ "\""
		| JList l when List.exists isComplex l ->
				let elems = List.map (textualOCaml (tab2+1) (tab2+1)) l in (
						"[\n"
						^ String.concat (",\n") elems ^ "\n"
						^ tab tab2 ^ "]"
					)
		| JList l ->
				let elems = List.map (textualOCaml 0 0) l in
					("[" ^ String.concat ", " elems ^ "]")
		| JAssoc [] ->
				"{}"
		| JAssoc l ->
				let field (s,j) = tab (tab2+1) ^ s ^ " : " ^ textualOCaml 0 (tab2+1) j in
					let elems = List.map field l in (
						"{\n"
						^ String.concat ",\n" elems ^ "\n"
						^ tab tab2 ^ "}"
					)

	let toStringN n j =
		textual 0 n j

	let toString j =
		toStringN 0 j

	let show (j: t) =
		Util.println [toString j]

	let remove (j: t) r =
		match j with
		| JAssoc l ->
			JAssoc (List.filter (fun (a,_) -> not (List.mem a r)) l)
		| _ ->
			j


(* MEMBERSHIP *)
	let isNull j =
		j = JNull

	let hasField j name =
		match j with
		| JAssoc obj -> (
				try
					ignore (List.assoc name obj); true
				with Not_found -> false
			)
		| _ ->
			false

	let getField name j =
		match j with
		| JAssoc obj -> (
				try
					List.assoc name obj
				with Not_found -> JNull
			)
		| _ ->
			JNull

(* MORE *)

	let error = Error.error
	
	let dummySymb = symb "#"
	let dummyState = state "#"
	let dummyDirection = L

	let fieldSymbol (j: t) (field: string): symbol =
		match j |> getField field with
		| JNull -> error field "Missing field" dummySymb
		| JString s -> str2symb s
		| _ -> error field "Expected symbol" dummySymb

	let asSymbol (j: t) (field: string): symbol =
		match j with
		| JString s -> str2symb s
		| _ -> error field "Expected symbol" dummySymb

	let asSymbolList (j: t) (field: string): symbol list =
		match j with
		| JList l -> List.map (fun j -> asSymbol j field) l
		| _ -> error field "Expected symbol list" []

	let fieldSymbolList (j: t) (field: string): symbol list =
		match j |> getField field with
		| JNull -> error field "Missing field" []
		| JList l -> List.map (fun j -> asSymbol j field) l
		| _ -> error field "Expected symbol list" []

	let fieldSymbolSet (j: t) (field: string): symbols =
		Set.validate (fieldSymbolList j field) field


	let fieldString (j: t) (field: string) =
		match j |> getField field with
		| JNull -> error field "Missing field" "#"
		| JString s -> s
		| _ -> error field "Expected string" "#"

	let asString (j: t) (field: string) =
		match j with
		| JString s -> s
		| _ -> error field "Expected string" "#"

	let fieldStringList (j: t) (field: string) =
		match j |> getField field with
		| JNull -> error field "Missing field" []
		| JList l -> List.map (fun j -> asString j field) l
		| _ -> error field "Expected string list" []

	let fieldStringSet (j: t) (field: string) =
		Set.validate (fieldStringList j field) field


	let asState (j: t) (field: string) =
		match j with
		| JString s -> state s
		| _ -> error field "Expected state" dummyState

	let fieldState (j: t) (field: string) =
		state (fieldString j field)
		
	let fieldStateList (j: t) (field: string) =
		List.map state (fieldStringList j field)
		
	let fieldStateSet (j: t) (field: string) =
		Set.validate (fieldStateList j field) field

	let fieldBool (j: t) (field: string) =
		match fieldString j field with
		| "false" -> false
		| "true" -> true
		| _ -> error field "Expected bool" false

	let fieldDirection (j: t) (field: string) =
		match fieldString j field with
		| "L" -> L
		| "S" -> S
		| "R" -> R
		| _ -> error field "Expected L|S|R" dummyDirection


	let asStateSymbolState (j: t) (field: string) =
		match j with
		| JList [a; b; c] -> (asState a field, asSymbol b field, asState c field)
		| _ -> error field "Malformed triple" (dummyState,dummySymb,dummyState)

	let fieldTriplesList (j: t) (field: string) =
		match j |> getField field with
		| JNull -> error field "Missing field" []
		| JList l -> List.map (fun j -> asStateSymbolState j field) l
		| _ -> []

	let fieldTriplesSet (j: t) (field: string) =
		Set.validate (fieldTriplesList j field) field


	let asWord (j: t) (field: string): word =
		match j with
			| JString s -> str2word s
			| _ -> error field "Expected word" []

	let asStateSymbolSymbolStateWord (j: t) (field: string) =
		match j with
		| JList [a; b; c; d; e] ->
			(	asState a field,
				asSymbol b field,
				asSymbol c field,
				asState d field,
				asWord e field
			)
		| _ -> error field "Malformed quintuplet" (dummyState,dummySymb,dummySymb,dummyState,[])

	
	let fieldQuintupletsList (j: t) (field: string) =
		match j |> getField field with
		| JNull -> error field "Missing field" []
		| JList l -> List.map (fun j -> asStateSymbolSymbolStateWord j field) l
		| _ -> []

	let fieldQuintupletsSet (j: t) (field: string) =
		Set.validate (fieldQuintupletsList j field) field

	let append j1 j2 =
		match j1, j2 with
		| JAssoc l1, JAssoc l2 -> JAssoc (l1 @ l2)
		| _, _ -> Error.fatal "JSon.append: not Assoc"

	let makeSymbol s =
		JString (symb2str s)

	let makeSymbolList (l: symbol list) =
		JList (List.map makeSymbol l)

	let makeSymbolSet (s: symbols) =
		makeSymbolList (Set.toList s)
		
	let makeString s =
		JString s

	let makeStringSet s =
		JList (List.map makeString (Set.toList s))
		
	let makeState s =
		makeString (state2str s)
		
	let makeStateSet s =
		JList (List.map makeState (Set.toList s))

	let makeBool b =
		makeString (if b then "true" else "false")
		
	let makeTriplesSet s =
		JList (List.map (fun (a,b,c) ->
				JList [JString (state2str a); JString (symb2str b);
						JString (state2str c)]) (Set.toList s))

	let makeQuintupletsSet s =
		JList (List.map (fun (a,b,c,d,e) ->
							JList [	JString (state2str a);
									JString (symb2str b);
									JString (symb2str c);
									JString (state2str d);
									JString (word2str e)])
							(Set.toList s))

	let makeAssoc l =
		JAssoc l
end

# 1 "src/Examples.ml"
(*
 * Examples.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
 * dec/2020 (amd) - Collected the examples in a single module.
 * sep/2019 (jg) - Initial version, each example in an individual file.
 *)

(*
 * Description: A set of good predefined examples.
 *
 * TODO: Check if these examples are really good and improve.
 *)

module type ExamplesSig =
sig
	val examples : string list
	val example : string -> string
	val jsonExample : string -> JSon.t
	val see : string -> unit
end

module Examples : ExamplesSig =
struct
(* FA examples *)
	let dfa_1 = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "dfa_1",
			alphabet: ["a", "b"],
			states : ["START", "A", "B", "C"],
			initialState : "START",
			transitions : [
					["START", "a", "A"], ["A", "b", "B"], ["B", "a", "C"], ["C", "b", "B"],
					["C", "a", "A"]
				],
			acceptStates : ["START", "B", "C"]
		} |}

	let dfa_2 = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "dfa_2",
			alphabet: ["0", "1"],
			states : ["START", "1", "2", "3"],
			initialState : "START",
			transitions : [
				["START", "1", "1"], ["1", "1", "START"], ["1", "0", "2"], ["2", "0", "1"],
				["2", "1", "3"], ["3", "1", "2"], ["3", "0", "START"], ["START", "0", "3"]
			],
			acceptStates : ["1"]
			} |}

	let dfa_astar = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "dfa_astar",
			alphabet: ["a"],
			states : ["START"],
			initialState : "START",
			transitions : [
				["START", "a", "START"]
			],
			acceptStates : ["START"]
			} |}

	let fa_abc = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "fa_abc",
			alphabet : ["a", "b", "c", "d"],
			states : ["START", "A", "AB", "SUCCESS"],
			initialState : "START",
			transitions : [
					["START","a","A"], ["START","b","START"], ["START","c","START"], ["START","d","START"],
					["A","a","A"], ["A","b","AB"], ["A","c","START"], ["A","d","START"],
					["AB","a","A"], ["AB","b","START"], ["AB","c","SUCCESS"], ["AB","d","START"],
					["SUCCESS","a","SUCCESS"], ["SUCCESS","b","SUCCESS"], ["SUCCESS","c","SUCCESS"], ["SUCCESS","d","SUCCESS"]
				],
			acceptStates : ["SUCCESS"]
		} |}

	let fa_error = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "fa_error",
			alphabet : ["a"],
			states : ["A"],
			initialState : "START",
			transitions : [],
			acceptStates : ["SUCCESS"]
		} |}

	let nfa_1 = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "nfa_1",
			alphabet: ["a", "b"],
			states : ["START", "A", "B"],
			initialState : "START",
			transitions : [
					["START", "a", "A"], ["A", "b", "B"], ["A", "b", "START"], ["B", "a", "START"]
				],
			acceptStates : ["START"]
			} |}

	let nfa_2 = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "nfa_2",
			alphabet : ["a", "b", "c", "d", "e"],
			states : ["START", "A", "AB", "SUCCESS", "UNREACHABLE", "UNPRODUCTIVE"],
			initialState : "START",
			transitions : [
					["START","a","A"], ["START","b","START"], ["START","c","START"], ["START","d","START"],
					["A","a","A"], ["A","b","AB"], ["A","c","START"], ["A","d","START"],
					["AB","a","A"], ["AB","b","START"], ["AB","c","SUCCESS"], ["AB","d","START"],
					["SUCCESS","a","SUCCESS"], ["SUCCESS","b","SUCCESS"], ["SUCCESS","c","SUCCESS"], ["SUCCESS","d","SUCCESS"], ["A","a","AB"], ["UNREACHABLE", "a", "SUCCESS"],
					["SUCCESS", "e", "UNPRODUCTIVE"], ["UNPRODUCTIVE", "a", "UNPRODUCTIVE"]
				],
			acceptStates : ["SUCCESS"]
		} |}

(* RE examples *)
	let re_abc = {| {
			kind : "regular expression",
			description : "this is an example",
			name : "re_abc",
			re : "((a+b)*(cd)*)*"
		} |}

	let re_complex = {| {
			kind : "regular expression",
			description : "this is a complex example",
			name : "re_complex",
			re : "(a+(b(c+d)+ea))*f*g"
		} |}

	let re_convoluted = {| {
			kind : "regular expression",
			description : "this is a convoluted example",
			name : "re_convoluted",
			re : "((((a+b)*(cd)*)*+(e(f+gh*i)*jk)*+lmn)op+q)"
		} |}

	let re_simple = {| {
			kind : "regular expression",
			description : "this is a simple example",
			name : "re_simple",
			re : "a+a*+bc*"
		} |}

	let re_astar = {| {
			kind : "regular expression",
			description : "this is a simple example",
			name : "re_astar",
			re : "a*"
		} |}

(* FE examples *)
	let fe_colors = {| {
		kind : "finite enumeration",
		description : "this is an example",
		name : "fe_colors",
		words : ["Red", "Yellow", "Blue"]
	} |}

(* CFG examples *)
	let cfg_simple = {| {
			kind : "context free grammar",
			description : "this is an example",
			name : "cfg_simple",
			alphabet : ["0", "1"],
			variables : ["S", "P"],
			initial : "S",
			rules : [	"S -> 1S0 | P",
						"P -> 0P1 | ~" ]
		} |}
		
	let cfg_balanced = {| {
			kind : "context free grammar",
			description : "CFG: Language of balanced square bracket parentheses",
			name : "cfg_balanced",
			alphabet : ["[", "]"],
			variables : ["S"],
			initial : "S",
			rules : [ "S -> [S] | SS | ~"]
		} |}

(* LL parsing *)

	let cfg_ll_thesis_g1 = {| {
			kind : "context free grammar",
			description : "Grammar G1 from thesis document",
			name : "cfg_ll_thesis_g1",
			alphabet : ["a", "b", "c"],
			variables : ["A", "B", "C", "S"],
			initial : "S",
			rules : ["A -> a", "A -> aAB", "B -> Bb", "B -> C", "C -> c", "S -> ABC"]
		} |}

	let cfg_ll_thesis_g2 = {| {
			kind : "context free grammar",
			description : "Grammar G2 from thesis document",
			name : "cfg_ll_thesis_g2",
			alphabet : ["a", "b", "c"],
			variables : ["A", "B", "C", "D", "E", "S"],
			initial : "S",
			rules : ["A -> aD", "B -> CE", "C -> c", "D -> ", "D -> AB", "E -> ", "E -> bE", "S -> ABC"]
	} |}

	let cfg_ll_1 = {| {
			kind : "context free grammar",
			description : "Example from old pratical classes",
			name : "cfg_ll_1",
			alphabet : ["(", ")", "*", "+", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9"],
			variables : ["D", "E", "F", "I", "S", "T", "X", "Y", "Z"],
			initial : "S",
			rules : ["D -> 0", "D -> 1", "D -> 2", "D -> 3", "D -> 4", "D -> 5", "D -> 6", "D -> 7", "D -> 8", "D -> 9", "E -> TX", "F -> (E)", "F -> I", "I -> DZ", "S -> E", "T -> FY", "X -> ", "X -> +TX", "Y -> ", "Y -> *FY", "Z -> ", "Z -> DZ"]
		} |}

	let cfg_ll_2 = {| {
			kind : "context free grammar",
			description : "classic grammar",
			name : "cfg_ll_2",
			alphabet : ["*", "+", "0", "1"],
			variables : ["D", "E"],
			initial : "E",
			rules : ["D -> 0", "D -> 1", "E -> D", "E -> E*E", "E -> E+E"]
		} |}

	let cfg_ll_3 = {| {
			kind : "context free grammar",
			description : "_",
			name : "cfg_ll_3",
			alphabet : ["(", ")", "*", "+", "i"],
			variables : ["E", "F", "T"],
			initial : "E",
			rules : ["E -> E+T", "E -> T", "F -> (E)", "F -> i", "T -> F", "T -> T*F"]
		} |}

	let cfg_ll_4 = {| {
			kind : "context free grammar",
			description : "_",
			name : "cfg_ll_4",
			alphabet : ["a", "b", "d", "g", "h"],
			variables : ["A", "B", "C", "S"],
			initial : "S",
			rules : ["A -> BC", "A -> da", "B -> ", "B -> g", "C -> ", "C -> h", "S -> ACB", "S -> Ba", "S -> CbB"]
		} |}

	let cfg_ll_5 = {| {
			kind : "context free grammar",
			description : "_",
			name : "cfg_ll_5",
			alphabet : ["a", "b", "c", "d", "e"],
			variables : ["A", "B", "C", "D", "E", "S"],
			initial : "S",
			rules : ["A -> ", "A -> a", "B -> ", "B -> b", "C -> c", "D -> ", "D -> d", "E -> ", "E -> e", "S -> ABCDE"]	
		} |}

	let cfg_ll_6 = {| {
			kind : "context free grammar",
			description : "Exemplo 9",
			name : "cfg_ll_6",
			alphabet : ["a", "b"],
			variables : ["A", "B", "C", "N"],
			initial : "N",
			rules : ["A -> CAC", "A -> a", "B -> CBC", "B -> b", "C -> a", "C -> b", "N -> AB", "N -> BA"]	
		} |}

(* LR parsing *)
	let cfg_lr0_thesis = {| {
			kind : "context free grammar",
			description : "This is an example for LR0",
			name : "cfg_lr0_thesis",
			alphabet : ["a", "b", "$"],
			variables : ["S", "X", "A"],
			initial : "S",
			rules : [	"S -> X$",
						"X -> XA | A",
						"A -> aXb | ab" ]
		} |}
		
	let cfg_slr1 = {| {
			kind : "context free grammar",
			description : "This is another example for SLR1",
			name : "cfg_slr1",
			alphabet : ["a", "c", "d","z", "$"],
			variables : ["T", "S","A","B"],
			initial : "T",
			rules : [	"T -> S$",
						"S -> aAc | aBd",
						"A -> z",
						"B -> z"]
		} |}
		
	let cfg_lr0_thesis = {| {
			kind : "context free grammar",
			description : "This is the example for LR0 in the thesis",
			name : "cfg_lr0_thesis",
			alphabet : ["a", "b", "$"],
			variables : ["S", "X", "A"],
			initial : "S",
			rules : [	"S -> X$",
						"X -> XA | A",
						"A -> aXb | ab" ]
		} |}
		
	let cfg_slr1_thesis = {| {
			kind : "context free grammar",
			description : "This is the example for SLR1 in the thesis",
			name : "cfg_slr1_thesis",
			alphabet : ["$","a", "b", "c"],
			variables : ["T", "S", "A", "B", "C"],
			initial : "T",
			rules : [	"T -> S$",
						"S -> aBbA | aA",
						"A -> b | ~",
						"B -> b | bC",
						"C -> c" ]
		} |}
		
	let cfg_lr1_thesis = {| {
			kind : "context free grammar",
			description : "This is the example for LR1 in the thesis",
			name : "cfg_lr1_thesis",
			alphabet : ["a", "c", "d", "z", "$"],
			variables : ["S", "X", "A", "B"],
			initial : "S",
			rules : [	"S -> X$",
						"X -> aAc | aBd | Bc",
						"A -> z",
						"B -> z"]
		} |}
		
	let cfg_lalr1_thesis = {| {
			kind : "context free grammar",
			description : "This is the example for LALR1 in the thesis",
			name : "cfg_lalr1_thesis",
			alphabet : ["c", "d", "$"],
			variables : ["S", "X","C"],
			initial : "S",
			rules : [	"S -> X$",
						"X -> CC",
						"C -> cC | d"]
		} |}
		
	let cfg_onlylr1 = {| {
			kind : "context free grammar",
			description : "This is an example for a LR1-only grammar",
			name : "cfg_onlylr1",
			alphabet : ["$", "a", "c", "d", "b", "z"],
			variables : ["S", "X", "A", "B"],
			initial : "S",
			rules : ["S -> X$", "X -> aAc", "X -> aBd", "X -> bA", "X -> bBc", "A -> z", "B -> z"]
		} |}
		
	let cfg_notlr1 = {| {
			kind : "context free grammar",
			description : "This is an example for an LR2 Grammar, so it should return 'It's not LR1'",
			name : "cfg_notlr1",
			alphabet : ["a", "c", "d", "z", "$"],
			variables : ["S", "X", "A", "B"],
			initial : "S",
			rules : [	"S -> X$",
						"X -> aAc | aBcd",
						"A -> z",
						"B -> z"]
		} |}			

(* UG examples *)
	let ug_simple = {| {
			kind : "grammar",
			description : "this is an example",
			name : "ug_simple",
			alphabet : ["0", "1"],
			variables : ["S", "P"],
			initial : "S",
			rules : [	"S -> 1S0 | P",
						"1P0 -> 0P1 | ~" ]
		} |}
		

(* Pushdown Automata *)
	let pda_WW_1 = {| {
			kind: "pushdown automaton",
			description : "this is an example",
			name : "pda_WW-1",
			inputAlphabet : ["a","b"],
			stackAlphabet: ["z","a","b"],
			states : ["S1","S2","S3","S4"],
			initialState : "S1",
			initialStackSymbol: "z",
			transitions : [
					["S1","z","a","S2","az"], 
					["S1","z","b","S2","bz"],
					["S2","a","a","S2","aa"],
					["S2","a","a","S3",""],
					["S2","a","b","S2","ba"],
					["S2","b","a","S2","ab"],
					["S2","b","b","S2","bb"],
					["S2","b","b","S3",""],
					["S3","a","a","S3",""],
					["S3","b","b","S3",""],
					["S3","z","~","S4","z"]
				],
			acceptStates : ["S1","S4"],
			criteria: "true"
		} |}

	let pda_AABB = {| {
			kind: "pushdown automaton",
			description: "this is an example",
			name: "pda_AABB",
			inputAlphabet: ["a", "b"],
			stackAlphabet: ["a", "z"],
			states: ["S1", "S2", "S3"],
			initialState: "S1",
			initialStackSymbol: "z",
			transitions: [
				["S1", "z", "a", "S1", "az"],
				["S1", "a", "a", "S1", "aa"],
				["S1", "a", "~", "S2", "a"],
				["S2", "a", "b", "S2", ""],
				["S2", "z", "~", "S3", "z"]
			],
			acceptStates: ["S3"],
			criteria: "true"
		} |}

		let pda_Explode = {| {
			kind : "pushdown automaton",
			description : "_",
			name : "pda_Explode",
			inputAlphabet : ["a"],
			stackAlphabet : ["a", "b", "z"],
			states : ["START", "A"],
			initialState : "START",
			initialStackSymbol : "z",
			transitions : [
				["START", "z", "a", "START", "az"],
				["START", "a", "a", "START", "aa"],
				["A", "a", "a", "A", "bb"],
				["A", "b", "a", "A", "aa"],
				["START", "a", "a", "A", "a"],
				["START", "a", "a", "A", "b"],
				["A", "a", "a", "START", "ab"]
			],
			acceptStates : [],
			criteria : "true"
		} |}
		
(* Turing Machine *)

   (* AMD multifita test *)
	let tm_translate_lb = {| {
		kind: "turing machine",
		description: "this is an example",
		name: "tm_translate_lb",
		entryAlphabet: ["a", "b", "[", "]"],
		tapeAlphabet: ["a", "b", "B", "[", "]"],
		empty: "B",
		states: ["q1", "q2"],
		initialState: "q1",
		transitions: [
			["q1", ["a", "B"], "q1", ["b", "B"], ["R", "R"]],
			["q1", ["b", "B"], "q1", ["a", "B"], ["R", "R"]],
			["q1", ["B", "B"], "q2", ["B", "B"], ["L", "L"]],
			["q2", ["a", "B"], "q2", ["a", "B"], ["L", "L"]],
			["q2", ["b", "B"], "q2", ["b", "B"], ["L", "L"]]
		],
		acceptStates: [],
		criteria: "false",
		markers: ["[", "]"]
		} |}


   (* AMD multifita test *)
	let tm_translate = {| {
		kind: "turing machine",
		description: "this is an example",
		name: "tm_translate",
		entryAlphabet: ["a", "b"],
		tapeAlphabet: ["a", "b", "B"],
		empty: "B",
		states: ["q1", "q2"],
		initialState: "q1",
		transitions: [
			["q1", ["a", "B"], "q1", ["b", "B"], ["R", "L"]],
			["q1", ["b", "B"], "q1", ["a", "B"], ["R", "L"]],
			["q1", ["B", "B"], "q2", ["B", "B"], ["L", "L"]],
			["q2", ["a", "B"], "q2", ["a", "B"], ["L", "L"]],
			["q2", ["b", "B"], "q2", ["b", "B"], ["L", "L"]]
		],
		acceptStates: [],
		criteria: "false"
		} |}

	let tm_astar1 = {| {
		kind: "turing machine",
		description: "this is an example",
		name: "tm_astar1",
		entryAlphabet: ["a", "b"],
		tapeAlphabet: ["a", "b", "B"],
		empty: "B",
		states: ["q1", "q2"],
		initialState: "q1",
		transitions: [
			["q1", "B", "q2", "B", "L"],
			["q1", "a", "q1", "b", "R"],
			["q1", "b", "q1", "a", "R"],
			["q2", "a", "q2", "a", "L"],
			["q2", "b", "q2", "b", "L"]
		],
		acceptStates: [],
		criteria: "false",
		markers: []
		} |}

	
	let tm_astar2 = {| {
		kind: "turing machine",
		description: "this is an example",
		name: "tm_astar2",
		entryAlphabet: ["a", "b"],
		tapeAlphabet: ["a", "b", "X", "Y","B"],
		empty: "B",
		states: ["q1", "q2", "q3", "q4", "q5", "q6", "q7"],
		initialState: "q1",
		transitions: [
			["q1", "a", "q2", "X", "R"],
			["q1", "b", "q5", "Y", "R"],
			["q1", "B", "q7", "B", "L"],

			["q2", "a", "q2", "a", "R"],
			["q2", "b", "q2", "b", "R"],
			["q2", "B", "q3", "B", "R"],

			["q3", "a", "q3", "a", "R"],
			["q3", "b", "q3", "b", "R"],
			["q3", "B", "q4", "a", "L"],

			["q4", "a", "q4", "a", "L"],
			["q4", "b", "q4", "b", "L"],
			["q4", "B", "q4", "B", "L"],
			["q4", "X", "q1", "X", "R"],
			["q4", "Y", "q1", "Y", "R"],

			["q5", "a", "q5", "a", "R"],
			["q5", "b", "q5", "b", "R"],
			["q5", "B", "q6", "B", "R"],

			["q6", "a", "q6", "a", "R"],
			["q6", "b", "q6", "b", "R"],
			["q6", "B", "q4", "b", "L"],

			["q7", "X", "q7", "a", "L"],
			["q7", "Y", "q7", "b", "L"]
		],
		acceptStates: [],
		criteria: "false",
		lbMarkers: []
		} |}

	let tm_astar3 = {| {
			kind: "turing machine",
			description: "this is an example changed",
			name: "tm_astar3",
			entryAlphabet: ["a", "b"],
			tapeAlphabet: ["a", "b", "B"],
			empty: "B",
			states: ["q1", "q2", "q3"],
			initialState: "q1",
			transitions: [
				["q1", "a", "q2", "a", "R"],
				["q1", "b", "q1", "b", "R"],
				["q2", "a", "q3", "a", "R"],
				["q2", "b", "q1", "b", "R"]
			],
			acceptStates: ["q3"],
			criteria: "true",
			lbMarkers: []
			} |}

	let tm_astar4 = {| {
			kind: "turing machine",
			description: "this is an example",
			name: "tm_astar4",
			entryAlphabet: ["a", "b", "c"],
			tapeAlphabet: ["a", "b", "c", "X", "Y", "Z", "B"],
			empty: "B",
			states: ["q1", "q2", "q3", "q4", "q5", "q6"],
			initialState: "q1",
			transitions: [
				["q1", "B", "q6", "B", "R"],
				["q1", "Y", "q5", "Y", "R"],
				["q1", "a", "q2", "X", "R"],

				["q2", "a", "q2", "a", "R"],
				["q2", "Y", "q2", "Y", "R"],
				["q2", "b", "q3", "Y", "R"],

				["q3", "b", "q3", "b", "R"],
				["q3", "Z", "q3", "Z", "R"],
				["q3", "c", "q4", "Z", "L"],

				["q4", "Z", "q4", "Z", "L"],
				["q4", "Y", "q4", "Y", "L"],
				["q4", "b", "q4", "b", "L"],
				["q4", "a", "q4", "a", "L"],

				["q5", "Y", "q5", "Y", "R"],
				["q5", "Z", "q5", "Z", "R"],
				["q5", "B", "q6", "B", "R"]
			],
			acceptStates: ["q6"],
			criteria: "true",
			lbMarkers: []
			} |}

	let tm_astar5 = {| {
			kind: "turing machine",
			description: "this is an example",
			name: "tm_astar5",
			entryAlphabet: ["a", "b"],
			tapeAlphabet: ["a", "b", "B"],
			empty: "B",
			states: ["q1", "q2", "q3", "q4"],
			initialState: "q1",
			transitions: [
				["q1", "a", "q2", "a", "R"],
				["q1", "b", "q1", "b", "R"],
				["q1", "B", "q4", "B", "R"],

				["q2", "a", "q3", "a", "R"],
				["q2", "b", "q1", "b", "R"],
				["q2", "B", "q4", "B", "R"],

				["q4", "a", "q4", "a", "R"],
				["q4", "b", "q4", "b", "R"],
				["q4", "B", "q4", "B", "R"]
			],
			acceptStates: [],
			criteria: "false",
			lbMarkers: []
			} |}

	let tm_astar6 = {| {
			kind: "turing machine",
			description: "this is an example",
			name: "tm_astar6",
			entryAlphabet: ["a", "b", "c"],
			tapeAlphabet: ["a", "b", "c", "B"],
			empty: "B",
			states: ["q1", "q2", "q3", "q4", "q5", "q6", "q7"],
			initialState: "q1",
			transitions: [
				["q1", "a", "q1", "a", "R"],
				["q1", "b", "q1", "b", "R"],
				["q1", "c", "q1", "c", "R"],

				["q1", "c", "q2", "c", "R"],
				["q1", "c", "q5", "c", "L"],

				["q2", "a", "q3", "a", "R"],

				["q3", "b", "q4", "b", "R"],

				["q5", "b", "q6", "b", "L"],

				["q6", "a", "q7", "a", "L"]
			],
			acceptStates: ["q4", "q7"],
			criteria: "true",
			lbMarkers: []
			} |}

	let tm_astar7 = {| {
			kind: "turing machine",
			description: "this is an example",
			name: "tm_astar7",
			entryAlphabet: ["a", "b", "c", "d", "e"],
			tapeAlphabet: ["a", "b", "c", "d", "e", "B"],
			empty: "B",
			states: ["q1", "q2", "q3"],
			initialState: "q1",
			transitions: [
				["q1", "a", "q2", "a", "R"],

				["q1", "a", "q1", "a", "R"],
				["q1", "b", "q1", "b", "R"],
				["q1", "c", "q1", "c", "R"],
				["q1", "d", "q1", "d", "R"],
				["q1", "e", "q1", "e", "R"],

				["q2", "c", "q3", "c", "R"]
			],
			acceptStates: ["q3"],
			criteria: "true",
			lbMarkers: []
			} |}

	let tm_astar8 = {| {
			kind: "turing machine",
			description: "this is an example",
			name: "tm_astar8",
			entryAlphabet: ["a"],
			tapeAlphabet: ["a", "B"],
			empty: "B",
			states: ["q1", "q2", "q3"],
			initialState: "q1",
			transitions: [
				["q1", "B", "q2", "B", "R"],
				["q2", "B", "q1", "B", "L"],

				["q2", "a", "q3", "a", "R"]
			],
			acceptStates: ["q3"],
			criteria: "true",
			lbMarkers: []
			} |}

	let tm_astar9 = {| {
			kind: "turing machine",
			description : "this is an example",
			name: "tm_astar9",
			entryAlphabet: ["a", "b", "c"],
			tapeAlphabet: ["a", "b", "c", "X", "Y", "Z", "B"],
			empty: "B",
			states: ["q1", "q2", "q3", "q4", "q5", "q6", "q7", "q8", "q9"],
			initialState: "q1",
			transitions: [

				["q1", "B", "q6", "B", "R"],
				["q1", "Y", "q5", "Y", "R"],
				["q1", "a", "q2", "X", "R"],

				["q2", "a", "q2", "a", "R"],
				["q2", "Y", "q2", "Y", "R"],
				["q2", "b", "q3", "Y", "R"],

				["q3", "b", "q3", "b", "R"],
				["q3", "Z", "q3", "Z", "R"],
				["q3", "c", "q4", "Z", "L"],

				["q4", "Z", "q4", "Z", "L"],
				["q4", "Y", "q4", "Y", "L"],
				["q4", "b", "q4", "b", "L"],
				["q4", "a", "q4", "a", "L"],
				
				["q4", "X", "q1", "X", "R"],

				["q5", "Y", "q5", "Y", "R"],
				["q5", "Z", "q5", "Z", "R"],
				["q5", "B", "q6", "B", "R"],

				["q5", "b", "q9", "c", "R"],

				["q7", "b", "q8", "c", "R"],
				["q7", "B", "q6", "B", "R"]

			],
			acceptStates: ["q6"],
			criteria: "true",
			lbMarkers: []
		} |}

	let tm_astar10 = {| {
		kind: "turing machine",
		description: "this is an example",
		name: "tm_astar10",
		entryAlphabet: ["a", "b", "c"],
		tapeAlphabet: ["a", "b", "c", "B"],
		empty: "B",
		states: ["q1"],
		initialState: "q1",
		transitions: [
			["q1", "B", "q1", "c", "R"],
			["q1", "a", "q1", "a", "R"],
			["q1", "b", "q1", "b", "R"],
			["q1", "c", "q1", "c", "R"]
		],
		acceptStates: [],
		criteria: "false",
		lbMarkers: []
		} |}

	let tm_astar11 = {| {
		kind : "turing machine",
		description : "this is an example",
		name : "tm_astar11",
		entryAlphabet: ["a", "b", "c"],
		tapeAlphabet: ["a", "b", "c", "B"],
		empty: "B",
		states : ["q1", "q2", "q3"],
		initialState : "q1",
		transitions : [
			["q1", "a", "q2", "c", "R"],
			["q1", "b", "q1", "b", "R"],
			["q1", "c", "q1", "a", "R"],
			["q2", "b", "q1", "b", "L"],
			["q2", "c", "q3", "c", "R"]
		],
		acceptStates : [],
		criteria : "false",
		lbMarkers: []
		} |}


(* Composition *)
	let comp_abc = {| {
			kind : "composition",
			description : "this is an example",
			name : "comp_abc",
			comp : "[tm_astar11]^[tm_astar11]"
	} |}


(* Exercises *)
	let exer_balanced_cfg = {| {
			kind : "exercise",
			description : "CFG: Create a CONTEXT FREE GRAMMAR that generates the language of balanced square bracket parentheses",
			name : "exer_balanced_cfg",
			problem : "CFG for the language of balanced parentheses",
			inside : ["","[]","[[]]","[][]","[[][][][[]]][]"],
			outside : ["[","][","[[]","[[]]]"],
			properties : ["context free grammar"]
		} |}

	let exer_astar_fa = {| {
			kind : "exercise",
			description : "FA: all sequences of 'a's",
			name : "exer_astar_fa",
			problem : "Create a deterministic FINITE AUTOMATON that recognizes all sequences of 'a's",
			inside : ["","a","aa","aaa","aaaaaaa"],
			outside : ["d","b","ava"],
			properties : ["finite automaton", "deterministic"]
		} |}

	let exer_astar_re = {| {
			kind : "exercise",
			description : "RE: all sequences of 'a's",
			name : "exer_astar_re",
			problem : "Create a REGULAR EXPRESSION that generates all sequences of 'a's",
			inside : ["","a","aa","aaa","aaaaaaa"],
			outside : ["d","b","ava"],
			properties : ["regular expression"]
		} |}

	let exer_abcd = {| {
			kind : "exercise",
			description : "this is an example",
			name : "exer_abcd",
			problem : "Convert the regular expression (a+b)*(c+d) to finite automaton.",
			inside : ["abc","c","abd","d","abac"],
			outside : ["","aba","bab","abba","baab","abcd"],
			properties : ["finite automaton"]
		} |}

	let exer_ab = {| {
			kind : "exercise",
			description : "this is an example",
			name : "exer_ab",
			problem : "Convert the regular expression ab*+ba* to finite automaton.",
			inside : ["a","ab","abb","abbbbbbbb","b","ba","baa","baaaaaa"],
			outside : ["","aba","bab","abba","baab","c"],
			properties : ["finite automaton"]
		} |}

	let exer_re2fa = {| {
			kind : "exercise",
			description : "this is an example",
			name : "exer_re2fa",
			problem : "Converta o autómato finito com alfabeto: [x, y, z], estados: [S, T, V], estado inicial: S, transições [[S, x, S], [S, y, T], [S, z, V], [T, x, T], [T, z, T], [T, y, V], [V, x, T]], e estados finais: [V] em expressão regular.",
			inside : ["z", "xz", "yy", "yzy", "xyy", "zxxy"],
			outside : ["x","y","xy", "xyz", "yyx", "xzxz", "xyxz"],
			properties : ["regular expression"]
		} |}

	let exer_readwrite = {| {
			kind : "exercise",
			description : "this is an example",
			name : "exer_readwrite",
			problem : "open,close,read,write",
			inside : ["","orc","owc","orwc","owwrwrrc","ocorwc"],
			outside : ["or","oo","o","w","r","c","orw","owrrww","corwc"],
			properties : ["finite automaton"]
		} |}

	let oflatExamplesTable = [
		("dfa_1", dfa_1);
		("dfa_2", dfa_2);
		("dfa_astar", dfa_astar);
		("fa_abc", fa_abc);
		("nfa_1", nfa_1);
		("nfa_2", nfa_2);

		("re_abc", re_abc);
		("re_complex", re_complex);
		("re_convoluted", re_convoluted);
		("re_simple", re_simple);
		("re_astar", re_astar);

		("fe_colors", fe_colors);

		("cfg_simple", cfg_simple);
		("cfg_balanced", cfg_balanced);
	
		("cfg_ll_thesis_g1", cfg_ll_thesis_g1);
		("cfg_ll_thesis_g2", cfg_ll_thesis_g2);
		("cfg_ll_1", cfg_ll_1);
		("cfg_ll_2", cfg_ll_2);
		("cfg_ll_3", cfg_ll_3);
		("cfg_ll_4", cfg_ll_4);
		("cfg_ll_5", cfg_ll_5);
		("cfg_ll_6", cfg_ll_6);	

		("cfg_lr0_thesis", cfg_lr0_thesis);
		("cfg_slr1_thesis", cfg_slr1_thesis);
		("cfg_slr1", cfg_slr1);
		("cfg_lr1_thesis", cfg_lr1_thesis);
		("cfg_lalr1_thesis", cfg_lalr1_thesis);
		("cfg_only_lr1", cfg_onlylr1);
		("cfg_not_lr1", cfg_notlr1);
		
		("ug_simple", ug_simple);

		("pda_WW_1", pda_WW_1);
		("pda_AABB", pda_AABB);
		("pda_Explode", pda_Explode);

		("tm_translate", tm_translate);
		("tm_translate_lb", tm_translate_lb);
		("tm_astar1", tm_astar1);
		("tm_astar2", tm_astar2);
		("tm_astar3", tm_astar3);
		("tm_astar4", tm_astar4);
		("tm_astar5", tm_astar5);
		("tm_astar6", tm_astar6);
		("tm_astar7", tm_astar7);
		("tm_astar8", tm_astar8);
		("tm_astar9", tm_astar9);
		("tm_astar10", tm_astar10);
		("tm_astar11", tm_astar11);
		
		("comp_abc", comp_abc);
		
		("exer_balanced_cfg", exer_balanced_cfg);
		("exer_astar_fa", exer_astar_fa);
		("exer_astar_re", exer_astar_re);
		("exer_abcd", exer_abcd);
		("exer_ab", exer_ab);
		("exer_re2fa", exer_re2fa);
		("exer_readwrite", exer_readwrite);

	]

	let examples =
		List.map fst oflatExamplesTable

	let example name =
		List.assoc name oflatExamplesTable

	let jsonExample name =
		let j = JSon.parse (example name) in
			if JSon.isNull j then
				Error.error "Invalid example" name ();
			j
			
	let see name =
		Util.println [example name]

	let validate () =
		List.iter (fun n -> ignore (jsonExample n)) examples

	let _ =
		if true then
			validate ()	
end
# 1 "src/Entity.ml"
(*
 * Entity.ml
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
 * set/2022 (amd) - Full restructuration.
 * jul/2021 (amd) - Improved error handling.
 * may/2021 (amd) - Added support for an extern representation.
 * may/2021 (amd) - Centralized the handling of kind/description/name.
 * feb/2021 (amd) - Added the alternative Predef.
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlat.ml".
 *)

(*
 * Description: An entity is a named instance of a concept. As now, the entities
 * are the exercises and the FLAT models. The type "alternatives" is to allow
 * the constructor to be used with several kind of parameter forms.
 *)

module Arg =
struct	
	type 'r alternatives =
		| JSon of JSon.t
		| Text of string
		| File of string
		| Predef of string
		| Representation of 'r

	let fromAlternatives alt =
		match alt with
		| JSon j -> j
		| Text str -> JSon.parse str
		| File str -> JSon.fromFile str 
		| Predef str -> JSon.parse (Examples.example str)
		| _ -> JSon.JNull
end

module EntityBasics =
struct
	type t = {
		kind : string;
		description : string;
		name : string
	}
	type tx =
		t 
end

module EntityConversions =
struct
	open EntityBasics

	let dummyId (k: string): t = {
		kind = k;
		description = "_";
		name = "_"
	}

	let fromJSon (j: JSon.t) (kind: string): t =
		if JSon.isNull j then (
			dummyId kind )
		else (
		 {
			kind = JSon.fieldString j "kind";
			description = JSon.fieldString j "description";
			name = JSon.fieldString j "name"
		})
		
	let toJSon (rep: t): JSon.t =
		JSon.makeAssoc [
			("kind", JSon.makeString rep.kind);
			("description", JSon.makeString rep.description);
			("name", JSon.makeString rep.name)
		]
end

module EntitySupport =
struct
	include EntityBasics
	include EntityConversions
end

module EntityPrivate =
struct
	include EntitySupport

	let startCreation () =
		Error.startGroup ()
	
	let createId (arg: 'r Arg.alternatives) (kind: string): t =
		startCreation ();
		match arg with
		| Arg.Representation r -> dummyId kind
		| _ -> fromJSon (Arg.fromAlternatives arg) kind

	let create (arg: 'r Arg.alternatives) fromJSon: 'r =
		match arg with
			| Arg.Representation r -> r
			| _ -> fromJSon (Arg.fromAlternatives arg)

	let endCreation (id: t) rep kind validate: unit =
		if id.kind <> kind then
			Error.error id.kind "Wrong kind" ();
		validate id.name rep;
		ignore (Error.endGroup kind id.name)
end

module Entity =
struct
	open EntityPrivate
	include EntitySupport

	let make2 (arg: 'r Arg.alternatives) (fromJSon: JSon.t -> 'r)
			(kind: string) (validate: string -> 'r -> unit): t * 'r =
		let id = createId arg kind in
		let m = create arg fromJSon in
			endCreation id m kind validate;
			(id, m)

	class virtual entity (data: t * 'r) =
		object(self)
			val id: t = fst data
			val representation: 'r = snd data
			val errors = Error.get ()
		(* Representation *)
			method id: t = id
			method errors: string list = errors
		(* Kind *)
			method isFiniteAutomaton : bool = false
			method isRegularExpression : bool = false
			method isGrammar : bool = false
			method isContextFreeGrammar : bool = false
			method isPushdownAutomaton : bool = false
			method isTuringMachine : bool = false
			method isExercise : bool = false
			method isComposition : bool = false
		(* Show *)			
			method virtual toJSon: JSon.t
			method virtual toJSon2: JSon.t
			method virtual show : unit
			method virtual show2 : unit
	end
end

module EntityTests : sig end =
struct
	let active = false

	let test0 () =
		()

	let runAll =
		if Util.testing active "Entity" then begin
			test0 ()
		end
end
# 1 "src/ExerciseSupport.ml"
(*
 * ExerciseSupport.ml
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
 * oct/2022 (amd) - New module
 *)

(*
 * Description: Support to pedagogical exercises. The solutions are validated
 * using unit tests.
 *)

open BasicTypes

module ExerciseBasics =
struct
	type tx = {
		problem : string;
		inside : wordX list;
		outside : wordX list;
		properties : properties
	}
	
	type t = {
		problem : string;
		inside : words;
		outside : words;
		properties : properties
	}
	
	let kind = "exercise"

	let exer_zero: t = {
		problem = "_";
		inside = Set.empty;
		outside = Set.empty;
		properties = Set.empty
	}
end

module ExerciseConversions =
struct
	open ExerciseBasics

	let internalize (e: tx): t = {
		problem = e.problem;
		inside = Set.make (List.map wordX2word e.inside);
		outside = Set.make (List.map wordX2word e.outside);
		properties = e.properties
	}

	let externalize (e: t): tx = {
		problem = e.problem;
		inside = List.map word2wordX (Set.toList e.inside);
		outside = List.map word2wordX (Set.toList e.outside);
		properties = e.properties
	}

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			exer_zero
		else {
			problem = JSon.fieldString j "problem";
			inside = Set.map str2word (JSon.fieldStringSet j "inside");
			outside = Set.map str2word (JSon.fieldStringSet j "outside");
			properties = JSon.fieldStringSet j "properties"
		}
	
	let toJSon (rep: t): JSon.t =
		JSon.makeAssoc [
			("problem", JSon.makeString rep.problem);
			("inside", JSon.makeStringSet (Set.map word2str rep.inside));
			("outside", JSon.makeStringSet (Set.map word2str rep.outside));
			("properties", JSon.makeStringSet rep.properties)
		]
	
	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon rep)
end

module ExerciseShow =
struct
	open ExerciseBasics
	open ExerciseConversions

	let show (rep: t): unit =
		let j = toJSon rep in
			JSon.show j

	let show2 (id: Entity.t) (rep: t): unit =
		let j = toJSon2 id rep in
			JSon.show j
	
	let showRes (ins,outs,props): unit =
		Util.println ["INS: "]; Util.printWords ins;
		Util.println ["OUTS: "]; Util.printWords outs;
		Util.println ["PROPS: "]; Util.printStrings props
end

module ExerciseSupport =
struct
	include ExerciseBasics
	include ExerciseConversions
	include ExerciseShow
end
# 1 "src/Exercise.ml"
(*
 * Exercise.ml
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
 * jul/2021 (amd) - Improved error handling.
 * mar/2021 (amd) - Added semantic constrains (properties) to the exercises.
 * jan/2021 (amd) - Module in an independent file.
 * set/2019 (amd) - Initial version, inside the big file "OCamlFlat.ml"
 *)

(*
 * Description: Support to pedagogical exercises. The solutions are validated
 * using unit tests.
 *)

open BasicTypes

module Exercise =
struct
	include ExerciseSupport
		
	(* Make *)
	let validate (name: string) (rep: t): unit =
		()

	let make2 (arg: t Arg.alternatives): Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives): t =
		snd (make2 arg)

	class exercise (arg: t Arg.alternatives) =
		object(self) inherit Entity.entity (make2 arg) as super
		(* Representation *)
			method representation = representation
			method representationx = externalize representation
		(* Kind *)
			method isExercise : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Learn-OCaml support *)				
			method moduleName =
				"Exercice"
	end
end

module ExerciseTests : sig end =
struct
	let active = false

	let test0 () =
		let e = Exercise.make (Arg.Predef "exer_balanced_cfg") in
			Exercise.show e

	let test1 () =
		let (id, e) = Exercise.make2 (Arg.Predef "exer_balanced_cfg") in
			Exercise.show2 id e

	let test2 () =
		let e = new Exercise.exercise (Arg.Predef "exer_balanced_cfg") in
		let j = e#toJSon2 in
			JSon.show j

	let runAll =
		if Util.testing active "Exercice" then begin
			test0 ();
			test1 ();
			test2 ()
		end
end


# 1 "src/Model.ml"
(*
 * Model.ml
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
 * jun/2023 (amd) - Added generic 'accept' and 'generate' methods.
 * set/2022 (amd) - Full restructuration.
 * jul/2021 (amd) - Improved Learn-OCaml support.
 * mar/2021 (amd) - Added support for semantic constrains (properties) in
 *                  the exercises, in this class and in all its subclasses.
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlat.ml".
 *)

(*
 * Description: Abstract FLAT model.
 *
 * TODO: Probably add a new method "canonical" to generate a
 * normalized/simplified version of the FLAT model.
 *)

open BasicTypes

module ModelBasics =
struct
end

module ModelExercises =
struct
	let checkProperty (prop: string) =
		match prop with
			| "fail" | "false" -> false
			| "true" -> true
			| _ ->
				let mesg = "checkProperty: unknown property ("
								^ prop ^ ")" in
					Error.fatal mesg

	let checkExercise (ex: Exercise.t) accept checkProperty =
		   Set.for_all accept ex.inside
		&& Set.for_all (fun w -> not (accept w)) ex.outside
		&& Set.for_all checkProperty ex.properties

	let checkExerciseFailures (ex: Exercise.t) ac cp = (
		Set.filter (fun w -> not (ac w)) ex.inside,
		Set.filter ac ex.outside,
		Set.filter (fun w -> not (cp w)) ex.properties
	)
end

module ModelSupport =
struct
	include ModelBasics
	include ModelExercises
end

module ModelPrivate =
struct
	let stats () =
		RuntimeControl.stats ()

	let checkWord (alphabet: symbols) (w: word): bool =
		let ok = Set.subset (Set.make w) alphabet in
		let str = word2str w in
		let mesg = "Word \"" ^ str ^ "\" contains symbols not belonging to the alphabet" in
			if not ok then Error.warning mesg;
			ok

	(* The result is true is the word is accepted. *)
	let accept (m: 'm) (w: word)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): bool =
		let rec acceptX (configs: 'c set) (seen: 'c set): bool =
			let newConfigs = Set.diff configs seen in
			let newSeen = Set.unionUnsafe newConfigs seen in
			let _ = RuntimeControl.update (Set.size newConfigs) in
			if Set.isEmpty newConfigs then
				false
			else if Set.exists (isAccepting m) newConfigs then
				true
			else if RuntimeControl.giveUp () then
				false
			else
				let nextConfigs = Set.flatMap (next m) newConfigs in
					acceptX nextConfigs newSeen
		in	
		let _ = RuntimeControl.start () in
		let initialConfigs = initial m w in
			acceptX initialConfigs Set.empty

	(* The result is a triple: acceptance, one path, trail with all the alternatives.  *)
	let acceptFull (m: 'm) (w: word)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): bool * 'c path * 'c trail =
		let base (r: bool) (configs: 'c set): bool * 'c path * 'c trail =
			let accepting = Set.filter (isAccepting m) configs in
			let c = Set.hd (if Set.isEmpty accepting then configs else accepting) in
				(r, [c], [configs])
		in
		let rec acceptX (configs: 'c set) (seen: 'c set) : bool * 'c path * 'c trail =
			let newConfigs = Set.diff configs seen in
			let newSeen = Set.unionUnsafe newConfigs seen in
			let _ = RuntimeControl.update (Set.size newConfigs) in
			if Set.isEmpty newConfigs then
				(false, [], [])
			else if Set.exists (isAccepting m) newConfigs then
				base true newConfigs
			else if RuntimeControl.giveUp () then
				base false newConfigs
			else
				let nextConfigs = Set.flatMap (next m) newConfigs in
				let (r,p,t) = acceptX nextConfigs newSeen in
					match p with
					| [] ->
						base r newConfigs
					| x::_ ->
						let c = Set.find (fun c -> Set.belongs x (next m c)) newConfigs in
							(r, c::p, newConfigs::t)
		in
		let _ = RuntimeControl.start () in
		let initialConfigs = initial m w in
			acceptX initialConfigs Set.empty
	
	(* invariant - for_all c in seen: c <= len *)
	let generate (m: 'm) (len: int)
				(initial: 'm -> word -> 'c set)
				(next2: 'm -> int -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool)
				(getWord: 'c -> word): words =

		let strict = len < 0 in
		let len = abs len in
		let lenWord c = List.length (getWord c) in
		let isNew seen c = lenWord c <= len && not (Set.belongs c seen) in
		let isExpanding c = lenWord c < len || not (isAccepting m c) in
		let finalSelection =
			if strict then (fun c -> isAccepting m c && lenWord c = len) 
					else (fun c -> isAccepting m c) 
		in
		let rec generateX (configs: 'c set) (seen: 'c set): 'c set =
			let newConfigs = Set.filter (isNew seen) configs in
			let newSeen = Set.union newConfigs seen in
			let _ = RuntimeControl.update (Set.size newConfigs) in (* ???, e também stack overflow, reutime controlo tem de ter varias instancias *) (* comparar o accept e o generate do joao *)
			let toExpand = Set.filter isExpanding newConfigs in
				if Set.isEmpty toExpand || RuntimeControl.giveUp () then
					newSeen
				else
					let nextConfigs = Set.flatMap (next2 m len) toExpand in
						if RuntimeControl.giveUp () then
							newSeen
						else
							generateX nextConfigs newSeen
		in
		let _ = RuntimeControl.start () in
		let initialConfigs = initial m (word "") in
		let collected = generateX initialConfigs Set.empty in
		let selected = Set.filter finalSelection collected in
			Set.map getWord selected

	(* generate and test. Will be improved.
	   Used for TMs because the "rest of the word" is not part of the configuration *)
	let generateDumb (m: 'm) (alphabet : symbols) (len: int)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): words =
				
		let addAll symb = List.map (fun l -> symb::l) in
		let rec combinations n l =
			if n = 0 then [[]]
			else let p = combinations (n-1) l in
					List.flatten (List.map  (fun x -> addAll x p) l)
		in
		let rec combinations2 n l =
			if n = 0 then [[]] else combinations2 (n-1) l @ combinations n l in
		let strict = len < 0 in
		let len: int = abs len in
		let s: word = Set.toList alphabet in
		let comb: word list = if strict then combinations len s else combinations2 len s in
		let accept w: bool = accept m w initial next isAccepting in
		let selected: word list = List.filter accept comb in
			Set.make selected

end

module Model =
struct
	include ModelSupport

	let stats = ModelPrivate.stats
	let checkWord = ModelPrivate.checkWord
	let accept = ModelPrivate.accept
	let acceptFull = ModelPrivate.acceptFull
	let generate = ModelPrivate.generate	
	let generateDumb =  ModelPrivate.generateDumb

	class virtual model (data: Entity.t * 'r) =
		object(self) inherit Entity.entity data

			method virtual accept: word -> bool
			(*method virtual acceptFull: 'c. word ->  bool * 'c path * 'c trail*)
			method virtual generate: int -> words
			(*method virtual generateDumb: int -> words*)
		
		(* Exercices support *)
			method checkProperty (prop: string) = checkProperty prop
			method checkExercise (exercise: Exercise.exercise) =
				checkExercise exercise#representation self#accept self#checkProperty
			method checkExerciseFailures (exercise: Exercise.exercise) =
				checkExerciseFailures exercise#representation self#accept self#checkProperty

		(* Learn-OCaml support *)
			method virtual moduleName: string
			method virtual xTypeName: string
			method virtual xTypeDeclString : string
			method virtual toDisplayString: string -> string
			method virtual example : JSon.t
	end

end

(*

(* this is only a test *)
class virtual cModel (arg: 'r Arg.alternatives) (expectedKind: string) =
	let open Model in
	object(self) inherit Entity.entity arg expectedKind

		method virtual accept: word -> bool
		method virtual acceptFull: 'c. word ->  bool * 'c path * 'c trail
		method virtual generate: int -> words
		method virtual generateDumb: int -> words
		
	(* Exercices support *)
		method checkProperty (prop: string) = checkProperty prop
		method checkExercise (exercise: Exercise.exercise) =
			checkExercise exercise#representation self#accept self#checkProperty
		method checkExerciseFailures (exercise: Exercise.exercise) =
			checkExerciseFailures exercise#representation self#accept self#checkProperty

	(* Learn-OCaml support *)
		method virtual moduleName: string
		method virtual xTypeName: string
		method virtual xTypeDeclString : string
		method virtual toDisplayString: string -> string
		method virtual example : JSon.t
end

*)

(*
SAVE- old versions that might be useful again

	(* trail alone *)
	let acceptTrail (m: 'm) (w: word)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): bool * 'c trail =

		let rec acceptX (configs: 'c set) (seen: 'c set) (trail: 'c trail): bool * 'c trail =
			let newConfigs = Set.diff configs seen in
			let newSeen = Set.unionUnsafe newConfigs seen in
			let newTrail = newConfigs::trail in
			if Set.isEmpty newConfigs then (false, trail)
			else if Set.exists (isAccepting m) newConfigs then (true, newTrail)
			else if RuntimeControl.giveUp (Set.size newSeen) then (false, newTrail)
			else
				let nextConfigs = Set.flatMap (next m) newConfigs in
					acceptX nextConfigs newSeen newTrail
		in
		let _ = RuntimeControl.start () in
		let initialConfigs = initial m w in
		let (b, trail) = acceptX initialConfigs Set.empty [] in
			(b, List.rev trail)

	(* path calculated from the trail *)
	let acceptPath (m: 'm) (w: word)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): 'c path =

		let rec acceptX (trail: 'c trail): 'c path =
			match trail with
			| [] -> Error.fatal "acceptX"
			| [c] ->
				let a = Set.filter (isAccepting m) c in
					[Set.hd (if Set.isEmpty a then c else a)]
			| c::cs ->
				(match acceptX cs with
				| [] ->  Error.fatal "acceptX"
				| p::ps ->
					let n = Set.find (fun c -> Set.belongs p (next m c)) c in
						n::p::ps)
		in
		let (_, trail) = acceptTrail m w initial next isAccepting in
			acceptX trail

			let acceptPaths (m: 'm) (w: word)
				(initial: 'm -> word -> 'c)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): 'c path set =


	(* all the paths alone *)
		let rec acceptX (paths: 'c path set) (seen: 'c set): 'c path set =
			let configs = Set.map List.hd paths in
			let newConfigs = Set.diff configs seen in				(* select the new *)
			let seen = Set.unionUnsafe newConfigs seen in			(* build new seen *)
			if Set.isEmpty newConfigs then							(* case repetition *)
				Set.map List.tl paths
			else if Set.exists (isAccepting m) newConfigs then		(* case accept *)
				Set.filter (fun p -> isAccepting m (List.hd p)) paths
			else
				let isNewPath p = Set.belongs (List.hd p) newConfigs in
				let nextPathsOne p = Set.map (fun c -> c::p) (next m (List.hd p))  in
				let newPaths = Set.filter isNewPath paths in
				let nextPaths = Set.flatMap nextPathsOne newPaths in
				if Set.size nextPaths = 0 then paths				(* case no-followup *)
				else	acceptX nextPaths seen
		in	
		let initialConfig = initial m w in
		let paths = acceptX (Set.make [[initialConfig]]) Set.empty in
			Set.map List.rev paths
	let acceptPath (m: 'm) (w: word)
				(initial: 'm -> word -> 'c)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): 'c path =
		let ps = acceptPaths m w initial next isAccepting in
		let min p1 p2 = if List.length p1 <= List.length p2 then p1 else p2 in
			Set.fold_left min (Set.hd ps) (Set.tl ps)

	(* trail and all the paths  *)
	let acceptFull (m: 'm) (w: word)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): bool * 'c path * 'c trail =

		let rec acceptX (paths: 'c path set) (trail: 'c trail) (seen: 'c set)
													: bool * 'c path set * 'c trail =
			let configs = Set.map List.hd paths in
				if Set.exists (isAccepting m) configs then			(* case accept *)
					(true, paths, trail)
				else if RuntimeControl.giveUp (Set.size seen) then
					(false, paths, trail)
				else
					let nextConfigsOne p = next m (List.hd p) in
					let newConfigsOne p = Set.diff (nextConfigsOne p) seen in
					let newPathsOne p = Set.map (fun c -> c::p) (newConfigsOne p) in
					let newPaths = Set.flatMap newPathsOne paths in
					let newConfigs = Set.map List.hd newPaths in
					let newTrail = newConfigs::trail in
					let newSeen = Set.unionUnsafe newConfigs seen in
						if Set.isEmpty newConfigs then				(* case reject *)
							(false, paths, trail)
						else
							acceptX newPaths newTrail newSeen
		in
		let _ = RuntimeControl.start () in
		let initialConfigs = initial m w in
		let initialPaths = Set.map (fun c -> [c]) initialConfigs in
		let initialTrail = [initialConfigs] in
		let initialSeen = initialConfigs in
		let (r, ps, t) = acceptX initialPaths initialTrail initialSeen in
		let (r, ps, t) = (r, Set.map List.rev ps, List.rev t) in
		let fps = Set.filter (fun p -> isAccepting m (List.hd p)) ps in
			(r, Set.hd (if Set.isEmpty fps then ps else fps), t)

	(* full from trail and path  *)
	let acceptFull (m: 'm) (w: word)
				(initial: 'm -> word -> 'c)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): bool * 'c path * 'c trail =
		let p = acceptPath m w initial next isAccepting in
		let (r,t) = acceptTrail m w initial next isAccepting in
			(r, p, t)
*)
# 1 "src/FiniteEnumerationSupport.ml"
(*
 * FiniteEnumerationSupport.ml
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
 * sep/2022 (amd) - New module
 *)

(*
 * Description: Support types and functions for FEs.
 *)

open BasicTypes

module FiniteEnumerationBasics =
struct
	type t = words

	let kind = "finite enumeration"
	
	let fe_zero: t = Set.empty
end

module FiniteEnumerationConversions =
struct
	open FiniteEnumerationBasics

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			fe_zero
		else
			let strings = JSon.fieldStringSet j "words" in
			let words = Set.map str2word strings in
				words
	
	let toJSon (rep: t): JSon.t =
		JSon.makeAssoc [
			("words", JSon.makeStringSet (Set.map word2str rep))
		]

	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon rep)
end

module FiniteEnumerationBasicFunctions =
struct
	open FiniteEnumerationBasics
	open FiniteEnumerationConversions

	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (rep: t): unit =
		let j = toJSon rep in
			JSon.show j

	let show2 (id: Entity.t) (rep: t): unit =
		let j = toJSon2 id rep in
			JSon.show j
end

module FiniteEnumerationX =
struct
	open FiniteEnumerationBasics
	
	type tx = string list

	let internalize (fe: tx): t =
		wordsI fe

	let externalize (fe: t): tx =
		wordsX fe
end

module FiniteEnumerationLearnOCaml =
struct
	open FiniteEnumerationBasics
	open FiniteEnumerationX

	let xTypeName =
		let l = String.split_on_char ' ' kind in
			List.nth l 0 ^ String.capitalize_ascii (List.nth l 1)
		
	let moduleName =
		String.capitalize_ascii xTypeName

	let displayHeader (name: string) (xTypeName: string) =
		if name = "" then ""
		else ("let " ^ name ^ ": " ^ xTypeName ^ " =\n\t\t")

	let solution (name: string) (rep: t): string =
		let repx = externalize rep in
		Printf.sprintf {zzz|
		%s	%s
		|zzz}	(* please, do not change this line *)
			(displayHeader name xTypeName)
			(stringsD repx)

	let prelude : string = {| {
		type symbol = char
		type state = string
		type transition = state * symbol * state

		type finiteENNNNN = {
			alphabet : symbol list;
			states : state list;
			initialState : state;
			transitions : transition list;
			acceptStates : state list
		}
		|}	(* please, do not change this line *)

	let example : JSon.t =
		JSon.parse {| {
			kind : "finite enumeration",
			description : "this is an example",
			name : "fe example",
			words : ["Red", "Yellow", "Blue"]
		}
		|}	(* please, do not change this line *)
end

module FiniteEnumerationSupport =
struct
	include FiniteEnumerationBasics
	include FiniteEnumerationConversions
	include FiniteEnumerationBasicFunctions
	include FiniteEnumerationLearnOCaml
end
# 1 "src/FiniteEnumeration.ml"
(*
 * FiniteEnumeration.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
 * set/2022 (amd) - Full restructuration.
 * jul/2021 (amd) - Improved Learn-OCaml support and error handling.
 * may/2021 (amd) - Added support for an extern representation.
 * mar/2021 (amd) - New module
 *)

(*
 * Description: Finite language, directly defined as a set of words.
 *)

open BasicTypes

module FiniteEnumerationPrivate =
struct
	open FiniteEnumerationSupport
	
	let validate (name: string) (rep: t): unit =
		()

	let accept (fe: t) (w: word): bool =
		Set.belongs w fe

	let generate (fe: t) (length: int): words =
		Set.filter (fun w -> List.length w == length) fe
end

module FiniteEnumeration =
struct
	include FiniteEnumerationSupport
	open FiniteEnumerationPrivate

	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t =
		make2 arg validate

	let make (arg: t Arg.alternatives): t =
		make arg validate

	(* Exercices support *)
	let checkProperty (fe: t) (prop: string) =
		match prop with
			| "finite enumeration" -> true
			| _ -> Model.checkProperty prop

	let checkExercise ex fe =
		Model.checkExercise ex (accept fe) (checkProperty fe)	

	let checkExerciseFailures ex fe =
		Model.checkExerciseFailures ex (accept fe) (checkProperty fe)	

	(* Ops *)
	let accept = accept
	let generate = generate	

	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model (make2 arg) as super
		(* Representation *)
			method representation: t = representation
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Ops *)				
			method accept (w: word): bool = accept representation w
			method generate (length: int): words = generate representation length
		(* Exercices support *)
			method checkProperty (prop: string) = checkProperty representation prop
		(* Learn-OCaml support *)
			method moduleName = moduleName
			method xTypeName = xTypeName
			method xTypeDeclString : string = prelude
			method toDisplayString (name: string): string = solution name self#representation
			method example : JSon.t = example
		end
end
# 1 "src/FiniteAutomatonSupport.ml"
(*
 * FiniteAutomatonSupport.ml
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
 * sep/2022 (amd) - New module
 *)

(*
 * Description: Support types and functions for FAs.
 *)

open BasicTypes

module FiniteAutomatonBasics =
struct
	type transition3 = state * symbol * state
	type transitions3 = transition3 set
	type t = {
		alphabet : symbols;
		states : states;
		initialState : state;
		transitions : transitions3;
		acceptStates : states
	}

	type configuration = state * word
	type configurations = configuration set
	type path = configuration list
	type trail = configurations list

	let kind = "finite automaton"

	let fa_zero: t = {
		alphabet = Set.empty;
		states = Set.make [draftState];
		initialState = draftState;
		transitions = Set.empty;
		acceptStates = Set.empty
	}
end

module FiniteAutomatonConversions =
struct
	open FiniteAutomatonBasics

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			fa_zero
		else {
			alphabet = JSon.fieldSymbolSet j "alphabet";
			states = JSon.fieldStateSet j "states";
			initialState = JSon.fieldState j "initialState";
			transitions = JSon.fieldTriplesSet j "transitions";
			acceptStates = JSon.fieldStateSet j "acceptStates"
		}

	let toJSon0 (rep: t): JSon.t =
		JSon.makeAssoc [
			("alphabet", JSon.makeSymbolSet rep.alphabet);
			("states", JSon.makeStateSet rep.states);
			("initialState", JSon.makeState rep.initialState);
			("transitions", JSon.makeTriplesSet rep.transitions);
			("acceptStates", JSon.makeStateSet rep.acceptStates)
		]
	
	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 rep)
	
	let toJSon (rep: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) rep
end

module FiniteAutomatonBasicFunctions =
struct
	open FiniteAutomatonBasics
	open FiniteAutomatonConversions

	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (rep: t): unit =
		let j = toJSon rep in
			JSon.show j

	let show2 (id: Entity.t) (rep: t): unit =
		let j = toJSon2 id rep in
			JSon.show j
end

module FiniteAutomatonX =
struct
	open FiniteAutomatonBasics

	type transition3X = state * symbolX * state
	type tx = {
		alphabet : symbolX list;
		states : state list;
		initialState : state;
		transitions : transition3X list;
		acceptStates : state list
	}

	let transitions3I (l: transition3X list): transitions3 =
		let trans3I (a,b,c): transition3 = (a, symbI b, c) in
			Set.make (List.map trans3I l)
			
	let transitions3X (s: transitions3): transition3X list =
		let trans3X (a,b,c): transition3X = (a, symbX b, c) in
			List.map trans3X (Set.toList s)

	let internalize (fa: tx): t = {
		alphabet = symbolsI fa.alphabet;
		states = Set.make fa.states;
		initialState = fa.initialState;
		transitions = transitions3I fa.transitions;
		acceptStates = Set.make fa.acceptStates
	}
	
	let externalize (fa: t): tx = {
		alphabet = symbolsX fa.alphabet;
		states = Set.toList fa.states;
		initialState = fa.initialState;
		transitions = transitions3X fa.transitions;
		acceptStates = Set.toList fa.acceptStates
	}
end

module FiniteAutomatonLearnOCaml =
struct
	open FiniteAutomatonBasics
	open FiniteAutomatonX

	let moduleName =
		"FiniteAutomaton"

	let xTypeName =
		"finiteAutomaton"

	let transs3XD (l: transition3X list): string =
		let t2d (a,b,c) =
			Printf.sprintf "(%s, %s, %s)"
			(stateXD a)
			(symbXD b)
			(stateXD c)
		in listD t2d l

	let solution (name: string) (rep: t): string =
		let repx = externalize rep in
		Printf.sprintf {zzz|
		%s{
			alphabet = %s;
			states = %s;
			initialState = %s;
			transitions = %s;
			acceptStates = %s
		}
		|zzz}	(* please, do not change this line *)
			(FiniteEnumerationLearnOCaml.displayHeader name xTypeName)
			(symbolsXD repx.alphabet)
			(statesXD repx.states)
			(stateXD repx.initialState)
			(transs3XD repx.transitions)
			(statesXD repx.acceptStates)


	let prelude : string =
		Printf.sprintf {zzz|
		type symbol = %s
		type state = string
		type finiteAutomaton = {
			alphabet : symbol list;
			states : state list;
			initialState : state;
			transitions : (state * symbol * state) list;
			acceptStates : state list
		}
		|zzz}	(* please, do not change this line *)
			symbolTypeName

	let example : JSon.t =
		JSon.parse {|
		{
			kind : "finite automaton",
			description : "this is an example",
			name : "fa example",
			alphabet: ["w", "z"],
			states : ["START", "X", "Z"],
			initialState : "START",
			transitions : [
				["START", "w", "X"], ["X", "z", "X"]
			],
			acceptStates : ["Z"]
		}
		|}	(* please, do not change this line *)
end

module FiniteAutomatonSupport =
struct
	include FiniteAutomatonBasics
	include FiniteAutomatonConversions
	include FiniteAutomatonBasicFunctions
	include FiniteAutomatonLearnOCaml
end
# 1 "src/FiniteAutomaton.ml"
(*
 * FiniteAutomaton.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
 * set/2022 (amd) - Full restructuration.
 * jul/2021 (amd) - Improved Learn-OCaml support and error handling.
 * jun/2021 (amd) - Added checks for epsilon ('~') in the #validate method.
 * may/2021 (amd) - Added support for an extern representation.
 * jan/2021 (amd) - Module in an independent file and some cleanup.
 * dec/2019 (jg) - Main functionalities.
 * jun/2019 (amd) - Initial skeleton, inside the big file "OCamlFlat.ml".
 *)

(*
 * Description: Finite automata functionality.
 *
 * TODO: More cleanup.
 *)

open BasicTypes

module FiniteAutomatonAccept = (* AMD *)
struct
	open FiniteAutomatonSupport

	let initialConfigs fa w : configurations =
		Set.make [(fa.initialState,w)]

	let isAcceptingConfig fa (st,w) : bool =
		Set.belongs st fa.acceptStates && w = []

	let nextConfigs fa (st,w) : configurations =
		match w with
		| [] ->
			let empty = Set.filter (fun (st1,sy,_) -> st1 = st && sy = epsilon) fa.transitions in
				Set.map (fun (_,_,st2) -> (st2,[])) empty
		| x::xs -> 
			let nonEmpty = Set.filter (fun (st1,sy,_) -> st1 = st && sy = x) fa.transitions in
			let empty = Set.filter (fun (st1,sy,_) -> st1 = st && sy = epsilon) fa.transitions in
			let res1 = Set.map (fun (_,_,st2) -> (st2,xs)) nonEmpty in
			let res2 = Set.map (fun (_,_,st2) -> (st2,w)) empty in
				Set.union res1 res2

	let accept (fa: t) (w: word) : bool =
		ignore (Model.checkWord fa.alphabet w);
		Model.accept fa w initialConfigs nextConfigs isAcceptingConfig

	let acceptFull (fa: t) (w: word) : bool * path * trail =
		ignore (Model.checkWord fa.alphabet w);
		Model.acceptFull fa w initialConfigs nextConfigs isAcceptingConfig
end

module FiniteAutomatonGenerate = (* AMD *)
struct
	open FiniteAutomatonSupport
	open FiniteAutomatonAccept

	let nextConfigs2 fa _ (st,w) =
		let selected = Set.filter (fun (st1,_,_) -> st1 = st) fa.transitions in
			Set.map (fun (_,sy,st2) -> (st2,if sy = epsilon then w else sy::w)) selected

	let isAcceptingConfig2 fa (st,_) =
		Set.belongs st fa.acceptStates

	let getWord (_,w) = List.rev w;;

	let generate (fa: t) (len: int): words =
		Model.generate fa len initialConfigs nextConfigs2 isAcceptingConfig2 getWord

	let generateDumb (fa: t) (len: int): words = 
		Model.generateDumb fa fa.alphabet len initialConfigs nextConfigs isAcceptingConfig
end

module FiniteAutomatonPrivate =
struct
	open FiniteAutomatonSupport

	(*------Auxiliary functions---------*)

	(* get starting state, symbol, and/or end state of all transitions in set *)
	let transitionGet1 trns = Set.map ( fun (a,_,_) -> a ) trns
	let transitionGet2 trns = Set.map ( fun (_,b,_) -> b ) trns
	let transitionGet3 trns = Set.map ( fun (_,_,c) -> c ) trns
	let transitionGet23 trns = Set.map (fun (_,b,c) -> (b,c)) trns

	(* fuse all states into a new state *)
	let fuseStates sts =
		let l = List.map state2str sts in
			state (String.concat "_" l)

	(* checks if set ts has at least one transition from state st through symbol sy *)
	let hasTrans st sy ts = Set.exists (fun (x,y,_) -> x = st && y = sy) ts

	(* returns the set of state st and all its states reachable by an epsilon transition *)
	let nextEpsilon1 st ts =
		let trns = Set.filter (fun (a,b,c) -> st = a && b = epsilon) ts in
		let nextStates = transitionGet3 trns in
			Set.add st nextStates

	(* returns the set of states sts and all states reachable from sts through epsilon transitions *)
	let rec closeEmpty sts t =
		let ns = Set.flatMap (fun st -> nextEpsilon1 st t) sts in
			if (Set.subset ns sts) then ns else closeEmpty (Set.union sts ns) t

	(* futuro
		let rec closeEmpty sts t =
			Set.fixedPoint (Set.flatMap (fun st -> nextEpsilon1 st t)) sts
	*)

	(* returns states reachable from st through symbol sy *)
	let nextStates st sy t =
		let n = Set.filter (fun (a,b,c) -> st = a && sy = b) t in
			transitionGet3 n

	(**
	* This function verifies if the automaton is valid.
	* An automaton is considered valid if its initial and acceptance states belong to the set of all its states
	* and if all its transitions have states and symbols belonging to the set of all its states and its alphabet respectively.
	*
	* Desc: If the automaton is invalid, the cause could derive from any combination of the following
	* three options: either the initial state, one of the acceptance states, or one of the transitions does not follow the
	* previously discussed predicate. This method will print to the console stating which combination of these options caused
	* the automaton to be invalid
	*)
	let validate (name: string) (fa: t): unit =
	(* the alphabet must not contain " " *)
		let validAlphabet = not (Set.belongs epsilon fa.alphabet) in
	(* does initial state belong to the set of all states *)
		let validInitSt = Set.belongs fa.initialState fa.states in
	(* are all accepted states members of all states *)
		let validAccSts = Set.subset fa.acceptStates fa.states in
		let fromSt = transitionGet1 fa.transitions in
		let sy = transitionGet2 fa.transitions in
		let toSt = transitionGet3 fa.transitions in
		let alpha = Set.add epsilon fa.alphabet in
	(* do all transitions have states belonging to all states and symbols belonging to the alphabet *)
		let validTrns = (Set.subset fromSt fa.states)
					&& (Set.subset sy alpha) && (Set.subset toSt fa.states) in
			if not validAlphabet then
				Error.error name "The alphabet contains epsilon '~', and it should not" ();
			if not validInitSt then
				Error.error name "The initial state does not belong to the set of all states" ();
			if not validAccSts then
				Error.error name "Some accept states do not belong to the set of all states" ();
			if not validTrns then
				Error.error name "Some transitions are invalid" ()

	(**
	* This function verifies if the given word is accepted by the automaton
	* @param w:word -> word to be tested for acceptance
	* @returns bool -> true if w is accepted and false otherwise
	* Desc: Checks if the automaton accepts word w using configurations (that is, pairs formed by a state and
	* a remaining word) and a breadth-first approach as to deal with potential non-termination
	*)
	let acceptBreadthFirst (fa: t) (w: word): bool = false
	(*
		let rec acc cf t sta =
			match cf with
				[] -> false
				|(st,[])::ls ->
					let accepts = (Set.inter (closeEmpty (Set.make [st]) t) sta) <> Set.empty in
						accepts || acc ls t sta
				|(st,x::xs)::ls ->
					let n = nextStates st x t in
					let cfn = Set.map (fun c -> (c,xs)) n in
					let n2 = nextStates st epsilon t in
					let cfn2 = Set.map (fun c -> (c,x::xs)) n2 in
						acc (Set.flatten (Set.make [ls;cfn;cfn2])) t sta in
		acc (Set.make [(fa.initialState,w)]) fa.transitions fa.acceptStates
	*)

	

	(**
	* This function verifies if the given word is accepted by the automaton
	* @param w:word -> word to be accepted
	* @returns bool -> true if w is accepted and false otherwise
	* Desc: Checks if the automaton accepts word w using functions over sets of states
	*)
	let accept_disabled (fa: t) (w: word): bool =
		let transition sts sy t =
			let nsts = Set.flatMap (fun st -> nextStates st sy t) sts in
				Set.union nsts (closeEmpty nsts t) in
		let rec acceptX sts w t =
			match w with
				[] -> (Set.inter sts fa.acceptStates) <> Set.empty
				|x::xs -> let nextSts = transition sts x t in
					nextSts <> Set.empty && acceptX nextSts xs t in
		let i = closeEmpty (Set.make [fa.initialState]) fa.transitions in
			acceptX i w fa.transitions


	let acceptWithTracing (fa: t) (w:word): unit =
		let transition sts sy t =
			let nsts = Set.flatMap (fun st -> nextStates st sy t) sts in
				Set.union nsts (closeEmpty nsts t) in
		let rec acceptX sts w t =
			match w with
				[] -> [(w,sts)]
				|x::xs -> let nextSts = transition sts x t in
							let res = acceptX nextSts xs t in
								(w,sts)::res in
		let i = closeEmpty (Set.make [fa.initialState]) fa.transitions in
		let res = acceptX i w fa.transitions in
		let printRes w sts =
			Util.print ["('"; word2str w; "',["];
			Set.iter (fun st -> Util.print [state2str st; ";"]) sts;
			Util.print ["])"]
		in List.iter (fun (w,sts) -> printRes w sts; Util.print [";"]) res; Util.println []

	(**
	* This function generates all words of the given size which are accepted by the automaton
	* Precondition -> length >= 0
	* @param length:int -> size of all words to be generated
	* @returns words -> the set of all words with size length
	*)
	let generate_disabled (fa: t) (length: int): words =
		(* adds symbol to the left of all words *)
		let addSyToRWords symb ws = Set.map (fun l -> symb::l) ws in
		let hasAcceptState sts accSts = Set.exists (fun st -> Set.belongs st accSts) sts in
		let nxtNonEmptyTrns st ts = Set.filter (fun (a,b,_) -> a = st && b <> epsilon) ts in
		let rec gen n state transitions accSts =
			let clsEmpty = (closeEmpty (Set.make [state]) transitions) in
			if n = 0 then
				if hasAcceptState clsEmpty accSts then Set.make [[]] else Set.empty
			else
				let trnsSet = Set.flatMap (fun st -> nxtNonEmptyTrns st transitions ) clsEmpty in
				let rwords st1 l1 = gen (l1-1) st1 transitions accSts in
				let genX sy st l = addSyToRWords sy (rwords st l) in
						Set.flatMap (fun (_,sy,st) -> genX sy st n) trnsSet
		in
			gen length fa.initialState fa.transitions fa.acceptStates


	(**
	* This function generates all words up to a given size which are accepted by the automaton
	* Precondition -> length >= 0
	* @param length:int -> maximum size of all words to be generated
	* @returns words -> the set of all words with size length or less
	*)
	let generateUntil (fa: t) (length: int): words =
		(* adds symbol to the left of all words *)
		let addSyToRWords symb ws = Set.map (fun l -> symb::l) ws in
		let hasAcceptState sts accSts = Set.exists (fun st -> Set.belongs st accSts) sts in
		let nxtNonEmptyTrns st ts = Set.filter (fun (a,b,_) -> a = st && b <> epsilon) ts in
		let rec gen n state transitions accSts =
			let clsEmpty = (closeEmpty (Set.make [state]) transitions) in
			if n = 0 then
				if hasAcceptState clsEmpty accSts then Set.make [[]] else Set.empty
			else
				let trnsSet = Set.flatMap (fun st -> nxtNonEmptyTrns st transitions ) clsEmpty in
				let genX sy st l = addSyToRWords sy (gen (l-1) st transitions accSts) in
				let lenOneOrMore = Set.flatMap (fun (_,sy,st) -> genX sy st n) trnsSet in
				let lenZero = if hasAcceptState clsEmpty accSts then Set.make [[]] else Set.empty in
					Set.union lenOneOrMore lenZero
		in
			gen length fa.initialState fa.transitions fa.acceptStates


	(**
	* This function generates all states that are reachable from the given state. A state is reachable from s if there
	* exists a word that starting on s will lead to that state
	* @param s:state -> the given state
	* @returns states -> the set of all states reachable from s.
	*)
	let reachable (fa: t) (s:state): states =
		let neighbourSts st t = transitionGet3 (Set.filter (fun (a,_,_) -> a = st) t) in
		let nextStates sts t = Set.flatMap (fun st -> neighbourSts st t) sts in
		let remain s t = Set.filter (fun (a,_,_) -> not (Set.belongs a s)) t in
		let rec reach visited s t = if visited = s then Set.empty else Set.union s ( reach s (nextStates s t) (remain s t) ) in
			reach Set.empty (Set.make [s]) fa.transitions



	(**
	* This function generates all productive states. A state is productive if there exists a word that will lead said state
	* to an acceptance state
	* @returns states -> the set of all productive states
	* Desc: For each state of the automaton, this method applies the reachable method and checks if any of the resulting
	* states is an acceptance state, and if it is then that state will belong to the resulting set of productive states
	*)
	let productive (fa: t): states =
		let reachsAccSt st = Set.exists (fun s -> Set.belongs s fa.acceptStates ) (reachable fa st) in
			Set.filter (fun st -> reachsAccSt st) fa.states

	(**
	* This function generates the set of all useful states
	* @returns states -> the set of all useful states
	*)
	let getUsefulStates (fa: t): states =
		Set.inter (productive fa) (reachable fa fa.initialState)

	(**
	* This function generates the set of all non useful states
	* @returns states -> the set of all non useful states
	*)
	let getUselessStates (fa: t): states =
		Set.diff fa.states (getUsefulStates fa)

	(**
	* This function creates the equivalent automaton where all states are useful
	* @returns FiniteAutomaton.model -> the new equivalent automaton where all states are useful
	* Desc: The new automaton is created by eliminating from the original automaton all its non useful states, all transitions
	* that have a non useful state, and all symbols of the alphabet that only appear in said transitions
	*)
	let cleanUselessStates (fa: t): t =
		let usfSts = getUsefulStates fa in
		let usfTrs = Set.filter
						(fun (a,_,c) -> Set.belongs a usfSts && Set.belongs c usfSts)
						fa.transitions in
		let alf = transitionGet2 usfTrs in
		let usfAlf = Set.diff alf (Set.make [epsilon]) in
		let newAccSts = Set.inter fa.acceptStates usfSts in
		let usfSts = Set.add fa.initialState usfSts in
			{
				alphabet = usfAlf;
				states = usfSts;
				initialState = fa.initialState;
				transitions = usfTrs;
				acceptStates = newAccSts
			}

	(**
	* This function verifies if all the automaton's states are useful
	* @returns bool -> true if all states of the automaton are useful, false otherwise
	*)
	let areAllStatesUseful (fa: t): bool =
		let usfSts = getUsefulStates fa in
			Set.size fa.states = Set.size usfSts

	(**
	* This function converts the non-deterministic automaton into its deterministic equivalent
	*
	* @returns FiniteAutomaton.model -> the new deterministic automaton
	*
	* Desc: If the automaton to determinize is already deterministic,
	* the resulting automaton will be equal to the original
	*)
	let toDeterministic (fa: t): t =

		let move sts sy ts = Set.flatMap (fun st -> nextStates st sy ts ) sts in

		(* generates the set of states reachable from the given state set though the given symbol *)
		let newR oneR sy ts =
			let nxtSts = move oneR sy ts in
			let clsempty = closeEmpty nxtSts ts in
			Set.union nxtSts clsempty in

		(* creates all transitions (given state set, a given symbol, states reachable from set through given symbol) *)
		let rToTs r =
			let nxtTrans = Set.map (fun sy -> (r,sy,newR r sy fa.transitions)) fa.alphabet in
				Set.filter (fun (_,_,z) -> not (z = Set.empty)) nxtTrans in

		(* applies previous function to all state sets until no new set is generated *)
		let rec rsToTs stsD rD trnsD alph =
			let nxtTs = Set.flatMap (fun stSet -> rToTs stSet ) rD in
			let nxtRs = Set.map (fun (_,_,z) -> z) nxtTs in
			let newRs = Set.filter (fun r -> not (Set.belongs r stsD)) nxtRs in
			if newRs = Set.empty then (Set.union trnsD nxtTs) else
				rsToTs (Set.union newRs stsD) newRs (Set.union trnsD nxtTs) alph in


		let r1 = closeEmpty (Set.make [fa.initialState]) fa.transitions in

		(* all transitions of the new deterministic automaton *)
		let trnsD = rsToTs (Set.make [r1]) (Set.make [r1]) Set.empty fa.alphabet in

		let tds = Set.map (fun (a,b,c) -> (fuseStates (Set.toList a), b, fuseStates (Set.toList c))) trnsD in

		let newInitialState = fuseStates (Set.toList r1) in

		let stSet1 = Set.map (fun (a,_,_) -> a) trnsD in
		let stSet2 = Set.map (fun (_,_,c) -> c) trnsD in
		let stSet = Set.union stSet1 stSet2 in

		let isAccepState st = Set.belongs st fa.acceptStates in
		let hasAnAccepSt set = Set.exists (fun st -> isAccepState st ) set in
		let newAccStsSet = Set.filter (fun set -> hasAnAccepSt set) stSet in

		let newAllSts = Set.map (fun set -> fuseStates (Set.toList set)) stSet in
		let newAccSts = Set.map (fun set -> fuseStates (Set.toList set)) newAccStsSet in
			{
				alphabet = fa.alphabet;
				states = newAllSts;
				initialState = newInitialState;
				transitions = tds;
				acceptStates = newAccSts
			}

	(**
	* This function verifies if the automaton is deterministic
	* @returns bool -> true if automaton is deterministic, false otherwise
	* Desc: For each state s, this method checks if there exists 2 or more transitions with the same symbol from any
	* state belonging to closeempty of s, independently of the state which said transitions will lead to.
	* If there is no state for which this property is true, then the automaton is deterministic
	*)
	let isDeterministic (fa: t): bool =
		let trnsFromSt st ts = Set.filter (fun (st1,sy,_) -> st1 = st && sy <> epsilon) ts in
		let isStDeter st ts =
			let allSts = closeEmpty (Set.make [st]) ts in
			let allTs = Set.flatMap (fun st -> trnsFromSt st ts) allSts in
			let sys = transitionGet2 allTs in
				Set.size allTs = Set.size sys in
		let hasNondeterSt = Set.exists (fun st -> not (isStDeter st fa.transitions) )
								fa.states in
			not hasNondeterSt


	(* partition states by equivalence *)
	let equivalencePartition (fa: t): states set =
		let fa = toDeterministic fa in
		let fa = cleanUselessStates fa in
		let (inF, notF) = Set.partition (fun x -> Set.belongs x fa.acceptStates) fa.states in
		let distI1 = Set.product inF notF in

		let hasTransMulti sts sy ts = Set.partition (fun st -> hasTrans st sy ts) sts in
		let distI2 = Set.flatMap (fun sy -> Util.distrib2 Set.product
											(hasTransMulti fa.states sy fa.transitions))
						fa.alphabet in


		let distI = Set.union distI1 distI2 in

		let stsXSts = Set.product fa.states fa.states in

		(* generates all pairs of states that can reach the pair (st1,st2) through a transition with symbol sy *)
		let reachingSts st1 st2 sy p =
			let t1 = Set.filter (fun (_,y,z) -> z = st1 && y = sy) fa.transitions in
			let t2 = Set.filter (fun (_,y,z) -> z = st2 && y = sy) fa.transitions in
			let s1 = transitionGet1 t1 in
			let s2 = transitionGet1 t2 in
				Set.diff (Set.product s1 s2) p in

		let findAR p q = Set.flatMap (fun (a,b) -> Set.flatMap (fun sy -> reachingSts a b sy p) fa.alphabet) q in

		let distA = findAR distI distI in

		let rec aped p q = if (q = Set.empty || (Set.union p q) = stsXSts) then Set.union p q
			else aped (Set.union p q) (findAR (Set.union p q) q ) in

		let dist = aped distI distA in


		(* given for example states a b c d generates (a,a) (a,b) (a,c) (a,d) (b,b) (b,c) (b,d) (c,c) (c,d) (d,d) *)
		let rec halfCombs sts =
			match sts with
				[] -> Set.empty
				|x::xs -> Set.union (Set.product (Set.make [x]) (Set.make sts)) (halfCombs xs) in

		let halfTriang = halfCombs (Set.toList fa.states) in

		(* given set of equivalent states dicti, substitutes state st for its leftmost equivalent state according to dicti *)
		let rec translate st dicti =
			match dicti with
				[] -> st
				|(eq1,eq2)::xs -> if eq2 = st then eq1 else translate st xs in

		(* the set of equivalent state pairs are those not present in the set of distinct state pairs *)
		let equiv = Set.filter ( fun (a,b) -> not (Set.belongs (a,b) dist) &&
												not (Set.belongs (b,a) dist) ) halfTriang in

		let equivList = Set.toList equiv in
		let hasAny st1 st2 sta stb = (translate st1 equivList) = sta || (translate st2 equivList) = sta
									|| (translate st1 equivList) = stb || (translate st2 equivList) = stb in


		let rec agroup eq =
			match eq with
				| [] -> Set.empty
				| (a,b)::ls ->
					let (part1,part2) = Set.partition (fun (x,y) -> hasAny x y a b) (Set.make eq) in
					let gRemain = Set.flatMap (fun (c,d) -> Set.make [c;d]) part1 in
						Set.add (Set.union (Set.make [a;b]) gRemain) (agroup (Set.toList part2))
		in

		agroup equivList



	(**
	* This function minimizes the automaton
	* @returns FiniteAutomaton.model -> the new minimal equivalent automaton
	* Desc: The given automaton is minimized according to the process described in lecture a15.
	*)
	let minimize (fa: t): t =
		let fa = toDeterministic fa in
		let fa = cleanUselessStates fa in

		let (inF, notF) = Set.partition (fun x -> Set.belongs x fa.acceptStates) fa.states in
		let distI1 = Set.product inF notF in

		let hasTransMulti sts sy ts = Set.partition (fun st -> hasTrans st sy ts) sts in
		let distI2 = Set.flatMap (fun sy -> Util.distrib2 Set.product
											(hasTransMulti fa.states sy fa.transitions))
						fa.alphabet in


		let distI = Set.union distI1 distI2 in

		let stsXSts = Set.product fa.states fa.states in

		(* generates all pairs of states that can reach the pair (st1,st2) through a transition with symbol sy *)
		let reachingSts st1 st2 sy p =
			let t1 = Set.filter (fun (_,y,z) -> z = st1 && y = sy) fa.transitions in
			let t2 = Set.filter (fun (_,y,z) -> z = st2 && y = sy) fa.transitions in
			let s1 = transitionGet1 t1 in
			let s2 = transitionGet1 t2 in
				Set.diff (Set.product s1 s2) p in

		let findAR p q = Set.flatMap (fun (a,b) -> Set.flatMap (fun sy -> reachingSts a b sy p) fa.alphabet) q in

		let distA = findAR distI distI in

		let rec aped p q = if (q = Set.empty || (Set.union p q) = stsXSts) then Set.union p q
			else aped (Set.union p q) (findAR (Set.union p q) q ) in

		let dist = aped distI distA in


		(* given for example states a b c d generates (a,b) (a,c) (a,d) (b,c) (b,d) (c,d) *)
		let rec halfCombs sts =
			match sts with
				[] -> Set.empty
				|x::xs -> Set.union (Set.product (Set.make [x]) (Set.make xs)) (halfCombs xs) in
		let halfTriang = halfCombs (Set.toList fa.states) in

		(* given set of equivalent states dicti, substitutes state st for its leftmost equivalent state according to dicti *)
		let rec translate st dicti =
			match dicti with
				[] -> st
				|(eq1,eq2)::xs -> if eq2 = st then eq1 else translate st xs in

		(* the set of equivalent state pairs are those not present in the set of distinct state pairs *)
		let equiv = Set.filter ( fun (a,b) -> not (Set.belongs (a,b) dist) &&
												not (Set.belongs (b,a) dist) ) halfTriang in

		let equivList = Set.toList equiv in

		let eq = Set.map (fun (a,b) -> b) equiv in
		let newSts = Set.diff fa.states eq in
		let newInitSt = translate fa.initialState equivList in
		let newAccSts = Set.inter fa.acceptStates newSts in
		let newTrans = Set.map (fun (x,y,z) -> (translate x equivList,y,translate z equivList) ) fa.transitions in
			{
				alphabet = fa.alphabet;
				states = newSts;
				initialState = newInitSt;
				transitions = newTrans;
				acceptStates = newAccSts
			}

	(**
	* This function verifies if the automaton is minimal
	* @returns boolean -> true if automaton is minimal, false otherwise
	* Desc: The given automaton is considered minimal if the result of minimizing it is an automaton with the same
	* number of states
	*)
	let isMinimized (fa: t): bool =
		let min = minimize fa in
			Set.size fa.states = Set.size min.states
end

module FiniteAutomaton =
struct
	include FiniteAutomatonSupport
	open FiniteAutomatonAccept
	open FiniteAutomatonGenerate
	open FiniteAutomatonPrivate

	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
	let make (arg: t Arg.alternatives): t = make arg validate

	(* Exercices support *)
	let checkProperty (fa: t) (prop: string) =
		match prop with
			| "deterministic" -> isDeterministic fa
			| "minimized" -> isMinimized fa
			| "finite automaton" -> true
			| _ -> Model.checkProperty prop
	let checkExercise ex fa = Model.checkExercise ex (accept fa) (checkProperty fa)	
	let checkExerciseFailures ex fa = Model.checkExerciseFailures ex (accept fa) (checkProperty fa)

	(* Ops *)
	let stats = Model.stats
	let accept = accept
	let acceptFull = FiniteAutomatonAccept.acceptFull
	let generate = generate	
	let toDeterministic = toDeterministic	

	(* Class *)
	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model (make2 arg) as super	
		(* Representation *)
			method representation = representation
		(* Kind *)
			method isFiniteAutomaton : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Ops *)
			method acceptBreadthFirst (w: word): bool = acceptBreadthFirst representation w
			method accept (w: word): bool = accept representation w
			method acceptFull (w: word) : bool * path * trail = acceptFull representation w

			method acceptWithTracing (w:word): unit = acceptWithTracing representation w
			method generate (length: int): words = generate representation length
			method generateUntil (length: int): words = generateUntil representation length

			method reachable (s:state): states = reachable representation s
			method productive: states = productive representation
			method getUsefulStates: states = getUsefulStates representation
			method getUselessStates: states = getUselessStates representation
			method cleanUselessStates: model =
				let fa = cleanUselessStates representation in
					new model (Arg.Representation fa)
			method areAllStatesUseful: bool = areAllStatesUseful representation

			method toDeterministic: model =
				let fa = toDeterministic representation in
					new model (Arg.Representation fa)
			method isDeterministic: bool = isDeterministic representation

			method equivalencePartition: states set = equivalencePartition representation
			method minimize: model =
				let fa = minimize representation in
					new model (Arg.Representation fa)
			method isMinimized: bool = isMinimized representation
		(* Exercices support *)
			method checkProperty (prop: string) = Util.println["WWW"]; checkProperty representation prop
				
		(* Learn-OCaml support *)
			method moduleName = moduleName
			method xTypeName = xTypeName
			method xTypeDeclString : string = prelude
			method toDisplayString (name: string): string = solution name self#representation
			method example : JSon.t = example
		end
end

module FiniteAutomatonTop =
struct
	open FiniteAutomaton
	open FiniteAutomatonX

	let faI fa = internalize fa
	let faX fa = externalize fa

	let fa_load file = faX (make (Arg.File file))
	let fa_text text = faX (make (Arg.Text text))
	let fa_json json = faX (make (Arg.JSon json))
	let fa_predef name = fa_text (Examples.example name)


	let confX (s, w) = (state2str s, word2str w)
	let pathX (p: path) = pathX confX p
	let trailX (t: trail) = trailX confX t
	
	let stats () = RuntimeControl.stats ()

	let fa_accept fa w = accept (faI fa) (wordI w)

	let fa_path fa w =
		let (r,p,t) = acceptFull (faI fa) (wordI w) in
			pathX p

	let fa_trail fa w =
		let (r,p,t) = acceptFull (faI fa) (wordI w) in
			trailX t

	let fa_generate fa len = wordsX (generate (faI fa) len)

end

open FiniteAutomatonTop


(*

--------------------
let fa = fa_predef "dfa_astar";;

fa_generate fa 8;;

fa_accept fa "aaaa";;
fa_accept fa "aaaca";;

fa_path fa "aaaa";;
fa_path fa "aaaca";;

fa_trail fa "aaaa";;
--------------------

#print_depth 10000;;
#print_length 10000;;



let fa_astar = {| {
		kind : "finite automaton2",
		description : "this is an example",
		name : "dfa_astar",
		alphabet: ["a"],
		states : ["START", "Z1"],
		initialState : "START",
		transitions : [
			["START", "a", "START"],
			["START", "~", "START"],			
			["START", "~", "Z"],			
			["Z", "a", "Z"],
			["START", "a", "Z"]
		],
		acceptStates : ["START", "Z"]
		} |}
;;
let fa = fa_text fa_astar;;


fa_accept fa "aaa";;
fa_accept fa "aab";;

fa_path fa "aaa";;
fa_trail fa "aaa";;


let rec str n =
	if n = 0 then ""
	else "a" ^ str (n-1)
;;

let res (r,p,t) = r;;



let n = 10;;
let big = str 20;;
let bign = (str 10) ^ "b" ^ (str 10);;
let big3 = str (2*n);;
let bign3 = (str n) ^ "b" ^ (str n);;


let z = 1500 ;;
let r = fa_accept fa ((str z));;
stats ();;
let r = res (fa_acceptFull fa (str z));;
stats ();;





let a = fa_accept fa bign;;
stats ();;
let t = fa_acceptTrail fa  bign;;
stats ();;
let p = fa_acceptPath fa  bign;;
stats ();;
let (r,p,t) = fa_acceptFull fa  bign;;
stats ();;

*)

# 1 "src/RegularExpressionSupport.ml"
(*
 * RegularExpressionSupport.ml
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
 * sep/2022 (amd) - New submodules RegularExpressionConversions and RegularExpressionLearnOCaml
 * jul/2021 (amd) - Now this module is client of the Scanner module and
 *                  the erros are registered using the Error module.
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlatSupport.ml".
 *)

(*
 * Description: Support types and functions for REs including a parser for REs.
 *)

open BasicTypes

module RegularExpressionBasics =
struct
	type t =
		| Plus of t * t
		| Seq of t * t
		| Star of t
		| Symb of symbol
		| Empty
		| Zero

	type reTree =
		| Fail
		| Tree of word * t * reTree list

	let kind = "regular expression"

	let re_zero: t =
		Zero
end

module type RegularExpressionSyntaxSig =
sig
	open RegularExpressionBasics
	
	val parse : string -> t
	val toString : t -> string
	val show : t -> unit
end

module RegularExpressionSyntax : RegularExpressionSyntaxSig =
struct
	open Scanner
	open RegularExpressionBasics

	(*	Grammar:
			E -> E + E | E E | E* | c | (E) | ()

		Grammar with priorities:
			E -> T | T + E
			T -> F | F T
			F -> A | A*
			A -> P | c
			P -> (E) | ()
	*)
	let rec parseExp () =
		let t = parseTerm () in
			match curr() with
				| '+' -> skip(); Plus (t, parseExp ())
				| _ -> t

	and parseTerm () =
		let f = parseFactor () in
			match curr() with
				| '+' | ')' | ' ' -> f
				| _ -> Seq (f, parseTerm ())

	and parseFactor () =
		let a = parseAtom () in
			match curr() with
				| '*' -> skip(); (Star a)
				| _ -> a

	and parseAtom () =
		match curr() with
			| '~' -> skip(); Empty
			| '!' -> skip(); Zero
			| '(' -> skip(); parseParentised ()
			| '+' | '*' -> invalid "Invalid use of wildcard\n"
			| ' ' -> invalid "Premature end of expression\n"
			| c -> skip(); (Symb (char2symb c))

	and parseParentised () =
		let e = parseExp () in (
			match curr() with
				| ')' -> skip(); e
				| _ -> invalid "Right-parenthesis expected\n"
		)

	let parse s =
		Scanner.start "RegExpSyntax" s;
		try
			parseExp ()
		with Not_found ->
			Zero

	let rec toStringN n re =
		match re with
			| Plus(l, r) ->
					(if n > 0 then "(" else "") ^
					toStringN 0 l ^ "+" ^ toStringN 0 r
					^ (if n > 0 then ")" else "")
			| Seq(l, r) ->
					(if n > 1 then "(" else "") ^
					toStringN 1 l ^ toStringN 1 r
					^ (if n > 1 then ")" else "")
			| Star(r) ->
					toStringN 2 r ^ "*"
			| Symb(c) -> symb2str c
			| Empty -> "~"
			| Zero -> "!"

	let toString re =
		toStringN 0 re

	let show re =
		Util.println [toString re]
end

module RegularExpressionConversions =
struct
	open RegularExpressionBasics

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			re_zero
		else
			let re = JSon.fieldString j "re" in
				RegularExpressionSyntax.parse re

	let toJSon0 (rep: t): JSon.t =
	JSon.makeAssoc [
			("re", JSon.makeString (RegularExpressionSyntax.toString rep));
		]

	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 rep)

	let toJSon (rep: t): JSon.t = 
		toJSon2 (Entity.dummyId kind) rep
end


module RegularExpressionBasicFunctions =
struct
	open RegularExpressionBasics
	open RegularExpressionConversions
	
	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (rep: t): unit =
		let j = toJSon rep in
			JSon.show j

	let show2 (id: Entity.t) (rep: t): unit =
		let j = toJSon2 id rep in
			JSon.show j
end

module RegularExpressionX =
struct
	open RegularExpressionBasics
	
	type tx = string

	let internalize (re: tx): t =
		RegularExpressionSyntax.parse re

	let externalize (re: t): tx =
		RegularExpressionSyntax.toString re
end

module RegularExpressionLearnOCaml =
struct
	open RegularExpressionBasics
	open RegularExpressionX

	let moduleName =
		"RegularExpression"

	let xTypeName =
		"regularExpression"

	let solution (name: string) (rep: t): string =
		let repx = externalize rep in
		Printf.sprintf {zzz|
		%s	%s
		|zzz}	(* please, do not change this line *)
			(FiniteEnumerationLearnOCaml.displayHeader name xTypeName)
			(strD repx)

	let prelude : string = {|
		type regularExpression = string
		|}	(* please, do not change this line *)

	let example : JSon.t =
		JSon.parse {| {
			kind : "regular expression",
			description : "this is a simple example",
			name : "re example",
			re : "w*+(w+yz)*"
		}
		|}	(* please, do not change this line *)
end

module RegularExpressionSupport =
struct
	include RegularExpressionBasics
	include RegularExpressionSyntax
	include RegularExpressionConversions
	include RegularExpressionBasicFunctions
	include RegularExpressionLearnOCaml
end

module RegularExpressionSyntaxTests : sig end =
struct
	let active = false

	let test0 () =
		let re = RegularExpressionSyntax.parse "ab+~*" in
			RegularExpressionSyntax.show re

	let test1 () =
		let re = RegularExpressionSyntax.parse "~((a+b)*(cd)*)*" in
			RegularExpressionSyntax.show re

	let runAll =
		if Util.testing active "RegularExpressionSyntax" then begin
			test0 ();
			test1 ()
		end
end
# 1 "src/RegularExpression.ml"
(*
 * RegularExpression.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
 * set/2022 (amd) - Full restructuration.
 * jul/2021 (amd) - Improved Learn-OCaml support and error handling.
 * may/2021 (amd) - Added support for an extern representation.
 * jan/2021 (amd) - Module in an independent file and some cleanup.
 * dec/2019 (jg) - Main functionalities.
 * jun/2019 (amd) - Initial skeleton, inside the big file "OCamlFlat.ml".
 *)

(*
 * Description: Regular expressions functionality.
 *
 * TODO: More cleanup. Improve the regular expression simplifier.
 *)

open BasicTypes

module RegularExpressionPartialDerivative =
struct
	open RegularExpressionSupport

	let rec hasEmpty (rep: t): bool =
		match rep with
		| Plus(l, r) -> hasEmpty l && hasEmpty r
		| Seq(l, r) -> hasEmpty l || hasEmpty r
		| Star _ | Empty -> true
		| _ -> false

	let rightConcat (s: t set) (rep: t): t set =
		match rep with
		| Empty -> s
		| Zero -> Set.empty
		| _ -> Set.map (fun e -> Seq(e,rep)) s

	let rec partialDerivative (rep: t) (a: symbol): t set =
		let pd = partialDerivative in
		match rep with
		| Plus(l, r) -> Set.union (pd l a) (pd r a)
		| Seq(l, r) when hasEmpty l -> Set.union (rightConcat (pd l a) r) (pd r a)
		| Seq(l, r) -> rightConcat (pd l a) r
		| Star r -> rightConcat (pd r a) (Star r)
		| Symb c when c=a -> Set.make [Empty]
		| Symb c -> Set.empty
		| Empty -> Set.empty
		| Zero -> Set.empty

	let partialDerivativeUno (rep: t) (a: symbol): t =
		let s = partialDerivative rep a in
			Set.fold_right ((fun r s -> Plus(r,s))) s Zero
end

module RegularExpressionPrivate =
struct
	open RegularExpressionSupport

	(** aux *)
	let seqConcat aset bset = Set.flatMap (fun s1 -> Set.map (fun s2 -> s1@s2) bset) aset

	let validate (name: string) (rep: t): unit =
		(

						(*
				let representation = RegExpSyntax.parse "(((xx+ut)+(aaa+dss+ghf)+(xx+uu))ee)+bgc*+(jgg+bgcd)" in

				let rec lang rep =
					match rep with
						| RegExpSyntax.Plus(l, r) -> Util.print "pls: "; Util.print (RegExpSyntax.toString l); Util.print ", ";
						Util.print (RegExpSyntax.toString r); Util.println ""; Set.union (lang l) (lang r)
						| RegExpSyntax.Seq(l, r) -> Util.print "seq: "; Util.print (RegExpSyntax.toString l); Util.print ", ";
						Util.print (RegExpSyntax.toString r); Util.println ""; Set.union (lang l) (lang r)
						| RegExpSyntax.Star(r) -> Util.print "str: "; Util.print (RegExpSyntax.toString r); Util.println ""; (lang r)
						| RegExpSyntax.Symb(c) -> Set.make [c]
						| RegExpSyntax.Empty -> Set.empty
						| RegExpSyntax.Zero -> Set.empty
				in
				let a = lang representation in
				()
				*)
		)


	(**
	* This method generates the alphabet of all symbols in the expression
	* @returns symbols -> the set of all symbols in the expression's alphabet
	*)
	let rec alphabet rep: symbols =
	match rep with
		| Plus(l, r) -> Set.union (alphabet l) (alphabet r)
		| Seq(l, r) -> Set.union (alphabet l) (alphabet r)
		| Star(r) -> alphabet r
		| Symb(c) -> Set.make [c]
		| Empty -> Set.empty
		| Zero -> Set.empty

	(**
	* This method generates the language of the regular expression for when klenne is always zero
	* @returns words -> set of generated words
	*)
	let rec quasiLanguage rep: words =
		match rep with
		| Plus(l, r) -> Set.union (quasiLanguage l) (quasiLanguage r)
		| Seq(l, r) -> seqConcat (quasiLanguage l) (quasiLanguage r)
		| Star(r) -> Set.make [[]]
		| Symb(c) -> Set.make [[c]]
		| Empty -> Set.empty
		| Zero -> Set.empty

	(** aux *)
	let partition w =
		let rec partX w pword =
			match w with
				[] -> Set.empty
				| x::xs -> let fwp = pword@[x] in
								Set.add (fwp, xs) (partX xs fwp) in
		Set.add ([],w) (partX w [])

	(**
	* This method tests if a given word is accepted by the regular expression
	* @param w:word -> word to be tested for acceptance
	* @returns bool -> true if w is accepted and false otherwise
	*)
	let rec accept rep (w: word): bool =
		match rep with
		| Plus(l, r) -> (accept l w) || (accept r w)
		| Seq(l, r) ->
			let wpl = partition w in
				Set.exists (fun (wp1,wp2) -> (accept l wp1) && (accept r wp2)) wpl
		| Star(re) ->
			w = []
			|| (let wpl = Set.remove ([],w) (partition w) in
					Set.exists (fun (wp1,wp2) -> (accept re wp1) && (accept (Star re) wp2)) wpl)
		| Symb(c) -> w = [c]
		| Empty -> w = []
		| Zero -> false

	(**
	* This method returns the derivation tree for the word acceptance
	* @param w:word -> word to be tested for acceptance
	* @returns reTree list -> list of derivation trees
	*)
	let allTrees rep w : unit =

		let rec acc rep w =
			match rep with
			| Plus(l, r) ->
				let l1 = acc l w in
				let r1 = acc r w in
					List.map (fun t -> Tree (w, rep, [t])) (l1 @ r1)

			| Seq(l, r) ->
				let wps = partition w in
				let wpl = Set.toList wps in
				List.flatten ( List.map (fun (wp1, wp2) ->
					let tl = acc l wp1 in
					let tr = acc r wp2 in
						List.flatten (List.map (fun x -> List.map
							(fun y -> Tree (w, rep, [x; y])) tr)tl)
				) wpl)

			| Star(re) ->
				if w = [] then
					[Tree ([epsilon], rep, [])]
				else
					(let wps = Set.remove ([],w) (partition w) in
					let wpl = Set.toList wps in
					List.flatten (List.map (fun (wp1, wp2) ->
						let tl = acc re wp1 in
						let tr = acc (Star re) wp2 in
						List.flatten (List.map (fun x -> List.map
							(fun y -> Tree (w, rep, [x; y])) tr) tl)) wpl))

			| Symb(c) ->
				if w = [c] then
					[Tree (w, rep, [])]
				else
					[Tree (w, rep, [Fail])]

			| Empty ->
				if w = [] then
					[Tree ([epsilon], rep, [])]
				else
					[Tree (w, rep, [Fail])]

			| Zero -> [Tree (w, rep, [Fail])]

		in

		let ac = acc rep w in



		let rec isNotFail t =
			match t with
				Fail -> false
				| Tree ([], re, []) -> true
				| Tree (w, re, []) -> true
				| Tree ([], re, x::xs) -> (isNotFail x) && (isNotFail (Tree ([], re, xs)))
				| Tree (w, re, x::xs) -> (isNotFail x) && (isNotFail (Tree (w, re, xs)))
		in

		let ts = List.filter (fun t -> isNotFail t) ac in


		let printTreeX w re n =
			let s = String.make (3*n) ' ' in
			Util.println [s; word2str w; " -> "; RegularExpressionSyntax.toString re]
		in

		let rec printTree t n =
			match t with
				Fail -> Util.println ["Fail"]
				| Tree ([], re, []) -> Util.println ["TREH "]
				| Tree (w, re, []) -> printTreeX w re n
				| Tree ([], re, x::xs) -> printTreeX [] re n; printTree x (n+1); List.iter (fun t -> printTree t (n+1)) xs
				| Tree (w, re, x::xs) -> printTreeX w re n; printTree x (n+1); List.iter (fun t -> printTree t (n+1)) xs
		in

			List.iter (fun t -> printTree t 0) ts


	(**
	* This method generates all words up to the given length that are generated by the regular expression
	* @param length:int -> maximum length of all generated words
	* @returns words -> set of generated words
	*)
	let rec generate rep (len: int): words =
		match rep with
		| Plus(l, r) ->
				Set.union (generate l len) (generate r len)
		| Seq(l, r) ->
				let left = generate l len in
				let rigth w = generate r (len - (List.length w)) in
				let conc w = Util.concatAll w (Set.toList (rigth w)) in
					Set.flatMap (fun lw -> Set.make (conc lw)) left
		| Star r ->
				let exp = generate r len in
					Set.star exp len

			(* alternate version of star, leave 4 now

			let rec starX ws sz =
				if sz <= 0 then Set.make [[]]
				else
					let ws = Set.filter (fun x -> sz >= (List.length x)) ws in
					let newLn w = sz - (List.length w) in
					let tail w ws = Set.toList (starX ws (newLn w)) in
					let conc w ws = Util.concatAll w (tail w ws) in
					let track w ws = Set.add w (Set.make (conc w ws)) in
						Set.flatMap (fun w -> if w = [] then Set.make [[]] else track w ws) ws in
			let exp = generate r len in
				Set.add [] (starX exp len)*)

		| Symb(c) -> if len > 0 then Set.make [[c]] else Set.empty
		| Empty -> Set.make [[]]
		| Zero -> Set.empty


	(**
	* This method simplifies the regular expression
	*
	* @returns RegularExpression.model -> the new simplified, equivalent expression
	*)
	let simplify rep =

		(* various base case simplification rules to apply to the given expressions *)
		let simpX re =
			match re with
				(* plus *)
				(* a* + empty *)
				| Plus(Star(l), Empty) -> Star(l)
				| Plus(Empty, Star(r)) -> Star(r)
				(* a* + zero *)
				| Plus(Zero, r) -> r
				| Plus(l, Zero) -> l
				(* ~ + aa* *)
				| Plus(Empty, Seq(l, Star(r))) when l = r -> Star(r)
				| Plus(Empty, Seq(Star(l), r)) when l = r -> Star(l)
				| Plus(Seq(l, Star(r)), Empty) when l = r -> Star(r)
				| Plus(Seq(Star(l), r), Empty) when l = r -> Star(l)
				(* a* + a + empty *)
				| Plus(Star(l), Plus(Empty, r)) when l = r -> Star(l)
				| Plus(Star(l), Plus(r, Empty)) when l = r -> Star(l)
				| Plus(Plus(Empty, l), Star(r)) when l = r -> Star(r)
				| Plus(Plus(l, Empty), Star(r)) when l = r -> Star(r)
				(* a* + a *)
				| Plus(Star(l), r) when l = r -> Star(l)
				| Plus(l, Star(r)) when l = r -> Star(r)
				(* a + b = a||b when a = b *)
				| Plus(l, r) when l = r -> l
				(* seq *)
				| Seq(Empty, Empty) -> Empty
				| Seq(Zero, Zero) -> Zero
				| Seq(Empty, r) -> r
				| Seq(l, Empty) -> l
				| Seq(Zero, r) -> Zero
				| Seq(l, Zero) -> Zero
				(* (~+a)a* *)
				| Seq(Plus(Empty, l),Star(r)) when l = r -> Star(r)
				| Seq(Plus(l, Empty),Star(r)) when l = r -> Star(r)
				| Seq(Star(l),Plus(Empty, r)) when l = r -> Star(l)
				| Seq(Star(l),Plus(r, Empty)) when l = r -> Star(l)
				| Seq(Star(l),Star(r)) when l = r -> Star(l)
				(* star *)
				| Star(Star(r)) -> Star(r)
				| Star(Plus(Empty, r)) -> Star(r)
				| Star(Plus(r, Empty)) -> Star(r)
				| Star(Empty) -> Empty
				| Star(Zero) -> Empty
				| Star(r) -> re
				(* symb *)
				| Symb(c) -> Symb c
				(* empty *)
				| Empty -> Empty
				(* zero *)
				| Zero -> Zero
				| _ -> re
		in

		(* applies various base case simplifications to the various sub-expressions of regular expression re *)
		let rec simplify re =

			match re with
				| Plus(l,r) -> simpX (Plus(simplify l, simplify r))
				| Seq(l,r) -> simpX (Seq(simplify l, simplify r))
				| Star(re) -> simpX (Star(simplify re))
				| Symb(c) -> Symb c
				| Empty -> Empty
				| Zero -> Zero
		in

			simplify rep


			(*CODIGO JP*)

	type configuration =
		t * word
	type configurations =
		configuration set
	type path =
		configuration list
	type trail =
		configurations list

	let initialConfigs (rep: t) (w: word): configurations =
		Set.make [(rep, w)]

	let nextConfigs (rep: t) (re, w) =
		match w with
		| [] -> Set.empty
		| x :: xs ->
			let der = RegularExpressionPartialDerivative.partialDerivativeUno re x in
				if der = Zero then Set.empty
				else Set.make [(der, xs)]

	let nextConfigs2 (rep: t) (re, w) : configurations =
		match w with
			| [] -> Set.empty
			| x :: xs ->
				let der = RegularExpressionPartialDerivative.partialDerivative re x in
					Set.map (fun re -> (re,xs)) der 


	let isAcceptingConfig (rep: t) (re,w) : bool =
		RegularExpressionPartialDerivative.hasEmpty re && w = []

	let accept (res: t) (w: word) : bool =
		Model.accept res w initialConfigs nextConfigs2 isAcceptingConfig
	
	let acceptFull (res: t) (w: word) : bool * path * trail =
		Model.acceptFull res w initialConfigs nextConfigs2 isAcceptingConfig

		let nextConfigs3 (_: t) (len: int) (re, w) : configurations = 
			show re;
			Util.show (word2str w);
				Set.flatMap (fun sym ->
					Util.show (symb2str sym);
					let der = RegularExpressionPartialDerivative.partialDerivative re sym in
						Set.map (fun re -> (re, sym::w)) der 
					) (alphabet re)

		let isAcceptingConfig2 (rep: t) (re,w) =
			RegularExpressionPartialDerivative.hasEmpty re

		let getWord (_, w) = List.rev w;;

		let generate (rep: t) (len: int): words =
			Model.generate rep len initialConfigs nextConfigs3 isAcceptingConfig2 getWord
					
end

module RegularExpression =
struct
	include RegularExpressionSupport
	open RegularExpressionPartialDerivative
	open RegularExpressionPrivate
	
	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
	let make (arg: t Arg.alternatives): t = make arg validate

	(* Exercices support *)
	let checkProperty (re: t) (prop: string) =
		match prop with
		| "regular expression" -> true
		| _ -> Model.checkProperty prop
	let checkExercise ex re = Model.checkExercise ex (accept re) (checkProperty re)	
	let checkExerciseFailures ex re = Model.checkExerciseFailures ex (accept re) (checkProperty re)	

	(* Ops *)
	let stats = Model.stats
	let accept = accept
	let generate = generate
	let simplify = simplify
	let partialDerivative = partialDerivative
	let partialDerivativeUno = partialDerivativeUno
	
	(* Class *)
	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model (make2 arg) as super
		(* Representation *)
			method representation = representation
		(* Kind *)
			method isRegulartExpression : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Ops *)				
			method accept w = accept representation w
			method acceptFull (w: word) : bool * path * trail = acceptFull representation w
			method allTrees w = allTrees representation w
			method generate n = generate representation n
			method alphabet = alphabet representation
			method quasiLanguage = quasiLanguage representation
			method simplify = new model (Arg.Representation (simplify representation))

			method partialDerivative sy =
				let s = partialDerivative representation sy in
					Set.map (fun rep -> new model (Arg.Representation rep)) s

		(* Exercices support *)
			method checkProperty (prop: string) = checkProperty representation prop

		(* Learn-OCaml support *)
			method moduleName = moduleName
			method xTypeName = xTypeName
			method xTypeDeclString : string = prelude
			method toDisplayString (name: string): string = solution name self#representation
			method example : JSon.t = example
		end
end

module RegularExpressionTop =
struct
	open RegularExpression
(*
	let reF file = make (Arg.File file)
	let reT text = make (Arg.Text text)
	let reI x = internalize x
	let reX re = externalize (simplify re)

	let re_load file = externalize (reF file)
	let re_predef name = externalize (reT (Examples.example name))
	let re_text text = externalize (reI text)

	let re_accept re w = accept (reI re) (wordI w)
	let re_pd re sy = reX (partialDerivativeUno (reI re) (symbI sy))
*)
end

open RegularExpressionTop

(*
	let re_build (text: string): RegularExpressionBasics.tx =
		let re = new RegularExpression.model (Arg.Text text) in
			re#representationx

	let re_predef (name: string): RegularExpressionBasics.tx =
		re_build (Examples.example name)

	let re_convertTo (re: RegularExpressionBasics.t) : RegularExpressionBasics.tx =
		RegularExpression.toString re

	let re_convertFrom (re: RegularExpressionBasics.tx): RegularExpressionBasics.t = RegularExpression.parse re

	let re_accept (re: RegularExpressionBasics.tx) (w: string): bool =
		let re = re_convertFrom re in
		let a = new RegularExpression.model (Arg.Representation re) in
		let w = str2word w in
			a#accept w
*)
# 1 "src/GrammarSupport.ml"
(*
 * GrammarSupport.ml
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
 * jul/2024 (amd) - New file.
 *)

(*
 * Description: Support types and functions for Formal Grammars,
                including a parser.
 *)
 
open BasicTypes

module GrammarBasics =
struct
	type rule = { head : word; body : word }
	type rules = rule set

	type t = {
		alphabet : symbols;
		variables : variables;
		initial : variable;
		rules : rules
	}
	
	type configuration =
		symbol list * word
	type configurations =
		configuration set

	type path =
		configuration Path.path
	type trail =
		configuration Trail.trail

	type cfgTree =
		  Leaf of symbol
		| Root of symbol * cfgTree list

	let kind = "grammar"

	let cfg_zero: t = {
		alphabet = Set.empty;
		variables = Set.make [draftVar];
		initial = draftVar;
		rules = Set.empty;
	}
end

module type GrammarSyntaxSig =
sig
	open GrammarBasics

	val parse : string set -> rules
	val parseLine : string -> rules
	val toStringList : rules -> string list
	val (-->) : string -> string -> rule
	val rule2str : rule -> string
	val show : rules -> unit
end

module GrammarSyntax: GrammarSyntaxSig =
struct
	open Scanner
	open GrammarBasics

	let isWhite c =
		List.mem c [' '; '\t']

	let parseString delim =
		skip();	(* skip quotation mark *)
		let tk = getUntil delim in
			match peek () with
				| x when x = delim -> skip(); ("<" ^ tk ^ ">")
				| err -> expecting ("closing '" ^ (Char.escaped delim) ^ "'") err
			
	let rec parseHead () : word =
		match peek() with
			| ' ' -> invalid "Premature end of expression\n"
			| '-' -> []
			| '<' -> let symb = str2symb (parseString '>')
						in symb::parseHead ()
			| c -> skip();
					let symb = char2symb c in
						symb::parseHead ()
			
	let parseNeck (): unit =
		match peek() with
			| ' ' -> invalid "Premature end of expression\n"
			| '-' -> skip();
					if peek() = '>' then skip()
					else invalid "Bad neck\n"
			| _ -> invalid "Bad neck\n"

	let rec parseBody (): word list =
		match peek() with
			| ' ' -> [[]]
			| '|' -> skip(); []::parseBody ()
			| '<' -> let symb = str2symb (parseString '>') in
						(match parseBody () with
							| [] -> invalid "never happens 1"
							| x::xs -> (symb::x)::xs)		
			| c -> skip();
					match parseBody () with
						| [] -> invalid "never happens 2"
						| x::xs -> ((char2symb c)::x)::xs
	
	let parseLine line: rules =
		if String.trim line = "" then
			Set.empty
		else (
			Scanner.start "GrammarSyntax" line;
			try
				let finish l = if l = [] then [epsilon] else l in
				let h = parseHead () in
				let _ = parseNeck () in
				let bs = Set.make (parseBody ()) in
					Set.map (fun b -> {head=finish h; body=finish b}) bs
			with Not_found ->
				Set.empty
		)

	let parse rs: rules =
		Set.flatMap parseLine rs
	
	let rule2str {head=h; body=b} =
			(word2str h) ^ " -> " ^ (word2str b)

	let toString rs: string =
		let rl = Set.toList rs in
		String.concat "\n" (List.map rule2str rl)

	let toStringList rs: string list =
		let rl = Set.toList rs in
			List.map rule2str rl
	
	let (-->) h b : rule =
		{ head = str2word h; body = str2word b } ;;

	let show rs =
		Util.println [toString rs]
end

module GrammarConversions =
struct
	open GrammarBasics
	open GrammarSyntax

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			cfg_zero
		else {
			alphabet = JSon.fieldSymbolSet j "alphabet";
			variables = JSon.fieldSymbolSet j "variables";
			initial = JSon.fieldSymbol j "initial";
			rules = GrammarSyntax.parse (JSon.fieldStringSet j "rules");
		}

	let toJSon0 (rep: t): JSon.t =
		JSon.makeAssoc [
			("alphabet", JSon.makeSymbolSet rep.alphabet);
			("variables", JSon.makeSymbolSet rep.variables);
			("initial", JSon.makeSymbol rep.initial);
			("rules", JSon.makeStringSet (Set.map rule2str rep.rules))
		]
	
	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 rep)

	
	let toJSon (rep: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) rep

end

module GrammarBasicFunctions =
struct
	open GrammarBasics
	open GrammarConversions

	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (rep: t): unit =
		let j = toJSon rep in
			JSon.show j

	let show2 (id: Entity.t) (rep: t): unit =
		let j = toJSon2 id rep in
			JSon.show j
end

module GrammarBasicsX =
struct
	open GrammarBasics

	type tx = {
		alphabet : symbolX list;
		variables : variableX list;
		initial : variableX;
		rules : string list
	}

	let internalize (cfg: tx): t = {
		alphabet = symbolsI cfg.alphabet;
		variables = symbolsI cfg.variables;
		initial = symbI cfg.initial;
		rules = GrammarSyntax.parse (Set.make cfg.rules)
	}

	let externalize (cfg: t): tx = {
		alphabet = symbolsX cfg.alphabet;
		variables = symbolsX cfg.variables;
		initial = symbX cfg.initial;
		rules = GrammarSyntax.toStringList cfg.rules
	}
end

module GrammarLearnOCaml =
struct
	open GrammarBasics
	open GrammarBasicsX

	let moduleName =
		"Grammar"

	let xTypeName =
		"contextFreeGrammar"

	let solution (name: string) (rep: t): string =
		let repx = externalize rep in
		Printf.sprintf {zzz|
		%s{
			alphabet = %s;
			variables = %s;
			initial = %s;
			rules = %s
		}
		|zzz}	(* please, do not change this line *)
			(FiniteEnumerationLearnOCaml.displayHeader name xTypeName)
			(symbolsXD repx.alphabet)
			(symbolsXD repx.variables)
			(symbXD repx.initial)
			(stringsD repx.rules)

	let prelude : string =
		Printf.sprintf {zzz|
			type symbol = %s
			type variable = %s
			type rule = string
			type contextFreeGrammar = {
				alphabet : symbol list;
				variables : variable list;
				initial : variable;
				rules : rule list
			}
		|zzz}	(* please, do not change this line *)
				symbolTypeName symbolTypeName

		let example : JSon.t =
			JSon.parse {| {
				kind : "context free grammar",
				description : "this is an example",
				name : "cfg_simple",
				alphabet : ["0", "1"],
				variables : ["S", "X"],
				initial : "S",
				rules : [ "S -> 1S0 | X", "X -> 0X1 | ~" ]
			}
			|}	(* please, do not change this line *)
end

module GrammarSupport =
struct
	include GrammarBasics
	include GrammarSyntax
	include GrammarConversions
	include GrammarBasicFunctions
	include GrammarLearnOCaml
end

module GrammarSyntaxTests : sig end =
struct
	let active = false

	let test0 () =
		let cfg = Set.make [ "aSb -> a~~Tb | ~~ |"; "T -> aSb"; "->" ] in
		let rules = GrammarSyntax.parse cfg in
			GrammarSyntax.show rules

	let test1 () =
		let cfg = Set.make ["a<variable>b -> a<variable>b | ~"] in
		let rules = GrammarSyntax.parse cfg in
			GrammarSyntax.show rules

	let runAll =
		if Util.testing active "GrammarSyntax" then begin
			Util.header "test0";
			test0 ();
			Util.header "test1";
			test1 ();
			Util.header ""
		end
end
# 1 "src/Grammar.ml"
(*
 * Grammar.ml
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
 *  Written by Pedro Carlos (p.carlos)
 *)

(*
 * ChangeLog:
 *
 * jul/2024 (amd) - New file.
 *)

(*
 * Description: General grammar functionality.
 *)

open BasicTypes



module GrammarPrivate =
struct
	open GrammarSupport

	let validate (name: string) (gram: t): unit =
		(* Util.show (symb2str gram.initial);
		Set.iter (fun v -> Util.show (symb2str v)) gram.variables;
		if Set.size gram.variables = 0 then
			Util.show "No variables"
		else
			Util.show "Variables"; *)
		(* The alphabet must not contain epsilon ('~') *)
		let isValidAlphabet = not (Set.belongs epsilon gram.alphabet) in
		(* The variables must not contain epsilon ('~') *)
		let isValidVariables = not (Set.belongs epsilon gram.variables) in
		(* The alphabet and the variables must not intersect *)
		let isIntersectionValid = (Set.inter gram.variables gram.alphabet) = Set.empty in
		(* The initial symbol must be a variable *)
		let isInitialValid = Set.belongs gram.initial gram.variables in
	
		(* heads should not be empty, and must be a subset of valid symbols (alphabet + variables) *)
		let areRuleHeadsValid =
			let allHeadSymbols = Set.flatMap (fun r -> Set.make r.head) gram.rules in (* set of all heads in rules, heads *)
			let allValidSymbs = Set.union gram.alphabet gram.variables in
			Set.subset allHeadSymbols allValidSymbs && 		(* heads must be a subset of valid symbols (alphabet + variables) *)
			Set.for_all (fun r -> r.head <> []) gram.rules (* heads should not be empty*)
		in
	
		(* bodies must be a subset of valid symbols (alphabet + variables + epsilon) *)
		let areRuleBodiesValid =
			let allBodySymbols = Set.flatMap (fun r -> Set.make r.body) gram.rules in (* set of all bodies in rules, bodies *)
			(* Set.iter (fun s -> Printf.printf "%s\n" (symb2str s)) allBodySymbols; *)
			let allValidSymbs = Set.add epsilon (Set.union gram.alphabet gram.variables) in 
			Set.subset allBodySymbols allValidSymbs (* bodies must be a subset of valid symbols (alphabet + variables + epsilon) *)
		in
	
	
		if not isValidAlphabet then
			Error.error name
				"The alphabet contains epsilon '~', and it should not" ();
		if not isValidVariables then
			Error.error name
				"The variables contain epsilon '~', and it should not" ();
		if not isIntersectionValid then
			Error.error name
				"The intersection between the alphabet and the variables is not empty" ();
		if not isInitialValid then
			Error.error (symb2str gram.initial)
				"The initial symbol is not a declared variable" ();
		if not areRuleHeadsValid then
			Error.error name
				"Some rule heads contain invalid symbols or are empty" ();
		if not areRuleBodiesValid then
			Error.error name
				"Some rule bodies contain invalid symbols" ()
	

	(*Get the variables in a rule*)
	(* let rec symbolsInRule r =
		(* Set.union (Set.make r.head) (Set.make r.body) *)
		Set.make r.body
	
	let getAccessibleSymbolsAux (gram: t) vars =
		let getFromHead h =
			(* Set.map (fun r -> symbolsInRule r) (Set.filter (fun r -> List.mem h r.head) gram.rules) *)
			Set.map (fun r -> symbolsInRule r) (Set.filter (fun r -> Set.subset (Set.make r.head) vars) gram.rules)
		in
		Set.flatten (Set.flatMap getFromHead vars)

	let getAccessibleSymbols (gram: t) =
		let initial = Set.make [gram.initial] in
			Util.acumFixedPoint (getAccessibleSymbolsAux gram) initial *)

	(* Check if all rules are accessible *)

	let rechableSymbs (gram: t) set =
		Set.fold_right (fun r acc -> 
				if List.exists (fun symb -> Set.belongs symb set) r.head then
						Set.union (Set.make r.body) acc
				else 
						acc
		) gram.rules set

	let rec reachSymbs (gram :t) symbSet =
		let reach = rechableSymbs gram symbSet in
		if Set.subset reach symbSet then
			reach
		else
			reachSymbs gram reach
			
	let allRulesAccessible (gram: t): bool =
		let accessSymbols = reachSymbs gram (Set.make [gram.initial]) in
		let allVars = gram.variables in
		(* print_endline "Acessible Symbols:";
		Set.iter (fun v -> Printf.printf "%s\n" (symb2str v)) accessSymbols;
		print_endline "Acessible Variables:";
		Set.iter (fun v -> Printf.printf "%s\n" (symb2str v)) (Set.inter accessSymbols allVars);
		print_endline "All Variables:";
		Set.iter (fun v -> Printf.printf "%s\n" (symb2str v)) allVars; *)
		Set.equals (Set.inter accessSymbols allVars) allVars

	(* Get the bodies of the rules with a given head *)
	(* let bodiesOfHead h rl =
		let rls = Set.filter (fun r -> [h] = r.head) rl in
		let bodies = Set.map (fun r -> r.body) rls in
		(* Print the result before returning *)
		(* Printf.printf "Bodies of Head containing %s:\n" (word2str [h]);
		Set.iter (fun body -> Printf.printf "  %s\n" (word2str body)) bodies; *)
		bodies
	  
		
	(*show the productive symbols of the current grammar*)
	let productiveVariables (gram :t) =
		(*given a rule and a set of productive variables, verifies if given*)
		(*rule is productive*)
		let isRuleProductive body prodVars (gram: t) =
			List.for_all (fun c -> Set.belongs c gram.alphabet || Set.belongs c prodVars || c = epsilon) body
		in

		(*given a variable and a set of productive variables, verifies if given *)
		(*variable is productive*)
		let isVariableProductive h prodVars (gram:t) =
			let bodies = bodiesOfHead h gram.rules in
				Set.exists (fun body -> isRuleProductive body prodVars gram) bodies 
		in

		let productiveVariablesAux (gram: t) varP =
			Set.filter (fun v -> isVariableProductive v varP gram) gram.variables
		in

		let terminalSymbs (gram: t) =
			Set.fold_right (fun r acc -> 
				if Set.subset (Set.make r.body) (Set.add epsilon gram.alphabet) then
					Set.union (Set.make r.head) acc
				else
					acc
			) gram.rules Set.empty 
		in

		Util.acumFixedPoint (productiveVariablesAux gram) (Set.inter gram.variables (Set.add gram.initial (terminalSymbs gram))) 
	 *)
	
	let terminalSymbs (gram: t) set =
			Set.fold_right (fun r acc -> 
					if Set.exists (fun elem -> Set.belongs elem set) (Set.make r.body) then
							Set.union (Set.make r.head) acc
					else 
							acc
			) gram.rules set
	
	let rec productiveSymbs (gram :t) symbSet =
		let prod = terminalSymbs gram symbSet in
		if Set.subset prod symbSet then
			prod
		else
			productiveSymbs gram prod




	
	
	let allRulesProductive (gram: t): bool =
		let prodVars = productiveSymbs gram (Set.add epsilon gram.alphabet) in
		let allVars = Set.add epsilon (Set.union gram.variables gram.alphabet) in
		(* print_endline "Productive Variables:";
		Set.iter (fun v -> Printf.printf "%s\n" (symb2str v)) prodVars;
		print_endline "All Variables:";
		Set.iter (fun v -> Printf.printf "%s\n" (symb2str v)) allVars;  *)
		Set.equals prodVars allVars

	(* Checks if the grammar is clean (all symbols are productive and accessible) *)
	let isClean (gram: t): bool =
		allRulesAccessible gram && allRulesProductive gram


	(* Cleans the grammar by removing unproductive symbols and rules *)
	let cleanUnproductive (gram: t) =
		let allVars = gram.variables in
		let prodSymbols = productiveSymbs gram (Set.add epsilon gram.alphabet) in
		let prodVars = Set.inter prodSymbols gram.variables in
		(* print_endline "Productive Symbols:";
		Set.iter (fun v -> Printf.printf "%s\n" (symb2str v)) prodSymbols;
		print_endline "Productive Variables:";
		Set.iter (fun v -> Printf.printf "%s\n" (symb2str v)) prodVars;
		print_endline "All Variables:";
		Set.iter (fun v -> Printf.printf "%s\n" (symb2str v)) allVars;      *)

		if Set.equals prodVars allVars then
			gram
		else
			let filteredRules = Set.filter (fun rule ->
				List.for_all (fun var -> (Set.belongs var prodSymbols || var = epsilon)) rule.body
			) gram.rules in

			(*In the context of unproductive rules we can i have a rule like A -> AA and A -> ~ , in this case rule A -> AA should be removed*)
			(*First get the heads of the rules that derive epsilon*)
			let epsilonRuleHeads = Set.flat_map (fun r -> Set.make r.head) (Set.filter (fun r -> r.body = [epsilon]) filteredRules) in			
			(*get the rules that have as head and body the head of epsilonRules*)
			let unprodictiveEpsilonRules =
					Set.filter
							(fun r ->
									List.for_all (fun s ->
										Set.belongs s epsilonRuleHeads
									) r.head
								&&
									List.for_all (fun s ->
											Set.belongs s epsilonRuleHeads
									) r.body
							)
							filteredRules
			in		
			(*remove the unproductive rules*)
			let newFilteredRules = Set.diff filteredRules unprodictiveEpsilonRules in
			(* print_endline "Filtered Rules:";
			Set.iter (fun r -> Printf.printf "%s\n" (rule2str r)) newFilteredRules; *)
			{ gram with
			variables = Set.inter allVars prodVars;
			rules = newFilteredRules
			}

	(* Cleans the grammar by removing inaccessible symbols and rules *)
	let cleanInaccessible (gram: t) =
		let allVars = gram.variables in
		let accessSymbols = reachSymbs gram (Set.make [gram.initial]) in
		(* print_endline "Acessible Symbols:";
		Set.iter (fun v -> Printf.printf "%s\n" (symb2str v)) accessSymbols;
		print_endline "Acessible Variables:";
		Set.iter (fun v -> Printf.printf "%s\n" (symb2str v)) (Set.inter accessSymbols allVars);
		print_endline "All Variables:";
		Set.iter (fun v -> Printf.printf "%s\n" (symb2str v)) allVars;   *)
		let accessibleVars = Set.inter accessSymbols allVars in
		if Set.equals accessibleVars allVars then
			gram
		else
			let filteredRules = Set.filter (fun rule ->
				List.for_all (fun var -> Set.belongs var accessSymbols) rule.head 
				(* &&
				List.for_all (fun var -> Set.belongs var accessSymbols) rule.body *)
			) gram.rules in
			let filteredAlphabet = Set.inter gram.alphabet accessSymbols in
			{ gram with
			alphabet = filteredAlphabet;
			variables = accessibleVars;
			rules = filteredRules
			}  

	(* Cleans the grammar by removing unproductive and then inaccessible symbols and rules *)
	let clean (gram: t) =
		let cleanUnproductiveGram = cleanUnproductive gram in
		(* print_endline "show cleanUnproductiveGram:";
		show cleanUnproductiveGram;   *)
		(* print_endline "show cleanInacessibleGram:"; *)
		(* let cleanInaccessibleGram = cleanInaccessible gram in *)
		(* show cleanInaccessibleGram;   *)
		cleanInaccessible cleanUnproductiveGram


	(*most check if head has at least one non-terminal *)
	let isUnrestrictedGrammar (gram: t): bool =
		true
		(* List.for_all (fun r ->
		  List.exists (fun symb -> Set.belongs symb gram.variables) r.head
		) (Set.toList gram.rules) *)
	
	let hasEpsilonRules (gram: t)=
		let isEpsilonRule r =
			if r.body = [epsilon] then (
				if r.head = [gram.initial] then ( (* Special case: S → ε *)
					(* Ensure S doesn't appear on the body of any rule *)
					List.for_all (fun r' -> not (List.mem gram.initial r'.body)) (Set.toList gram.rules)
				)
				else false
			)
			else true (* Not an epsilon rule, so it's valid *)
		in
		List.for_all isEpsilonRule (Set.toList gram.rules)
	(* A grammar is monotonic if the length of the body of each rule is greater or equal to the length of the head. *)
	let isMonotonicGrammar (gram: t): bool =
		hasEpsilonRules gram && 
		List.for_all (fun r ->
			(* Check if the rule's head is the initial symbol and the body is epsilon *)
				(* if r.head = [gram.initial] && r.body = [epsilon] then
					false
				else   /// this applys for essentially noncontracting grammars *)
				List.length r.body >= List.length r.head
		) (Set.toList gram.rules)



	let isNoncontractingGrammar = isMonotonicGrammar



	(* A grammar is context-sensitive if it is monotonic and if each rule in P is either of the form S → ε where ε is the empty string, or of the form αAβ → αγβ *)
	let isContextSensitiveGrammar (gram: t): bool =
		(* Check if epsilon rule is valid: S → ε is allowed only if S is the start symbol and S does not appear in any rule's body *)
		let isContextRule (rule: rule) = (*check if rule are of the from αAβ → αγβ*)
			let rec findContextsHelper head body match_found =
				match head, body with
				| [], _ -> match_found  (* Return true if a match was found *)
				| _, [] -> false  (* No match found *)
				| h::ht, b::bt ->
				if h = b then
					findContextsHelper ht bt true  (* Continue matching and set match_found to true *)
				else
					Set.belongs h gram.variables &&  (* Check if h belongs to variables *)
					List.length body >= List.length head &&  (* Ensure rule is monotonic *)
					findContextsHelper ht bt match_found  (* Continue matching with the same match_found status *)
		  	in
		  	let findContexts head body =
				findContextsHelper head body false  (* Start with match_found set to false *)
		  	in
		  findContexts rule.head rule.body
		in
		(* Helper function to check if the head of the rule is a single nonterminal *)
		let isSingleNonterminal (rule: rule) =
			match rule.head with
			| [h] -> Set.belongs h gram.variables || h = epsilon
			| _ -> false
		in
		List.for_all (fun rule -> isSingleNonterminal rule || isContextRule rule) (Set.toList gram.rules)



	(*In a context-free grammar, each production rule is of the form A → α with A a single nonterminal symbol, and α a string of terminals and/or nonterminals  *)
	(*i.e the head of each rule is a single variable. *)
	let isContextFreeGrammar (gram: t): bool = (*verify if the head has exactly one symbol (length 1) and that this symbol belongs to the set of variables *)
		List.for_all (fun r -> List.length r.head = 1 && Set.belongs (List.hd r.head) gram.variables) (Set.toList gram.rules)
		
	(*in a left linear grammar all rules are of the form A → αw where α is either empty or a single nonterminal and w is a string of terminals *)
	let isLeftLinearGrammar (gram: t): bool =
		isContextFreeGrammar gram && 
		List.for_all (fun r ->
			match r.body with
			| [] -> 										
					true
			| [var] -> 					
					let belongs_to_vars = Set.belongs var gram.variables in
					let belongs_to_alphabet = Set.belongs var gram.alphabet in
					belongs_to_vars || belongs_to_alphabet || var = epsilon
			| var :: rest ->
					let var_belongs = Set.belongs var gram.variables in
					let rest_belongs = List.for_all (fun s -> Set.belongs s gram.alphabet) rest in
					var_belongs && rest_belongs
		) (Set.toList gram.rules)

	let isRightLinearGrammar (gram: t): bool =
		isContextFreeGrammar gram && 
		List.for_all (fun r ->
			match List.rev r.body with
			| [] -> 
					true
			| [var] -> 					
					let belongs_to_vars = Set.belongs var gram.variables in
					let belongs_to_alphabet = Set.belongs var gram.alphabet in
					belongs_to_vars || belongs_to_alphabet || var = epsilon (*Allow epsilon ?? *)
			| var :: rest ->
					let var_belongs = Set.belongs var gram.variables in
					let rest_belongs = List.for_all (fun s -> Set.belongs s gram.alphabet) rest in
					var_belongs && rest_belongs
		) (Set.toList gram.rules)

	(*linear grammar is a context-free grammar that has at most one nonterminal in the right-hand side of each of its productions. *)
	let isLinearGrammar (gram: t): bool =
		isContextFreeGrammar gram && 
		(List.for_all (fun r ->
			let var_count = List.fold_left (fun count symb ->
				if Set.belongs symb gram.variables then count + 1 else count) 
				0 
				r.body 
				in var_count <= 1 (* Only one variable allowed on the right-hand side *)
		) (Set.toList gram.rules))



	let rec starts_with sub lst =
		match sub, lst with
		| [], _ -> true
		| _, [] -> false
		| shd::stail, lhd::ltail -> shd = lhd && starts_with stail ltail
	
	let rec removeN n lst =
		match n, lst with
		| 0, _ -> lst
		| _, [] -> []
		| n, _::tail -> removeN (n - 1) tail
			

	let rec replace_subsequence original subseq replacement subseq_lenght = (*passing lenght to improve performance since List.lenght is O(n) *)
		match original with
		| [] -> []
		| _ when starts_with subseq original -> replacement @ (removeN subseq_lenght original) (*Returns on first occurence replacement*)
		| x::xs -> x :: (replace_subsequence xs subseq replacement subseq_lenght)

	let rec replace_subsequence_all original subseq replacement subseq_length =
		match original with
		| [] -> []
		| _ when starts_with subseq original -> 
			replacement @ (replace_subsequence_all (removeN subseq_length original) subseq replacement subseq_length)
		| x::xs -> x :: (replace_subsequence_all xs subseq replacement subseq_length)

	let hasEpsilonRules (gram: t)=
		let isEpsilonRule r =
			if r.body = [epsilon] then
				true
			else false
		in
		List.exists isEpsilonRule (Set.toList gram.rules)


	let removeEpsilonRules (gram: t) : t =
		(* Step 1: Identify Nullable Variables *)
		let rec nullableVars nullable =
			let newNullable = Set.fold_right (fun rule acc ->
				if List.for_all (fun symb -> Set.belongs symb nullable) rule.body then
					Set.union (Set.make rule.head) acc
				else
					acc
			) gram.rules nullable
			in
			if Set.equals newNullable nullable then
				nullable
			else
				nullableVars newNullable
		in
		let nullable = nullableVars (Set.filter (fun r -> r.body = [epsilon]) gram.rules |> Set.flatMap (fun r -> Set.make r.head)) in

		(* Step 2: Adjust Productions *)
		let newRules = Set.flatMap (fun rule ->
			let rec generateCombinations body =
				match body with
				| [] -> [[]]
				| hd :: tl ->
					let tlCombinations = generateCombinations tl in
					if Set.belongs hd nullable then
						List.map (fun comb -> hd :: comb) tlCombinations @ tlCombinations
					else
						List.map (fun comb -> hd :: comb) tlCombinations
			in
			let newBodies = generateCombinations rule.body in
			Set.make (List.map (fun body -> { head = rule.head; body }) newBodies)
		) gram.rules
		|> Set.filter (fun r -> r.body <> [] && r.body <> [epsilon] && r.head <> r.body) (* Step 3: Remove Epsilon Rules *)
		in

		{ gram with rules = newRules }

end

module GrammarAccept = (* Pedro + Artur *)
struct
	open GrammarSupport
	open GrammarPrivate
	(* open ContextFreeGrammarBasic *)


	let initialConfig (gram: t) (w: word) : configurations =
		Set.make [([gram.initial], w)]

	let rec containsSubSequence subSequence list =
		match subSequence, list with
		| [], _ -> true
		| _, [] -> false
		| sShd::sStail, lhd::ltail -> 
			if sShd = lhd then containsSubSequence sStail ltail
			else containsSubSequence subSequence ltail


	let showInFile (msg: string) : unit =
		let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "file.txt" in
		output_string oc (msg ^ "\n");
		close_out oc 
	


	let expand2 (gram: t) (sf,w) : configurations =
		let rules = Set.filter (fun r -> containsSubSequence r.head sf) gram.rules in
		(* Generate one configuration for each matching rule *)
		Set.flatMap (fun rule ->
				(* For each rule, generate just one new configuration by replacing the first and only the first occurence of its head with its body *)
				let rec combinations sf rule =
						match sf with
						| [] -> []
						| x::xs -> 
								if rule.body = [epsilon] then
										(replace_subsequence sf rule.head [] (List.length rule.head)) :: (List.map (fun c -> x :: c) (combinations xs rule))
								else
										(replace_subsequence sf rule.head rule.body (List.length rule.head)) :: (List.map (fun c -> x :: c) (combinations xs rule))
				in
				let newSfs = combinations sf rule in
				Set.make (List.map (fun newSf -> (newSf, w)) newSfs)
		) rules 

	let nextConfigs2 (gram: t) (sf, w) : configurations =
		showInFile("Starting nextConfigs for: " ^ word2str sf);  
		let configs = expand2 gram (sf, w) in
		if isMonotonicGrammar gram then
			let filtered = Set.filter (fun (sf', _) -> List.length sf' <= List.length w) configs in 
			Set.iter(fun (sf', w) -> showInFile("[" ^ word2str sf' ^ "," ^ word2str w ^ "]")) filtered;
			filtered
		else
			configs

	let nextConfigs2Full (gram: t) (sf, w) : configurations =
		showInFile("Starting nextConfigs for: " ^ word2str sf);  
		let configs = expand2 gram (sf, w) in
		configs

	let rec partOneX fs h =
		match fs, h with
		| [], [] -> (true, [])
		| [], _ -> (false, [])
		| x::xs, [] -> (true, fs)
		| x::xs, y::ys ->
			if x = y then
				partOneX xs ys
			else
				(false, [])
	
	let partOne fs h =
		let (a,b) = partOneX fs h in
			(a,h,b)
	
	let part fs heads =
		let tryMatch = List.map (partOne fs) heads in
		let reallyMatch = List.filter (fun (a, b, c) -> a) tryMatch in
			List.map (fun (a,b,c) -> (b,c)) reallyMatch

	let rec processHRest heads rules w (h, rest) =
		let xRules = Set.filter (fun r -> r.head = h) rules in
		let xBodies = Set.map (fun r -> if r.body = [epsilon] then [] else r.body) xRules in (*special case foe epsilon rule*)
		let ySet = expand heads rules rest w in
		Set.flatMap (fun (fs1, w) -> Set.map (fun fs2 -> (fs2@fs1, w)) xBodies) ySet
	and expand heads rules fs w =
		match fs with
		| [] -> Set.make [([],w)]
		| x :: xs ->
			let alternativesX = Set.make (part fs heads) in
			let useX = Set.flatMap (processHRest heads rules w) alternativesX in
			let ignoreX = expand heads rules xs w in
			let restoreX = Set.map (fun (fs, w) -> (x::fs, w)) ignoreX in
			Set.union useX restoreX


	let nextConfigs (gram: t) (sf, w) : configurations =
		showInFile("Starting nextConfigs for: " ^ word2str sf); 
		let rules = gram.rules in
		let heads = Set.toList (Set.map (fun r -> r.head) rules) in
		let configs = expand heads rules sf w in
		(* Set.iter(fun (sf', w) -> showInFile("[" ^ word2str sf' ^ "," ^ word2str w ^ "]")) configs;  *)
		if isMonotonicGrammar gram then
			let filtered = Set.filter (fun (sf', _) -> List.length sf' <= List.length w) configs in
			Set.iter(fun (sf', w) -> showInFile("[" ^ word2str sf' ^ "," ^ word2str w ^ "]")) filtered;
			filtered
		else
			let cs = Set.toList configs in
			let cs_rev = Set.make (List.rev cs) in
			Set.iter(fun (sf', w) -> showInFile("[" ^ word2str sf' ^ "," ^ word2str w ^ "]")) configs;
			cs_rev
			(* configs *)
	


	let isAcceptingConfig (gram: t) (genW, w) : bool =
		(* Printf.printf "genW: %s , w: %s\n" (word2str genW) (word2str w);  *)
		genW = w

	let accept (gram: t) (w: word) : bool =
		let processed_gram =
			gram
			|> (fun g -> if not (isClean g) then clean g else g)
			|> (fun g ->
				if isContextFreeGrammar g && hasEpsilonRules g
				then removeEpsilonRules g
				else g)
		in
		Model.accept processed_gram w initialConfig nextConfigs isAcceptingConfig

	let accept2 (gram: t) (w: word) : bool =
		let processed_gram =
			gram
			|> (fun g -> if not (isClean g) then clean g else g)
			|> (fun g ->
				if isContextFreeGrammar g && hasEpsilonRules g
				then removeEpsilonRules g
				else g)
		in
		Model.accept processed_gram w initialConfig nextConfigs2 isAcceptingConfig


	let acceptFull (gram: t) (w: word) : bool * path * trail =
		Model.acceptFull gram w initialConfig nextConfigs2 isAcceptingConfig

	let split_at n lst =
		let rec aux i acc = function
			| [] -> (List.rev acc, [])
			| h :: t as l -> if i = 0 then (List.rev acc, l) else aux (i - 1) (h :: acc) t
		in
		aux n [] lst

	let find_applied_rule (gram: t) (current: symbol list) (next: symbol list) : rule option =
		let rec find_rule rules =
			match rules with
			| [] -> None
			| rule :: rest ->
			let head_len = List.length rule.head in
			let rec check_sublist lst =
				match lst with
				| [] -> false
				| _ when List.length lst < head_len -> false
				| _ ->
				let (prefix, suffix) = split_at head_len lst in
				if prefix = rule.head then
					let replaced = List.append rule.body suffix in
					if replaced = next then true else check_sublist (List.tl lst)
				else check_sublist (List.tl lst)
			in
			if check_sublist current then Some rule else find_rule rest
		in
		find_rule (Set.toList gram.rules)
		
	(* let find_applied_rules (gram: t) (path: path) : rule list =
				print_endline ("Path: " ^ 
		  (String.concat " -> " (List.map (fun (symbols, _) -> 
			"[" ^ (String.concat ", " (List.map BasicTypes.symb2str symbols)) ^ "]") path))
		);
	  let rec aux path acc =
		match path with
		| [] | [_] -> List.rev acc
		| (current, _) :: ((next, _) :: _ as rest) ->
		  match find_applied_rule gram current next with
		  | Some rule -> aux rest (rule :: acc)
		  | None -> aux rest acc
	  in
	  aux path [] *)	
	let string_of_symbol_list symbols =
	  "[" ^ (String.concat "; " (List.map symb2str symbols)) ^ "]"

	let count_subsequence_occurrences subseq lst =
		let rec aux count lst =
			match lst with
			| [] -> count
			| _ when starts_with subseq lst -> aux (count + 1) (List.tl lst)
			| _ :: tl -> aux count tl
		in
	aux 0 lst

	let find_applied_rules (gram: t) (path: path) =
		let rule_map = Hashtbl.create (List.length path) in
		let rec aux i =
			if i < List.length path - 1 then
				let current = fst (List.nth path i) in
				let next = fst (List.nth path (i + 1)) in
				Printf.printf "Current: %s, Next: %s\n" (string_of_symbol_list current) (string_of_symbol_list next);
				let applicable_rules = Set.filter (fun rule -> 
					let head_current_occurences = count_subsequence_occurrences rule.head current in
					let head_next_occurences = count_subsequence_occurrences rule.head next in
					let body_next_occurences = count_subsequence_occurrences rule.body next in
					head_current_occurences > 0 && body_next_occurences > 0 &&
					head_next_occurences <= head_current_occurences
				) gram.rules in
				Hashtbl.add rule_map (current, i) (Set.toList applicable_rules);
				aux (i + 1)
		in
		aux 0;
		Hashtbl.add rule_map ((fst (List.nth path (List.length path - 1))), (List.length path - 1)) [];
		rule_map


	(* let rec get_tree (gram: t) (w: word) path =
			match path with
			| [] -> [||]
			| sf :: rest ->
					let configs = Set.map (fun (sf', w) -> sf') (nextConfigs2 gram (sf, w)) in 
					Array.append [| configs |] (get_tree gram w rest)
	
	
	let build_tree gram w path =
		let word_path = List.map fst path in
		let rec build_tree_aux gram w path depth =
				if depth <= 0 then
						Leaf [epsilon]
				else
						match path with
						| [] -> Leaf [epsilon]
						| parent :: rest ->
								let configs = Set.map (fun (sf', _) -> sf') (nextConfigs2 gram (parent, w)) in
								let children = Set.toList configs in
								Node (parent, List.map (fun child -> build_tree_aux gram w [child] (depth - 1)) children)
		in
		build_tree_aux gram w word_path (List.length word_path)

	let rec print_tree tree =
		let rec aux t indent =
			match t with
			| Leaf data ->
					Printf.printf "%sLeaf: %s\n" (String.make indent ' ') (String.concat ", " (List.map symb2str data))
			| Node (parent, children) ->
				Printf.printf "%sNode: %s\n" (String.make indent ' ') (word2str parent);
				List.iter (fun child -> aux child (indent + 2)) children
		in
		aux tree 0 *)
end

module GrammarGenerate = 
struct
	open GrammarSupport
	open GrammarAccept
	open GrammarPrivate


	let expandGenerate (gram: t) (len: int) (sf,w) : configurations =
		let rules = gram.rules in
		let heads = Set.toList (Set.map (fun r -> r.head) rules) in
		let configs = expand heads rules sf w in
		if isMonotonicGrammar gram then
			let filtered = Set.filter (fun (sf', _) -> List.length sf' <= len) configs in
			filtered
		else
			configs

	let nextConfigsGenerate (gram: t) (len: int) (sf, w) : configurations =
		(* showInFile("Starting nextConfigs for: " ^ word2str sf);  *)
		let res = expandGenerate gram len (sf, w) in
			(* let has_only_alphabet_symbols config =
				let configuration = fst config in 
				let count = List.fold_left (fun acc s -> if Set.belongs s gram.alphabet then acc + 1 else acc) 0 configuration in
				count >= len

			in
			(* Set.iter (fun (sf, w) -> print_endline ("[" ^ word2str sf ^ "," ^ word2str w ^ "]")) res; *)
			if isMonotonic gram then
				let filtered = Set.filter (fun s -> not (has_only_alphabet_symbols s)) res in
				Set.iter (fun (sf, w) -> showInFile ("[" ^ word2str sf ^ "," ^ word2str w ^ "]")) filtered;
				filtered
			else *)
				(* Set.iter (fun (sf, w) -> print_endline ("[" ^ word2str sf ^ "," ^ word2str w ^ "]")) res;   *)
			res 

				(*  *)
	let lenRef = ref 0
				(*  *)

	let isAcceptingConfigGenerate (gram: t) (sf, w) : bool =
		List.for_all(fun sym -> Set.belongs sym gram.alphabet) sf

	let isTerminalSymbol (symbol: symbol) : bool =
		let str = symb2str symbol in
		not ("A" <= str && str <= "Z") && not (String.get str 0 = '<' && String.get str (String.length str - 1) = '>')  

	let getWord (sf, _) = List.filter (fun symb -> isTerminalSymbol symb) sf

	let generate (gram: t) (len: int) : words =
		lenRef := len;
		let processed_gram =
			gram
			|> (fun g -> if not (isClean g) then clean g else g)
			|> (fun g ->
				if isContextFreeGrammar g && hasEpsilonRules g
				then removeEpsilonRules g
				else g)
		in
		show processed_gram;
		assert (isMonotonicGrammar processed_gram);
		Model.generate processed_gram len initialConfig nextConfigsGenerate isAcceptingConfigGenerate getWord

end

module GrammarConversion = (* Pedro + Artur *)
struct
	open GrammarSupport
	open GrammarPrivate
	open GrammarGenerate

	let generateNewVariable variables=
		let start = 65 in (* ASCII value for 'A' *)
		let rec auxGenerateNewVariable i =
			if i > 90 then (* ASCII value for 'Z' No more capital letters available for new nonterminals*)
				Symbol.str2symb (IdGenerator.genVar "A")
			else
				let newVar = Char.uppercase_ascii (char_of_int i) in
				if Set.belongs (Symbol.str2symb (Char.escaped newVar)) variables then
					auxGenerateNewVariable (i + 1)
				else
					Symbol.str2symb (Char.escaped newVar)
		in
		auxGenerateNewVariable start




		
	(*HOW TO DO CSG to Kuroda normal form: 
	Ensure the grammar is context-sensitive 
	Remove useless symbols:  
		Ensure all nonterminals can derive a terminal string and can be reached from the start symbol. Use the clean.
	Convert long productions to binary form:  
		Break down rules with more than two nonterminals or terminals (e.g.,  A -> X_1 X_2 X_3 ) into binary forms, using intermediate nonterminals:
		A -> X_1 A_1, A_1 -> X_2 X_3
	Handle terminal symbols:  
		If a terminal appears with a nonterminal (e.g.,  A -> aB ), introduce a new nonterminal for the terminal:
		A -> T_a B, T_a -> a
	*)
		(* Helper function to count variables in a list of symbols *)
		let countVariables symbols variables =
			List.fold_left (fun count symb -> if Set.belongs symb variables then count + 1 else count) 0 symbols
		
		(* Helper function to find consecutive non-terminals in a list of symbols *)
		let rec findConsecutiveNonTerminals variables body =
			match body with
			| [] | [_] -> None
			| x :: y :: xs ->
				if Set.belongs x variables && Set.belongs y variables then
					Some [x; y]
				else
					findConsecutiveNonTerminals variables (y :: xs)
		
		(* Helper function to find a sequence of a variable and an alphabet symbol *)
		let rec findSequence variables alphabet body =
			match body with
			| [] | [_] -> None
			| x :: y :: xs ->
				if (Set.belongs x variables && Set.belongs y alphabet) || (Set.belongs x alphabet && Set.belongs y variables) then
					Some [x; y]
				else
					findSequence variables alphabet (y :: xs)
		
		(* Helper function to find an alphabet symbol in a sequence *)
		let rec findAlphabetSymbol alphabet sequence =
			match sequence with
			| [] -> str2symb "a" (* not reached *)
			| x :: xs ->
				if Set.belongs x alphabet then
					x
				else
					findAlphabetSymbol alphabet xs
		
		(* Main transformation function *)
		let rec transformGrammar gram =
			let longProductions = Set.filter (fun r -> countVariables r.body gram.variables > 2) gram.rules in
			let mixedProductions = Set.filter (fun r ->
				List.exists (fun s -> Set.belongs s gram.alphabet) r.body &&
				List.exists (fun s -> Set.belongs s gram.variables) r.body
			) gram.rules in
		
			if Set.isEmpty longProductions && Set.isEmpty mixedProductions then
				gram
			else
				let gram =
					if not (Set.isEmpty longProductions) then
						let longProduction = Set.hd longProductions in
						let newVariable = generateNewVariable gram.variables in
						let consecutiveNonTerminals = findConsecutiveNonTerminals gram.variables longProduction.body in
						let newRules = 
							List.map (fun rule ->
								match consecutiveNonTerminals with
								| Some cn -> 
									let new_body = replace_subsequence rule.body cn [newVariable] 2 in
									{ rule with body = new_body }
								| None -> rule
							) (Set.toList gram.rules)
						in
						let newRules = Set.add {head = [newVariable]; body = Option.get consecutiveNonTerminals} (Set.make newRules) in
						{gram with rules = newRules; variables = Set.add newVariable gram.variables}
					else
						gram
				in
		
				let gram =
					if not (Set.isEmpty mixedProductions) then
						let mixedProduction = Set.hd mixedProductions in
						let sequence = findSequence gram.variables gram.alphabet mixedProduction.body in
						let alphabetSymbol = findAlphabetSymbol gram.alphabet (Option.get sequence) in
						let newVariable = generateNewVariable gram.variables in
						let newRules = 
							List.map (fun rule ->
								match sequence with
								| Some seq -> 
									let new_body = replace_subsequence rule.body [alphabetSymbol] [newVariable] 1 in
									let new_head = replace_subsequence rule.head [alphabetSymbol] [newVariable] 1 in
									{ head = new_head; body = new_body }
								| None -> rule
							) (Set.toList gram.rules)
						in
						let newRules = Set.add {head = [newVariable]; body = [alphabetSymbol]} (Set.make newRules) in
						{gram with rules = newRules; variables = Set.add newVariable gram.variables}
					else
						gram
				in
		
				transformGrammar gram
		
		(* Main function to convert grammar to Kuroda Normal Form *)
	let kurodaNormalForm (gram: t) : t =
		gram
		|> clean
		|> transformGrammar


	(* 
	NOTE:
	Conversely, every noncontracting grammar that does not generate the empty string 
	can be converted to Kuroda normal form.
	
	A straightforward technique attributed to György Révész 
	transforms a grammar in Kuroda normal form to a 
	context-sensitive grammar: AB → CD is replaced 
	by four context-sensitive rules AB → AZ, AZ → WZ, WZ → WD and WD → CD. *)

	let makeContextRules (gram: t) : t =
		let rec processRules rulesToCheck gramAux =
			match rulesToCheck with
			| [] -> gramAux
			| rule :: rest ->
					if List.length rule.head = 2 && List.length rule.body = 2 then 
							match rule.head, rule.body with
							| [a; b], [c; d] ->
								if a <> c && b <> d then
									let z = generateNewVariable gramAux.variables in
									let w = generateNewVariable (Set.union gramAux.variables (Set.make [z])) in
									let new_variables = Set.add z (Set.add w gramAux.variables) in
							
									let new_rules = Set.add {head = [a; b]; body = [a; z]} gramAux.rules in
									let new_rules = Set.add {head = [a; z]; body = [w; z]} new_rules in
									let new_rules = Set.add {head = [w; z]; body = [w; d]} new_rules in
									let new_rules = Set.add {head = [w; d]; body = [c; d]} new_rules in
									processRules rest {gramAux with rules = (Set.remove rule new_rules); variables = new_variables}
								else
									processRules rest gramAux
							| _ -> failwith  "No supposed to happen, matching error"
					else processRules rest gramAux
					
		in
		processRules (Set.toList gram.rules) gram

	let nonContractingToCSG (gram: t) : t =
			if isContextSensitiveGrammar gram then
					gram
			else
					if isNoncontractingGrammar gram then
						let kuroda_gram = kurodaNormalForm gram in
						(* print_endline "Kuroda Grammar:";
						show kuroda_gram; *)
						(* let new_gram = makeContextRules kuroda_gram in *)
						(* print_endline "New Grammar:"; *)
						makeContextRules kuroda_gram
					else
							failwith "Grammar is not noncontracting"

	(*HOW TO DO Grammar to Penttonen normal form: 
	Perform the Kuroda Normal Form Conversion
	Remove unit productions:  
		Eliminate any unit productions of the form  A -> B , where both  A  and  B  are nonterminals.*)
	let penttonenNormalForm (gram: t) : t =
		if isContextSensitiveGrammar gram then
			let rec removeUnitProductions (gram: t) : t =
					(* Identify unit productions *)
					let unitProductions = Set.filter (fun r -> List.length r.head = 1 
							&& List.length r.body = 1 
							&& Set.belongs (List.hd r.body) gram.variables
							&& Set.belongs (List.hd r.head) gram.variables) 
					gram.rules in

					if Set.isEmpty unitProductions then
							gram
					else
					(* Select a unit production *)
					let unitProduction = Set.hd unitProductions in
					let symbolToReplace = List.hd unitProduction.head in
					let replacementSymbol = List.hd unitProduction.body in
					let replace_symbol lst =
							List.map (fun x -> if x = symbolToReplace then replacementSymbol else x) lst
					in
					(* Replace occurrences of unitProduction.head with unitProduction.body in other rules *)
					let newRules = 
							List.filter (fun rule -> rule.head <> rule.body) (
									List.map (fun rule ->
											let new_head = replace_symbol rule.head in
											let new_body = replace_symbol rule.body in
											{ head = new_head; body = new_body }
									) (Set.toList gram.rules)
							)
					in
					let newVariables = Set.remove symbolToReplace gram.variables in
					let newInitial = if gram.initial = symbolToReplace then replacementSymbol else gram.initial in
					removeUnitProductions {gram with rules = (Set.make newRules); variables = newVariables; initial = newInitial}
			in
			(* let gram1 = kurodaNormalForm gram in
					print_endline "kuroda";
			show gram1;
			let gram2 = makeContextRules gram1 in
					print_endline "context";
			show gram2;
			let gram3 = removeUnitProductions gram2 in
					print_endline "removeUnitProductions";
			show gram3; *)
			gram
			|> kurodaNormalForm
			|> makeContextRules
			|> removeUnitProductions
		else
			failwith "Grammar is not context sensitive"
       
		
end


module GrammarGeneration = 
struct
	open GrammarSupport
	open GrammarPrivate


	let generate_random_grammar num_variables num_terminals num_rules : t =
		let generate_vars count =
			List.init count (fun i -> str2symb ("<V" ^ string_of_int (i + 1) ^ ">"))
		in
		let generate_terminals count =
				if count > 36 then
						failwith "Exceeded the alphabet and digit limit"
				else
						List.init count (fun i ->
								if i < 26 then
										str2symb (String.make 1 (Char.chr (97 + i))) (* 'a' to 'z' *)
								else
										str2symb (String.make 1 (Char.chr (48 + (i - 26)))) (* '0' to '9' *)
						)
		in
	
		let variables = Set.make (generate_vars num_variables) in
		let terminals = Set.make (generate_terminals num_terminals) in
		let initial = List.hd (Set.toList variables) in
	
		let all_symbols = Set.toList (Set.union terminals variables) in
	
		let random_rule_part () =
			let rule_part_length = Random.int 3 + 1 in (* Body length between 1 and 3 *)
			List.init rule_part_length (fun _ -> List.nth all_symbols (Random.int (List.length all_symbols)))
		in
	
		let rules =
			let initial_rule = 
					{
							head = [initial];
							body = random_rule_part ();
					}
			in
			let rec generate n acc =
					if n = 0 then acc
					else
							let head = random_rule_part () in
							let body = random_rule_part () in
							let rule = { head; body } in
							generate (n - 1) (Set.add rule acc)
			in
			generate (num_rules - 1) (Set.add initial_rule Set.empty)
		in
	
		{
			alphabet = terminals;
			variables;
			initial;
			rules;
		}


end


module Grammar =
struct
    include GrammarSupport
    open GrammarPrivate

    (* Make *)
    let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
    let make (arg: t Arg.alternatives): t = make arg validate

    let isUnrestrictedGrammar = isUnrestrictedGrammar
    let isContextFreeGrammar = isContextFreeGrammar
    let isLinearGrammar = isLinearGrammar
    let isRightLinearGrammar = isRightLinearGrammar
    let isLeftLinearGrammar = isLeftLinearGrammar
    let isContextSensitiveGrammar = isContextSensitiveGrammar
    let isMonotonicGrammar = isMonotonicGrammar
    let isNoncontractingGrammar = isNoncontractingGrammar
		let removeEpsilonRules = removeEpsilonRules
		let hasEpsilonRules = hasEpsilonRules
		

	(*Conversions*)
	let kurodaNormalForm = GrammarConversion.kurodaNormalForm
	let penttonenNormalForm = GrammarConversion.penttonenNormalForm
	let nonContractingToCSG = GrammarConversion.nonContractingToCSG
	(* Clean *)
	let allRulesAccessible = allRulesAccessible
	let allRulesProductive = allRulesProductive
	let isClean = isClean
	let clean = clean

	(* Acceptance *)
	let accept = GrammarAccept.accept
	let accept2 = GrammarAccept.accept2
	let acceptFull = GrammarAccept.acceptFull
	let find_applied_rules = GrammarAccept.find_applied_rules
	(* let get_tree = GrammarAccept.get_tree *)
	(* let build_tree = GrammarAccept.build_tree
	let print_tree = GrammarAccept.print_tree *)

	(* Generation *)

	(* Generate *)
	let generate = GrammarGenerate.generate

	(* Generation *)
	let generate_random_grammar = GrammarGeneration.generate_random_grammar



    (* Exercices support *)
    let checkProperty (gram: t) (prop: string) =
        match prop with
        | "grammar" -> true
        | _ -> Model.checkProperty prop
    let checkExercise ex gram = Model.checkExercise ex (accept gram) (checkProperty gram)	
    let checkExerciseFailures ex gram = Model.checkExerciseFailures ex (accept gram) (checkProperty gram)




    class model (arg: t Arg.alternatives) =
        object(self) inherit Model.model (make2 arg) as super
            val mutable simplified = false
        (* Representation *)
            method representation = representation
        (* Kind *)

        (* Show *)			
            method toJSon: JSon.t = toJSon representation
            method toJSon2: JSon.t = toJSon2 id representation
            method show: unit = show representation
            method show2: unit = show2 id representation

            method accept (testWord:word) : bool = false
            method generate (length:int) : words = Set.empty

        (* Exercices support *)
            method checkProperty (prop: string) = checkProperty representation prop

        (* Learn-OCaml support *)
            method moduleName = moduleName
            method xTypeName = xTypeName
            method xTypeDeclString : string = prelude
            method toDisplayString (name: string): string = solution name self#representation
            method example : JSon.t = example
        end

end


module GrammarTop =
struct
	open Grammar
	open GrammarBasicsX
	
	type configurationX = string * string
	type configurationsX = configurationX list

	let confX ((s,w): configuration): configurationX =
		(wordX s, wordX w)
	let confsX (c: configurations): configurationsX =
		List.map confX (Set.toList c)

	let pathX (p: path) = pathX confX p
	let trailX (t: trail) = trailX confX t

	let gI = internalize
	let gX = externalize

	let g_load file = gX (make (Arg.File file))
	let g_text text = gX (make (Arg.Text text))
	let g_json json = gX (make (Arg.JSon json))
	let g_predef name = g_text (Examples.example name)

	let g_init gx w =
		let is = GrammarAccept.initialConfig (gI gx) (wordI w) in
			confsX is

	let stats () = RuntimeControl.stats ()

	let g_accept gx w = accept (gI gx) (wordI w)

	let g_path gx w =
		let (r,p,t) = acceptFull (gI gx) (wordI w) in
			pathX p

	let g_trail gx w =
		let (r,p,t) = acceptFull (gI gx) (wordI w) in
			trailX t

	let g_generate gx len = wordsX (generate (gI gx) len)
end

open GrammarTop


(*

--------------------

#print_depth 10000;;
#print_length 10000;;

let ab = {| {
		kind : "grammar",
		description : "this is an example",
		name : "ab",
		alphabet : ["a", "b"],
		variables : ["S", "A", "B"],
		initial : "S",
		rules : [	"S -> AB",
					"A -> aA | ~",
					"B -> b" ]
		} |};;

let g = g_text ab;;
let w = "ab";;
g_init g w;;
g_accept g "ab";;
g_path g "ab";;
g_trail g "ab";;
g_generate g 4;;
--------------------

*)
# 1 "src/GrammarTests.ml"
(*
 * GrammarUnrestrictedTests.ml
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
 *  Written by Pedro Carlos (p.carlos)
 *)

(*
 * ChangeLog:
 *
 * jul/2024 (amd) - New file.
 *)

(*
 * Description: Unrestricted grammar testing.
 *)

open BasicTypes

module GrammarTests : sig end =
struct
	open Grammar
	
	let active = false

	let test0 () =
		let g = make (Arg.Predef "ug_simple") in
			show g

	let ab = {| {
			kind : "grammar",
			description : "this is an example",
			name : "ab",
			alphabet : ["a", "b"],
			variables : ["S", "A", "B"],
			initial : "S",
			rules : [	"S -> AB",
						"A -> aA | ~",
						"B -> b" ]
		} |}

	let test1 () =
		let g = make (Arg.Text ab) in
			show g

	let runAll =
		if Util.testing active "Grammar" then begin
			Util.sep (); test0 ();
			Util.sep (); test1 ();
		end
end

# 1 "src/ContextFreeGrammarSupport.ml"
(*
 * ContextFreeGrammarSupport.ml
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
 * sep/2022 (amd) - New submodules CFGConversions and CFGLearnOCaml
 * jul/2021 (amd) - Now this module is client of the Scanner module and
 *                  the erros are registered using the Error module.
 * jan/2021 (amd) - Module moved to an independent file.
 * dec/2019 (amd) - Initial version, inside the big file "OCamlFlatSupport.ml".
 *)

(*
 * Description: Support types and functions for CFGs including a parser for CFGs.
 *)
 
open BasicTypes

module ContextFreeGrammarBasics =
struct
	type rule = { head : symbol; body : word }
	type rules = rule set

	type t = {
		alphabet : symbols;
		variables : variables;
		initial : variable;
		rules : rules
	}
	
	type configuration =
		symbol list * word
	type configurations =
		configuration set

	type path =
		configuration Path.path
	type trail =
		configuration Trail.trail

	type cfgTree =
		  Leaf of symbol
		| Root of symbol * cfgTree list

	let kind = "context free grammar"

	let cfg_zero: t = {
		alphabet = Set.empty;
		variables = Set.make [draftVar];
		initial = draftVar;
		rules = Set.empty;
	}
end

module type ContextFreeGrammarSyntaxSig =
sig
	open ContextFreeGrammarBasics

	val parse : string set -> rules
	val parseLine : string -> rules
	val toStringList : rules -> string list
	val (-->) : symbol -> string -> rule
	val rule2str : rule -> string
	val showRules : rules -> unit
end

module ContextFreeGrammarSyntax: ContextFreeGrammarSyntaxSig =
struct
	open Scanner
	open ContextFreeGrammarBasics

	let isWhite c =
		List.mem c [' '; '\t']

	let parseString delim =
		skip();	(* skip quotation mark *)
		let tk = getUntil delim in
			match peek () with
				| x when x = delim -> skip(); ("<" ^ tk ^ ">")
				| err -> expecting ("closing '" ^ (Char.escaped delim) ^ "'") err
	
	let parseHead () : symbol =
		match peek() with
			| ' ' -> invalid "Premature end of expression\n"
			| '<' -> str2symb (parseString '>')
			| c -> skip() ; char2symb c
			
	let parseNeck (): unit =
		match peek() with
			| ' ' -> invalid "Premature end of expression\n"
			| '-' -> skip();
					if peek() = '>' then skip()
					else invalid "Bad neck\n"
			| _ -> invalid "Bad neck\n"

	let rec parseBody (): word list =
		match peek() with
			| ' ' -> [[]]
			| '|' -> skip(); []::parseBody ()
			| '~' -> skip(); parseBody ()
			| '<' ->
				(let symb = str2symb (parseString '>') in
					match parseBody () with
						| [] -> invalid "never happens"
						| x::xs -> (symb::x)::xs)		
			| c -> skip();
					match parseBody () with
						| [] -> invalid "never happens"
						| x::xs -> ((char2symb c)::x)::xs

	let parseLine line: rules =
		if String.trim line = "" then
			Set.empty
		else (
			Scanner.start "ContextFreeGrammarSyntax" line;
			try
				let finish l = if l = [] then [epsilon] else l in
				let h = parseHead () in
				let _ = parseNeck () in
				let bs = Set.make (parseBody ()) in
					Set.map (fun b -> {head=h; body=finish b}) bs
			with Not_found ->
				Set.empty
		)

	let parse rs: rules =
		Set.flatMap parseLine rs
	
	let rule2str {head=h; body=b} =
		let b = if b = [] then [epsilon] else b in
			(symb2str h) ^ " -> " ^ (word2str b)

	let toString rs: string =
		let rl = Set.toList rs in
		String.concat "\n" (List.map rule2str rl)

	let toStringList rs: string list =
		let rl = Set.toList rs in
			List.map rule2str rl
	
	let (-->) h b : rule =
		{ head = h; body = str2word b } ;;

	let showRules rs =
		Util.println [toString rs]
end

module ContextFreeGrammarConversions =
struct
	open ContextFreeGrammarBasics
	open ContextFreeGrammarSyntax

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			cfg_zero
		else {
			alphabet = JSon.fieldSymbolSet j "alphabet";
			variables = JSon.fieldSymbolSet j "variables";
			initial = JSon.fieldSymbol j "initial";
			rules = ContextFreeGrammarSyntax.parse (JSon.fieldStringSet j "rules");
		}

	let toJSon0 (rep: t): JSon.t =
		JSon.makeAssoc [
			("alphabet", JSon.makeSymbolSet rep.alphabet);
			("variables", JSon.makeSymbolSet rep.variables);
			("initial", JSon.makeSymbol rep.initial);
			("rules", JSon.makeStringSet (Set.map rule2str rep.rules))
		]
	
	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 rep)

	let toJSon (rep: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) rep
end

module ContextFreeGrammarBasicFunctions =
struct
	open ContextFreeGrammarBasics
	open ContextFreeGrammarConversions

	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (rep: t): unit =
		let j = toJSon rep in
			JSon.show j

	let show2 (id: Entity.t) (rep: t): unit =
		let j = toJSon2 id rep in
			JSon.show j
end

module ContextFreeGrammarBasicsX =
struct
	open ContextFreeGrammarBasics

	type tx = {
		alphabet : symbolX list;
		variables : variableX list;
		initial : variableX;
		rules : string list
	}

	let internalize (cfg: tx): t = {
		alphabet = symbolsI cfg.alphabet;
		variables = symbolsI cfg.variables;
		initial = symbI cfg.initial;
		rules = ContextFreeGrammarSyntax.parse (Set.make cfg.rules)
	}

	let externalize (cfg: t): tx = {
		alphabet = symbolsX cfg.alphabet;
		variables = symbolsX cfg.variables;
		initial = symbX cfg.initial;
		rules = ContextFreeGrammarSyntax.toStringList cfg.rules
	}
end

module ContextFreeGrammarLearnOCaml =
struct
	open ContextFreeGrammarBasics
	open ContextFreeGrammarBasicsX

	let moduleName =
		"ContextFreeGrammar"

	let xTypeName =
		"contextFreeGrammar"

	let solution (name: string) (rep: t): string =
		let repx = externalize rep in
		Printf.sprintf {zzz|
		%s{
			alphabet = %s;
			variables = %s;
			initial = %s;
			rules = %s
		}
		|zzz}	(* please, do not change this line *)
			(FiniteEnumerationLearnOCaml.displayHeader name xTypeName)
			(symbolsXD repx.alphabet)
			(symbolsXD repx.variables)
			(symbXD repx.initial)
			(stringsD repx.rules)

	let prelude : string =
		Printf.sprintf {zzz|
			type symbol = %s
			type variable = %s
			type rule = string
			type contextFreeGrammar = {
				alphabet : symbol list;
				variables : variable list;
				initial : variable;
				rules : rule list
			}
		|zzz}	(* please, do not change this line *)
				symbolTypeName symbolTypeName

		let example : JSon.t =
			JSon.parse {| {
				kind : "context free grammar",
				description : "this is an example",
				name : "cfg_simple",
				alphabet : ["0", "1"],
				variables : ["S", "X"],
				initial : "S",
				rules : [ "S -> 1S0 | X", "X -> 0X1 | ~" ]
			}
			|}	(* please, do not change this line *)
end

module ContextFreeGrammarSupport =
struct
	include ContextFreeGrammarBasics
	include ContextFreeGrammarSyntax
	include ContextFreeGrammarConversions
	include ContextFreeGrammarBasicFunctions
	include ContextFreeGrammarLearnOCaml
end

module ContextFreeGrammarSyntaxTests : sig end =
struct
	let active = false

	let test0 () =
		let cfg = Set.make [ "S -> aTb | ~"; "T -> aSb" ] in
		let rules = ContextFreeGrammarSyntax.parse cfg in
			ContextFreeGrammarSyntax.showRules rules

	let test1 () =
		let cfg = Set.make ["S -> aSb | ~"] in
		let rules = ContextFreeGrammarSyntax.parse cfg in
			ContextFreeGrammarSyntax.showRules rules

	let runAll =
		if Util.testing active "ContextFreeGrammarSyntax" then begin
			Util.header "test0";
			test0 ();
			Util.header "test1";
			test1 ();
			Util.header ""
		end
end
# 1 "src/ContextFreeGrammarChomsky.ml"
(*
 * ChomskyNormalForm.ml
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
 *  Written by Guilherme Fernandes (gf)
 *)

(*
 * ChangeLog:
 *
 * sep/2022 (amd) - Adapted the Guilherme code to the context of OCamlFLAT
 * jul/2022 (gf) - New module (original code inside the "contributions" dir)
 *)

(*
 * Description: Conversion of CFG to Chomsky Normal Form
 *)
 
open BasicTypes

module type ChomskyNormalFormSig =
sig
	open ContextFreeGrammarBasics

	val chomsky : t -> t	
	val cykAccept : t -> word -> bool	
	val accept : t -> word -> bool	
end

module ChomskyNormalForm : ChomskyNormalFormSig =
struct
	open ContextFreeGrammarBasics
	
	(*Remove rule rule from grammar cfg
	  and return a new grammar*)
	let removeRule (rule : rule) (cfg : t) : t = 
	  let newRules = Set.filter (fun x -> x <> rule) cfg.rules in 
	  {alphabet = cfg.alphabet;
	  variables = cfg.variables;
	  initial = cfg.initial;
	  rules = newRules
	  }
	;;

	(*Generate a random char*)
	let randVar (forbiddenSymbols : symbols) : symbol =
		let var = ref (Char.uppercase_ascii (Char.chr (97 + (Random.int 26)))) in
		while Set.belongs (char2symb !var) forbiddenSymbols do 
			var := Char.uppercase_ascii (Char.chr (97 + (Random.int 26))) 
		done;
		char2symb !var
	;;

	(* return the symbols used in grammar cfg *)
	let usedSymbols (cfg : t) : symbols = 
		Set.union cfg.variables cfg.alphabet
	;;

	(* return the direct derivations of the 
	   variable var in grammar cfg*)
	let directDeriv (var : symbol) (cfg : t) : rules =
		Set.filter ( fun x -> x.head = var) cfg.rules
	;;

	(* return the number of direct derivations
	 of the variable var in grammar cfg*)
	let numberOfProdVar (var : symbol) (cfg : t) : int = 
		Set.size (directDeriv var cfg)
	;;


	(*returns the rule with a body equal to bdy and,
	  if it does not exist, generates a new one with the body bdy*)
	  (* in rulesWithSameBdy it is necessary to check
		if numberOfProdVar x.head is equal to 1
		because if not, we may be changing
		the grammar ex: S -> a
		S -> b
		if we look for bdy 'a' we will find the S
		but we will also add production b
		the grammar
		 *)   
	let getRule (bdy : word) (cfg : t) : rule = 
		let rulesWithSameBdy =
				Set.filter ( fun x -> x.body = bdy && numberOfProdVar x.head cfg = 1) cfg.rules in
			if Set.size rulesWithSameBdy > 0 then 
				Set.hd rulesWithSameBdy
			else
				{head = randVar (usedSymbols cfg); body = bdy}
	;;


	(*checks if there is a rule in grammar cfg that 
	  contains the initial variable on the right-hand side*)
	let containsSInRHS (cfg : t) : bool = 
		Set.exists (fun x -> List.mem cfg.initial x.body) cfg.rules
	;;

	(* adds a new rule to grammar cfg and sSymb indicates if 
	  variable in the left-hand side is the initial variable*)
	let addRule (rule : rule) (cfg : t) (sSymb : bool): t = 
	  {alphabet = cfg.alphabet;
	  variables = Set.union (Set.make [rule.head]) cfg.variables;
	  initial = if sSymb then rule.head else cfg.initial;
	  rules = Set.cons rule cfg.rules
	  }
	;;

	(*START*)
	(*Eliminate the start symbol from right-hand side *)
	let delSFromRHS (cfg : t) : t = 
	  if containsSInRHS cfg then 
		let newS = randVar (usedSymbols cfg) in
		addRule {head = newS; body = [cfg.initial]} cfg true
	  else cfg
	;;

	(*------------------------------------------------------------------------------------------------*)

	(*checks if symbol var is a cfg grammar variable*)
	let isVariable (var : symbol) (cfg : t) : bool = 
	  Set.belongs var cfg.variables
	;;

	(*checks if symbol symbol is a terminal symbol*)
	let isTerminalSymbol (symbol : symbol) (cfg : t) : bool = 
	  Set.belongs symbol cfg.alphabet
	;;
	(*checks if var produces the word in grammar cfg
	  and seen are the rules already parsed*)
	let rec prodWord (var : symbol) (word : word) (cfg : t) (seen : rules): bool = 
	  let direct = directDeriv var cfg in 
	  let words = Set.map (fun x -> x.body) direct in 
			Set.belongs word words 
		|| Set.exists (fun x -> not (Set.belongs x seen) 
			&& List.for_all (fun y -> prodWord y word cfg (Set.cons x seen)) x.body) direct
	;; 

	(*checks if var produces the word in grammar cfg*)
	let varProdWord (var : symbol) (word : word) (cfg : t) : bool = 
	  prodWord var word cfg Set.empty
	;;

	(*checks if var produces the empty word in grammar cfg*)
	let prodEpsilon (var : symbol) (cfg : t) : bool =
	  varProdWord var [] cfg 
	;;

	(*generates all possible words by applying the epsilon
	  transformation, if the variable we are analyzing derives epsilon*)
	let rec epsilonProdsCombs (word : word) (cfg : t) : words = 
	  match word with
	  | [] -> Set.make [[]]
	  | hd::tl -> let a = epsilonProdsCombs tl cfg in
				  if prodEpsilon hd cfg then 
					let b = Set.map ( fun x -> hd::x) a in
					if numberOfProdVar hd cfg > 1 then
					  Set.union a b
					else a
				  else
					Set.map (fun x -> hd::x) a
	;;


	(*test*)
	let rec print rules =
	  match rules with
	  | [] -> Format.printf "\n"
	  | hd::tl ->
			Format.printf "{head = %s; body = " (symb2str hd.head); 
			List.iter (fun x -> Format.printf "%s" (symb2str x)) hd.body;
			Format.printf "}\n";
			Format.print_flush ();
			print tl
	;;

	(*for each element x in bodies 
	  add a rule with head leftSide and body x*)
	let rec addNewRules (leftSide : symbol) (bodies : words) (cfg : t) : t =
		Set.match_ bodies
			(fun () -> cfg)
			(fun hd tl ->
				let nCfg = addNewRules leftSide tl cfg in
				  if hd <> [leftSide] then
					addRule {head = leftSide; body = hd} nCfg false
				  else nCfg)
	  ;;

	(*verifies if symb is the cfg grammar start symbol *)
	let isStartSymbol (symb : symbol) (cfg : t) : bool = 
	  symb = cfg.initial
	;;

	(*Eliminate ε-rules of cfgRules
	  and returns a new grammar without ε-rules *)
	  let rec delEpsilonRules (cfgRules: rules) (cfg : t) : t =
		Set.match_ cfgRules
			(fun () -> cfg)
			(fun hd tl ->
				let nCfg = delEpsilonRules tl cfg in
				  let epsilonProd = epsilonProdsCombs hd.body cfg in 
				  let cfgWithRules = addNewRules hd.head epsilonProd nCfg in
				  if isStartSymbol hd.head cfgWithRules then 
					cfgWithRules 
				  else 
					removeRule {head = hd.head; body = []} cfgWithRules)
	;;




	(*DEL*)
	(*Eliminate ε-rules of cfg grammar*)
	let cleanEpsilonRules (cfg : t) : t = 
	  delEpsilonRules cfg.rules cfg 
	;;





	(*------------------------------------------------------------------------------------------------*)

	(*checks if rule derivates only one variable*)
	let isAnUnitProduction (rule : rule) (cfg : t) : bool = 
	  List.length rule.body = 1 && isVariable (List.hd rule.body) cfg
	;;

	let rec addRules (rules : rules ) (cfg : t) : t =
		Set.match_ rules
			(fun () -> cfg)
			(fun hd tl -> addRules tl (addRule hd cfg false))

	(*UNIT*)
	(*let unitFor1 (seen : rules) (rule : rule) (cfg : t) : rules * cfg = 
	  let nCfg = removeRule rule cfg in
	  let direct = directDeriv (List.hd rule.body) nCfg in 
	  let words = List.map (fun x -> x.body) direct in
	  let nW = List.filter( fun x -> not(List.mem {head = rule.head; body = x} seen)) words in
	  let analyzed = List.map( fun x-> {head = rule.head; body = x})nW in
	  (analyzed, addNewRules rule.head nW nCfg)
	;;

	(* Eliminate unit rules and seen
	  are the rules already parsed*)
	let rec processUnitProduction (seen : rules) (cfgRules: rules) (cfg : t) : t = 
	  match cfgRules with
	  | [] -> cfg
	  | hd::tl -> if isAnUnitProduction hd cfg then
					let (a, b) = unitFor1 seen hd cfg in
					processUnitProduction (seen@a) b.rules b
				  else 
					processUnitProduction seen tl cfg
	;;*)
	let unitFor1 (seen : rules) (rule : rule) (cfg : t) : rules  = 
	  let direct = directDeriv (List.hd rule.body) cfg in 
	  let words = Set.map (fun x -> x.body) direct in
	  let nW = Set.filter ( fun x -> not (Set.belongs {head = rule.head; body = x} seen)) words in
	  Set.map ( fun x-> {head = rule.head; body = x}) nW 
	;;

	(* Eliminate unit rules and seen
	  are the rules already parsed*)
	let rec processUnitProduction (seen : rules) (cfgRules: rules) (cfg : t) : t = 
		Set.match_ cfgRules
			(fun () -> cfg)
			(fun hd tl ->
				let nCfg = processUnitProduction seen tl cfg in
				  if isAnUnitProduction hd nCfg then
					let sdnCfg = removeRule hd nCfg in
					let rules = unitFor1 seen hd sdnCfg in
					processUnitProduction (Set.union rules seen) rules (addRules rules sdnCfg)
				  else 
					nCfg)
	;;

	(*UNIT*)  
	(*Eliminate unit rules from cfg grammar*)
	let delUnitProductions (cfgRules: rules) (cfg : t) : t = 
	  processUnitProduction Set.empty cfgRules cfg;;

	(*------------------------------------------------------------------------------------------------*)

	(*checks if the right-hand side of the 
	  rule has one isolated terminal symbol*)
	let isNonSolitaryTerminalsRule (rule : rule) (cfg : t) : bool = 
	  let terminals = List.filter ( fun x -> isTerminalSymbol x cfg) rule.body in
			List.length terminals > 1 
		||  (List.length terminals > 0 && List.length rule.body > 1)
	;;

	(*removes the non solitary terminal symbols from word and
	  add a new rule to cfg grammar for each one
	  and returns a ( new word * new grammar)*)
	let rec addRulesFromNonSolitary (bdy : word) (cfg : t) : word * t = 
	  match bdy with
	  | [] -> (bdy, cfg)
	  | hd::tl -> let (a, b) = addRulesFromNonSolitary tl cfg in
				  if isTerminalSymbol hd b then
					let rule = getRule [hd] b in
					let nCfg = addRule rule b false in
					(rule.head::a, nCfg)
				  else
					(hd::a, b)
	;;

	(*TERM*)
	(*Eliminate rules with nonsolitary terminals*)
	(*let rec delRulesNonSolitaryTerminals (cfgRules: rules) (cfg : t) : t = (*trocar nome*)
	  match cfgRules with
	  | [] -> cfg
	  | hd::tl -> if isNonSolitaryTerminalsRule hd cfg then 
					let (a, b) = cleanNonSolitary hd.body cfg in
					let nCfg = addRule {head = hd.head; body = a} b false in
					delRulesNonSolitaryTerminals tl (removeRule hd nCfg)
				  else
					delRulesNonSolitaryTerminals tl cfg

	;;*)


	let rec processRulesWithNonSolitaryTerminals (cfgRules: rules) (cfg : t) : t = 
		Set.match_ cfgRules
			(fun () -> cfg)
			(fun hd tl ->
				let nCfg = processRulesWithNonSolitaryTerminals tl cfg in
				  if isNonSolitaryTerminalsRule hd nCfg then 
					let (a, b) = addRulesFromNonSolitary hd.body nCfg in
					addRule {head = hd.head; body = a} (removeRule hd b) false 
				  else
					nCfg)
	;;


	(*------------------------------------------------------------------------------------------------*)
	(* checks if the rule has more than 2 
	  non terminal symbols in right-hand side*)
	let hasMoreThan2NonTerminalsInRHS (rule : rule) (cfg : t) : bool = 
		let nonTerminalsInRHS = List.filter ( fun x -> isVariable x cfg) rule.body in
		List.length nonTerminalsInRHS > 2
	;;

	(* split the word when it finds the first variable*)
	let rec splitBodyByVariables (body:word) (cfg : t) : word * word = 
		match body with
		| [] -> ([], [])
		| hd::tl -> let (a, b) = splitBodyByVariables tl cfg in
								if isVariable hd cfg then 
									([hd], tl)
								else
									(hd::a, b)
	;;

	(*let binFor1 (rule : rule) (cfg : t) : t = 
	  let cfgWithoutHd = removeRule rule cfg in 
	  let (a, b) = splitBodyByVariables rule.body cfgWithoutHd in
	  let var = randVar (usedSymbols cfgWithoutHd) in 
	  let nCfg = addRule {head = rule.head; body = a@[var]} cfgWithoutHd false in
	  addRule {head = var; body = b} nCfg false
	;;*)


	let binFor1 (rule : rule) (cfg : t) : rules = 
	  let (a, b) = splitBodyByVariables rule.body cfg in
	  let var = randVar (usedSymbols cfg) in 
		Set.make [{head = rule.head; body = a@[var]}; {head = var; body = b}]
	;;

	let rec processRHSwithMoreThan2NonTerminals (cfgRules: rules) (cfg : t) : t = 
		Set.match_ cfgRules
			(fun () -> cfg)
			(fun hd tl ->
				let nCfg = processRHSwithMoreThan2NonTerminals tl cfg in
				  if hasMoreThan2NonTerminalsInRHS hd nCfg then 
					let cfgWithoutHd = removeRule hd nCfg in 
					let rules = binFor1 hd cfgWithoutHd in
					let sdCfg = addRules rules cfgWithoutHd in
					processRHSwithMoreThan2NonTerminals rules sdCfg
				  else
					nCfg)
	;;

	(*BIN*)
	(*Eliminate right-hand sides with more than 2 nonterminals*)
	(*let rec processRHSwithMoreThan2NonTerminals (cfgRules: rules) (cfg : t) : t = 
	  match cfgRules with
	  | [] -> cfg
	  | hd::tl -> if hasMoreThan2NonTerminalsInRHS hd cfg then 
					let sdCfg = binFor1 hd cfg in
					processRHSwithMoreThan2NonTerminals sdCfg.rules sdCfg
				  else
					processRHSwithMoreThan2NonTerminals tl cfg
	;;*)

	(*let rec delRHSwithMoreThan2NonTerminals (cfgRules: rules) (cfg : t) : t = 
	  match cfgRules with
	  | [] -> cfg
	  | hd::tl -> let nCfg = delRHSwithMoreThan2NonTerminals tl cfg in 
				  if hasMoreThan2NonTerminalsInRHS hd nCfg then 
					binFor1 hd nCfg   // It doesn't work because we need to
									  // analyze the new rules added in binFor1
				  else
					nCfg

				
	;;*)



	(*------------------------------------------------------------------------------------------------*)
	(*Convert cfg grammar to Chomsky normal form*)
	let chomsky (cfg: t) : t =
	  let start = delSFromRHS cfg in
	  let term = processRulesWithNonSolitaryTerminals start.rules start in
	  let bin = processRHSwithMoreThan2NonTerminals term.rules term in 
	  let del = cleanEpsilonRules bin in
	  let unit = delUnitProductions del.rules del in
	  unit 
	;;

	(* IMPERATIVE code - https://www.geeksforgeeks.org/cocke-younger-kasami-cyk-algorithm/ *)
	(* pre: rule is in chomsky form *)
	let prodVars (rule : rule) : bool =
		List.length rule.body = 2

	let cykAccept (cfg: t) (w: word) =
	  if w = [] then
		prodEpsilon cfg.initial cfg
	  else
		let n = List.length w in
		let matrix = Array.make_matrix n n (Set.empty) in
		for j = 0 to (n-1) do
		  let vars = Set.filter(fun x -> List.length x.body = 1 && List.nth x.body 0 = List.nth w j) cfg.rules in
		  let lhs = Set.map ( fun x -> x.head) vars in
		  matrix.(j).(j) <- Set.union matrix.(j).(j) lhs;
		  for i = j downto 0 do 
			for k = i to (j-1) do
			  let vars = Set.filter(fun x -> prodVars x && Set.belongs (List.nth x.body 0) matrix.(i).(k)
											  && Set.belongs (List.nth x.body 1) matrix.(k+1).(j)) cfg.rules in
			  let lhs = Set.map ( fun x -> x.head) vars in
			  matrix.(i).(j) <- Set.union matrix.(i).(j) lhs
			done
		  done
		done; 
		Set.belongs cfg.initial matrix.(0).(n-1)

	let accept (cfg: t) (w: word) =
		cykAccept (chomsky cfg) w

end
# 1 "src/ContextFreeGrammarBasic.ml"
(*
 * ContextFreeGrammarBasic.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
 * jul/2021 (amd) - Improved Learn-OCaml support and error handling.
 * jun/2021 (amd) - Added checks for '~' in the #validate method.
 * may/2021 (amd) - Added support for an extern representation.
 * jan/2021 (amd) - Module in an independent file and some cleanup.
 * feb/2020 (jg) - Main functionalities.
 * dec/2019 (amd) - Initial skeleton, inside the big file "OCamlFlat.ml".
 *)

(*
 * Description: Context-free grammar functionality.
 *
 * TODO: More cleanup.
 *)

open BasicTypes

module ContextFreeGrammarPrivate =
struct
	open ContextFreeGrammarSupport

	(*------Auxiliary functions---------*)

	(* given a head, returns the set of all its bodies according to the cfg's rules *)
	let bodiesOfHead h rl =
		let rls = Set.filter (fun r -> r.head = h) rl in
			Set.map (fun r -> r.body) rls


	(* given 2 sets of words, to each word of the left set, appends each word of the right set *)
	let concatWords lws rws =
		if lws = Set.empty then rws
		else if rws = Set.empty then lws
		else
			let pairs = Set.product lws rws in
				Set.map (fun (x,y) -> x@y) pairs

	(* tests if the number of symbols in the given word exceeds the given lenght *)
	let exceedsMaxLen w l alph =
		let cleanWord = List.filter (fun c -> Set.belongs c alph) w in
			(List.length cleanWord) > l



	let subX h rws rl =
		let bs = bodiesOfHead h rl in
			concatWords bs rws


	(* applies the cfg's rules to the given word *)
	let rec subVar w vs rs =
		match w with
			| [] -> Set.make [[]]
			| x::xs -> if (Set.belongs x vs) then subX x (subVar xs vs rs) rs
				else concatWords (Set.make [[x]]) (subVar xs vs rs)


	(* removes the empty symbol from all non-empty words *)
	let removeEpsi w = List.filter (fun c -> c <> epsilon) w


	(* filters out all words that have variables and cleans any unnecessary epsilon *)
	let cleanNonWords ws vs =
		let hasVar w = List.exists (fun c -> Set.belongs c vs) w in
		let ws = Set.filter (fun w -> not (hasVar w)) ws in
			Set.map (fun w -> removeEpsi w) ws

  let removeEpsilonFromWord w =
    List.filter (fun c -> c <> epsilon) w

  let removeDollarFromWord w =
    List.filter (fun c -> c <> dollar) w

  let rec doWordGenerateEmptyX w seen (rep:t) =
    let doGenerateEmpty x =
      if List.mem x seen
      then false
      else(
		    let bodies = bodiesOfHead x rep.rules in
		    Set.exists (fun b -> doWordGenerateEmptyX b (x::seen) rep) bodies 
		  )
		in      
      List.for_all doGenerateEmpty w

  let doWordGenerateEmpty w (rep:t) =
    doWordGenerateEmptyX (removeDollarFromWord w) [] rep

  let rec firstX testWord seen simple (rep:t) =
    match testWord with
		  | [] -> Set.empty
			| [x] when Set.belongs x rep.variables -> 
					let bodies = bodiesOfHead x rep.rules in
					if Set.belongs x seen 
					  then Set.empty
					  else let result = Set.flatMap ( fun b ->
					          let result = firstX b (Set.add x seen) simple rep in
                    let empty = if b = []
                                then Set.make [epsilon]
                                else Set.empty in
					          Set.union empty result
					        ) bodies
					        in
                  if Set.exists (fun b -> doWordGenerateEmpty b rep) bodies 
                    then Set.union result (Set.make [epsilon])
                    else Set.make (removeEpsilonFromWord (Set.toList result))
			| x::xs when Set.belongs x rep.alphabet -> 
					Set.make [x]
			| x::xs -> Set.union 
		  						(firstX [x] seen simple rep) 
									(if doWordGenerateEmpty [x] rep then firstX xs seen simple rep else Set.empty)  

  let first2 (testWord:word) simple (rep:t) =
    firstX testWord Set.empty simple rep

  let first (testWord:word) simple (rep:t) =
    let first = first2 testWord simple rep in
    if simple then Set.filter (fun c -> c <> epsilon) first else first

	let getFollowRules (testSymbol:symbol) (rep:t) =
	  Set.filter (fun r -> Set.belongs testSymbol (Set.make r.body) ) rep.rules

  let rec getFollowInfo2 testSymbol h b =
    match b with
      | [] -> []
      | x::xs when x = testSymbol -> (h, xs) :: getFollowInfo2 testSymbol h xs
      | x::xs -> getFollowInfo2 testSymbol h xs

  (* given a variable X, returns the pairs (Y,w2) *)
  let getFollowInfo testSymbol rep =
    let rules = Set.toList (getFollowRules testSymbol rep) in
    List.flatten (List.map (fun r -> getFollowInfo2 testSymbol r.head r.body) rules )

    
  let rec followX (testSymbol:symbol) seen simple (rep:t) =
    let pairs = Set.make (getFollowInfo testSymbol rep) in
    let dollar = if testSymbol = rep.initial
                  then Set.make [dollar]
                  else Set.empty
    in
    let set = Set.flatMap (fun (y,w) -> 
          Set.union 
            (Set.filter (fun s -> s <> epsilon) (first w simple rep))
            (if (not (Set.belongs y seen) && doWordGenerateEmpty w rep) 
              then followX y (Set.add testSymbol seen) simple rep
              else Set.empty
            )
    ) pairs 
    in
    Set.union set dollar
    
  let follow2 testSymbol simple rep =
    followX testSymbol (Set.make []) simple rep
  
  let follow testSymbol simple rep =
    let follow = follow2 testSymbol simple rep in
    if simple then Set.filter (fun c -> c <> dollar) follow else follow


  let lookahead rule simple (rep:t) =
    let x = rule.head in
    let w = rule.body in
      Set.filter (
        fun c -> c <> epsilon 
      ) (Set.union (first2 w simple rep) (if doWordGenerateEmpty w rep then follow2 x simple rep else Set.empty))

	(* Make *)
	let validate (name: string) (rep: t): unit =
		(* the alphabet must not contain epsilon ('~') *)
		let isValidAlphabet = not (Set.belongs epsilon rep.alphabet) in
		(* the variables must not contain epsilon ('~') *)
		let isValidVariables = not (Set.belongs epsilon rep.variables) in
		let isIntersectionValid = (Set.inter rep.variables rep.alphabet) = Set.empty in
		let isInitialValid = Set.belongs rep.initial rep.variables in
		let areRuleHeadsValid =
			let hs = Set.map (fun r -> r.head) rep.rules in
				Set.subset hs rep.variables
		in
		let areRuleBodiesValid =
			let allBodySymbols = Set.flatMap (fun r -> Set.make r.body) rep.rules in
			let allValidSymbs = Set.add epsilon (Set.union rep.alphabet rep.variables) in
				Set.subset allBodySymbols allValidSymbs
		in
		if not isValidAlphabet then
			Error.error name
				"The alphabet contains epsilon '~', and it should not" ();
		if not isValidVariables then
			Error.error name
				"The variables contain epsilon '~', and it should not" ();
		if not isIntersectionValid then
			Error.error name
				"The intersection between the alphabet and the variables is not empty" ();
		if not isInitialValid then
			Error.error (symb2str rep.initial)
				"The initial symbol is not a declared variable" ();
		if not areRuleHeadsValid then
			Error.error name
				"Some rule heads are not declared variables" ();
		if not areRuleBodiesValid then
			Error.error name
				"Some rule bodies are not declared symbols" ()
				
	let accept (fe: t) (w: word): bool =
		false (* TODO *)

	let generate (fe: t) (length: int): words =
		Set.empty (* TODO *)

(* ----------------------------------------------------------------------------*)

	(*CODIGO JP*)

	(*checks if symbol var is a cfg grammar variable*)
	let isVariable (var : symbol) (cfg : t) : bool = 
		Set.belongs var cfg.variables
	;;
	
		(*checks if symbol symbol is a terminal symbol*)		
	let isTerminalSymbol (symbol : symbol) (cfg : t) : bool = 
		Set.belongs symbol cfg.alphabet
	;;

	let isTerminalSymbol2 (symbol: symbol) : bool =
		not ("A" <= (symb2str symbol) && (symb2str symbol) <= "Z" )

	let hasEmpty body =
		body = [epsilon]

	let rec expandsEmpty sym cfg =
		let xRules = Set.filter(fun r -> r.head = sym) cfg.rules in
		let xBodies = Set.map (fun r -> r.body) (Set.filter (fun r -> List.length r.body == 1) xRules) in
		Set.for_all(fun b -> hasEmpty b || List.for_all (fun sy -> expandsEmpty sy cfg && isVariable sy cfg) b) xBodies
				
	let rec calcSymExpansions cfg sym seen =
		let xRules = Set.filter(fun r -> r.head == sym) cfg.rules in
		let xBodies = Set.toList (Set.map (fun r -> r.body) xRules) in
		let rec minBody bodies min seen =
			match bodies with
			| [] -> (min, seen)
			| ba :: bb -> 
				let terminalLength = List.length (List.filter (fun sy -> isTerminalSymbol sy cfg) ba) in
				let nonTerms = List.filter (fun sy -> isVariable sy cfg && sy != sym) ba in
				let sameSymLength = List.length (List.filter (fun sy -> sy == sym) ba) in
				let rec expandNonTerms terms seen =
					match terms with
					| [] -> (0, seen)
					| sa :: sb ->
						if (Set.exists(fun (sy, value) -> sy == sa) seen)
							then
						let (_, kValue) = Set.find(fun (sy, value) -> sy == sa) seen in
							let (value, newSeen) = expandNonTerms sb seen in
							(kValue + value, newSeen)
						else (
							let (_, saValue, newSymSeen) = calcSymExpansions cfg sa seen in
							let newSymSeen2 = Set.add (sa, saValue) newSymSeen in
							let (ntValue, newNonTermSeen) = expandNonTerms sb newSymSeen2 in
							let unionSeen = Set.unionUnsafe newSymSeen2 newNonTermSeen in
							(saValue + ntValue, unionSeen)
						)					
				in
				let (value, newSeen) = expandNonTerms nonTerms seen in
				if (sameSymLength != 0) then
					let (minVal, newSeen) = minBody bb min seen in
					if (minVal < min) then
						let bodyLength = terminalLength + value + (sameSymLength * minVal) in
						if (bodyLength < min) then
							let (minVal2, newSeen) = minBody bb bodyLength seen in
								(minVal2, newSeen)
						else (
							let (minVal, newSeen) = minBody bb min seen in
								(minVal, newSeen)
						)
					else (
						let (minVal2, newSeen) = minBody bb min seen in
						(minVal2, newSeen)
					)
				else(
					let bodyLength = terminalLength + value in
					if (bodyLength < min) then
						let (minVal, newSeen) = minBody bb bodyLength seen in
							(minVal, newSeen)
					else (
						let (minVal, newSeen) = minBody bb min seen in
							(minVal, newSeen)
					)
				)
				
			in
			let (minValue, newSeen) = minBody xBodies (Int.max_int) seen in
			(sym, minValue, newSeen)


	let calcExpans cfg =
		let vars = Set.toList (cfg.variables) in
		let seen = Set.make ([]) in
		let rec buildPairs vars seen =
			match vars with
			| [] -> []
			| va :: vb -> 
				if not (Set.exists(fun (sy, value) -> sy == va) seen)
					then
						let (_, minValue, newSeen) = calcSymExpansions cfg va seen in
						let newSeen2 = Set.add (va, minValue) newSeen in 
						(va, minValue) :: buildPairs vb newSeen2
				else (
					let pair = Set.find(fun (sy, value) -> sy == va) seen in
					pair :: buildPairs vb seen
					)
		in
		buildPairs vars seen
	
	let verifyLength2 cfg sf body len pairs =
		let terminalLengthSf = List.length (List.filter(fun sy -> isTerminalSymbol sy cfg) sf) in
		let terminalLengthBody = List.length (List.filter(fun sy -> isTerminalSymbol sy cfg) body) in
		let rec sumMinExpansions syms =
			match syms with
			| [] -> 0
			| sa :: sb ->
				let (_, value) = List.find(fun (sy, value) -> sy == sa) pairs in
				value + sumMinExpansions sb
		in
		let sfVars = List.filter(fun sy -> isVariable sy cfg) sf in 
		let bodyVars = List.filter(fun sy -> isVariable sy cfg) body in
		terminalLengthSf + terminalLengthBody + (sumMinExpansions sfVars) + (sumMinExpansions bodyVars) - 1 <= len
	

	let verifyLength cfg sf body len =
		let lengthSf = List.length (sf) in
		let lengthBody = List.length (body) in
		let sfVars = List.length (List.filter(fun sy -> isVariable sy cfg && expandsEmpty sy cfg) sf) in 
		let bodyVars = List.length (List.filter(fun sy -> isVariable sy cfg && expandsEmpty sy cfg) body) in
		lengthSf + lengthBody - sfVars - bodyVars - 1 <= len


		(*
			4
			2 -> 5
			2 -> 4	 
		*)

	let initialConfig (cfg: t) (w: word) : configurations =
		Set.make [([cfg.initial], w)]


	let rec expand (cfg: t) (sf,w) : configurations =
		match sf with
			| [] -> Set.make [([],w)]
			| x::xs ->
				let ySet = expand cfg (xs, w) in
					if isTerminalSymbol x cfg then
						Set.map (fun (fs, w) -> (x::fs, w)) ySet
					else
						let xRules = Set.filter(fun r -> r.head = x) cfg.rules in
						let xBodies = Set.map (fun r -> r.body) xRules in
						let res = Set.flatMap (fun (fs1, w) -> Set.map (fun fs2 -> (fs2@fs1, w)) xBodies) ySet in
						res

	let rec expandGenerate (cfg: t) (len: int) (sf,w) : configurations =
		match sf with
			| [] -> Set.make [([],[])]
			| x::xs ->
				let ySet = expandGenerate cfg len (xs, w) in
					if isTerminalSymbol x cfg then
						Set.map (fun (fs, w) -> (x :: fs, w)) ySet
					else
						let xRules = Set.filter(fun r -> r.head = x) cfg.rules in
						let xBodies = Set.map (fun r -> r.body) (Set.filter(fun r -> hasEmpty r.body || verifyLength cfg sf r.body len) xRules) in
						let res = Set.flatMap (fun (fs1, w) -> Set.map (fun fs2 -> (fs2@fs1, w)) xBodies) ySet in
						res
				
		(* 0P1, 0P1*)
		(* *)


	let nextConfigs (cfg: t) (sf, w) : configurations =
		Util.show("Starting nextConfigs for: "^word2str sf);
		let res = expand cfg (sf,w) in
			Set.iter(fun (sf, w) -> Util.show("[" ^ word2str sf ^ "," ^ word2str w ^ "]")) res;
			res

	let nextConfigs2 (cfg: t) (len: int) (sf, w) : configurations =
		Util.show("Starting nextConfigs for: "^word2str sf);
		let res = expandGenerate cfg len (sf,w) in
			Set.iter(fun (sf, w) -> Util.show("[" ^ word2str sf ^ "," ^ word2str w ^ "]")) res;
			res

		

	let isAcceptingConfig (cfg: t) (rl, w) : bool =
		rl = w

	
	let accept (cfg: t) (w: word) : bool =
			Model.accept cfg w initialConfig nextConfigs isAcceptingConfig
		
	let acceptFull (cfg: t) (w: word) : bool * path * trail =
			Model.acceptFull cfg w initialConfig nextConfigs isAcceptingConfig
	
	let isAcceptingConfig2 (cfg: t) (sf, w) : bool =
		List.for_all(fun sym -> isTerminalSymbol sym cfg) sf
	
	

	let getWord (sf, _) = List.filter (fun symb -> isTerminalSymbol2 symb) sf

	let generate (cfg: t) (len: int) : words =
		
		Model.generate cfg len initialConfig nextConfigs2 isAcceptingConfig2 getWord


(* ----------------------------------------------------------------------------*)



end

module ContextFreeGrammarBasic =
struct
	include ContextFreeGrammarSupport
	open ContextFreeGrammarPrivate

	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
	let make (arg: t Arg.alternatives): t = make arg validate

	(* Exercices support *)
	let checkProperty (re: t) (prop: string) =
		match prop with
		| "regular" -> false (* TODO self#isRegular *)
		| "context free grammar" -> true
		| _ -> Model.checkProperty prop
	let checkExercise ex re = Model.checkExercise ex (accept re) (checkProperty re)	
	let checkExerciseFailures ex re = Model.checkExerciseFailures ex (accept re) (checkProperty re)	

	(* Ops *)
	let lookahead = lookahead
	let follow = follow
	let first = first
	let accept = accept
	let generate = generate	

	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model (make2 arg) as super
			val mutable simplified = false
		(* Representation *)
			method representation = representation
		(* Kind *)
			method isContextGrammar : bool = true
			method isContextFreeGrammar : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Ops *)
			(* This method checks if the grammar is regular
			*
			* @returns bool -> true if regular, false otherwise
			*)
			method isRegular : bool =

				let vs = representation.variables in
				let alp = representation.alphabet in

				let bs = Set.map (fun r -> r.body) representation.rules in

				let isRightLinear bs =
					let isRightLinearX b =
						match b with
							| [a] -> (Set.belongs a alp) || a = epsilon
							| [a; v] -> (Set.belongs a alp) && (Set.belongs v vs)
							| _ -> false
					in
						Set.for_all (fun b -> isRightLinearX b) bs
				in

				let isLeftLinear bs =
					let isLeftLinearX b =
						match b with
							| [a] -> (Set.belongs a alp) || a = epsilon
							| [v; a] -> (Set.belongs v vs) && (Set.belongs a alp)
							| _ -> false
					in
						Set.for_all (fun b -> isLeftLinearX b) bs
				in
					isRightLinear bs || isLeftLinear bs


      method first testWord = first testWord simplified self#representation
      method follow testSymbol = follow testSymbol simplified self#representation
      method lookahead rule = lookahead rule simplified self#representation

			(* This method checks if the given word is accepted by the grammar
			*
			* @param testWord -> word to be tested
			*
			* @returns bool -> true if it accepts the word, false otherwise
			*)


			method accept (testWord:word) : bool =
				ChomskyNormalForm.accept (self#representation) testWord

				method acceptFull (w: word) : bool * path * trail = acceptFull representation w
				
			method private acceptXXX (testWord:word) : bool =

				(* any word with a symbol not from the cfg alphabet will not be accepted
				if not (Set.subset (Set.make testWord) representation.alphabet) then false else
				*)

				let vs = representation.variables in


				(* for word wa, get subword to the left of its first variable *)
				let rec getPrefix wa =
					match wa with
						| [] -> []
						| x::xs -> if Set.belongs x vs then [] else x::(getPrefix xs)
				in

				(* for word wa, get subword to the rigth of its last variable *)
				let getSuffix wa =
					let rec getSuffixX wa sfx =
						match wa with
							| [] -> sfx
							| x::xs -> let auxSfx = sfx@[x] in
										if Set.belongs x vs then getSuffixX xs []
											else getSuffixX xs auxSfx
					in
						getSuffixX wa []
				in

				let rec firstNElements w n =
					match w with
						| [] -> []
						| x::xs -> if n > 0 then x::(firstNElements xs (n-1)) else []
				in

				let rec lastNElements w n =
					match w with
						| [] -> []
						| x::xs -> if n < (List.length w) then lastNElements xs n else w
				in

				(* a word can be discarded if its prefix does not match the leftmostmost part of word w *)
				let keepByPrefix genW testW =
					let pgw = getPrefix genW in
					let ptw = firstNElements testW (List.length pgw) in
						pgw = [] || pgw = ptw
				in


				(* a word can be discarded if its suffix does not match the rightmost part of word w *)
				let keepBySufix genW testW =
					let sgw = getSuffix genW in
					let stw = lastNElements testW (List.length sgw) in
						sgw = [] || sgw = stw
				in

				(* the word inst discarded only if it cant be discarded by neither its prefix nor its suffix *)
				let toKeep w tw = (w = [] && tw = []) || (keepByPrefix w tw && keepBySufix w tw) in


				let alph = representation.alphabet in
				let vs = representation.variables in
				let rs = representation.rules in
				let l = List.length testWord in

				let nextGeneration ws =
					let subsWs = Set.flatMap (fun w -> subVar w vs rs) ws in
					let rws = Set.filter (fun w -> not (exceedsMaxLen w l alph)) subsWs in
					let rws = Set.map (fun w -> removeEpsi w) rws in
						Set.filter (fun w -> toKeep w testWord ) rws

				in

				let start = Set.make [[representation.initial]] in

				let res = Set.historicalFixedPoint nextGeneration start in
					Set.exists (fun x -> x = testWord ) res




			method acceptWithTracing (testWord:word) =



				let vs = representation.variables in


				(* for word wa, get subword to the left of its first variable *)
				let rec getPrefix wa =
					match wa with
						| [] -> []
						| x::xs -> if Set.belongs x vs then [] else x::(getPrefix xs)
				in

				(* for word wa, get subword to the rigth of its last variable *)
				let getSuffix wa =
					let rec getSuffixX wa sfx =
						match wa with
							| [] -> sfx
							| x::xs -> let auxSfx = sfx@[x] in
										if Set.belongs x vs then getSuffixX xs []
											else getSuffixX xs auxSfx
					in
						getSuffixX wa []
				in

				let rec firstNElements w n =
					match w with
						| [] -> []
						| x::xs -> if n > 0 then x::(firstNElements xs (n-1)) else []
				in

				let rec lastNElements w n =
					match w with
						| [] -> []
						| x::xs -> if n < (List.length w) then lastNElements xs n else w
				in

				(* a word can be discarded if its prefix does not match the leftmostmost part of word w *)
				let keepByPrefix genW testW =
					let pgw = getPrefix genW in
					let ptw = firstNElements testW (List.length pgw) in
						pgw = [] || pgw = ptw
				in


				(* a word can be discarded if its suffix does not match the rightmost part of word w *)
				let keepBySufix genW testW =
					let sgw = getSuffix genW in
					let stw = lastNElements testW (List.length sgw) in
						sgw = [] || sgw = stw
				in

				(* the word inst discarded only if it cant be discarded by neither its prefix nor its suffix *)
				let toKeep w tw = (w = [] && tw = []) || (keepByPrefix w tw && keepBySufix w tw) in


				let alph = representation.alphabet in
				let vs = representation.variables in
				let rs = representation.rules in
				let l = List.length testWord in

				let nextGeneration ws =
					let subsWs = Set.flatMap (fun w -> subVar w vs rs) ws in
					let rws = Set.filter (fun w -> not (exceedsMaxLen w l alph)) subsWs in
					let rws = Set.map (fun w -> removeEpsi w) rws in
						Set.filter (fun w -> toKeep w testWord ) rws

				in

				let start = Set.make [[representation.initial]] in

				let res = Set.historicalFixedPointTracing nextGeneration start in


				let trimRes l =
					match l with
					| [] -> []
					| x::xs -> if Set.belongs testWord x then xs
								else l
				in

				let res2 = List.rev (trimRes (List.rev res)) in


				let printWset ws =
					Util.print ["["];
					Set.iter (fun w -> Util.print [word2str w; ";"]) ws;
					Util.println ["]"];
				in

					List.iter (fun ws -> printWset ws) res2




			(* This method generates all words up the the given lenght that belong to the grammars language
			*
			* @ param lenght -> the max lenght of generated words
			*
			* @returns words -> the set of generated words
			*)
			method generate (length:int) : words =

				let alph = representation.alphabet in
				let vs = representation.variables in
				let rs = representation.rules in


				let nextGeneration ws =
					let subsWs = Set.flatMap (fun w -> subVar w vs rs) ws in
						Set.filter (fun w -> not (exceedsMaxLen w length alph)) subsWs
				in

				let start = Set.make [[representation.initial]] in

				let res = Set.historicalFixedPoint nextGeneration start in

					cleanNonWords res vs

		(* Exercices support *)
			method checkProperty (prop: string) = checkProperty representation prop

		(* Learn-OCaml support *)
			method moduleName = moduleName
			method xTypeName = xTypeName
			method xTypeDeclString : string = prelude
			method toDisplayString (name: string): string = solution name self#representation
			method example : JSon.t = example
		end
end

module ContextFreeGrammarTop =
struct
	open ContextFreeGrammarBasic
	open ContextFreeGrammarBasicsX

	let cfgI cfg = internalize cfg
	let cfgX cfg = externalize cfg
	
	let cfg_load file = cfgX (make (Arg.File file))
	let cfg_text text = cfgX (make (Arg.Text text))
	let cfg_json json = cfgX (make (Arg.JSon json))
	let cfg_predef name = cfg_text (Examples.example name)

(*	let confX (s, w) = (state2str s, word2str w)
	let pathX (p: path) = pathX confX p
	let trailX (t: trail) = trailX confX t *)
	
	let stats () = RuntimeControl.stats ()

	let cfg_accept cfg w = accept (cfgI cfg) (wordI w)

(*
	let cfg_path cfg w =
		let (r,p,t) = acceptFull (cfgI cfg) (wordI w) in
			pathX p

	let cfg_trail cfg w =
		let (r,p,t) = acceptFull (cfgI cfg) (wordI w) in
			trailX t
		*)

	let cfg_generate cfg len = wordsX (generate (cfgI cfg) len)
end

open ContextFreeGrammarTop

     (* Adds a sufix to a variable name name *)
     let addSufixCFG (v: symbol)(sufix: string): symbol =
       str2symb((symb2str v)^"_"^sufix)


(* addSufix a que? *)
    let addSufixList  body sufix =
        List.map(fun s -> addSufixCFG  s sufix) body

       (* Renames all the variables in one gramatic adding a sufix *)	
     let renameVariablesCFG (cfg: ContextFreeGrammarBasic.t) (sufix: string): ContextFreeGrammarBasic.t =
       let open ContextFreeGrammarBasic in 
       {alphabet = cfg.alphabet;
       variables =	Set.map (fun v -> addSufixCFG v sufix) cfg.variables;
       initial = addSufixCFG cfg.initial sufix;
       rules = Set.map (fun {head= h;body = b} -> {head=(addSufixCFG h sufix);body= addSufixList b sufix}) cfg.rules
       }


(*

--------------------

let cfg_balanced = {| {
		kind : "context free grammar",
		description : "CFG: Language of balanced square bracket parentheses",
		name : "cfg_balanced",
		alphabet : ["[", "]"],
		variables : ["<Start>"],
		initial : "<Start>",
		rules : [ "<Start> -> [<Start>] | <Start><Start> | ~"]
	} |};;

let cfg = cfg_text cfg_balanced;;

let cfg2 = cfgX cfg;;





















let cfg2 = renameVariablesCFG (cfgI cfg) "ola";;





let cfg = cfg_predef "cfg_simple";;

let cfg2 = renameVariablesCFG (cfgI cfg) "ola";;



let cfg2 = cfgX (renameVariablesCFG (cfgI cfg) "ola");;

fa_generate fa 8;;

fa_accept fa "aaaa";;
fa_accept fa "aaaca";;

fa_path fa "aaaa";;
fa_path fa "aaaca";;

fa_trail fa "aaaa";;
--------------------

#print_depth 10000;;
#print_length 10000;;




--------------------
let fa = fa_predef "dfa_astar";;

fa_generate fa 8;;

fa_accept fa "aaaa";;
fa_accept fa "aaaca";;

fa_path fa "aaaa";;
fa_path fa "aaaca";;

fa_trail fa "aaaa";;
--------------------

#print_depth 10000;;
#print_length 10000;;



let fa_astar = {| {
		kind : "finite automaton2",
		description : "this is an example",
		name : "dfa_astar",
		alphabet: ["a"],
		states : ["START", "Z1"],
		initialState : "START",
		transitions : [
			["START", "a", "START"],
			["START", "~", "START"],			
			["START", "~", "Z"],			
			["Z", "a", "Z"],
			["START", "a", "Z"]
		],
		acceptStates : ["START", "Z"]
		} |}
;;
let fa = fa_text fa_astar;;

let fa_astar = {| {
		kind : "finite automaton2",
		description : "this is an example",
		name : "dfa_astar",
		alphabet: ["a"],
		states : ["START", "Z1"],
		initialState : "START",
		transitions : [
			["START", "a", "START"],
			["START", "~", "START"],			
			["START", "~", "Z"],			
			["Z", "a", "Z"],
			["START", "a", "Z"]
		],
		acceptStates : ["START", "Z"]
		} |}
;;
let fa = fa_text fa_astar;;

*)

# 3 "src/ContextFreeGrammarRDParser.ml"
open BasicTypes
open ContextFreeGrammarBasic

module RDParser =
struct

  (* given a head, returns the set of all its bodies according to the cfg's rules *)
	let bodiesOfHead h rl =
	  let open ContextFreeGrammarBasic in
		let rls = Set.filter (fun r -> r.head = h) rl in
			Set.map (fun r -> r.body) rls

  let rec tabCreator tabLevel =
    if tabLevel > 0 then "\t"^ tabCreator (tabLevel - 1) else ""

  class virtual parser =
    object(self)

    val arrayVar = "word"
    val currentCharVar = "currentChar"
    val currentIndexVar = "wordIndex"
      
    val getCharFun = "getChar"
    val parseErrorFun = "parseError"
    val matchCharFun = "matchChar"

    val virtual equality : string
    val virtual orOp : string
    val virtual functionArgsOpen : string
    val virtual functionArgsClose : string
    val virtual ifOpen : string 
    val virtual ifClose : string
    val virtual ifElseGuardOpen : string
    val virtual ifElseGuardClose : string
    val virtual expressionTermination : string
    val virtual return : string

    (* Method that will print includes/imports needed for the parser *)
    method virtual setupIncludes : string
    
    
    (* Method used to setup the variables for the parser. *)
  	(* Use values arrayVar, currentCharVar and currentIndexVar *)
  	(* to get correct variable names. *)
    method virtual setupVariables : string
    
    
    (* Method that prints the getCharFunction. *)
    (* This function consumes a symbol while parsing. *)
    method virtual getCharFunction : string
    
    
    (* Method that prints the match function. *)
    (* This function verifies if symbols match. *)
    (* Consumes the symbol if there is a match. *)
    (* Otherwise, calls error function. *)
    method virtual matchFunction : string
    
    
    (* Method that prints the error function. *)
    (* This function exists the program when called symbols match. *)
    method virtual errorFunction : string
    

    method printFunctions vars rep =
      if vars = Set.empty then ""
      else let (x,xs) = Set.cut vars in
        self#symbolFunction x rep ^
        (self#printFunctions xs rep)
 
    (* Method that prints the programs main function. *)
    method virtual mainFunction : symbol -> string
    

    method virtual createFun : string -> string -> string


    (*TODO Move to lower level*)
    method createFunCalls funs (rep: t) =
      match funs with
      | [] -> []
      | x::xs when Set.belongs x rep.alphabet -> [matchCharFun ^ functionArgsOpen ^ "\'" ^ symb2str x ^ "\'" ^ functionArgsClose ^ expressionTermination] @ self#createFunCalls xs rep
      | x::xs when Set.belongs x rep.variables -> [symb2str x ^ functionArgsOpen ^ functionArgsClose ^ expressionTermination] @ self#createFunCalls xs rep
      | x::xs -> []

    (*TODO Move to lower level*)
    method createIfConds conditions =
      let p = String.make 1 '\'' in
      match conditions with
      | [] -> ""
      | [x] -> currentCharVar ^ equality ^ p ^ symb2str x ^ p
      | x::xs -> currentCharVar ^ equality ^ p ^ symb2str x ^ p ^ " " ^ orOp ^ " " ^ self#createIfConds xs
      
    (*TODO Move to lower level*)
    method createIf ifList tabLevel = 
      let rec createIf2 first ifList tabLevel =
        let rec createExpr exprList tabLevel =
          match exprList with 
          | [] -> ""
          | x::xs -> (tabCreator tabLevel) ^ x ^ "\n" ^ createExpr xs tabLevel
        in
        let tab = (tabCreator tabLevel) in
        match ifList with
        | [] -> ""
        | [(c,e)] -> tab ^ "else" ^ ifElseGuardOpen ^ "\n" ^ (createExpr e (tabLevel+1)) ^ tab ^ ifElseGuardClose
        | (c,e)::xs -> tab ^ (if first then "if" else "else if") ^ ifOpen ^ c ^ ifClose ^ ifElseGuardOpen ^ "\n" ^ 
                       (createExpr e (tabLevel+1)) ^
                       tab ^ (ifElseGuardClose) ^ "\n" ^ createIf2 false xs tabLevel
      in
      createIf2 true ifList tabLevel

  
    method symbolFunction s (rep: t) =
      let open ContextFreeGrammarBasic in
      let getNextTerminals rule = 
(*        Printf.printf "\tGetting lookahead for rules";*)
(*        List.iter (fun r -> Printf.printf " %s " r) (CFGSyntax.toStringList (Set.make [rule]));*)
(*        Printf.printf "\n";*)
(*        Set.iter (fun r -> Printf.printf "\tGot result %s\n" (symb2str r)) (ContextFreeGrammarBasic.lookahead rule false rep);*)
        ContextFreeGrammarBasic.lookahead rule false rep
      in

      let rules = Set.filter (fun {head;body} -> head = s) rep.rules in
      let funCalls = (List.map (fun {head;body} -> self#createFunCalls body rep) (Set.toList rules)) in
      let lookaheads = Set.map (getNextTerminals) rules in
      let mergedMap = List.map2 (fun a b -> (self#createIfConds (Set.toList a),b)) (Set.toList lookaheads) funCalls in
(*      Printf.printf "Current Var: %s\n" (symb2str s);*)
(*      List.iter (fun (a,b) -> Printf.printf "\t%s" a;*)
(*                              Printf.printf "\n";*)
(*                              List.iter (fun c -> Printf.printf "\t\t%s\n" c) b*)
(*      ) mergedMap;*)
      let mergedMap = mergedMap @ [("",[(parseErrorFun ^ functionArgsOpen ^ functionArgsClose ^  expressionTermination)])] in
      self#createFun (symb2str s) (self#createIf mergedMap 1)


    method virtual build : t -> string

  end
end


module RDParserWithDeclarations =
struct

  class virtual parser =
    object(self) inherit RDParser.parser as super
    
  end

end


module RDParserWithoutDeclarations =
struct

  class virtual parser =
    object(self) inherit RDParser.parser as super
    
      method build (rep: t) =
        self#setupIncludes ^
        self#setupVariables ^
        self#getCharFunction ^
        self#errorFunction ^
        self#matchFunction ^
        (self#printFunctions rep.variables rep) ^
        (self#mainFunction rep.initial)
    
  end
end


module RDParserNeedFunDeclaration =
struct

  class virtual parser =
    object(self) inherit RDParserWithDeclarations.parser as super
    
      (* Method that prints function declarations *)
      method functionDeclarations vars =
        let rec printDecl vars =
          if vars = Set.empty then ""
          else let (x,xs) = Set.cut vars in
            Printf.sprintf {|void %s();|} (symb2str x) ^ "\n" ^ printDecl xs
          in
      printDecl vars ^ "\n"
    
      method build (rep: t) =
        Util.stripHead (self#setupIncludes ^
        self#setupVariables ^
        self#functionDeclarations rep.variables ^
        self#getCharFunction ^
        self#errorFunction ^
        self#matchFunction ^
        (self#printFunctions rep.variables rep) ^
        (self#mainFunction rep.initial))
    
  end

end


module RDParserNeedRecursiveFunDeclaration =
struct

  class virtual parser =
    object(self) inherit RDParserWithDeclarations.parser as super
    
      method printFunctions vars rep =
        let first = true in
        let rec printFunctionsX vars rep first =
          if vars = Set.empty then ""
          else let (x,xs) = Set.cut vars in
            (if first then "let rec " else "and ") ^
            self#symbolFunction x rep ^
            (printFunctionsX xs rep false)
        in
        printFunctionsX vars rep first
    
      method build (rep: t) =
        Util.stripHead (self#setupIncludes ^
        self#setupVariables ^
        self#getCharFunction ^
        self#errorFunction ^
        self#matchFunction ^
        (self#printFunctions rep.variables rep) ^
        (self#mainFunction rep.initial))
    
  end

end


module RDParserC =
struct

  class parser =
    object(self) inherit RDParserNeedFunDeclaration.parser as super

    val equality = "=="
    val orOp = "||"
    val functionArgsOpen = "("
    val functionArgsClose = ")"
    val ifOpen = "("
    val ifClose = ")"
    val ifElseGuardOpen = "{"
    val ifElseGuardClose = "}"
    val expressionTermination = ";"
    val return = "return"


    method setupIncludes =
  	  Printf.sprintf {|
		 #include <stdio.h>
		 #include <stdlib.h>
		 #include <string.h>
      |}
    
    
    method setupVariables =
      Printf.sprintf {|
		char* %s;
		char %s;
		int %s;
		|} arrayVar currentCharVar currentIndexVar
    
    
    method getCharFunction =
      Printf.sprintf {|
		char %s(){
			return %s[%s++];
		}
      |} (getCharFun) (arrayVar) (currentIndexVar)
    
    
    method matchFunction =
      Printf.sprintf {|
		void %s(char t) {
			if(%s == t) {
				%s = %s();
			}
			else {
				%s();
			}
		}
      |} (matchCharFun) (currentCharVar) (currentCharVar) (getCharFun) (parseErrorFun)
    
    
    method errorFunction = 
      Printf.sprintf {|
		void %s() {
			printf("Error parsing! %s = %%c\n", %s);
			exit(1);
		}
      |} (parseErrorFun) (currentCharVar) (currentCharVar)
    
      
    method mainFunction initialVar = 
      Printf.sprintf {|
		int main(int argc, char* argv[]){
		  char termChar = '$'; 
		  char* tmp = strcat( argv[1], &termChar);
			%s = tmp;
			%s = %s();
			%s();
			if(%s == '$'){
				printf("Parsing OK!\n");
			} else {
				%s();
			}
			return 0;
		}
    |} (arrayVar) (currentCharVar) (getCharFun) (symb2str initialVar) (currentCharVar) (parseErrorFun)
    

    method createFun name contents =
      Printf.sprintf {|
        void %s() {
        %s
        }
      |} name contents

  end
end


module RDParserOCaml =
struct

	let tabCreator = RDParser.tabCreator

  class parser =
    object(self) inherit RDParserNeedRecursiveFunDeclaration.parser as super

    val equality = "="
    val orOp = "||"
    val functionArgsOpen = "("
    val functionArgsClose = ")"
    val ifOpen = "("
    val ifClose = ")"
    val ifElseGuardOpen = "("
    val ifElseGuardClose = ")"
    val expressionTermination = ";"
    val return = "()"
    
    method setupIncludes = ""


    method setupVariables = 
      Printf.sprintf {|
        let %s = ref [||]
        let %s = ref 'l'
        let %s = ref 0
      |} arrayVar currentCharVar currentIndexVar
      
    
    method getCharFunction = 
      Printf.sprintf {|
        let %s() =
          if ( !%s < (Array.length !%s) - 1 )
          then %s := !%s + 1;
          %s := !%s.(!%s)
              |} (getCharFun)
                (currentIndexVar) (arrayVar)
                (currentIndexVar) (currentIndexVar)
                currentCharVar (arrayVar) (currentIndexVar)
        
        
    method createFunCalls funs (rep: t) =
      match funs with
      | [] -> []
      | x::xs when Set.belongs x rep.alphabet -> [matchCharFun ^ functionArgsOpen ^ "\'" ^ (symb2str x) ^ "\'" ^ functionArgsClose ^ expressionTermination] @ self#createFunCalls xs rep
      | x::xs when Set.belongs x rep.variables -> [String.lowercase_ascii (symb2str x) ^ functionArgsOpen ^ functionArgsClose ^ expressionTermination] @ self#createFunCalls xs rep
      | x::xs -> []


    method matchFunction = 
      Printf.sprintf {|
		let %s t =
			if (!%s = t)
			then (%s())
			else (%s())
      |} matchCharFun currentCharVar getCharFun parseErrorFun

      
    method errorFunction = 
      Printf.sprintf {|
		let %s() =
			Printf.printf "Error parsing! %s = %%c\n" !%s;
			exit 1
      |} parseErrorFun currentCharVar currentCharVar


    method createIfConds conditions =
      let p = String.make 1 '\'' in
      match conditions with
      | [] -> ""
      | [x] -> "!" ^ currentCharVar ^ equality ^ p ^ symb2str x ^ p
      | x::xs -> "!" ^ currentCharVar ^ equality ^ p ^ symb2str x ^ p ^ " " ^ orOp ^ " " ^ self#createIfConds xs
      

    method createIf ifList tabLevel = 
      let rec createIf2 first ifList tabLevel =
        let rec createExpr exprList tabLevel =
          match exprList with 
          | [] -> ""
          | x::xs -> (tabCreator tabLevel) ^ x ^ "\n" ^ createExpr xs tabLevel
        in
        let tab = (tabCreator tabLevel) in
        match ifList with
        | [] -> ""
        | [(c,e)] -> tab ^ "else" ^ ifElseGuardOpen ^ "\n" ^ (createExpr e (tabLevel+1)) ^ tab ^ ifElseGuardClose
        | (c,e)::xs -> tab ^ (if first then "if" else "else if") ^ ifOpen ^ c ^ ifClose ^ " then " ^ ifElseGuardOpen ^ "\n" ^ 
                       (createExpr e (tabLevel+1)) ^
                       tab ^ (ifElseGuardClose) ^ "\n" ^ createIf2 false xs tabLevel
      in
      createIf2 true ifList tabLevel
    
    
    method mainFunction i = 
      Printf.sprintf {|
		let explode s = List.init (String.length s) (String.get s)

		let main () =
			%s := Array.of_list (explode Sys.argv.(1));
			%s := Array.append (!%s) ([|'$'|]);
			%s := !%s.(0);
			%s();
			if !%s = '$'
			then Printf.printf "Parsing OK!"
			else %s();
			exit 0

		let _ = main()
	  |} arrayVar arrayVar arrayVar
                  currentCharVar arrayVar
                  (String.lowercase_ascii (symb2str i))
                  currentCharVar
                  parseErrorFun

    method createFun name contents =
      (* Does not need let, inherited class deals with it *)
      Printf.sprintf {|
		%s () =
			%s
      |} (String.lowercase_ascii name) contents

  end
end

module RDParserJava =
struct

  class parser =
    object(self) inherit RDParserWithoutDeclarations.parser as super

    val equality = "=="
    val orOp = "||"
    val functionArgsOpen = "("
    val functionArgsClose = ")"
    val ifOpen = "("
    val ifClose = ")"
    val ifElseGuardOpen = "{"
    val ifElseGuardClose = "}"
    val expressionTermination = ";"
    val return = "return"

    method setupIncludes = ""
    
    method setupVariables =
  	  Printf.sprintf {|
		static char[] %s;
		static char %s;
		static int %s;
      |} arrayVar currentCharVar currentIndexVar
 

    method getCharFunction =
      Printf.sprintf {|
		static char %s() {
			return %s[%s++];
		}
      |} (getCharFun) (arrayVar) (currentIndexVar)
    
    method matchFunction =
      Printf.sprintf {|
		static void %s(char t) {
			if(%s == t)
				%s = %s();
			else %s();
		}
      |} (matchCharFun) (currentCharVar) (currentCharVar) (getCharFun) (parseErrorFun)
    
    
    method errorFunction = 
      Printf.sprintf {|
		static void %s() {
			System.out.println("Error parsing! %s = " + %s);
			System.exit(1);
		}
      |} (parseErrorFun) (currentCharVar) (currentCharVar)


    method mainFunction initialVar = 
      Printf.sprintf {|
		public static void main(String[] args) {
			%s = 0;
			%s = (args[0].toString()+'$').toCharArray(); //Add terminal symbol
			%s = %s();
			%s();
			if(%s == '$')
				System.out.println("Parsing OK!");
			else %s();
		}
    |} currentIndexVar arrayVar (currentCharVar) (getCharFun) (symb2str initialVar) (currentCharVar) (parseErrorFun)


    method createFun name contents =
      Printf.sprintf {|
		static void %s () {
			%s
		}
      |} name contents

	method build (rep: t) =
		"public class Main {" ^
			super#build rep ^
		"}"

  end
end


# 3 "src/ContextFreeGrammarLL1.ml"
open BasicTypes
open ContextFreeGrammarBasic  

module ContextFreeGrammarLL1 =
struct
  open RDParserC
  open RDParserOCaml
  open RDParserJava
   
  type syntaxTable = { term : symbol option; var : symbol option; rBody : word option }
  type acceptTable = { input : string; stack: string; production: string }
  type recognized = { recog : string; left : string }
	type acceptStep = {
    syntaxTable : syntaxTable;
    acceptedString: string;
    acceptTable : acceptTable;
    recognized : recognized;
    accepted: bool option;
    nodes: cfgTree list
  }
  
  let bodiesOfHead = RDParser.bodiesOfHead
  
  let leftRecursionRemovalTransform = "Remove left recursion"
  let leftFactoringTransform = "Left factoring"
  let cleanProductiveTransform = "Clean unproductive symbols"
  let cleanAccessibleTransform = "Clean inaccessible symbols"
  let unitRemovalTransform = "Unit productions removal"
  let epsilonRemovalTransform = "Epsilon productions removal"
  let ll1Transform = "LL1 transformation"
  
  type transformation = { tType : string; grammar : ContextFreeGrammarBasic.model }
  
  let newStep ?(term = None) ?(var = None) ?(rBody = None)
              ?(acceptedString = "") 
              ?(input = "") ?(stack = "") ?(production = "") 
              ?(recog = "") ?(left = "") 
              ?(accepted = None) ?(nodes = []) simple =
    (* let dollar = String.make 1 dollar in
    let input = if simple then input else input ^ dollar in
    let stack = if simple then stack else stack ^ dollar in *)
    {
      syntaxTable = {term; var; rBody};
      acceptedString = acceptedString;
      acceptTable = {input; stack; production};
      recognized = {recog; left};
      accepted = accepted;
      nodes = nodes
    }
    
  
  (*type rule = CFGSyntax.rule*)
  

  let rec doWordGenerateEmptyX w seen (rep:t) =
    let doGenerateEmpty x =
      if List.mem x seen
      then false
      else(
		    let bodies = bodiesOfHead x rep.rules in
		    Set.exists (fun b -> doWordGenerateEmptyX b (x::seen) rep) bodies 
		  )
		in      
      List.for_all doGenerateEmpty w

  let removeEpsilonFromWord w =
    List.filter (fun c -> c <> epsilon) w

  let removeDollarFromWord w =
    List.filter (fun c -> c <> dollar) w

  let doWordGenerateEmpty w (rep:t) =
    doWordGenerateEmptyX (removeDollarFromWord w) [] rep
    
  let printRepresentation (rep:t) =
    Printf.printf "Alphabet = "; Util.printAlphabet rep.alphabet;
    Printf.printf "Variables = "; Util.printAlphabet rep.variables;
    Printf.printf "Initial = %s\n" (symb2str rep.initial);
    Printf.printf "Rules {\n"; Set.iter (fun {head=h; body=b} -> Printf.printf "\t%s -> %s\n" (symb2str h) (word2str b)) rep.rules;
    Printf.printf "}\n\n"

  let rec print_tuples = (*TEST*)
    function
    | [] -> ()
    | (a, b) :: rest ->
      Printf.printf "%c -> " a;
      Util.printAlphabet b;
      print_tuples rest
      
  let rec print_list = (*TEST*)
    function
    | [] -> Printf.printf "";
    | x::xs ->
      Printf.printf "%c" x;
      print_list xs  
  
  (*Given a variable, returns all rules with variable as head*)
  let sameHeadRules (testSymbol:symbol) (rep:t) =
	  Set.toList (Set.filter (fun r -> testSymbol = r.head) rep.rules)

  let rec pairs l =
    match l with
      | [] -> []
      | x::xs -> List.map (fun v -> (x,v)) xs :: pairs xs

  (*Given a word and variable, returns the word behind the variable*)
  let rec behindSymbol (word:word) (var:variable) = 
    match word with
    | [] -> []
    | x::xs -> if x <> var then x::behindSymbol xs var else []


  let rec leftRecursionTest initial (seen: variables) (rep:t) =
    if Set.belongs initial rep.alphabet then false else (*rule starting with a terminal symbol can't be left recursive*)
      let ruleBodies = Set.toList (bodiesOfHead initial rep.rules) in (* example: rulesBodies = [['B';'a']; ['b']*)
(*        Printf.printf "initial = %c\n" initial;*)
      let leftRecursionTest2 head body seen (rep:t) =
        let wordBehind = behindSymbol body head in
        let behindGenerateEmpty = doWordGenerateEmpty wordBehind rep in
        let body = if behindGenerateEmpty 
                     then List.filter (fun x -> not (List.mem x wordBehind)) body 
                     else body
        in
        
        match body with
        | [] -> false
        | x::xs when x = head || Set.belongs x seen -> true
        | x::xs -> leftRecursionTest x (Set.cons x seen) rep in
        
      List.exists (fun x -> x = true) (List.map (fun x -> leftRecursionTest2 initial x seen rep) ruleBodies)

      
  let isLeftRecursive (rep:t) = 
    Set.exists (fun x -> x = true) (Set.map (fun v -> leftRecursionTest v Set.empty rep) rep.variables)

  let isLL1Deterministic simple (rep:t) =
    let variables = rep.variables in
    let pairsSet = Set.map (fun v -> Set.make (List.flatten (pairs (sameHeadRules v rep)))) variables in
    let lookaheadInterSet = Set.flatMap (fun v -> Set.map (fun (p1,p2) -> Set.inter (lookahead p1 simple rep) (lookahead p2 simple rep)) v) pairsSet in
      Set.for_all (fun x -> Set.size x = 0) lookaheadInterSet

  let isLL1 simple (rep:t) = 
    isLL1Deterministic simple rep
  
  (*given a production X->a, does lookahead(X->a), b, and returns pair ((X,b),a)*)
  let lookahead2Tuple rule simple (rep:t) =
    let lookahead = lookahead rule simple rep in 
      Set.map (fun l -> ((rule.head, l), rule.body)) lookahead
  
  let createParsingTable simple (rep:t) = 
    let lookaheadSet = Set.flatMap (fun r -> lookahead2Tuple r simple rep) rep.rules in
      lookaheadSet
  
  let hasParsingTableConflict simple (rep:t) =
    let parsingTable = createParsingTable simple rep in
    let repeatsTbl = Hashtbl.create (Set.size parsingTable) in
    let getRepeatNum c repeatsTbl =
      let repeat = Hashtbl.find_opt repeatsTbl c in
      match repeat with
      | None -> Hashtbl.add repeatsTbl c 1; false
      | Some a -> true
    in
    let boolResults = Set.map (fun ( (v,t), _ ) -> getRepeatNum (v,t) repeatsTbl ) parsingTable in
    Set.exists (fun r -> r) boolResults
    
  
  (*accept*)
  
(*  let printParsingInfo entry stack sub isSub =*)
(*    Printf.printf "\t"; print_list entry;*)
(*    Printf.printf "\t"; print_list stack;*)
(*    if isSub*)
(*      then (Printf.printf "\t%c->" (List.nth stack 0); print_list sub;)*)
(*      else Printf.printf "\t";*)
(*    Printf.printf "\n"*)
(*  *)
(*  (*given the entry, stack and parsingTable, rewrites the leftmost*)*)
(*  (*variable on the stack with its respective parsingTable rule*)*)
(*  let ruleRewrite (entry:word) (stack:word) parsingTable =*)
(*    let entryChar = List.nth entry 0 in*)
(*    let stackChar = List.nth stack 0 in*)
(*    let parsingTableList = Set.toList parsingTable in*)
(*    let substitution = List.assoc (stackChar, entryChar) parsingTableList in*)
(*      match stack with*)
(*      | [] -> []*)
(*      | x::xs ->*)
(*                printParsingInfo entry stack substitution true;*)
(*                substitution@xs*)
(*  *)
(*  let rec acceptX entry stack parsingTable (rep:t) =*)
(*    match entry with*)
(*    | [] -> if doWordGenerateEmpty stack rep then true else false*)
(*    | x::xs -> match stack with*)
(*                | [] -> false*)
(*                | x2::xs2 -> if Set.belongs x2 rep.variables*)
(*                             then*)
(*                                let newStack = ruleRewrite entry stack parsingTable in*)
(*                                acceptX entry newStack parsingTable rep*)
(*                             else if x=x2 *)
(*                                  then (printParsingInfo entry stack [] false;*)
(*                                       acceptX xs xs2 parsingTable rep )*)
(*                                  else false*)
(*  *)
(*  let acceptZ word rep = *)
(*    Printf.printf "\t"; Printf.printf "Entry: ";*)
(*    Printf.printf "\t"; Printf.printf "Stack: ";*)
(*    Printf.printf "\t"; Printf.printf "Rule: \n";*)
(*    let parsingTable = createParsingTable rep in*)
(*      try (acceptX word [rep.initial] parsingTable rep) *)
(*        with Not_found -> Printf.printf "\t\t\tApplicable rule not found!\n"; false*)

  let word2tree w (rep:t) =
    let rec word2tree2 w =
    match w with
    | [] -> []
    | x::xs -> (if Set.belongs x rep.alphabet
                then Leaf x
                else Root(x,[]))
                :: word2tree2 xs
    in
    
    if List.length w = 0
    then [Leaf epsilon]
    else word2tree2 w

  let rec acceptX entry stack parsingTable (currPerm:symbol list) simple (rep:t) =
    match entry with
    | [] -> [] (*Not supposed to happen*)
    | x::xs when x = dollar ->
          (match stack with
          | [] -> [] (*Not supposed to happen*)
          | x::xs -> if doWordGenerateEmpty [x] rep
                      then
                        (
                          if x = dollar
                          then [newStep ~acceptedString:(word2str currPerm)
                               ~input:(word2str entry)
                               ~stack:(word2str stack)
                               ~recog:(word2str (currPerm))
                               ~accepted:(Some true)
                                simple]
                          else (newStep ~var:(Some (List.hd stack))
                              ~term:(Some dollar)
                              ~rBody:(Some [])
                              ~acceptedString:(word2str currPerm)
                              ~input:(word2str entry)
                              ~stack:(word2str stack) 
                              ~production:(symb2str (List.hd stack) ^ " -> " ^ "") 
                              ~recog:(word2str currPerm)
                              ~nodes:(word2tree [] rep)
                              simple) :: acceptX entry xs parsingTable currPerm simple rep
                        )
                      else [newStep ~var:(Some (List.hd stack))
                      ~term:(Some dollar)
                      ~rBody:(Some [])
                      ~acceptedString:(word2str currPerm) 
                      ~input:(word2str entry)
                      ~stack:(word2str stack)
                      ~recog:(word2str currPerm) ~left:(word2str (removeDollarFromWord stack))
                      ~accepted:(Some false)
                      simple]
             )
    | x::xs -> match stack with
                | [] -> [] (*Not supposed to happen*)
                | [epsilon] -> [newStep ~acceptedString:(word2str currPerm)
                                ~input:(word2str entry)
                                ~stack:(word2str stack)
                                ~recog:(word2str currPerm) ~left:(word2str (removeDollarFromWord stack))
                                ~accepted:(Some false)
                                simple]
                | x2::xs2 -> if Set.belongs x2 rep.variables
                             then
                                let entryChar = List.nth entry 0 in
                                let stackChar = List.nth stack 0 in
                                let parsingTableList = Set.toList parsingTable in
                                let substitution = List.assoc_opt (stackChar, entryChar) parsingTableList in
                                match substitution with
                                  | None -> [newStep ~term:(Some entryChar) ~var:(Some stackChar)
                                                     ~acceptedString:(word2str currPerm)
                                                     ~input:(word2str entry) ~stack:(word2str stack)
                                                     ~recog:(word2str currPerm) ~left:(word2str (removeDollarFromWord stack))
                                                     ~accepted:(Some false)
                                                     simple]
                                  | Some s -> let newStack = 
                                                match stack with
                                                | [] -> []
                                                | x::xs -> s@xs 
                                              in
                                              (newStep ~term:(Some entryChar) ~var:(Some stackChar) ~rBody:(Some s)
                                                       ~acceptedString:(word2str currPerm)
                                                       ~input:(word2str entry) ~stack:(word2str stack) ~production:(symb2str (List.nth stack 0) ^ " -> " ^ word2str s)
                                                       ~recog:(word2str currPerm) ~left:(word2str (removeDollarFromWord stack))
                                                       ~nodes:(word2tree s rep)
                                                       simple) :: acceptX entry newStack parsingTable currPerm simple rep
                              else if x=x2 
                                  then
                                    let newCurrPerm = currPerm @ [x] in
                                    (newStep ~acceptedString:(word2str newCurrPerm)
                                             ~input:(word2str entry) ~stack:(word2str stack)
                                             ~recog:(word2str newCurrPerm) ~left:(word2str (List.tl (removeDollarFromWord stack)))
                                             simple) :: acceptX xs xs2 parsingTable newCurrPerm simple rep 
                                  else [newStep ~acceptedString:(word2str currPerm)
                                                ~input:(word2str entry) ~stack:(word2str stack) 
                                                ~recog:(word2str currPerm) ~left:(word2str (removeDollarFromWord stack))
                                                ~accepted:(Some false)
                                                simple]
  
  let acceptZ word simple (rep:t) = 
    let word = word @ [dollar] in
    let initial = [rep.initial] @ [dollar] in
    let parsingTable = createParsingTable simple rep in
      (newStep ~input:(word2str word) ~stack:(word2str initial) ~nodes:[Root(rep.initial,[])] simple)
      ::acceptX word initial parsingTable [] simple rep

  let rec acumFixedPoint (f: 'a set -> 'a set) (x: 'a set): 'a set =
    let next = Set.union x (f x) in
      if x = next then x
      else acumFixedPoint f next
  
  (*productive symbols*)
  
  (*given a rule and a set of productive variables, verifies if given*)
  (*rule is productive*)
  let isRuleProductive r prodVars (rep:t) =
(*    Printf.printf "\t\t\tisRuleProductive - Prod = %s   prodVars = %s\n" (word2str r) (word2str (Set.toList prodVars));*)
    List.for_all (fun c -> Set.belongs c rep.alphabet || Set.belongs c prodVars) r
      
  (*given a variable and a set of productive variables, verifies if given *)
  (*variable is productive*)
  let isSymbolProductive h prodVars (rep:t) =
    let rules = bodiesOfHead h rep.rules in
      Set.exists (fun r -> 
(*                          Printf.printf "\t\tProduction = %c -> %s\n" h (word2str r);*)
                          isRuleProductive r prodVars rep
                  ) rules
      
        
  let productiveSymbolsFP (rep:t) varP =
    Set.filter (fun v -> (*Printf.printf "\tVar %c\n" v;*) isSymbolProductive v varP rep) (Set.diff rep.variables varP)
  
  (*show the productive symbols of the current grammar*)
  let productiveSymbols (rep:t) =
    acumFixedPoint (productiveSymbolsFP rep) Set.empty
  
  (*show the simplified grammar with only productive symbols*)
  (*TODO Confirm correct new model*)
  let productiveGrammarRewrite (rep:t) =
    let prodSyms = productiveSymbols rep in
(*    Printf.printf "Productive Symbols:\n";*)
(*    Set.iter (fun s -> Printf.printf "\t%c\n" s) prodSyms;*)
(*    Printf.printf "\n";*)
    let unprodSyms = Set.diff rep.variables prodSyms in
(*    Printf.printf "Unproductive Symbols:\n";*)
(*    Set.iter (fun s -> Printf.printf "\t%c\n" s) unprodSyms;*)
(*    Printf.printf "\n";*)
    let newRules = Set.filter (fun r -> Set.belongs r.head prodSyms && List.for_all (fun c -> not (Set.belongs c unprodSyms)) r.body) rep.rules in
(*    Printf.printf "New productions:\n";*)
(*    Set.iter (fun {head=h;body=b} -> Printf.printf "\t%c -> %s\n" h (word2str b)) newRules;*)
      new ContextFreeGrammarBasic.model (Arg.Representation {
								alphabet = rep.alphabet; (*TODO Get productive alphabet*)
								variables = prodSyms;
								initial = rep.initial;
								rules = newRules
						} )

  
  (*accessible symbols*)
  
  (*given a rule and a set of accessible symbols, adds all symbols from the*)
  (*rule to the set*)
  let ruleAccessibleSymbols r aSymbols =
    Set.flatten (Set.make (List.map (fun s -> Set.cons s aSymbols) r))

  let rulesAccessibleSymbols h aSymbols (rep:t) =
    let rules = bodiesOfHead h rep.rules in
      Set.flatMap (fun r -> ruleAccessibleSymbols r aSymbols) rules
  
  let accessibleSymbolsX (rep:t) aSymbols =
    let vars = Set.filter (fun v -> Set.belongs v rep.variables) aSymbols in (*Remove terminals*)
      Set.flatMap (fun v -> rulesAccessibleSymbols v aSymbols rep) vars
  
  (*show the accessible symbols of the current grammar*)
  let accessibleSymbols (rep:t) = 
    Util.fixedPoint (accessibleSymbolsX rep) (Set.make [rep.initial])
  
  (*TODO Confirm correct new model*)
  let accessibleGrammarRewrite (rep:t) =
    let accessSymbs = accessibleSymbols rep in
    let accessTerms = Set.filter (fun s -> Set.belongs s rep.alphabet) accessSymbs in
    let accessVars = Set.filter (fun s -> Set.belongs s rep.variables) accessSymbs in
    let rules = Set.filter (fun r -> Set.belongs r.head accessVars) rep.rules in
      new ContextFreeGrammarBasic.model (Arg.Representation {
								alphabet = accessTerms;
								variables = accessVars;
								initial = rep.initial;
								rules = rules
						} )

  let clean (rep:t) =
    let prodRewrite = {tType = cleanProductiveTransform; grammar = productiveGrammarRewrite rep} in
    let accessRewrite = {tType = cleanAccessibleTransform; grammar = accessibleGrammarRewrite prodRewrite.grammar#representation} in
    [prodRewrite; accessRewrite]
(*    accessibleGrammarRewrite (productiveGrammarRewrite rep)#representation*)

  let isCFGFullyProductive (rep:t) =
    Set.equals (productiveSymbols rep) (rep.variables)

  let isCFGFullyAccessible (rep:t) =
    Set.equals (accessibleSymbols rep) (Set.union rep.variables rep.alphabet)
    
  let isClean (rep:t) =
    isCFGFullyProductive rep && isCFGFullyAccessible rep
  
  let getNewVar vs =
    let chars = Set.make ['A'; 'B'; 'C'; 'D'; 'E'; 'F'; 'G'; 'H'; 'I'; 'J'; 'K'; 'L'; 'M'; 'N'; 'O'; 'P'; 'Q'; 'R'; 'S'; 'T'; 'U'; 'V'; 'W'; 'X'; 'Y'; 'Z'] in
    let symbs = Set.map char2symb chars in
    let acceptableVars = Set.diff symbs vs in
      Set.nth acceptableVars 0


  let rec leftCorner2 symbol seen (rep: t) =
    match symbol with
    | [] -> Set.empty
    | x::xs ->
      if Set.belongs x seen 
      then Set.make [x]
      else 
        if Set.belongs x rep.alphabet
        then Set.make [x]
        else Set.union 
              (Set.make [x])
              (Set.flatMap (fun b -> (leftCorner2 b (Set.cons x seen) rep)) (bodiesOfHead x rep.rules))

  let leftCorner symbol rep =
    leftCorner2 [symbol] Set.empty rep

    
  (*left recursion removal*)

  let sortLeftCorner l =
    let sortFun e1 e2 =
      let (_, e1) = e1 in
      let (_, e2) = e2 in
      if List.length e1 > List.length e2 then -1
      else (if List.length e1 < List.length e2 then 1 else 0)
    in
    List.sort sortFun l

  let addToMap map varL =
    let rec addToMap2 map varL value =
      match varL with
      | [] -> ()
      | x::xs -> (*Printf.printf "Adding var %c with value %d\n" x value;*)
                  Hashtbl.add map x value; addToMap2 map xs (value+1)
    in
    addToMap2 map varL 0

(* TODO Util.printWord does not exist anymore *)
(*  let rec print_rules r =*)
(*    match r with*)
(*    | [] -> Printf.printf "\n"*)
(*    | x::xs -> Printf.printf " - %c ->" x.head; Util.printWord x.body; print_rules xs*)


  let removeDirectLeftRecursion (rep:t) = 
    let hasRuleDirectLeftRecursion r =
      match r.body with
      | [] -> false
      | x::xs when x = r.head -> true
      | x::xs -> false
    in
    
    let recursiveRuleRewrite r nV =
      let body =
        match r.body with
        | [] -> [epsilon] (*Not reacheable*)
        | x::xs -> xs@[nV]
      in
      { head = nV; body = body }
    in
      
    let nRecursiveRuleRewrite r nV =
      let body = r.body@[nV] in
        { head = r.head; body = body }
    in
    
    let rec removeDLRFromVar v drs ndrs nV =
      if v = Set.empty then Set.empty
      else let (x,xs) = Set.cut v in
(*        Printf.printf "\tRemoving direct left recursion from variable %c\n" x;*)
        let recursiveRs = Set.filter (fun r -> r.head = x) drs in
        let nRecursiveRs = Set.filter (fun r -> r.head = x) ndrs in
        let newVar = getNewVar nV in
(*        Printf.printf "\tNew variable is %c\n" newVar;*)
        let recRulesRewriteTmp = Set.map (fun r -> recursiveRuleRewrite r newVar) recursiveRs in
        let recRulesRewrite = Set.cons ( {head = newVar; body = []} ) recRulesRewriteTmp in
        let nRecRulesRewrite = Set.map (fun r -> nRecursiveRuleRewrite r newVar) nRecursiveRs in
        let newRules = Set.union recRulesRewrite nRecRulesRewrite in
(*        print_rules (Set.toList newRules);*)
          Set.union newRules (removeDLRFromVar xs drs ndrs (Set.cons newVar nV))
    in
    
    let leftRecursiveRules = Set.filter (fun r -> hasRuleDirectLeftRecursion r) rep.rules in
(*        print_rules (Set.toList leftRecursiveRules);*)
    let leftRecursiveVars = Set.map (fun r -> r.head) leftRecursiveRules in
    let nonLeftRecursiveRules = Set.diff rep.rules leftRecursiveRules in
(*        print_rules (Set.toList nonLeftRecursiveRules);*)
    let nonLeftRecursiveRulesClean = Set.filter (fun {head = h; body = _} -> not (Set.belongs h leftRecursiveVars)) nonLeftRecursiveRules in
    let newRules = Set.union nonLeftRecursiveRulesClean (removeDLRFromVar leftRecursiveVars leftRecursiveRules nonLeftRecursiveRules rep.variables) in
(*      print_rules (Set.toList newRules);*)
    let newVars = Set.union rep.variables (Set.map (fun r -> r.head) newRules) in
      new ContextFreeGrammarBasic.model (Arg.Representation {
		    alphabet = rep.alphabet;
		    variables = newVars;
			  initial = rep.initial;
			  rules = newRules
		  } )


  let rec removeIndirectLeftRecursion map varL (rep:t) = 
    match varL with
    | [] -> new ContextFreeGrammarBasic.model (Arg.Representation {
		          alphabet = rep.alphabet;
		          variables = rep.variables;
			        initial = rep.initial;
			        rules = rep.rules
		        } )
    | var::xs -> 
      let perVarIndirectRemoval map var (rep:t) =
        let perVarProdIndirectRemoval prodHead iVal prodBody rhsValues (rep:t) =
          let results = Set.flatMap (
            fun (jVal, rhsBody) ->
              match jVal with
              | None -> Set.make [{head = prodHead; body = rhsBody}]
              | Some jVal -> 
                if iVal > jVal
                then (
                  let rhsVar = (List.hd rhsBody) in
                  let rhsVarBodies = bodiesOfHead rhsVar rep.rules in
                  let replaceRules = Set.flatMap (fun rhsBody ->
                    if List.length prodBody >= 1
                    then (
                      if List.hd prodBody = rhsVar
                      then Set.make [{head = prodHead; body = rhsBody@(if List.length prodBody >= 1 then List.tl prodBody else prodBody)}]
                      else Set.make []
                    )
                    else Set.make [] 
                  ) rhsVarBodies 
                  in
                  replaceRules
                )
                else  Set.make [{head = prodHead; body = rhsBody}]
          ) rhsValues in
          results
        in
        let iVal = Hashtbl.find_opt map var in
        match iVal with
        | None -> Set.filter (fun {head=h;body=_} -> h=var) rep.rules
        | Some iVal -> (
          let varRules = bodiesOfHead var rep.rules in
          let rhsValues = Set.map (
            fun b -> 
              if List.length b >= 1 
              then (Hashtbl.find_opt map (List.hd b), b)
              else (None, b)
          ) varRules
          in
          Set.flatMap (fun b ->
            let r = perVarProdIndirectRemoval var iVal b rhsValues rep in
            r
          ) varRules)
      in
      let newProds = Set.flatMap (fun v -> perVarIndirectRemoval map v rep) rep.variables in
      let newGrammar = new ContextFreeGrammarBasic.model (Arg.Representation {
         alphabet = rep.alphabet;
         variables = rep.variables;
         initial = rep.initial;
         rules = newProds
       } ) in
      let newGrammar = removeDirectLeftRecursion newGrammar#representation in
      removeIndirectLeftRecursion map xs newGrammar#representation


  let removeLeftRecursion (rep:t) =
    let map = Hashtbl.create (Set.size rep.variables) in
    let leftCornerTest = List.map (fun v -> (v, (Set.toList (leftCorner v rep))) ) (Set.toList rep.variables) in
    let sortedLeftCornerTest = sortLeftCorner leftCornerTest in
    addToMap map (List.map (fun (v,_) -> v) sortedLeftCornerTest);
    let sortedVars = List.map (fun (s,_) -> s) sortedLeftCornerTest in
    let result = removeIndirectLeftRecursion map sortedVars rep in
      {tType = leftRecursionRemovalTransform; grammar = result}
      
  (*left factoring*)
  
  let rec lcp l1 l2 =
    match l1 with
    | [] -> []
    | x1::xs1 -> match l2 with
                | [] -> []
                | x2::xs2 -> if x1=x2 then [x1]@(lcp xs1 xs2) else []
  
  let perVarLCP v rs =
    let rules = Set.filter (fun r -> r.head = v) rs in
    let combos = List.flatten (pairs (Set.toList rules)) in
    let lcpList = List.map ( fun (r1,r2) -> lcp r1.body r2.body) combos in
    let lcpList = List.filter (fun l -> l <> []) lcpList in
      Set.toList (Set.make lcpList) (*Remove repeats*)
  
  let rec sameRuleFactoring nV p rb =
    match p with
    | [] -> [nV]
    | x::xs -> match rb with
              | [] -> []
              | x2::xs2 -> [x2]@sameRuleFactoring nV xs xs2
      
  let rec newRuleFactoring rb p =
    match rb with
    | [] -> []
    | x::xs -> match p with
              | [] -> [x]@newRuleFactoring xs p
              | x2::xs2 -> []@newRuleFactoring xs xs2
      
  let rec ruleHasPrefix r p rb =
    match p with
    | [] ->true
    | x::xs -> match rb with
              |[] -> false
              |x2::xs2 -> if x = x2 then ruleHasPrefix r xs xs2 else false
     
  let rec getSmallestLCP l currSmallest =
    match l with
    | [] -> currSmallest
    | x::xs -> if (x <> [] && List.length x < List.length currSmallest)
               then getSmallestLCP xs x
               else getSmallestLCP xs currSmallest
      
  let rec getBiggestList ll currBiggest =
    match ll with
    | [] -> currBiggest
    | x::xs -> let length = List.length x in
                if length > currBiggest
                then getBiggestList xs length
                else getBiggestList xs currBiggest
      
  let rec createLargeList size =
    match size with
    | 0 -> []
    | _ -> [symb "a"] @ createLargeList (size-1)
      
  let rec perVarFactoring pair allVars (rep:t) = (* pair = ('A', ['a']) *)
    if pair = Set.empty then Set.empty
    else let (x,xs) = Set.cut pair in
      let var = fst x in
      let prefix = snd x in
(*     Printf.printf "prefix = "; print_list prefix; Printf.printf "\n";*)
      let varRules = Set.filter (fun r -> r.head = var) rep.rules in
      let prefixedRules = Set.filter (fun r -> ruleHasPrefix r prefix r.body) varRules in
(*     Printf.printf "prefixedRules = "; Util.println (CFGSyntax.toStringList prefixedRules);*)
      let nonPrefixedRules = Set.filter (fun r -> not (ruleHasPrefix r prefix r.body)) varRules in
(*     Printf.printf "nonPrefixedRules = "; Util.println (CFGSyntax.toStringList nonPrefixedRules);*)
      let newVar = getNewVar allVars in
(*     Printf.printf "newVar = %c\n" newVar;*)
      let newSameHeadRulesSet = Set.map (fun r -> { head = var; body = sameRuleFactoring newVar prefix r.body } ) prefixedRules in
      let newHeadRulesSet = Set.map (fun r -> { head = newVar; body = newRuleFactoring r.body prefix } ) prefixedRules in
      let rules = Set.union nonPrefixedRules (Set.union newSameHeadRulesSet newHeadRulesSet) in
(*     print_rules (Set.toList rules);*)
        Set.union rules (perVarFactoring xs (Set.cons newVar allVars) rep)
  
  let getPerVarLCPResult (rep:t) = 
    let perVarLCPResult = Set.map (fun v -> (v, perVarLCP v rep.rules)) rep.variables in
    let perVarLCPResult = Set.filter (fun (_,l) -> l <> []) perVarLCPResult in
      Set.map ( fun (v,l) -> (v, getSmallestLCP l (createLargeList ((getBiggestList l 0)+1))) ) perVarLCPResult

  let isLeftFactoring (rep:t) =
    Set.map (fun (v,l) -> v) (getPerVarLCPResult rep) <> Set.empty

  let rec leftFactoring (rep:t) =
    let perVarLCPResult = getPerVarLCPResult rep in
(*    Printf.printf "perVarLCPResult = "; Set.iter (fun (v,l) -> Printf.printf "%c, " v; print_list l) perVarLCPResult; Printf.printf "\n";*)
    let variablesToFactorize = Set.map (fun (v,l) -> v) perVarLCPResult in
(*    Printf.printf "Variables to factorize = "; print_list (Set.toList variablesToFactorize); Printf.printf "\n";*)
    let unchangedVariables = Set.diff rep.variables variablesToFactorize in
(*    Printf.printf "Unchanged variables = "; print_list (Set.toList unchangedVariables); Printf.printf "\n";*)
    let unchangedRules = Set.filter (fun {head = h; body = _} -> Set.belongs h unchangedVariables) rep.rules in
    let newRules = perVarFactoring perVarLCPResult rep.variables rep in
    let newVars = Set.map (fun ({head=v;body=_}) -> v ) newRules in
    let newGrammar = new ContextFreeGrammarBasic.model (Arg.Representation {
	      alphabet = rep.alphabet;
	      variables = Set.union rep.variables newVars;
	      initial = rep.initial;
	      rules = Set.union newRules unchangedRules
	    } ) in
    if isLeftFactoring newGrammar#representation 
    then leftFactoring newGrammar#representation 
    else {tType = leftFactoringTransform; grammar = newGrammar}

  let hasEmptyProductions (rep:t) =
    let nullableVars = Set.filter (fun v -> doWordGenerateEmpty [v] rep) rep.variables in
    Set.size nullableVars <> 0

  let removeEmptyProductions2 (rep:t) = 
    let rec combi vars body =
      match body with
      | [] -> Set.make [[]]
      | x::xs -> let res = combi vars xs in
                  (*Printf.printf "Current body symbol is %c\n" x;
                  Printf.printf "res = \n";
                  Set.iter (fun l -> Printf.printf "\t%s\n" (word2str l)) res;*)
                  Set.flatMap (fun v ->
                                (*(if x = v
                                then (
                                  Printf.printf "\tx = v (%c = %c)\n" x v;
                                  Set.iter (fun p -> Printf.printf "\t\t{%s}\n" (word2str p)) (Set.union res (Set.map (fun l -> v::l) res))
                                )
                                else (
                                  Printf.printf "\tx =/= v (%c =/= %c)\n" x v;
                                  Set.iter (fun p -> Printf.printf "\t\t{%s}\n" (word2str p)) (Set.map (fun l -> x::l) res)
                                ));*)
                                if x = v
                                then Set.union res (Set.map (fun l -> v::l) res)
                                else Set.map (fun l -> x::l) res
                  ) vars
    in
    let changeProds vars prod = 
      let {head=h; body=b} = prod in
      if List.length b = 0 then Set.empty
      else (
        let prodBodiesSet = Set.filter (fun p -> List.length p <> 0) (combi vars b) in
        Set.map (fun b -> {head = h; body = b} ) prodBodiesSet
      )
    in
    let nullableVars = Set.filter (fun v -> doWordGenerateEmpty [v] rep) rep.variables in
    if Set.size nullableVars = 0 
    then (
      new ContextFreeGrammarBasic.model (Arg.Representation {
	        alphabet = rep.alphabet;
	        variables = rep.variables;
	        initial = rep.initial;
	        rules = rep.rules
	      })
    )
    else (
      let toChangeProds = Set.filter (fun {head=h;body=b} -> 
                                        Set.exists (
                                          fun v -> List.length b >= 1 && List.mem v b
                                        ) nullableVars
                           ) rep.rules 
      in
      let unchangedProds = Set.filter (
                            fun p -> List.length p.body >= 1
                           ) (Set.diff rep.rules toChangeProds) in
      let newProds = Set.flatMap (changeProds nullableVars) toChangeProds in
(*      Set.iter (fun p -> Printf.printf "{%c;%s}\n" p.head (word2str p.body) ) newProds;*)
(*      if Set.belongs rep.initial nullableVars
      then (
        let newInitial = getNewVar rep.variables in
        let newInitialProds = Set.make [ { head = newInitial; body = []}; { head = newInitial; body = [rep.initial]} ] in
        let newProds = Set.union newInitialProds newProds in
        new ContextFreeGrammarBasic.model (Arg.Representation {
	        alphabet = rep.alphabet;
	        variables = Set.cons newInitial rep.variables;
	        initial = newInitial;
	        rules = Set.union newProds unchangedProds
	      } )
      ) else ( *)
        new ContextFreeGrammarBasic.model (Arg.Representation {
	        alphabet = rep.alphabet;
	        variables = rep.variables;
	        initial = rep.initial;
	        rules = Set.union newProds unchangedProds
	      } (* ) *)
      )
    )
    
  
  let removeEmptyProductions (rep:t) =
    { tType = epsilonRemovalTransform; grammar = removeEmptyProductions2 rep }
  

  let isUnitProd body (rep:t) =
    let rec isUnitProd2 cS cB p =
      match cB with
      | [] -> false
      | x::xs -> if doWordGenerateEmpty cB rep && doWordGenerateEmpty p rep
                  then true
                  else isUnitProd2 x xs (p@[cS])
    in
    let isUnitProdAux r (rep:t) =
      match r with
      | [] -> false
      | x::xs -> isUnitProd2 x xs []
    in
    if (List.length body = 1 && Set.belongs (List.hd body) rep.variables) 
    then true 
    else (
      if List.length body > 1 && List.for_all ( fun c -> Set.belongs c rep.variables ) body
        then isUnitProdAux body rep 
        else false
      )

  let hasUnitProductions (rep:t) =
    Set.size (Set.filter (fun {head = _; body = b} -> isUnitProd b rep ) rep.rules) <> 0


  let rec findUnitPair2 cS cB p (rep:t) =
    match cB with
    | [] -> []
    | x::xs -> if doWordGenerateEmpty cB rep && doWordGenerateEmpty p rep
                then [cS]
                else findUnitPair2 x xs (p@[cS]) rep

  let findUnitPairAux r (rep:t) =
    match r with
    | [] -> []
    | x::xs -> findUnitPair2 x xs [] rep
             
  let rec findUnitPairX origVar var seen (rep:t) =
    if Set.belongs var seen then [] else (
      let rules = bodiesOfHead var rep.rules in
      let results = List.flatten (
                      List.map (fun r -> 
                          if List.length r = 1 && Set.belongs (List.hd r) rep.variables
                          then (
                            if Set.belongs (List.hd r) seen
                            then []@findUnitPairX origVar (List.hd r) (Set.cons var seen) rep
                            else r@findUnitPairX origVar (List.hd r) (Set.cons var seen) rep
                          )
                          else  findUnitPairAux r rep 
                      ) (Set.toList rules)
                    ) 
      in
      results
    )
    
  let findUnitPair var (rep:t) =
    let results = List.map (fun r -> (var, r)) (findUnitPairX var var Set.empty rep) in
    [(var, var)] @ results
(*    (var,(findUnitPairX var Set.empty rep))*)

  (*Used to sort unit pair lists by biggest length to lowest length*)
  let compareUnitPairList l1 l2 =
    if List.length l1 > List.length l2 then -1
    else (if List.length l1 < List.length l2 then 1
    else 0)  
   
  let getNonUnitProductions var (rep:t) = 
    let prods = bodiesOfHead var rep.rules in
(*    Printf.printf "var = %c\n" var;*)
(*    Set.iter (fun p -> Printf.printf "\tIs %c -> %s unit? %b\n" var (word2str p) (isUnitProd p rep)) prods;*)
(*    Printf.printf "\n";*)
    Set.filter (fun p -> not (isUnitProd p rep)) prods

  let removeUnitProductions (rep:t) = 
    let perVarPair pair (rep:t) =
      let (h,b) = pair in
      let nUnitProds = getNonUnitProductions b rep in
(*      Set.iter (fun p -> Printf.printf "%c -> %s\n" h (word2str p)) nUnitProds;*)
      Set.toList (Set.map (fun p -> {head = h; body = p}) nUnitProds)
    in
    let perVar pairs (rep:t) =
      List.flatten (List.map (fun p -> perVarPair p rep) pairs)
    in
    let unitPairs = List.map (fun v -> findUnitPair v rep) (Set.toList rep.variables) in
    (*let unitPairs = List.sort compareUnitPairList unitPairs in*)
    let newProds = List.flatten (
                    List.map (fun l ->
                      perVar l rep
                     ) unitPairs 
                   ) in
    let result = new ContextFreeGrammarBasic.model (Arg.Representation {
	      alphabet = rep.alphabet;
	      variables = rep.variables;
	      initial = rep.initial;
	      rules = Set.make newProds
	    } )
	  in
	    {tType = unitRemovalTransform; grammar = result}

    
    
  let generateRecursiveDescendentParser lang (rep:t) =
    match String.lowercase_ascii lang with
      | "c" -> let parser = new RDParserC.parser in parser#build rep
      | "ocaml" -> let parser = new RDParserOCaml.parser in parser#build rep
      | "java" -> let parser = new RDParserJava.parser in parser#build rep
      | _ -> "Language " ^ lang ^ " is not supported.\n"


  let transformToLL1 (rep:t) =
    let transform1 = {tType = epsilonRemovalTransform; grammar = (removeEmptyProductions rep).grammar} in
    let transform2 = {tType = unitRemovalTransform; grammar = (removeUnitProductions transform1.grammar#representation).grammar} in
    let cleanResult = clean transform2.grammar#representation in
    let transform3 = {tType = cleanProductiveTransform; grammar = (List.nth cleanResult 0).grammar} in
    let transform4 = {tType = cleanAccessibleTransform; grammar = (List.nth cleanResult 1).grammar} in
    let transform5 = {tType = leftRecursionRemovalTransform; grammar = (removeLeftRecursion transform4.grammar#representation).grammar} in
    let transform6 = {tType = leftFactoringTransform; grammar = (leftFactoring transform5.grammar#representation).grammar} in
    [transform1; transform2; transform3; transform4; transform5; transform6]
  

  class model (arg: t Arg.alternatives) =
    object(self) inherit ContextFreeGrammarBasic.model arg as super
    
    method isSimplified = simplified
    method rdparserOpts = [ "OCaml"; "C"; "Java"; "Rust" ]
    method toggleSimplified = Printf.printf "simplified is %b toggling to %b\n" simplified (not simplified);
                              simplified <- not simplified
    
    method follow testSymbol = follow testSymbol simplified self#representation
    method lookahead rule = lookahead rule simplified self#representation
    method isLL1 = isLL1 simplified self#representation
    method isLeftRecursive = isLeftRecursive self#representation
    method createParsingTable = createParsingTable simplified self#representation
    method hasParsingTableConflict = hasParsingTableConflict simplified self#representation
    method acceptZ w = acceptZ w simplified self#representation
    method productiveSymbols = productiveSymbols self#representation
    method accessibleSymbols = accessibleSymbols self#representation
    method productiveRewrite = productiveGrammarRewrite self#representation
    method accessibleRewrite = accessibleGrammarRewrite self#representation
    method clean = clean self#representation
    method isFullyProductive = isCFGFullyProductive self#representation
    method isFullyAccessible = isCFGFullyAccessible self#representation
    method isClean = isClean self#representation
    method removeLeftRecursion = removeLeftRecursion self#representation
    method removeDirectLeftRecursion = removeDirectLeftRecursion self#representation
    method leftFactoring = leftFactoring self#representation
    method isLeftFactoring = isLeftFactoring self#representation
    method leftCorner s = leftCorner s self#representation
    method hasEmptyProductions = hasEmptyProductions self#representation
    method removeEmptyProductions = removeEmptyProductions self#representation
    method hasUnitProductions = hasUnitProductions self#representation
    method removeUnitProductions = removeUnitProductions self#representation
    method generateRecursiveDescendentParser pLang = generateRecursiveDescendentParser pLang self#representation
    method transformToLL1 = transformToLL1 self#representation
  end
end


# 3 "src/ContextFreeGrammarLR.ml"
(*
 * ContextFreeGrammarLR.ml
 *
 * This file is part of the OCamlFlat library
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
 *  Written by Bernardo Sousa (br)
 *)

(*
 * ChangeLog:
 * sep/2022 (br) - Bug fixes.
 * july/2022 (br) - Added step-by-step table creation.
 * may/2022 (br) - Most of the LR theory implemented.
 * mar/2022 (amd/br) - Skeleton.
 *)

(*
 * Description: A very simple parser for CFG syntax.
 *)
 
open BasicTypes
open ContextFreeGrammarBasic  

module LRAux =
struct
	let word s = str2word s
		
	let rec nats n = if n = 0 then [] else nats(n-1) @ [string_of_int (n-1)]
	
	let rec pop n l (*uses reverse stack and removes n heads from stack *)= 
		match l with
		| [] -> []
		| x::xs -> if(n>0) then pop (n-1) xs else x::pop n xs  
	
	
	let getTail l = (*remove head from list *)
		match l with
		| [] -> []
		|_::xs -> xs
		
	let rec rev l =
		match l with
		| [] -> []
		| x::xs -> (rev xs) @ x
	
	
end	

module LR0Grammar =
struct
	open LRAux
	type t = ContextFreeGrammarBasic.t

	type lr0Item = {head:symbol; body1:symbol list; body2:symbol list}		
	type lr0State = lr0Item set
	type lr0Diagram = lr0State set * (lr0State * symbol * lr0State ) set
	
	type stateName = string
	
	type lr0StateId = stateName * lr0State 
	type lr0DiagramId = lr0StateId set * (lr0StateId * symbol * lr0StateId ) set
	
	type lr0Action = Accept | Shift | Reduce of rule 
	type lr0TableEntry = stateName * (symbol * stateName) set * lr0Action
	type lr0Table = lr0TableEntry set
	
	let rule2Item (rule: rule) : lr0Item = (* converte uma regra num item novo, com o ponto á esquerda do corpo desse item *)
		{head = rule.head; body1 = []; body2 = rule.body} 
		
	
	let kernelAdvanceItem {head=h; body1=b1; body2=b2} = (* função auxiliar para avançar o ponto de um item em um simbolo para o nucleo do proximo estado. Ex: A ->.ab para A -> a.b *)
		match b2 with
		| [] -> Error.fatal "kernelAdvanceItem: Este caso nem deve ser alcançavel"
		| x::xs -> {head = h; body1 = b1 @ [x]; body2 = xs} 
	
	

	
		
	let getDirector {head=_; body1=_; body2=b2} = (* obtem o simbolo diretor de um item *)
		match b2 with 
			| [] -> epsilon (* epsilon, aka no symbol *) 
			| x::_ -> x	
			
			
		
			
	let getDirectors state = (* Aplica a função getDirector a todos os itens de um dado estado*)
		Set.filter (fun d-> d <> epsilon)(Set.map getDirector state)
	
		
		
	let getRulesWithThisHead rules director = (* recebe o conjunto de regras da gramática e filtra esse conjunto para obter as regras cuja cabeça tem aquele simbolo diretor *)
		Set.filter (fun {head = h; body =_} -> h = director) rules 
		
	
	let diagramsJoin2 (s0,t0) (s1,t1) = (Set.union s0 s1, Set.union t0 t1) (* juntar dois diagramas LR0 para obter um diagrama LR0 resultante da união *)	
	
	let rec diagramsJoinList l : lr0Diagram = (* Juntar um conjunto de diagramas para produzir o diagrama LR0, cada diagrama desta lista corresponde a um estado rescrito como diagrama *)
		match l with
		| [] -> (Set.empty , Set.empty) 
		| d::ds -> diagramsJoin2 d (diagramsJoinList ds)
	
	
	let isNextSymbolNotAVariable {head=h; body1=b1; body2=b2} (cfg:t)=
		if(List.length b2 = 0) then true
		else
			if(Set.belongs (List.hd b2) cfg.variables) then false else true
	
	let isCompleteItem {head=h; body1=b1; body2=b2} =
		b2 = []
	
	let isStateInConflict lr0State cfg = 
		let completeItems = Set.filter(isCompleteItem) lr0State in
		if(Set.size completeItems < 1 ) then false
		else if(Set.size completeItems > 1 ) then true
		else
			let itemsProneToConflict = Set.filter(fun it -> isNextSymbolNotAVariable it cfg) lr0State in
			if(Set.size itemsProneToConflict > 1) then true else false
	
	let makeLR0DiagramId diagram : lr0DiagramId (* Cria etiquetas para os estados e os mesmos estados contidos nas transições do diagrama*) =
		let (states,transitions) = diagram in
		let dictionary = List.combine (Set.toList states) (nats (Set.size states)) in
		let statesId = Set.map (fun s -> (List.assoc s dictionary,s) ) states in
		let transitionsId = Set.map (fun (a,b,c) -> ((List.assoc a dictionary, a), b,(List.assoc c dictionary, c))) transitions in
			(statesId, transitionsId)
	
	
	let makeLR0TableEntry (id, lr0State) (cfg:t) transitions = 
		let stateTransitions = Set.filter (fun ((a,_),_,_)-> a = id) transitions in
			if Set.size stateTransitions = 0 then
				let {head = h;body1 = b1;body2 = b2} = List.hd (Set.toList lr0State) in
					if h = cfg.initial then 
						(id,Set.empty,Accept)
					else
						(id,Set.empty,Reduce ({head = h;body = b1}))			
			else  
				let nextShifts = Set.map (fun (a,b,(cId,c)) -> (b,cId)) stateTransitions in
					(id, nextShifts, Shift)
		
	(* falta uma função para aceitar/recusar palavra usando a tabela *)
	
	(*pre: isLR0 cfg *)
	let makeLR0Table (labeledDiagram:lr0DiagramId) cfg : lr0Table = (* recebe um diagrama numerado e constroi a tabela de parsing a partir das transições *) 
		let (statesId, transitionsId) = labeledDiagram in
			Set.map (fun s -> makeLR0TableEntry s cfg transitionsId) statesId
	
	
	let startRules (cfg: t) =
		let initial = cfg.initial in
		let rules = cfg.rules in
			Set.filter (fun {head=h; body=_} -> h = initial) rules
			
		
		
	let lr0StateClosureStep (cfg: t) currentItems = (* Create items for current directors *)
		let directors = getDirectors currentItems in
		let varDirectors = Set.inter directors cfg.variables in
		let newRules = Set.flatMap (fun d -> getRulesWithThisHead cfg.rules d) varDirectors in
		let newItems = Set.map rule2Item newRules in
			Set.union currentItems newItems 
		
		
	let rec lr0StateClosure cfg currentItems : lr0State = (* Create all items for a singular state *)
		let next = lr0StateClosureStep cfg currentItems in
		let next2 = Set.union currentItems next in
			if Set.size next2 = Set.size currentItems then next2
			else lr0StateClosure cfg next2


		
	let makeSingularNextLR0Diagram (cfg:t) prevState symbol : lr0Diagram = (* Creates a diagram containing only 1 state using the previous state and the transition symbol*)
		let items4Kernel = Set.filter (fun it -> getDirector it = symbol) prevState in (* falta avançar o ponto *)
		let kernel = Set.map (kernelAdvanceItem) items4Kernel in
		let closure = lr0StateClosure cfg kernel in
			(Set.make [prevState; closure], Set.make [(prevState ,symbol , closure )])
					

	
	let makeNextLR0Diagram (cfg:t) prevState : lr0Diagram = (* For each director symbol on the previous state, create a diagram and join all obtained diagrams into a single diagram*)
		let dirs = getDirectors prevState in
		let diagrams = Set.map (fun d -> makeSingularNextLR0Diagram cfg prevState d) dirs in
			diagramsJoinList (Set.toList diagrams) 

			
		
	let makeNextLR0DiagramAll (cfg:t) states : lr0Diagram = (* build the diagram using the initial state, then use the makeNextLR0Diagram function to calculate all states obtainable from the initial state*)
		let diagrams = Set.map (fun s -> makeNextLR0Diagram cfg s) states in
			diagramsJoinList (Set.toList diagrams)
			
	
	let makeFirstLR0Diagram (cfg:t) : lr0Diagram = (* O primeiro estado tem um procedimento de criação um pouco differente *) 
		let kernel = Set.map rule2Item (startRules cfg) in
		let closure = lr0StateClosure cfg kernel in
		(Set.make [closure], Set.empty)
		
		(*Set.make [closure] (* apesar de ser criado um par, nesta função só se cria o conjunto de items, o conjunto vazio das transições vazias é criado no makeLR0Diagram *) *)
		

	
	let rec makeLR0DiagramX (cfg:t) diagram = (* função auxiliar que irá produzir o diagrama LR0 *)
		let (states,transitions) : lr0Diagram = diagram in 
		let next = makeNextLR0DiagramAll cfg states in
		let next2 = diagramsJoin2 next (states,transitions) in
		let (states2,transitions2) = next2 in
			if Set.size states = Set.size states2 && Set.size transitions = Set.size transitions2 then next2
			else makeLR0DiagramX cfg next2 
					 

	let makeLR0Diagram (cfg:t) = makeLR0DiagramX cfg (makeFirstLR0Diagram cfg)  (* ponto de partida na construlão do diagrama LR0 *)
	
	(*
	type stackEntry = StateEntry of stateName | SymbolEntry of symbol
	
	let getState e =
		match e with
		| StateEntry s -> s
		| _ -> Error.fatal "getState: desnecessário" 
		
	let getSymbol s =
		match s with
		| SymbolEntry s -> s
		| _ -> Error.fatal "getState: desnecessário" 
	*)	
	let rec parseOperationV2 lr0Table word revStack (cfg:t) = 
		let currentState = int_of_string (List.hd revStack) in 
		let (id,shifts,action) = Set.nth lr0Table currentState in (* get corresponding table entry *)	
		match action with
		| Shift -> 
			begin
				match word with
				| [] -> false
				| s::_ -> 
					if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
						let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
							if(Set.size targetShifts = 0) then false
							(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
							(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
							else
								let (nextSymbol,nextState) = Set.nth targetShifts 0 in
								let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
									parseOperationV2 lr0Table (getTail word) nextRevStack cfg
					else
						Error.fatal "singleParseOperation: este simbolo não pertence ao alfabeto desta gramatica"
			end
		| Accept -> 
			word = [dollar]	
		| Reduce({head = h;body = b}) -> 
			let popNumber = List.length b in
			let nextRevStack = pop (popNumber*2) revStack in
			let wordWithAddedHead = [h] @ word in
				parseOperationV2 lr0Table (wordWithAddedHead) nextRevStack cfg (*Add the variable, aka head of the reduction rule, to the word being processed *)
					
	
	(* pre: isLR0 cfg 
	   pre: isWordValid word cfg *)
	let acceptWordLR0V2 (word:symbol list) cfg : bool = 
		let lr0Table = makeLR0Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg in
		let revStack = ["0"] in (*char list due to mix of numbers and symbols *) 
			parseOperationV2 lr0Table (word @ [dollar]) revStack cfg	
		

	(* let nextStack = [StateEntry nextState; StateSymbol nextSymbol] @ stack in *)
	
	let rec parseOperation lr0Table word stateStack symbolStack (cfg:t) = 
		let currentState = int_of_string (List.hd stateStack) in 
		let (id,shifts,action) = Set.nth lr0Table currentState in (* get corresponding table entry *)	
		match action with
		| Shift -> 
			begin
				match word with
				| [] -> false
				| s::_ -> 
					if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
						let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
							if(Set.size targetShifts = 0) then false
							(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
							(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
							else
								let (nextSymbol,nextState) = Set.nth targetShifts 0 in
								let nextStateStack = [nextState] @ stateStack in
								let nextSymbolStack = [nextSymbol] @ symbolStack in
									parseOperation lr0Table (getTail word) nextStateStack nextSymbolStack cfg
					else
						Error.fatal "singleParseOperation: este simbolo não pertence ao alfabeto desta gramatica"
			end
		| Accept -> 
			word = [dollar]	
		| Reduce({head = h;body = b}) -> 
			let popNumber = List.length b in
			let nextStateStack = (pop popNumber stateStack) in
			let nextSymbolStack = (pop popNumber symbolStack) in
			let wordWithAddedHead = [h] @ word in
				parseOperation lr0Table (wordWithAddedHead) nextStateStack nextSymbolStack cfg (*Add the variable, aka head of the reduction rule, to the word being processed *)
					
	
	(* pre: isLR0 cfg 
	   pre: isWordValid word cfg *)
	let acceptWordLR0 (word:symbol list) cfg : bool = 
		let lr0Table = makeLR0Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
			parseOperation lr0Table (word @ [dollar]) stateRevStack symbolRevStack cfg
			
	(* Added functions to provide a step-by step LR0 visualization of accepting *)

	type lr0TableStep = symbol list * string list * symbol list * lr0Table * bool
	
	let acceptWordLR0Init (word:symbol list) cfg : lr0TableStep =
		let lr0Table = makeLR0Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
		let valid = true in
		let initStep = ((word @ [dollar]),stateRevStack,symbolRevStack,lr0Table,valid) in
			initStep
	
	let parseStepLR0Operation (step:lr0TableStep) (cfg:t) : lr0TableStep = 
		let (word, stateStack, symbolStack, lr0Table, valid) = step in
		let currentState = int_of_string (List.hd stateStack) in 
		let (id,shifts,action) = Set.nth lr0Table currentState in (* get corresponding table entry *)	
		match action with
		| Shift -> 
			begin
				match word with
				| [] -> (word, stateStack, symbolStack, lr0Table, false)
				| s::_ -> 
					if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
						let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
							if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, lr0Table, false)
							(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
							(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
							else
								let (nextSymbol,nextState) = Set.nth targetShifts 0 in
								let nextStateStack = [nextState] @ stateStack in
								let nextSymbolStack = [nextSymbol] @ symbolStack in
								let nextStep = ((getTail word), nextStateStack, nextSymbolStack, lr0Table, valid) in
									nextStep
					else
						Error.fatal "singleParseOperation: este simbolo não pertence ao alfabeto desta gramatica"
			end
		| Accept -> 
			if (word = [dollar]) then
					((getTail word), stateStack, symbolStack, lr0Table, valid)
				else 
					((getTail word), stateStack, symbolStack, lr0Table, false)
		| Reduce({head = h;body = b}) -> 
			let popNumber = List.length b in
			let nextStateStack = (pop popNumber stateStack) in
			let nextSymbolStack = (pop popNumber symbolStack) in
			let wordWithAddedHead = [h] @ word in
			let nextStep = (wordWithAddedHead, nextStateStack, nextSymbolStack, lr0Table, valid) in
				nextStep
		
	
	
	
		
	let acceptWordLR0Step (step:lr0TableStep) cfg : lr0TableStep = 
			parseStepLR0Operation step cfg
			
			
	(* updated acceptStep, you can use the previous version if you want to split the stack contaning both state and symbols*)
	
	type truelr0TableStep = symbol list * string list * lr0Table * string
	
	let acceptWordLR0InitV2 (word:symbol list) cfg : truelr0TableStep =
		let lr0Table = makeLR0Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg in
		let revStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let valid = "Ongoing" in
		let initStep = ((word @ [dollar]),revStack,lr0Table,valid) in
			initStep
	
	let parseStepLR0OperationV2 (step:truelr0TableStep) (cfg:t) : truelr0TableStep = 
		let (word, revStack, lr0Table, valid) = step in (* if you want to print use this: print_string (List.hd revStack ^ "\n"); *)
		let currentState = int_of_string (List.hd revStack) in 
		let (id,shifts,action) = Set.nth lr0Table currentState in (* get corresponding table entry *)	
		match action with
		| Shift -> 
			begin
				match word with
				| [] -> (word, revStack, lr0Table, "Rejeitada")
				| s::_ -> 
					if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
						let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
							if(Set.size targetShifts = 0) then (word, revStack, lr0Table, "Rejeitada")
							(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
							(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
							else
								let (nextSymbol,nextState) = Set.nth targetShifts 0 in
								let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
								let nextStep = ((getTail word), nextRevStack, lr0Table, valid) in
									nextStep
					else
						(word, revStack, lr0Table, "Rejeitada")
			end
		| Accept -> 
			if (word = [dollar]) then
					((getTail word), [symb2str cfg.initial], lr0Table, "Aceite")
				else 
					((word), revStack, lr0Table, "Rejeitada")
		| Reduce({head = h;body = b}) -> 
			let popNumber = List.length b in
			let nextRevStack = pop (popNumber*2) revStack in
			let wordWithAddedHead = [h] @ word in
			let nextStep = (wordWithAddedHead, nextRevStack, lr0Table, valid) in
				nextStep
	
		
	let acceptWordLR0StepV2 (step:truelr0TableStep) cfg : truelr0TableStep = 
			parseStepLR0OperationV2 step cfg
			
		
	let isLR0 cfg = (* verificar se a gramatica é lr0, ou seja, em todos os estados com items completos, não existem simbolos não terminais á direita de um ponto (item não completo *)
		let (states,transitions) = makeLR0Diagram cfg in
		let conflictItemStates = Set.filter(fun s -> isStateInConflict s cfg) states in
			if(Set.size conflictItemStates > 0) then false else true
	
	let getLR0DiagramId cfg : lr0DiagramId =
		makeLR0DiagramId (makeLR0Diagram cfg)
		
	let getLR0Table cfg : lr0Table =
		makeLR0Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg 
		
	(* -------extended LR0 for clarity----------- Allows LR0 Tables to display multiple actions in each state line.*)	
	
	let isCompleteLR0Item (it:lr0Item) =
		it.body2 = []

	let countCompleteLR0Items lr0State = 
		let completeItems = Set.filter(isCompleteLR0Item) lr0State in
			Set.size completeItems	
	
	let buildLR0ReductionActionsForOne item cfg = (* Warning, input must only contain complete items *)
		if(isCompleteItem item) then
			Reduce ({head = item.head;body = item.body1})
		else
			Shift (* this should not happen *)

	let buildLR0ReductionActions completeItems cfg = 
		Set.map(fun it -> (buildLR0ReductionActionsForOne it cfg) ) completeItems
	
			
	let buildLR0MixedActionsForOne item cfg = 
		if(isCompleteItem item) then
			Reduce ({head = item.head;body = item.body1})
		else
			Shift
	

	let buildLR0MixedActions (items:lr0State) cfg =
		Set.map(fun it -> (buildLR0MixedActionsForOne it cfg) ) items
	
	
	
	
	type lr0TableEntryExt = stateName * (symbol * stateName) set * lr0Action set
	type lr0TableExt = lr0TableEntryExt set
		
	let makeLR0TableEntryExt (id, lr0State) (cfg:t) transitions = 
		let stateTransitions = Set.filter (fun ((a,_),_,_)-> a = id) transitions in
			if Set.size stateTransitions = 0 then
				let {head = h;body1 = b1;body2 = b2} = List.hd (Set.toList lr0State) in
					if h = cfg.initial then 
							(id,Set.empty,Set.make [Accept])
					else
						let lr0Actions : lr0Action set = buildLR0ReductionActions lr0State cfg in
							(id,Set.empty, lr0Actions)	
			else  
				let nextShifts = Set.map (fun (a,b,(cId,c)) -> (b,cId)) stateTransitions in
					if(countCompleteLR0Items lr0State = 0) then (* Não existem reducoes *)
							(id, nextShifts, Set.make[Shift])
					else (* Existem reducoes e transferencias *)
						let lr0Actions = buildLR0MixedActions lr0State cfg in
							(id, nextShifts, lr0Actions)	
		

	let makeLR0TableExt (labeledDiagram:lr0DiagramId) cfg : lr0TableExt = (* recebe um diagrama numerado e constroi a tabela de parsing a partir das transições *) 
		let (statesId, transitionsId) = labeledDiagram in
			Set.map (fun s -> makeLR0TableEntryExt s cfg transitionsId) statesId
			
	let getLR0TableExt cfg : lr0TableExt =
		makeLR0TableExt (makeLR0DiagramId (makeLR0Diagram cfg)) cfg 

		
end		
	(* ----- SLR1 -----*)
module SLR1Grammar =
struct
	open LRAux
	open LR0Grammar
	type t = ContextFreeGrammarBasic.t
	
(*
	type lr0Item = LR0Grammar.lr0Item		
	type lr0State = LR0Grammar.lr0State	
	type lr0Diagram = LR0Grammar.lr0Diagram	
	
	type stateName = LR0Grammar.stateName
	
	type lr0StateId = LR0Grammar.lr0StateId	
	type lr0DiagramId = LR0Grammar.lr0DiagramId		
*)
	
	type slr1Action = Accept | Shift | Reduce of rule 
	type slr1TableEntry = stateName * (symbol * stateName) set * (symbol * slr1Action set ) set
	type slr1Table = slr1TableEntry set
	
	let kernelAdvanceItem {head=h; body1=b1; body2=b2} = (* função auxiliar para avançar o ponto de um item em um simbolo para o nucleo do proximo estado. Ex: A ->.ab para A -> a.b *)
		match b2 with
		| [] -> Error.fatal "kernelAdvanceItem: Este caso nem deve ser alcançavel"
		| x::xs -> {head = h; body1 = b1 @ [x]; body2 = xs} 
	
	let getNextSymbolForLR0Item (it:lr0Item)  =
		match it.body2 with
		| [] -> epsilon
		| x::xs -> x
	
	(*
	let follow w = (* Injected follow to test SLR1 grammars*)
		match w with
		| [] -> Set.make [dollar] (* Não deve acontecer*)
		| x::xs -> 
			if(x = symb "A") then Set.make [symb "c"]
			else if(x = symb "B") then Set.make [symb "d"]
			else if(x = symb "X") then Set.make [dollar]
			else Set.make [dollar]
    *)
			
	let followSetForSLR1Item it cfg =
		ContextFreeGrammarBasic.follow it.head false cfg
		
	let isCompleteLR0Item (it:lr0Item) =
		it.body2 = []

	let countCompleteLR0Items lr0State = 
		let completeItems = Set.filter(isCompleteLR0Item) lr0State in
			Set.size completeItems	
			
	let buildSLR1ReductionActionsForOne completeItems symbol cfg = (* Warning, input must only contain complete items *)
		let reductionItems = Set.filter(fun it -> Set.belongs symbol (followSetForSLR1Item it cfg)) completeItems in
			Set.map (fun it -> Reduce ({head = it.head;body = it.body1}) ) reductionItems	
			


	let buildSLR1ReductionActions completeItems alphabet cfg= 
		Set.map(fun symbol -> (symbol, buildSLR1ReductionActionsForOne completeItems symbol cfg) ) alphabet
	
	
	
	let buildSLR1ShiftActionsForOne items symbol : slr1Action set = 
		let shiftItems = Set.filter(fun it -> (getNextSymbolForLR0Item it) = symbol) items in
		if(Set.size shiftItems > 0) then
			Set.make [Shift]
		else
			Set.empty
			


	let buildSLR1ShiftActions completeItems alphabet = 
		Set.map(fun symbol -> (symbol, buildSLR1ShiftActionsForOne completeItems symbol) ) alphabet
	
			
	let buildSLR1MixedActionsForOne items symbol cfg= 
		let reductionItems = Set.filter(fun it -> (Set.belongs symbol (followSetForSLR1Item it cfg)) && isCompleteLR0Item it) items in
		let fixedreductionItems = Set.filter (fun it-> it.head != cfg.initial) reductionItems in (* Porque este fixed? R: Porque os items de accept podem ser interpretados como reduções. logo vamos ter de separar estes items *)
		let acceptItems = Set.filter (fun it -> it.head = cfg.initial && symbol = dollar && isCompleteLR0Item it && (Set.belongs it fixedreductionItems) = false) items in
		let shiftItems = Set.filter(fun it -> (getNextSymbolForLR0Item it) = symbol) items in
		let reductionEntries = Set.map (fun it -> Reduce ({head = it.head;body = it.body1}) ) fixedreductionItems in
		
		if(Set.size acceptItems > 0) then
			if(Set.size shiftItems > 0) then
				Set.union (Set.union (Set.make [Shift]) reductionEntries) (Set.make [Accept])
			else
				Set.union reductionEntries (Set.make [Accept])
		else	
			if(Set.size shiftItems > 0) then
				Set.union (Set.make [Shift]) reductionEntries
			else
				reductionEntries

	let buildSLR1MixedActions (items:lr0State) alphabet cfg= (* True build function - prototype *) (* transformar na forma do buildLR1ReductionActions *)
		Set.map(fun symbol -> (symbol, buildSLR1MixedActionsForOne items symbol cfg) ) alphabet
	
			
			
	let makeSLR1TableEntry (id, lr0State) (cfg:t) transitions = 
		let stateTransitions = Set.filter (fun ((a,_),_,_)-> a = id) transitions in
			if Set.size stateTransitions = 0 then
				let {head = h;body1 = b1;body2 = b2} = List.hd (Set.toList lr0State) in
					if h = cfg.initial then 
						let slr1Actions : (symbol * slr1Action set) set = Set.make [dollar,Set.make [Accept]] in
							(id,Set.empty,slr1Actions)
					else
						let completeAlphabet = Set.add dollar cfg.alphabet in (* Se o $, final da palavra, não estiver no alfabeto da gramática *)
						let slr1Actions : (symbol * slr1Action set) set = buildSLR1ReductionActions lr0State completeAlphabet cfg in
							(id,Set.empty, slr1Actions)	
			else  
				let nextShifts = Set.map (fun (a,b,(cId,c)) -> (b,cId)) stateTransitions in
					if(countCompleteLR0Items lr0State = 0) then (* Não existem reducoes *)
						let slr1Actions = buildSLR1ShiftActions lr0State cfg.alphabet in
							(id, nextShifts, slr1Actions)
					else (* Existem reducoes e transferencias *)
						let completeAlphabet = Set.add dollar cfg.alphabet in (* Se o $, final da palavra, não estiver no alfabeto da gramática *)
						let slr1Actions = buildSLR1MixedActions lr0State completeAlphabet cfg in
							(id, nextShifts, slr1Actions)	
		
	
	(*pre: isLR1 cfg *)

	let makeSLR1Table (labeledDiagram:lr0DiagramId) cfg : slr1Table = (* recebe um diagrama numerado e constroi a tabela de parsing a partir das transições *) 
		let (statesId, transitionsId) = labeledDiagram in
			Set.map (fun s -> makeSLR1TableEntry s cfg transitionsId) statesId
			
			
		
		
	let rec parseOperationSLR1 slr1Table word stateStack symbolStack (cfg:t) = 
		let currentState = int_of_string(List.hd stateStack) in 
		let (id,shifts,actionSet) = Set.nth slr1Table currentState in (* get corresponding table entry *)
		let topSymbol = List.nth word 0 in
			if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
				let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
					if(Set.size targetShifts = 0) then false
					else
						let (nextSymbol,nextState) = Set.nth targetShifts 0 in
						let nextStateStack = [nextState] @ stateStack in
						let nextSymbolStack = [nextSymbol] @ symbolStack in
							parseOperationSLR1 slr1Table (getTail word) nextStateStack nextSymbolStack cfg
			else 
				let peekedSymbol = List.nth word 0 in
				let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
				let nEntries = Set.size peekedsymbolAndActions in
					if nEntries = 0 then 
						false
					else if nEntries > 1 then
						Error.fatal "ParseOperationLR1: conflito"
					else
						let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
						let action = Set.hd actions in
						match action with
						| Shift -> 
							begin
								match word with
								| [] -> false
								| s::_ -> 
									if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
										let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
											if(Set.size targetShifts = 0) then false
											(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
											(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
											else
												let (nextSymbol,nextState) = Set.nth targetShifts 0 in
												let nextStateStack = [nextState] @ stateStack in
												let nextSymbolStack = [nextSymbol] @ symbolStack in
													parseOperationSLR1 slr1Table (getTail word) nextStateStack nextSymbolStack cfg
									else
										Error.fatal "ParseOperationSLR1: este simbolo não pertence ao alfabeto desta gramatica"
							end
						| Accept -> 
							word = [dollar]	
						| Reduce({head = h;body = b}) -> 
							let popNumber = List.length b in
							let nextStateStack = (pop popNumber stateStack) in
							let nextSymbolStack = (pop popNumber symbolStack) in
							let wordWithAddedHead = [h] @ word in
								parseOperationSLR1 slr1Table (wordWithAddedHead) nextStateStack nextSymbolStack cfg (*Add the variable, aka head of the reduction rule, to the word being processed *)
			
	(* pre: isSLR1 cfg 
	   pre: isWordValid word cfg *)
	let acceptWordSLR1 (word:symbol list) cfg : bool = 
		let slr1Table = makeSLR1Table (LR0Grammar.makeLR0DiagramId (LR0Grammar.makeLR0Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
			parseOperationSLR1 slr1Table (word @ [dollar]) stateRevStack symbolRevStack cfg	
			
	(* Added functions to provide a step-by step SLR1 visualization of accepting *)

	type slr1TableStep = symbol list * string list * symbol list * slr1Table * bool
	
	let acceptWordSLR1Init (word:symbol list) cfg : slr1TableStep =
		let slr1Table = makeSLR1Table (LR0Grammar.makeLR0DiagramId (LR0Grammar.makeLR0Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
		let valid = true in
		let initStep = ((word @ [dollar]),stateRevStack,symbolRevStack,slr1Table,valid) in
			initStep
	
	let parseStepSLR1Operation (step:slr1TableStep) (cfg:t) : slr1TableStep = 
		let (word, stateStack, symbolStack, slr1Table, valid) = step in
		let currentState = int_of_string(List.hd stateStack) in 
		let (id,shifts,actionSet) = Set.nth slr1Table currentState in (* get corresponding table entry *)
		let topSymbol = List.nth word 0 in
			if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
				let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
					if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, slr1Table, false)
					else
						let (nextSymbol,nextState) = Set.nth targetShifts 0 in
						let nextStateStack = [nextState] @ stateStack in
						let nextSymbolStack = [nextSymbol] @ symbolStack in
						let nextStep = ((getTail word), nextStateStack, nextSymbolStack, slr1Table, valid) in
							nextStep
			else 
				let peekedSymbol = List.nth word 0 in
				let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
				let nEntries = Set.size peekedsymbolAndActions in
					if nEntries = 0 then 
						(word, stateStack, symbolStack, slr1Table, false)
					else if nEntries > 1 then
						Error.fatal "parseStepSLR1Operation: conflito"
					else
						let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
						let action = Set.hd actions in
						match action with
						| Shift -> 
							begin
								match word with
								| [] -> (word, stateStack, symbolStack, slr1Table, false)
								| s::_ -> 
									if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
										let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
											if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, slr1Table, false)
											(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
											(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
											else
												let (nextSymbol,nextState) = Set.nth targetShifts 0 in
												let nextStateStack = [nextState] @ stateStack in
												let nextSymbolStack = [nextSymbol] @ symbolStack in
												let nextStep = ((getTail word), nextStateStack, nextSymbolStack, slr1Table, valid) in
													nextStep
									else
										Error.fatal "parseStepSLR1Operation: este simbolo não pertence ao alfabeto desta gramatica"
							end
						| Accept -> 
							if (word = [dollar]) then
								((getTail word), stateStack, symbolStack, slr1Table, valid)
							else 
								((getTail word), stateStack, symbolStack, slr1Table, false)
						| Reduce({head = h;body = b}) -> 
							let popNumber = List.length b in
							let nextStateStack = (pop popNumber stateStack) in
							let nextSymbolStack = (pop popNumber symbolStack) in
							let wordWithAddedHead = [h] @ word in
							let nextStep = (wordWithAddedHead, nextStateStack, nextSymbolStack, slr1Table, valid) in
								nextStep
		
	
	
	
		
	let acceptWordSLR1Step (step:slr1TableStep) cfg : slr1TableStep = 
			parseStepSLR1Operation step cfg
					
			
	(* updated accept *)
	type trueslr1TableStep = symbol list * string list * slr1Table * string
	
	let acceptWordSLR1InitV2 (word:symbol list) cfg : trueslr1TableStep =
		let slr1Table = makeSLR1Table (LR0Grammar.makeLR0DiagramId (LR0Grammar.makeLR0Diagram cfg)) cfg in
		let revStack = ["0"] in 
		let valid = "Ongoing" in
		let initStep = ((word @ [dollar]),revStack,slr1Table,valid) in
			initStep
	
	let parseStepSLR1OperationV2 (step:trueslr1TableStep) (cfg:t) : trueslr1TableStep = 
		let (word, revStack, slr1Table, valid) = step in
		(*print_string (List.hd revStack ^ "\n");
		print_string (valid); *)
		let currentState = int_of_string(List.hd revStack) in 
		let (id,shifts,actionSet) = Set.nth slr1Table currentState in (* get corresponding table entry *)
		(* print_string ((word2str word) ^ "\n"); *)
		if(List.length word = 0) then
			(word, revStack, slr1Table, "Rejeitada")
		else
			let topSymbol = List.nth word 0 in
				if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
					let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
						if(Set.size targetShifts = 0) then (word, revStack, slr1Table, "Rejeitada")
						else
							let (nextSymbol,nextState) = Set.nth targetShifts 0 in
							let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
							let nextStep = ((getTail word), nextRevStack, slr1Table, valid) in
								nextStep
				else 
					let peekedSymbol = List.nth word 0 in
					let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
					let nEntries = Set.size peekedsymbolAndActions in
						if nEntries = 0 then 
							(word, revStack, slr1Table, "Rejeitada")
						else if nEntries > 1 then
							(word, revStack, slr1Table, "Conflito")
						else
							let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
							(* Durante o accept, se encontrar um conflito, para imediatamente e retorna "... Conflito ..." AMD *)
							if Set.size actions > 1 then (* NEW *)
								(word, revStack, slr1Table, "Conflito")
							else
						
							let action = Set.hd actions in
							match action with
							| Shift -> 
								begin
									match word with
									| [] -> (word, revStack, slr1Table, "Rejeitada")
									| s::_ -> 
										if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
											let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
												if(Set.size targetShifts = 0) then (word, revStack, slr1Table, "Rejeitada")
												(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
												(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
												else
													let (nextSymbol,nextState) = Set.nth targetShifts 0 in
													let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
													let nextStep = ((getTail word), nextRevStack, slr1Table, valid) in
														nextStep
										else
											(word, revStack, slr1Table, "Simbolo Inválido")
								end
							| Accept -> 
								if (word = [dollar]) then
									((getTail word), [symb2str cfg.initial], slr1Table, "Aceite")
								else 
									((word), revStack, slr1Table, "Rejeitada")
							| Reduce({head = h;body = b}) -> 
								let popNumber = List.length b in
								let nextRevStack = pop (popNumber*2) revStack in
								let wordWithAddedHead = [h] @ word in
								let nextStep = (wordWithAddedHead, nextRevStack, slr1Table, valid) in
									nextStep
		
	
	
	
		
	let acceptWordSLR1StepV2 (step:trueslr1TableStep) cfg : trueslr1TableStep = 
			parseStepSLR1OperationV2 step cfg
						
			
			
			
	
	let entryHasConflict slr1TableEntry : bool =
		let (id,shifts,actionSet) = slr1TableEntry in
		let entryConflicts = Set.filter ( fun (_, actions) -> Set.size actions > 1) actionSet in
			not (Set.isEmpty entryConflicts)
	
	let isSLR1 cfg : bool =
		let slr1Table = makeSLR1Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg in
		let conflicts = Set.filter (entryHasConflict) slr1Table in
			Set.isEmpty conflicts
			
			
	let getSLR1DiagramId cfg : lr0DiagramId = (* igual ao LR0 *)
		makeLR0DiagramId (makeLR0Diagram cfg)
		
	let getSLR1Table cfg : slr1Table =
		makeSLR1Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg 

end
	(* ----- LR1 -----*)
module LR1Grammar =
struct
	open LRAux
	type t = ContextFreeGrammarBasic.t
	
	type lr1Item = {head:symbol; body1:symbol list; body2:symbol list; lookahead:symbols}	
	type lr1State = lr1Item set
	type lr1Diagram = lr1State set * (lr1State * symbol * lr1State ) set
	
	type stateName = string
	type lr1StateId = stateName * lr1State 
	type lr1DiagramId = lr1StateId set * (lr1StateId * symbol * lr1StateId ) set
	

	type lr1Action = Accept | Shift | Reduce of rule
	type lr1TableEntry = stateName * (symbol * stateName) set * (symbol * lr1Action set ) set (* talvez seja (symbol * lr1Action set ) set *)
	type lr1Table = lr1TableEntry set
	
	let isCompleteLR1Item {head=h; body1=b1; body2=b2;lookahead=l} =
		b2 = []

	let countCompleteLR1Items lr1State = 
		let completeItems = Set.filter(isCompleteLR1Item) lr1State in
			Set.size completeItems
			
			
	let getNextSymbolForLR1Item {head=h; body1=b1; body2=b2;lookahead=l}  =
		match b2 with
		| [] -> epsilon
		| x::xs -> x
		
	let getDirectorLR1 {head=_; body1=_; body2=b2; lookahead=l} = (* obtem o simbolo diretor de um item *)
		match b2 with 
			| [] -> epsilon (* epsilon, aka no symbol *) 
			| x::_ -> x
			
	(*
	let first symbols = (* Injected first to test LR1 grammars lookahead - Luis Monteiro *)
		match symbols with
		| [] -> Set.make ['$'] (* Não deve acontecer*)
		| x::xs -> 
			if(x = 'A') then ['$';'a';'b']
			else if(x = 'B') then ['a';'b']
			else if(x = 'a') then ['a']
			else ['b']
	*)		
	(*		
	let first symbols = (* Injected first to test LALR1 grammars lookahead - Luis Monteiro *)
		match symbols with
		| [] -> Set.make [dollar] (* Não deve acontecer*)
		| x::xs -> 
			if(x = symb "X") then Set.make [symb "c"; symb "d"]
			else if(x = symb "C") then Set.make [symb "c"; symb "d"]
			else if(x = symb "c") then Set.make [symb "c"]
			else Set.make [symb "d"]
	*)
	let getDirectorWithLookaheadLR1 {head=_; body1=_; body2=b2; lookahead=l} cfg = (* obtem o simbolo diretor de um item *)
		match b2 with 
			| [] -> (epsilon,Set.empty) (* epsilon, aka no symbol *) 
			| x::xs -> if(List.length b2 > 1) then (x,ContextFreeGrammarBasic.first xs true cfg) else (x,l)	
			
			
	let getDirectorsLR1 state = (* Aplica a função getDirector a todos os itens de um dado estado*)
		Set.filter (fun d-> d <> epsilon)(Set.map getDirectorLR1 state)
			
	(* função auxiliar para avançar o ponto de um item em um simbolo para
	    o nucleo do proximo estado. Ex: A ->.ab para A -> a.b *)
	let kernelAdvanceLR1Item {head=h; body1=b1; body2=b2;lookahead = l} =
		match b2 with
		| [] -> Error.fatal "kernelAdvanceItem: Este caso nem deve ser alcançavel"
		| x::xs -> {head = h; body1 = b1 @ [x]; body2 = xs;lookahead = l} 
			
	let buildLR1Item {head=h; body1=b1; body2=b2; lookahead=_} lookahead =
		{head=h; body1=b1; body2=b2; lookahead=lookahead}
				
	let getDirectorsWithLookaheadLR1 (state:lr1State) cfg = (* Aplica a função getDirectorWithLookaheadLR1 a todos os itens de um dado estado*)
		Set.filter (fun (d,l)-> d <> epsilon)(Set.map (fun it -> getDirectorWithLookaheadLR1 it cfg) state) 
		
	let hasSameCore {head=h1; body1=b1; body2=b2; lookahead=l1} {head=h2; body1=b21; body2=b22; lookahead=l2} = 
		(h1 = h2 && b1 = b21 && b2 = b22)
		
	let mergeTwoItemsWithSameCore {head=h1; body1=b1; body2=b2; lookahead=l1} {head=h2; body1=b21; body2=b22; lookahead=l2} =
		let combinedLookahead = Set.union l1 l2 in
		{head=h1; body1=b1;body2=b2;lookahead=combinedLookahead}
		
	let mergeOneItem item currentItems = (* careful with the args order*)
		let (a,b) = Set.partition (fun i -> hasSameCore item i ) currentItems in
			if Set.size a = 0 then Set.add item currentItems
			else Set.add (mergeTwoItemsWithSameCore (Set.hd a) item) b	
			
	(*
	let mergeItems2 currentItems newItems =
		let rec process currentItems newItems =
			match newItems with
			| [] -> currentItems 
			| i::is -> process (mergeOneItem i currentItems) is 
		in
			process currentItems (Set.toList newItems) 		
	*)
	
			
	let rec mergeItems currentItems newItems =
		if Set.isEmpty newItems then
			currentItems
		else
			let (i,is) = Set.cut newItems in
				mergeItems (mergeOneItem i currentItems) is 
	
	(*			
	let rec mergeItems currentItems newItems =
		Set.match_ newItems 
			(fun () -> currentItems)
			(fun i is -> mergeItems (mergeOneItem i currentItems) is)
	*)
	
	let rule2ItemLR1 (rule: rule) lookahead =
		{head = rule.head; body1 = []; body2 = rule.body; lookahead = lookahead} 
	
	let generateItemsForVarDirectorWithLookahead director rules lookahead = 
		let itemRules = Set.filter (fun {head = h; body =_} -> h = director) rules in 
		let items = Set.map (fun r -> rule2ItemLR1 r lookahead) itemRules in	
			items
			
	let diagramsJoin2LR1 (s0,t0) (s1,t1) = (Set.union s0 s1, Set.union t0 t1) (* juntar dois diagramas LR0 para obter um diagrama LR0 resultante da união *)	
	
	let rec diagramsJoinListLR1 l : lr1Diagram = (* Juntar um conjunto de diagramas para produzir o diagrama LR0, cada diagrama desta lista corresponde a um estado rescrito como diagrama *)
		match l with
		| [] -> (Set.empty , Set.empty) 
		| d::ds -> diagramsJoin2LR1 d (diagramsJoinListLR1 ds)
	
	
	
	let makeLR1DiagramId diagram : lr1DiagramId (* Cria etiquetas para os estados e os mesmos estados contidos nas transições do diagrama*) =
		let (states,transitions) = diagram in
		let dictionary = List.combine (Set.toList states) (nats (Set.size states)) in
		let statesId = Set.map (fun s -> (List.assoc s dictionary,s) ) states in
		let transitionsId = Set.map (fun (a,b,c) -> ((List.assoc a dictionary, a), b,(List.assoc c dictionary, c))) transitions in
			(statesId, transitionsId)
	



	let buildLR1ReductionActionsForOne completeItems symbol = (* Warning, input must only contain complete items *)
		let reductionItems = Set.filter(fun it -> Set.belongs symbol it.lookahead) completeItems in
			Set.map (fun it -> Reduce ({head = it.head;body = it.body1}) ) reductionItems	
			


	let buildLR1ReductionActions completeItems alphabet = 
		Set.map(fun symbol -> (symbol, buildLR1ReductionActionsForOne completeItems symbol) ) alphabet
	
	
	let buildLR1ShiftActionsForOne items symbol : lr1Action set = 
		let shiftItems = Set.filter(fun it -> (getNextSymbolForLR1Item it) = symbol) items in
		if(Set.size shiftItems > 0) then
			Set.make [Shift]
		else
			Set.empty
			


	let buildLR1ShiftActions completeItems alphabet = 
		Set.map(fun symbol -> (symbol, buildLR1ShiftActionsForOne completeItems symbol) ) alphabet
	
	

	let buildLR1MixedActionsForOne cfgInitial items symbol = 
		let reductionItems = Set.filter(fun it -> (Set.belongs symbol it.lookahead) && isCompleteLR1Item it) items in
		let fixedreductionItems = Set.filter (fun it-> it.head != cfgInitial) reductionItems in
		let acceptItems = Set.filter (fun it -> it.head = cfgInitial && symbol = dollar && isCompleteLR1Item it && (Set.belongs it fixedreductionItems) = false) items in
		let shiftItems = Set.filter(fun it -> (getNextSymbolForLR1Item it) = symbol) items in
		let reductionEntries = Set.map (fun it -> Reduce ({head = it.head;body = it.body1}) ) fixedreductionItems in
	
		if(Set.size acceptItems > 0) then
			if(Set.size shiftItems > 0) then
				Set.union (Set.union (Set.make [Shift]) reductionEntries) (Set.make [Accept])
			else
				Set.union reductionEntries (Set.make [Accept])
		else	
			if(Set.size shiftItems > 0) then
				Set.union (Set.make [Shift]) reductionEntries
			else
				reductionEntries
				
				
				

	let buildLR1MixedActions cfgInitial (items:lr1State) alphabet = (* True build function - prototype *) (* transformar na forma do buildLR1ReductionActions *)
		Set.map(fun symbol -> (symbol, buildLR1MixedActionsForOne cfgInitial items symbol) ) alphabet
		
			
	let makeLR1TableEntry (id, lr1State) (cfg:t) transitions = (* possivelmente dar merge aos buildLR1Actions?*)
		let stateTransitions = Set.filter (fun ((a,_),_,_)-> a = id) transitions in
			if Set.size stateTransitions = 0 then (* this part seems fine *)
				let {head = h;body1 = b1;body2 = b2;lookahead = l} = List.hd (Set.toList lr1State) in
					if h = cfg.initial then 
						let lr1Actions : (symbol * lr1Action set) set = Set.make [dollar,Set.make [Accept]] in
							(id,Set.empty,lr1Actions)
					else
						let completeAlphabet = Set.add dollar cfg.alphabet in (* Se o $, final da palavra, não estiver no alfabeto da gramática *)
						let lr1Actions : (symbol * lr1Action set) set = buildLR1ReductionActions lr1State completeAlphabet in
							(id,Set.empty, lr1Actions)		
			else  (* Existem Shifts e possivelmente tambem reducoes *)
				let nextShifts = Set.map (fun (a,b,(cId,c)) -> (b,cId)) stateTransitions in
					if(countCompleteLR1Items lr1State = 0) then (* Não existem reducoes *)
						let lr1Actions = buildLR1ShiftActions lr1State cfg.alphabet in
							(id, nextShifts, lr1Actions)
					else (* Existem reducoes e transferencias *)
						let completeAlphabet = Set.add dollar cfg.alphabet in (* Se o $, final da palavra, não estiver no alfabeto da gramática *)
						let lr1Actions = buildLR1MixedActions cfg.initial lr1State completeAlphabet in
							(id, nextShifts, lr1Actions)
					
	
	(*pre: isLR1 cfg *)
	let makeLR1Table (labeledDiagram:lr1DiagramId) cfg : lr1Table = (* recebe um diagrama numerado e constroi a tabela de parsing a partir das transições *) 
		let (statesId, transitionsId) = labeledDiagram in
			Set.map (fun s -> makeLR1TableEntry s cfg transitionsId) statesId


	
		
	let lr1StateClosureStep (cfg: t) currentItems = (* Create items for current directors *)
		let directorsWithLookahead : (symbol * symbols) set = getDirectorsWithLookaheadLR1 currentItems cfg in
		
		let varDirectorsWithLookahead = Set.filter (fun (d,_) -> Set.belongs d cfg.variables) directorsWithLookahead in
		let newItems = Set.flatMap (fun (d,l) -> generateItemsForVarDirectorWithLookahead d cfg.rules l) varDirectorsWithLookahead in
		let mergedItems = mergeItems currentItems newItems in
			mergedItems
		
		
	let rec lr1StateClosure cfg currentItems : lr1State = (* Create all items for a singular state *)
		let next = lr1StateClosureStep cfg currentItems in
			if Set.subset next currentItems then next
			else lr1StateClosure cfg next
			
			
	
	let makeSingularNextLR1Diagram (cfg:t) prevState symbol : lr1Diagram = (* Creates a diagram containing only 1 state using the previous state and the transition symbol*)
		let items4Kernel = Set.filter (fun it -> getDirectorLR1 it = symbol) prevState in (* falta avançar o ponto *)
		let kernel = Set.map (kernelAdvanceLR1Item) items4Kernel in
		let closure = lr1StateClosure cfg kernel in
			(Set.make [prevState; closure], Set.make [(prevState ,symbol , closure )])
					

	
	let makeNextLR1Diagram (cfg:t) prevState : lr1Diagram = (* For each director symbol on the previous state, create a diagram and join all obtained diagrams into a single diagram*)
		let dirs = getDirectorsLR1 prevState in
		let diagrams = Set.map (fun d -> makeSingularNextLR1Diagram cfg prevState d) dirs in
			diagramsJoinListLR1 (Set.toList diagrams) 

			
		
	let makeNextLR1DiagramAll (cfg:t) states : lr1Diagram = (* build the diagram using the initial state, then use the makeNextLR0Diagram function to calculate all states obtainable from the initial state*)
		let diagrams = Set.map (fun s -> makeNextLR1Diagram cfg s) states in
			diagramsJoinListLR1 (Set.toList diagrams)

		
		
	let rec makeLR1DiagramX (cfg:t) diagram = (* função auxiliar que irá produzir o diagrama LR1 *)
		let (states,transitions) : lr1Diagram = diagram in 
		let next = makeNextLR1DiagramAll cfg states in
		let next2 = diagramsJoin2LR1 next (states,transitions) in
		let (states2,transitions2) = next2 in
			if Set.size states = Set.size states2 && Set.size transitions = Set.size transitions2 then next2
			else makeLR1DiagramX cfg next2 
			
			
	let makeFirstLR1Diagram (cfg:t) : lr1Diagram = (* O primeiro estado tem um procedimento de criação um pouco differente *) 
		let kernel = Set.map (fun r -> rule2ItemLR1 r (Set.make [dollar])) (LR0Grammar.startRules cfg) in	
		(*let kernelWithLookahead : lr1Item = buildLR1KernelItems kernel '$' in *)
		let closure = lr1StateClosure cfg kernel in
			(Set.make [closure], Set.empty)	
	
	let makeLR1Diagram (cfg:t) = makeLR1DiagramX cfg (makeFirstLR1Diagram cfg)  (* ponto de partida na construção do diagrama LR1 *)
	
	
	let rec parseOperationLR1 lr1Table word stateStack symbolStack (cfg:t) = 
		let currentState = int_of_string(List.hd stateStack) in 
		let (id,shifts,actionSet) = Set.nth lr1Table currentState in (* get corresponding table entry *)
		let topSymbol = List.nth word 0 in
			if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
				let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
					if(Set.size targetShifts = 0) then false
					else
						let (nextSymbol,nextState) = Set.nth targetShifts 0 in
						let nextStateStack = [nextState] @ stateStack in
						let nextSymbolStack = [nextSymbol] @ symbolStack in
							parseOperationLR1 lr1Table (getTail word) nextStateStack nextSymbolStack cfg
			else 
				let peekedSymbol = List.nth word 0 in
				let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
				let nEntries = Set.size peekedsymbolAndActions in
					if nEntries = 0 then 
						false
					else if nEntries > 1 then
						Error.fatal "ParseOperationLR1: conflito"
					else
						let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
						let action = Set.hd actions in
						match action with
						| Shift -> 
							begin
								match word with
								| [] -> false
								| s::_ -> 
									if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
										let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
											if(Set.size targetShifts = 0) then false
											(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
											(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
											else
												let (nextSymbol,nextState) = Set.nth targetShifts 0 in
												let nextStateStack = [nextState] @ stateStack in
												let nextSymbolStack = [nextSymbol] @ symbolStack in
													parseOperationLR1 lr1Table (getTail word) nextStateStack nextSymbolStack cfg
									else
										Error.fatal "ParseOperationLR1: este simbolo não pertence ao alfabeto desta gramatica"
							end
						| Accept -> 
							word = [dollar]	
						| Reduce({head = h;body = b}) -> 
							let popNumber = List.length b in
							let nextStateStack = (pop popNumber stateStack) in
							let nextSymbolStack = (pop popNumber symbolStack) in
							let wordWithAddedHead = [h] @ word in
								parseOperationLR1 lr1Table (wordWithAddedHead) nextStateStack nextSymbolStack cfg (*Add the variable, aka head of the reduction rule, to the word being processed *)
								
	
	(* pre: isLR1 cfg 
	   pre: isWordValid word cfg *)
	let acceptWordLR1 (word:symbol list) cfg : bool = 
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLR1Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
			parseOperationLR1 lr1Table (word @ [dollar]) stateRevStack symbolRevStack cfg
			
			
	(* Added functions to provide a step-by step LR1 visualization of accepting *)

	type lr1TableStep = symbol list * string list * symbol list * lr1Table * bool
	
	let acceptWordLR1Init (word:symbol list) cfg : lr1TableStep =
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLR1Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
		let valid = true in
		let initStep = ((word @ [dollar]),stateRevStack,symbolRevStack,lr1Table,valid) in
			initStep
	
	let parseStepLR1Operation (step:lr1TableStep) (cfg:t) : lr1TableStep = 
		let (word, stateStack, symbolStack, lr1Table, valid) = step in
		let currentState = int_of_string(List.hd stateStack) in 
		let (id,shifts,actionSet) = Set.nth lr1Table currentState in (* get corresponding table entry *)
		let topSymbol = List.nth word 0 in
			if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
				let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
					if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, lr1Table, false)
					else
						let (nextSymbol,nextState) = Set.nth targetShifts 0 in
						let nextStateStack = [nextState] @ stateStack in
						let nextSymbolStack = [nextSymbol] @ symbolStack in
						let nextStep = ((getTail word), nextStateStack, nextSymbolStack, lr1Table, valid) in
							nextStep
			else 
				let peekedSymbol = List.nth word 0 in
				let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
				let nEntries = Set.size peekedsymbolAndActions in
					if nEntries = 0 then 
						(word, stateStack, symbolStack, lr1Table, false)
					else if nEntries > 1 then
						Error.fatal "parseStepLR1Operation: conflito"
					else
						let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
						let action = Set.hd actions in
						match action with
						| Shift -> 
							begin
								match word with
								| [] -> (word, stateStack, symbolStack, lr1Table, false)
								| s::_ -> 
									if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
										let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
											if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, lr1Table, false)
											(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
											(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
											else
												let (nextSymbol,nextState) = Set.nth targetShifts 0 in
												let nextStateStack = [nextState] @ stateStack in
												let nextSymbolStack = [nextSymbol] @ symbolStack in
												let nextStep = ((getTail word), nextStateStack, nextSymbolStack, lr1Table, valid) in
													nextStep
									else
										Error.fatal "parseStepLR1Operation: este simbolo não pertence ao alfabeto desta gramatica"
							end
						| Accept -> 
							if (word = [dollar]) then
								((getTail word), stateStack, symbolStack, lr1Table, valid)
							else 
								((getTail word), stateStack, symbolStack, lr1Table, false)
						| Reduce({head = h;body = b}) -> 
							let popNumber = List.length b in
							let nextStateStack = (pop popNumber stateStack) in
							let nextSymbolStack = (pop popNumber symbolStack) in
							let wordWithAddedHead = [h] @ word in
							let nextStep = (wordWithAddedHead, nextStateStack, nextSymbolStack, lr1Table, valid) in
								nextStep
		
	
	
	
		
	let acceptWordLR1Step (step:lr1TableStep) cfg : lr1TableStep = 
			parseStepLR1Operation step cfg
			
			
	(* updated accept *)
	type truelr1TableStep = symbol list * string list * lr1Table * string
	
	let acceptWordLR1InitV2 (word:symbol list) cfg : truelr1TableStep =
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLR1Diagram cfg)) cfg in
		let revStack = ["0"] in 
		let valid = "Ongoing" in
		let initStep = ((word @ [dollar]),revStack,lr1Table,valid) in
			initStep
	
	let parseStepLR1OperationV2 (step:truelr1TableStep) (cfg:t) : truelr1TableStep = 
		let (word, revStack, lr1Table, valid) = step in
		let currentState = int_of_string(List.hd revStack) in 
		let (id,shifts,actionSet) = Set.nth lr1Table currentState in (* get corresponding table entry *)
		if(List.length word = 0) then
			(word, revStack, lr1Table, "Rejeitada")
		else
			let topSymbol = List.nth word 0 in
				if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
					let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
						if(Set.size targetShifts = 0) then (word, revStack, lr1Table, "Rejeitada")
						else
							let (nextSymbol,nextState) = Set.nth targetShifts 0 in
							let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
							let nextStep = ((getTail word), nextRevStack, lr1Table, valid) in
								nextStep
				else 
					let peekedSymbol = List.nth word 0 in
					let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
					let nEntries = Set.size peekedsymbolAndActions in
						if nEntries = 0 then 
							(word, revStack, lr1Table, "Rejeitada")
						else if nEntries > 1 then
							(word, revStack, lr1Table, "Conflito")
						else
							let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
							(*Durante o accept, se encontrar um conflito, para imediatamente e retorna "... Conflito ..."
								Uma possibilidade possivel. Se há conflitos, só ficam ativos os botões de Accept que sejam imunes a esses conflitos.
								*)
	
							if Set.size actions > 1 then (* NEW *)
								(word, revStack, lr1Table, "Conflito")
							else

						let action = Set.hd actions in
							match action with
							| Shift -> 
								begin
									match word with
									| [] -> (word, revStack, lr1Table, "Rejeitada")
									| s::_ -> 
										if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
											let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
												if(Set.size targetShifts = 0) then (word, revStack, lr1Table, "Rejeitada")
												(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
												(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
												else
													let (nextSymbol,nextState) = Set.nth targetShifts 0 in
													let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
													let nextStep = ((getTail word), nextRevStack, lr1Table, valid) in
														nextStep
										else
											(word, revStack, lr1Table, "Simbolo Inválido")
								end
							| Accept -> 
								if (word = [dollar]) then
									((getTail word), [symb2str cfg.initial], lr1Table, "Aceite")
								else 
									((getTail word), revStack, lr1Table, "Rejeitada")
							| Reduce({head = h;body = b}) -> 
								let popNumber = List.length b in
								let nextRevStack = pop (popNumber*2) revStack in
								let wordWithAddedHead = [h] @ word in
								let nextStep = (wordWithAddedHead, nextRevStack, lr1Table, valid) in
									nextStep
		
	
	
	
		
	let acceptWordLR1StepV2 (step:truelr1TableStep) cfg : truelr1TableStep = 
			parseStepLR1OperationV2 step cfg
			
			
			
			
			
	
	let entryHasConflict lr1TableEntry : bool =
		let (id,shifts,actionSet) = lr1TableEntry in
		let entryConflicts = Set.filter ( fun (_, actions) -> Set.size actions > 1) actionSet in
			Set.size entryConflicts > 0
	
	let isLR1 cfg : bool =
		let slr1Table = makeLR1Table (makeLR1DiagramId (makeLR1Diagram cfg)) cfg in
		let conflicts = Set.filter (entryHasConflict) slr1Table in
			Set.size conflicts = 0
			
			
	let getLR1DiagramId cfg : lr1DiagramId =
		makeLR1DiagramId (makeLR1Diagram cfg)
		
	let getLR1Table cfg : lr1Table =
		makeLR1Table (makeLR1DiagramId (makeLR1Diagram cfg)) cfg 
	
end	
	(* ----- LALR1 -----*)
module LALR1Grammar =
	struct
	open LRAux
	open LR0Grammar	
	open LR1Grammar	
		
		
	let itemsSameCores it1 it2 =
		it1.head = it2.head && it1.body1 = it2.body1 && it1.body2 = it2.body2
		
	let itemsJoinLookahead it1 it2 =
		{head = it1.head; body1 = it1.body1; body2 = it1.body2; lookahead = (Set.union it1.lookahead it2.lookahead)}
	
	
	let getStateCore (state:lr1State) =
		Set.map (fun it -> {head = it.head; body1 = it.body1; body2 = it.body2}) state
	
	
	let haveSameCores lr1state1 lr1state2 =
		let state1Core = getStateCore lr1state1 in
		let state2Core = getStateCore lr1state2 in
			Set.equals state1Core state2Core
				
	(*pre: hasSameCores state1 state2 *)
	let mergeLR1States state1 state2 =
		Set.map (fun it -> 
			let fit = Set.find (fun it2 -> itemsSameCores it it2) state2 in itemsJoinLookahead it fit) state1 
	
	
	
	type lr1StateId = stateName * lr1State 
	type lr1DiagramId = lr1StateId set * (lr1StateId * symbol * lr1StateId ) set
		
	let rec lr1StateFusionId statesId  = (* Esta deve ser a função a aplicar na versão final, a differença é que esta função trabalha com o diagrama diretamente (a parte dos estados identificados) *)
		match statesId with
		| [] -> []
		| (id,x)::xs -> 
			let ss = lr1StateFusionId xs in
			let (a,b) = List.partition (fun (_,y)-> haveSameCores x y) ss in 
				match a with
				| [] -> (id,x)::ss 
				| [(id2,y)] -> (id^","^id2,mergeLR1States x y)::b(* fundir x com y*)
				| _ -> Error.fatal "lr1StateFusionFail"	
		
				
	
	let rec lr1StateFusion states  =
		match states with
		| [] -> []
		| x::xs -> 
			let ss = lr1StateFusion xs in
			let (a,b) = List.partition (haveSameCores x) ss in 
				match a with
				| [] -> x::ss 
				| [y] -> mergeLR1States x y::b(* fundir x com y*)
				| _ -> Error.fatal "lr1StateFusionFail"
		
	let translate state fstates =
		Set.find (fun s -> haveSameCores state s) fstates
		
				
	let lr1TransFusion trans fstates =
		Set.map (fun (s1,sym,s2) -> (translate s1 fstates,sym,translate s2 fstates)) trans
				
	
	let makeLALR1FromLR1 diagram =
		let (states,transitions) : lr1Diagram = diagram in 
		let fstates = lr1StateFusion (Set.toList states) in
		let ftrans = lr1TransFusion transitions (Set.make fstates) in
		let lalr1Diagram : lr1Diagram = ((Set.make fstates),ftrans) in
			lalr1Diagram
			
			
	(* pre: isLR1 cfg 
	   pre: isWordValid word cfg *)
	let acceptWordLALR1 (word: word) cfg : bool = 
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
			parseOperationLR1 lr1Table (word @ [dollar]) stateRevStack symbolRevStack cfg
			
			
	(* Added functions to provide a step-by step LR1 visualization of accepting *)

	type lr1TableStep = symbol list * string list * symbol list * lr1Table * bool
	
	let acceptWordLALR1Init (word:symbol list) cfg : lr1TableStep =
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
		let valid = true in
		let initStep = ((word @ [dollar]),stateRevStack,symbolRevStack,lr1Table,valid) in
			initStep
	
	let parseStepLALR1Operation (step:lr1TableStep) (cfg:t) : lr1TableStep = 
		let (word, stateStack, symbolStack, lr1Table, valid) = step in
		let currentState = int_of_string(List.hd stateStack) in 
		let (id,shifts,actionSet) = Set.nth lr1Table currentState in (* get corresponding table entry *)
		let topSymbol = List.nth word 0 in
			if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
				let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
					if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, lr1Table, false)
					else
						let (nextSymbol,nextState) = Set.nth targetShifts 0 in
						let nextStateStack = [nextState] @ stateStack in
						let nextSymbolStack = [nextSymbol] @ symbolStack in
						let nextStep = ((getTail word), nextStateStack, nextSymbolStack, lr1Table, valid) in
							nextStep
			else 
				let peekedSymbol = List.nth word 0 in
				let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
				let nEntries = Set.size peekedsymbolAndActions in
					if nEntries = 0 then 
						(word, stateStack, symbolStack, lr1Table, false)
					else if nEntries > 1 then
						Error.fatal "parseStepLR1Operation: conflito"
					else
						let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
						let action = Set.hd actions in
						match action with
						| Shift -> 
							begin
								match word with
								| [] -> (word, stateStack, symbolStack, lr1Table, false)
								| s::_ -> 
									if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
										let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
											if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, lr1Table, false)
											(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
											(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
											else
												let (nextSymbol,nextState) = Set.nth targetShifts 0 in
												let nextStateStack = [nextState] @ stateStack in
												let nextSymbolStack = [nextSymbol] @ symbolStack in
												let nextStep = ((getTail word), nextStateStack, nextSymbolStack, lr1Table, valid) in
													nextStep
									else
										Error.fatal "parseStepLR1Operation: este simbolo não pertence ao alfabeto desta gramatica"
							end
						| Accept -> 
							if (word = [dollar]) then
								((getTail word), stateStack, symbolStack, lr1Table, valid)
							else 
								((getTail word), stateStack, symbolStack, lr1Table, false)
						| Reduce({head = h;body = b}) -> 
							let popNumber = List.length b in
							let nextStateStack = (pop popNumber stateStack) in
							let nextSymbolStack = (pop popNumber symbolStack) in
							let wordWithAddedHead = [h] @ word in
							let nextStep = (wordWithAddedHead, nextStateStack, nextSymbolStack, lr1Table, valid) in
								nextStep
		
	
	
	
		
	let acceptWordLALR1Step (step:lr1TableStep) cfg : lr1TableStep = 
			parseStepLALR1Operation step cfg		
			
			
	(* updated accept *)
	
	let acceptWordLALR1InitV2 (word:symbol list) cfg : truelr1TableStep =
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))) cfg in
		let revStack = ["0"] in 
		let valid = "Ongoing" in
		let initStep = ((word @ [dollar]),revStack,lr1Table,valid) in
			initStep
	
	let parseStepLALR1OperationV2 (step:truelr1TableStep) (cfg:t) : truelr1TableStep = 
		let (word, revStack, lr1Table, valid) = step in
		let currentState = int_of_string(List.hd revStack) in 
		let (id,shifts,actionSet) = Set.nth lr1Table currentState in (* get corresponding table entry *)
		if(List.length word = 0) then
			(word, revStack, lr1Table, "Rejeitada")
		else
			let topSymbol = List.nth word 0 in
				if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
					let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
						if(Set.size targetShifts = 0) then (word, revStack, lr1Table, "Rejeitada")
						else
							let (nextSymbol,nextState) = Set.nth targetShifts 0 in
							let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
							let nextStep = ((getTail word), nextRevStack, lr1Table, valid) in
								nextStep
				else 
					let peekedSymbol = List.nth word 0 in
					let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
					let nEntries = Set.size peekedsymbolAndActions in
						if nEntries = 0 then 
							(word, revStack, lr1Table, "Rejeitada")
						else if nEntries > 1 then
							(word, revStack, lr1Table, "Conflito")
						else
							let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)

							(*Durante o accept, se encontrar um conflito, para imediatamente e retorna "... Conflito ..."*)
							if Set.size actions > 1 then (* NEW *)
								(word, revStack, lr1Table, "Conflito")
							else
				
							
							let action = Set.hd actions in
							match action with
							| Shift -> 
								begin
									match word with
									| [] -> (word, revStack, lr1Table, "Rejeitada")
									| s::_ -> 
										if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
											let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
												if(Set.size targetShifts = 0) then (word, revStack, lr1Table, "Rejeitada")
												(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
												(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
												else
													let (nextSymbol,nextState) = Set.nth targetShifts 0 in
													let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
													let nextStep = ((getTail word), nextRevStack, lr1Table, valid) in
														nextStep
										else
											(word, revStack, lr1Table, "Simbolo Inválido")
								end
							| Accept -> 
								if (word = [dollar]) then
									((getTail word), [symb2str cfg.initial], lr1Table, "Aceite")
								else 
									((getTail word), revStack, lr1Table, "Rejeitada")
							| Reduce({head = h;body = b}) -> 
								let popNumber = List.length b in
								let nextRevStack = pop (popNumber*2) revStack in
								let wordWithAddedHead = [h] @ word in
								let nextStep = (wordWithAddedHead, nextRevStack, lr1Table, valid) in
									nextStep
		
	
	
	
		
	let acceptWordLALR1StepV2 (step:truelr1TableStep) cfg : truelr1TableStep = 
			parseStepLALR1OperationV2 step cfg
					
			
			
			
			
	let entryHasConflict slr1TableEntry : bool =
		let (id,shifts,actionSet) = slr1TableEntry in
		let entryConflicts = Set.filter ( fun (_, actions) -> Set.size actions > 1) actionSet in
			not (Set.isEmpty entryConflicts)
	
	let isLALR1 cfg : bool =
		let lalr1Table = makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))) cfg in
		let conflicts = Set.filter (entryHasConflict) lalr1Table in
			Set.isEmpty conflicts
			
			
	let getLALR1DiagramId cfg : lr1DiagramId =
		 makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))
		
	let getLALR1Table cfg : lr1Table =
		makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))) cfg
end

module ContextFreeGrammarLR =
struct
	type t = ContextFreeGrammarBasic.t
	open LR0Grammar
	open SLR1Grammar
	open LR1Grammar
	open LALR1Grammar
	
	class model (arg: t Arg.alternatives) =
		object(self) inherit ContextFreeGrammarLL1.model arg as super
		
				
			method isLR0 : bool =
				isLR0 (self#representation)
				
			method getLR0DiagramId : LR0Grammar.lr0DiagramId =
				getLR0DiagramId (self#representation)
				
			method getLR0Table : LR0Grammar.lr0Table =
				getLR0Table (self#representation)
				
			method getLR0TableExt : LR0Grammar.lr0TableExt =
				getLR0TableExt (self#representation)
				
		(* SLR1 *)
			method isSLR1 : bool =
				isSLR1 (self#representation)
				
			method getSLR1Table : SLR1Grammar.slr1Table =
				getSLR1Table (self#representation)
				
		(* LR1 *)	
		
			method isLR1 : bool =
				isLR1 (self#representation)
			
			method getLR1DiagramId : LR1Grammar.lr1DiagramId =
				getLR1DiagramId (self#representation)
			
			method getLR1Table : LR1Grammar.lr1Table =
				getLR1Table (self#representation)
				
		(* LALR1 *)		
			method isLALR1 : bool =
				isLALR1 (self#representation)
			
			method getLALR1DiagramId : LR1Grammar.lr1DiagramId =
				getLALR1DiagramId (self#representation)
				
			method getLALR1Table : LR1Grammar.lr1Table =
				getLALR1Table (self#representation)
	end
end

# 1 "src/ContextFreeGrammar.ml"
(*
 * ContextFreeGrammar.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
????
 *)

(*
 * Description: Context-free grammar functionality.
 *
 * TODO: More cleanup.
 *)

open BasicTypes

module ContextFreeGrammar =
struct
	include ContextFreeGrammarSupport

	class model (arg: t Arg.alternatives) =
		object(self) inherit ContextFreeGrammarLR.model arg as super
     end
end
# 1 "src/AttributeGrammarSupport.ml"
(*
 * AttributeGrammarSupport.ml
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
 * mar/2025 (amd) - New module
 *)

(*
 * Description: Support types and functions for FAs.
 *)

open BasicTypes

module AttributeGrammarBasics =
struct
	type attribute = symbol
	type attributes = attribute set
	type attrArg = variable * int
	type value =
	    | Int of int
        | String of string
        | Bool of bool
	type expression =
		| Const of value
		| Apply of attribute * attrArg
		| Expr of string * expression * expression
	type equation = expression * expression
	type equations = equation set
	type condition = expression 
	type conditions = condition set


	(*
 * condition: tem que ser booleano
 * equation do lado esquerdo é um apply
 *)

	type rule = {
		head : variable;
		body : word;
		equations : equations;
		conditions : conditions
	}
	type rules = rule set

	type t = {
		alphabet : symbols;
		variables : variables;
		synthesized : attributes;
		inherited : attributes;
		initial : variable;
		rules : rules
	}

	let kind = "attribute grammar"

	let ag_zero: t = {
		alphabet = Set.empty;
		variables = Set.make [draftVar];
		inherited = Set.empty;
		synthesized = Set.empty;
		initial = draftVar;
		rules = Set.empty;
	}



	type evaluation = attribute * value

	type evaluations = evaluation set

    type node = symbol * evaluations

    type parseTree =
              Leaf of node
            | Node of node * parseTree list

end

module ExpressionSyntax =
struct
	open CharType
	open Scanner
	open AttributeGrammarBasics

(* Literals: T, F, 1, 10, 100, "", "ola"
   Ops: [<, <=, <>, >, >=, =] [+] [*]
*)
	let parseApply (): expression =
		let attr = getAlpha () in
		let _ = getChar '(' in
		let v, i = getCharInt () in
		let _ = getChar ')' in
			Apply (char2symb attr, (char2symb v, i))
		
	let rec parseExp3 (): expression =
		match peek () with
		| c when isDigit c -> Const (Int (getInt ()))
		| '\'' ->  Const (String (getDelim '\'' '\''))
		| 'T' -> skip (); Const (Bool true)
		| 'F' -> skip (); Const (Bool false)
		| '(' -> let _ = getChar '(' in
				let e = parseExp0 () in
				let _ = getChar ')' in
					Expr ("(", e, Const (Int 0))
		| _ -> parseApply ()

	and parseExp2 (): expression =
		let l = parseExp3 () in
		let c = peek () in
			if c = '*' then (
				skip();
				Expr ("*", l, parseExp2 ())
			)
			else
				l
		
	and parseExp1 (): expression =
		let l = parseExp2 () in
		let c = peek () in
			if c = '+' then (
				skip();
				Expr ("+", l, parseExp1 ())
			)
			else
				l
	
	and parseExp0 (): expression =
		let l = parseExp1 () in
			match peek () with
			| '<' ->
				skip();
				(match peek () with
				| '=' -> skip (); Expr ("<=", l, parseExp0 ())
				| '>' -> skip (); Expr ("<>", l, parseExp0 ())
				| _ -> Expr ("<", l, parseExp0 ()))
			| '=' ->
				skip(); Expr ("=", l, parseExp0 ())
			| '>' ->
				skip();
				(match peek () with
				| '=' -> skip (); Expr (">=", l, parseExp0 ())
				| _ -> Expr (">", l, parseExp0 ()))
			| _ ->
				l
		
	let parseExpression (): expression =
		parseExp0 ()
	
	let rec expression2str e =
		match e with
		| Const (Int i) ->
			string_of_int i
		| Const (String s) ->
			"\"" ^ s ^ "\""
		| Const (Bool b) ->
			if b then "T" else "F"
		| Apply (attr, (var, i)) when i = -1 ->
			symb2str attr ^ "(" ^ symb2str var ^ ")"
		| Apply (attr, (var, i)) ->
			symb2str attr ^ "(" ^ symb2str var ^ string_of_int i ^ ")"
		| Expr ("(", l, _) ->
			"(" ^ expression2str l ^ ")"
		| Expr (op, l, r) ->
			expression2str l ^ " " ^ op ^ " " ^ expression2str r
end

module EquationsSyntax =
struct
	open CharType
	open Scanner
	open AttributeGrammarBasics
	
	let parseEquation (): equation =
		let l = ExpressionSyntax.parseApply () in
			let _ = getChar '=' in
			let r = ExpressionSyntax.parseExpression () in
				(l, r)

	let rec parseEquationsX (): equations =
		match peek() with
			| '}' -> Set.empty
			| _ ->
				let e = parseEquation () in
					match peek () with
					| ';' -> skip (); Set.cons e (parseEquationsX ())
					| '}' -> Set.make [e]
					| _ -> rubbish "at the end of equation"

	let parseEquations (): equations =
		match peek() with
			| '{' -> skip();
					let res = parseEquationsX () in
					let _ = getChar '}' in
						res
			| _ -> Set.empty

	let equation2str (l, r) =
		ExpressionSyntax.expression2str l
		^ " = "
		^ ExpressionSyntax.expression2str r
end

module ConditionsSyntax =
struct
	open CharType
	open Scanner
	open AttributeGrammarBasics

	let parseCondition (): condition =
		ExpressionSyntax.parseExpression ()

	let rec parseConditionsX (): conditions =
		match peek() with
		| ']' -> Set.empty
		| _ ->
			let e = parseCondition () in
				match peek () with
				| ';' -> skip (); Set.cons e (parseConditionsX ())
				| ']' -> Set.make [e]
				| _ -> rubbish "at the end of condition"
			
	let parseConditions (): conditions =
		match peek() with
		| '[' -> skip();
				let res = parseConditionsX () in
				let _ = getChar ']' in
					res
		| _ -> Set.empty

	let condition2str c =
		ExpressionSyntax.expression2str c
end	

module AttributeGrammarSyntax =
struct
	open CharType
	open Scanner
	open AttributeGrammarBasics

	let parseSymbol () : symbol =
		if peek () = '<' then
			let str = getDelim '<' '>' in 
				str2symb ("<" ^ str ^ ">")
		else
			char2symb (get ())
						
	let parseHead (): symbol =
		match peek() with
		| ' ' -> invalid "Empty rule"
		| _ -> parseSymbol ()
		
	let parseNeck (): unit =
		getStr "->"

	let rec parseBody (): word =
		match peek() with
		| ' ' | '{' -> []
		| _ -> let sy = parseSymbol () in
					sy::parseBody ()

	let parseFinish (): unit =
		match peek() with
		| ' ' -> ()
		| _ -> 	rubbish "at the end of rule"

	let parseLine line: rules =
		if String.trim line = "" then
			Set.empty
		else begin
			Scanner.start "AttributeGrammarSyntax" line;
			try
				let h = parseHead () in
				let _ = parseNeck () in
				let b = parseBody () in
				let b = if b = [] then [epsilon] else b in
				let e = EquationsSyntax.parseEquations () in
				let c = ConditionsSyntax.parseConditions () in
				let _ = parseFinish () in
					Set.make [{head=h; body=b;
						equations=e; conditions=c}]
			with Not_found ->
				Set.empty
		end

	let parse rs: rules =
		Set.flatMap parseLine rs
					
	let rule2str {head=h; body=b; equations=eqs; conditions=conds} =
		let rule = (symb2str h) ^ " -> " ^ (word2str b) in
		let eqs = Set.toList eqs in
		let eqs = String.concat "; " (List.map EquationsSyntax.equation2str eqs) in
		let eqs = if eqs = "" then "" else " {" ^ eqs ^ "}" in
		let conds = Set.toList conds in
		let conds = String.concat "; " (List.map ConditionsSyntax.condition2str conds) in
		let conds = if conds = "" then "" else " [" ^ conds ^ "]" in
			rule ^  eqs ^ conds

	let toString rs: string =
		let rl = Set.toList rs in
			String.concat "\n" (List.map rule2str rl)

	let toStringList rs: string list =
		let rl = Set.toList rs in
			List.map rule2str rl
	
	let (-->) h b : rule =
		{ head = h; body = str2word b;
		equations=Set.empty; conditions=Set.empty }

	let show rs =
		Util.println [toString rs]
end


module AttributeGrammarJSon =
struct
end

module AttributeGrammarConversions =
struct
	open AttributeGrammarBasics
	open AttributeGrammarSyntax

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			ag_zero
		else {
			alphabet = JSon.fieldSymbolSet j "alphabet";
			variables = JSon.fieldSymbolSet j "variables";
			inherited = JSon.fieldSymbolSet j "inherited";
			synthesized = JSon.fieldSymbolSet j "synthesized";
			initial = JSon.fieldSymbol j "initial";
			rules = AttributeGrammarSyntax.parse (JSon.fieldStringSet j "rules");
		}

	let toJSon0 (rep: t): JSon.t =
		JSon.makeAssoc [
			("alphabet", JSon.makeSymbolSet rep.alphabet);
			("variables", JSon.makeSymbolSet rep.variables);
			("inherited", JSon.makeSymbolSet rep.inherited);
			("synthesized", JSon.makeSymbolSet rep.synthesized);
			("initial", JSon.makeSymbol rep.initial);
			("rules", JSon.makeStringSet (Set.map rule2str rep.rules))
		]
	
	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 rep)

	let toJSon (rep: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) rep
end

module AttributeGrammarBasicFunctions =
struct
	open AttributeGrammarBasics
	open AttributeGrammarConversions

	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (rep: t): unit =
		let j = toJSon rep in
			JSon.show j

	let show2 (id: Entity.t) (rep: t): unit =
		let j = toJSon2 id rep in
			JSon.show j
end

module AttributeGrammarX =
struct
	open AttributeGrammarBasics
end

module AttributeGrammarLearnOCaml =
struct
	open AttributeGrammarBasics
	open AttributeGrammarX

	let moduleName =
		"AttributeGrammar"

	let xTypeName =
		"AttributeGrammar"

	let solution (name: string) (rep: t): string =
		""

	let prelude : string =
		""

	let example : JSon.t =
		JNull
end

module AttributeGrammarSupport =
struct
	include AttributeGrammarBasics
	include AttributeGrammarConversions
	include AttributeGrammarBasicFunctions
	include AttributeGrammarLearnOCaml
end
# 1 "src/AttributeGrammar.ml"
(*
 * AttributeGrammar.ml
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
 *  Written by Pedro Bailão (pb)
 *)

(*
 * ChangeLog:
 *
 * mar/2025 (pb) - validateAG implementation method.
 * feb/2025 (amd) - New file "AttributeGrammar.ml".
 *)

(*
 * Description: Attribute grammar functionality.
 *
 * TODO: More cleanup.
 *)

	open BasicTypes
	open Set

	module AttributeGrammarPrivate =
	struct
		open AttributeGrammarSupport

		let howMany (body: word) (v: variable) =
			List.length (List.filter (fun x-> x = v) body)

		let ag2cfg (rep: t): ContextFreeGrammarBasic.t =
			ContextFreeGrammarBasic.cfg_zero

		let validateAttrArg (ag:t) (r:rule) (attr: attribute) (v,i) =
			if i = 0 then
				r.head = v && Set.belongs attr ag.inherited
		else
			let counter = howMany r.body v in
				counter >= i


		let rec validateExp (name: string) (ag: t) (r: rule) (e: expression) : string =
					  let attr_exists attr =
					    Set.belongs attr (Set.union ag.synthesized ag.inherited)
					  in

					  let vars_exists vars =
					    Set.belongs vars ag.variables
					  in

					  match e with
					  | Const (Int _) -> "int"
					  | Const (String _) -> "string"
					  | Const (Bool _) -> "bool"
					  | Apply (attr, (var, i)) ->
					      if attr_exists attr then
					        if vars_exists var then
					          if validateAttrArg ag r attr (var, i) then "int"
					          else Error.error name  "Argumento do Atributo invalido" "error"
					        else  Error.error name  "Variável não encontrada" "error"
					      else Error.error name  "Atributo não encontrado" "error"
					  | Expr (op, l, r_expr) ->
					      let tl = validateExp name ag r l in  (* Pass `r` explicitly *)
					      let tr = validateExp name ag r r_expr in  (* Pass `r` explicitly *)
					      if tl = tr then
					        match op with
					        | "+" | "*" ->
					            if tl <> "string" then tl
					            else Error.error name "Incompatibilidade de tipos" "error"
					        | "<" | ">" | "<=" | ">=" | "=" | "<>" ->
					            if tl = "int" then "bool"
					            else Error.error name "Incompatibilidade de tipos" "error"
					        | _ -> Error.error name "Operador desconhecido" "error"
					      else Error.error name "Incompatibilidade de tipos" "error"

		let validateEquation (name: string) (ag: t) ((lhs, rhs): equation) (r: rule): unit =
		    match lhs with
		    | Apply _ ->
		        let lhs_type = validateExp name ag r lhs in
		        let rhs_type = validateExp name ag r rhs in
		        if lhs_type = rhs_type && lhs_type <> "erro" then ()
		        else Error.error name "Incompatibilidade de tipos na equaçao" () (* passar os erros para ingles*)
		    | _ -> Error.error name "Lado esquerdo da equação deve ser Apply" ()

		    (*fazer vadildação das condições, fazer validar da expr e ver se é booleano*)
		    (*passo seguinte calcular os atributos utilizando a tree??*)
		    (*começar com atributos sintetizados*)

        let validateCondition (name: string) (ag: t) (cond: condition) (rule: rule): unit =
           if validateExp name ag rule cond = "bool" then ()
           else Error.error name "Condição deve ser booleana" ()


		let accept (rep: t) (w: word): bool =
			false

        let ag_to_cfg (ag: t): ContextFreeGrammar.t =
          {
            alphabet = ag.alphabet;
            variables = ag.variables;
            initial = ag.initial;
            rules = Set.map (fun r ->
              {
                ContextFreeGrammar.head = r.head;
                body = r.body
              }
            ) ag.rules
          }



        let cfg_to_ag (cfg: ContextFreeGrammar.t): t =
          {
            alphabet = cfg.alphabet;
            variables = cfg.variables;
            synthesized = Set.empty;
            inherited = Set.empty;
            initial = cfg.initial;
            rules = Set.map (fun (r: ContextFreeGrammar.rule) ->
              {
                head = r.head;
                body = r.body;
                equations = Set.empty;
                conditions = Set.empty
              }
            ) cfg.rules
          }

        let validateEquations (name: string) (rep: t): unit =
            Set.iter (fun r ->
                Set.iter (fun eq ->
                    validateEquation name rep eq r
                ) r.equations
            ) rep.rules

        let validateConditions (name: string) (rep: t): unit =
            Set.iter (fun r ->
                Set.iter (fun eq ->
                    validateCondition name rep eq r
                ) r.conditions
            ) rep.rules

        let validate (name: string) (rep: t): unit =
            let cfg = ag2cfg rep in
                ContextFreeGrammarPrivate.validate name cfg;
                validateEquations name rep;
                validateConditions name rep

        let rec collectFromExpression (exp: expression): attributes =
          match exp with
            | Apply (attr, _) -> Set.make [attr]
            | Expr (_, l, r) -> Set.union (collectFromExpression l) (collectFromExpression r)
            | _ -> Set.empty

        let collectFromEquation (eq: equation): attributes =
            let (lhs, rhs) = eq in
            Set.union (collectFromExpression lhs) (collectFromExpression rhs)

        let collectFromCondition (cond: condition): attributes =
            collectFromExpression cond

        let collectFromRule (r: rule): attributes =
            let fromEquations = Set.flat_map collectFromEquation r.equations in
            let fromConditions = Set.flat_map collectFromCondition r.conditions in
            Set.union fromEquations fromConditions

        let removeUnusedAttributes (rep: t): t =
            let used = Set.flat_map collectFromRule rep.rules in
            let newSynthesized = Set.inter rep.synthesized used in
            let newInherited = Set.inter rep.inherited used in
           {
              rep with
              synthesized = newSynthesized;
              inherited = newInherited;
            }

        let collectVarsFromRule (r: rule) (vars: variables): variables =
          Set.inter vars (Set.make r.body)

        let removeUnusedRulesAndVariables (rep: t) =
          let rec collectUsedVariables rules used =
            match rules with
            | [] -> used
            | rule :: rest ->
                let usedInBody = List.fold_left (fun acc sym -> Set.cons sym acc) used rule.body in
                collectUsedVariables rest (Set.cons rule.head usedInBody)
          in
          let usedVariables = collectUsedVariables (Set.toList rep.rules) (Set.make [rep.initial]) in
          let newVariables = Set.filter (fun var -> Set.belongs var usedVariables) rep.variables in
          let newRules =
            Set.filter
              (fun rule ->
                Set.belongs rule.head newVariables &&
                List.for_all (fun sym -> Set.belongs sym newVariables || Set.belongs sym rep.alphabet) rule.body
              )
              rep.rules
          in
          { rep with variables = newVariables; rules = newRules }

        let getRoot (pt: parseTree): node =
                match pt with
                | Leaf ((s,e)) -> (s,e)
                | Node ((s,e), _) -> (s,e)

        let getRootSymbol (pt: parseTree): symbol =
            getRoot pt |> fst

        let getRule (ag: t) (head: variable) (body: word): rule =
            Set.find (fun r -> r.head = head && r.body = body) ag.rules

        let rec associ key i l =
            match l with
                | [] ->
                    failwith "associ"
                | (a,b)::xs when a = key ->
                    if i = 1 || i = -1 then b
                    else associ key (i-1) xs
                | (a,b)::xs ->
                    associ key i xs

       (*
let rec replace (expr: expression) (nodes: node list): expression =
           match expr with
           | Apply (attr, (var, i)) ->
                let (_, evals) = associ var i nodes in
                let value = Set.find (fun (a, _) -> a = attr) evals in
                Int value
           | Expr (op, left, right) ->
                Expr (op, replace left nodes, replace right nodes)
           | _ -> expr *)
        let evaluateOp (op: string) (l: value) (r:value): value =
            match op with
                | "+" ->(
                    match (l, r) with
                    | Int li, Int ri -> Int (li + ri)
                    | String ls, String rs -> String (ls ^ rs)
                    | _ -> failwith "Invalid expression in evaluation"
                )
                | "*" -> (
                    match (l, r) with
                    | Int li, Int ri -> Int (li * ri)
                    | _ -> failwith "Invalid expression in evaluation"
                )

                (* acabar isto com os outros valores  -> *)
                | _ -> failwith "Unknown operator in evaluation"

       let rec evaluate (e: expression) (nodes: node list): value =
            match e with
            | Const v -> v
            | Apply (attr, (var, i)) ->
                let evals = associ var i nodes in
                let (_,b) = Set.find (fun (a, _) -> a = attr) evals in
                b
            | Expr (op, left, right) ->
                let l = evaluate left  nodes in
                let r = evaluate right nodes in
                evaluateOp op l r


       let eval (e: equation) (children: parseTree list): evaluation =
            let nodes = List.map getRoot children in
            match e with
            | (Apply (attr, (var, _)), expr) ->
                (attr, evaluate expr nodes)
            | _ -> failwith "Invalid equation in evaluation"

       let rec calcAtributes (ag: t) (pt: parseTree): parseTree =
            match pt with
                | Leaf n -> Leaf n (*ainda não ha semente*)
                | Node ((head,_), children) ->
                    let body = List.map getRootSymbol children in
                    let rule = getRule ag head body in
                    let children = List.map (calcAtributes ag) children in
                    let evals = Set.map (fun e -> eval e children) rule.equations in
                    Node ((head, evals), children)

	end

	module AttributeGrammar =
	struct
		include AttributeGrammarSupport
		open AttributeGrammarPrivate

		(* Make *)
		let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
		let make (arg: t Arg.alternatives): t = make arg validate

		(* Exercices support *)
		let checkProperty (fa: t) (prop: string) =
			match prop with
				| _ -> Model.checkProperty prop
		let checkExercise ex fa = Model.checkExercise ex (accept fa) (checkProperty fa)
		let checkExerciseFailures ex fa = Model.checkExerciseFailures ex (accept fa) (checkProperty fa)

		(* Ops *)
		let stats = Model.stats
		let accept = accept
	end

	module AttributeGrammarTop =
	struct
		open AttributeGrammar
	end

	open AttributeGrammarTop

	module AttributeGrammarSupportTests : sig end =
	struct
		open AttributeGrammar
		open AttributeGrammarPrivate

		let active = true

		let ag0 = {| {
					kind : "attribute grammar",
					description : "",
					name : "ag",
					alphabet : ["[", "]"],
					variables : ["S"],
					inherited : [],
					synthesized : [],
					initial : "S",
					rules : [ "S -> [S] {l(S) = 2; l(S) = 'ole'; l(S0) = l(S1)} [123 + 56; 56; 'ola']",
										"S -> SS {l(S) = l(S1) + 3 + 'ola' + l(S12345)}",
										"S -> ~ {l(S0) = 6}",
										"S -> ~ {l(S0) = 1+2*3<T>F<=T>=5=T<>T+(1*2)}"
									]
	} |}

        let ag = {| {
                            kind : "attribute grammar",
                            description : "",
                            name : "ag",
                            alphabet : ["[", "]"],
                            variables : ["S"],
                            inherited : ["l"],
                            synthesized : ["l"],
                            initial : "S",
                            rules : [ "S -> [S] {l(S) = 2; l(S) = 'ole'; l(S0) = l(S1)} [123 + 56; 56; 'ola']",
                                                "S -> SS {l(S) = l(S1) + 3 + 'ola' + l(S1)}",
                                                "S -> ~ {l(S0) = 6}",
                                                "S -> ~ {l(S0) = 1+2*3<T>F<=T>=5=T<>T+(1*2)}"
                                            ]
            } |}

		let test0 () =
			let j = JSon.parse ag in
			let g = fromJSon j in
			let h = toJSon g in
				JSon.show h

		let test1 () =
			let g = make (Arg.Text ag) in
			let h = toJSon g in
			validate "ag" g;
			JSon.show h


        let test_ag_to_cfg () =
            let ag = make (Arg.Text ag) in
            let cfg = ag_to_cfg ag in
            let converted_ag = cfg_to_ag cfg in
            let h = toJSon converted_ag in
                JSon.show h

        let test_cfg_to_ag () =
          let ag = make (Arg.Text ag) in
          let cfg = ag_to_cfg ag in
          let converted_ag = cfg_to_ag cfg in
          (* Add assertions to verify the converted AG *)
          JSon.show (toJSon converted_ag)

        let runAll =
          if Util.testing active "AttributeGrammarSupport" then begin
            Util.header "test0";
            test0 ();
            Util.header "test1";
            test1 ();
          end
	end


# 3 "src/PushdownAutomatonSupport.ml"
(*
 * PushdownAutomaton.ml
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
 *  Written by Carlos Freitas (cf)
 *)

(*
 * ChangeLog:
 *
 * ???/2022 (cf) - ???.
 * may/2022 (amd) - Initial skeleton.
 *)

(*
 * Description: Pushdown automata functionality.
 *)

open BasicTypes

module PushdownAutomatonBasics =
struct
	type transition =
		  state			(* state *)
		* symbol		(* current symbol on top of the stack *)
		* symbol		(* consumed input symbol *)
		* state			(* next state *)
		* symbol list	(* new top of stack*)
	type transitions = transition set
		
	type t = {
		inputAlphabet : symbols;
		stackAlphabet : symbols;
		states : states;
		initialState : state;
		initialStackSymbol : symbol;
		transitions : transitions;
		acceptStates : states;
		criteria: bool; (* true = acceptStates | false = emptyStack *) 
	}
	
	let kind = "pushdown automaton"
	
	let pda_zero: t = {
		inputAlphabet = Set.empty;
		stackAlphabet = Set.make [draftVar];
		states = Set.make [draftState];
		initialState = draftState;
		initialStackSymbol = draftVar;
		transitions = Set.empty;
		acceptStates = Set.empty;
		criteria = false
	}
end

module PushdownAutomatonConversions =
struct
	open PushdownAutomatonBasics

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			pda_zero
		else {
			inputAlphabet = JSon.fieldSymbolSet j "inputAlphabet";
			stackAlphabet = JSon.fieldSymbolSet j "stackAlphabet";
			states = JSon.fieldStateSet j "states";
			initialState = JSon.fieldState j "initialState";
			initialStackSymbol = JSon.fieldSymbol j "initialStackSymbol";
			transitions = JSon.fieldQuintupletsSet j "transitions";
			acceptStates = JSon.fieldStateSet j "acceptStates";
			criteria = JSon.fieldBool j "criteria"
		}

	let toJSon0 (rep: t): JSon.t =
		JSon.makeAssoc [
			("inputAlphabet", JSon.makeSymbolSet rep.inputAlphabet);
			("stackAlphabet", JSon.makeSymbolSet rep.stackAlphabet);
			("states", JSon.makeStateSet rep.states);
			("initialState", JSon.makeState rep.initialState);
			("initialStackSymbol", JSon.makeSymbol rep.initialStackSymbol);
			("transitions", JSon.makeQuintupletsSet rep.transitions);
			("acceptStates", JSon.makeStateSet rep.acceptStates);
			("criteria", JSon.makeBool rep.criteria)
		]
	
	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 rep)


	
	let toJSon (rep: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) rep
end

module PushdownAutomatonBasicFunctions =
struct
	open PushdownAutomatonBasics
	open PushdownAutomatonConversions

	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (rep: t): unit =
		let j = toJSon rep in
			JSon.show j

	let show2 (id: Entity.t) (rep: t): unit =
		let j = toJSon2 id rep in
			JSon.show j
end

module PushdownAutomatonX =
struct
	open PushdownAutomatonBasics

	type tx = {
		inputAlphabet: symbol list;
		stackAlphabet: symbol list;
		states: state list;
		initialState: state;
		initialStackSymbol: symbol;
		transitions: transition list;
		acceptStates: state list;
		criteria: bool
	}

	let internalize (pda: tx): t = {
		inputAlphabet = Set.make pda.inputAlphabet;
		stackAlphabet = Set.make pda.stackAlphabet;
		states = Set.make pda.states;
		initialState = pda.initialState;
		initialStackSymbol = pda.initialStackSymbol;
		transitions = Set.make pda.transitions;
		acceptStates = Set.make pda.acceptStates;
		criteria = pda.criteria
	}

	let externalize (pda: t): tx = {
		inputAlphabet = Set.toList pda.inputAlphabet;
		stackAlphabet = Set.toList pda.stackAlphabet;
		states = Set.toList pda.states;
		initialState = pda.initialState;
		initialStackSymbol = pda.initialStackSymbol;
		transitions = Set.toList pda.transitions;
		acceptStates = Set.toList pda.acceptStates;
		criteria = pda.criteria
	}
end

module PushdownAutomatonLearnOCaml =
struct
	open PushdownAutomatonBasics
	open PushdownAutomatonX

	let moduleName =
		"PushdownAutomaton"

	let xTypeName =
		"pushdownAutomaton"


	let solution (name: string) (rep: t): string =
		""

	let prelude : string =
		""

	let example : JSon.t =
		JSon.parse {|
		{
			kind : "finite automaton",
			description : "this is an example",
			name : "pda example",
			alphabet: ["w", "z"],
			states : ["START", "X", "Z"],
			initialState : "START",
			transitions : [
				["START", "w", "X"], ["X", "z", "X"]
			],
			acceptStates : ["Z"]
		}
		|}	(* please, do not change this line *)
end

module PushdownAutomatonSupport =
struct
	include PushdownAutomatonBasics
	include PushdownAutomatonConversions
	include PushdownAutomatonBasicFunctions
	include PushdownAutomatonLearnOCaml
end


# 3 "src/PushdownAutomaton.ml"
(*
 * PushdownAutomaton.ml
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
 *  Written by Carlos Freitas (cf)
 *)

(*
 * ChangeLog:
 *
 * mar/2023 (cf) - First release.
 * may/2022 (amd) - Initial skeleton.
 *)

(*
 * Description: Pushdown automata functionality.
 *)

open BasicTypes

module PushdownAutomatonPrivate =
struct
	open PushdownAutomatonSupport

	(* TYPES *)
	type configuration =
		  state
		* symbol list
	type configurations = configuration set

	type path = configuration list
	type paths = path list

	type stack = symbol list

	type configuration_ =
		  state
		* stack
		* word
	type configurations_ = configuration_ set

	type searchTreeRef =
		  	NotAcceptLeafRef of configuration_
    	| AcceptLeafRef of configuration_
      | NodeRef of configuration_ * searchTreeRef set ref

	type searchTree =
		  	NotAcceptLeaf of configuration_
    	| AcceptLeaf of configuration_
      | Node of configuration_ * searchTree set
      | BestNode of configuration_ * searchTree set

	(* CONSTANTS *)
	let stackSpecialSymb: symbol = symb "z"
	let stackConverterSymb: symbol = symb "$"

	exception TooManyTries
	let maxTries = 100


	(* AUXILIARY *)

	let transitionGet1 trns = Set.map ( fun (a,_,_,_,_) -> a ) trns
	let transitionGet2 trns = Set.map ( fun (_,b,_,_,_) -> b ) trns
	let transitionGet3 trns = Set.map ( fun (_,_,c,_,_) -> c ) trns
	let transitionGet4 trns = Set.map ( fun (_,_,_,d,_) -> d ) trns
	let transitionGet345 trns = Set.map ( fun (_,_,c,d,e) -> (c, d, e) ) trns
	let transitionGet45 trns = Set.map ( fun (_,_,_,d,e) -> (d, e) ) trns
	let transitionGet5 trns = Set.map ( fun (_,_,_,_,e) -> e ) trns
	let transitionGet5Flat trns = Set.flatten (Set.map ( fun (_,_,_,_,e) -> Set.make e ) trns)

	let getStackSymbols trns =
		let stackSymbtoPutInStack =
			Set.fold_left ( fun acc symbList ->
				Set.union acc (Set.make symbList)
			) Set.empty (transitionGet5 trns)
		in
			Set.union (transitionGet2 trns) stackSymbtoPutInStack

	let configurationGet1 configs = Set.map ( fun (a,_) -> a ) configs
	let configurationGet2 configs = Set.map ( fun (_,b) -> b ) configs

	let configuration_Get1 configs = Set.map ( fun (a,_,_) -> a ) configs
    let configuration_Get2 configs = Set.map ( fun (_,b,_) -> b ) configs
    let configuration_Get3 configs = Set.map ( fun (_,_,c) -> c ) configs

    
	let validate (name: string) (pda: t): unit = (

		(* the alphabet must not contain "~" *)
		let validAlphabet = not (Set.belongs epsilon pda.inputAlphabet) in

		(* does initial state belong to the set of all states *)
		let validInitSt = Set.belongs pda.initialState pda.states in

		(* does initial stack symbol belong to the stack alphabet *)
		let validInitStackSymbol = Set.belongs pda.initialStackSymbol pda.stackAlphabet in

		(* are all accepted states members of all states *)
		let validAccSts = Set.subset pda.acceptStates pda.states in

		let fromSt = transitionGet1 pda.transitions in
		let syfromStack = transitionGet2 pda.transitions in
		let sy = transitionGet3 pda.transitions in
		let toSt = transitionGet4 pda.transitions in
		let sysToStack = transitionGet5Flat pda.transitions in
		let alpha = Set.add epsilon pda.inputAlphabet in

		(* do all transitions have states belonging to all states, symbols belonging to the alphabet and stackSymbol belonging to stack alphabet *)
		let validTrns =
			(Set.subset fromSt pda.states) &&
			(Set.subset syfromStack pda.stackAlphabet) &&
			(Set.subset sy alpha) &&
			(Set.subset toSt pda.states) &&
			(Set.subset sysToStack pda.stackAlphabet)
		in

		if not validAlphabet then
			Error.error name
				"The alphabet contains epsilon '~', and it should not" ();
			if not validInitSt then
				Error.error name
					"The initial state does not belong to the set of all states" ();
			if not validInitStackSymbol then
				Error.error name
					"The initial stack symbol does not belong to the stack alphabet" ();
			if not validAccSts then
				Error.error name
					"Some accept states do not belong to the set of all states" ();
			if not validTrns then
				Error.error name
					"Some transitions are invalid" ()
		)

	let rec fixedPointN (f: 'a -> 'a)(x: 'a) (moves: int): 'a =
		if moves = 0 then raise TooManyTries;
		let next = f x in
			if x = next then x
			else fixedPointN f next (moves-1)

	let fixedPointMaxTries f x = fixedPointN f x maxTries

	let getValidNonEmptyTransitions currentState topStackSymb trns: transitions =
		Set.filter (fun (a,b,c,_,_) -> a = currentState && b = topStackSymb && c <> epsilon) trns

	let mapStepsToConfigurationAndSymbol steps stack: (configuration * symbol) set =
		Set.map (fun ((symb, nextState, toPutInStack)) -> ((nextState, toPutInStack @ stack), symb)) steps

	let getNextConfigurationsWithSymbols trns (currentState, stack): (configuration * symbol) set =
		match stack with
		|	[] -> Set.make []
		| topStackSymb::restStack ->
				let nextSteps = transitionGet345 (getValidNonEmptyTransitions currentState topStackSymb trns) in
					mapStepsToConfigurationAndSymbol nextSteps restStack

	let getNextConfigurationsWithSymbols trns configurations: (configuration * symbol) set =
		Set.flatMap (getNextConfigurationsWithSymbols trns) configurations

	let addSymbToWords (w: symbol) (words: words): words =
		Set.map (fun word -> w::word ) words


	let mapStepsToConfiguration steps stack: configurations =
		Set.map (fun ((nextState, toPutInStack)) -> (nextState, toPutInStack @ stack)) steps

	let getValidTransitions currentState topStackSymb w trns: transitions =
		Set.filter (fun (a,b,c,_,_) -> a = currentState && b = topStackSymb && (c = w)) trns

	let getNextConfigurationsFromConfig w trns (currentState, stack): configurations =
		match stack with
		|	[] -> Set.make []
		| topStackSymb::restStack ->
				let nextSteps = transitionGet45 (getValidTransitions currentState topStackSymb w trns) in
					mapStepsToConfiguration nextSteps restStack

	let getNextConfigurations w trns configurations: configurations =
		Set.flatMap (getNextConfigurationsFromConfig w trns) configurations

	let addNextConfigurations w trns configurations: configurations =
		let nextConfigs = getNextConfigurations w trns configurations in
		Set.union nextConfigs configurations

	let exploreEmptyTransitions trns configurations: configurations =
		fixedPointMaxTries (addNextConfigurations epsilon trns) configurations

	let isInAcceptState configs acceptStates criteria: bool =
		if criteria then Set.inter (configurationGet1 configs) acceptStates <> Set.empty
		else Set.exists (fun stack -> stack = []) (configurationGet2 configs)

	let tickComputation w configurations transitions: configurations =
			let nextConfigs = getNextConfigurations w transitions configurations in
				exploreEmptyTransitions transitions nextConfigs

	let getInitialConfig initialState initialStackSymbol transitions =
		let initialConfig = Set.make [(initialState, [initialStackSymbol])] in
			exploreEmptyTransitions transitions initialConfig

	let generate length pda: words = (* ! AMD TROCAR !!! *)
		let rec gen n configuration =
			let configs = exploreEmptyTransitions pda.transitions (Set.make [configuration]) in
			if n = 0 then
				if isInAcceptState configs pda.acceptStates pda.criteria then Set.make [[]] else Set.empty
			else
				let newConfigsAndSymbols = getNextConfigurationsWithSymbols pda.transitions configs in
					let genX symb n config = addSymbToWords symb (gen (n-1) config) in (*exprimentar uniao para n-1*)
						Set.flatMap (fun (config, symb) -> genX symb n config) newConfigsAndSymbols
		in
			let initialConfig = (pda.initialState, [pda.initialStackSymbol]) in
				gen length initialConfig

	let printConfig (state,stack,word) =
		let open Util in
		Printf.printf "(%s, " (state2str state);
		print (List.map symb2str stack); print_string ", ";
		print_string (word2str word); print_string ")\n"

	let rec printSearchTree = function
		| NotAcceptLeaf c -> print_string "NotAcceptLeaf "; printConfig c
		| AcceptLeaf c -> print_string "AcceptLeaf "; printConfig c
		| Node (c,nodes) -> print_string "Node ";printConfig c; Set.iter printSearchTree nodes
		| BestNode (c,nodes) -> print_string "BestNode ";printConfig c; Set.iter printSearchTree nodes

	let configIsInAcceptState_ acceptStates criteria (state, stack, word): bool =
			word = [] && (if criteria then Set.belongs state acceptStates else stack = [])

	let configsAreInAcceptState_ acceptStates criteria configs: bool =
		Set.exists (configIsInAcceptState_ acceptStates criteria) configs

	let advanceOneTransition transitions (state, stack, word): configurations_ =
		let getNextConfig restStack wordLeft (_,_,_,nextState,toPutInStack) = (nextState, toPutInStack@restStack, wordLeft) in
		let buildNewTransitions restStack restWord validTrns = Set.map (getNextConfig restStack restWord) validTrns in
		let getNextConfigs inputSymbol restWord topStack restStack =
			let validTransitions = getValidTransitions state topStack inputSymbol transitions in
				buildNewTransitions restStack restWord validTransitions
	in
		match stack, word with
		| [], _ -> Set.empty
		| s::ss, [] -> getNextConfigs epsilon [] s ss
		| s::ss, w::ww ->
			let nextConfigConsumed = getNextConfigs w ww s ss in
			let nextConfigNotConsumed = getNextConfigs epsilon (w::ww) s ss  in
				Set.union nextConfigConsumed nextConfigNotConsumed

	let accept pda word: bool =
		let rec acceptRec configurations: bool =
			Set.match_ configurations
			(fun () -> false)
			(fun _ _ ->
				if configsAreInAcceptState_ pda.acceptStates pda.criteria configurations then true
				else
					let nextConfigs = Set.flatMap (advanceOneTransition pda.transitions) configurations in
					if Set.equals configurations nextConfigs then false
					else acceptRec nextConfigs
			)
		in
			let getInitialConfig = Set.make [(pda.initialState, [pda.initialStackSymbol], word)] in
				acceptRec getInitialConfig

	let configHasNoSymbolToConsume (_,_,word) = word=[]

	let buildEndNode acceptStates criteria transitions config =
		if configIsInAcceptState_ acceptStates criteria config then AcceptLeafRef(config)
        else if configHasNoSymbolToConsume config && (advanceOneTransition transitions config) = Set.empty then NotAcceptLeafRef(config)
        else NodeRef(config, ref (Set.make[]))

	let foundAcceptConfig searchTreeSet =
		Set.exists (fun node -> match node with | AcceptLeafRef _ -> true | _ -> false) searchTreeSet

	let filterSearchNode searchTreeSet =
		Set.filter (fun node -> match node with | NodeRef _ -> true | _ -> false) searchTreeSet

	exception ShouldNotHappen
	let getNodeElements = function
		| NodeRef(config, setNodes) -> (config, setNodes)
		| _ -> raise ShouldNotHappen

	let getNextConfigsPair searchTreeSet transitions =
		Set.map (fun tree ->
			let (config, _) = getNodeElements tree in
			let nextConfigs = advanceOneTransition transitions config in
            	(tree, nextConfigs)
		) searchTreeSet

	let buildTree acceptStates criteria transitions pairTreesAndNextConfigs =
		Set.flatMap (fun (tree, nextConfigs) ->
			let (_, setNodes) = getNodeElements tree in
			let newNodes = Set.map (buildEndNode acceptStates criteria transitions) nextConfigs in
            setNodes := newNodes;
            	newNodes
		) pairTreesAndNextConfigs

	let buildSearchTree (word: word) pda: searchTreeRef =
		let rec buildSearchTree (forest: searchTreeRef set) =
			Set.match_ forest
			(fun () -> ())
			(fun _ _ ->
				let pairTreesAndNextConfigs = getNextConfigsPair forest pda.transitions in
				let nextNodes = buildTree pda.acceptStates pda.criteria pda.transitions pairTreesAndNextConfigs in
				if foundAcceptConfig nextNodes || Set.equals forest nextNodes then ()
				else buildSearchTree (filterSearchNode nextNodes)
			)
		in
			let initialConfig = (pda.initialState, [pda.initialStackSymbol], word) in
			if configIsInAcceptState_ pda.acceptStates pda.criteria initialConfig then AcceptLeafRef(initialConfig)
			else
				let searchTree: searchTreeRef = NodeRef(initialConfig, ref (Set.make [])) in
					buildSearchTree (Set.make [searchTree]);
					searchTree

	let isBestNode = function | AcceptLeaf _ -> true | BestNode _ -> true | _ -> false
	let hasBestPath searchTreeSet =
    	Set.exists isBestNode searchTreeSet

	let rec mapBestPath: searchTreeRef -> searchTree = function
		| AcceptLeafRef c -> AcceptLeaf(c)
		| NotAcceptLeafRef c -> NotAcceptLeaf(c)
		| NodeRef(c, treeSet) ->
			let nextLayer = Set.map mapBestPath !treeSet in
			if hasBestPath nextLayer then BestNode(c, nextLayer) else Node(c, nextLayer)

	let getSearchTree word pda =
		buildSearchTree word pda |> mapBestPath

	let transformConfig (state,stack,word) = (state,stack)

	let getWordFromNode = function
		| AcceptLeaf((_,_,word)) -> word
		| NotAcceptLeaf((_,_,word)) -> word
		| Node((_,_,word), _) -> word
		| BestNode((_,_,word), _) -> word

	let getBestNodeAndWord setNodes =
    	let node = Set.find isBestNode setNodes in
    		(node, getWordFromNode node)

	let rec buildBestPath: searchTree -> path = function
		| AcceptLeaf(c) -> [transformConfig c]
		| NotAcceptLeaf(c) -> []
		| Node(c, treeSet) -> []
		| BestNode((_,_,word) as c, treeSet) ->
					let (nextBestNode, nextWord) = getBestNodeAndWord treeSet in
					if (word = nextWord) then buildBestPath(nextBestNode)
					else (transformConfig c)::buildBestPath(nextBestNode)

	let getBestPath word pda =
			getSearchTree word pda |> buildBestPath

	let getConfigsAndNextNodes: searchTree -> configuration * searchTree set = function
			| AcceptLeaf(c) -> (transformConfig c, Set.empty)
			| NotAcceptLeaf(c) -> (transformConfig c, Set.empty)
			| Node(c, treeSet) -> (transformConfig c, treeSet)
			| BestNode(c, treeSet) -> (transformConfig c, treeSet)

	let getAllConfigsAndFilterNextNodesThatConsumeSymbol nodes =
		Set.fold_left (fun (configsAcc,treeSetAcc) tree ->
			let (c,treeSet) = getConfigsAndNextNodes tree in
			let word = getWordFromNode tree in
			let nextTreeSet = Set.filter (fun t -> word <> getWordFromNode t) treeSet in
				(Set.add c configsAcc, Set.union nextTreeSet treeSetAcc)
		) (Set.empty, Set.empty) nodes

	let getNextEpsilonNodes nodes =
		Set.fold_left (fun treeSetAcc tree ->
			let (_,treeSet) = getConfigsAndNextNodes tree in
			let word = getWordFromNode tree in
			let nextTreeSet = Set.filter (fun t -> word = getWordFromNode t) treeSet in
				Set.union nodes (Set.union nextTreeSet treeSetAcc)
		) Set.empty nodes

	let rec getConfigsBySymbolConsumedStep (forest: searchTree set): configurations list =
		Set.match_ forest
		(fun () -> [])
		(fun _ _ ->
			let closureNodes = Set.fixedPoint getNextEpsilonNodes forest in
			let (configs, nextNodes) = getAllConfigsAndFilterNextNodesThatConsumeSymbol closureNodes in
					configs::(getConfigsBySymbolConsumedStep nextNodes)
		)

	let getConfigsPathBySymbolConsumedAndBestPath word pda: configurations list * path =
		let searchTree = getSearchTree word pda in
			let bestPath = buildBestPath searchTree in
				let configsBySymbolConsumedStep = getConfigsBySymbolConsumedStep (Set.make [searchTree]) in
					(configsBySymbolConsumedStep, bestPath)



	let rec generateUntil length pda: words =
		if length < 0 then Set.empty
		else Set.union (generate length pda) (generateUntil (length-1) pda)

	let transformPdaToAcceptStates pda: t =
		let buildNewTransitions (si: state) (sf: state): transitions = (*si estado inicial, sf estado final*)
			let initialTrsn: transition =
				(si, stackConverterSymb, epsilon, pda.initialState, [pda.initialStackSymbol; stackConverterSymb]) in
			let buildTrasitionToFinalState s =
				(state s, stackConverterSymb, epsilon, sf, [stackConverterSymb]) in
			let buildTransitions states = Set.map buildTrasitionToFinalState states in
				Set.add initialTrsn (buildTransitions pda.states)
		in
		let convertedPda: t = {
			inputAlphabet = pda.inputAlphabet;
			stackAlphabet = Set.add stackConverterSymb pda.stackAlphabet;
			states = Set.union (pda.states) (Set.make [state "Si"; state "Sf"]);
			initialState = state "Si";
			initialStackSymbol = stackConverterSymb;
			transitions = Set.union (pda.transitions) (buildNewTransitions (state "Si") (state "Sf"));
			acceptStates = Set.make [(state "Sf")];
			criteria = true
			}
		in
			if pda.criteria then pda else convertedPda

	let transformPdaToAcceptEmptyStack pda: t =
		let newStackAlphabet = Set.add stackConverterSymb pda.stackAlphabet in
		let buildNewTransitions si sf: transitions = (*si estado inicial, sf estado final*)
			let initialTrsn: transition = (si, stackConverterSymb, epsilon, pda.initialState, [pda.initialStackSymbol; stackConverterSymb]) in
			let buildFinalTransitionsToConsumeStack stackAlphabet: transitions =
				Set.map ( fun symbStack -> (sf, symbStack, epsilon, sf, []) ) stackAlphabet
			in
			let buildTrasitionsFromAcceptState acceptState: transitions =
				let symbsStack = getStackSymbols pda.transitions in
					Set.map ( fun symbStack -> (acceptState, symbStack, epsilon, sf, [symbStack])) symbsStack
			in
			let buildTransitions states: transitions = Set.flatten (Set.map buildTrasitionsFromAcceptState pda.acceptStates) in
				Set.union (Set.add initialTrsn (buildTransitions pda.states)) (buildFinalTransitionsToConsumeStack newStackAlphabet)
		in
		let convertedPda: t = {
			inputAlphabet = pda.inputAlphabet;
			stackAlphabet = newStackAlphabet;
			states = Set.union (pda.states) (Set.make [state "Si"; state "Sf"]);
			initialState = state "Si";
			initialStackSymbol = stackConverterSymb;
			transitions = Set.union (pda.transitions) (buildNewTransitions (state "Si") (state "Sf"));
			acceptStates = Set.empty;
			criteria = false
			}
		in
			if pda.criteria then convertedPda else pda

	let pda2fa pda: FiniteAutomaton.model =
		let transitionsFa trns = Set.map ( fun (s1,_,a,s2,_) -> (s1,a,s2) ) trns in
		let fa: FiniteAutomaton.t = {
				alphabet = pda.inputAlphabet;
				states = pda.states;
				initialState = pda.initialState;
				transitions = transitionsFa pda.transitions;
				acceptStates = pda.acceptStates
			} in
		new FiniteAutomaton.model (Arg.Representation fa)

(* AMD repetido *)
	let fa2pda (fa : FiniteAutomaton.t ): t =
		let upgradeTransitions trns = Set.map ( fun (s1,symb,s2) -> (s1,stackSpecialSymb,symb,s2,[stackSpecialSymb]) ) trns in
			{
				inputAlphabet = fa.alphabet;
				stackAlphabet = Set.make [stackSpecialSymb];
				states = fa.states;
				initialState = fa.initialState;
				initialStackSymbol = stackSpecialSymb;
				transitions = upgradeTransitions fa.transitions;
				acceptStates = fa.acceptStates;
				criteria = true
			}

	let reachable s pda: states =
		let fa : FiniteAutomaton.model = pda2fa pda in
		fa#reachable (s)

	let productive pda: states =
		let pdaTransformed = transformPdaToAcceptStates pda in
		let fa : FiniteAutomaton.model = pda2fa pdaTransformed in
		Set.inter fa#productive pda.states

	let getUsefulStates pda: states =
		let pdaTransformed = transformPdaToAcceptStates pda in
		let fa : FiniteAutomaton.model = pda2fa pdaTransformed in
		Set.inter fa#getUsefulStates pda.states

	let getUselessStates pda: states =
		let pdaTransformed = transformPdaToAcceptStates pda in
		let fa : FiniteAutomaton.model = pda2fa pdaTransformed in
		Set.inter fa#getUselessStates pda.states


	let cleanUselessStates pda: t =
		let getEquivalentTransitions (s1,sym,s2) =
			Set.filter (fun (a,b,c,d,e) -> a = s1 && c = sym && d = s2 ) pda.transitions in
		let getCleanedTransitions faCleanedTransitions =
			Set.flatMap getEquivalentTransitions faCleanedTransitions in
		let pdaTransformed = transformPdaToAcceptStates pda in
		let fa : FiniteAutomaton.model = pda2fa pdaTransformed in
		let faClean: FiniteAutomaton.model = fa#cleanUselessStates in
			{
				inputAlphabet = pda.inputAlphabet;
				stackAlphabet = pda.stackAlphabet;
				states = Set.inter faClean#representation.states pda.states;
				initialState = pda.initialState;
				initialStackSymbol = pda.initialStackSymbol;
				transitions = getCleanedTransitions faClean#representation.transitions;
				acceptStates = Set.inter fa#representation.acceptStates pda.acceptStates;
				criteria = pda.criteria
			}

(*trocar para a positiva AMD*)
	let isDeterministic pda: bool =

		(*returns the trasitions for a given state, stackSymbol and inputSymbol, including epsilon transitions*)
		let trnsFromStateAndSymbs st stackSymb inputSymb =
			Set.filter (fun (s1,stackS,symb,_,_) -> (st = s1) && (stackSymb = stackS) && (symb = inputSymb || symb = epsilon)) pda.transitions
		in

		(*Validates if there is more than one transition possible for a given state, stackSymbol*)
		let isnotDeterministicForStateAndStackSymbol st stackSymb =
			Set.exists (fun symb -> Set.size (trnsFromStateAndSymbs st stackSymb symb) > 1) pda.inputAlphabet
		in

		(*Validates if a state is non deterministic*)
		let isStateNonDeterministic st =
			Set.exists (fun stackSymb -> isnotDeterministicForStateAndStackSymbol st stackSymb) pda.stackAlphabet
		in
			not (Set.exists (fun st -> isStateNonDeterministic st) pda.states)

	let isFiniteAutomaton pda: bool =
		let validateTransition (_,a,_,_,b) = [a] = b in
			Set.for_all validateTransition pda.transitions	
end

module PushdownAutomatonJoao =
struct
	open PushdownAutomatonSupport
	open PushdownAutomatonPrivate

	(*CODIGO JP*)
	
	type path_ = configuration_ list
	type trail = configurations_ list


	let initialConfigs (pda: t) (w: word) : configurations_ =
			Set.make [(pda.initialState, [pda.initialStackSymbol], w)]

	let nextConfigs (pda: t) (st, sa, w) : configurations_ =
	let stackLeft = List.tl sa in
	let stackTop = List.hd sa in
	match w with
	| [] ->
		let empty = Set.filter(fun (st1, sa1, sy, _, _)->
			st1 = st && sy = epsilon && sa1 = stackTop
			) pda.transitions in 
				Set.map (fun (_,_,_,st2, sa2) -> (st2, sa2@stackLeft, [])) empty
	| x :: xs ->
		let nonEmpty = Set.filter (fun (st1, sa1, sy, _, _) ->
			st1 = st && sy = x && sa1 = stackTop
			) pda.transitions
		in
		let empty = Set.filter(fun (st1, sa1, sy, _, _)->
			st1 = st && sy = epsilon && sa1 = stackTop
			) pda.transitions 
		in
		let res1 = Set.map (fun (_, _, _, st2, sa2) -> 
			(st2, sa2@stackLeft, xs)
			) nonEmpty in
		let res2 = Set.map (fun (_, _, _, st2, sa2) -> 
			(st2, sa2@stackLeft, w)
			) empty in
		Set.union res1 res2

	let isAcceptingConfig (pda: t) (st, sa, w) : bool =
		if (pda.criteria) then (
				 w = [] && Set.belongs st pda.acceptStates
		)
		else (w = [] && sa = [])

	let nextConfigs2 pda (len: int) (st, sa, w) = 
		let stackTop = List.hd sa in
		let stackLeft = List.tl sa in
			let selected = Set.filter (fun (st1, sa1, _, _, _) -> 
				st1 = st && sa1 = stackTop) pda.transitions in
			Set.map (fun (_, _, sy, st2, sa2) -> (st2, sa2@stackLeft, if sy = epsilon then w else sy::w)) selected

	let isAcceptingConfig2 pda (st, sa, _) =
		if (pda.criteria) then Set.belongs st pda.acceptStates else sa = []

	let accept (pda: t) (w: word) : bool =
		Model.accept pda w initialConfigs nextConfigs isAcceptingConfig
	
	let acceptFull (pda: t) (w: word) : bool * path_ * trail =
		Model.acceptFull pda w initialConfigs nextConfigs isAcceptingConfig

	let getWord (_, _, w) = List.rev w;;

	let generate (pda: t) (len: int): words =
		Model.generate pda len initialConfigs nextConfigs2 isAcceptingConfig2 getWord

	(*generate*)
	
end

module PushdownAutomaton =
struct
	include PushdownAutomatonSupport
	include PushdownAutomatonPrivate

	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
	let make (arg: t Arg.alternatives): t = make arg validate

	(* Exercices support *)
	let checkProperty (pda: t) (prop: string) =
		match prop with
			| "true" -> true
			| _ -> Model.checkProperty prop
	let checkExercise ex pda = Model.checkExercise ex (accept pda) (checkProperty pda)	
	let checkExerciseFailures ex pda = Model.checkExerciseFailures ex (accept pda) (checkProperty pda)

	(* Ops *)
	let accept = accept
	let generate = generate	
	
	(* Class *)
	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model (make2 arg) as super
		(* Representation *)
			method representation: t = representation
		(* Kind *)
			method isPushdownAutomaton : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Ops *)
			method accept (w: word): bool = accept representation w
			method acceptFull (w: word) : bool * PushdownAutomatonJoao.path_ * PushdownAutomatonJoao.trail = 
				PushdownAutomatonJoao.acceptFull representation w
			method generate (length: int): words = generate length representation
			method generateUntil (length: int): words = generateUntil length representation
			method getSearchTree (w: word): searchTree = getSearchTree w representation
			method getBestPath (w: word): path = getBestPath w representation

			method getConfigsPathBySymbolConsumedAndBestPath word: configurations list * path =
				getConfigsPathBySymbolConsumedAndBestPath word representation

			method transformPdaToAcceptStates: model =
				let pda = transformPdaToAcceptStates representation in
					new model (Arg.Representation pda)

			method transformPdaToAcceptEmptyStack: model =
				let pda = transformPdaToAcceptEmptyStack representation in
					new model (Arg.Representation pda)

			method reachable (s: state): states = reachable s representation
			method productive: states = productive representation
			method getUsefulStates: states = getUsefulStates representation
			method getUselessStates: states = getUselessStates representation
			method cleanUselessStates: model =
				let pda = cleanUselessStates representation in
					new model(Arg.Representation pda)
			method areAllStatesUseful: bool =
				let usefullStates = self#getUsefulStates in
					Set.size representation.states = Set.size usefullStates
			method isDeterministic: bool = isDeterministic representation
			method isFiniteAutomaton: bool = isFiniteAutomaton representation
		(* Exercices support *)
			method checkProperty (prop: string) = Util.println["WWW"]; checkProperty representation prop
		(* Learn-OCaml support *)
			method moduleName = moduleName
			method xTypeName = xTypeName
			method xTypeDeclString : string = prelude
			method toDisplayString (name: string): string = solution name self#representation
			method example : JSon.t = example
	end
end


# 3 "src/TuringMachineSupport.ml"
(*
 * TuringMachineSupport.ml
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
 * jan/2025 (amd) - Code improved and adjusted for multitape.
 * jun/2022 (amd) - New module.
 *)

(*
 * Description: Types and functions supporting multitape TMs.
 *)

open BasicTypes

module TuringMachineBasics =
struct
	type symbolM = symbol list
	type directionM = direction list
	type transition  = state * symbolM * state * symbolM * directionM
	type transitions = transition set

	type t = {
		entryAlphabet: symbols;
		tapeAlphabet: symbols;
		empty: symbol;
		states: states;
		initialState: state;
		transitions: transitions;
		acceptStates: states;
		criteria: bool; (* true = acceptStates | false = stop *)
		lbMarkers: symbol list;
		_nTapes: int
	}

	type halfTape = symbol list
	type tape = halfTape * halfTape
	type tapes = tape list
	type configuration = state * tapes
	type configurations = configuration set

	type path = configuration BasicTypes.path
	type trail = configuration BasicTypes.trail

	let kind = "turing machine"

	let tm_zero: t = {
		entryAlphabet = Set.empty;
		tapeAlphabet = Set.make [empty];	
		empty = empty;
		states = Set.make [draftState];
		initialState = draftState;
		transitions = Set.empty;
		acceptStates = Set.empty;
		criteria = false;
		lbMarkers = [];
		_nTapes = 1
	}
	
	let nTapes (tm: t): int =
		tm._nTapes

	let multi (tm: t) x =
		List.init (nTapes tm) (fun _-> x)

	let lbLeft (tm: t) =
		List.nth tm.lbMarkers 0

	let lbRight (tm: t) =
		List.nth tm.lbMarkers 1

	let calcNTapes (ts: transitions): int =
		Set.match_ ts
			(fun () -> 1)
			(fun (_,b,_,_,_) _ -> List.length b)

	let getTransSymbolMs (rep: t): symbolM set =
		let trns = rep.transitions in
		let trns2 = Set.map (fun (_,b,_,_,_) -> b) trns in
		let trns4 = Set.map (fun (_,_,_,d,_) -> d) trns in
			Set.union trns2 trns4

	let getTransSymbols (rep: t): symbols =
		Set.flatten (Set.map Set.make (getTransSymbolMs rep))

	let getTransDirectionMs (rep: t): directionM set =
		Set.map (fun (_,_,_,_,e) -> e) rep.transitions
		
	let getTransDirections (rep: t): direction set =
		Set.flatten (Set.map Set.make (getTransDirectionMs rep))
		end

module TuringMachineJSon =
struct
	open JSon
	open TuringMachineBasics

	let asDirection (j: JSon.t) (field: string): direction =
		match j with
		| JString "L" -> L
		| JString "S" -> S
		| JString "R" -> R
		| _ -> error field "Expected L|S|R" dummyDirection

	let asOptionalDirectionList (j: JSon.t) (field: string): direction list =
		match j with
		| JList l -> List.map (fun j -> asDirection j field) l
		| JString _ -> [asDirection j field]
		| _ -> error field "Expected direction list" []

	let dummyTransition = (
		dummyState,[dummySymb],dummyState,[dummySymb],[dummyDirection]
	)
	
	let asOptionalSymbolList (j: JSon.t) (field: string): symbol list =
		match j with
		| JList l -> List.map (fun j -> asSymbol j field) l
		| JString _ -> [asSymbol j field]
		| _ -> error field "Expected transition symbols" []
	
	let asTransition (j: JSon.t) (field: string): transition =
		match j with
		| JList [a; b; c; d; e] ->
			(	asState a field,
				asOptionalSymbolList b field,
				asState c field,
				asOptionalSymbolList d field,
				asOptionalDirectionList e field
			)
		| _ -> error field "Malformed TM transition" dummyTransition

	let fieldTMTransitionList (j: JSon.t) (field: string): transition list =
		match j |> getField field with
		| JNull -> Error.error field "Missing field" []
		| JList l -> List.map (fun j -> asTransition j field) l
		| _ -> []

	let fieldTransitions (j: JSon.t) (field: string): transitions  =
		Set.validate (fieldTMTransitionList j field) field

	let makeTransitions (s: transitions): JSon.t =
		JList (List.map (fun (a,b,c,d,e) ->
							JList [	JString (state2str a);
									JList (List.map (fun s -> JString (symb2str s)) b);
									JString (state2str c);
									JList (List.map (fun s -> JString (symb2str s)) d);
									JList (List.map (fun d -> JString (dirX d)) e)
							]) (Set.toList s))

end

module TuringMachineConversions =
struct
	open TuringMachineBasics

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			tm_zero
		else
			let ts = TuringMachineJSon.fieldTransitions j "transitions" in
			{
			entryAlphabet = JSon.fieldSymbolSet j "entryAlphabet";
			tapeAlphabet = JSon.fieldSymbolSet j "tapeAlphabet";
			empty = JSon.fieldSymbol j "empty";
			states = JSon.fieldStateSet j "states";
			initialState = JSon.fieldState j "initialState";
			transitions = ts;
			acceptStates = JSon.fieldStateSet j "acceptStates";
			criteria = JSon.fieldBool j "criteria";
			lbMarkers = if JSon.hasField j "markers" then	(* optional *)
							JSon.fieldSymbolList j "markers"
						else [];
			_nTapes = calcNTapes ts
			}

	let toJSon0 (tm: t): JSon.t =
		JSon.makeAssoc [
			("entryAlphabet", JSon.makeSymbolSet tm.entryAlphabet);
			("tapeAlphabet", JSon.makeSymbolSet tm.tapeAlphabet);
			("empty", JSon.makeSymbol tm.empty);
			("states", JSon.makeStateSet tm.states);
			("initialState", JSon.makeState tm.initialState);
			("transitions", TuringMachineJSon.makeTransitions tm.transitions);
			("acceptStates", JSon.makeStateSet tm.acceptStates);
			("criteria", JSon.makeBool tm.criteria);
			("lbMarkers", JSon.makeSymbolList tm.lbMarkers);
		]	

	let toJSon2 (id: Entity.t) (tm: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 tm)
	
	let toJSon (tm: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) tm
end

module TuringMachineBasicFunctions =
struct
	open TuringMachineBasics
	open TuringMachineConversions

	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (tm: t): unit =
		let j = toJSon tm in
			JSon.show j

	let show2 (id: Entity.t) (tm: t): unit =
		let j = toJSon2 id tm in
			JSon.show j
end

module TuringMachineX =
struct
	open TuringMachineBasics

	type symbolXM = symbolX list
	type directionXM = string list
	type transitionX  = state * symbolXM * state * symbolXM * directionXM

	type tapeX = string * string
	type tapesX = tapeX list
	type configurationX = state * tapesX
	type configurationsX = configurationX list

	type tx = {
		entryAlphabet: symbolX list;
		tapeAlphabet: symbolX list;
		empty: symbolX;
		states: state list;
		initialState: state;
		transitions: transitionX list;
		acceptStates: state list;
		criteria: bool;
		lbMarkers: symbolX list;
	}

	let transI (a,b,c,d,e): transition =
		(a, List.map symbI b, c, List.map symbI d, List.map dirI e)
	let transX (a,b,c,d,e): transitionX =
		(a, List.map symbX b, c, List.map symbX d, List.map dirX e)

	let tmI (tmx: tx): t =
		let ts = Set.make (List.map transI tmx.transitions) in {
			entryAlphabet = symbolsI tmx.entryAlphabet;
			tapeAlphabet = symbolsI tmx.tapeAlphabet;	
			empty = symbI tmx.empty;	
			states = Set.make tmx.states;
			initialState = tmx.initialState;
			transitions = ts;
			acceptStates = Set.make tmx.acceptStates;
			criteria = tmx.criteria;
			lbMarkers = List.map symbI tmx.lbMarkers;
			_nTapes = calcNTapes ts
		}

	let tmX (tm: t): tx = {
		entryAlphabet = symbolsX tm.entryAlphabet;
		tapeAlphabet = symbolsX tm.tapeAlphabet;	
		empty = symbX tm.empty;
		states = Set.toList tm.states;
		initialState = tm.initialState;
		transitions = Set.toList (Set.map transX tm.transitions);
		acceptStates = Set.toList tm.acceptStates;
		criteria = tm.criteria;
		lbMarkers = List.map symbX tm.lbMarkers;
	}
	
	let confX ((s,tapes): configuration): configurationX =
		let tsx = List.map (fun (l,r) ->
				(word2str (List.rev l), word2str r)) tapes in
			(s, tsx)		
	let confsX (c: configurations): configurationsX =
		List.map confX (Set.toList c)

	let pathX (p: path): configurationX pathX = pathX confX p
	let trailX (t: trail): configurationX trailX = trailX confX t
end

module TuringMachineS =
struct
	open TuringMachineBasics
	
	let pairS (a: string) (b: string): string =
		"(" ^ a ^ ", " ^ b ^ ")"
	let wordS (w: word): string = 
		wordX w
	let listS (l: string list): string =
		"[" ^ String.concat ", " l ^ "]" 
	let setS (s: string Set.t): string =
		"{" ^ String.concat ", " (Set.toList s) ^ "}" 
	let confS ((s,tapes): configuration): string =
		let tsx = List.map (fun (l,r) ->
				pairS (wordS (List.rev l)) (wordS r)) tapes in
			pairS s (listS tsx)		

	let confsS (confS: 'config -> string) (c: configurations): string =
		setS (Set.map confS c)

	let confsS (c: configurations): string =
		confsS confS c





	let pathS (configS: 'config -> string) (p: 'config BasicTypes.path): string =
		listS (List.map configS p)
	
	let pathS (p: path): string = pathS confS p
	
end


module TuringMachineLearnOCaml =
struct
	open TuringMachineBasics
	open TuringMachineX
end

module TuringMachineSupport =
struct
	include TuringMachineBasics
	include TuringMachineConversions
	include TuringMachineBasicFunctions
	include TuringMachineLearnOCaml
end

# 1 "src/TuringMachine.ml"
(*
 * TuringMachine.ml
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
 *  Written by Miguel Lourenço (ml)
 *)

(*
 * ChangeLog:
 *
 * jan/2025 (amd) - Adapted for multitape TMs and also reorganized.
 * ???/2023 (ml) - Implementation of singletape TMs.
 * jun/2022 (amd) - Initial skeleton.
 *)

(*
 * Description: Multi-tape Turing machine functionality.
 *)

open BasicTypes

module TuringMachineAcceptPrivate =
struct
	open TuringMachineSupport

	let initialConfigs (tm: t) (w: word): configurations =
		let n = nTapes tm in
		let emptyTape = ([empty], [empty]) in
		let firstTape = ([empty], w@[empty]) in
		let emptyTapes = List.init (n-1) (fun _ -> emptyTape) in
		let conf = (tm.initialState, firstTape::emptyTapes) in
			Set.make [conf]

	let getCurr (ps: tapes): symbolM =
		List.map (fun (l,r) -> List.hd r) ps
	
	let isAcceptingConfig (tm: t) ((s,ps): configuration): bool =
		let curr = getCurr ps in
		let ts = tm.transitions in
		let triggered = Set.filter (fun (a,b,_,_,_) -> a = s && b = curr) ts in
		let stops = Set.isEmpty triggered in
			if tm.criteria then
				stops && Set.belongs s tm.acceptStates
			else
				stops

	let fix (p: halfTape): halfTape =	
		match p with
		| [] -> [empty]
		| _ -> p

	let updateTape (p: tape) (d: symbol) (e: direction): tape =
		match p with
		| l::ls, _::rs ->
			(match e with
			| R -> (d::l::ls, fix rs)
			| L -> (fix ls, l::d::rs)
			| S -> (l::ls, d::rs))
		| _, _ -> failwith "nextTape"
	
	let rec map3 f l l1 l2 =
		match l, l1, l2 with
		| [], [], [] -> []
		| x::xs, y::ys, z::zs -> f x y z:: map3 f xs ys zs
		| _, _, _ -> failwith "map3"

	let nextConfig (tm: t) (tr: transition) (conf: configuration): configurations =
		match tr, conf with
		| (a,b,c,d,e), (s,ps) when a = s && b = getCurr ps ->
			let ps2 = map3 updateTape ps d e in
				Set.make [(c, ps2)]
		| _, _ -> Set.empty

	let nextConfigs (tm: t) (config: configuration): configurations = 
		Set.flatMap (fun tr -> nextConfig tm tr config) tm.transitions

	let accept (tm: t) (w: word): bool =
		Model.checkWord tm.entryAlphabet w
		&&
		Model.accept tm w
				initialConfigs
				nextConfigs
				isAcceptingConfig

	let acceptFull (tm: t) (w: word): bool * path * trail = 
		if Model.checkWord tm.entryAlphabet w then
			Model.acceptFull tm w
						initialConfigs nextConfigs isAcceptingConfig
		else
			(false, [], [])
end

module TuringMachineGeneratePrivate =
struct
	open TuringMachineSupport
	open TuringMachineAcceptPrivate

	let generate (tm: t) length =
		Model.generateDumb tm tm.entryAlphabet
				length initialConfigs nextConfigs isAcceptingConfig
end

module TuringMachineLBPrivate =
struct
	open TuringMachineSupport
	open TuringMachineAcceptPrivate

	let isLB (rep: t) = 
		List.length rep.lbMarkers = 2

	let validateLB (name: string) (rep: t) =
		(* pre: List.length rep.lbMarkers > 0 && validMarkers *)
		let lbMarkers = Set.make rep.lbMarkers in
		
		let inEntryAlph =
			Set.subset lbMarkers rep.entryAlphabet in
	
		let validSymbolM (s: symbolM) =
			let t = Set.make s in
			let i = Set.inter t lbMarkers in
			let withoutMarker =  Set.isEmpty i in
				withoutMarker || Set.size t = 1 in
		
		let validSymbolMs =
			Set.for_all validSymbolM (getTransSymbolMs rep) in
			
		let isLeftSafe  =
			let leftM = multi rep (lbLeft rep) in
			let lM = multi rep L in
			let safeT (_,b,_,d,e) = b <> leftM || (d = leftM && e <> lM) in
				Set.for_all safeT rep.transitions in

		let isRightSafe =
			let rightM = multi rep (lbRight rep) in
			let rM = multi rep R in
			let safeT (_,b,_,d,e) = b <> rightM || (d = rightM && e <> rM) in
				Set.for_all safeT rep.transitions in

		if not inEntryAlph then
			Error.error name
				"The LB markers must belong to the entry alphabet" ()
		;	
		if not validSymbolMs then	
			Error.error name
				"Each LB marker cannot be mixed with other symbols in a transition" ()
		;
		if not isLeftSafe then
			Error.error name
				"Some transition does not respect the left mark" ()
		;
		if not isRightSafe then
			Error.error name
				"Some transition does not respect the right mark" ()

	let checkLB rep: bool =
		let ok = isLB rep in
		let mesg = "Not a LB Turing machine" in
			if not ok then Error.warning mesg;
			ok

	let acceptLB w rep =
		checkLB rep
		&&
		accept rep ([lbLeft rep]@w@[lbRight rep])

	let acceptFullLB w rep =
		if checkLB rep then
			acceptFull rep ([lbLeft rep]@w@[lbRight rep])
		else
			(false, [], [])
end

module TuringMachinePrivate =
struct
	open TuringMachineSupport

(*
	let getDefaultMachine: t = {
		entryAlphabet = Set.empty;
		tapeAlphabet = Set.add empty Set.empty;	
		empty = empty;
		states = Set.add "START" Set.empty;
		initialState = "START";
		transitions = Set.empty;
		acceptStates = Set.empty;
		criteria = false;
		lbMarkers = Set.empty
	}
*)

	let validate (name: string) (rep: t) =
		let trns = rep.transitions in
		let trns1 = Set.map (fun (a,_,_,_,_) -> a) trns in
		let trns2 = Set.map (fun (_,b,_,_,_) -> b) trns in
		let trns3 = Set.map (fun (_,_,c,_,_) -> c) trns in
		let trns4 = Set.map (fun (_,_,_,d,_) -> d) trns in
		let trns5 = Set.map (fun (_,_,_,_,e) -> e) trns in
		let alpha = Set.add empty rep.tapeAlphabet in
		
		let validInitSt =
			Set.belongs rep.initialState rep.states in
		let validAccSts =
			Set.subset rep.acceptStates rep.states in

		let validEntryAlph =
			Set.subset rep.entryAlphabet rep.tapeAlphabet in	
		let emptyInAlph =
			Set.belongs empty rep.tapeAlphabet
			&& not (Set.belongs empty rep.entryAlphabet) in
		let emptyIsEmpty =
			rep.empty = empty in
			
		let nTapes = nTapes rep in
		
		let validLengths =
			Set.for_all (fun s -> List.length s = nTapes) trns2
			&& Set.for_all (fun s -> List.length s = nTapes) trns4
			&& Set.for_all (fun s -> List.length s = nTapes) trns5 in

		let validTrns =
			Set.subset trns1 rep.states
			&& Set.subset trns3 rep.states
			&& Set.subset (getTransSymbols rep) alpha
			&& Set.subset (getTransDirections rep) allDirections in

		let validMarkers =
			if List.length rep.lbMarkers = 2 then
				let l = List.nth rep.lbMarkers 0 in
				let r = List.nth rep.lbMarkers 1 in
					l <> r
			else
				List.length rep.lbMarkers = 0 in

		let validCriteria =
			rep.criteria || Set.size rep.acceptStates = 0 in

		if not validInitSt then
			Error.error name
				"The initial state does not belong to the set of all states" ()
		;
		if not validAccSts then
			Error.error name
				"Some accept states do not belong to the set of all states" ()
		;
		if not validEntryAlph then
			Error.error name
				"The entry alphabel must be contained in the tape alphabet" ()
		;
		if not validLengths then
			Error.error name
				"Some transitions have elements with inconsistent lengths" ()
		;
		if not validTrns then
			Error.error name
				"Some transitions are invalid" ()
		;
		if not emptyInAlph then
			Error.error name (
				"The empty symbol must be in the tape alphabet"
				^ " but not in the entry alphabet") ()
		;
		if not emptyIsEmpty then
			Error.error name
				"The empty symbol is not correct, change it to 'B'" ()
		;
		if not validCriteria then
			Error.error name
				"A TM that uses the stop criteria cannot have accept states" ()
		;
		if List.length rep.lbMarkers > 0 && validMarkers then
			TuringMachineLBPrivate.validateLB name rep

	let downgradeModelToFiniteAutomaton rep = 
		let alphaB = Set.union (Set.make [empty]) rep.tapeAlphabet in
		let transitionsTm2Fa = Set.map (fun (a,b,c,_,_) -> (a,List.hd b,c)) in
		let fa: FiniteAutomaton.t = {
				alphabet = alphaB;
				states = rep.states;
				initialState = rep.initialState;
				transitions = transitionsTm2Fa rep.transitions;
				acceptStates = rep.acceptStates
			} in
		new FiniteAutomaton.model (Arg.Representation fa)

	let reachable s rep = 
		let fa = downgradeModelToFiniteAutomaton rep in
			fa#reachable s

	let productive rep =
		if rep.criteria then
			let fa = downgradeModelToFiniteAutomaton rep in
				fa#productive
		else rep.states
		
	let getUsefulStates rep =
		Set.inter (productive rep) (reachable rep.initialState rep)

	let getUselessStates rep =
		Set.diff rep.states (getUsefulStates rep)

	let isDeterministic rep =
		let fa = downgradeModelToFiniteAutomaton rep in
			fa#isDeterministic

	let cleanUselessStates rep =
		let ts = rep.transitions in
		let usfSts = getUsefulStates rep in
		let usfTrs = Set.filter (fun (a,_,c,_,_)
				-> Set.belongs a usfSts && Set.belongs c usfSts) ts in
		let tapeAlf = Set.add empty (getTransSymbols rep) in
		let entryAlf = Set.inter tapeAlf rep.entryAlphabet in
		let newAccSts = Set.inter rep.acceptStates usfSts in
			{ rep with
				entryAlphabet = entryAlf;
				tapeAlphabet = tapeAlf;
				states = usfSts;
				transitions = usfTrs;
				acceptStates = newAccSts }
			(* This and all the other updates of a TM need
				to be analysed, to check for the validity
				of the resulting TM. - AMD  *)

	let areAllStatesUseful rep =
		let fa = downgradeModelToFiniteAutomaton rep in
			fa#areAllStatesUseful

(*	let convertToStopCriteria rep =
		let stEnd = state "END" in
		let endState = stEnd in
		let completeStates = Set.union (rep.states) (Set.make [endState]) in

		let newAlph = Set.union (rep.tapeAlphabet) (Set.make [empty]) in
		let nonAcceptStates =  Set.filter (fun x -> not (Set.exists (fun y -> y = x) rep.acceptStates)) rep.states in

		let missingSymbols st = Set.filter (fun x -> not (Set.exists (fun (a,b,_,_,_) -> a = st && b = x) rep.transitions)) newAlph in
		let createTransitions st = Set.map (fun x -> (st,x,endState,x,R)) (missingSymbols st) in
		let newTransList = Set.flatten (Set.map (fun x -> createTransitions x) nonAcceptStates) in
		let fullTransitions = Set.union (rep.transitions) (newTransList) in
			{
				entryAlphabet = rep.entryAlphabet;
				tapeAlphabet = rep.tapeAlphabet;
				empty = rep.empty;
				states = completeStates;
				initialState = rep.initialState;
				transitions = fullTransitions;
				acceptStates = Set.empty;
				criteria = false;
				lbMarkers = rep.lbMarkers
			}
*)

	let convertToStopCriteria rep =
		{ rep with
			acceptStates = Set.empty;
			criteria = false }

	let hasState st rep = 
		Set.belongs st rep.states

	let hasTransition trs rep =
		Set.belongs trs rep.transitions

	let isFinal st rep = 
		Set.belongs st rep.acceptStates

	let isInitial st rep = 
		st = rep.initialState
	
	let addState s rep =
		{ rep with
			states = Set.add s rep.states }
			
	let addInitialState s rep =
		{ rep with
			states = Set.add s rep.states;
			initialState = s }

	let addFinalState s rep =
		{ rep with
			states = Set.add s rep.states;
			acceptStates = Set.add s rep.acceptStates;
			criteria = true }

	let removeState s rep =
		if s = rep.initialState then
			rep
		else
		{ rep with
			states = Set.remove s rep.states;
			transitions = Set.filter (fun (a,_,c,_,_) ->
							a <> s || c <> s) rep.transitions;
			acceptStates = Set.remove s rep.acceptStates }

	let changeStateToInitial s rep =
		{ rep with
			initialState = s }

	let changeStateFromFinal s rep =
		let newAcceptSts = Set.remove s rep.acceptStates in
		{ rep with
			acceptStates = newAcceptSts;
			criteria = Set.size newAcceptSts <> 0 }

	let changeStateToFinal s rep =
		{ rep with
			acceptStates = Set.add s rep.acceptStates;
			criteria = true }

	let renameState st name rep =
		let initial = if st = rep.initialState then name else rep.initialState in
		let newStates = Set.remove st (Set.add name rep.states) in
		let newTransitions = Set.map
					(fun (s,a,t,b,c) -> 
						if s = st && t = st then (name,a,name,b,c)
						else if s = st then (name,a,t,b,c)
						else if t = st then (s,a,name,b,c)
						else (s,a,t,b,c)
					) rep.transitions in
		let newAcceptStates =
			Set.map (fun s -> if s = st then name else s) rep.acceptStates in
				{ rep with
					states = newStates;
					initialState = initial;
					transitions = newTransitions;
					acceptStates = newAcceptStates;
					criteria = true }

	let addTransition trs rep =
		{ rep with
			transitions = Set.add trs rep.transitions }

	let removeTransition trs rep =
		{ rep with
			transitions = Set.remove trs rep.transitions }
end

module TuringMachine =
struct
	include TuringMachineSupport
	open TuringMachineAcceptPrivate
	open TuringMachineGeneratePrivate
	open TuringMachineLBPrivate
	open TuringMachinePrivate

	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
	let make (arg: t Arg.alternatives): t = make arg validate

	(* Exercices support *)
	let checkProperty (tm: t) (prop: string) =
		match prop with
			| "turing machine" -> true
			| _ -> Model.checkProperty prop		
	let checkExercise ex (tm: t) = Model.checkExercise ex (accept tm) (checkProperty tm)
	let checkExerciseFailures ex (tm: t) = Model.checkExerciseFailures ex (accept tm) (checkProperty tm)

	(* Ops *)
	let stats = Model.stats
	let accept = accept
	let acceptFull = acceptFull
	let generate = generate
	let isLB = isLB
	let initialConfigs = initialConfigs

	(* Class *)
	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model (make2 arg) as super
		(* Representation *)
			method representation: t = representation
		(* Kind *)
			method isTuringMachine : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Ops *)				
			method accept (w: word): bool =
				accept representation w

			method acceptFull (w:word): bool * 'c list * 'c set list =
				acceptFull representation w

			method generate (length: int): words =
				generate representation length

			method reachable (s:state): states =
				reachable s representation

			method productive : states =
				productive representation
				
			method getUsefulStates: states =
				getUsefulStates representation

			method getUselessStates: states =
				getUselessStates representation

			method isDeterministic: bool =
				isDeterministic representation

			method cleanUselessStates: t =
				cleanUselessStates representation

			method areAllStatesUseful: bool =
				areAllStatesUseful representation

			method acceptLB (w: word) : bool =
				acceptLB w representation

			method acceptFullLB (w: word) : bool * 'c list * 'c set list =
				acceptFullLB w representation

			method isLB : bool = 	
				isLB representation

			method convertToStopCriteria: model =
				let tm = convertToStopCriteria representation in
					new model (Arg.Representation tm)

			method hasState(s: state): bool =
				hasState s representation

			method hasTransition (trs: transition): bool =
				hasTransition trs representation

			method isFinal (st: state): bool =
				isFinal st representation

			method isInitial (st: state): bool =
				isInitial st representation

			method addState (s: state) : t =
				addState s representation

			method addInitialState (s: state) : t =
				addInitialState s representation

			method addFinalState (s: state) : t =
				addFinalState s representation
		
			method removeState (s: state) : t =
				removeState s representation

			method changeStateToInitial (s: state) : t =
				changeStateToInitial s representation

			method changeStateToFinal (s: state) : t =
				changeStateToFinal s representation

			method changeStateFromFinal (s: state) : t =
				changeStateFromFinal s representation
			
			method renameState (s:state) (newS:state): t =
				renameState s newS representation

			method addTransition (trs:transition) : t =
				addTransition trs representation

			method removeTransition (trs:transition) : t =
				removeTransition trs representation

			method downgradeModelToFiniteAutomaton: FiniteAutomaton.model =
				downgradeModelToFiniteAutomaton representation
			
			method checkProperty prop =
				match prop with
					| "deterministic" -> self#isDeterministic
					| "linear bounded" -> self#isLB
					| "acceptance by states" -> representation.criteria
					| "acceptance by stop" -> not representation.criteria
					| "turing machine" -> true
					| _ -> super#checkProperty prop
		
		(* Learn-OCaml support *)
		(* incomplete *)
			method moduleName =
				"TuringMachine"

			method xTypeName =
				"turingMachine"
				
			method xTypeDeclString : string = "todo"

			method toDisplayString (name: string): string = "todo"

			method example : JSon.t =
				JSon.parse {|
				{
					kind : "turing machine todo"
				}
			|}

	end

end

module TuringMachineTop =
struct
	open TuringMachine
	open TuringMachineX

	let tm_load file = tmX (make (Arg.File file))
	let tm_text text = tmX (make (Arg.Text text))
	let tm_json json = tmX (make (Arg.JSon json))
	let tm_predef name = tm_text (Examples.example name)

	let tm_ntapes tmx =
		nTapes (tmI tmx)

	let tm_init tmx w =
		let is = initialConfigs (tmI tmx) (wordI w) in
			confsX is

	let stats () = RuntimeControl.stats ()

	let tm_accept tm w = accept (tmI tm) (wordI w)

	let tm_path tm w =
		let (r,p,t) = acceptFull (tmI tm) (wordI w) in
			pathX p

	let tm_trail tm w =
		let (r,p,t) = acceptFull (tmI tm) (wordI w) in
			trailX t

	let tm_generate tm len = wordsX (generate (tmI tm) len)


	open TuringMachineS
	let tm_init tmx w =
		let is = initialConfigs (tmI tmx) (wordI w) in
			confsS is

end

open TuringMachineTop

(*

--------------------

#print_depth 10000;;
#print_length 10000;;

let tm = tm_predef "tm_translate";;
let w = "aba";;
tm_ntapes tm;;
tm_init tm w;;
tm_accept tm "aba";;
tm_accept tm "abac";;
tm_path tm "aba";;
tm_trail tm "aba";;

--------------------
let tm = tm_predef "tm_astar2";;

tm_generate tm 4;;

tm_accept tm "abab";;
tm_accept tm "abcab";;

tm_path tm "abab";;
tm_path tm "abcab";;

tm_trail tm "abab";;
--------------------

*)
# 1 "src/CompositionSupport.ml"
(*
 * CompositionSupport.ml
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
 * dec/2023 (amd) - Initial version.
 *)

(*
 * Description: Support types and functions for COMPs including a parser for COMPs.
 *)

open BasicTypes

module CompositionBasics =
struct
	type tx = string

	type t =
		| Plus of t * t
		| Seq of t * t
		| Intersect of t * t
		| Star of t
		| FA of FiniteAutomaton.t
		| RE of RegularExpression.t
		| CFG of ContextFreeGrammar.t
		| PDA of PushdownAutomaton.t
		| TM of TuringMachine.t
		| FAO of FiniteAutomaton.model
		| REO of RegularExpression.model
		| CFGO of ContextFreeGrammar.model
		| PDAO of PushdownAutomaton.model
		| TMO of TuringMachine.model
		| Rep of string
		| Comp of t
		| Empty
		| Zero

	let kind = "composition"

	let comp_zero: t =
		Zero
end

module type CompositionSyntaxSig =
sig
	open CompositionBasics
	
	val parse : string -> t
	val toString : t -> string
	val show : t -> unit
end

module CompositionSyntax : CompositionSyntaxSig =
struct
	open Scanner
	open CompositionBasics

	(*	Grammar:
			E -> E + E | E E | E* | c | (E) | ()

		Grammar with priorities:
			E -> I | I ^ E
			I -> T | T + I
			T -> F | F T
			F -> A | A*
			A -> P | c
			P -> (E) | ()
	*)
	let rec parseExp () =
		let i = parseInter () in
			match curr() with
				| '^' -> skip(); Intersect (i, parseExp ())
				| _ -> i

	and parseInter () =
		let t = parseTerm () in
			match curr() with
				| '+' -> skip(); Plus (t, parseInter ())
				| _ -> t

	and parseTerm () =
		let f = parseFactor () in
			match curr() with
				| '(' | '[' -> Seq (f, parseTerm ())
				| _ -> f

	and parseFactor () =
		let a = parseAtom () in
			match curr() with
				| '*' -> skip(); (Star a)
				| _ -> a

	and parseAtom () =
		match curr() with
			| '~' -> skip(); Empty
			| '!' -> skip(); Zero
			| '(' -> skip(); parseParentheses ()
			| '^' | '+' | '*' -> invalid "Invalid use of wildcard\n"
			| ' ' -> invalid "Premature end of expression\n"
			| '[' -> skip(); parseId ()
			| _ -> invalid "invalid expression\n"

	and parseParentheses () =
		let e = parseExp () in begin
			match curr() with
				| ')' -> skip(); e
				| _ -> invalid "Right-parenthesis expected\n"
		end

	and parseId () =
		let e = Rep (getId ()) in begin
			match curr() with
				| ']' -> skip(); e
				| _ -> invalid "Id close-parenthesis expected\n"
		end

	let parse s =
		Scanner.start "CompositionSyntax" s;
		try
			parseExp ()
		with Not_found ->
			Zero

	let rec toStringN n comp =
		match comp with
			| Intersect(l, r) ->
					(if n > 0 then "(" else "") ^
					toStringN 0 l ^ "^" ^ toStringN 0 r
					^ (if n > 0 then ")" else "")
			| Plus(l, r) ->
					(if n > 1 then "(" else "") ^
					toStringN 1 l ^ "+" ^ toStringN 1 r
					^ (if n > 1 then ")" else "")
			| Seq(l, r) ->
					(if n > 2 then "(" else "") ^
					toStringN 2 l ^ toStringN 2 r
					^ (if n > 2 then ")" else "")
			| Star r ->
					toStringN 3 r ^ "*"
			| Rep str -> "[" ^ str ^ "]"
			| Empty -> "~"
			| Zero -> "!"
			| _ -> "?"

	let toString comp =
		toStringN 0 comp

	let show comp =
		Util.println [toString comp]
end

module CompositionConversions =
struct
	open CompositionBasics

	let internalize (comp: tx): t =
		CompositionSyntax.parse comp

	let externalize (comp: t): tx =
		CompositionSyntax.toString comp

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			comp_zero
		else
			let comp = JSon.fieldString j "comp" in
				CompositionSyntax.parse comp

	let toJSon0 (comp: t): JSon.t =
	JSon.makeAssoc [
			("comp", JSon.makeString (CompositionSyntax.toString comp));
		]

	let toJSon2 (id: Entity.t) (comp: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 comp)

	
	let toJSon (rep: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) rep
end


module CompositionBasicFunctions =
struct
	open CompositionBasics
	open CompositionConversions
	
	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (comp: t): unit =
		let j = toJSon comp in
			JSon.show j

	let show2 (id: Entity.t) (comp: t): unit =
		let j = toJSon2 id comp in
			JSon.show j
end

module CompositionLearnOCaml =
struct
	open CompositionBasics

	let moduleName =
		"Composition"

	let xTypeName =
		"composition"

	let solution (name: string) (compx: tx): string =
		Printf.sprintf {zzz|
		%s	%s
		|zzz}	(* please, do not change this line *)
			(FiniteEnumerationLearnOCaml.displayHeader name xTypeName)
			(stateXD compx)

	let prelude : string = {|
		type composition = string
		|}	(* please, do not change this line *)

	let example : JSon.t =
		JSon.parse {| {
			kind : "regular expression",
			description : "this is a simple example",
			name : "comp example",
			comp : "w*+(w+yz)*"
		}
		|}	(* please, do not change this line *)
end

module CompositionSupport =
struct
	include CompositionBasics
	include CompositionSyntax
	include CompositionConversions
	include CompositionBasicFunctions
	include CompositionLearnOCaml
	let makeCompositionRef : (t Arg.alternatives -> t) ref = ref (fun a -> Error.fatal "" )
end

module CompositionSyntaxTests : sig end =
struct
	let active = false

	let test00 () =
		let comp = CompositionSyntax.parse "[a]^[b]" in
			CompositionSyntax.show comp

	let test0 () =
		let comp = CompositionSyntax.parse "[az][b]+~*" in
			CompositionSyntax.show comp

	let test1 () =
		let comp = CompositionSyntax.parse "~(([a]^[b])*([c][d])*)*" in
			CompositionSyntax.show comp

	let runAll =
		if Util.testing active "CompositionSyntax" then begin
			test00 ();
			test0 ();
			test1 ();
		end
end
# 1 "src/PolyModel.ml"
(*
 * PolyModel.ml
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
 *  Written by Various
 *)

(*
 * ChangeLog:
 *
 * apr/2021 (amd) - Several new build functions.
 * jan/2021 (amd) - Created this module, collecting all the operation.
                    involving two or more kinds of models.
                    This allows to got rid of the mutual recursion between
                    modules, allowing storing each module in a different file.
 * dec/2019 (jg) - Initial code, across several modules in file "OCamlFlat.ml".
 *)

(*
 * Description: Poly-model operations.
 *
 * TODO: Cleanup.
 *)
 
open BasicTypes

(********************************************************************)
module RE2FA =
struct
	open RegularExpression
	open FiniteAutomaton

	(*auxiliary var for genName function*)
	let k = ref 0

	(*for each new state, generates a name that will distinguish it from all the other generated states *)
	let genName () =
		let n = !k in
		let () = k:= n + 1 in
			(*easy way of having all single digit state names have a zero before their actual number*)
			let name = if n > 9 then "new_St" ^ (string_of_int n)
						else "new_St0" ^ (string_of_int n) in
				str2state name

	let rec compile (re: RegularExpression.t) : FiniteAutomaton.t =
		match re with
			| Plus(l, r) ->
					let fa1 = compile l in
					let fa2 = compile r in
					let newStart = genName () in
					let newSts = Set.add newStart (Set.union fa1.states fa2.states) in
					let newAccSts = Set.union fa1.acceptStates fa2.acceptStates in
					let newTran1 = (newStart, epsilon, fa1.initialState) in
					let newTran2 = (newStart, epsilon, fa2.initialState) in
					let newTrans = Set.add newTran1 (Set.add newTran2
						(Set.union fa1.transitions fa2.transitions)) in
					let newAlf = Set.union fa1.alphabet fa2.alphabet in
						{alphabet = newAlf; states = newSts; initialState = newStart;
							transitions = newTrans; acceptStates = newAccSts}
			| Seq(l, r) ->
					let fa1 = compile l in
					let fa2 = compile r in
					let ist = fa1.initialState in
					let sts = Set.union fa1.states fa2.states in
					let asts = fa2.acceptStates in
					let newTrns = Set.map (fun x -> (x, epsilon, fa2.initialState) ) fa1.acceptStates in
					let trns = Set.union newTrns (Set.union fa1.transitions fa2.transitions) in
					let alf = Set.union fa1.alphabet fa2.alphabet in
						{alphabet = alf; states = sts; initialState = ist;
							transitions = trns; acceptStates = asts}
			| Star(r) ->
					let fa = compile r in
					let newStart = genName () in
					let newSts = Set.add newStart fa.states in
					let newTrns = Set.map (fun st -> (st, epsilon, newStart)) fa.acceptStates in
					let allNewTrns = Set.add (newStart, epsilon, fa.initialState) (Set.union newTrns fa.transitions) in
						{alphabet = fa.alphabet; states = newSts; initialState = newStart;
							transitions = allNewTrns; acceptStates = Set.make [newStart]}
			| Symb(c) ->
					let newStart = genName () in
					let newAcc = genName () in
					let newSts = Set.make [newStart; newAcc] in
					let newTrn = Set.make [(newStart, c, newAcc)] in
						{alphabet = Set.make [c]; states = newSts; initialState = newStart;
							transitions = newTrn; acceptStates = Set.make [newAcc]}
			| Empty ->
					let newStart = genName () in
							{alphabet = Set.empty; states = Set.make [newStart]; initialState = newStart;
								transitions = Set.empty; acceptStates = Set.make [newStart]}
			| Zero ->
					let newStart = genName () in
						{alphabet = Set.empty; states = Set.make [newStart]; initialState = newStart;
								transitions = Set.empty; acceptStates = Set.empty}
	
	let re2fa (re: RegularExpression.t): FiniteAutomaton.t =
		compile re
end

(********************************************************************)
module FA2RE =
struct
	open FiniteAutomaton
	open RegularExpression

	(* transforms the set of expressions into the regex: plus of all expressions of the set *)
	let plusSet reSet =
		let rec pls l =
			match l with
				[] -> Zero
				| x::xs -> if xs = [] then x else Plus (x, pls xs)
		in
			pls (Set.toList reSet)

	(* For the given i and j, returns the value of R when k is zero.
		Note that k will always be 0 when called inside this method *)
	let calczerok k i j trns =
		let ts = Set.filter (fun (a,_,b) -> i = a && j = b) trns in
		if ts <> Set.empty then
			if i <> j then
				let res = Set.map (fun (_,c,_) -> Symb c) ts in
					(k,i,j,plusSet res)
			else
				let res = Set.map (fun (_,c,_) -> Symb c) ts in
				let re = Plus(Empty, (plusSet res)) in
					(k,i,j,re)

		else (k,i,j,Zero)
		
	let getRij i j prvK =
		let r = Set.nth (Set.filter (fun (_,x,y,_) -> x = i && y = j) prvK) 0 in
			(fun (_,_,_,re) -> re) r

	let assembleRe st i j prvK =
		let rik = getRij i st prvK in
		let rkk = Star (getRij st st prvK) in
		let rkj = getRij st j prvK in
			Seq(rik, Seq(rkk,rkj))
				
	(* For the given i and j, returns the value of R when k is not zero. *)
	let calck k i j prvK sts =
		let rij = getRij i j prvK in
		let rikjs = Set.map (fun st -> assembleRe st i j prvK) sts in
		let rikj = plusSet rikjs in
			(k,i,j,Plus(rij,rikj))

	(* Main function that applies previous 2 functions to all possible i and j pairs *)
	let rec rkij k trns sts =
		if k < 1 then
			Set.map (fun (i,j) -> calczerok k i j trns) (Set.product sts sts)
		else
			let prvK = rkij (k-1) trns sts in
				Set.map (fun(i,j) -> calck k i j prvK sts) (Set.product sts sts)

	let fa2re (fa: FiniteAutomaton.t): RegularExpression.t =
		(* Since the algorithm only works for deterministic automaton, we first convert it
			to its deterministic equivalent *)
		let fa = FiniteAutomaton.toDeterministic fa in
		let sts = fa.states in
		let trns = fa.transitions in
		let allRks = rkij (Set.size sts) trns sts in
		let result = Set.filter (fun (_,i,j,_) -> i = fa.initialState && Set.belongs j fa.acceptStates ) allRks in
		let res = Set.map (fun (_,_,_,re) -> re) result in		
			plusSet res
		(*	simplify (plusSet res) *)
end

(********************************************************************)
module RE2CFG =
struct
	open RegularExpression
	open ContextFreeGrammarBasic
	
	(*auxiliary var for genVar function*)
	let k = ref 0

	(* generates new unused variable name for the cfg *)
	let genVar () =
		let n = !k in
		let () = k:= n + 1 in
		let ascii = 65 + n in
		if ascii < 65 || ascii > 90
		then char2symb 'A'
		else char2symb (Char.chr ascii)

	(*
	let convertPlsRules rl i1 i2 newInit =
		(* swaps the initial variables of both old cfgs for the new initial var *)
		let swapInits c = if c = i1 || c = i2 then newInit else c in

		let newBody b = List.map (fun c -> swapInits c) b in
		let newRule r = {head = swapInits r.head; body = newBody r.body} in

			Set.map (fun r -> newRule r) rl

	in
	*)
	(* create gcf rules for plus expression *)
	let convertPlsRules rl i1 i2 newInit =
		let newRule1 = {head = newInit; body = [i1]} in
		let newRule2 = {head = newInit; body = [i2]} in
			Set.add newRule1 (Set.add newRule2 rl)

	(* create gcf rules for seq expression *)
	let convertSeqRules lcfg rcfg =
		let rl1 = lcfg.rules in
		let rl2 = rcfg.rules in
		let alp1 = lcfg.alphabet in
		let rl = Set.union rl1 rl2 in
		let newBody r =
			let b = r.body in
				match b with
					| [c] when Set.belongs r rl1 && not (Set.belongs c alp1) && c <> epsilon -> b
					| [c] when Set.belongs r rl1 && Set.belongs c alp1 -> [c; rcfg.initial]
					| [epsilon] when Set.belongs r rl1 -> [epsilon; rcfg.initial]
					| b when Set.belongs r rl2 -> b
					| _ -> b
		in
		let newRule r = {head = r.head; body = newBody r} in
			Set.map (fun r -> newRule r) rl

	(* create gcf rules for star expression *)
	let convertStrRules cfg =
		let newBody b =
			match b with
				| [c] when Set.belongs c cfg.alphabet -> [c; cfg.initial]
				| _ -> b
		in
		let r0 = {head = cfg.initial; body = [epsilon]} in

		let newRule r = {head = r.head; body = newBody r.body} in
		let newRules = Set.map (fun r -> newRule r) cfg.rules in
			Set.add r0 newRules

	let rec compile re =
		match re with
			| Plus(l, r) ->
					let cl = compile l in
					let cr = compile r in
					let alp = Set.union cl.alphabet cr.alphabet in
					let init = genVar () in
					let vs = Set.add init (Set.union cl.variables cr.variables) in
					let rl = Set.union cl.rules cr.rules in
					let rl = convertPlsRules rl cl.initial cr.initial init in
						{alphabet = alp; variables = vs;
							initial = init; rules = rl}
			| Seq(l, r) ->
					let cl = compile l in
					let cr = compile r in
					let alp = Set.union cl.alphabet cr.alphabet in
					let init = cl.initial in
					let vs = Set.union cl.variables cr.variables in
					let rl = convertSeqRules cl cr in
						{alphabet = alp; variables = vs;
							initial = init; rules = rl}
			| Star(re) ->
					let cre = compile re in
					let alp = cre.alphabet in
					let init = cre.initial in
					let vs = cre.variables in
					let rl = convertStrRules cre in
						{alphabet = alp; variables = vs;
							initial = init; rules = rl}
			| Symb(c) ->
					let alp = Set.make [c] in
					let init = genVar () in
					let vars = Set.make [init] in
					let rules = Set.make [{head = init; body = [c]}] in
						{alphabet = alp; variables = vars;
							initial = init; rules = rules}
			| Empty ->
					let alp = Set.empty in
					let init = genVar () in
					let vars = Set.make [init] in
					let rules = Set.make [{head = init; body = [epsilon]}] in
						{alphabet = alp; variables = vars;
							initial = init; rules = rules}
			| Zero ->
					let alp = Set.empty in
					let init = genVar () in
					let var2 = genVar () in
					let vars = Set.make [init; var2] in
					let r1 = {head = init; body = [var2]} in
					let r2 = {head = var2; body = [init]} in
					let rules = Set.make [r1; r2] in
						{alphabet = alp; variables = vars;
								initial = init; rules = rules}

	let re2cfg (re: RegularExpression.t): ContextFreeGrammarBasic.t =
		compile re
end

(********************************************************************)
module FA2CFG =
struct
	let fa2cfg fa =
		let re = FA2RE.fa2re fa in
			RE2CFG.re2cfg re
end

(********************************************************************)
module CFG2FA = (* right-linear CFG *)
struct
	open ContextFreeGrammarBasic
	open FiniteAutomaton
	
	let toState sy = state (symb2str sy)

	let toStates ssy = Set.map toState ssy

	(* This name will always be unique in the generated automaton *)
	let accSt = state "AccSt"

	let ruleToTrans (cfg: ContextFreeGrammarBasic.t) rh rb =
		let alp = cfg.alphabet in
		let vrs = cfg.variables in
		match rb with
			| [s;v] when Set.belongs s alp && Set.belongs v vrs	-> Set.make [(toState rh, s, toState v)]
			| [v] when Set.belongs v vrs -> Set.make [(toState rh, epsilon, toState v)]
			| [s] when Set.belongs s alp -> Set.make [(toState rh, s, accSt)]
			| [e] when e = epsilon -> Set.make [(toState rh, epsilon, accSt)]
			| _ -> Set.empty

	let cfg2fa (cfg: ContextFreeGrammarBasic.t): FiniteAutomaton.t =
	{	alphabet = cfg.alphabet;
		states = Set.add accSt (toStates cfg.variables);
		initialState = toState cfg.initial;
		transitions = Set.flatMap (fun r -> ruleToTrans cfg r.head r.body) cfg.rules;
		acceptStates = Set.make [accSt]
	}
end

(********************************************************************)
module CFG2RE = (* right-linear CFG *)
struct
	let cfg2re (cfg: ContextFreeGrammarBasic.t): RegularExpression.t =
		let fa = CFG2FA.cfg2fa cfg in
			FA2RE.fa2re fa
end

(********************************************************************)
module PDA2FA =
struct
	let transitionsFa trns = Set.map ( fun (s1,_,a,s2,_) -> (s1,a,s2) ) trns
	
	let pda2fa (pda: PushdownAutomaton.t): FiniteAutomaton.t  =
	{	alphabet = pda.inputAlphabet;
		states = pda.states;
		initialState = pda.initialState;
		transitions = transitionsFa pda.transitions;
		acceptStates = pda.acceptStates
	}
end

(********************************************************************)
module FA2PDA =
struct
	let upgradeTransition (s1,symb,s2) =
			(s1,PushdownAutomaton.stackSpecialSymb,symb,s2,[PushdownAutomaton.stackSpecialSymb])
			
	let upgradeTransitions trns =
		Set.map upgradeTransition trns
		
	let fa2pda (fa: FiniteAutomaton.t): PushdownAutomaton.t =
	{	inputAlphabet = fa.alphabet;
		stackAlphabet = Set.make [PushdownAutomaton.stackSpecialSymb];
		states = fa.states;
		initialState = fa.initialState;
		initialStackSymbol = PushdownAutomaton.stackSpecialSymb;
		transitions = upgradeTransitions fa.transitions;
		acceptStates = fa.acceptStates;
		criteria = true
	}
end

(********************************************************************)
module RE2PDA =
struct
	let re2pda (re: RegularExpression.t): PushdownAutomaton.t =
		let fa = RE2FA.re2fa re in
			FA2PDA.fa2pda fa
end

(********************************************************************)
module PDA2RE =
struct
	let pda2re (pda: PushdownAutomaton.t): RegularExpression.t =
		let fa = PDA2FA.pda2fa pda in
			FA2RE.fa2re fa
end

(********************************************************************)
module CFG2PDA =
struct
	open ContextFreeGrammarBasic
	open PushdownAutomaton

	let computeState = state "q"
	
	let makeNewTransition symbToConsume topStackSymbol toPutInStack: transition =
		(computeState, topStackSymbol, symbToConsume, computeState, toPutInStack)

	let buildTransitions(cfg: ContextFreeGrammarBasic.t): transitions =
		let transitionsRules = Set.map (fun r -> makeNewTransition epsilon r.head r.body) cfg.rules in
		let transitionsFinalSymb = Set.map (fun alph -> makeNewTransition alph alph []) cfg.alphabet in
			Set.union transitionsRules transitionsFinalSymb

	let cfg2pda (cfg: ContextFreeGrammarBasic.t): PushdownAutomaton.t = 
	{	inputAlphabet = cfg.alphabet;
		stackAlphabet = Set.union cfg.alphabet cfg.variables;
		states = Set.make [computeState];
		initialState = computeState;
		initialStackSymbol = cfg.initial;
		transitions = buildTransitions cfg;
		acceptStates = Set.empty;
		criteria = false
	}
end

(********************************************************************)
module PDA2CFG = (* todo *)
struct
	let pda2cfg (pda: PushdownAutomaton.t): ContextFreeGrammarBasic.t =
		ContextFreeGrammarBasic.make (Arg.Text {|{}|})
end

(********************************************************************)
module PDA2TM =
struct
	let generateTransitionsToPD st alphEntr alphPD: TuringMachine.transitions =
		let allAlph = Set.add dollar (Set.union alphEntr alphPD) in
			Set.map (fun symb -> (st,[symb],st,[symb],[R])) allAlph 

	let generateTransitionsFromPD st alphEntr alphPD: TuringMachine.transitions =
		let allAlph = Set.add dollar (Set.union alphEntr alphPD) in
			Set.map (fun symb -> (st,[symb],st,[symb],[L])) allAlph 

	let insertSymbolsPD alphEntr (pda: PushdownAutomaton.t): states * TuringMachine.transitions =
		let alphPD = pda.stackAlphabet in
		let st1 = state (IdGenerator.gen("q")) in
		let st2 = state (IdGenerator.gen("q")) in
		let st3 = state (IdGenerator.gen("q")) in
		let newSts = Set.add st1 ( Set.add st2 ( Set.add st3 Set.empty)) in
		let newTrs1 = Set.union (generateTransitionsToPD st1 alphEntr alphPD) (generateTransitionsFromPD st3 alphEntr alphPD) in
		let newTrs2 = Set.add (st1,[empty],st2,[symb "$"],[R]) (Set.add (st2,[empty],st3,[pda.initialStackSymbol],[R]) ( Set.add (st3,[empty],pda.initialState,[empty],[R])  newTrs1 )) in
			(Set.union pda.states newSts) , newTrs2

	let rec fillStackTransition lastSt prevSt (trs: TuringMachine.transitions) wordL: TuringMachine.transitions =
		match wordL with
		| [] -> trs
		| x::y ->	let newState = if (Set.isEmpty (Set.make y)) then lastSt else IdGenerator.gen("q") in
							let dir = if (Set.isEmpty (Set.make y)) then L else R in
								fillStackTransition lastSt newState (Set.add (prevSt,[empty], newState, [x], [dir]) trs) y 

	let convertNormalTransition (tr: PushdownAutomaton.transition) alphEntr alphPD: states * TuringMachine.transitions =
		let (startState,unstackedSymbol,readSymbol,nextState,writeSymbolL) = tr in
		let st1 = state (IdGenerator.gen("q")) in
		let st2 = state (IdGenerator.gen("q")) in
		let st3 = state (IdGenerator.gen("q")) in
		let ftrs = (startState,[readSymbol],st1,[empty],[R]) in
		let trsTPD = Set.add ftrs (generateTransitionsToPD st1 alphEntr alphPD) in
		let trsRTOP = Set.add (st1,[empty],st2,[empty],[L]) trsTPD in
		let firstDirection = if ((List.length writeSymbolL) = 1) then L else R in
		let lastSt = if ((List.length writeSymbolL) = 1) then st3 else state (IdGenerator.gen("q")) in
		let replaceTop = Set.add (st2,[unstackedSymbol],st3, [List.hd writeSymbolL], [firstDirection]) trsRTOP in
		let additionalSymbolTrs = Set.union replaceTop (fillStackTransition lastSt st3 Set.empty (List.tl writeSymbolL)) in
		let trsFPD = Set.union additionalSymbolTrs (generateTransitionsFromPD lastSt alphEntr alphPD) in
		let trsLast = Set.add (lastSt,[empty],nextState,[empty],[R]) trsFPD in
			Set.add lastSt (Set.add st3 (Set.add st2 (Set.add st1 Set.empty))), trsLast

	let convertAcceptTransition (tr: PushdownAutomaton.transition) alphEntr alphPD initialStackSymb: states * TuringMachine.transitions =
		let (startState,unstackedSymbol,readSymbol,nextState,writeSymbolL) = tr in
		let st1 = state (IdGenerator.gen("q")) in
		let st2 = state (IdGenerator.gen("q")) in
		let st3 = state (IdGenerator.gen("q")) in
		let ftrs = Set.add (startState,[dollar],st1,[dollar],[R]) Set.empty in
		let checkInitSS = Set.add (st1,[initialStackSymb],st2,[empty],[R]) ftrs in
		let lastCheck = Set.add (st2,[empty],st3,[empty],[R]) checkInitSS in
			Set.add st3 (Set.add st2 (Set.add st1 Set.empty)), lastCheck

	let convertTransitionX (tr: PushdownAutomaton.transition) alphEntr alphPD initialStackSymb: states * TuringMachine.transitions = 
		let (_,_,readSymbol,_,_) = tr in
			if readSymbol == draftVar then convertAcceptTransition tr alphEntr alphPD initialStackSymb
			else convertNormalTransition tr alphEntr alphPD

	let rec convertTransitions newSts newTrs alphEntr (pda: PushdownAutomaton.t) (trs: PushdownAutomaton.transitions): states * TuringMachine.transitions = 
		let alphPD = pda.stackAlphabet in
		let initialStackSymb = pda.initialStackSymbol in
		if (Set.size trs) = 0 then newSts, newTrs
		else 
			let (nSts,nTrs) = convertTransitionX (Set.hd trs) alphEntr alphPD initialStackSymb in
				convertTransitions (Set.union nSts newSts) (Set.union nTrs newTrs) alphEntr pda (Set.tl trs)

	(*Se parar por pilha vazia 'e ncess'ario criar um estado final*)
	let getFinalStates trs: states =
		Set.map (fun (_,_,_,d,_) -> d) (Set.filter (fun (_,_,c,_,_) -> c = dollar) trs)

	let pda2tm (pda: PushdownAutomaton.t): TuringMachine.t =
		let pdaAlphabet = Set.remove draftVar pda.inputAlphabet in
		let (initialStates, initialTransitions) = insertSymbolsPD pdaAlphabet pda in
		let (convertedTransitionStates,convertedTransitions) =
			convertTransitions Set.empty Set.empty pdaAlphabet pda pda.transitions in
		let allAlphabet = Set.add dollar ( Set.union pdaAlphabet pda.stackAlphabet) in
		let allStates = Set.union initialStates convertedTransitionStates in
		let allTransitions = Set.union initialTransitions convertedTransitions in
		let allAcceptStates = Set.union pda.acceptStates (getFinalStates pda.transitions) in
			{ TuringMachine.tm_zero with
				entryAlphabet = pda.inputAlphabet;
				tapeAlphabet = allAlphabet;
				states = allStates;
				initialState = state "q00";
				transitions = allTransitions;
				acceptStates = allAcceptStates;
				criteria = true }
end

(********************************************************************)
module FA2TM = (* Carolina *)
struct
	let fa2tm (fa : FiniteAutomaton.t): TuringMachine.t = 
	{	entryAlphabet = fa.alphabet;
		tapeAlphabet = fa.alphabet;
		empty = empty;
		states = fa.states;
		initialState = fa.initialState;
		transitions = Set.map (fun (a,b,c) -> (a,[b],c,[b],[R])) fa.transitions;
		acceptStates = fa.acceptStates;
		criteria = true;
		lbMarkers = [];
		_nTapes = 1
	}
end

(********************************************************************)
module RE2TM =
struct
	let re2tm (re: RegularExpression.t): TuringMachine.t =
		let re = RE2FA.re2fa re in
			FA2TM.fa2tm re
end

(********************************************************************)
module CFG2TM = (* ??? *)
struct
	let cfg2tm (cfg: ContextFreeGrammarBasic.t): TuringMachine.t =
		let cfg = CFG2FA.cfg2fa cfg in
			FA2TM.fa2tm cfg
end

(********************************************************************)
module PolyBasic =
struct
	let re2fa = RE2FA.re2fa
	let pda2fa = PDA2FA.pda2fa
	let cfg2fa = CFG2FA.cfg2fa
	
	let fa2re = FA2RE.fa2re
	let pda2re = PDA2RE.pda2re
	let cfg2re = CFG2RE.cfg2re

	let fa2pda = FA2PDA.fa2pda
	let re2pda = RE2PDA.re2pda
	let cfg2pda = CFG2PDA.cfg2pda
	
	let fa2cfg = FA2CFG.fa2cfg
	let re2cfg = RE2CFG.re2cfg
	let pda2cfg = PDA2CFG.pda2cfg
	
	let fa2tm = FA2TM.fa2tm
	let re2tm = RE2TM.re2tm
	let pda2tm = PDA2TM.pda2tm
	let cfg2tm = CFG2TM.cfg2tm
end

(********************************************************************)
module PolyModel =
struct
	open PolyBasic
	
	let json2model (j: JSon.t): Model.model =
		let kind = JSon.fieldString j "kind" in
			if FiniteAutomaton.kind = kind then
				(new FiniteAutomaton.model (Arg.JSon j) :> Model.model)
			else if RegularExpression.kind = kind then
				(new RegularExpression.model (Arg.JSon j) :> Model.model)
			else if PushdownAutomaton.kind = kind then
				(new PushdownAutomaton.model (Arg.JSon j) :> Model.model)
			else if ContextFreeGrammarBasic.kind = kind then
				(new ContextFreeGrammarBasic.model (Arg.JSon j) :> Model.model)
			else if TuringMachine.kind = kind then
				(new TuringMachine.model (Arg.JSon j) :> Model.model)
			else if FiniteEnumeration.kind = kind then
				(new FiniteEnumeration.model (Arg.JSon j) :> Model.model)
			else if Exercise.kind = kind then (
				ignore (new Exercise.exercise (Arg.JSon j));			
				(new FiniteAutomaton.model (Arg.JSon FiniteAutomaton.example) :> Model.model)
			)
			else (* need to ignore Composition.kind *)
				(new FiniteAutomaton.model (Arg.JSon FiniteAutomaton.example) :> Model.model)
				
	let text2model (text: string): Model.model = json2model (JSon.parse text)
	
	let file2model (filename: string): Model.model = json2model (JSon.fromFile filename)
	
	let example2model (name: string): Model.model = text2model (Examples.example name)

	let fa2model (fa: FiniteAutomaton.t): FiniteAutomaton.model =
		new FiniteAutomaton.model (Arg.Representation fa)

	let re2model (re: RegularExpression.t): RegularExpression.model =
		new RegularExpression.model (Arg.Representation re)

	let pda2model (pda: PushdownAutomaton.t): PushdownAutomaton.model =
		new PushdownAutomaton.model (Arg.Representation pda)

	let cfg2model (cfg: ContextFreeGrammarBasic.t): ContextFreeGrammarBasic.model =
		new ContextFreeGrammarBasic.model (Arg.Representation cfg)

	let tm2model (tm: TuringMachine.t): TuringMachine.model =
		new TuringMachine.model (Arg.Representation tm)

	let model2fa (model: Model.model): FiniteAutomaton.t =
		if model#isFiniteAutomaton then FiniteAutomaton.make (Arg.JSon (model#toJSon))
		else Error.fatal "model2fa"
		
	let model2re (model: Model.model): RegularExpression.t =
		if model#isRegularExpression then RegularExpression.make (Arg.JSon (model#toJSon))
		else Error.fatal "model2re"
		
	let model2cfg (model: Model.model): ContextFreeGrammarBasic.t =
		if model#isContextFreeGrammar then ContextFreeGrammarBasic.make (Arg.JSon (model#toJSon))
		else Error.fatal "model2cfg"
		
	let model2pda (model: Model.model): PushdownAutomaton.t =
		if model#isPushdownAutomaton then PushdownAutomaton.make (Arg.JSon (model#toJSon))
		else Error.fatal "model2pda"
		
	let model2tm (model: Model.model): TuringMachine.t =
		if model#isTuringMachine then TuringMachine.make (Arg.JSon (model#toJSon))
		else Error.fatal "model2tm"

	(* Carolina *)
	let model2comp (model: Model.model): CompositionSupport.t =
		if model#isFiniteAutomaton then FA (model2fa model)
		else if model#isRegularExpression then RE (model2re model)
		else if model#isPushdownAutomaton then PDA (model2pda model)
		else if model#isContextFreeGrammar then CFG (model2cfg model)
		else if model#isTuringMachine then TM (model2tm model)
		else if model#isComposition then 
			!CompositionSupport.makeCompositionRef (Arg.JSon (model#toJSon))
		else Error.fatal "model2comp"

	let re2fa m = fa2model (re2fa m#representation)
	let pda2fa m = fa2model (pda2fa m#representation)
	let cfg2fa m = fa2model (cfg2fa m#representation)

	let fa2re m = re2model (fa2re m#representation)
	let pda2re m = re2model (pda2re m#representation)
	let cfg2re m = re2model (cfg2re m#representation)

	let fa2pda m = pda2model (fa2pda m#representation)
	let re2pda m = pda2model (re2pda m#representation)
	let cfg2pda m = pda2model (cfg2pda m#representation)

	let fa2cfg m = cfg2model (fa2cfg m#representation)
	let re2cfg m = cfg2model (re2cfg m#representation)
	let pda2cfg m = cfg2model (pda2cfg m#representation)
	
	let fa2tm m = tm2model (fa2tm m#representation)	
	let re2tm m = tm2model (re2tm m#representation)	
	let pda2tm m = tm2model (pda2tm m#representation)	
	let cfg2tm m = tm2model (cfg2tm m#representation)
end

module PolyCheckExamples: sig end =
struct
	open Examples
	open PolyModel

	let checkExamples = (* run immediately *)
		List.iter
			(fun name -> ignore (text2model (example name)))
			examples
end

(********************************************************************)
module PolyBasicTests: sig end =
struct
	open PolyBasic

	let active = false

	let testToFA () =
		let re = RegularExpression.make (Arg.Predef "re_abc") in
		let fa = re2fa re in
			JSon.show (FiniteAutomaton.toJSon fa)

	let testToFA2 () =
		let re = RegularExpression.make (Arg.Predef "re_simple") in
		let fa = re2fa re in
			JSon.show (FiniteAutomaton.toJSon fa)

	let testToFA3 () =
		let re = RegularExpression.make (Arg.Predef "re_complex") in
		let fa = re2fa re in
			JSon.show (FiniteAutomaton.toJSon fa)

	let testToFA4 () =
		let re = RegularExpression.make (Arg.Predef "re_convoluted") in
		let fa = re2fa re in
			JSon.show (FiniteAutomaton.toJSon fa)

	let fa_toRe = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "fa_toRe",
		alphabet : ["a","b"],
		states : ["1", "2"],
		initialState : "1",
		transitions : [
				["1","a","2"],["2","b","2"]
			],
		acceptStates : ["2"]
	} |}

	let testSimplify () =
		let fa = FiniteAutomaton.make (Arg.Text fa_toRe) in
		let re = fa2re fa in
			RegularExpression.show re;
			let rs =  RegularExpression.simplify re in
				RegularExpression.show rs

	let testToRe () =
		let fa = FiniteAutomaton.make (Arg.Text fa_toRe) in
		let re = fa2re fa in
			RegularExpression.show re

	let testToGrammar () =
		let re = RegularExpression.make (Arg.Predef "re_simple") in
		let cfg = re2cfg re in
			ContextFreeGrammarBasic.show cfg

	let testToAutomaton () =
		let cfg = ContextFreeGrammarBasic.make (Arg.Predef "cfg_abc") in
		let fa = cfg2fa cfg in
			FiniteAutomaton.show fa

	let testToRe () =
		let cfg = ContextFreeGrammarBasic.make (Arg.Predef "cfg_abc") in
		let re = cfg2re cfg in
			RegularExpression.show re

	let runAll =
		if Util.testing active "PolyModel" then begin
			testSimplify ()
		end
end
# 1 "src/Composition.ml"
(*
 * Composition.ml
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
 *  Written by Carolina Duarte (cd)
 *)

(*
 * ChangeLog:
 *
 *)

(*
 * Description: Composition of models.
 *
 *)

 open BasicTypes

 module Repository = struct 
   type t = CompositionSupport.t
 
   let data : (string * t) list ref = ref []
   
   let exists (name:string) : bool =
     List.mem_assoc name !data 
   
 
   let delete (name:string) : unit =
     data := List.remove_assoc name !data
   
   
   let update (name:string) (model: t) : unit =
     delete name;
     data := (name,model)::!data
 

        
   let updateModel (name:string) (model: Model.model) : unit =
    delete name;
    let m = PolyModel.model2comp model in
      data := (name,m)::!data
    

   let getExample (name:string) : t  =  
       let j = Examples.jsonExample name in
       let kind = JSon.fieldString j "kind" in
         if FiniteAutomaton.kind = kind then
           (FA (FiniteAutomaton.make (Arg.JSon j)))
         else if RegularExpression.kind = kind then
           (RE (RegularExpression.make (Arg.JSon j)))
         else if ContextFreeGrammar.kind = kind then
           (CFG (ContextFreeGrammarBasic.make (Arg.JSon j)))
         else if PushdownAutomaton.kind = kind then
           (PDA (PushdownAutomaton.make (Arg.JSon j)))
         else if TuringMachine.kind = kind then
           (TM (TuringMachine.make (Arg.JSon j)))
         else if CompositionSupport.kind = kind then
            (!CompositionSupport.makeCompositionRef (Arg.JSon j))
         else Error.fatal "getExample"
       
 
   let get (name:string) : t  =
     try
       List.assoc name !data 
     with Not_found -> getExample name

   let getText (name:string) : string =
    try
      let m = List.assoc name !data in
      match m with
      | Plus (a,b) ->
        JSon.toString (CompositionSupport.toJSon m)
      |Intersect (a,b) ->
        JSon.toString (CompositionSupport.toJSon m)
      | Seq (a,b) ->
        JSon.toString (CompositionSupport.toJSon m)
      | Star t ->
        JSon.toString (CompositionSupport.toJSon m)
      | FA fa ->
        JSon.toString (FiniteAutomaton.toJSon fa)
      | RE re ->
        JSon.toString (PolyModel.re2model re)#toJSon
      | CFG cfg ->
        JSon.toString (PolyModel.cfg2model cfg)#toJSon
      | PDA pda ->
        JSon.toString (PolyModel.pda2model pda)#toJSon
      | TM tm ->
        JSon.toString (PolyModel.tm2model tm)#toJSon
      | FAO fao ->
        JSon.toString fao#toJSon 
      | REO reo ->
        JSon.toString reo#toJSon 
      | CFGO cfgo ->
        JSon.toString cfgo#toJSon 
      | PDAO pdao ->
        JSon.toString pdao#toJSon 
      | TMO tmo ->
        JSon.toString tmo#toJSon
     | _ -> Error.fatal "getText"
    with Not_found -> Examples.example name


 let getJSon (name:string) : JSon.t =
  try
    let m = List.assoc name !data in
    match m with
    | Plus (a,b) ->
      CompositionSupport.toJSon2 (Entity.dummyId CompositionSupport.kind) m
    |Intersect (a,b) ->
      CompositionSupport.toJSon2 (Entity.dummyId CompositionSupport.kind) m
    | Seq (a,b) ->
      CompositionSupport.toJSon2 (Entity.dummyId CompositionSupport.kind) m
    | Star t ->
      CompositionSupport.toJSon2 (Entity.dummyId CompositionSupport.kind) m
    | FA fa ->
      FiniteAutomaton.toJSon2 (Entity.dummyId FiniteAutomaton.kind) fa
    | RE re ->
      RegularExpression.toJSon2 (Entity.dummyId RegularExpression.kind) re
    | CFG cfg ->
      ContextFreeGrammar.toJSon2 (Entity.dummyId ContextFreeGrammar.kind) cfg
    | PDA pda ->
      PushdownAutomaton.toJSon2 (Entity.dummyId PushdownAutomaton.kind) pda
    | TM tm ->
      TuringMachine.toJSon2 (Entity.dummyId TuringMachine.kind) tm
    | FAO fao ->
      fao#toJSon2 
    | REO reo ->
      reo#toJSon2 
    | CFGO cfgo ->
      cfgo#toJSon2 
    | PDAO pdao ->
      pdao#toJSon2 
    | TMO tmo ->
      tmo#toJSon2
    | _ -> Error.fatal "getJSon"
  with Not_found -> Examples.jsonExample name

  let getListLabels =
    let e = Examples.examples in
    let d = List.map fst !data in
    List.append e d;
end
 
 (*not use
 module Repository2 = struct 
 
   type 'a t = (string * 'a) list
   let rep: 'a t = []
 
   let r = ref rep
 
   let f (x: 'a t) = x
 
   let exists (name:string) : bool = 
     List.exists (fun (n,_) -> n=name) !r
   
   let get (name:string) =
     let c = List.find_opt (fun (n,_) -> n = name) !r in
     match c with
       | None -> None
       | Some (n,m) -> Some m
 
   let delete (name:string) =
     r := List.filter (fun (n,_) -> n != name) !r
 
 
   let update (name:string) (model: 'a) =
     delete (name);
     r := (name,model)::!r
   end*)
 
 
 module Composition =
 struct
 
   include CompositionSupport
 
 
 
 (*let repository : t Repository.t ref = ref [] 
 
   let xx = 
     repository := Repository.update "ola" (Rep "ole")*)
 
 
   (* example *)
   (* AMD
   let fa_empty = {| {
       kind : "finite automaton",
       description : "empty finite automaton",
       name : "fa_empty",
       alphabet: ["a"],
       states : ["START"],
       initialState : "START",
       transitions : [
         ["START", "a", "START"]
       ],
       acceptStates : []
       } |}
 
   let emptyFA =
     FiniteAutomaton.make (Arg.Text fa_empty)
	*)
 
 
 
   (** aux *)
   let rec decompositions l =
     match l with
       [] -> [([], [])]
       | x::xs -> let lp = decompositions xs in
         ([], l) :: List.map (fun (a,b) -> (x::a,b)) lp
   ;;
 
 
   (* Try to recognize a word *)
   let rec accept (c: t) (w: word) : bool =
     match c with
     | Plus (a,b) ->
       accept a w || accept b w
     | Intersect (a,b) ->
       accept a w && accept b w
     | Seq (a,b) ->
       let list = Set.make(decompositions w) in
       Set.exists (fun (p0,p1) -> (accept a p0) && (accept b p1)) list
       (*false*)
     | Star t ->
       w = []
       || (let list = Set.remove ([],w) (Set.make(decompositions w)) in
           Set.exists (fun (p0,p1) -> (accept t p0) && (accept (Star t) p1)) list)
       (*false*)
     | FA fa ->
       FiniteAutomaton.accept fa w
     | RE re ->
       RegularExpressionPrivate.accept re w
     | CFG cfg ->
       ContextFreeGrammarBasic.accept cfg w
     | PDA pda ->
       PushdownAutomaton.accept pda w
     | TM tm ->
       TuringMachine.accept tm w
     | FAO fao ->
         FiniteAutomaton.accept fao#representation w 
     | REO reo ->
         RegularExpressionPrivate.accept reo#representation w
     | CFGO cfgo ->
         ContextFreeGrammarBasic.accept cfgo#representation w
     | PDAO pdao ->
         PushdownAutomaton.accept pdao#representation w
     | TMO tmo ->
         TuringMachine.accept tmo#representation w
     | Rep rep ->
      (try
        let m = Repository.get rep in
          accept m w
      with Not_found -> Error.fatal "Composition with invalid repository name")
       
     | _ -> Error.fatal "accept"
       
   (* Concat  *)
   let concatAllS w s =
     Set.map (fun l -> w@l) s
 
 
   (* Generate all the accepted word with maximum length *)
   let rec generate (c: t) (len: int) : words =
     match c with
     | Plus (a,b) ->
       Set.union (generate a len)  (generate b len)
     | Intersect (a,b) ->
       Set.inter (generate a len) (generate b len)
     | Seq (a,b) ->
       let left = generate a len in
       let rigth w = generate b (len - (List.length w)) in
       let conc w = concatAllS w (rigth w) in
         Set.flatMap (fun lw -> conc lw) left    
     | Star t ->
       let exp = generate t len in
         Set.star exp len
     | FA fa ->
       FiniteAutomaton.generate fa len
     | RE re ->
       RegularExpressionPrivate.generate re len
     | CFG cfg ->
       ContextFreeGrammarBasic.generate cfg len
     | PDA pda ->
       PushdownAutomaton.generate len pda
     | TM tm ->
       TuringMachine.generate tm len
     | FAO fao ->
         FiniteAutomaton.generate fao#representation len 
     | REO reo ->
         RegularExpressionPrivate.generate reo#representation len
     | CFGO cfgo ->
         ContextFreeGrammarBasic.generate cfgo#representation len
     | PDAO pdao ->
         PushdownAutomaton.generate len pdao#representation
     | TMO tmo ->
         TuringMachine.generate tmo#representation len
     | Rep rep ->
      (try
        let m = Repository.get rep in
          generate m len
      with Not_found -> Error.fatal "Composition with invalid repository name")
     | _ -> Error.fatal "generate"
 
     (* Adds a sufix to a state name *)
     let addSufixFA (st: state)(sufix: string): state =
       str2state ((state2str st)^"_"^sufix)  
 
     (* Adds a sufix to a variable name name *)
     let addSufixCFG (v: symbol)(sufix: string): symbol =
       str2symb((symb2str v)^"_"^sufix)
     
 
     (* Renames all the states in one automaton adding a sufix *)	
     let renameStatesFA(fa: FiniteAutomaton.t) (sufix: string): FiniteAutomaton.t =
 
       {
         alphabet = fa.alphabet; 
         states = Set.map (fun st -> addSufixFA st sufix) fa.states;
         initialState = addSufixFA fa.initialState sufix;
         transitions = Set.map (fun (s1,sy,s2) -> (addSufixFA s1 sufix,sy,addSufixFA s2 sufix)) fa.transitions;
         acceptStates = Set.map (fun st -> addSufixFA st sufix) fa.acceptStates
       }
 
     let addSufixList body sufix =
        List.map(fun s -> addSufixCFG  s sufix) body
     
     let addSufixListCFG body sufix alphabet =
        List.map
			(fun s -> if Set.belongs s alphabet then s else addSufixCFG s sufix)
			body
     
       (* Renames all the variables in one gramatic adding a sufix *)	
     let renameVariablesCFG (cfg: ContextFreeGrammarBasic.t) (sufix: string): ContextFreeGrammarBasic.t =
       let open ContextFreeGrammarBasic in 
       {alphabet = cfg.alphabet;
        variables =	Set.map (fun v -> addSufixCFG v sufix) cfg.variables;
        initial = addSufixCFG cfg.initial sufix;
        rules = Set.map
					(fun {head= h;body = b} -> {head=(addSufixCFG h sufix); body=addSufixListCFG b sufix cfg.alphabet})
					cfg.rules
       }
     
     let renameStatesPDA (pda: PushdownAutomaton.t) (sufix: string): PushdownAutomaton.t =
       
       {
         inputAlphabet = pda.inputAlphabet;
         stackAlphabet = Set.map (fun s -> addSufixCFG s sufix) pda.stackAlphabet;
         states = Set.map (fun st -> addSufixFA st sufix) pda.states;
         initialState = addSufixFA pda.initialState sufix;
         initialStackSymbol = addSufixCFG pda.initialStackSymbol sufix;
         transitions = Set.map (fun (q1,s1,sy,q2,s2) -> (addSufixFA q1 sufix,addSufixCFG s1 sufix,sy,addSufixFA q2 sufix,addSufixList s2 sufix )) pda.transitions;
         acceptStates = Set.map (fun st -> addSufixFA st sufix) pda.acceptStates;
         criteria = true
       }
 
     let renameStatesTM (tm: TuringMachine.t) (sufix: string): TuringMachine.t =
		{ tm with
			states = Set.map (fun st -> addSufixFA st sufix) tm.states;
			initialState = addSufixFA tm.initialState sufix;
			transitions = Set.map (fun (s1,symb1,s2,symb2,d) ->
						(addSufixFA s1 sufix,symb1,addSufixFA s2 sufix,symb2,d ))
						tm.transitions;
			acceptStates = Set.map (fun st -> addSufixFA st sufix) tm.acceptStates;
			criteria = true }
   
     let rec rename (c: t): t =
     match c with
     | Plus (a,b) ->
         Plus(rename a,rename b)
     | Seq (a,b) ->
         Seq(rename a,rename b)
     | Intersect (a,b) ->
         Intersect(rename a,rename b)
     | Star t ->
         Star(rename t)
     | FA fa ->
         FA (renameStatesFA fa (IdGenerator.gen("")))
     | RE re ->
       RE re
     | CFG cfg ->
       CFG (renameVariablesCFG cfg (IdGenerator.gen("")))
     | PDA pda ->
       PDA (renameStatesPDA pda (IdGenerator.gen("")))
     | TM tm ->
       TM (renameStatesTM tm (IdGenerator.gen("")))
     | _ -> Error.fatal "rename"
     
 
     (* calculate a composite finite automaton resulting from a plus operation *)	
     let evalPlusFA (fa: FiniteAutomaton.t) 
                   (fb: FiniteAutomaton.t): FiniteAutomaton.t = 
 
       let qI = str2state (IdGenerator.gen("q")) in
       let ta = (qI, epsilon,fa.initialState) in
       let tb = (qI,epsilon,fb.initialState) in
       {
         alphabet = Set.union fa.alphabet fb.alphabet; 
         states = Set.add qI (Set.union fa.states fb.states);
         initialState = qI;
         transitions = Set.add tb (Set.add ta (Set.union fa.transitions fb.transitions));
         acceptStates = Set.union fa.acceptStates fb.acceptStates
       }
 
     (* Creates a transition between two states in a Finite Automata*)
     let createTransitionFA firstState secondState =
       (firstState, epsilon,secondState) 
 
     (* calculate a composite finite automaton resulting from a sequence operation *)	
     let evalSeqFA (fa: FiniteAutomaton.t) (fb: FiniteAutomaton.t): FiniteAutomaton.t = 
         
       let t = Set.map (fun st -> createTransitionFA st fb.initialState) fa.acceptStates in
       {
         alphabet = Set.union fa.alphabet fb.alphabet; 
         states = Set.union fa.states fb.states;
         initialState = fa.initialState;
         transitions = Set.union t (Set.union fa.transitions fb.transitions);
         acceptStates = fb.acceptStates
       }
 
 
     (*Transforms 2 strings in one string *)
     let makeName2 a b = a^"_#_"^b
 
     (*finds the transions for the 2 states and symbol of the alphabet*)
     let findTransitions a b s transA transB  : FiniteAutomaton.transition3 set = 
 
       let ab = makeName2 a b in
 
       let at = Set.filter (fun (x,s1,y) -> x = a && s1 = s  ) transA in
 
       let bt = Set.filter (fun (x,s1,y) -> x = b && s1 = s  ) transB in
 
       let abt = Set.product at bt in
 
       Set.map (fun ((x1,s1,y1),(x2,s2,y2)) -> (ab,s,makeName2 y1 y2)) abt
 
     let createEmptyTransition a b transA transB  : FiniteAutomaton.transition3 set = 
 
       let ab = makeName2 a b in
       let at = Set.filter (fun (x,s,y) -> x = a && s = epsilon ) transA in
       let bt = Set.filter (fun (x,s,y) -> x = b && s = epsilon ) transB in
       let abt = Set.product at bt in
 
       let emptyAB = Set.map (fun ((x1,s1,y1),(x2,s2,y2)) -> (ab,epsilon,makeName2 y1 y2)) abt in
       let emptyA = Set.map (fun (x,s,y) -> ab,epsilon,makeName2 y b) at in
       let emptyB = Set.map (fun (x,s,y) -> ab,epsilon,makeName2 a y) bt in
 
       Set.union emptyAB (Set.union emptyA emptyB)
 
 
 
     (*performs findTransitions for every symbol of the alphabet*)
     let findTransitions2 a b  transA transB alphabet  : FiniteAutomaton.transition3 set = 
 
       let t = Set.flat_map (fun s -> findTransitions a b s transA transB) alphabet in
       let emptyt = createEmptyTransition a b transA transB in
       Set.union t emptyt
 
     (* calculate a composite finite automaton resulting from a intersection operation *)	
     let evalIntersectFA (fa: FiniteAutomaton.t) (fb: FiniteAutomaton.t): FiniteAutomaton.t =
 
       let s = Set.product fa.states fb.states in
       let newAlphabet = Set.inter fa.alphabet fb.alphabet in
       let trans = Set.flat_map (fun (a,b) -> findTransitions2 a b fa.transitions fb.transitions newAlphabet ) s in
       let newStates = Set.map (fun (a,b) -> makeName2 a b) s in
       let s1 = Set.product fa.acceptStates fb.acceptStates in
       let newAccept = Set.map (fun (a,b)  -> makeName2 a b) s1 in
       {
         alphabet = newAlphabet; 
         states =  newStates;
         initialState = makeName2 fa.initialState fb.initialState;
         transitions =  trans;
         acceptStates = newAccept
       }
 
 
     (* calculate a composite finite automaton resulting from a star operation *)	
     let evalStarFA (ft: FiniteAutomaton.t) : FiniteAutomaton.t = 
         
       let qI = str2state (IdGenerator.gen("q")) in
       let ta = (qI, epsilon,ft.initialState) in
       let t = Set.map (fun st -> createTransitionFA st ft.initialState) ft.acceptStates in
       {
         alphabet = ft.alphabet; 
         states = Set.add qI ft.states;
         initialState = qI;
         transitions = Set.add ta (Set.union t ft.transitions);
         acceptStates = Set.add qI ft.acceptStates
       }
 
 
     
      
   
   (* calculate a composite finite automaton *)
   (*Pre: c already renamed*)
   let rec calcEvalFA (c: t): FiniteAutomaton.t =
     match c with
     | Plus (a,b) ->
         let fa = calcEvalFA a in 
         let fb = calcEvalFA b in
           evalPlusFA fa fb
     | Seq (a,b) ->
         let fa = calcEvalFA a in
         let fb = calcEvalFA b in
         evalSeqFA fa fb	
     | Intersect (a,b) ->
       let fa = calcEvalFA a in
       let fb = calcEvalFA b in
       evalIntersectFA fa fb
     | Star t ->
         let ft = calcEvalFA t in
         evalStarFA ft
     | FA fa ->
       fa
     |  _ ->
       Error.fatal "calcEvalFA"
 
 
   (* calculate a composite regular expression resulting from a plus operation *)	
   let evalPlusRE (ra: RegularExpression.t) (rb: RegularExpression.t) : RegularExpression.t =
     Plus(ra, rb)
 
   
 
   (* calculate a composite regular expression resulting from a sequence operation *)	
   let evalSeqRE (ra: RegularExpression.t) (rb: RegularExpression.t) : RegularExpression.t =
     Seq(ra, rb)
 
   
   (* calculate a composite regular expression resulting from a intersection operation *)	
   let evalIntersectRE (ra: RegularExpression.t) (rb: RegularExpression.t) : RegularExpression.t =
     let fa = PolyBasic.re2fa ra in
     let fb = PolyBasic.re2fa rb in
     let faComp = evalIntersectFA fa fb in
      PolyBasic.fa2re faComp
 
   (* calculate a composite regular expression resulting from a star operation *)	
   let evalStarRE (rt: RegularExpression.t) : RegularExpression.t =
     Star rt
 
   (* calculate a composite Regular Expression *)
   let rec calcEvalRE (c: t): RegularExpression.t =
     match c with
     | Plus (a,b) ->
         let ra = calcEvalRE a in 
         let rb = calcEvalRE b in
           evalPlusRE ra rb
     | Seq (a,b) ->
         let ra = calcEvalRE a in
         let rb = calcEvalRE b in
         evalSeqRE ra rb
     | Intersect (a,b) ->
       let ra = calcEvalRE a in
       let rb = calcEvalRE b in
       evalIntersectRE  ra rb
     | Star t ->
         let rt = calcEvalRE t in
         evalStarRE rt
     | RE re ->
       re
     |  _ ->
       Error.fatal "calcEvalRE"
 
 
   (* calculate a composite context free grammar resulting from a plus operation *)	
   let evalPlusCFG (ca: ContextFreeGrammarBasic.t) (cb: ContextFreeGrammarBasic.t) : ContextFreeGrammarBasic.t =
 
     let open ContextFreeGrammarBasic in 
      let s =  str2symb (IdGenerator.gen("S")) in
     let r1 = {head = s; body = [ca.initial]} in
     let r2 = {head = s; body = [cb.initial]} in
     {alphabet = Set.union ca.alphabet cb.alphabet;
     variables =	Set.add s (Set.union ca.variables cb.variables);
     initial = s;
     rules = Set.add r1 (Set.add r2 (Set.union ca.rules cb.rules))
     }
   
 
 
   (* calculate a composite context free grammar resulting from a sequence operation *)	
   let evalSeqCFG (ca: ContextFreeGrammarBasic.t) (cb: ContextFreeGrammarBasic.t) : ContextFreeGrammarBasic.t =
 
     let open ContextFreeGrammarBasic in 
      let s =  str2symb (IdGenerator.gen("S")) in
     let r1 = {head = s; body = [ca.initial; cb.initial]} in
     {alphabet = Set.union ca.alphabet cb.alphabet;
     variables =	Set.add s (Set.union ca.variables cb.variables);
     initial = s;
     rules =Set.add r1 (Set.union ca.rules cb.rules)
     }
   
 
   (* calculate a composite context free grammar resulting from a star operation *)	
   let evalStarCFG (ct: ContextFreeGrammarBasic.t)  : ContextFreeGrammarBasic.t =
 
     let open ContextFreeGrammarBasic in 
      let s =  str2symb (IdGenerator.gen("S")) in
     let r1 = {head = s; body = [s;ct.initial]} in
     let r2 = {head = s; body = [epsilon]} in
     {alphabet = ct.alphabet;
     variables =	Set.add s ct.variables;
     initial = s;
     rules = Set.add r1 (Set.add r2 ct.rules)
     }		
 
   (* calculate a composite Context Free Grammar *)
   let rec calcEvalCFG (c: t): ContextFreeGrammarBasic.t =
     match c with
     | Plus (a,b) ->
         let ca = calcEvalCFG a in 
         let cb = calcEvalCFG b in
         evalPlusCFG ca cb
     | Seq (a,b) ->
         let ca = calcEvalCFG a in
         let cb = calcEvalCFG b in
         evalSeqCFG ca cb	
     | Star t ->
         let ct = calcEvalCFG t in
         evalStarCFG ct
     | CFG cfg ->
       cfg
     |  _ ->
       Error.fatal "calcEvalCFG"
 
 
   (* calculate a composite pushdown automata resulting from a plus operation *)	
   (* AMD *)
   (* DOES NOT HANDLE LB-TMs *)
   (* DOES NOT HANDLE DIRECTION S *)
   (* DOES NOT HANDLE TWO MULTITAPE TMs *)
   let evalPlusPDA (pa: PushdownAutomaton.t) (pb: PushdownAutomaton.t) : PushdownAutomaton.t =
     
     let qI = str2state (IdGenerator.gen("q")) in
     let sI = str2symb (IdGenerator.gen("s")) in
     let t1 = (qI,sI,epsilon,pa.initialState,[pa.initialStackSymbol]) in
     let t2 = (qI,sI,epsilon,pb.initialState,[pb.initialStackSymbol]) in
     {
       inputAlphabet = Set.union pa.inputAlphabet pb.inputAlphabet;
       stackAlphabet = Set.add sI (Set.union pa.stackAlphabet pb.stackAlphabet);
       states = Set.add qI (Set.union pa.states pb.states);
       initialState = qI;
       initialStackSymbol = sI;
       transitions = Set.add t2 (Set.add t1 (Set.union pa.transitions pb.transitions));
       acceptStates = Set.union pa.acceptStates pb.acceptStates;
       criteria = true
     }
 
   (* Creates a transition between two states in a pushdowm automata *)
   let createTransitionPDA firstState secondState stackSymbol symbolstackAlphabet =
       
     Set.map(fun s -> (firstState,s,epsilon,secondState, [stackSymbol])) symbolstackAlphabet
     
   
   (* calculate a composite pushdown automata resulting from a sequence operation *)	
   let evalSeqPDA (pa: PushdownAutomaton.t) (pb: PushdownAutomaton.t) : PushdownAutomaton.t =
     
     let t = Set.flatten (Set.map (fun st -> createTransitionPDA st pb.initialState pb.initialStackSymbol pa.stackAlphabet) pa.acceptStates) in
     {
       inputAlphabet = Set.union pa.inputAlphabet pb.inputAlphabet;
       stackAlphabet = Set.union pa.stackAlphabet pb.stackAlphabet;
       states = Set.union pa.states pb.states;
       initialState = pa.initialState;
       initialStackSymbol = pa.initialStackSymbol;
       transitions = Set.union t (Set.union pa.transitions pb.transitions);
       acceptStates = pb.acceptStates;
       criteria = true
     }
 
 
   (* calculate a composite pushdown automata resulting from a star operation *)	
   let evalStarPDA (pt: PushdownAutomaton.t)  : PushdownAutomaton.t =
     
     let qI = str2state (IdGenerator.gen("q")) in
     let sI = str2symb (IdGenerator.gen("s")) in
     let t1 = (qI,sI,epsilon,pt.initialState,[pt.initialStackSymbol]) in
     let t = Set.flatten (Set.map (fun st -> createTransitionPDA st pt.initialState pt.initialStackSymbol pt.stackAlphabet) pt.acceptStates) in
     {
       inputAlphabet = pt.inputAlphabet;
       stackAlphabet = Set.add sI pt.stackAlphabet;
       states = Set.add qI pt.states;
       initialState = qI;
       initialStackSymbol = sI;
       transitions = Set.add t1 (Set.union t pt.transitions);
       acceptStates = Set.add qI pt.acceptStates;
       criteria = true
     }
 
 
 
   (* calculate a composite Pushdown Automata *)
   let rec calcEvalPDA (c: t): PushdownAutomaton.t =
     match c with
     | Plus (a,b) ->
         let pa = calcEvalPDA a in 
         let pb = calcEvalPDA b in
         evalPlusPDA pa pb
     | Seq (a,b) ->
         let pa = calcEvalPDA a in
         let pb = calcEvalPDA b in
         evalSeqPDA pa pb
     | Star t ->
         let pt = calcEvalPDA t in
         evalStarPDA pt
     | PDA pda ->
       pda
     |  _ ->
       Error.fatal "calcEvalPDA";;
 
   (* calculate a composite turing machine resulting from a plus operation *)	
   let evalPlusTM (ta: TuringMachine.t) (tb: TuringMachine.t): TuringMachine.t =
 
     let qI = str2state (IdGenerator.gen("q")) in
     let t1 = (qI,[empty],ta.initialState,[empty],[L]) in
     let t2 = (ta.initialState,[empty],ta.initialState,[empty],[R]) in
     let t3 = (qI,[empty],tb.initialState,[empty],[L]) in
     let t4 = (tb.initialState,[empty],tb.initialState,[empty],[R]) in
     let t = Set.make [t1;t2;t3;t4] in
     {
       entryAlphabet = Set.union ta.entryAlphabet tb.entryAlphabet;
       tapeAlphabet = Set.add empty (Set.union ta.tapeAlphabet tb.tapeAlphabet);
       empty = empty;
       states = Set.add qI (Set.union ta.states tb.states);
       initialState = qI;
       transitions = Set.union t (Set.union ta.transitions tb.transitions);
       acceptStates = Set.union ta.acceptStates tb.acceptStates;
       criteria = true;
       lbMarkers = ta.lbMarkers;
       _nTapes = 1
     }

   
 
   (* Creates a transition between two states in a Turing Machine*)
   let createTransitionTM firstState secondState tapeAlphabetTA =
       
     Set.map(fun s -> (firstState,[s],secondState,[s],[R])) tapeAlphabetTA
 
   (* calculate a composite turing machine resulting from a sequence operation *)	
   let evalSeqTM (ta: TuringMachine.t) (tb: TuringMachine.t): TuringMachine.t =
 
     let t = Set.flatten (Set.map (fun st -> createTransitionTM st tb.initialState ta.tapeAlphabet) ta.acceptStates) in
     
     {
       entryAlphabet = Set.union ta.entryAlphabet tb.entryAlphabet;
       tapeAlphabet = Set.add empty (Set.union ta.tapeAlphabet tb.tapeAlphabet);
       empty = empty;
       states = Set.union ta.states tb.states;
       initialState = ta.initialState;
       transitions = Set.union t (Set.union ta.transitions tb.transitions);
       acceptStates = tb.acceptStates;
       criteria = true;
       lbMarkers = ta.lbMarkers;
       _nTapes = 1
     }
 
   (* calculate a composite turing machine resulting from a star operation *)	
   let evalStarTM (tt: TuringMachine.t) : TuringMachine.t =
    let qI = str2state (IdGenerator.gen("q")) in
    let t1 = (qI,[empty],tt.initialState,[empty],[L]) in
    let t2 = (tt.initialState,[empty],tt.initialState,[empty],[R]) in
     let t = Set.flatten (Set.map (fun st -> createTransitionTM st tt.initialState tt.tapeAlphabet) tt.acceptStates) in
     
     {
       entryAlphabet = tt.entryAlphabet;
       tapeAlphabet = Set.add empty tt.tapeAlphabet;
       empty = empty;
       states = Set.add qI tt.states;
       initialState = qI;
       transitions = Set.add t2 (Set.add t1 (Set.union t tt.transitions));
       acceptStates = Set.add qI tt.acceptStates;
       criteria = true;
       lbMarkers = tt.lbMarkers;
       _nTapes = 1
     }
   
   (* Auxiliar function *)
   let direction2direction3 dir : direction = if dir = L then L else R
   (*creates the transions for the 2 states *)
   let createsTransitionsInter (a: state) (b: state) (transA: TuringMachine.transitions) (transB: TuringMachine.transitions)  : TuringMachine.transition set = 
 
     let ab = makeName2 a b in
 
     let at = Set.filter (fun (sa,x,s,y,d) -> sa = a ) transA in
 
     let bt = Set.filter (fun (sb,x,s,y,d) -> sb = b ) transB in
 
     let abt = Set.product at bt in
     
	 let f (a, b) =
		match a, b with
		| (sa,[x1],s1,[y1],[d1]), (sb,[x2],s2,[y2],[d2]) ->
			(ab,[x1;x2], makeName2 s1 s2,[y1;y2],
				[direction2direction3 d1; direction2direction3 d2])
		| _, _ ->
			failwith "createsTransitionsInter"
	 in
		Set.map f abt
   
   let evalIntersectTM (ta: TuringMachine.t) (tb: TuringMachine.t): TuringMachine.t =
 
     let s = Set.product ta.states tb.states in
     let newEntryAlphabet = Set.inter ta.entryAlphabet tb.entryAlphabet in
     let trans = Set.flat_map (fun (a,b) -> createsTransitionsInter a b ta.transitions tb.transitions ) s in
     let newStates = Set.map (fun (a,b) -> makeName2 a b) s in
     let acceptS = Set.product ta.acceptStates tb.acceptStates in
     let newAccept = Set.map (fun (a,b)  -> makeName2 a b) acceptS in
 
     {
       entryAlphabet = newEntryAlphabet;
       tapeAlphabet = Set.union ta.tapeAlphabet tb.tapeAlphabet;
       empty = empty;
       states = newStates;
       initialState = makeName2 ta.initialState tb.initialState;
       transitions = trans;
       acceptStates = newAccept;
       criteria = true; (* true = acceptStates | false = stop *)
       lbMarkers = ta.lbMarkers;
       _nTapes = 1
     }
 
   (* calculate a composite Turing Machine *)
   let rec calcEvalTM (c: t): TuringMachine.t =
     match c with
     | Plus (a,b) ->
         let ta = calcEvalTM a in 
         let tb = calcEvalTM b in
         evalPlusTM ta tb
     | Seq (a,b) ->
         let ta = calcEvalTM a in
         let tb = calcEvalTM b in
         evalSeqTM ta tb
    | Intersect (a,b)->
         let ta = calcEvalTM a in
         let tb = calcEvalTM b in
         evalIntersectTM ta tb
     | Star t ->
         let tt = calcEvalTM t in
         evalStarTM tt
     | TM tm ->
       tm
     |  _ ->
       Error.fatal "calcEvalTM"

 
   (* tranforms a composition of elements to a composition of finite automaton *)
   (*Pre: c isFAConvertivel*)		
   let rec comp2facomp (c: t): t =
     match c with
       | Plus (a,b) ->
           Plus (comp2facomp a, comp2facomp b)
       | Seq (a,b) ->
           Seq (comp2facomp a, comp2facomp b)
       | Intersect (a,b) ->
           Intersect (comp2facomp a, comp2facomp b)
       | Star t ->
           Star (comp2facomp t)
       | FA fa ->
           FA fa
       | RE re ->
           FA (PolyBasic.re2fa re)
       | CFG cfg ->
         FA (PolyBasic.cfg2fa cfg)			
       | PDA pda ->
         FA (PolyBasic.pda2fa pda)
      | TM tm ->
         let tmobj = new TuringMachine.model (Representation tm) in
         FA (tmobj#downgradeModelToFiniteAutomaton)#representation	
      | _ -> Error.fatal "comp2facomp"
 
   
 
   (* tranforms a composition of elements to a composition of regular expressions *)
   (*Pre: c isREConvertivel*)		
   let rec comp2recomp (c: t): t =
     match c with
       | Plus (a,b) ->
           Plus (comp2recomp a, comp2recomp b)
       | Seq (a,b) ->
           Seq (comp2recomp a, comp2recomp b)
       | Intersect (a,b) ->
           Intersect (comp2recomp a, comp2recomp b)
       | Star t ->
           Star (comp2recomp t)
       | RE re ->
           RE re
       | FA fa ->
           RE (PolyBasic.fa2re fa)
       | CFG cfg ->
           RE (PolyBasic.cfg2re cfg)
       | PDA pda ->
           RE (PolyBasic.pda2re pda)
       | TM tm ->
         let tmobj = new TuringMachine.model (Representation tm) in
         RE (PolyModel.fa2re (tmobj#downgradeModelToFiniteAutomaton))#representation			
       | _ -> Error.fatal "comp2recomp"
     
   (* tranforms a composition of elements to a composition of Context Free Grammar *)
   (*Pre: c isCFGConvertivel*)		
   let rec comp2CFGcomp (c: t): t =
     match c with
       | Plus (a,b) ->
           Plus (comp2CFGcomp a, comp2CFGcomp b)
       | Seq (a,b) ->
           Seq (comp2CFGcomp a, comp2CFGcomp b)
       | Intersect (a,b) ->
           Intersect (comp2CFGcomp a, comp2CFGcomp b)
       | Star t ->
           Star (comp2CFGcomp t)
       | CFG cfg ->
           CFG cfg 
       | PDA pda ->
           CFG (PolyBasic.pda2cfg pda)
       | FA fa ->
           CFG (PolyBasic.fa2cfg fa)
       | RE re ->
           CFG (PolyBasic.re2cfg re)
       | _ -> Error.fatal "comp2CFGcomp"
 
   (* tranforms a composition of elements to a composition of Pushdown Automata *)
   (*Pre: c isPDAConvertivel*)		
   let rec comp2PDAcomp (c: t): t =
     match c with
       | Plus (a,b) ->
           Plus (comp2PDAcomp a, comp2PDAcomp b)
       | Seq (a,b) ->
           Seq (comp2PDAcomp a, comp2PDAcomp b)
       | Intersect (a,b) ->
           Intersect (comp2PDAcomp a, comp2PDAcomp b)
       | Star t ->
           Star (comp2PDAcomp t)
       | CFG cfg ->
           PDA (PolyBasic.cfg2pda cfg)
       | PDA pda ->
           PDA pda
       | FA fa ->
           PDA (PolyBasic.fa2pda fa)		
       | RE re ->
           PDA (PolyBasic.re2pda re)				
       | _ -> Error.fatal "comp2PDAcomp"
   
   (* tranforms a composition of elements to a composition of Turing Machine*)
   (*Pre: c isTMConvertivel*)		
   let rec comp2TMcomp (c: t): t =
     match c with
       | Plus (a,b) ->
           Plus (comp2TMcomp a, comp2TMcomp b)
       | Seq (a,b) ->
           Seq (comp2TMcomp a, comp2TMcomp b)
       | Intersect (a,b) ->
           Intersect (comp2TMcomp a, comp2TMcomp b)
       | Star t ->
           Star (comp2TMcomp t)
       | CFG cfg ->
           TM (PolyBasic.cfg2tm cfg)					
       | PDA pda ->
           TM (PolyBasic.pda2tm pda)	
       | FA fa ->
           TM (PolyBasic.fa2tm fa)	
       | RE re ->
           TM (PolyBasic.re2tm re)
       | TM tm ->
         TM tm			
       | _ -> Error.fatal "comp2PDAcomp"
      
   
   (* calculate a composition of elements into a finite automaton *)
   let evalMixFA (c:t) : FiniteAutomaton.t = 
     let c1  = comp2facomp c in
     let c2 = rename c1 in
     calcEvalFA c2
 
   (* calculate a composition of elements into a Regular Expression *)
   let evalMixRE (c:t) : RegularExpression.t = 
     let c1  = comp2recomp c in
     calcEvalRE c1
 
   (* calculate a composition of elements into a Context Free Grammar *)
   let evalMixCFG (c:t) : ContextFreeGrammarBasic.t = 
     let c1  = comp2CFGcomp c in
     let c2 = rename c1 in
     calcEvalCFG c2
 
   (* calculate a composition of elements into a Pushdown Automata *)
   let evalMixPDA (c:t) : PushdownAutomaton.t = 
     let c1  = comp2PDAcomp c in
     let c2 = rename c1 in
     calcEvalPDA c2
 
   (* calculate a composition of elements into a Turing Machine *)
   let evalMixTM (c:t) : TuringMachine.t = 
     let c1  = comp2TMcomp c in
     let c2 = rename c1 in
     calcEvalTM c2
   
   (*auxiliar functions*)
	let fx a =	
		match a with
		| (s,[symb],nextS,[nextSymb],[dir]) -> symb == nextSymb && dir == R
		| _ -> failwith "fx"
	let isTM2FA (tm : TuringMachine.t) : bool =
		Set.for_all fx tm.transitions
 
   (* checks if a composition of elements is convertivel to Finite Automaton *)
   let rec isFAConvertivel(c:t): bool =
     match c with
       | Plus (a,b) ->
         isFAConvertivel a && isFAConvertivel b
       | Seq (a,b) ->
         isFAConvertivel a && isFAConvertivel b
       | Intersect (a,b) ->
         isFAConvertivel a && isFAConvertivel b
       | Star t ->
         isFAConvertivel t
       | FA fa -> 
         true
       | RE re ->
         true
       | CFG cfg ->
         let cfgobj = new ContextFreeGrammarBasic.model (Representation cfg) in
         cfgobj#isRegular
       | PDA pda ->
         let pdaobj = new PushdownAutomaton.model (Representation pda) in
         pdaobj#isFiniteAutomaton
       | TM tm ->
         isTM2FA tm
       | _ -> 
         false
 
   (* checks if a composition of elements is convertivel to Regular Expression *)			
   let rec isREConvertivel(c:t): bool =
     match c with
       | Plus (a,b) ->
         isREConvertivel a && isREConvertivel b
       | Seq (a,b) ->
         isREConvertivel a && isREConvertivel b
       | Intersect (a,b) ->
         isREConvertivel a && isREConvertivel b
       | Star t ->
         isFAConvertivel t
       | FA fa -> 
         true
       | RE re ->
         true
       | CFG cfg -> 
         let cfgobj = new ContextFreeGrammarBasic.model (Representation cfg) in
         cfgobj#isRegular
       | PDA pda ->
         let pdaobj = new PushdownAutomaton.model (Representation pda) in
         pdaobj#isFiniteAutomaton
       | TM tm ->
         isTM2FA tm
       | _ -> 
         false
 
   (* checks if a composition of elements is convertivel to Context free grammar *)
   let rec isCFGConvertivel(c:t): bool =
     match c with
       | Plus (a,b) ->
         isCFGConvertivel a && isCFGConvertivel b
       | Seq (a,b) ->
         isCFGConvertivel a && isCFGConvertivel b
       | Intersect (a,b) ->
         isCFGConvertivel a && isCFGConvertivel b
       | Star t ->
         isCFGConvertivel t
       | CFG fa -> 
         true
       | PDA re ->
         true
       | FA fa ->
         true
       | RE re ->
         true
       | _ -> 
         false
 
   (* checks if a composition of elements is convertivel to pushdown automata *)
   let rec isPDAConvertivel(c:t): bool =
     match c with
       | Plus (a,b) ->
         isPDAConvertivel a && isPDAConvertivel b
       | Seq (a,b) ->
         isPDAConvertivel a && isPDAConvertivel b
       | Intersect (a,b) ->
         isPDAConvertivel a && isPDAConvertivel b
       | Star t ->
         isPDAConvertivel t
       | CFG cfg -> 
         true
       | PDA re ->
         true
       | FA fa ->
         true
       | RE re ->
         true
       | _ -> 
         false
   
   (* checks if a composition of elements is convertivel to turing machine *)
   let rec isTMConvertivel(c:t): bool =
     match c with
       | Plus (a,b) ->
         isTMConvertivel a && isTMConvertivel b
       | Seq (a,b) ->
         isTMConvertivel a && isTMConvertivel b
       | Intersect (a,b) ->
         isTMConvertivel a && isTMConvertivel b
       | Star t ->
         isTMConvertivel t
       | CFG cfg -> 
         true
       | PDA re ->
         true
       | FA fa ->
         true
       | RE re ->
         true
       | TM tm ->
         true
      | _ -> 
         false
 
 
 
   let isFA (c:t) : bool =
     match c with 
       | FA _ -> true
       | _ -> false
 
   (*transforms everything in type t *)
   let rec transformt (c: t) : t =
     match c with
       | Plus (a,b) ->
         Plus (transformt a, transformt b)
       | Seq (a,b) ->
         Seq (transformt a, transformt b)
       | Intersect (a,b) ->
         Intersect (transformt a, transformt b)
       | Star t ->
         Star (transformt t)
       | FA fa -> 
         FA fa
       | RE re ->
         RE re
       | CFG cfg -> 
         CFG cfg
       | PDA pda ->
         PDA pda
       | FAO fao ->
         FA fao#representation
       | REO reo ->
         RE reo#representation
       | CFGO cfgo ->
         CFG cfgo#representation
       |	PDAO pdao ->
         PDA pdao#representation 
       | Rep str ->
         (try
           let m = Repository.get str in
             transformt m
         with Not_found -> Error.fatal "Composition with invalid repository name")
       | _ -> 
         Error.fatal "transformt"
 
 
   
   (* calculate a composite finite automaton given a composition of elements *)		
   let evalFA (c: t) : FiniteAutomaton.t  =
     let c1 = transformt c in
     match isFAConvertivel c1 with
       | true -> evalMixFA c1 
       | false -> Error.fatal "evalFA"
 
   (* calculate a composite regular expression given a composition of elements *)		
   let evalRE (c: t) : RegularExpression.t  =
     let c1 = transformt c in
     match isREConvertivel c1 with
       | true -> evalMixRE c1
       | false -> Error.fatal "evalRE"
 
   (* calculate a composite context free grammar given a composition of elements *)		
   let evalCFG (c: t) : ContextFreeGrammarBasic.t  =
     let c1 = transformt c in
     match isCFGConvertivel c1 with
       | true -> evalMixCFG c1
       | false -> Error.fatal "evalCFG"
 
   (* calculate a composite pushdown automata given a composition of elements *)		
   let evalPDA (c: t) : PushdownAutomaton.t  =
     let c1 = transformt c in
     match isPDAConvertivel c1 with
       | true -> evalMixPDA c1											
       | false -> Error.fatal "evalPDA"
 
  (* calculate a composite turing machine given a composition of elements *)
   let evalTM (c: t) : TuringMachine.t  =
     let c1 = transformt c in
     match isTMConvertivel c1 with
       | true -> evalMixTM c1											
       | false -> Error.fatal "evalTM"
 
   let setRep (c: t) (name: string) : unit  = 
     Repository.update name c
   
   let getRep (name: string) : t =
     try
       Repository.get name
     with Not_found -> Error.fatal "getRep"
 
         
   let findRep (name: string ) : bool = 
     Repository.exists name
 
   let validate (name: string) (comp: t) : unit = ()
 

   
  let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
	let make (arg: t Arg.alternatives): t = make arg validate


   let _ = makeCompositionRef := make
	(* Exercices support *)
  let checkProperty (comp: t) (prop: string) =
		match prop with
			| "composition" -> true
			| _ -> Model.checkProperty prop

	let checkExercise ex comp = Model.checkExercise ex (accept comp) (checkProperty comp)	
	let checkExerciseFailures ex comp = Model.checkExerciseFailures ex (accept comp) (checkProperty comp)

   (* Class *)
   class model (arg: t Arg.alternatives) =
     object(self) inherit Model.model (make2 arg) as super	
     (* Representation *)
       method representation = representation
     (* Kind *)
			method isComposition : bool = true
     (* Show *)			
       method toJSon: JSon.t = toJSon representation 
       method toJSon2: JSon.t = toJSon2 id representation
       method show: unit = show representation
       method show2: unit = show2 id representation
 
       method accept (w: word): bool = accept representation w
 
       method generate (length: int): words = generate representation length
    
       method evalFA : FiniteAutomaton.t = evalFA representation

       method evalPDA : PushdownAutomaton.t = evalPDA representation

       method evalRE : RegularExpression.t = evalRE representation

       method evalCFG : ContextFreeGrammarBasic.t = evalCFG representation
       
       method evalTM : TuringMachine.t = evalTM representation

     (* Ops *)(*
       method acceptBreadthFirst (w: word): bool = acceptBreadthFirst representation w
       method accept (w: word): bool = accept representation w
       method acceptFull (w: word) : bool * path * trail = acceptFull representation w
 
       method acceptWithTracing (w:word): unit = acceptWithTracing representation w
       method generate (length: int): words = generate representation length
       method generateUntil (length: int): words = generateUntil representation length
 
       method reachable (s:state): states = reachable representation s
       method productive: states = productive representation
       method getUsefulStates: states = getUsefulStates representation
       method getUselessStates: states = getUselessStates representation
       method cleanUselessStates: model =
         let fa = cleanUselessStates representation in
           new model (Arg.Representation fa)
       method areAllStatesUseful: bool = areAllStatesUseful representation
 
       method toDeterministic: model =
         let fa = toDeterministic representation in
           new model (Arg.Representation fa)
       method isDeterministic: bool = isDeterministic representation
 
       method equivalencePartition: states set = equivalencePartition representation
       method minimize: model =
         let fa = minimize representation in
           new model (Arg.Representation fa)
       method isMinimized: bool = isMinimized representation*)
     (* Exercices support *)
       method checkProperty (prop: string) =  checkProperty representation prop
       
      
     (* Learn-OCaml support *)
       method moduleName = ""
       method xTypeName = ""
       method xTypeDeclString : string = ""
       method toDisplayString (name: string): string = ""
       method example : JSon.t = JNull
       
     end
               
    
 end
 
 


# 3 "src/TopLevel.ml"
(*
 * TopLevel.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
 * feb/2021 (amd) - Added some missing functions.
 * feb/2020 (jg) - Initial version.
 *)

(*
 * Description: Set of functions with simple signatures to the used in the
 * ocaml toplevel system. In a sense, this provides a command-line interface
 * to most of the functionalities of the OCamlFLAT library.
 *
 * TODO: Improve.
 *)

(*

let f str =
	let r = fa_accept fa str in
	let q = stats() in
	let t = fa_acceptTrail fa str in
	let x = stats() in
	let p = fa_acceptPath fa str in
	let y = stats() in
	let (_,p1,t1) = fa_acceptFull fa str in
	let z = stats() in
	let w =  if t = t1 && p = p1 then "OK" else "BAD" in
		(r,q,x,y,z,w)
;;

#print_depth 10000;;
#print_length 10000;;


*)

open FiniteAutomatonTop


# 1 "src/LearnOCaml.ml"
(*
 * LearnOCaml.ml
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
 *  Written by Artur Miguel Dias, Rita Macedo (amd, rm)
 *)

(*
 * ChangeLog:
 *
 * jul/2021 (amd) - Added semantic validation of the student's solution.
 * jun/2021 (amd) - Added support for typed student answers in the file
 *                  "template.ml". Many improvements in the implementation,
 *                  and managed to get rid of many technical
 *                  complexities in the file "template.ml".
 * mar/2021 (amd, rm) - Initial version
 *)

(*
 * Description: This module helps in the use of the OCamlFLAT library
 * inside Learn-OCaml (the platform for learning the OCaml language). The goal
 * is to support FLAT related exercises inside Learn-OCaml. 
 *  
 * As for FLAT exercises developed for current text-based interaction of
 * Learn-OCaml, our current approach is to avoid changing Learn-OCaml
 * itself.
 * 
 * The current solution comprehends:
 *
 * - A technique that allows the OCamlFLAT library to be available inside the
 *   exercise environment of Learn-OCaml (via the file "prepare.ml").
 *   
 * - The idea of reducing FLAT model analysis to OCaml function analysis. This
 *   allows us to represent FLAT exercises using what is available in
 *   Learn-OCaml, without changing anything in Learn-OCaml.
 *   
 * - This module, which supplies some functions that helps in
 *   the creation by hand of FLAT exercises following the conventions
 *   of Learn-OCaml.
 *   
 * - A translator from the OCamlFLAT exercise format to the Learn-OCaml
 *   exercise format. The translator generates a directory containing all
 *   the usual files: "template.ml", "solution.ml", "meta.json", etc.
 *)

open BasicTypes

module type LearnOCamlSig =
sig
	val setOCamlFlatDir : string -> unit
	val setExercicesDir : string -> unit
	val setExerciceName : string -> unit
	val processAnswer : Model.model
					-> Exercise.exercise -> (string * int) list
	val decl2json : string -> JSon.t
	val generateExerciseDir : JSon.t -> JSon.t -> bool -> unit
end

module LearnOCaml : LearnOCamlSig =
struct
	(* ----- Dir/File management ----- *)
	let oCamlFlatDir = ref ""
	let exercicesDir = ref ""
	let exerciceName = ref ""		

	let setOCamlFlatDir dirname =
		oCamlFlatDir := Util.handleHomeDir dirname

	let setExercicesDir dirname =
		exercicesDir := Util.handleHomeDir dirname

	let setExerciceName filename =
		exerciceName := filename

	let initialize () =
		if !oCamlFlatDir = "" then
			begin
				setOCamlFlatDir
					"~/work/OCamlFlat";
				setExercicesDir
					"~/work/learn-test/my-learn-ocaml-repository/exercises";
				setExerciceName
					"default"
			end

	let libFile () =
		!oCamlFlatDir ^ "/lib/OCamlFlat.ml"

	let targetDir () =
		!exercicesDir ^ "/" ^ !exerciceName
	
	let targetFile fileName =
		targetDir () ^ "/" ^ fileName
	
	let adjust txt =
		Util.stripHead txt
 
	let createTargetDir () =
		ignore (Sys.command ("mkdir -p " ^ targetDir ()) )

	let createTargetFile fileName text =
		let co = open_out (targetFile fileName) in
		let text = adjust text in
		begin
			output_string co text;
			close_out co
		end

	let getExerciceDirContents () =
		Array.to_list (Sys.readdir !exercicesDir)
	
	(* ----- Utility functions ----- *)
	let processUnitTest m expected w =
			(word2str w, expected, m#accept w = expected)

	let semanticValidation (m: Model.model) =
		m#errors

	let convertSemanticValidationResult mesg =
			(mesg, 0)

	let processUnitTests (m: Model.model) (e: Exercise.exercise) =
		let open Exercise in
		let rep = e#representation in
			List.map (processUnitTest m true) (Set.toList rep.inside)
			@
			List.map (processUnitTest m false) (Set.toList rep.outside)
			
	let convertUnitTestResult (word, acceptance, passed) =
		let ar = if acceptance then "Acceptance" else "Rejection" in
		let pf = if passed then "passed" else "failed" in
		let points = if passed then 1 else 0 in
			(ar ^ " of word \"" ^ word ^ "\" " ^ pf, points)

	let processProperty m p =
		(p, m#checkProperty p)
	
	let processProperties (m: Model.model) (e: Exercise.exercise) =
		let open Exercise in
		let rep = e#representation in
		let props = Set.toList rep.properties in
			List.map (processProperty m) props	
		
	let convertPropertyResult (property, passed) =
		let pf = if passed then "passed" else "failed" in
		let points = if passed then 3 else 0 in
			("Property \"" ^ property ^ "\" " ^ pf, points)

	let finalResult0 res =
		[("###  Checking for static semantic errors...", -999)]
		@ res
		@ [("### Errors found", -999)]

	let finalResult1 res1 res2 =
		[]
		@ [("###  Checking for static semantic errors...", -999)]
		@ [("### Checking unit tests...", -999)]
		@ res1
		@ [("### Checking properties...", -999)]
		@ res2
		@ [("### Done", -999)]

	let processAnswer (m: Model.model) (e: Exercise.exercise) =
		let semanticValidationResults = semanticValidation m in
		let res0 = List.map convertSemanticValidationResult semanticValidationResults in
		if res0 <> [] then
			finalResult0 res0
		else
			let unitTestsResults = processUnitTests m e in
			let res1 = List.map convertUnitTestResult unitTestsResults in
			let propertyResults = processProperties m e in
			let res2 = List.map convertPropertyResult propertyResults in
				finalResult1 res1 res2

	let stdKind kind =
		match kind with
		| "finiteAutomaton" | "FiniteAutomaton.tx" ->
			FiniteAutomaton.kind
		| "regularExpression" | "RegularExpression.tx" ->
			RegularExpression.kind
		| "ContextFreeGrammarBasic" | "ContextFreeGrammarBasic.tx" ->
			ContextFreeGrammarBasic.kind
		| "finiteEnumeration" | "FiniteEnumeration.tx" ->
			FiniteEnumeration.kind
		| _ ->
			"*** invalid ***"

	let completeJSon kind j  =
		match kind with
		| "regularExpression" | "RegularExpression.tx" ->
			JSon.makeAssoc [("re", j)]
		| "finiteEnumeration" | "FiniteEnumeration.tx" ->
			JSon.makeAssoc [("words", j)]
		| _ ->
			j

	let decl2json s =
		try
			let a = String.index_from s 0 ':' in
			let b = String.index_from s a '=' in
			let kind = String.trim (String.sub s (a+1) (b-a-1)) in
			let ocamlExp = String.sub s (b+1) (String.length s -b-1) in
			let jExp = JSon.parseOon ocamlExp in
			let mainJSon = completeJSon kind jExp in
			let jHead = Entity.toJSon (Entity.dummyId (stdKind kind)) in
				JSon.append jHead mainJSon
		with _ ->
			JSon.JNull
	
	(* ----- FILE descr.html ----- *)
	let fileName =
		"descr.html"
	
	let contents (exercise: JSon.t) =
		Printf.sprintf
{ooo_descr_html_ooo|
		<h3> %s </h3>
		<p> %s </p>
|ooo_descr_html_ooo}
		(JSon.fieldString exercise "description")
		(JSon.fieldString exercise "problem")
	
	let generateFile_Descr (exercise: JSon.t) =
		let text = contents exercise in
			createTargetFile fileName text

	(* ----- FILE meta.json ----- *)
	let fileName =
		"meta.json"
		
	let contents (exercise: JSon.t) =
		Printf.sprintf
	{ooo_meta_json_ooo|
		{
		  "learnocaml_version" : "1",
		  "kind" : "exercise",
		  "stars" : 0,
		  "title" : "%s"
		}
	|ooo_meta_json_ooo}
		(JSon.fieldString exercise "description")
	
	let generateFile_Meta (exercise: JSon.t) =
		let text = contents exercise in
			createTargetFile fileName text

	(* ----- FILE prelude.ml ----- *)
	let fileName =
		"prelude.ml"

	let generateFile_Prelude (solution: Model.model) =
		let text = solution#xTypeDeclString in
			createTargetFile fileName text
	
	(* ----- FILE prepare.ml ----- *)
	let fileName =
		"prepare.ml"

	let generateFile_Prepare () =
		let cmd = "cp -a " ^ libFile () ^ " " ^ targetFile fileName in
			ignore (Sys.command cmd)

	(* ----- FILE solution.ml ----- *)
	let fileName =
		"solution.ml"

	let contentsJSon (solution: Model.model) =
		Printf.sprintf
	{ooo_solution_ml_ooo|
		let solution = {| %s |}
	|ooo_solution_ml_ooo}
		(JSon.toStringN 2 solution#toJSon)

	let contents (solution: Model.model) =
		let signature = "\n\t\t(* OCamlFlat exercise *)" in
		let body = solution#toDisplayString "solution" in
			signature ^ body
	
	let generateFile_Solution (solution: Model.model) useJSon =
		let text =
			if useJSon then contentsJSon solution
			else contents solution
		in
			createTargetFile fileName text

	(* ----- FILE template.ml ----- *)
	let fileName =
		"template.ml"

	let contentsJSon (solution: Model.model) =
		Printf.sprintf
	{ooo_template_ml_json_ooo|
		(* Write your solution below, by using the provided example as a template *)

		let solution = {| %s |}
	|ooo_template_ml_json_ooo}
		(JSon.toStringN 2 solution#example)

	let contents (solution: Model.model) =
		Printf.sprintf
	{ooo_template_ml_ooo|
		(* Write your solution below, by using the provided example as a template *)
		%s|ooo_template_ml_ooo}	(* please, do not change this *)
		((PolyModel.json2model solution#example)#toDisplayString "solution")

	let generateFile_Template (solution: Model.model) useJSon =
		let text =
			if useJSon then contentsJSon solution
						else contents solution
		in
			createTargetFile fileName text

	(* ----- FILE test.ml ----- *)
	let fileName =
		"test.ml"
	
	let exercisePart (exercise: JSon.t) =
		Printf.sprintf
	{ooo_exercise_ooo|
		let exercise = {| %s |}
	|ooo_exercise_ooo}
		(JSon.toStringN 2 exercise)

	let handleAnswerPartJSon =
		Printf.sprintf
	{ooo_handle_answer_json_ooo|
		let handleAnswer (): Learnocaml_report.t =
			test_variable_property
				[%%ty: string]
				"solution"
				(fun solution ->
					checkAnswer
						(PolyModel.text2model solution)
						(new Exercise.exercise (Arg.Text exercise))
				)
	|ooo_handle_answer_json_ooo}
	
	let handleAnswerPart (solution: Model.model) =
		Printf.sprintf
	{ooo_handle_answer_ooo|
		let handleAnswer (): Learnocaml_report.t =
			test_variable_property
				[%%ty: %s]
				"solution"
				(fun solution ->
					checkAnswer
						((new %s.model (Arg.Representation (%s.internalize solution))):
										%s.model :> Model.model)
						(new Exercise.exercise (Arg.Text exercise))
				)
	|ooo_handle_answer_ooo}
	solution#xTypeName
	solution#moduleName
	solution#moduleName
	solution#moduleName
		
	let contents exerciseText handleAnswerText =
		Printf.sprintf
	{ooo_test_ml_ooo|
		open Test_lib
		open Report
		%s
		let convertResult (diagnostic, points) =
			match points with
			| _ when points > 0 ->
				Message ([Text diagnostic], Success points)
			| -999 ->
				Message ([Break; Text diagnostic], Informative)
			| _ ->
				Message ([Text diagnostic], Failure)
		
		let checkAnswer (m: Model.model) (e: Exercise.exercise) =
			let res = LearnOCaml.processAnswer m e in
				List.map convertResult res
		%s
		let () =
			set_result @@
			ast_sanity_check code_ast @@
			handleAnswer
	|ooo_test_ml_ooo}
		exerciseText
		handleAnswerText

	let generateFile_Test (exercise: JSon.t) (solution: Model.model) useJSon =
		let ex = exercisePart exercise in
		let hs =
			if useJSon then handleAnswerPartJSon
			else handleAnswerPart solution
		in
		let text = contents ex hs
		in
			createTargetFile fileName text	

	(* ----- FILE index.json ----- *)
	let fileName =
		"../index.json"
		
	let contents (l: string list) =
		Printf.sprintf
	{ooo_index_json_ooo|
		{
		  "learnocaml_version" : "1",
		  "groups" : { "OCamlFLAT": {
		    "title": "OCamlFLAT exercise pack for Learn-OCaml",
		    "exercises": %s
		  } }
		}
	|ooo_index_json_ooo}
		(stringsD l)
	
	let generateFile_Index () =
		let l = getExerciceDirContents () in
		let l = List.filter (fun x -> x <> "index.json") l in
		let text = contents l in
		let text = String.map (fun x -> if x = ';' then ',' else x) text in
			createTargetFile fileName text

	(* ----- generateExerciseDir ----- *)
	
	let generateExerciseDir exercise solution useJSon =
		let solution: Model.model = PolyModel.json2model solution in
			initialize ();
			createTargetDir ();
			generateFile_Descr exercise;
			generateFile_Meta exercise;
			generateFile_Prelude solution;
			generateFile_Prepare ();
			generateFile_Solution solution useJSon;
			generateFile_Template solution useJSon;
			generateFile_Test exercise solution useJSon;
			generateFile_Index ()
end

(*
Learnocaml_report.t:

	type report = item list

	and item =
	  | Section of text * report
	  (** A titled block that groups subreports *)
	  | Message of text * status
	  (** Basic report block *)

	and status =
	  | Success of int (** With given points *)
	  | Failure (** With missed points *)
	  | Warning (** A student error without influence on the grade *)
	  | Informative (** A message for the student *)
	  | Important (** An important message *)

	and text = inline list

	and inline =
	  | Text of string (** A word *)
	  | Break (** Line separator *)
	  | Code of string (** For expressions *)
	  | Output of string (** For output *)
*)
# 1 "src/PreOpen.ml"
open Examples


(*
type symbol = char
type finiteAutomaton = FiniteAutomatonX.tx
type regularExpression = RegularExpression.tx
type contextFreeGrammar = ContextFreeGrammarBasic.tx
type finiteEnumeration = FiniteEnumeration.tx
*)

(* CHECKING *)

(*

let _: finiteAutomaton =
{
	alphabet = ['a'];
	states = ["START"];
	initialState = "START";
	transitions = [("START", 'a', "START")];
	acceptStates = ["START"]
}

let _: contextFreeGrammar =
{
	alphabet = ['['; ']'];
	variables = ['S'];
	initial = 'S';
	rules = ["S -> [S]"; "S -> SS"; "S -> ~"]
}
*)
# 1 "src/Tests.ml"
(*
 * Tests.ml
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
 * jan/2021 (amd) - Initial version.
 *)

(*
 * Description: Set of unit tests for checking the library from time to time.
 *
 * TODO: This is only a starting point. There are already many (disabled) unit
 * tests in several modules and this stuff needs to be reviewed.
 *)

module Tests : sig end =
struct
	open Examples

	let active = false

(*
	open TopLevel



	let test1 () =
		let a = fa_predef "dfa_1" in
			Util.println [if fa_accept a "ab" then "OK" else "ERROR"] *)

	let runAll =
		if Util.testing active "Tests" then begin

		end
end
# 1 "src/JSonTests.ml"
(*
 * JSonTests.ml
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
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: JSon parser tests.
 *)

open BasicTypes

module JSonTests : sig end =
struct
	let active = false

	let jsonSample = {| {
		name: {
			first: "aa",
			last: "22",
			fullname: "33"
		},
		age: "33",
		hobbies: [ "44", "55" ]
	} |}
	
	let jsonSample2 = {| "aa" |}
	
	let test0 () =
		let json = JSon.parse jsonSample in
		let json2 = JSon.parse jsonSample2 in
			JSon.show json; JSon.show json2
	
	let oonSample = {| {
		alphabet = ['a';'b'];
		states = ["START"; "33"];
		initialState = "START";
		transitions = [("START", 'a', "START"); ("START", 'a', "START")];
		acceptStates = ["START"]
	} |}
	
	let oonSample2 = {| "z*" |}

	let oonSample3 = {| ("START", ["ee"], "yu") |}

	let test1 () =
		let oon = JSon.parseOon oonSample in
		let oon2 = JSon.parseOon oonSample2 in
		let oon3 = JSon.parseOon oonSample3 in
			JSon.show oon; JSon.show oon2; JSon.show oon3

	let test () =
		let oon2 = JSon.parseOon oonSample2 in
			JSon.show oon2

	let runAll =
		if Util.testing active "JSon" then begin
			test ()
		end

end
# 1 "src/FiniteEnumerationTests.ml"
(*
 * FiniteEnumerationTests.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: Finite enumeration testing.
 *)

open BasicTypes

module FiniteEnumerationTests : sig end =
struct
	open FiniteEnumeration

	let active = false
	
	let fe_colors = {| {
		kind : "finite enumeration",
		description : "this is an example",
		name : "colors",
		words : ["Red", "Yellow", "Blue"]
	} |}
	
	let exer_colors = {| {
		kind : "exercise",
		description : "this is an example",
		name : "exer_colors",
		problem : "Colors of length 3",
		inside : ["Red", ""],
		outside : ["Yellow","Blue"],
		properties : ["fail"]
	} |}

	let test0 () =
		let (id,fe) = FiniteEnumeration.make2 (Arg.Text fe_colors) in
			Util.sep ();
			show2 id fe

	let test1 () =
		let fe = FiniteEnumeration.make (Arg.Text fe_colors) in
		let ex = Exercise.make (Arg.Text exer_colors) in
		let (ins,outs,props) = FiniteEnumeration.checkExerciseFailures ex fe in
			Util.sep ();
			FiniteEnumeration.show fe;
			Exercise.show ex;
			Exercise.showRes (ins,outs,props)

	let test2 () =
		let fe = new FiniteEnumeration.model (Arg.Text fe_colors) in
		let e = new Exercise.exercise (Arg.Text exer_colors) in
		let (ins,outs,props) = fe#checkExerciseFailures e in	
			Util.sep ();
			fe#show;
			e#show;
			Exercise.showRes (ins,outs,props)
		
	let runAll =
		if Util.testing active "FiniteEnumeration" then begin
			test0 ();
			test1 ();
			test2 ()
		end
end

# 1 "src/FiniteAutomatonTests.ml"
(*
 * FiniteAutomatonTests.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: Finite automata testing.
 *)

open BasicTypes

module FiniteAutomatonTests : sig end =
struct
	open FiniteAutomaton

	let active = false


	let test0 () =
		let fa = new FiniteAutomaton.model (Arg.Predef "fa_abc") in
			let j = fa#toJSon in
				JSon.show j

	let testBug () =
		let fa = new FiniteAutomaton.model (Arg.Predef "fa_abc") in
		let fa2 = fa#toDeterministic in
			let j = fa2#toJSon in
				JSon.show j;
		let fa3 = fa2#cleanUselessStates in
			let j = fa3#toJSon in
				JSon.show j

	let testBug2 () =
		let fa = new FiniteAutomaton.model (Arg.Predef "fa_abc") in
		let fa2 = fa#toDeterministic in
			Util.println ["productive states:"];
			Util.printStates fa2#productive;
			Util.println []

	let faAccept = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "ab123",
		alphabet : ["a", "b"],
		states : ["1", "2", "3"],
		initialState : "1",
		transitions : [
				["1","a","2"], ["1","b","3"],
				["2","b","2"],
				["3","a","3"]
			],
		acceptStates : ["2", "3"]
	} |}

	let faAccept2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b", "c", "d"],
		states : ["START", "A", "AB", "C", "SUCCESS", "D"],
		initialState : "START",
		transitions : [
				["START","a","A"], ["START","~","AB"],
				["A","~","C"],
				["AB","b","SUCCESS"], ["AB","~","SUCCESS"],
				["C","~","SUCCESS"], ["C","d","C"],
				["SUCCESS","~","START"]
			],
		acceptStates : ["SUCCESS"]
	} |}

	let check f w =
		let msg = 
			if f w then "word was accepted" else "word was not accepted"
		in Util.println [msg]

	let testAcceptBF () =
		let fa = new FiniteAutomaton.model (Arg.Text faAccept) in
			check fa#acceptBreadthFirst [];
			check fa#acceptBreadthFirst (word "a");
			check fa#acceptBreadthFirst (word "ab");
			check fa#acceptBreadthFirst (word "b");
			check fa#acceptBreadthFirst (word "ba");
			check fa#acceptBreadthFirst (word "abb");
			check fa#acceptBreadthFirst (word "aba");
			check fa#acceptBreadthFirst (word "baa");
			check fa#acceptBreadthFirst (word "bab");
			Util.println []

	let testAcceptBF2 () =
		let fa = new FiniteAutomaton.model (Arg.Text faAccept2) in
			check fa#acceptBreadthFirst [];
			check fa#acceptBreadthFirst (word "a");
			check fa#acceptBreadthFirst (word "ad");
			check fa#acceptBreadthFirst (word "abad");
			check fa#acceptBreadthFirst (word "c");
			Util.println []

	let testAccept () =
		let fa = new FiniteAutomaton.model (Arg.Text faAccept) in
			check fa#accept [];
			check fa#accept (word "a");
			check fa#accept (word "ab");
			check fa#accept (word "b");
			check fa#accept (word "ba");
			check fa#accept (word "abb");
			check fa#accept (word "aba");
			check fa#accept (word "baa");
			check fa#accept (word "bab");
			Util.println []

	let testAccept2 () =
		let fa = new FiniteAutomaton.model (Arg.Text faAccept2) in
			check fa#accept [];
			check fa#accept (word "a");
			check fa#accept (word "ad");
			check fa#accept (word "abad");
			check fa#accept (word "c");
			Util.println []

	let testAccTrace () =
		let fa = new FiniteAutomaton.model (Arg.Predef "fa_abc") in
			fa#acceptWithTracing (word "abe")

	let faGenerate = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","b","S2"], ["S1","a","S3"], ["S1","~","S3"],
				["S2","~","S3"],
				["S3","~","S3"]
			],
		acceptStates : ["S3"]
	} |}

	let faGenerate2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1", "S2"],
		initialState : "S1",
		transitions : [
				["S1","a","S1"], ["S1","b","S2"],
				["S2","a","S2"], ["S2","b","S1"]

			],
		acceptStates : ["S2"]
	} |}

	let faGenerate3 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a"],
		states : ["S1"],
		initialState : "S1",
		transitions : [
				["S1","a","S1"]
			],
		acceptStates : ["S1"]
	} |}

	let faGenerate4 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a","b"],
		states : ["S1","S2"],
		initialState : "S1",
		transitions : [
				["S1","a","S1"], ["S1","b","S2"],
				["S2","a","S2"]
			],
		acceptStates : ["S1"]
	} |}

	let testGenerate () =
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate) in
			Util.println ["generated words size 0:"]; Util.printWords (fa#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (fa#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (fa#generate 2);
			Util.println ["generated words size 100:"]; Util.printWords (fa#generate 100);
			Util.println []

	let testGenerate2 () =
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate2) in
			Util.println ["generated words size 0:"]; Util.printWords (fa#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (fa#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (fa#generate 2);
			Util.println ["generated words size 3:"]; Util.printWords (fa#generate 3);
			Util.println ["generated words size 4:"]; Util.printWords (fa#generate 4);
			Util.println ["generated words size 18:"]; Util.printWords (fa#generate 18);

			Util.println []

	let testGenerate3 () =
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate3) in
			Util.println ["generated words size 0:"]; Util.printWords (fa#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (fa#generate 1);
			Util.println ["generated words size 10:"]; Util.printWords (fa#generate 10);
			Util.println ["generated words size 50:"]; Util.printWords (fa#generate 50);
			Util.println ["generated words size 100:"]; Util.printWords (fa#generate 100);
			Util.println ["generated words size 1000:"]; Util.printWords (fa#generate 1000);
			Util.println []

	let testGenerate4 () =
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate4) in
			Util.println ["generated words size 0:"]; Util.printWords (fa#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (fa#generate 1);
			Util.println ["generated words size 10:"]; Util.printWords (fa#generate 10);
			Util.println ["generated words size 100:"]; Util.printWords (fa#generate 100);
			Util.println []

	let testGenerateUntil () =
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate) in
			Util.println ["generated words size 5:"]; Util.printWords (fa#generateUntil 5);
			Util.println [];
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate2) in
			Util.println ["generated words size 5:"]; Util.printWords (fa#generateUntil 5);
			Util.println [];
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate3) in
			Util.println ["generated words size 5:"]; Util.printWords (fa#generateUntil 5);
			Util.println [];
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate4) in
			Util.println ["generated words size 5:"]; Util.printWords (fa#generateUntil 5);
			Util.println []

	let faReach = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3"],
		initialState : "S1",
		transitions : [
			],
		acceptStates : ["S1"]
	} |}

	let faReach2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a","b"],
		states : ["S1","S2","S3","S4","S5","S6"],
		initialState : "S1",
		transitions : [
				["S1","~","S2"], ["S1","a","S3"],
				["S2","a","S2"],
				["S3","~","S4"],
				["S4","~","S5"],
				["S5","~","S3"], ["S5","b","S6"], ["S5","~","S5"]
			],
		acceptStates : ["S1"]
	} |}

	let testReachable () =
			let open FiniteAutomaton in
			let fa = new FiniteAutomaton.model (Arg.Text faReach) in
			let fa2 = new FiniteAutomaton.model (Arg.Text faReach2) in
			let start = fa#representation.initialState in
			let start2 = fa2#representation.initialState in
				Util.println ["reachable states:"]; Util.printStates (fa#reachable start); Util.println [];
				Util.println ["reachable states:"]; Util.printStates (fa#reachable start2); Util.println []

	let faProductive = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1","S2","S3","S4"],
		initialState : "S1",
		transitions : [
				["S1","a","S2"], ["S1","b","S3"],
				["S4","a","S2"], ["S4","b","S3"], ["S3","a","S3"]
			],
		acceptStates : ["S4"]
	} |}

	let faProductive2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1","S2","S3","S4","S5","S6","S7"],
		initialState : "S1",
		transitions : [
				["S1","~","S2"], ["S1","a","S2"], ["S1","~","S3"], ["S1","a","S3"], ["S1","~","S5"], ["S1","a","S5"],
				["S2","~","S1"], ["S2","a","S1"],
				["S4","~","S3"], ["S4","a","S3"],["S4","~","S4"], ["S4","a","S4"],
				["S5","~","S2"], ["S5","a","S2"],["S5","~","S6"], ["S5","a","S6"],
				["S6","~","S6"], ["S6","a","S6"],["S6","~","S7"], ["S6","a","S7"],
				["S7","~","S3"], ["S7","a","S3"],["S7","~","S5"], ["S7","a","S5"]
			],
		acceptStates : ["S2","S4"]
	} |}

	let testProductive () =
		let fa = new FiniteAutomaton.model (Arg.Text faProductive) in
		let fa2 = new FiniteAutomaton.model (Arg.Text faProductive2) in
			Util.println ["productive states:"]; Util.printStates fa#productive; Util.println [];
			Util.println ["productive states:"]; Util.printStates fa2#productive; Util.println []


	let faClean = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1","S2","S3","S4"],
		initialState : "S1",
		transitions : [
				["S1","a","S2"], ["S1","b","S3"],
				["S4","a","S2"], ["S4","b","S3"], ["S3","a","S3"]
			],
		acceptStates : ["S4"]
	} |}

	let faClean2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1","S2","S3","S4"],
		initialState : "S1",
		transitions : [
				["S1","a","S2"], ["S1","~","S3"],
				["S3","a","S2"], ["S3","~","S1"], ["S3","a","S4"]
			],
		acceptStates : ["S2"]
	} |}

	let testClean () =
		let fa = new FiniteAutomaton.model (Arg.Text faClean) in
		let fa2 = new FiniteAutomaton.model (Arg.Text faClean2) in
		let mfa = fa#cleanUselessStates in
		let mfa2 = fa2#cleanUselessStates in
		let j = mfa#toJSon in
		let j2 = mfa2#toJSon in
			JSon.show j; Util.println [];
			JSon.show j2; Util.println []

	let faIsDeter = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "isDeter",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","~","S2"], ["S1","a","S3"],
				["S2","a","S3"], ["S2","b","S2"]
			],
		acceptStates : ["S3"]
	} |}

	let faIsDeter2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "isDeter",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","~","S2"], ["S1","b","S3"],
				["S2","a","S4"], ["S4","b","S5"],
				["S3","b","S5"]
			],
		acceptStates : ["S5"]
	} |}

	let faIsDeter3 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "isDeter",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","a","S2"], ["S1","a","S3"],
				["S2","b","S4"],
				["S3","b","S4"]
			],
		acceptStates : ["S4"]
	} |}

	let faToDeter = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["0", "1"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","1","S2"], ["S1","1","S3"] , ["S1","0","S5"],
				["S2","~","S4"],
				["S4","0","S3"],
				["S5","1","S2"], ["S5","0","S3"], ["S5","0","S4"]
			],
		acceptStates : ["S3"]
	} |}

	let testIsDeterministic () =
		let fa = new FiniteAutomaton.model (Arg.Text faIsDeter) in
		let fa2 = new FiniteAutomaton.model (Arg.Text faIsDeter2) in
		let fa3 = new FiniteAutomaton.model (Arg.Text faIsDeter3) in
			if fa#isDeterministic then
				Util.println ["automata is deterministic"] else Util.println ["automata is non-deterministic"];
		if fa2#isDeterministic then
				Util.println ["automata is deterministic"] else Util.println ["automata is non-deterministic"];
			if fa3#isDeterministic then
				Util.println ["automata is deterministic"] else Util.println ["automata is non-deterministic"]



	let testToDeterministic () =
		let fa = new FiniteAutomaton.model (Arg.Text faToDeter) in
		let mfa = fa#toDeterministic in
		let j = mfa#toJSon in
			JSon.show j;
		let fa = new FiniteAutomaton.model (Arg.Text faIsDeter) in
		let mfa = fa#toDeterministic in
		let j = mfa#toJSon in
			JSon.show j


	let testEquivalence () =
		let fa = new FiniteAutomaton.model (Arg.Predef "fa_abc") in
		let s = fa#equivalencePartition in
			Set.iter (fun s -> Util.print ["set: "]; Util.printStates s) s


	let faMinimize = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","a","S2"], ["S1","b","S3"],
				["S2","b","S4"], ["S2","a","S3"],
				["S3","a","S2"], ["S3","b","S4"],
				["S4","b","S3"], ["S4","a","S2"],
				["S4","a","S5"]
			],
		acceptStates : ["S4"]
	} |}

	let faMinimize2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "min",
		alphabet : ["i", "c", "1", "2"],
		states : ["S01", "S02", "S03", "S04", "S05",
				"S06", "S07", "S08", "S09", "S10"],
		initialState : "S01",
		transitions : [
				["S01","i","S02"],
				["S02","1","S03"], ["S02","i","S02"],
				["S03","1","S04"], ["S03","i","S04"],
				["S04","1","S03"], ["S04","2","S05"], ["S04","i","S04"],
				["S05","i","S06"], ["S05","c","S07"],
				["S06","i","S06"], ["S06","1","S03"],
				["S07","1","S04"], ["S07","i","S08"],
				["S08","i","S08"], ["S08","1","S03"], ["S08","2","S09"],
				["S09","c","S03"], ["S09","i","S10"],
				["S10","1","S03"], ["S10","i","S10"]
			],
		acceptStates : ["S10"]
	} |}

	let faMinimize3 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b","c"],
		states : ["S0","S1", "S2", "S3", "S4", "S5"],
		initialState : "S0",
		transitions : [
				["S0","a","S1"], ["S0","b","S2"],
				["S1","b","S0"], ["S1","a","S1"], ["S1","c","S4"],
				["S2","b","S0"], ["S2","a","S2"], ["S2","c","S5"],
				["S3","b","S1"], ["S3","a","S3"], ["S3","c","S4"],
				["S4","b","S5"],
				["S5","b","S4"]
			],
		acceptStates : ["S4","S5"]
	} |}

	let faMinimize4 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["0", "1"],
		states : ["00","01", "10", "11"],
		initialState : "00",
		transitions : [
				["00","1","01"], ["00","0","10"],
				["01","1","00"], ["01","0","11"],
				["10","0","00"], ["10","1","11"],
				["11","1","10"], ["11","0","01"]
			],
		acceptStates : ["01"]
	} |}

	let testMinimize () =
		let fa = new FiniteAutomaton.model (Arg.Text faMinimize) in
		let mfa = fa#minimize in
		let j = mfa#toJSon in
			JSon.show j

	let testMinimize2 () =
		let fa = new FiniteAutomaton.model (Arg.Text faMinimize2) in
		let mfa = fa#minimize in
		let j = mfa#toJSon in
			JSon.show j

	let testMinimize3 () =
		let fa = new FiniteAutomaton.model (Arg.Text faMinimize3) in
		let mfa = fa#minimize in
		let j = mfa#toJSon in
			JSon.show j

	let testMinimize4 () =
		let fa = new FiniteAutomaton.model (Arg.Text faMinimize4) in
		let mfa = fa#minimize in
		let j = mfa#toJSon in
			JSon.show j
			
	let testExercice () =
		let e = new Exercise.exercise (Arg.Predef "exer_astar_fa") in
		let fa = new FiniteAutomaton.model (Arg.Predef "dfa_astar") in
		let (ins,outs,props) = fa#checkExerciseFailures e in
			e#show2;
			fa#show2;
			Exercise.showRes (ins,outs,props)

	let faMinimize4 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["0", "1"],
		states : ["00","01", "10", "11"],
		initialState : "00",
		transitions : [
				["00","1","01"], ["00","0","10"],
				["01","1","00"], ["01","0","11"],
				["10","0","00"], ["10","1","11"],
				["11","1","10"], ["11","0","01"]
			],
		acceptStates : ["01"]
	} |}

	let runAll =
		if Util.testing active "FiniteAutomaton" then begin
			Util.sep (); test0 ();


(*
			
			Util.sep (); testExercice ();
			Util.sep (); testBug ();
			Util.sep (); testBug2 ();
			Util.sep (); testAcceptBF ();
			Util.sep (); testAcceptBF2 ();
			Util.sep (); testAccept ();
			Util.sep (); testAccept2 ();
			Util.sep (); testAccTrace () *)
		end
end

# 1 "src/RegularExpressionTests.ml"
(*
 * RegularExpressionTests.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: Regular expressions testing.
 *)

open BasicTypes

module RegularExpressionTests: sig end =
struct
	let active = false

	let test0 () =
		let m = new RegularExpression.model (Arg.Predef "re_abc") in
			let j = m#toJSon in
				JSon.show j

	let test1 () =
		let re = new RegularExpression.model (Arg.Predef "re_abc") in
			let j = re#toJSon in
				JSon.show j

	let testAlphabet () =
		let re = new RegularExpression.model (Arg.Predef "re_abc") in
			Util.println ["alphabet: "]; Util.printAlphabet re#alphabet;
			Util.println []

	let testAlphabet2 () =
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
			Util.println ["alphabet: "]; Util.printAlphabet re#alphabet;
			Util.println []

	let testAlphabet3 () =
		let re = new RegularExpression.model (Arg.Predef "re_complex") in
			Util.println ["alphabet: "]; Util.printAlphabet re#alphabet;
			Util.println []

	let testAlphabet4 () =
		let re = new RegularExpression.model (Arg.Predef "re_convoluted") in
			Util.println ["alphabet: "]; Util.printAlphabet re#alphabet;
			Util.println []

	let testQuasiLang () =
		let re = new RegularExpression.model (Arg.Predef "re_abc") in
			let ws = re#quasiLanguage in
			Util.printWords ws

	let testQuasiLang2 () =
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
			let ws = re#quasiLanguage in
			Util.printWords ws

	let testQuasiLang3 () =
		let re = new RegularExpression.model (Arg.Predef "re_complex") in
			let ws = re#quasiLanguage in
			Util.printWords ws

	let testQuasiLang4 () =
		let re = new RegularExpression.model (Arg.Predef "re_convoluted") in
			let ws = re#quasiLanguage in
			Util.printWords ws

	let check f w =
		let msg = 
			if f w then "word was accepted" else "word was not accepted"
		in Util.println [msg]

	let testAccept () =
		let m = new RegularExpression.model (Arg.Predef "re_abc") in
			check m#accept (word "aa")

	let testAccept2 () =
		let m = new RegularExpression.model (Arg.Predef "re_simple") in
			check m#accept (word "aa")

	let testAccept3 () =
		let m = new RegularExpression.model (Arg.Predef "re_complex") in
			check m#accept (word "aa")

	let testAccept4 () =
		let m = new RegularExpression.model (Arg.Predef "re_convoluted") in
			check m#accept (word "aa")

	let testGenerate () =
		let re = new RegularExpression.model (Arg.Predef "re_abc") in
			Util.println ["generated words size 0:"]; Util.printWords (re#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (re#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (re#generate 2);
			Util.println ["generated words size 3:"]; Util.printWords (re#generate 3);
			Util.println ["generated words size 4:"]; Util.printWords (re#generate 4);
			Util.println []

	let testGenerate2 () =
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
			Util.println ["generated words size 0:"]; Util.printWords (re#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (re#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (re#generate 2);
			Util.println ["generated words size 3:"]; Util.printWords (re#generate 3);
			Util.println ["generated words size 4:"]; Util.printWords (re#generate 4);
			Util.println []

	let testGenerate3 () =
		let re = new RegularExpression.model (Arg.Predef "re_complex") in
			Util.println ["generated words size 0:"]; Util.printWords (re#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (re#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (re#generate 2);
			Util.println ["generated words size 3:"]; Util.printWords (re#generate 3);
			Util.println ["generated words size 4:"]; Util.printWords (re#generate 4);
			Util.println []

	let testGenerate4 () =
		let re = new RegularExpression.model (Arg.Predef "re_convoluted") in
			Util.println ["generated words size 0:"]; Util.printWords (re#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (re#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (re#generate 2);
			Util.println ["generated words size 3:"]; Util.printWords (re#generate 3);
			Util.println ["generated words size 4:"]; Util.printWords (re#generate 4);
			Util.println []

	let testSimplify2 () =
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
		let res = re#simplify in
			JSon.show res#toJSon

	let testEnum () =
		let e = new Exercise.exercise (Arg.Predef "exer_re2fa") in
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
		let result = re#checkExercise e in
			if result then Util.print ["it works"] else Util.print ["it does not work"]

	let testTrace () =
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
			re#allTrees (word "acbacb")
	
	let re_more = {| {
			kind : "regular expression",
			description : "this is an example",
			name : "re_more",
			re : "a*"
	} |}
				
	let testMore () =
		let re = new RegularExpression.model (Arg.Text re_more) in
			re#allTrees (word "aa")

	let runAll =
		if Util.testing active "RegularExpression" then begin
			testMore ()
		end
end
# 1 "src/ContextFreeGrammarBasicTests.ml"
(*
 * ContextFreeGrammarBasicTests.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: Context-free grammar testing.
 *)

open BasicTypes

module ContextFreeGrammarBasicTests : sig end =
struct
	open ContextFreeGrammarBasic

	let active = false
	
	let test0 () =
		let m = new model (Arg.Predef "cfg_simple") in
		let j = m#toJSon in
			JSon.show j

	let test1 () =
		let m = new model (Arg.Predef "cfg_balanced") in
		let e = new Exercise.exercise (Arg.Predef "exer_balanced_cfg") in
		let result = m#checkExercise e in
			if result then Util.println ["it works"] else Util.println ["it does not work"]

	let testRegular () =
		let m = new model (Arg.Predef "cfg_simple") in
		let ws = m#isRegular in
			if ws then Util.println ["is regular"] else Util.println ["is not regular"]


	let testAcc () =
		let m = new model (Arg.Predef "cfg_simple") in
		let ws = m#accept [] in
			if ws then Util.println ["Word was accepted"]
			else Util.println ["Word was not accepted"]


	let testTrace () =
		let m = new model (Arg.Predef "cfg_simple") in
			m#acceptWithTracing (word "01")

	let testGen () =
		let m = new model (Arg.Predef "cfg_simple") in
		let ws = m#generate 4 in
			Util.printWords ws

	let showM m =
		let j = m#toJSon in
			JSon.show j
	
	let showB b =
		if b then print_string "YES\n"
		else print_string "NO\n"	
	
	let testChomsky () =
		let m = new model (Arg.Predef "cfg_balanced") in
			showB (m#accept (word ""));			
			showB (m#accept (word "[[[]]]"));			
			showB (m#accept (word "[[][][]][]"));		
			showB (m#accept (word "[[][]]][]"))			

	let testExercice () =
		let e = new Exercise.exercise (Arg.Predef "exer_balanced_cfg") in
		let g = new model (Arg.Predef "cfg_balanced") in
		let b = g#checkExercise e in
			e#show2;
			g#show2;
			showB b

	let zzz = {| {
			kind : "context free grammar",
			description : "this is an example",
			name : "qq_simple",
			alphabet : ["0", "2"],
			variables : ["S", "P"],
			initial : "S",
			rules : [	"S -> 2S0 | P",
						"2P0 -> 0P2 | ~",
						" -> A",
						" ~ -> B" ]
		} |}
		
	let testBadHeads () =
		let g = make (Arg.Text zzz) in
			show g

	let runAll =
		if Util.testing active "ContextFreeGrammarBasic" then begin
			Util.sep (); test0 ();
			Util.sep (); test1 ();
			Util.sep (); testRegular ();
			Util.sep (); testAcc ();
			Util.sep (); testTrace ();
			Util.sep (); testGen ();
			Util.sep (); testExercice();
			Util.sep (); testBadHeads()
		end
end


# 3 "src/ContextFreeGrammarLL1Tests.ml"
open BasicTypes
open ContextFreeGrammarBasic  

module ContextFreeGrammarLL1Tests : sig end =
struct
	let active = false

  let example1 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 1",
	  name : "G1",
	  alphabet : ["a", "b", "c", "d", "e"],
	  variables : ["S", "A", "B", "C", "D", "E"],
	  initial : "S",
    rules : ["S -> ABCDE", "A -> a | ", "B -> b | ", "C -> c", "D -> d | ", "E -> e | "]
  } |}

  let example2 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 2",
	  name : "G2",
	  alphabet : ["a", "b", "c", "d"],
	  variables : ["S", "B", "C"],
	  initial : "S",
    rules : ["S -> Bb | Cd", "B -> aB | ", "C -> cC | "]
  } |}
  
  let example3 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 3",
	  name : "G3",
	  alphabet : ["+", "*", "(", ")", "i"],
	  variables : ["E", "D", "T", "U", "F"],
	  initial : "E",
    rules : ["E -> TD", "D -> +TD | ", "T -> FU", "U -> *FU | ", "F -> i | (E)"]
  } |}
  
  let example4 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 4",
	  name : "G4",
	  alphabet : ["a", "b", "c", "f", "g", "h"],
	  variables : ["S", "B", "C", "D", "E", "F"],
	  initial : "S",
    rules : ["S -> aBDh", "B -> cC", "C -> bC | ", "D -> EF", "E -> g | ", "F -> f | "]
  } |}

  let example5 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 5",
	  name : "G5",
	  alphabet : ["n", "+", "*"],
	  variables : ["E", "A", "B"],
	  initial : "E",
    rules : ["E -> nA", "A -> EB | ", "B -> +A | *A"]
  } |}
  
  let example6 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 6",
	  name : "G6",
	  alphabet : ["a", "b"],
	  variables : ["N", "A", "B", "C"],
	  initial : "N",
    rules : ["N -> AB | BA", "A -> a | CAC", "B -> b | CBC", "C -> a | b"]
  } |}
  
  let cfg_dissertation = {| {
	  kind : "context free grammar", 
	  description : "dissertation example",
	  name : "G2",
	  alphabet : ["a", "b", "c"],
	  variables : ["S", "A", "B", "C", "D", "E"],
	  initial : "S",
    rules : ["S -> ABC", "A -> aD", "B -> CE", "C -> c", "D -> AB | ", "E -> bE | "]
  } |}

  let non_deterministic_grammar = {| {
	  kind : "context free grammar", 
	  description : "Non deterministic grammar",
	  name : "N",
	  alphabet : ["a", "b", "d", "g", "h"],
	  variables : ["S", "A", "B", "C"],
	  initial : "S",
    rules : ["S -> ACB | CbB | Ba", "A -> da | BC", "B -> g | ", "C -> h | "]
  } |}

  let accessible_symbols1 = {| {
	  kind : "context free grammar", 
	  description : "Accessible symbols example",
	  name : "AS1",
	  alphabet : ["a", "b"],
	  variables : ["A", "B", "C", "D", "E"],
	  initial : "A",
    rules : ["A -> aBb | bBa", "B -> Cb | bC", "C -> a | aC", "D -> E | Db", "E -> aE | Da"]
  } |}
  
  let accessible_symbols2 = {| {
	  kind : "context free grammar", 
	  description : "Accessible symbols example",
	  name : "AS2",
	  alphabet : ["a", "b"],
	  variables : ["S", "B"],
	  initial : "S",
    rules : ["S -> a", "B -> b"]
  } |}
  
  let productive_symbols1 = {| {
	  kind : "context free grammar", 
	  description : "Productive symbols example",
	  name : "PS1",
	  alphabet : ["a", "b"],
	  variables : ["A", "B", "C", "D", "E"],
	  initial : "A",
    rules : ["A -> aBb | bBa", "B -> CD | aC | Ab", "C -> a | aC", "D -> E | DA", "E -> aE | Da"]
  } |}

  let productive_symbols2 = {| {
	  kind : "context free grammar", 
	  description : "Productive symbols example",
	  name : "PS2",
	  alphabet : ["a", "b"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> a | A", "A -> AB", "B -> b"]
  } |}
  
  let clean_grammar1 = {| {
	  kind : "context free grammar", 
	  description : "Clean example from https://www.cs.scranton.edu/~mccloske/courses/cmps260/cfg_remove_useless.html",
	  name : "Clean1",
	  alphabet : ["a", "b", "c", "d"],
	  variables : ["S", "A", "B", "C", "D"],
	  initial : "S",
    rules : ["S -> aSa | bB | bAA", "A -> a | SbA | aB", "B -> AB | CaB", "C -> cC | Sa | bD", "D -> dD | "]
  } |}

  let direct_left_recursion_grammar1 = {| {
	  kind : "context free grammar", 
	  description : "Direct Left-recursion example 1",
	  name : "DR1",
	  alphabet : ["a", "b"],
	  variables : ["A"],
	  initial : "A",
    rules : ["A -> Aa | b"]
  }  |}
  
  let direct_left_recursion_grammar2 = {| {
	  kind : "context free grammar", 
	  description : "Direct Left-recursion example 2",
	  name : "DR2",
	  alphabet : ["a", "b"],
	  variables : ["B"],
	  initial : "B",
    rules : ["B -> a | Bb"]
  } |}
  
  let indirect_left_recursion_grammar1 = {| {
	  kind : "context free grammar", 
	  description : "Indirect Left-recursion example 1",
	  name : "IR1",
	  alphabet : ["a"],
	  variables : ["S", "A"],
	  initial : "S",
    rules : ["S -> A | a", "A -> S"]
  }  |}

  let indirect_left_recursion_grammar2 = {| {
	  kind : "context free grammar", 
	  description : "Indirect Left-recursion example 2",
	  name : "IR2",
	  alphabet : ["a"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> A | B", "A -> a", "B -> S"]
  }  |}
  
  let indirect_left_recursion_grammar3 = {| {
	  kind : "context free grammar", 
	  description : "Indirect Left-recursion example 2",
	  name : "IR3",
	  alphabet : ["a", "b", "c"],
	  variables : ["S", "A", "B", "C"],
	  initial : "S",
    rules : ["S -> ABCS", "A -> a | ", "B -> b | ", "C -> c | "]
  }  |} 
  
  let indirect_left_recursion_grammar4 = {| {
	  kind : "context free grammar", 
	  description : "Indirect Left-recursion example",
	  name : "IR4",
	  alphabet : ["a", "b", "d", "e", "f", "g"],
	  variables : ["A", "B", "C", "D"],
	  initial : "A",
    rules : ["A -> Ba | b", "B -> Cd | e", "C-> Df | g", "D -> Df | Aa | Cg"]
  }  |}

  let indirect_left_recursion_grammar5 = {| {
	  kind : "context free grammar", 
	  description : "Indirect Left-recursion example 2",
	  name : "IR3",
	  alphabet : ["a"],
	  variables : ["S", "A"],
	  initial : "S",
    rules : ["S -> AS", "A -> a | "]
  }  |}

  let left_factoring_example = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF1",
	  alphabet : ["a", "b", "e", "i", "t"],
	  variables : ["S", "E"],
	  initial : "S",
    rules : ["S -> iEtS | iEtSeS | a", "E -> b"]
  } |}

  let left_factoring_example2 = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF2",
	  alphabet : ["a", "c"],
	  variables : ["A", "B"],
	  initial : "A",
    rules : ["A -> aAB | aBc | aAc", "B ->"]
  } |}

  let left_factoring_example3 = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF3",
	  alphabet : ["a", "b"],
	  variables : ["S"],
	  initial : "S",
    rules : ["S -> bSSaaS | bSSaSb | bSb | a"]
  } |}

  let left_factoring_example4 = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF4",
	  alphabet : ["a", "b"],
	  variables : ["S"],
	  initial : "S",
    rules : ["S -> aSSbS | aSaSb | abb | b"]
  } |}
  
  let left_factoring_example5 = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF5",
	  alphabet : ["a", "b", "c", "d"],
	  variables : ["S"],
	  initial : "S",
    rules : ["S -> a | ab | abc | abcd"]
  } |}
  
  let left_factoring_example6 = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF6",
	  alphabet : ["a", "b", "c", "d"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> aAd | aB", "A -> a | ab", "B -> ccd | ddc"]
  } |}
  
  let unit_removal_example1 = {| {
	  kind : "context free grammar", 
	  description : "unit removal example",
	  name : "UR1",
	  alphabet : ["a", "b"],
	  variables : ["E", "T", "F", "I"],
	  initial : "E",
    rules : ["E -> T", "T -> F", "F -> I", "I -> a | b | Ia | Ib"]
  } |}

  let unit_removal_example2 = {| {
	  kind : "context free grammar", 
	  description : "unit removal example 2",
	  name : "UR2",
	  alphabet : ["a", "b", "c"],
	  variables : ["A", "B", "C"],
	  initial : "A",
    rules : ["A -> B | a", "B -> C | b", "C -> A | c"]
  } |}
  
  let unit_removal_example3 = {| {
	  kind : "context free grammar", 
	  description : "unit removal example 3",
	  name : "UR3",
	  alphabet : ["a", "b", "c"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> Aa | B | c", "A -> a | bc | B", "B -> A | bb"]
  } |}
  
  let unit_removal_example4 = {| {
	  kind : "context free grammar", 
	  description : "unit removal example 4",
	  name : "UR4",
	  alphabet : ["a", "b", "d"],
	  variables : ["S", "A", "B", "C", "D", "E"],
	  initial : "S",
    rules : ["S -> AC", "A -> a", "B -> D", "C -> B | d", "D -> E", "E -> b"]
  } |}
  
  let unit_removal_example5 = {| {
	  kind : "context free grammar", 
	  description : "unit removal example 5",
	  name : "UR5",
	  alphabet : ["a", "b", "0", "1", "(", ")", "+", "*"],
	  variables : ["I", "F", "T", "E"],
	  initial : "E",
    rules : ["E -> T | E+T", "T -> F | T*F", "F -> I | (E)", "I -> a | b | Ia | Ib | I0 | I1"]
  } |}

  let epsilon_removal_example1 = {| {
	  kind : "context free grammar", 
	  description : "epsilon removal example",
	  name : "ER1",
	  alphabet : ["a", "b", "d"],
	  variables : ["S", "A", "B", "C", "D"],
	  initial : "S",
    rules : ["S -> ABaC", "A -> BC", "B -> b | ", "C -> D | ", "D -> d"]
  } |}
  
  let epsilon_removal_example2 = {| {
	  kind : "context free grammar", 
	  description : "epsilon removal example 2",
	  name : "ER2",
	  alphabet : ["a", "b"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> AB", "A -> AaA | ", "B -> BbB | "]
  } |}
  
  let epsilon_removal_example3 = {| {
	  kind : "context free grammar", 
	  description : "epsilon removal example 3",
	  name : "ER3",
	  alphabet : ["a", "b"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> AB", "A -> aAA | ", "B -> bBB | "]
  } |}

  let firstPairConversion_old l = Set.make (List.map (fun (a,b) -> (a, Set.make b)) l)
  let followPairConversion_old l = Set.make (List.map (fun (a,b) -> (a, Set.make b)) l)
  let lookaheadPairConversion_old l = Set.make (List.map (fun (a,b) -> ContextFreeGrammarBasic.parseLine a, Set.make b) l)

  let firstPairConversion l = Set.make (List.map (fun (a,b) -> (symb a, Set.make (List.map char2symb b))) l)
  let followPairConversion l = Set.make (List.map (fun (a,b) -> (char2symb a, Set.make (List.map char2symb b))) l)
  let lookaheadPairConversion l = Set.make (List.map (fun (a,b) -> (Set.nth (ContextFreeGrammarBasic.parseLine a) 0), Set.make (List.map char2symb b)) l)

  let printRepresentation (rep: t) =
    Printf.printf "Alphabet = "; Util.printAlphabet rep.alphabet;
    Printf.printf "Variables = "; Util.printAlphabet rep.variables;
    Printf.printf "Initial = %s\n" (symb2str rep.initial);
    Printf.printf "Rules {\n"; Set.iter (fun {head=h; body=b} -> Printf.printf "\t%s -> %s\n" (symb2str h) (word2str b)) rep.rules;
    Printf.printf "}\n\n"

  let rec testFunction2 f l c =
    if l = Set.empty then ()
    else let ((t,r),xs) = Set.cut l in
      if (f t = r) then () else Printf.printf "\t\tTest %i fails!\n" c;
      testFunction2 f xs (c+1)


	let colorRed = "\027[31m"
	let colorGreen = "\027[32m"
	let colorOff = "\027[0m"

(*	let colorRed = ""*)
(*	let colorGreen = ""*)
(*	let colorOff = ""*)

  let failPrint str =
    Printf.printf "%s" (colorRed ^ str ^ colorOff)
    
  let okPrint str =
    Printf.printf "%s" (colorGreen ^ str ^ colorOff)

  let printResult r =
    if r
    then okPrint "O"
    else failPrint "X"
  
  let printFirstTest t =
    Set.iter (fun (v,s) -> 
      Printf.printf "(%s, [" v;
      Set.iter (fun v -> Printf.printf "%c " v) s;
      Printf.printf "%s" "]) "
    ) t
    
  let compareTheseSets s1 s2 =
    Set.for_all (fun (h1,r1) ->
      Set.exists (fun (h2,r2) -> h1 = h2 && Set.equals r1 r2) s2
    ) s1 && Set.size s1 = Set.size s2

  let testFirst g r =
    let allResults = Set.map (fun v -> (v, g#first [v])) (g#representation : t).variables in
(*    Printf.printf "\n\tComparing:";*)
(*    Set.iter (fun (v,b) -> Printf.printf "\n\t\t%s->\t" (symb2str v); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) b) r;*)
(*    Printf.printf "\n\twith:";*)
(*    Set.iter (fun (v,b) -> Printf.printf "\n\t\t%s->\t" (symb2str v); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) b) allResults;*)
(*    Printf.printf "\n";*)
(*    r = allResults*)
    compareTheseSets r allResults

  let testFollow g r =
    let allResults = Set.map (fun v -> (v, g#follow v)) (g#representation : t).variables in
(*    Printf.printf "\n\tComparing:";*)
(*    Set.iter (fun (v,b) -> Printf.printf "\n\t\t%s->\t" (symb2str v); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) b) r;*)
(*    Printf.printf "\n\twith:";*)
(*    Set.iter (fun (v,b) -> Printf.printf "\n\t\t%s->\t" (symb2str v); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) b) allResults;*)
(*    Printf.printf "\n";*)
(*    r = allResults*)
    compareTheseSets r allResults
    
  let testLookahead g r =
    let rep = (g#representation : t) in
    let allResults = 
      Set.flatMap (fun v -> 
        let rules = Set.filter (fun {head=h; _} -> h = v ) rep.rules in
        Set.map (fun r -> 
          (r, g#lookahead r)
        ) rules
      ) rep.variables 
    in
(*    Printf.printf "\n\tComparing:";*)
(*    Set.iter (fun ({head=h;body=b},r) -> Printf.printf "\n\t\t%s->%s\t" (symb2str h) (word2str b); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) r) r;*)
(*    Printf.printf "\n\twith:";*)
(*    Set.iter (fun ({head=h;body=b},r) -> Printf.printf "\n\t\t%s->%s\t" (symb2str h) (word2str b); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) r) allResults;*)
(*    Printf.printf "\n";*)
(*    r = allResults*)
    compareTheseSets r allResults

  let testFunction1 f r =
    f = r



(*	let test0 () =*)
(*		let m = new ContextFreeGrammarLL1.model (Arg.Text cfg_simple) in*)
(*		let j = m#toJSon in*)
(*			JSon.show j*)

	let dollar = '$'
	let epsilon = '~'

  let testExample1 () =
    Printf.printf "Example1 test: [";
    let first = [ ("S", ['a'; 'b'; 'c']); ("A", ['a'; '~']); ("B", ['b'; '~']); ("C", ['c']); ("D", ['d'; '~']); ("E", ['e'; '~']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', ['$']); ('A', ['b'; 'c']); ('B', ['c']); ('C', ['d'; 'e'; '$']); ('D', ['e'; '$']); ('E', ['$']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->ABCDE", ['a'; 'b'; 'c']); 
                      ("A->a", ['a']); ("A->", ['b'; 'c']);
                      ("B->b", ['b']); ("B->", ['c']); 
                      ("C->c", ['c']); 
                      ("D->d", ['d']); ("D->", ['e'; dollar]); 
                      ("E->e", ['e']); ("E->", [dollar]) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
	  printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testExample2 () =
    Printf.printf "Example2 test: [";
    let first = [ ("S", ['a'; 'b'; 'c'; 'd']); ("B", ['a'; epsilon]); ("C", ['c'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('B', ['b']); ('C', ['d']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->Bb", ['a'; 'b']); ("S->Cd", ['c'; 'd']);
                      ("B->aB", ['a']); ("B->", ['b']);
                      ("C->cC", ['c']); ("C->", ['d']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testExample3 () =
    Printf.printf "Example3 test: [";
    let first = [ ("U", ['*'; epsilon]); ("D", ['+'; epsilon]); ("E", ['('; 'i']); ("F", ['('; 'i']); ("T", ['('; 'i']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('U', [')'; '+'; dollar]); ('D', [')'; dollar]); ('E', [')'; dollar]); ('F', [')'; '*'; '+'; dollar]); ('T', [')'; '+'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("U->*FU", ['*']); ("U->", [')'; '+'; dollar]); 
                      ("D->+TD", ['+']); ("D->", [')'; dollar]); 
                      ("E->TD", ['('; 'i']); 
                      ("F->i", ['i']); ("F->(E)", ['(']);
                      ("T->FU", ['('; 'i']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example3) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testExample4 () =
    Printf.printf "Example4 test: [";
    let first = [ ("S", ['a']); ("B", ['c']); ("C", ['b'; epsilon]); ("D", ['f'; 'g'; epsilon]); ("E", ['g'; epsilon]); ("F", ['f'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('B', ['f'; 'g'; 'h']); ('C', ['f'; 'g'; 'h']); ('D', ['h']); ('E', ['f'; 'h']); ('F', ['h']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->aBDh", ['a']);
                      ("B->cC", ['c']);
                      ("C->bC", ['b']); ("C->", ['f'; 'g'; 'h']); 
                      ("D->EF", ['f'; 'g'; 'h']);
                      ("E->g", ['g']); ("E->", ['f'; 'h']);
                      ("F->f", ['f']); ("F->", ['h']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example4) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testExample5 () =
    Printf.printf "Example5 test: [";
    let first = [ ("E", ['n']); ("A", ['n'; epsilon]); ("B", ['*'; '+']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('E', ['*'; '+'; dollar]); ('A', ['*'; '+'; dollar]); ('B', ['*'; '+'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("E->nA", ['n']);
                      ("A->EB", ['n']); ("A->", ['*'; '+'; dollar]);
                      ("B->+A", ['+']); ("B->*A", ['*']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example5) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testExample6 () =
    Printf.printf "Example6 test: [";
    let first = [ ("N", ['a'; 'b']); ("A", ['a'; 'b']); ("B", ['a'; 'b']); ("C", ['a'; 'b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('N', [dollar]); ('A', ['a'; 'b'; dollar]); ('B', ['a'; 'b'; dollar]); ('C', ['a'; 'b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("N->AB", ['a'; 'b']); ("N->BA", ['a'; 'b']);
                      ("A->a", ['a']); ("A->CAC", ['a'; 'b']);
                      ("B->b", ['b']); ("B->CBC", ['a'; 'b']); 
                      ("C->a", ['a']); ("C->b", ['b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example6) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"

  let testDissertation () =
    Printf.printf "%s" (Printf.sprintf "Dissertation test: [");
    let first = [ ("S", ['a']); ("A", ['a']); ("B", ['c']); ("C", ['c']); ("D", ['a'; epsilon]); ("E", ['b'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['c']); ('B', ['c']); ('C', ['b'; 'c'; dollar]); ('D', ['c']); ('E', ['c']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->ABC", ['a']); 
                      ("A->aD", ['a']); 
                      ("B->CE", ['c']);
                      ("C->c", ['c']); 
                      ("D->AB", ['a']); ("D->", ['c']);
                      ("E->bE", ['b']); ("E->", ['c']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text cfg_dissertation) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testNFGrammar () =
    Printf.printf "Non deterministic grammar test: [";
    let first = [ ("S", ['a'; 'b'; 'd'; 'g'; 'h'; epsilon]); ("A", ['d'; 'g'; 'h'; epsilon]); ("B", ['g'; epsilon]); ("C", ['h'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['g'; 'h'; dollar]); ('B', ['a'; 'g'; 'h'; dollar]); ('C', ['b'; 'g'; 'h'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->ACB", ['d'; 'g'; 'h'; dollar]); ("S->CbB", ['b'; 'h']); ("S->Ba", ['a'; 'g']);
                      ("A->da", ['d']); ("A->BC", ['g'; 'h'; dollar]); 
                      ("B->g", ['g']); ("B->", ['a'; 'g'; 'h'; dollar]); 
                      ("C->h", ['h']); ("C->", ['b'; 'g'; 'h'; dollar]); ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text non_deterministic_grammar) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"

  let testAccessible1 () =
    Printf.printf "%s" (Printf.sprintf "Remove inaccessible symbols test 1: [");
    let first = [ ("A", ['a'; 'b']); ("B", ['a'; 'b']); ("C", ['a']); ("D", ['a']); ("E", ['a']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', [dollar]); ('B', ['a'; 'b']); ('C', ['a'; 'b']); ('D', ['a'; 'b']); ('E', ['a'; 'b']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("A->aBb", ['a']); ("A->bBa", ['b']); 
                      ("B->Cb", ['a']); ("B->bC", ['b']);
                      ("C->a", ['a']); ("C->aC", ['a']); 
                      ("D->E", ['a']); ("D->Db", ['a']);
                      ("E->aE", ['a']); ("E->Da", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text accessible_symbols1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 m#isFullyAccessible false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#accessibleRewrite#representation) in
(*      printRepresentation m#representation;*)
(*      printRepresentation transformed#representation;*)
      printResult (testFunction1 transformed#isFullyAccessible true);
    Printf.printf "]\n"
    
  let testAccessible2 () =
    Printf.printf "%s" (Printf.sprintf "Remove inaccessible symbols test 2: [");
    let first = [ ("S", ['a']); ("B", ['b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('B', []) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->a", ['a']); 
                      ("B->b", ['b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text accessible_symbols2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive false);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isFullyAccessible false);
      printResult (testFunction1 m#isFullyProductive true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#accessibleRewrite#representation) in
      printResult (testFunction1 transformed#isFullyAccessible true);
      printResult (testFunction1 transformed#isFullyProductive true);
    Printf.printf "]\n"

  let testProductive1 () =
    Printf.printf "%s" (Printf.sprintf "Remove unproductive symbols test 1: [");
    let first = [ ("A", ['a'; 'b']); ("B", ['a'; 'b']); ("C", ['a']); ("D", ['a']); ("E", ['a']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', ['a'; 'b'; dollar]); ('B', ['a'; 'b']); ('C', ['a'; 'b']); ('D', ['a'; 'b']); ('E', ['a'; 'b']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("A->aBb", ['a']); ("A->bBa", ['b']); 
                      ("B->CD", ['a']); ("B->aC", ['a']); ("B->Ab", ['a'; 'b']);
                      ("C->a", ['a']); ("C->aC", ['a']); 
                      ("D->E", ['a']); ("D->DA", ['a']);
                      ("E->aE", ['a']); ("E->Da", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text productive_symbols1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring true);
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 m#isFullyProductive false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#productiveRewrite#representation) in
      printResult (testFunction1 transformed#isFullyProductive true);
    Printf.printf "]\n"

  let testProductive2 () =
    Printf.printf "%s" (Printf.sprintf "Remove unproductive symbols test 2: [");
    let first = [ ("S", ['a']); ("A", []); ("B", ['b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['b'; dollar]); ('B', ['b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->a", ['a']); ("S->A", []); 
                      ("A->AB", []);
                      ("B->b", ['b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text productive_symbols2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isFullyAccessible true);
      printResult (testFunction1 m#isFullyProductive false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#productiveRewrite#representation) in
      printResult (testFunction1 transformed#isFullyAccessible false);
      printResult (testFunction1 transformed#isFullyProductive true);
    let fullyTransformed =  new ContextFreeGrammarLL1.model (Arg.Representation (List.nth m#clean 1).grammar#representation) in
      printResult (testFunction1 fullyTransformed#isFullyAccessible true);
      printResult (testFunction1 fullyTransformed#isFullyProductive true);
    Printf.printf "]\n"

  let cleanGrammar1 () = 
    Printf.printf "%s" (Printf.sprintf "Clean grammar test 1: [");
    let first = [ ("S", ['a'; 'b']); ("A", ['a'; 'b']); ("B", ['a'; 'b'; 'c']); ("C", ['a'; 'b'; 'c']); ("D", ['d'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', ['a'; 'b'; dollar]); ('A', ['a'; 'b'; 'c'; dollar]); ('B', ['a'; 'b'; 'c'; dollar]); ('C', ['a']); ('D', ['a']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->aSa", ['a']); ("S->bB", ['b']); ("S->bAA", ['b']);
                      ("A->a", ['a']); ("A->SbA", ['a'; 'b']); ("A->aB", ['a']);
                      ("B->AB", ['a'; 'b']); ("B->CaB", ['a'; 'b'; 'c']);
                      ("C->cC", ['c']); ("C->Sa", ['a'; 'b']); ("C->bD", ['b']);
                      ("D->dD", ['d']); ("D->", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text clean_grammar1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive false);
      printResult (testFunction1 m#isLeftFactoring true);
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 m#isFullyAccessible true);
      printResult (testFunction1 m#isFullyProductive false);
    let fullyTransformed =  new ContextFreeGrammarLL1.model (Arg.Representation (List.nth m#clean 1).grammar#representation) in
      printResult (testFunction1 fullyTransformed#isFullyAccessible true);
      printResult (testFunction1 fullyTransformed#isFullyProductive true);
    Printf.printf "]\n"
    
  let testDirectRecursion1 () =
    Printf.printf "Direct recursion test 1: [";
    let first = [ ("A", ['b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', ['a'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("A->Aa", ['b']); ("A->b", ['b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text direct_left_recursion_grammar1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeLeftRecursion.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
    Printf.printf "]\n"

  let testDirectRecursion2 () =
    Printf.printf "Direct recursion test 2: [";
    let first = [ ("B", ['a']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('B', ['b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("B->a", ['a']); ("B->Bb", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text direct_left_recursion_grammar2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeLeftRecursion.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
    Printf.printf "]\n"

  let testIndirectRecursion1 () =
    Printf.printf "Indirect recursion test 1: [";
    let first = [ ("A", ['a']); ("S", ['a']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', [dollar]); ('S', [dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->A", ['a']); ("S->a", ['a']); ("A->S", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text indirect_left_recursion_grammar1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are unit productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
      printResult (testFunction1 transformed#isClean false);
    (*Grammar can be cleaned yet.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation (List.nth transformed#clean 1).grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
      printResult (testFunction1 transformed#isClean true);
    Printf.printf "]\n"
    
  let testIndirectRecursion2 () = (*FIXME Trying to clean grammar right away fails*)
    Printf.printf "Indirect recursion test 2: [";
    let first = [ ("S", ['a']); ("A", ['a']); ("B", ['a']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', [dollar]); ('B', [dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->A", ['a']); ("S->B", ['a']);
                      ("A->a", ['a']);
                      ("B->S", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text indirect_left_recursion_grammar2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are epsilon productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive true);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are unit productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation transformed#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
    (*Grammar can be cleaned yet.*)
      printResult (testFunction1 transformed#isClean false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation (List.nth transformed#clean 1).grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
      printResult (testFunction1 transformed#isClean true);
    Printf.printf "]\n"

  let testIndirectRecursion3 () =
    Printf.printf "Indirect recursion test 3: [";
    let first = [ ("S", ['a'; 'b'; 'c']); ("A", ['a'; epsilon]); ("B", ['b'; epsilon]); ("C", ['c'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a'; 'b'; 'c']); ('B', ['a'; 'b'; 'c']); ('C', ['a'; 'b'; 'c']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->ABCS", ['a'; 'b'; 'c']);
                      ("A->a", ['a']); ("A->", ['a'; 'b'; 'c']); 
                      ("B->b", ['b']); ("B->", ['a'; 'b'; 'c']); 
                      ("C->c", ['c']); ("C->", ['a'; 'b'; 'c']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text indirect_left_recursion_grammar3) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are epsilon productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive true);
      printResult (testFunction1 transformed#isLeftFactoring true);
      printResult (testFunction1 transformed#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are unit productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation transformed#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring true);
      printResult (testFunction1 transformed#isLL1 false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation transformed#leftFactoring.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 false); (*This grammar is not LL(1)*)
    Printf.printf "]\n"
    
  let testIndirectRecursion4 () =
    Printf.printf "Indirect recursion test 4: [";
    let first = [ ("A", ['b'; 'e'; 'g']); ("B", ['b'; 'e'; 'g']); ("C", ['b'; 'e'; 'g']); ("D", ['b'; 'e'; 'g']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', ['a'; dollar]); ('B', ['a']); ('C', ['d'; 'g']); ('D', ['f']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("A->Ba", ['b'; 'e'; 'g']); ("A->b", ['b']);
                      ("B->Cd", ['b'; 'e'; 'g']); ("B->e", ['e']);
                      ("C->Df", ['b'; 'e'; 'g']); ("C->g", ['g']);
                      ("D->Df", ['b'; 'e'; 'g']); ("D->Aa", ['b'; 'e'; 'g']); ("D->Cg", ['b'; 'e'; 'g']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text indirect_left_recursion_grammar4) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeLeftRecursion.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring true);
      printResult (testFunction1 transformed#isLL1 false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation transformed#leftFactoring.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 false);
    Printf.printf "]\n"

  let testIndirectRecursion5 () =
    Printf.printf "Indirect recursion test 5: [";
    let first = [ ("S", ['a']); ("A", ['a'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->AS", ['a']);
                      ("A->a", ['a']); ("A->", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text indirect_left_recursion_grammar5) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are epsilon productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive true);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are unit productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation transformed#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
    Printf.printf "]\n"

  let testLeftFactoring1 () =
    Printf.printf "Left factoring test 1: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 false);
    Printf.printf "]\n"
    
  let testLeftFactoring2 () =
    Printf.printf "Left factoring test 2: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example2) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 false);
    Printf.printf "]\n"
    
  let testLeftFactoring3 () =
    Printf.printf "Left factoring test 3: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example3) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 false);
    Printf.printf "]\n"
    
  let testLeftFactoring4 () =
    Printf.printf "Left factoring test 4: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example4) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 false);
    Printf.printf "]\n"
    
  let testLeftFactoring5 () =
    Printf.printf "Left factoring test 5: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example5) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 true);
    Printf.printf "]\n"
    
  let testLeftFactoring6 () =
    Printf.printf "Left factoring test 6: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example6) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 true);
    Printf.printf "]\n"

  let testUnitRemoval1 () =
    Printf.printf "Unit production removal test 1: [";
    let first = [ ("E", ['a'; 'b']); ("T", ['a'; 'b']); ("F", ['a'; 'b']); ("I", ['a'; 'b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('E', [dollar]); ('T', [dollar]); ('F', [dollar]); ('I', ['a'; 'b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("E->T", ['a'; 'b']);
                      ("T->F", ['a'; 'b']); 
                      ("F->I", ['a'; 'b']);
                      ("I->a", ['a']); ("I->b", ['b']); ("I->Ia", ['a'; 'b']); ("I->Ib", ['a'; 'b'])] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text unit_removal_example1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasUnitProductions true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasUnitProductions false);
    Printf.printf "]\n"

  let testUnitRemoval2 () =
    Printf.printf "Unit production removal test 2: [";
    let first = [ ("A", ['a'; 'b'; 'c']); ("B", ['a'; 'b'; 'c']); ("C", ['a'; 'b'; 'c']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', [dollar]); ('B', [dollar]); ('C', [dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("A->B", ['a'; 'b'; 'c']); ("A->a", ['a']);
                      ("B->C", ['a'; 'b'; 'c']); ("B->b", ['b']);
                      ("C->A", ['a'; 'b'; 'c']); ("C->c", ['c'])] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text unit_removal_example2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasUnitProductions true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasUnitProductions false);
    Printf.printf "]\n"

  let testUnitRemoval3 () =
    Printf.printf "Unit production removal test 3: [";
    let first = [ ("S", ['a'; 'b'; 'c']); ("A", ['a'; 'b']); ("B", ['a'; 'b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a'; dollar]); ('B', ['a'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->Aa", ['a'; 'b']); ("S->B", ['a'; 'b']); ("S->c", ['c']);
                      ("A->a", ['a']); ("A->bc", ['b']); ("A->B", ['a'; 'b']); 
                      ("B->A", ['a'; 'b';]); ("B->bb", ['b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text unit_removal_example3) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasUnitProductions true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasUnitProductions false);
    Printf.printf "]\n"

  let testUnitRemoval4 () =
    Printf.printf "Unit production removal test 4: [";
    let first = [ ("S", ['a']); ("A", ['a']); ("B", ['b']); ("C", ['b'; 'd']); ("D", ['b']); ("E", ['b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['b'; 'd']); ('B', [dollar]); ('C', [dollar]); ('D', [dollar]); ('E', [dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->AC", ['a']);
                      ("A->a", ['a']); 
                      ("B->D", ['b']);
                      ("C->B", ['b']); ("C->d", ['d']);
                      ("D->E", ['b']);
                      ("E->b", ['b'])] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text unit_removal_example4) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasUnitProductions true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasUnitProductions false);
    Printf.printf "]\n"
    
  let testUnitRemoval5 () =
    Printf.printf "Unit production removal test 5: [";
    let first = [ ("E", ['a'; 'b'; '(']); ("T", ['a'; 'b'; '(']); ("F", ['a'; 'b'; '(']); ("I", ['a'; 'b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('E', [')'; '+'; dollar]); ('T', [')'; '*'; '+'; dollar]); ('F', [')'; '*'; '+'; dollar]); ('I', ['0'; 'a'; '1'; 'b'; ')'; '*'; '+'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("E->T", ['a'; 'b'; '(']); ("E->E+T", ['a'; 'b'; '(']);
                      ("T->F", ['a'; 'b'; '(']); ("T->T*F", ['a'; 'b'; '(']); 
                      ("F->I", ['a'; 'b']); ("F->(E)", ['(']);
                      ("I->a", ['a']); ("I->b", ['b']); ("I->Ia", ['a'; 'b']); ("I->Ib", ['a'; 'b']); ("I->I0", ['a'; 'b']); ("I->I1", ['a'; 'b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text unit_removal_example5) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasUnitProductions true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasUnitProductions false);
    Printf.printf "]\n"

  let testEmptyRemoval1 () =
    Printf.printf "Empty production removal test 1: [";
    let first = [ ("S", ['a'; 'b'; 'd']); ("A", ['b'; 'd'; epsilon]); ("B", ['b'; epsilon]); ("C", ['d'; epsilon]); ("D", ['d']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a'; 'b']); ('B', ['a'; 'b'; 'd']); ('C', ['a'; 'b'; dollar]); ('D', ['a'; 'b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->ABaC", ['a'; 'b'; 'd']);
                      ("A->BC", ['a'; 'b'; 'd']); 
                      ("B->b", ['b']); ("B->", ['a'; 'b'; 'd']);
                      ("C->D", ['d']); ("C->", ['a'; 'b'; dollar]); 
                      ("D->d", ['d']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text epsilon_removal_example1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasEmptyProductions true); 
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasEmptyProductions false); 
    Printf.printf "]\n"
    
  let testEmptyRemoval2 () =
    Printf.printf "Empty production removal test 2: [";
    let first = [ ("S", ['a'; 'b'; epsilon]); ("A", ['a'; epsilon]); ("B", ['b'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a'; 'b'; dollar]); ('B', ['b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->AB", ['a'; 'b'; dollar]);
                      ("A->AaA", ['a']); ("A->", ['a'; 'b'; dollar]); 
                      ("B->BbB", ['b']); ("B->", ['b'; dollar]) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text epsilon_removal_example2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasEmptyProductions true); 
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasEmptyProductions false); 
    Printf.printf "]\n"
    
  let testEmptyRemoval3 () =
    Printf.printf "Empty production removal test 3: [";
    let first = [ ("S", ['a'; 'b'; epsilon]); ("A", ['a'; epsilon]); ("B", ['b'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a'; 'b'; dollar]); ('B', ['b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->AB", ['a'; 'b'; dollar]);
                      ("A->aAA", ['a']); ("A->", ['a'; 'b'; dollar]); 
                      ("B->bBB", ['b']); ("B->", ['b'; dollar]) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text epsilon_removal_example3) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasEmptyProductions true); 
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasEmptyProductions false);
    Printf.printf "]\n"
    ;;
    
	let runAll =
		if Util.testing active "ContextFreeGrammarLL1" then begin
			testExample1 ();
			testExample2 ();
			testExample3 ();
			testExample4 ();
			testExample5 ();
			testExample6 ();
			testDissertation ();
			testNFGrammar ();
			testAccessible1 ();
			testAccessible2 ();
			testProductive1 ();
			testProductive2 ();
			cleanGrammar1 ();
			testDirectRecursion1 ();
			testDirectRecursion2 ();
			testIndirectRecursion1 ();
			testIndirectRecursion2 ();
			testIndirectRecursion3 ();
			testIndirectRecursion4 ();
			testIndirectRecursion5 ();
			testLeftFactoring1 ();
			testLeftFactoring2 ();
			testLeftFactoring3 ();
			testLeftFactoring4 ();
			testLeftFactoring5 ();
			testLeftFactoring6 ();
			testUnitRemoval1 ();
			testUnitRemoval2 ();
			testUnitRemoval3 ();
			testUnitRemoval4 ();
			testUnitRemoval5 ();
			testEmptyRemoval1 ();
			testEmptyRemoval2 ();
			testEmptyRemoval3 ()
		end
end


# 3 "src/ContextFreeGrammarLRTests.ml"
(*
 * ContextFreeGrammarLRTests.ml
 *
 * This file is part of the OCamlFlat library
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
 *  Written by Bernardo Sousa (br)
 *)

(*
 * ChangeLog:
 *
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: Context-free grammar testing.
 *)
 
open BasicTypes
open ContextFreeGrammarBasic  

module ContextFreeGrammarLRTests : sig end =
struct
	let active = false

	open LR0Grammar
	open SLR1Grammar
	open LR1Grammar
	open LALR1Grammar

	let (lr1grammar:t) = (* basic LR1 with no First usage *)
	{alphabet = symbols "01";
	variables = symbols "SXA" ;
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X"; "X -> A"; "A -> 0" ; "A -> 1"])
	} ;;

	let (lr1grammar2:t) = (* basic LR1 with basic First usage *)
	{alphabet = symbols "01";
	variables = symbols "SXA" ;
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X"; "X -> A01"; "A -> 0" ; "A -> 1"])
	} ;;

	let ttLR1 () = (* Full grammar *)
		makeLR1Diagram lr1grammar;;

	let (lr1grammarX:t) = (* exemplo do professor Luis Monteiro *) 
	{alphabet = symbols "ab";
	variables = symbols "SAB";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> A"; "A -> BA"; "A -> ~" ; "B -> aB"; "B -> b"; ])
	} ;; (* Resumindo esta gramatica: (B)^n, onde B = (a)^m b *)
	(* (a*b)* *)

	let (lr0htmlgrammar:t) = (* teste de html *) 
	{alphabet = symbols "abcde";
	variables = symbols "SABCDE";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> ABCDE"; "A -> a | "; "B -> b | "; "C -> c"; "D -> d | "; "E -> e | "])
	} 

	let ttisLR0 () =
		isLR0 lr0htmlgrammar;;

	let ttLR1X () = (* Full grammar *)
		makeLR1Diagram lr1grammarX;;
		
	let ttLR1Id () = 
		makeLR1DiagramId (makeLR1Diagram lr1grammarX) ;;
		
	let ttLR1Table () =
		makeLR1Table (makeLR1DiagramId (makeLR1Diagram lr1grammarX)) lr1grammarX ;; 
		
	let ttLR1Word () = (* simple test *)
		acceptWordLR1 (word "ab") lr1grammarX ;;
		
		
		
	let ttLR1Word2 () = (* long simple test *)
		acceptWordLR1 (word "bbbbbbbb") lr1grammarX ;;
		
	let ttLR1Word3 () = (* long complex test *)
		acceptWordLR1 (word "aaaaaaaaabbbbbbbb") lr1grammarX ;;
		
	let ttLR1Word4 () = (* empty test *)
		acceptWordLR1 [] lr1grammarX ;;
		
	let ttLR1Word5 () = (* combination test *)
		acceptWordLR1 (word "ababababababababaaaaaaaaabbbbbbbb") lr1grammarX ;;
		
	let ttLR1WordFail () = (* falha mas da erro em vez de false *)
		acceptWordLR1 (word "bbbbbbbba") lr1grammarX ;;
		
		
	(*----- Test functions LALR1-----*)


	let (lalr1grammar:t) = (* basic SLR1 with Follow usage *)
		{alphabet = symbols "cd";
		variables = symbols "SXC";
		initial = symb "S";
		rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X"; "X -> CC"; "X -> ~"; "C -> cC" ; "C -> d"])
	} ;;

	let ttLALR1 () = (* Full grammar *)
		makeLALR1FromLR1 (makeLR1Diagram lalr1grammar);;	
		
	let ttLR1Table () =
		makeLR1Table (makeLR1DiagramId (makeLR1Diagram lalr1grammar)) lalr1grammar ;; 
		
	let ttLALR1Table () =
		makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram lalr1grammar))) lalr1grammar ;; 	

	let ttLALR1Word () = (* simple test *)
		acceptWordLALR1 [] lalr1grammar ;;
		
	let ttLALR1Word2 () = (* simple test *)
		acceptWordLALR1 (word "dd" ) lalr1grammar ;;
		
		
	let ttLALR1WordFail () = (* simple test *)
		acceptWordLALR1 (word "cd" )  lalr1grammar ;;
		
	let ttIsLALR1 () = isLALR1 lalr1grammar ;;

	let ttIsLR1 () = isLR1 lalr1grammar ;;

		
		
	(*----- Test functions SLR1-----*)

	let (slr1grammar:t) = (* basic SLR1 with Follow usage *)
		{alphabet = symbols "acdz";
		variables = symbols "SXAB";
		initial = symb "S";
		rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X"; "X -> aAc"; "X -> aBd"; "A -> z" ; "B -> z"])
	} ;;


	let (slr1grammarFail:t) = (* basic SLR1 with Follow usage *)
		{alphabet = symbols "acdz";
		variables = symbols "SXAB";
		initial = symb "S";
		rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X"; "X -> aAd"; "X -> aBd"; "A -> z" ; "B -> z"])
	} ;;

	let ttSLR1Table () =
		makeSLR1Table (makeLR0DiagramId (makeLR0Diagram slr1grammar)) slr1grammar ;; 

	let ttSLR1Word() =
		acceptWordSLR1 (word "azc") slr1grammar ;;
		
	let ttSLR1Word2() =
		acceptWordSLR1 (word "azd") slr1grammar ;;
		
	let ttSLR1WordFail() =
		acceptWordSLR1 (word "") slr1grammar ;;
		
	let ttSLR1WordFail2() =
		acceptWordSLR1 (word "azcd") slr1grammar ;;
		
	let ttSLR1WordFail3() =
		acceptWordSLR1 (word "az") slr1grammar ;;
		
	let ttSLR1WordFail4() =
		acceptWordSLR1 (word "azc$") slr1grammar ;;
		
	let ttIsSLR1() = isSLR1 slr1grammar ;;

	let ttIsSLR1Fail() = isSLR1 slr1grammarFail ;; (* é preciso alterar o follow para testar fails... dor *)
		


	(*----- Test functions LR0-----*)

	let showLR0States (cfg:t) =
		let diagram = makeLR0Diagram cfg in
		let (states,transitions) : lr0Diagram = diagram in
		states
		
	let showLR0Transitions (cfg:t) =
		let diagram = makeLR0Diagram cfg in
		let (states,transitions) : lr0Diagram = diagram in
		transitions


	let (grammar:t) = 
	{alphabet = symbols "01";
	variables = symbols "SX";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 1S0"; "S -> X"; "X -> 0X1" ; "X -> ~"])
	} ;;

	let tt () = (* Full grammar *)
		makeLR0Diagram grammar;;


	let (grammar2:t) = 
	{alphabet = symbols "1";
	variables = symbols "S";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 1"])
	} ;;

	let tt2 () (* Single State Grammar *) =
		makeLR0Diagram grammar2;;
		

	let (grammar3:t)  = 
	{alphabet = symbols "01";
	variables = symbols "S";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 111111"])
	} ;;

	let tt3 () (* Multiple State/Single Rule Grammar *)=
		makeLR0Diagram grammar3;;


	let (grammar4:t)  = 
	{alphabet = symbols "01";
	variables = symbols "S";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 111111"; "S -> 000000"])
	} ;;

	let tt4 () (* Multiple State/Multiple Rule Grammar *) =
		makeLR0Diagram grammar4;;


	let (grammar5:t)  = 
	{alphabet = symbols "01";
	variables = symbols "SA";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 111111"; "S -> 0X1"; "X -> 01" ])
	} ;;

	let (grammar5v2:t) (* Copy to test sorting in sets *) = 
	{alphabet = symbols "01";
	variables = symbols "SA";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 111111"; "S -> 0A1"; "A -> 01" ])
	} ;;

	let tt5 () (* Multiple Variables/Multiple State/Multiple Rule Grammar *) =
		makeLR0Diagram grammar5;;


	let (grammar6:t) = 
	{alphabet = symbols "01";
	variables = symbols "SXA";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 1X0"; "X -> A"; "A -> 0A1"; "A -> 01"])
	} ;;

	let tt6 () (* Almost Full Grammar\No rule containing only epsilon *) =
		makeLR0Diagram grammar6;;

	let (grammar7:t) = 
	{alphabet = symbols "ab$";
	variables = symbols "SXA";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X$"; "X -> XA"; "X -> A"; "A -> aXb"; "A -> ab"])
	} ;;

	let tt7 () (* Gramática LR0 do exemplo de Luis Monteiro *) =
		makeLR0Diagram grammar7;;

		
	let tt7Count () : bool (* Gramática LR0 do exemplo de Luis Monteiro *) =
		let (a,b) :lr0Diagram = makeLR0Diagram grammar7 in
		if (Set.size a = 9 && Set.size b = 13) then true else false
		
		
	let (grammar7f:t) = 
	{alphabet = symbols "abc$";
	variables = symbols "SXA";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X$"; "X -> XA"; "X -> A"; "A -> aXb"; "A -> ab";"A -> abc"])
	} ;;

	let (grammar7alt:t) = 
	{alphabet = symbols "ab$";
	variables = symbols "SXAF";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X$"; "X -> XA"; "X -> A"; "A -> aXb"; "A -> ab";"A -> abF"; "F -> FA" ])
	} ;;
		
	let tt7LR0 () (* Gramática LR0 do exemplo de Luis Monteiro *) =
		isLR0 grammar7;;
		
	let ttLR0Fail () (* Deve dar falso devido a dois items completos *) =
		isLR0 grammar7f;;
		
	let ttLR0Alt () (* Devia dar verdadeiro com um item completo e um item incompleto que espera uma variavel, mas na prática isto é impossivel, porque é preciso calcular o fecho para essa variavel, esse fecho novo causa um conflito, a menos que a variavel não tenha uma regra respectiva, sendo nesse caso uma variavel inutil *) =
		isLR0 grammar7alt;;

	let ttIncon1 () = makeLR0Diagram grammar5;;

	let ttIncon2 () = makeLR0Diagram grammar5v2;;


	let ttId () = makeLR0DiagramId (makeLR0Diagram grammar7) ;;
			
	let ttx () =
		makeLR0Table (makeLR0DiagramId (makeLR0Diagram grammar7)) grammar7 ;; 
		
	let ttx2 () =
		makeLR0Table (makeLR0DiagramId (makeLR0Diagram grammar5)) grammar5 ;; 


	let ttWord () = 
		acceptWordLR0V2 (word "1") grammar2 ;;
		
	let ttWordFail () = 
		acceptWordLR0V2 (word "10") grammar2 ;;
		
	let ttWord2 () = 
		acceptWordLR0V2 (word "111111") grammar5 ;;
		
	let ttWord2Fail () = 
		acceptWordLR0V2 (word "1111111") grammar5 ;;	
		
	let ttWord3 () = 
		acceptWordLR0V2 (word "0011") grammar5 ;;
		
	let ttWord3Fail () = 
		acceptWordLR0V2 (word "00111") grammar5 ;;
		
	let ttWord4 () = 
		acceptWordLR0V2 (word "100110") grammar6 ;;
		
	let ttWord4Fail () = 
		acceptWordLR0V2 (word "10011") grammar6 ;;
		
	let ttWordX () =
		acceptWordLR0V2 (word "aaabbb$") grammar7 ;;
		
	let ttWordXFail () =
		acceptWordLR0V2 (word "aaabbb") grammar7 ;;
		
	let tt3LR0 () (* bug test *) =
		isLR0 grammar5;;	
		
	let lr0DiagnosticTest () =
		ttWord() && ttWord2() && ttWord3() && ttWord4() && ttWordX()
		
	let lr0DiagnosticFailTest () =
		ttWordFail() && ttWord2Fail() && ttWord3Fail() && ttWord4Fail() && ttWordXFail()	

	let runAll =
		if Util.testing active "ContextFreeGrammarLR" then begin
			ignore (tt3LR0 ())
		end		
end	


# 3 "src/PushdownAutomatonTests.ml"
(*
 * PushdownAutomatonTests.ml
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
 *  Written by Carlos Freitas (cf)
 *)

(*
 * ChangeLog:
 *
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: Pushdown automata testing.
 *)

open BasicTypes

module PushdownAutomatonTests : sig end =
struct
	let active = false

	let exer_abcd = {| {
			kind : "exercise",
			description : "this is an example",
			name : "exer_abcd",
			problem : "Convert the regular expression (a+b)*(c+d) to finite automaton.",
			inside : ["abc","c","ab","b","abac"],
			outside : ["","aba","bab","abba","baab","abcd"],
			properties : []
		} |}

	let pda_astar = {| {
			kind: "pushdown automaton",
			description: "this is an example",
			name: "pda_astar",
			inputAlphabet: ["a"],
			stackAlphabet: ["a", "$"],
			states: ["START"],
			initialState: "START",
			initialStackSymbol: "$",
			transitions: [
				["START", "$", "a", "START", "$"]
			],
			acceptStates: ["START"],
			criteria: "true"
			} |}

	let test0 () =
		let pda = new PushdownAutomaton.model (Arg.Text pda_astar) in
			let j = pda#toJSon in
				JSon.show j


	let pdaReach = {| {
			kind: "pushdown automaton",
			description : "this is an example",
			name : "abc",
			inputAlphabet : ["a","b"],
			stackAlphabet: ["$"],
			states : ["S1","S2","S3","S4","S5","S6"],
			initialState : "S1",
			initialStackSymbol: "$",
			transitions : [
					["S1","$","~","S2","$"], ["S1","$","a","S3","$"],
					["S2","$","a","S2","$"],
					["S3","$","~","S4","$"],
					["S4","$","~","S5","$"],
					["S5","$","~","S3","$"], ["S5","$","~","S5","$"]
				],
			acceptStates : ["S1"],
			criteria: "true"
	} |}

	let testReachable () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaReach) in
		let start = pda#representation.initialState in
		Util.println ["Reachable states:"]; Util.printStates (pda#reachable start)

		let pdaProductive = {| {
			kind: "pushdown automaton",
			description : "this is an example",
			name : "abc",
			inputAlphabet : ["a","b"],
			stackAlphabet: ["$"],
			states : ["S1","S2","S3","S4","S5","S6"],
			initialState : "S1",
			initialStackSymbol: "$",
			transitions : [
					["S1","$","~","S2","$"], ["S1","$","a","S3","$"],
					["S2","$","a","S2","$"],
					["S3","$","~","S4","$"],
					["S4","$","~","S5","$"],
					["S5","$","~","S3","$"], ["S5","$","~","S5","$"]
				],
			acceptStates : ["S2"],
			criteria: "true"
		} |}

	let testProductive () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaProductive) in
		Util.println ["Productive states:"]; Util.printStates pda#productive

	let testGetUsefulStates () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaProductive) in
		Util.println ["Useful states:"]; Util.printStates pda#getUsefulStates

	let testGetUselessStates () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaProductive) in
		Util.println ["Useless states:"]; Util.printStates pda#getUselessStates

	let pdaEmptyStackCriteria = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pda_astar",
		inputAlphabet: ["a"],
		stackAlphabet: ["a", "$"],
		states: ["S2"],
		initialState: "S2",
		initialStackSymbol: "$",
		transitions: [
			["S2", "$", "a", "S2", "$"]
		],
		acceptStates: [],
		criteria: "false"
		} |}

	let pdaEmptyAcceptStatesCriteria = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pda_astar",
		inputAlphabet: ["a"],
		stackAlphabet: ["a", "$"],
		states: ["S2"],
		initialState: "S2",
		initialStackSymbol: "$",
		transitions: [
			["S2", "$", "a", "S2", "$"]
		],
		acceptStates: ["S2"],
		criteria: "true"
		} |}

	let testTransformToAcceptCriteria () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaEmptyStackCriteria) in
		let result: PushdownAutomaton.model = pda#transformPdaToAcceptStates in
		Util.println ["Initial PDA empty stack criteria:"];JSon.show pda#toJSon;
		Util.println ["PDA transformed to accept states criteria:"]; JSon.show (result#toJSon)

	let testTransformToEmptyStackCriteria () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaEmptyAcceptStatesCriteria) in
		let result: PushdownAutomaton.model = pda#transformPdaToAcceptEmptyStack in
		Util.println ["Initial PDA accept states criteria:"];JSon.show pda#toJSon;
		Util.println ["PDA transformed to empty stack criteria:"]; JSon.show (result#toJSon)


	let pdaNonDeterministic = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pda_astar",
		inputAlphabet: ["a"],
		stackAlphabet: ["a", "$"],
		states: ["S1"],
		initialState: "S1",
		initialStackSymbol: "$",
		transitions: [
			["S1", "$", "a", "S1", "$"],
			["S1", "$", "~", "S1", "$"]
		],
		acceptStates: ["S1"],
		criteria: "true"
		} |}

	let pdaDeterministic = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pda_astar",
		inputAlphabet: ["a", "b"],
		stackAlphabet: ["a", "$"],
		states: ["S1"],
		initialState: "S1",
		initialStackSymbol: "$",
		transitions: [
			["S1", "$", "a", "S1", "$"],
			["S1", "$", "b", "S1", "$"],
			["S1", "a", "~", "S1", "$"]
		],
		acceptStates: ["S1"],
		criteria: "true"
		} |}

	let testNotDeterministic () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaNonDeterministic) in
		let deterministic = pda#isDeterministic in
		if deterministic then
			Util.println ["automata is deterministic"] else Util.println ["automata is non-deterministic"];
		assert (not deterministic)

	let testDeterministic () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaDeterministic) in
		let deterministic = pda#isDeterministic in
		if deterministic then
			Util.println ["automata is deterministic"] else Util.println ["automata is non-deterministic"];
		assert (deterministic)

	let testIsFa () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaNonDeterministic) in
		let isFa = pda#isFiniteAutomaton in
		if isFa then
			Util.println ["automata is equivalent to FA"] else Util.println ["automata is not equivalent to FA"];
		assert (isFa)

	let testIsNotFa () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaDeterministic) in
		let isFa = pda#isFiniteAutomaton in
		if isFa then
			Util.println ["automata is equivalent to FA"] else Util.println ["automata is not equivalent to FA"];
		assert (not isFa)

	let pdaAccept = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pdaAccept",
		inputAlphabet: ["a", "b"],
		stackAlphabet: ["a", "$"],
		states: ["S1", "S2"],
		initialState: "S1",
		initialStackSymbol: "$",
		transitions: [
			["S1", "$", "a", "S1", "a$"],
			["S1", "a", "a", "S1", "aa"],
			["S1", "a", "b", "S2", "a"]
		],
		acceptStates: ["S2"],
		criteria: "true"
		} |}

	let pdaAccept2 = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pdaAccept2",
		inputAlphabet: ["a", "b"],
		stackAlphabet: ["a", "$"],
		states: ["S1", "S2", "S3"],
		initialState: "S1",
		initialStackSymbol: "$",
		transitions: [
			["S1", "$", "a", "S1", "a$"],
			["S1", "a", "a", "S1", "aa"],
			["S1", "a", "~", "S2", "a"],
			["S2", "a", "b", "S2", ""],
			["S2", "$", "~", "S3", "$"]
		],
		acceptStates: ["S3"],
		criteria: "true"
		} |}

	let pdaAccept3 = {| {
			kind: "pushdown automaton",
			description: "this is an example",
			name: "pdaAccept2",
			inputAlphabet: ["a", "b"],
			stackAlphabet: ["a", "$"],
			states: ["S1", "S2", "S3"],
			initialState: "S1",
			initialStackSymbol: "$",
			transitions: [
				["S1", "$", "a", "S1", "a$"],
				["S1", "a", "a", "S1", "aa"],
				["S1", "a", "~", "S2", "a"],
				["S1", "a", "~", "S1", "aa"],
				["S2", "a", "b", "S2", ""],
				["S2", "$", "~", "S3", "$"]
			],
			acceptStates: ["S3"],
			criteria: "true"
			} |}

	let testAccept() =
	let pda = new PushdownAutomaton.model (Arg.Text pdaAccept) in
	let accepted = pda#accept [symb "a"; symb "a"; symb "b"] in
		if accepted then
			Util.println ["Accepted word"] else Util.println ["Did not accept word"];
			assert (accepted)

	let testAccept2() =
		let pda = new PushdownAutomaton.model (Arg.Text pdaAccept2) in
		let accepted = pda#accept [symb "a"; symb "a"; symb "b"; symb "b"] in
			if accepted then
				Util.println ["Accepted word"] else Util.println ["Did not accept word"];
				assert (accepted)

	let testAccept3() =
		let pda = new PushdownAutomaton.model (Arg.Text pdaAccept3) in
		let accepted = pda#accept [symb "a"; symb "a"; symb "b"; symb "b"] in
			if accepted then
				Util.println ["Accepted word"] else Util.println ["Did not accept word"];
				assert (accepted)

	let testGenerate() =
		let pda = new PushdownAutomaton.model (Arg.Text pdaAccept2) in
		let words = pda#generate 6 in
			Util.println ["Generated words:"];
			Util.printWords words

	let testSearchTree() =
		let pda = new PushdownAutomaton.model (Arg.Text pdaAccept3) in
		let searchTree = pda#getSearchTree [symb "a"; symb "b"] in
			PushdownAutomatonPrivate.printSearchTree searchTree

	let runAll =
		if Util.testing active "PushdownAutomaton" then begin
			Util.header "PushdownAutomatonTests starting...";
			test0 ();
			testReachable ();
			testProductive ();
			testGetUsefulStates ();
			testGetUselessStates ();
			testTransformToAcceptCriteria ();
			testTransformToEmptyStackCriteria ();
			testNotDeterministic ();
			testDeterministic ();
			testIsFa ();
			testIsNotFa ();
			testAccept ();
			testAccept2 ();
			testAccept3 ();
			testGenerate ();
			testSearchTree()
		end
end


# 3 "src/TuringMachineTests.ml"
(*
 * PushdownAutomatonTests.ml
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
 * jan/2025 (amd) - New file.
 *)

(*
 * Description: Pushdown automata testing.
 *)

open BasicTypes

module TuringMachineTests : sig end =
struct
	open TuringMachine
	open TuringMachineX
	
	let active = false

	let test0 () =
		let j = Examples.jsonExample "tm_astar1" in
		let tm: t = make (Arg.JSon j) in
			if isLB tm then print_string "LB\n" else print_string "not LB\n";
			show tm

	let test1 () =
		let tm = new TuringMachine.model (Arg.Predef "tm_astar1") in
			tm#show

	let test2 () =
		let j = Examples.jsonExample "tm_translate" in
		let tm: t = make (Arg.JSon j) in
		let tmx = tmX tm in
		let tm = tmI tmx in
			show tm

	let test3 () =
		let j = Examples.jsonExample "tm_translate" in
		let tm: t = make (Arg.JSon j) in
		let tm: t = { tm with initialState = "q2" } in
			show tm

	let runAll =
		if Util.testing active "TuringMachineSupport" then begin
			Util.sep (); test3 ()
		end

end

# 1 "src/CompositionTests.ml"
(*
 * Composition.ml
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
 *  Written by Carolina Duarte (cd)
 *)

(*
 * ChangeLog:
 *
 *)

(*
 * Description: Model composition testing.
 *
 *)
 
open BasicTypes

module CompositionTests : sig end =
struct
	open Composition

	let active = false

	let comp_abc = {| {
			kind : "composition",
			description : "this is an example",
			name : "comp_abc",
			comp : "[dfa_astar]^[dfa_astar]"
	} |}
	
	let test0 () =
		let comp = new Composition.model (Arg.Text comp_abc) in
			comp#show2

	let checkWord comp s =
		if comp#accept (str2word s) then "ACCEPT" else "REJECT"

	let checkWords comp l =
		List.iter (fun s -> Printf.printf "\"%s\" %s\n" s (checkWord comp s)) l

	let test1 () =
		let comp = new Composition.model (Arg.Text comp_abc) in
			checkWords comp ["aa"; "bb"]

	let runAll =
		if Util.testing active "Composition" then begin
			Util.sep (); test0();
			Util.sep (); test1();
			
		end
end



# 1 "src/LearnOCamlTests.ml"
(*
 * LearnOCamlTests.ml
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
 *  Written by Artur Miguel Dias, Rita Macedo (amd, rm)
 *)

(*
 * ChangeLog:
 *
 * apr/2023 (amd) - New file.
 *)

open BasicTypes

module LearnOCamlTests : sig end =
struct
	let active = false

	let prepare target =
		print_string ("Generate: " ^ target ^ "\n");
		LearnOCaml.setOCamlFlatDir "~/work/OCamlFlat";
		LearnOCaml.setExercicesDir "~/work/OCamlFlat/exercises";
		LearnOCaml.setExerciceName target

	let prepare0 () =
		LearnOCaml.setOCamlFlatDir "~/work/OCamlFlat";
		LearnOCaml.setExercicesDir "~/work/learn/my-learn-ocaml-repository/exercises";
		LearnOCaml.setExerciceName "default"

	let make exercise model =
		prepare exercise;
		let exercise = Examples.jsonExample exercise in
		let solution = Examples.jsonExample model in
			LearnOCaml.generateExerciseDir exercise solution false
	
	let test0 () =
		make "exer_astar_fa" "dfa_astar"
			
	let test1 () =
		make "exer_astar_re" "re_astar"
			
	let test2 () =
		make "exer_balanced_cfg" "cfg_balanced"
	
	let fe_colors = {| {
		kind : "finite enumeration",
		description : "this is an example",
		name : "colors",
		words : ["Red", "Yellow", "Blue"]
	} |}
			
	let test3 () =
		prepare "exer_astar";
		let exercise = Examples.jsonExample "exer_astar" in
		let solution = JSon.parse fe_colors in
			LearnOCaml.generateExerciseDir exercise solution false

	let decl1 = {|
		let solution: finiteAutomaton =
		{
			alphabet = ['a'];
			states = ["START"];
			initialState = "START";
			transitions = [("START", 'a', "START")];
			acceptStates = ["START"]
		} |}
		
	let decl2 = {|
		let solution: RegularExpression.tx =
			"z*"
	|}
		
	let decl3 = {|
		let solution: ContextFreeGrammarBasic.tx =
		{
			alphabet = ['0'; '1'];
			variables = ['S'; 'P'];
			initial = 'S';
			rules = [	"S -> 1S0 | P";
						"P -> 0P1 | ~" ]
		}
	|}
		
	let decl4 = {|
		let solution: FiniteEnumeration.tx =
			["A"; "B"; "C"; "D"; "E"]
	|}

	let test4 () =
		let j = LearnOCaml.decl2json decl1  in
			JSon.show j
 
	let runAll =
		if Util.testing active "LearnOCaml" then begin
			test0 ();
			test1 ();
			test2 ()
		end
end
