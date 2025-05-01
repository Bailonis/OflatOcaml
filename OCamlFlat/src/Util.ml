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
