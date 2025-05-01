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

#define SYMBOL_IS_CHAR	0
#define OPAQUE_SYMBOL	1

module type SymbolOpaqueSig =
sig

#if OPAQUE_SYMBOL = 1
	type symbol (* opaque *)
#else
	type symbol = string
#endif

#if SYMBOL_IS_CHAR > 0
	type symbolX = char
#else
	type symbolX = string
#endif
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
#if SYMBOL_IS_CHAR > 0
	type symbol = char
	type symbolX = char
	
	let char2symb (c: char): symbol = c
	let symb2char (s: symbol): char = s
	let str2symb (s: string): symbol = if String.length s > 0 then String.get s 0 else '?'
	let symb2str (s: symbol): string = Char.escaped s

	let symbolTypeName = "char"
	let symbDisplayQuote = "'" 
	
#else
	type symbol = string
	type symbolX = string

	let char2symb c: symbol = Char.escaped c
	let symb2char s: char = if String.length s > 0 then String.get s 0 else '?'
	let str2symb s: symbol = s
	let symb2str s: string = s

	let symbolTypeName = "string"
	let symbDisplayQuote = "\"" 
#endif

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
