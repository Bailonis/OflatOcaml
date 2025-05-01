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
