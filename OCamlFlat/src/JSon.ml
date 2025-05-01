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

