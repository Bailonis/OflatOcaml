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
