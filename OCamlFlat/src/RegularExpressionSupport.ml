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
