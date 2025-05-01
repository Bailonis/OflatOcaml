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
