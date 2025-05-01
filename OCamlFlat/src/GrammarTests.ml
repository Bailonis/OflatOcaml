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

