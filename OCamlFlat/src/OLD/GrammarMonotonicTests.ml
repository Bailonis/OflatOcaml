(*
 * GrammarMonotonicTests.ml
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
 * Description: Monotonic grammar testing.
 *)

open BasicTypes

module GrammarMonotonicTests : sig end =
struct
	open GrammarMonotonic
	
	let active = true

	let zzz = {| {
			kind : "grammar",
			description : "this is an example",
			name : "ug_simple",
			alphabet : ["0", "2"],
			variables : ["S", "P"],
			initial : "S",
			rules : [	"S -> 2S0 | P",
						"2P0 -> 0P2 | ~" ]
		} |}

	let test0 () =
		let gram = make (Arg.Text zzz) in
			if isMonotonic gram then
				print_string "isMonotonic\n";
			if isContextSensitive gram then
				print_string "isContextSensitive\n";
			let gram2 = asContextSensitive gram in
				show gram2

	let runAll =
		if Util.testing active "GrammarMonotonic" then begin
			Util.sep (); test0 ();
		end
end

