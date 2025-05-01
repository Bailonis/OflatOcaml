#ifdef ALL

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

#endif
