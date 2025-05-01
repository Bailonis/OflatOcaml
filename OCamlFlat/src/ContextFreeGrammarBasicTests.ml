(*
 * ContextFreeGrammarBasicTests.ml
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
 *  Written by João Gonçalves (jg)
 *)

(*
 * ChangeLog:
 *
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: Context-free grammar testing.
 *)

open BasicTypes

module ContextFreeGrammarBasicTests : sig end =
struct
	open ContextFreeGrammarBasic

	let active = false
	
	let test0 () =
		let m = new model (Arg.Predef "cfg_simple") in
		let j = m#toJSon in
			JSon.show j

	let test1 () =
		let m = new model (Arg.Predef "cfg_balanced") in
		let e = new Exercise.exercise (Arg.Predef "exer_balanced_cfg") in
		let result = m#checkExercise e in
			if result then Util.println ["it works"] else Util.println ["it does not work"]

	let testRegular () =
		let m = new model (Arg.Predef "cfg_simple") in
		let ws = m#isRegular in
			if ws then Util.println ["is regular"] else Util.println ["is not regular"]


	let testAcc () =
		let m = new model (Arg.Predef "cfg_simple") in
		let ws = m#accept [] in
			if ws then Util.println ["Word was accepted"]
			else Util.println ["Word was not accepted"]


	let testTrace () =
		let m = new model (Arg.Predef "cfg_simple") in
			m#acceptWithTracing (word "01")

	let testGen () =
		let m = new model (Arg.Predef "cfg_simple") in
		let ws = m#generate 4 in
			Util.printWords ws

	let showM m =
		let j = m#toJSon in
			JSon.show j
	
	let showB b =
		if b then print_string "YES\n"
		else print_string "NO\n"	
	
	let testChomsky () =
		let m = new model (Arg.Predef "cfg_balanced") in
			showB (m#accept (word ""));			
			showB (m#accept (word "[[[]]]"));			
			showB (m#accept (word "[[][][]][]"));		
			showB (m#accept (word "[[][]]][]"))			

	let testExercice () =
		let e = new Exercise.exercise (Arg.Predef "exer_balanced_cfg") in
		let g = new model (Arg.Predef "cfg_balanced") in
		let b = g#checkExercise e in
			e#show2;
			g#show2;
			showB b

	let zzz = {| {
			kind : "context free grammar",
			description : "this is an example",
			name : "qq_simple",
			alphabet : ["0", "2"],
			variables : ["S", "P"],
			initial : "S",
			rules : [	"S -> 2S0 | P",
						"2P0 -> 0P2 | ~",
						" -> A",
						" ~ -> B" ]
		} |}
		
	let testBadHeads () =
		let g = make (Arg.Text zzz) in
			show g

	let runAll =
		if Util.testing active "ContextFreeGrammarBasic" then begin
			Util.sep (); test0 ();
			Util.sep (); test1 ();
			Util.sep (); testRegular ();
			Util.sep (); testAcc ();
			Util.sep (); testTrace ();
			Util.sep (); testGen ();
			Util.sep (); testExercice();
			Util.sep (); testBadHeads()
		end
end

