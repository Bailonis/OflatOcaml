(*
 * LearnOCamlTests.ml
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
 *  Written by Artur Miguel Dias, Rita Macedo (amd, rm)
 *)

(*
 * ChangeLog:
 *
 * apr/2023 (amd) - New file.
 *)

open BasicTypes

module LearnOCamlTests : sig end =
struct
	let active = false

	let prepare target =
		print_string ("Generate: " ^ target ^ "\n");
		LearnOCaml.setOCamlFlatDir "~/work/OCamlFlat";
		LearnOCaml.setExercicesDir "~/work/OCamlFlat/exercises";
		LearnOCaml.setExerciceName target

	let prepare0 () =
		LearnOCaml.setOCamlFlatDir "~/work/OCamlFlat";
		LearnOCaml.setExercicesDir "~/work/learn/my-learn-ocaml-repository/exercises";
		LearnOCaml.setExerciceName "default"

	let make exercise model =
		prepare exercise;
		let exercise = Examples.jsonExample exercise in
		let solution = Examples.jsonExample model in
			LearnOCaml.generateExerciseDir exercise solution false
	
	let test0 () =
		make "exer_astar_fa" "dfa_astar"
			
	let test1 () =
		make "exer_astar_re" "re_astar"
			
	let test2 () =
		make "exer_balanced_cfg" "cfg_balanced"
	
	let fe_colors = {| {
		kind : "finite enumeration",
		description : "this is an example",
		name : "colors",
		words : ["Red", "Yellow", "Blue"]
	} |}
			
	let test3 () =
		prepare "exer_astar";
		let exercise = Examples.jsonExample "exer_astar" in
		let solution = JSon.parse fe_colors in
			LearnOCaml.generateExerciseDir exercise solution false

	let decl1 = {|
		let solution: finiteAutomaton =
		{
			alphabet = ['a'];
			states = ["START"];
			initialState = "START";
			transitions = [("START", 'a', "START")];
			acceptStates = ["START"]
		} |}
		
	let decl2 = {|
		let solution: RegularExpression.tx =
			"z*"
	|}
		
	let decl3 = {|
		let solution: ContextFreeGrammarBasic.tx =
		{
			alphabet = ['0'; '1'];
			variables = ['S'; 'P'];
			initial = 'S';
			rules = [	"S -> 1S0 | P";
						"P -> 0P1 | ~" ]
		}
	|}
		
	let decl4 = {|
		let solution: FiniteEnumeration.tx =
			["A"; "B"; "C"; "D"; "E"]
	|}

	let test4 () =
		let j = LearnOCaml.decl2json decl1  in
			JSon.show j
 
	let runAll =
		if Util.testing active "LearnOCaml" then begin
			test0 ();
			test1 ();
			test2 ()
		end
end
