(*
 * FiniteEnumerationTests.ml
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
 * Description: Finite enumeration testing.
 *)

open BasicTypes

module FiniteEnumerationTests : sig end =
struct
	open FiniteEnumeration

	let active = false
	
	let fe_colors = {| {
		kind : "finite enumeration",
		description : "this is an example",
		name : "colors",
		words : ["Red", "Yellow", "Blue"]
	} |}
	
	let exer_colors = {| {
		kind : "exercise",
		description : "this is an example",
		name : "exer_colors",
		problem : "Colors of length 3",
		inside : ["Red", ""],
		outside : ["Yellow","Blue"],
		properties : ["fail"]
	} |}

	let test0 () =
		let (id,fe) = FiniteEnumeration.make2 (Arg.Text fe_colors) in
			Util.sep ();
			show2 id fe

	let test1 () =
		let fe = FiniteEnumeration.make (Arg.Text fe_colors) in
		let ex = Exercise.make (Arg.Text exer_colors) in
		let (ins,outs,props) = FiniteEnumeration.checkExerciseFailures ex fe in
			Util.sep ();
			FiniteEnumeration.show fe;
			Exercise.show ex;
			Exercise.showRes (ins,outs,props)

	let test2 () =
		let fe = new FiniteEnumeration.model (Arg.Text fe_colors) in
		let e = new Exercise.exercise (Arg.Text exer_colors) in
		let (ins,outs,props) = fe#checkExerciseFailures e in	
			Util.sep ();
			fe#show;
			e#show;
			Exercise.showRes (ins,outs,props)
		
	let runAll =
		if Util.testing active "FiniteEnumeration" then begin
			test0 ();
			test1 ();
			test2 ()
		end
end

