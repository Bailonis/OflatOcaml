(*
 * ExerciseSupport.ml
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
 * oct/2022 (amd) - New module
 *)

(*
 * Description: Support to pedagogical exercises. The solutions are validated
 * using unit tests.
 *)

open BasicTypes

module ExerciseBasics =
struct
	type tx = {
		problem : string;
		inside : wordX list;
		outside : wordX list;
		properties : properties
	}
	
	type t = {
		problem : string;
		inside : words;
		outside : words;
		properties : properties
	}
	
	let kind = "exercise"

	let exer_zero: t = {
		problem = "_";
		inside = Set.empty;
		outside = Set.empty;
		properties = Set.empty
	}
end

module ExerciseConversions =
struct
	open ExerciseBasics

	let internalize (e: tx): t = {
		problem = e.problem;
		inside = Set.make (List.map wordX2word e.inside);
		outside = Set.make (List.map wordX2word e.outside);
		properties = e.properties
	}

	let externalize (e: t): tx = {
		problem = e.problem;
		inside = List.map word2wordX (Set.toList e.inside);
		outside = List.map word2wordX (Set.toList e.outside);
		properties = e.properties
	}

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			exer_zero
		else {
			problem = JSon.fieldString j "problem";
			inside = Set.map str2word (JSon.fieldStringSet j "inside");
			outside = Set.map str2word (JSon.fieldStringSet j "outside");
			properties = JSon.fieldStringSet j "properties"
		}
	
	let toJSon (rep: t): JSon.t =
		JSon.makeAssoc [
			("problem", JSon.makeString rep.problem);
			("inside", JSon.makeStringSet (Set.map word2str rep.inside));
			("outside", JSon.makeStringSet (Set.map word2str rep.outside));
			("properties", JSon.makeStringSet rep.properties)
		]
	
	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon rep)
end

module ExerciseShow =
struct
	open ExerciseBasics
	open ExerciseConversions

	let show (rep: t): unit =
		let j = toJSon rep in
			JSon.show j

	let show2 (id: Entity.t) (rep: t): unit =
		let j = toJSon2 id rep in
			JSon.show j
	
	let showRes (ins,outs,props): unit =
		Util.println ["INS: "]; Util.printWords ins;
		Util.println ["OUTS: "]; Util.printWords outs;
		Util.println ["PROPS: "]; Util.printStrings props
end

module ExerciseSupport =
struct
	include ExerciseBasics
	include ExerciseConversions
	include ExerciseShow
end
