(*
 * FiniteAutomatonSupport.ml
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
 * Description: Support types and functions for FAs.
 *)

open BasicTypes

module FiniteAutomatonBasics =
struct
	type transition3 = state * symbol * state
	type transitions3 = transition3 set
	type t = {
		alphabet : symbols;
		states : states;
		initialState : state;
		transitions : transitions3;
		acceptStates : states
	}

	type configuration = state * word
	type configurations = configuration set
	type path = configuration list
	type trail = configurations list

	let kind = "finite automaton"

	let fa_zero: t = {
		alphabet = Set.empty;
		states = Set.make [draftState];
		initialState = draftState;
		transitions = Set.empty;
		acceptStates = Set.empty
	}
end

module FiniteAutomatonConversions =
struct
	open FiniteAutomatonBasics

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			fa_zero
		else {
			alphabet = JSon.fieldSymbolSet j "alphabet";
			states = JSon.fieldStateSet j "states";
			initialState = JSon.fieldState j "initialState";
			transitions = JSon.fieldTriplesSet j "transitions";
			acceptStates = JSon.fieldStateSet j "acceptStates"
		}

	let toJSon0 (rep: t): JSon.t =
		JSon.makeAssoc [
			("alphabet", JSon.makeSymbolSet rep.alphabet);
			("states", JSon.makeStateSet rep.states);
			("initialState", JSon.makeState rep.initialState);
			("transitions", JSon.makeTriplesSet rep.transitions);
			("acceptStates", JSon.makeStateSet rep.acceptStates)
		]
	
	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 rep)
	
	let toJSon (rep: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) rep
end

module FiniteAutomatonBasicFunctions =
struct
	open FiniteAutomatonBasics
	open FiniteAutomatonConversions

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

module FiniteAutomatonX =
struct
	open FiniteAutomatonBasics

	type transition3X = state * symbolX * state
	type tx = {
		alphabet : symbolX list;
		states : state list;
		initialState : state;
		transitions : transition3X list;
		acceptStates : state list
	}

	let transitions3I (l: transition3X list): transitions3 =
		let trans3I (a,b,c): transition3 = (a, symbI b, c) in
			Set.make (List.map trans3I l)
			
	let transitions3X (s: transitions3): transition3X list =
		let trans3X (a,b,c): transition3X = (a, symbX b, c) in
			List.map trans3X (Set.toList s)

	let internalize (fa: tx): t = {
		alphabet = symbolsI fa.alphabet;
		states = Set.make fa.states;
		initialState = fa.initialState;
		transitions = transitions3I fa.transitions;
		acceptStates = Set.make fa.acceptStates
	}
	
	let externalize (fa: t): tx = {
		alphabet = symbolsX fa.alphabet;
		states = Set.toList fa.states;
		initialState = fa.initialState;
		transitions = transitions3X fa.transitions;
		acceptStates = Set.toList fa.acceptStates
	}
end

module FiniteAutomatonLearnOCaml =
struct
	open FiniteAutomatonBasics
	open FiniteAutomatonX

	let moduleName =
		"FiniteAutomaton"

	let xTypeName =
		"finiteAutomaton"

	let transs3XD (l: transition3X list): string =
		let t2d (a,b,c) =
			Printf.sprintf "(%s, %s, %s)"
			(stateXD a)
			(symbXD b)
			(stateXD c)
		in listD t2d l

	let solution (name: string) (rep: t): string =
		let repx = externalize rep in
		Printf.sprintf {zzz|
		%s{
			alphabet = %s;
			states = %s;
			initialState = %s;
			transitions = %s;
			acceptStates = %s
		}
		|zzz}	(* please, do not change this line *)
			(FiniteEnumerationLearnOCaml.displayHeader name xTypeName)
			(symbolsXD repx.alphabet)
			(statesXD repx.states)
			(stateXD repx.initialState)
			(transs3XD repx.transitions)
			(statesXD repx.acceptStates)


	let prelude : string =
		Printf.sprintf {zzz|
		type symbol = %s
		type state = string
		type finiteAutomaton = {
			alphabet : symbol list;
			states : state list;
			initialState : state;
			transitions : (state * symbol * state) list;
			acceptStates : state list
		}
		|zzz}	(* please, do not change this line *)
			symbolTypeName

	let example : JSon.t =
		JSon.parse {|
		{
			kind : "finite automaton",
			description : "this is an example",
			name : "fa example",
			alphabet: ["w", "z"],
			states : ["START", "X", "Z"],
			initialState : "START",
			transitions : [
				["START", "w", "X"], ["X", "z", "X"]
			],
			acceptStates : ["Z"]
		}
		|}	(* please, do not change this line *)
end

module FiniteAutomatonSupport =
struct
	include FiniteAutomatonBasics
	include FiniteAutomatonConversions
	include FiniteAutomatonBasicFunctions
	include FiniteAutomatonLearnOCaml
end
