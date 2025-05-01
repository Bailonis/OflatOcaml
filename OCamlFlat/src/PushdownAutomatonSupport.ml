#ifdef ALL

(*
 * PushdownAutomaton.ml
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
 *  Written by Carlos Freitas (cf)
 *)

(*
 * ChangeLog:
 *
 * ???/2022 (cf) - ???.
 * may/2022 (amd) - Initial skeleton.
 *)

(*
 * Description: Pushdown automata functionality.
 *)

open BasicTypes

module PushdownAutomatonBasics =
struct
	type transition =
		  state			(* state *)
		* symbol		(* current symbol on top of the stack *)
		* symbol		(* consumed input symbol *)
		* state			(* next state *)
		* symbol list	(* new top of stack*)
	type transitions = transition set
		
	type t = {
		inputAlphabet : symbols;
		stackAlphabet : symbols;
		states : states;
		initialState : state;
		initialStackSymbol : symbol;
		transitions : transitions;
		acceptStates : states;
		criteria: bool; (* true = acceptStates | false = emptyStack *) 
	}
	
	let kind = "pushdown automaton"
	
	let pda_zero: t = {
		inputAlphabet = Set.empty;
		stackAlphabet = Set.make [draftVar];
		states = Set.make [draftState];
		initialState = draftState;
		initialStackSymbol = draftVar;
		transitions = Set.empty;
		acceptStates = Set.empty;
		criteria = false
	}
end

module PushdownAutomatonConversions =
struct
	open PushdownAutomatonBasics

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			pda_zero
		else {
			inputAlphabet = JSon.fieldSymbolSet j "inputAlphabet";
			stackAlphabet = JSon.fieldSymbolSet j "stackAlphabet";
			states = JSon.fieldStateSet j "states";
			initialState = JSon.fieldState j "initialState";
			initialStackSymbol = JSon.fieldSymbol j "initialStackSymbol";
			transitions = JSon.fieldQuintupletsSet j "transitions";
			acceptStates = JSon.fieldStateSet j "acceptStates";
			criteria = JSon.fieldBool j "criteria"
		}

	let toJSon0 (rep: t): JSon.t =
		JSon.makeAssoc [
			("inputAlphabet", JSon.makeSymbolSet rep.inputAlphabet);
			("stackAlphabet", JSon.makeSymbolSet rep.stackAlphabet);
			("states", JSon.makeStateSet rep.states);
			("initialState", JSon.makeState rep.initialState);
			("initialStackSymbol", JSon.makeSymbol rep.initialStackSymbol);
			("transitions", JSon.makeQuintupletsSet rep.transitions);
			("acceptStates", JSon.makeStateSet rep.acceptStates);
			("criteria", JSon.makeBool rep.criteria)
		]
	
	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 rep)


	
	let toJSon (rep: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) rep
end

module PushdownAutomatonBasicFunctions =
struct
	open PushdownAutomatonBasics
	open PushdownAutomatonConversions

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

module PushdownAutomatonX =
struct
	open PushdownAutomatonBasics

	type tx = {
		inputAlphabet: symbol list;
		stackAlphabet: symbol list;
		states: state list;
		initialState: state;
		initialStackSymbol: symbol;
		transitions: transition list;
		acceptStates: state list;
		criteria: bool
	}

	let internalize (pda: tx): t = {
		inputAlphabet = Set.make pda.inputAlphabet;
		stackAlphabet = Set.make pda.stackAlphabet;
		states = Set.make pda.states;
		initialState = pda.initialState;
		initialStackSymbol = pda.initialStackSymbol;
		transitions = Set.make pda.transitions;
		acceptStates = Set.make pda.acceptStates;
		criteria = pda.criteria
	}

	let externalize (pda: t): tx = {
		inputAlphabet = Set.toList pda.inputAlphabet;
		stackAlphabet = Set.toList pda.stackAlphabet;
		states = Set.toList pda.states;
		initialState = pda.initialState;
		initialStackSymbol = pda.initialStackSymbol;
		transitions = Set.toList pda.transitions;
		acceptStates = Set.toList pda.acceptStates;
		criteria = pda.criteria
	}
end

module PushdownAutomatonLearnOCaml =
struct
	open PushdownAutomatonBasics
	open PushdownAutomatonX

	let moduleName =
		"PushdownAutomaton"

	let xTypeName =
		"pushdownAutomaton"


	let solution (name: string) (rep: t): string =
		""

	let prelude : string =
		""

	let example : JSon.t =
		JSon.parse {|
		{
			kind : "finite automaton",
			description : "this is an example",
			name : "pda example",
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

module PushdownAutomatonSupport =
struct
	include PushdownAutomatonBasics
	include PushdownAutomatonConversions
	include PushdownAutomatonBasicFunctions
	include PushdownAutomatonLearnOCaml
end

#endif
