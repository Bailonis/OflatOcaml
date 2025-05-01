#ifdef ALL

(*
 * TuringMachineMultiSupportPrev.ml
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
 *  Written by Miguel Lourenço (ml)
 *)

(*
 * ChangeLog:
 *
 * dez/2024 (amd) - Initial version.
 *)

(*
 * Description: Turing machine functionality.
 *)
 
open BasicTypes

module TuringMachineMultiBasics =
struct
	type symbolMulti = symbol list
	type directionMulti = direction3 list
	type transition = state * symbolMulti * state * symbolMulti * directionMulti
	type transitions = transition set

	type tx = {
		entryAlphabet: symbol list;
		tapeAlphabet: symbol list;
		empty: symbol;
		states: state list;
		initialState: state;
		transitions: transition list;
		acceptStates: state list;
		criteria: bool;
		markers: symbol list
	}
	
	type t = {
		entryAlphabet: symbols;
		tapeAlphabet: symbols;
		empty: symbol;
		states: states;
		initialState: state;
		transitions: transitions;
		acceptStates: states;
		criteria: bool; (* true = acceptStates | false = stop *)
		markers: symbols
	}
	type configuration = state * symbol list * symbol list
	type configurations = configuration set

	type path = configuration list
	type paths = path list

	let kind = "turing machine multi"
end

module TuringMachineConversions =
struct
	open TuringMachineBasics

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then {
			entryAlphabet = Set.empty;
			tapeAlphabet = Set.make [empty];	
			empty = empty;
			states = Set.make [draftState];
			initialState = draftState;
			transitions = Set.empty;
			acceptStates = Set.empty;
			criteria = false;
			markers = Set.empty
		}
		else {
			entryAlphabet = JSon.fieldSymbolSet j "entryAlphabet";
			tapeAlphabet = JSon.fieldSymbolSet j "tapeAlphabet";
			empty = JSon.fieldSymbol j "empty";
			states = JSon.fieldStateSet j "states";
			initialState = JSon.fieldState j "initialState";
			transitions = JSon.fieldTMTransitionSet j "transitions";
			acceptStates = JSon.fieldStateSet j "acceptStates";
			criteria = JSon.fieldBool j "criteria";
			markers = JSon.fieldSymbolSet j "markers"
		}

	let toJSon0 (rep: t): JSon.t =
		JSon.makeAssoc [
			("entryAlphabet", JSon.makeSymbolSet rep.entryAlphabet);
			("tapeAlphabet", JSon.makeSymbolSet rep.tapeAlphabet);
			("empty", JSon.makeSymbol rep.empty);
			("states", JSon.makeStateSet rep.states);
			("initialState", JSon.makeState rep.initialState);
			("transitions", JSon.makeTMTransitionsSet rep.transitions);
			("acceptStates", JSon.makeStateSet rep.acceptStates);
			("criteria", JSon.makeBool rep.criteria);
			("markers", JSon.makeSymbolSet rep.markers)
		]	

	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 rep)


	
	let toJSon (rep: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) rep
end

module TuringMachineBasicFunctions =
struct
	open TuringMachineBasics
	open TuringMachineConversions
	
	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		let id = Entity.createId arg kind in
		let rep = Entity.create arg fromJSon in
			Entity.endCreation id rep kind validate;
			(id, rep)

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (rep: t): unit =
		let j = toJSon rep in
			JSon.show j

	let show2 (id: Entity.t) (rep: t): unit =
		let j = toJSon2 id rep in
			JSon.show j
end

module TuringMachineX =
struct
	open TuringMachineBasics

	type transitionX  = state * symbolX * state * symbolX * direction
	
	type tx = {
		entryAlphabet: symbolX list;
		tapeAlphabet: symbolX list;
		empty: symbolX;
		states: state list;
		initialState: state;
		transitions: transitionX list;
		acceptStates: state list;
		criteria: bool;
		markers: symbolX list
	}

	let transI (a,b,c,d,e): transition = (a, symbI b, c, symbI d, e)
	let transX (a,b,c,d,e): transitionX = (a, symbX b, c, symbX d, e)

	let internalize (tm: tx): t =
	 {
		entryAlphabet = symbolsI tm.entryAlphabet;
		tapeAlphabet = symbolsI tm.tapeAlphabet;	
		empty = symbI tm.empty;	
		states = Set.make tm.states;
		initialState = tm.initialState;
		transitions = Set.make (List.map transI tm.transitions);
		acceptStates = Set.make tm.acceptStates;
		criteria = tm.criteria;
		markers = symbolsI tm.markers
	}

	let externalize (tm: t): tx = {
		entryAlphabet = symbolsX tm.entryAlphabet;
		tapeAlphabet = symbolsX tm.tapeAlphabet;	
		empty = symbX tm.empty;
		states = Set.toList tm.states;
		initialState = tm.initialState;
		transitions = Set.toList (Set.map transX tm.transitions);
		acceptStates = Set.toList tm.acceptStates;
		criteria = tm.criteria;
		markers = symbolsX tm.markers
	}
end

module TuringMachineLearnOCaml =
struct
	open TuringMachineBasics
	open TuringMachineX
end


module TuringMachineSupport =
struct
	include TuringMachineBasics
	include TuringMachineConversions
	include TuringMachineBasicFunctions
	include TuringMachineLearnOCaml
end
#endif
