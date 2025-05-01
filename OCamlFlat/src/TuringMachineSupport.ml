#ifdef ALL

(*
 * TuringMachineSupport.ml
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
 * jan/2025 (amd) - Code improved and adjusted for multitape.
 * jun/2022 (amd) - New module.
 *)

(*
 * Description: Types and functions supporting multitape TMs.
 *)

open BasicTypes

module TuringMachineBasics =
struct
	type symbolM = symbol list
	type directionM = direction list
	type transition  = state * symbolM * state * symbolM * directionM
	type transitions = transition set

	type t = {
		entryAlphabet: symbols;
		tapeAlphabet: symbols;
		empty: symbol;
		states: states;
		initialState: state;
		transitions: transitions;
		acceptStates: states;
		criteria: bool; (* true = acceptStates | false = stop *)
		lbMarkers: symbol list;
		_nTapes: int
	}

	type halfTape = symbol list
	type tape = halfTape * halfTape
	type tapes = tape list
	type configuration = state * tapes
	type configurations = configuration set

	type path = configuration BasicTypes.path
	type trail = configuration BasicTypes.trail

	let kind = "turing machine"

	let tm_zero: t = {
		entryAlphabet = Set.empty;
		tapeAlphabet = Set.make [empty];	
		empty = empty;
		states = Set.make [draftState];
		initialState = draftState;
		transitions = Set.empty;
		acceptStates = Set.empty;
		criteria = false;
		lbMarkers = [];
		_nTapes = 1
	}
	
	let nTapes (tm: t): int =
		tm._nTapes

	let multi (tm: t) x =
		List.init (nTapes tm) (fun _-> x)

	let lbLeft (tm: t) =
		List.nth tm.lbMarkers 0

	let lbRight (tm: t) =
		List.nth tm.lbMarkers 1

	let calcNTapes (ts: transitions): int =
		Set.match_ ts
			(fun () -> 1)
			(fun (_,b,_,_,_) _ -> List.length b)

	let getTransSymbolMs (rep: t): symbolM set =
		let trns = rep.transitions in
		let trns2 = Set.map (fun (_,b,_,_,_) -> b) trns in
		let trns4 = Set.map (fun (_,_,_,d,_) -> d) trns in
			Set.union trns2 trns4

	let getTransSymbols (rep: t): symbols =
		Set.flatten (Set.map Set.make (getTransSymbolMs rep))

	let getTransDirectionMs (rep: t): directionM set =
		Set.map (fun (_,_,_,_,e) -> e) rep.transitions
		
	let getTransDirections (rep: t): direction set =
		Set.flatten (Set.map Set.make (getTransDirectionMs rep))
		end

module TuringMachineJSon =
struct
	open JSon
	open TuringMachineBasics

	let asDirection (j: JSon.t) (field: string): direction =
		match j with
		| JString "L" -> L
		| JString "S" -> S
		| JString "R" -> R
		| _ -> error field "Expected L|S|R" dummyDirection

	let asOptionalDirectionList (j: JSon.t) (field: string): direction list =
		match j with
		| JList l -> List.map (fun j -> asDirection j field) l
		| JString _ -> [asDirection j field]
		| _ -> error field "Expected direction list" []

	let dummyTransition = (
		dummyState,[dummySymb],dummyState,[dummySymb],[dummyDirection]
	)
	
	let asOptionalSymbolList (j: JSon.t) (field: string): symbol list =
		match j with
		| JList l -> List.map (fun j -> asSymbol j field) l
		| JString _ -> [asSymbol j field]
		| _ -> error field "Expected transition symbols" []
	
	let asTransition (j: JSon.t) (field: string): transition =
		match j with
		| JList [a; b; c; d; e] ->
			(	asState a field,
				asOptionalSymbolList b field,
				asState c field,
				asOptionalSymbolList d field,
				asOptionalDirectionList e field
			)
		| _ -> error field "Malformed TM transition" dummyTransition

	let fieldTMTransitionList (j: JSon.t) (field: string): transition list =
		match j |> getField field with
		| JNull -> Error.error field "Missing field" []
		| JList l -> List.map (fun j -> asTransition j field) l
		| _ -> []

	let fieldTransitions (j: JSon.t) (field: string): transitions  =
		Set.validate (fieldTMTransitionList j field) field

	let makeTransitions (s: transitions): JSon.t =
		JList (List.map (fun (a,b,c,d,e) ->
							JList [	JString (state2str a);
									JList (List.map (fun s -> JString (symb2str s)) b);
									JString (state2str c);
									JList (List.map (fun s -> JString (symb2str s)) d);
									JList (List.map (fun d -> JString (dirX d)) e)
							]) (Set.toList s))

end

module TuringMachineConversions =
struct
	open TuringMachineBasics

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			tm_zero
		else
			let ts = TuringMachineJSon.fieldTransitions j "transitions" in
			{
			entryAlphabet = JSon.fieldSymbolSet j "entryAlphabet";
			tapeAlphabet = JSon.fieldSymbolSet j "tapeAlphabet";
			empty = JSon.fieldSymbol j "empty";
			states = JSon.fieldStateSet j "states";
			initialState = JSon.fieldState j "initialState";
			transitions = ts;
			acceptStates = JSon.fieldStateSet j "acceptStates";
			criteria = JSon.fieldBool j "criteria";
			lbMarkers = if JSon.hasField j "markers" then	(* optional *)
							JSon.fieldSymbolList j "markers"
						else [];
			_nTapes = calcNTapes ts
			}

	let toJSon0 (tm: t): JSon.t =
		JSon.makeAssoc [
			("entryAlphabet", JSon.makeSymbolSet tm.entryAlphabet);
			("tapeAlphabet", JSon.makeSymbolSet tm.tapeAlphabet);
			("empty", JSon.makeSymbol tm.empty);
			("states", JSon.makeStateSet tm.states);
			("initialState", JSon.makeState tm.initialState);
			("transitions", TuringMachineJSon.makeTransitions tm.transitions);
			("acceptStates", JSon.makeStateSet tm.acceptStates);
			("criteria", JSon.makeBool tm.criteria);
			("lbMarkers", JSon.makeSymbolList tm.lbMarkers);
		]	

	let toJSon2 (id: Entity.t) (tm: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 tm)
	
	let toJSon (tm: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) tm
end

module TuringMachineBasicFunctions =
struct
	open TuringMachineBasics
	open TuringMachineConversions

	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (tm: t): unit =
		let j = toJSon tm in
			JSon.show j

	let show2 (id: Entity.t) (tm: t): unit =
		let j = toJSon2 id tm in
			JSon.show j
end

module TuringMachineX =
struct
	open TuringMachineBasics

	type symbolXM = symbolX list
	type directionXM = string list
	type transitionX  = state * symbolXM * state * symbolXM * directionXM

	type tapeX = string * string
	type tapesX = tapeX list
	type configurationX = state * tapesX
	type configurationsX = configurationX list

	type tx = {
		entryAlphabet: symbolX list;
		tapeAlphabet: symbolX list;
		empty: symbolX;
		states: state list;
		initialState: state;
		transitions: transitionX list;
		acceptStates: state list;
		criteria: bool;
		lbMarkers: symbolX list;
	}

	let transI (a,b,c,d,e): transition =
		(a, List.map symbI b, c, List.map symbI d, List.map dirI e)
	let transX (a,b,c,d,e): transitionX =
		(a, List.map symbX b, c, List.map symbX d, List.map dirX e)

	let tmI (tmx: tx): t =
		let ts = Set.make (List.map transI tmx.transitions) in {
			entryAlphabet = symbolsI tmx.entryAlphabet;
			tapeAlphabet = symbolsI tmx.tapeAlphabet;	
			empty = symbI tmx.empty;	
			states = Set.make tmx.states;
			initialState = tmx.initialState;
			transitions = ts;
			acceptStates = Set.make tmx.acceptStates;
			criteria = tmx.criteria;
			lbMarkers = List.map symbI tmx.lbMarkers;
			_nTapes = calcNTapes ts
		}

	let tmX (tm: t): tx = {
		entryAlphabet = symbolsX tm.entryAlphabet;
		tapeAlphabet = symbolsX tm.tapeAlphabet;	
		empty = symbX tm.empty;
		states = Set.toList tm.states;
		initialState = tm.initialState;
		transitions = Set.toList (Set.map transX tm.transitions);
		acceptStates = Set.toList tm.acceptStates;
		criteria = tm.criteria;
		lbMarkers = List.map symbX tm.lbMarkers;
	}
	
	let confX ((s,tapes): configuration): configurationX =
		let tsx = List.map (fun (l,r) ->
				(word2str (List.rev l), word2str r)) tapes in
			(s, tsx)		
	let confsX (c: configurations): configurationsX =
		List.map confX (Set.toList c)

	let pathX (p: path): configurationX pathX = pathX confX p
	let trailX (t: trail): configurationX trailX = trailX confX t
end

module TuringMachineS =
struct
	open TuringMachineBasics
	
	let pairS (a: string) (b: string): string =
		"(" ^ a ^ ", " ^ b ^ ")"
	let wordS (w: word): string = 
		wordX w
	let listS (l: string list): string =
		"[" ^ String.concat ", " l ^ "]" 
	let setS (s: string Set.t): string =
		"{" ^ String.concat ", " (Set.toList s) ^ "}" 
	let confS ((s,tapes): configuration): string =
		let tsx = List.map (fun (l,r) ->
				pairS (wordS (List.rev l)) (wordS r)) tapes in
			pairS s (listS tsx)		

	let confsS (confS: 'config -> string) (c: configurations): string =
		setS (Set.map confS c)

	let confsS (c: configurations): string =
		confsS confS c





	let pathS (configS: 'config -> string) (p: 'config BasicTypes.path): string =
		listS (List.map configS p)
	
	let pathS (p: path): string = pathS confS p
	
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
