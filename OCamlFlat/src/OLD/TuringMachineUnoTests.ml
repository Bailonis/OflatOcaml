#ifdef ALL

(*
 * TuringMachineTests.ml
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
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: Turing machine testing.
 *)


open BasicTypes
	
module TuringMachineTests : sig end =
struct
	let active = false

	(* usar exemplos 1,2,4,10 *)

	(*
	Primeiro exemplo dos slides do professor - Troca os a's pelos b's
	Este exemplo e:
		- determinista
		- nao entra em loop de configuracao
		- nao corre infinitamente sem repetir configuracao
		- nao tem estados useless
		- termina por paragem
	}
	*)
	let tm_astar1 = {| {
		kind: "turing machine",
		description: "this is an example",
		name: "tm_astar1",
		entryAlphabet: ["a", "b"],
		tapeAlphabet: ["a", "b","B"],
		empty: "B",
		states: ["q1", "q2"],
		initialState: "q1",
		transitions: [
			["q1", "B", "q2", "B", "L"],
			["q1", "a", "q1", "b", "R"],
			["q1", "b", "q1", "a", "R"],
			["q2", "a", "q2", "a", "L"],
			["q2", "b", "q2", "b", "L"]
		],
		acceptStates: [],
		criteria: "false",
		markers: [],
		} |}


	(*
	Segundo exemplo dos slides do professor - Transforma a fita BuB em BuBuB
	Este exemplo e:
		- determinista
		- nao entra em loop de configuracao
		- nao corre infinitamente sem repetir configuracao
		- nao tem estados useless
		- termina por paragem
	*)
	let tm_astar2 = {| {
		kind: "turing machine",
		description: "this is an example",
		name: "tm_astar2",
		entryAlphabet: ["a", "b"],
		tapeAlphabet: ["a", "b", "X", "Y","B"],
		empty: "B",
		states: ["q1", "q2", "q3", "q4", "q5", "q6", "q7"],
		initialState: "q1",
		transitions: [
			["q1", "a", "q2", "X", "R"],
			["q1", "b", "q5", "Y", "R"],
			["q1", "B", "q7", "B", "L"],

			["q2", "a", "q2", "a", "R"],
			["q2", "b", "q2", "b", "R"],
			["q2", "B", "q3", "B", "R"],

			["q3", "a", "q3", "a", "R"],
			["q3", "b", "q3", "b", "R"],
			["q3", "B", "q4", "a", "L"],

			["q4", "a", "q4", "a", "L"],
			["q4", "b", "q4", "b", "L"],
			["q4", "B", "q4", "B", "L"],
			["q4", "X", "q1", "X", "R"],
			["q4", "Y", "q1", "Y", "R"],

			["q5", "a", "q5", "a", "R"],
			["q5", "b", "q5", "b", "R"],
			["q5", "B", "q6", "B", "R"],

			["q6", "a", "q6", "a", "R"],
			["q6", "b", "q6", "b", "R"],
			["q6", "B", "q4", "b", "L"],

			["q7", "X", "q7", "a", "L"],
			["q7", "Y", "q7", "b", "L"]
		],
		acceptStates: [],
		criteria: "false",
		markers: []
		} |}

	(*
		Terceiro exemplo dos slides do stor - Aceita a palavra (a + b)*aa(a + b)*
		Este exemplo e:
			- determinista
			- nao entra em loop de configuracao
			- nao corre infinitamente sem repetir configuracao
			- nao tem estados useless
			- termina por estados de aceitacao
	*)
	let tm_astar3 = {| {
			kind: "turing machine",
			description: "this is an example changed",
			name: "tm_astar3",
			entryAlphabet: ["a", "b"],
			tapeAlphabet: ["a", "b","B"],
			empty: "B",
			states: ["q1", "q2", "q3"],
			initialState: "q1",
			transitions: [
				["q1", "a", "q2", "a", "R"],
				["q1", "b", "q1", "b", "R"],
				["q2", "a", "q3", "a", "R"],
				["q2", "b", "q1", "b", "R"]
			],
			acceptStates: ["q3"],
			criteria: "true",
			markers: []
			} |}

	(*
		Quarto exemplo dos slides do professor - Aceita a palavra a(i)b(i)c(i) para i >= 0
		Este exemplo e:
			- determinista
			- nao entra em loop de configuracao
			- nao corre infinitamente sem repetir configuracao
			- nao tem estados useless	
			- termina por estados de aceitacao
	*)
	let tm_astar4 = {| {
			kind: "turing machine",
			description: "this is an example",
			name: "tm_astar4",
			entryAlphabet: ["a", "b", "c"],
			tapeAlphabet: ["a", "b", "c", "X", "Y", "Z", "B"],
			empty: "B",
			states: ["q1", "q2", "q3", "q4", "q5", "q6"],
			initialState: "q1",
			transitions: [
				["q1", "B", "q6", "B", "R"],
				["q1", "Y", "q5", "Y", "R"],
				["q1", "a", "q2", "X", "R"],

				["q2", "a", "q2", "a", "R"],
				["q2", "Y", "q2", "Y", "R"],
				["q2", "b", "q3", "Y", "R"],

				["q3", "b", "q3", "b", "R"],
				["q3", "Z", "q3", "Z", "R"],
				["q3", "c", "q4", "Z", "L"],

				["q4", "Z", "q4", "Z", "L"],
				["q4", "Y", "q4", "Y", "L"],
				["q4", "b", "q4", "b", "L"],
				["q4", "a", "q4", "a", "L"],

				["q5", "Y", "q5", "Y", "R"],
				["q5", "Z", "q5", "Z", "R"],
				["q5", "B", "q6", "B", "R"]
			],
			acceptStates: ["q6"],
			criteria: "true",
			markers: []
			} |}

	(*
		Quinto exemplo dos slides do professor - Aceita a palavra (a + b)*aa(a + b)* por paragem (Semelhante ao exemplo 3)
		Este exemplo e:
			- nao determinista
			- nao entra em loop de configuracao
			- nao corre infinitamente sem repetir configuracao
			- nao tem estados useless
			- termina por paragem
	*)
	let tm_astar5 = {| {
			kind: "turing machine",
			description: "this is an example",
			name: "tm_astar5",
			entryAlphabet: ["a", "b"],
			tapeAlphabet: ["a", "b", "B"],
			empty: "B",
			states: ["q1", "q2", "q3", "q4"],
			initialState: "q1",
			transitions: [
				["q1", "a", "q2", "a", "R"],
				["q1", "b", "q1", "b", "R"],
				["q1", "B", "q4", "B", "R"],

				["q2", "a", "q3", "a", "R"],
				["q2", "b", "q1", "b", "R"],
				["q2", "B", "q4", "B", "R"],

				["q4", "a", "q4", "a", "R"],
				["q4", "b", "q4", "b", "R"],
				["q4", "B", "q4", "B", "R"]
			],
			acceptStates: [],
			criteria: "false",
			markers: []
			} |}

	(*
		Exemplo nao determinista dos slides - Aceita todas as palavras contendo um c precedido ou seguido de ab
		Este exemplo e:
			- nao determinista
			- nao entra em loop de configuracao
			- nao corre infinitamente sem repetir configuracao
			- nao tem estados useless
			- termina por estados de aceitacao
	*)
	let tm_astar6 = {| {
			kind: "turing machine",
			description: "this is an example",
			name: "tm_astar6",
			entryAlphabet: ["a", "b", "c"],
			tapeAlphabet: ["a", "b", "c", "B"],
			empty: "B",
			states: ["q1", "q2", "q3", "q4", "q5", "q6", "q7"],
			initialState: "q1",
			transitions: [
				["q1", "a", "q1", "a", "R"],
				["q1", "b", "q1", "b", "R"],
				["q1", "c", "q1", "c", "R"],

				["q1", "c", "q2", "c", "R"],
				["q1", "c", "q5", "c", "L"],

				["q2", "a", "q3", "a", "R"],

				["q3", "b", "q4", "b", "R"],

				["q5", "b", "q6", "b", "L"],

				["q6", "a", "q7", "a", "L"]
			],
			acceptStates: ["q4", "q7"],
			criteria: "true",
			markers: []
			} |}

	(*
		Primeiro exemplo original
		Este exemplo e:
			- nao determinista
			- nao entra em loop de configuracao
			- nao corre infinitamente sem repetir configuracao
			- nao tem estados useless
			- termina por estado de aceitacao
	*)
	let tm_astar7 = {| {
			kind: "turing machine",
			description: "this is an example",
			name: "tm_astar7",
			entryAlphabet: ["a", "b", "c", "d", "e"],
			tapeAlphabet: ["a", "b", "c", "d", "e", "B"],
			empty: "B",
			states: ["q1", "q2", "q3"],
			initialState: "q1",
			transitions: [
				["q1", "a", "q2", "a", "R"],

				["q1", "a", "q1", "a", "R"],
				["q1", "b", "q1", "b", "R"],
				["q1", "c", "q1", "c", "R"],
				["q1", "d", "q1", "d", "R"],
				["q1", "e", "q1", "e", "R"],

				["q2", "c", "q3", "c", "R"]
			],
			acceptStates: ["q3"],
			criteria: "true",
			markers: []
			} |}

	(*
		Segundo exemplo original
		Este exemplo e:
			- determinista
			- entra em loop de configuracao quando a palavra e vazia -> ""
			- nao corre infinitamente sem repetir configuracao
			- nao tem estados useless
			- termina por estados de aceitacao
	*)
	let tm_astar8 = {| {
			kind: "turing machine",
			description: "this is an example",
			name: "tm_astar8",
			entryAlphabet: ["a"],
			tapeAlphabet: ["a", "B"],
			empty: "B",
			states: ["q1", "q2", "q3"],
			initialState: "q1",
			transitions: [
				["q1", "B", "q2", "B", "R"],
				["q2", "B", "q1", "B", "L"],

				["q2", "a", "q3", "a", "R"]
			],
			acceptStates: ["q3"],
			criteria: "true",
			markers: []
			} |}

	(*
		Variante do exemplo 4 com estados useless
		Este exemplo e:
			- determinista
			- nao entra em loop de configuracao
			- nao corre infinitamente sem repetir configuracao
			- tem estados useless:
				- o estado q7 e unreachable e productive
				- o estado q8 e unreachable e unproductive
				- o estado q9 e reachable e unproductive
				(Os restantes sao todos reachable e productive)
			- termina por estados de aceitacao				
	*)
	let tm_astar9 = {| {
			kind: "turing machine",
			description : "this is an example",
			name: "tm_astar9",
			entryAlphabet: ["a", "b", "c"],
			tapeAlphabet: ["a", "b", "c", "X", "Y", "Z", "B"],
			empty: "B",
			states: ["q1", "q2", "q3", "q4", "q5", "q6", "q7", "q8", "q9"],
			initialState: "q1",
			transitions: [

				["q1", "B", "q6", "B", "R"],
				["q1", "Y", "q5", "Y", "R"],
				["q1", "a", "q2", "X", "R"],

				["q2", "a", "q2", "a", "R"],
				["q2", "Y", "q2", "Y", "R"],
				["q2", "b", "q3", "Y", "R"],

				["q3", "b", "q3", "b", "R"],
				["q3", "Z", "q3", "Z", "R"],
				["q3", "c", "q4", "Z", "L"],

				["q4", "Z", "q4", "Z", "L"],
				["q4", "Y", "q4", "Y", "L"],
				["q4", "b", "q4", "b", "L"],
				["q4", "a", "q4", "a", "L"],
				
				["q4", "X", "q1", "X", "R"],

				["q5", "Y", "q5", "Y", "R"],
				["q5", "Z", "q5", "Z", "R"],
				["q5", "B", "q6", "B", "R"],

				["q5", "b", "q9", "c", "R"],

				["q7", "b", "q8", "c", "R"],
				["q7", "B", "q6", "B", "R"]

			],
			acceptStates: ["q6"],
			criteria: "true"
			} |}

	(*
		Este exemplo e:
			- determinista
			- nao entra em loop de configuracao
			- corre infinitamente sem repetir configuracao
			- nao tem estados useless
			- termina por paragem
	*)
	let tm_astar10 = {| {
		kind: "turing machine",
		description: "this is an example",
		name: "tm_astar10",
		entryAlphabet: ["a", "b", "c"],
		tapeAlphabet: ["a", "b", "c", "B"],
		empty: "B",
		states: ["q1"],
		initialState: "q1",
		transitions: [
			["q1", "B", "q1", "c", "R"],
			["q1", "a", "q1", "a", "R"],
			["q1", "b", "q1", "b", "R"],
			["q1", "c", "q1", "c", "R"]
		],
		acceptStates: [],
		criteria: "false",
		markers: []
		} |}

	(*
		Este exemplo e:
			- determinista
			- entra em loop de configuracao
			- nao corre infinitamente sem repetir configuracao
			- nao tem estados useless
			- termina por paragem
	*)
	let tm_astar11 = {| {
		kind : "turing machine",
		description : "this is an example",
		name : "tm_astar11",
		entryAlphabet: ["a", "b", "c"],
		tapeAlphabet: ["a", "b", "c", "B"],
		empty: "B",
		states : ["q1", "q2", "q3"],
		initialState : "q1",
		transitions : [
			["q1", "a", "q2", "c", "R"],
			["q1", "b", "q1", "b", "R"],
			["q1", "c", "q1", "a", "R"],
			["q2", "b", "q1", "b", "L"],
			["q2", "c", "q3", "c", "R"]
		],
		acceptStates : [],
		criteria : "false",
		markers: []
		} |}
	(*
		Testar:

		method representation: t
		method representationx: tx
		method toJSon: JSon.t
		method validate: unit 
		method acceptOld(w: word): bool
		method accept (w: word): bool
		method acceptFull (w:word): bool * 'c list * 'c set list
		method generate (length: int): words 
		method reachable (s:state): states
		method productive : states
		method getUsefulStates: states
		method getUselessStates: states
		method isDeterministic: bool
		method cleanUselessStates: t
		method areAllStatesUseful: bool
		method acceptLB (w: word) : bool
		method acceptFullLB (w: word) : bool * 'c list * 'c set list
		method isLB : bool
		method convertToStopCriteria: model
		method addState (s: state) : t
		method addInitialState (s: state) : t
		method addFinalState (s: state) : t
		method removeState (s: state) : t
		method changeStateToInitial (s: state) : t
		method changeStateToFinal (s: state) : t
		method changeStateFromFinal (s: state) : t
		method renameState (s:state) (newS:state): t 
		method addTransition (trs:transition) : t
		method removeTransition (trs:transition) : t
		method downgradeModelToFiniteAutomaton: FiniteAutomaton.model

		Tipos de maquina:
		 - Determinista ou Nao
		 - Entra em loop de configuracoes ou Nao
		 - Tem estados useless ou nao
		 - Corre infinitamente sem repetir configuracao ou nao
	*)
	let print_init_msg b =
		String.concat " " ["current function:"; b]

	let check_accept f w =
		let msg = if f w then "true" else "false" in 
			Util.println [msg]

	let check_ret_bool f =
		let msg = if f then "true" else "false" in 
			Util.println [msg]

	let check_reachable f st =
		let sts : states = f st in
			Util.printStates sts

	let check_ret_states f =
		let sts : states = f in
			Util.printStates sts

	
	let test0 () =
		let tm3 = new TuringMachine.model (Arg.Text tm_astar3) in
			Util.println ["++++++++++++++++++"];
			check_accept tm3#acceptOld (word "baaa");
			check_accept tm3#accept (word "baaa");
			check_accept tm3#acceptOld (word "bab");
			check_accept tm3#accept (word "bab")
(*
	let test_representation () =
	let test_representationx () =
	let test_toJSon () =
	let test_validate () =
	let test_acceptOld () =
	let test_accept () =
	let test_acceptFull () =
	let test_generate () =
	let test_reachable () =
	let test_productive () =
	let test_getUsefulStates () =
	let test_getUselessStates () =
	let test_isDeterministic () =
	let test_cleanUselessStates () =
	let test_areAllStatesUseful () =
	let test_acceptLB () =
	let test_acceptFullLB () =
	let test_isLB () =
	let test_convertToStopCriteria () =
	let test_addState () =
	let test_addInitialState () =
	let test_addFinalState () =
	let test_removeState () =
	let test_changeStateToInitial () =
	let test_changeStateToFinal () =
	let test_changeStateFromFinal () =
	let test_renameState () =
	let test_addTransition () =
	let test_removeTransition () =
	let test_downgradeModelToFiniteAutomaton () =
*)

(*
	For the accept, we will test if it accepts a word,
	if an automata gets stuck repeating the same configuration
	or simply keeps going infinetly
*)
	
	let testAccept () =
		Util.println [print_init_msg "accept"];

		let tm3 = new TuringMachine.model (Arg.Text tm_astar3) in
		let tm5 = new TuringMachine.model (Arg.Text tm_astar5) in
		let tm10 = new TuringMachine.model (Arg.Text tm_astar10) in
		let tm11 = new TuringMachine.model (Arg.Text tm_astar11) in

			(* 
				Test accepts word / stop by acceptence
				Expeted: q3, true
			*)
			check_accept tm3#acceptOld (word "baaa");
			(* 
				Test NOT accepts word
				Expected: q1, false
			*)
			check_accept tm3#acceptOld (word "bbb");

			(* 
				Test accepts word / no accept states
				Expected: q3, true
			*)
			check_accept tm5#accept (word "aaa");
			(*
				Test NOT accepts word / no replace states (expected to be impossible)
				Expected: q1, true
			*)
			check_accept tm5#acceptOld (word "abbcc");
			(* 
				Test runs infinitely
				Expected: ~, false
			*)
			check_accept tm10#acceptOld (word "a");
			(* 
				Test get stuck in configuration loop 
				Expected: ~, false
			*)
			check_accept tm11#acceptOld (word "ab");
			(*
				Test does NOT get stuck in configuration loop
				Expected: true
			*)
			check_accept tm11#acceptOld (word "ac")

			

	let testReachable () =
		Util.println [print_init_msg "reachable"];

		let tm4 = new TuringMachine.model (Arg.Text tm_astar4) in
		let tm9 = new TuringMachine.model (Arg.Text tm_astar9) in

		 	(*
				Expected: q2, q3, q4	 
			*)
			check_reachable tm4#reachable (state "q2");
			(*
				Expected: q2, q3, q4, q5, q6, q9	 
			*)
			check_reachable tm9#reachable (state "q1");
			(*
				Expected: q7, q8, q6	 
			*)
			check_reachable tm9#reachable (state "q7")
			

	let testProductive () =
		Util.println [print_init_msg "productive"];

		let tm3 = new TuringMachine.model (Arg.Text tm_astar3) in
		let tm6 = new TuringMachine.model (Arg.Text tm_astar6) in
		let tm9 = new TuringMachine.model (Arg.Text tm_astar9) in
			(*
				Expected:	 q1,q2
			*)
			check_ret_states tm3#productive;
			(*
				Expected:	 q1,q2,q3,q4,q5
			*)
		  check_ret_states tm6#productive;
			(*
				Expected:	 q1,q2,q3,q4,q5,q7
			*)
			check_ret_states tm9#productive

	let testGetUsefulStates () =
		Util.println [print_init_msg "getUsefulStates"];

		let tm3 = new TuringMachine.model (Arg.Text tm_astar3) in
		let tm6 = new TuringMachine.model (Arg.Text tm_astar6) in
		let tm9 = new TuringMachine.model (Arg.Text tm_astar9) in

			(*
				Expected:	 q1,q2,q3
			*)
			check_ret_states tm3#getUsefulStates;
			(*
				Expected:	 q1,q2,q3,q4,q5,q6,q7
			*)
		  check_ret_states tm6#getUsefulStates;
			(*
				Expected:	 q1,q2,q3,q4,q5,q6
			*)
			check_ret_states tm9#getUsefulStates

	let testGetUselessStates () =
		Util.println [print_init_msg "getUselessStates"];

		let tm3 = new TuringMachine.model (Arg.Text tm_astar3) in
		let tm6 = new TuringMachine.model (Arg.Text tm_astar6) in
		let tm9 = new TuringMachine.model (Arg.Text tm_astar9) in

			(*
				Expected:	
			*)
			check_ret_states tm3#getUselessStates;
			(*
				Expected:	 
			*)
		  check_ret_states tm6#getUselessStates;
			(*
				Expected:	 q1,q2,q3,q4,q5,q6
			*)
			check_ret_states tm9#getUselessStates

	let testIsDeterministic () =
		Util.println [print_init_msg "isDeterministic"];

		let tmND = new TuringMachine.model (Arg.Text tm_astar6) in
		let tmD = new TuringMachine.model (Arg.Text tm_astar4) in

			(*
				Expected:	 false
			*)
			check_ret_bool tmND#isDeterministic;
			(*
				Expected:	 true
			*)
			check_ret_bool tmD#isDeterministic

	let testAreAllStatesUseful () =
		Util.println [print_init_msg "areAllStatesUseful"];

		let tm3 = new TuringMachine.model (Arg.Text tm_astar3) in
		let tm6 = new TuringMachine.model (Arg.Text tm_astar6) in
		let tm9 = new TuringMachine.model (Arg.Text tm_astar9) in

			(*
				Expected:	 true
			*)
			check_ret_bool tm3#areAllStatesUseful;
			(*
				Expected:	 true
			*)
			check_ret_bool tm6#areAllStatesUseful;
			(*
				Expected:	 false
			*)
			check_ret_bool tm9#areAllStatesUseful
		
	let testCleanUselessStates () =
		let tm = new TuringMachine.model (Arg.Text tm_astar9) in
			Util.println [print_init_msg "areAllStatesUseful"];
			let ntm = new TuringMachine.model (Arg.Representation tm#cleanUselessStates) in
				let j = ntm#toJSon in
					JSon.show j;
					Util.println []

	let runAll =
		if Util.testing active "TuringMachine" then begin
			Util.header "TuringMachineTests starting...";
			test0 ();
			(*
				testCleanUselessStates ();
				testAccept ();
				testReachable ();
				testProductive ();
				testGetUsefulStates ();
				testGetUselessStates ();
				testIsDeterministic ();
				testAreAllStatesUseful ();
				testCleanUselessStates ();
			*)
		end
end

#endif
