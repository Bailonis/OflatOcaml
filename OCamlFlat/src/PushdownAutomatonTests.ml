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
 *  Written by Carlos Freitas (cf)
 *)

(*
 * ChangeLog:
 *
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: Pushdown automata testing.
 *)

open BasicTypes

module PushdownAutomatonTests : sig end =
struct
	let active = false

	let exer_abcd = {| {
			kind : "exercise",
			description : "this is an example",
			name : "exer_abcd",
			problem : "Convert the regular expression (a+b)*(c+d) to finite automaton.",
			inside : ["abc","c","ab","b","abac"],
			outside : ["","aba","bab","abba","baab","abcd"],
			properties : []
		} |}

	let pda_astar = {| {
			kind: "pushdown automaton",
			description: "this is an example",
			name: "pda_astar",
			inputAlphabet: ["a"],
			stackAlphabet: ["a", "$"],
			states: ["START"],
			initialState: "START",
			initialStackSymbol: "$",
			transitions: [
				["START", "$", "a", "START", "$"]
			],
			acceptStates: ["START"],
			criteria: "true"
			} |}

	let test0 () =
		let pda = new PushdownAutomaton.model (Arg.Text pda_astar) in
			let j = pda#toJSon in
				JSon.show j


	let pdaReach = {| {
			kind: "pushdown automaton",
			description : "this is an example",
			name : "abc",
			inputAlphabet : ["a","b"],
			stackAlphabet: ["$"],
			states : ["S1","S2","S3","S4","S5","S6"],
			initialState : "S1",
			initialStackSymbol: "$",
			transitions : [
					["S1","$","~","S2","$"], ["S1","$","a","S3","$"],
					["S2","$","a","S2","$"],
					["S3","$","~","S4","$"],
					["S4","$","~","S5","$"],
					["S5","$","~","S3","$"], ["S5","$","~","S5","$"]
				],
			acceptStates : ["S1"],
			criteria: "true"
	} |}

	let testReachable () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaReach) in
		let start = pda#representation.initialState in
		Util.println ["Reachable states:"]; Util.printStates (pda#reachable start)

		let pdaProductive = {| {
			kind: "pushdown automaton",
			description : "this is an example",
			name : "abc",
			inputAlphabet : ["a","b"],
			stackAlphabet: ["$"],
			states : ["S1","S2","S3","S4","S5","S6"],
			initialState : "S1",
			initialStackSymbol: "$",
			transitions : [
					["S1","$","~","S2","$"], ["S1","$","a","S3","$"],
					["S2","$","a","S2","$"],
					["S3","$","~","S4","$"],
					["S4","$","~","S5","$"],
					["S5","$","~","S3","$"], ["S5","$","~","S5","$"]
				],
			acceptStates : ["S2"],
			criteria: "true"
		} |}

	let testProductive () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaProductive) in
		Util.println ["Productive states:"]; Util.printStates pda#productive

	let testGetUsefulStates () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaProductive) in
		Util.println ["Useful states:"]; Util.printStates pda#getUsefulStates

	let testGetUselessStates () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaProductive) in
		Util.println ["Useless states:"]; Util.printStates pda#getUselessStates

	let pdaEmptyStackCriteria = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pda_astar",
		inputAlphabet: ["a"],
		stackAlphabet: ["a", "$"],
		states: ["S2"],
		initialState: "S2",
		initialStackSymbol: "$",
		transitions: [
			["S2", "$", "a", "S2", "$"]
		],
		acceptStates: [],
		criteria: "false"
		} |}

	let pdaEmptyAcceptStatesCriteria = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pda_astar",
		inputAlphabet: ["a"],
		stackAlphabet: ["a", "$"],
		states: ["S2"],
		initialState: "S2",
		initialStackSymbol: "$",
		transitions: [
			["S2", "$", "a", "S2", "$"]
		],
		acceptStates: ["S2"],
		criteria: "true"
		} |}

	let testTransformToAcceptCriteria () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaEmptyStackCriteria) in
		let result: PushdownAutomaton.model = pda#transformPdaToAcceptStates in
		Util.println ["Initial PDA empty stack criteria:"];JSon.show pda#toJSon;
		Util.println ["PDA transformed to accept states criteria:"]; JSon.show (result#toJSon)

	let testTransformToEmptyStackCriteria () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaEmptyAcceptStatesCriteria) in
		let result: PushdownAutomaton.model = pda#transformPdaToAcceptEmptyStack in
		Util.println ["Initial PDA accept states criteria:"];JSon.show pda#toJSon;
		Util.println ["PDA transformed to empty stack criteria:"]; JSon.show (result#toJSon)


	let pdaNonDeterministic = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pda_astar",
		inputAlphabet: ["a"],
		stackAlphabet: ["a", "$"],
		states: ["S1"],
		initialState: "S1",
		initialStackSymbol: "$",
		transitions: [
			["S1", "$", "a", "S1", "$"],
			["S1", "$", "~", "S1", "$"]
		],
		acceptStates: ["S1"],
		criteria: "true"
		} |}

	let pdaDeterministic = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pda_astar",
		inputAlphabet: ["a", "b"],
		stackAlphabet: ["a", "$"],
		states: ["S1"],
		initialState: "S1",
		initialStackSymbol: "$",
		transitions: [
			["S1", "$", "a", "S1", "$"],
			["S1", "$", "b", "S1", "$"],
			["S1", "a", "~", "S1", "$"]
		],
		acceptStates: ["S1"],
		criteria: "true"
		} |}

	let testNotDeterministic () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaNonDeterministic) in
		let deterministic = pda#isDeterministic in
		if deterministic then
			Util.println ["automata is deterministic"] else Util.println ["automata is non-deterministic"];
		assert (not deterministic)

	let testDeterministic () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaDeterministic) in
		let deterministic = pda#isDeterministic in
		if deterministic then
			Util.println ["automata is deterministic"] else Util.println ["automata is non-deterministic"];
		assert (deterministic)

	let testIsFa () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaNonDeterministic) in
		let isFa = pda#isFiniteAutomaton in
		if isFa then
			Util.println ["automata is equivalent to FA"] else Util.println ["automata is not equivalent to FA"];
		assert (isFa)

	let testIsNotFa () =
		let pda = new PushdownAutomaton.model (Arg.Text pdaDeterministic) in
		let isFa = pda#isFiniteAutomaton in
		if isFa then
			Util.println ["automata is equivalent to FA"] else Util.println ["automata is not equivalent to FA"];
		assert (not isFa)

	let pdaAccept = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pdaAccept",
		inputAlphabet: ["a", "b"],
		stackAlphabet: ["a", "$"],
		states: ["S1", "S2"],
		initialState: "S1",
		initialStackSymbol: "$",
		transitions: [
			["S1", "$", "a", "S1", "a$"],
			["S1", "a", "a", "S1", "aa"],
			["S1", "a", "b", "S2", "a"]
		],
		acceptStates: ["S2"],
		criteria: "true"
		} |}

	let pdaAccept2 = {| {
		kind: "pushdown automaton",
		description: "this is an example",
		name: "pdaAccept2",
		inputAlphabet: ["a", "b"],
		stackAlphabet: ["a", "$"],
		states: ["S1", "S2", "S3"],
		initialState: "S1",
		initialStackSymbol: "$",
		transitions: [
			["S1", "$", "a", "S1", "a$"],
			["S1", "a", "a", "S1", "aa"],
			["S1", "a", "~", "S2", "a"],
			["S2", "a", "b", "S2", ""],
			["S2", "$", "~", "S3", "$"]
		],
		acceptStates: ["S3"],
		criteria: "true"
		} |}

	let pdaAccept3 = {| {
			kind: "pushdown automaton",
			description: "this is an example",
			name: "pdaAccept2",
			inputAlphabet: ["a", "b"],
			stackAlphabet: ["a", "$"],
			states: ["S1", "S2", "S3"],
			initialState: "S1",
			initialStackSymbol: "$",
			transitions: [
				["S1", "$", "a", "S1", "a$"],
				["S1", "a", "a", "S1", "aa"],
				["S1", "a", "~", "S2", "a"],
				["S1", "a", "~", "S1", "aa"],
				["S2", "a", "b", "S2", ""],
				["S2", "$", "~", "S3", "$"]
			],
			acceptStates: ["S3"],
			criteria: "true"
			} |}

	let testAccept() =
	let pda = new PushdownAutomaton.model (Arg.Text pdaAccept) in
	let accepted = pda#accept [symb "a"; symb "a"; symb "b"] in
		if accepted then
			Util.println ["Accepted word"] else Util.println ["Did not accept word"];
			assert (accepted)

	let testAccept2() =
		let pda = new PushdownAutomaton.model (Arg.Text pdaAccept2) in
		let accepted = pda#accept [symb "a"; symb "a"; symb "b"; symb "b"] in
			if accepted then
				Util.println ["Accepted word"] else Util.println ["Did not accept word"];
				assert (accepted)

	let testAccept3() =
		let pda = new PushdownAutomaton.model (Arg.Text pdaAccept3) in
		let accepted = pda#accept [symb "a"; symb "a"; symb "b"; symb "b"] in
			if accepted then
				Util.println ["Accepted word"] else Util.println ["Did not accept word"];
				assert (accepted)

	let testGenerate() =
		let pda = new PushdownAutomaton.model (Arg.Text pdaAccept2) in
		let words = pda#generate 6 in
			Util.println ["Generated words:"];
			Util.printWords words

	let testSearchTree() =
		let pda = new PushdownAutomaton.model (Arg.Text pdaAccept3) in
		let searchTree = pda#getSearchTree [symb "a"; symb "b"] in
			PushdownAutomatonPrivate.printSearchTree searchTree

	let runAll =
		if Util.testing active "PushdownAutomaton" then begin
			Util.header "PushdownAutomatonTests starting...";
			test0 ();
			testReachable ();
			testProductive ();
			testGetUsefulStates ();
			testGetUselessStates ();
			testTransformToAcceptCriteria ();
			testTransformToEmptyStackCriteria ();
			testNotDeterministic ();
			testDeterministic ();
			testIsFa ();
			testIsNotFa ();
			testAccept ();
			testAccept2 ();
			testAccept3 ();
			testGenerate ();
			testSearchTree()
		end
end

#endif
