(*
 * FiniteAutomatonTests.ml
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
 * Description: Finite automata testing.
 *)

open BasicTypes

module FiniteAutomatonTests : sig end =
struct
	open FiniteAutomaton

	let active = false


	let test0 () =
		let fa = new FiniteAutomaton.model (Arg.Predef "fa_abc") in
			let j = fa#toJSon in
				JSon.show j

	let testBug () =
		let fa = new FiniteAutomaton.model (Arg.Predef "fa_abc") in
		let fa2 = fa#toDeterministic in
			let j = fa2#toJSon in
				JSon.show j;
		let fa3 = fa2#cleanUselessStates in
			let j = fa3#toJSon in
				JSon.show j

	let testBug2 () =
		let fa = new FiniteAutomaton.model (Arg.Predef "fa_abc") in
		let fa2 = fa#toDeterministic in
			Util.println ["productive states:"];
			Util.printStates fa2#productive;
			Util.println []

	let faAccept = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "ab123",
		alphabet : ["a", "b"],
		states : ["1", "2", "3"],
		initialState : "1",
		transitions : [
				["1","a","2"], ["1","b","3"],
				["2","b","2"],
				["3","a","3"]
			],
		acceptStates : ["2", "3"]
	} |}

	let faAccept2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b", "c", "d"],
		states : ["START", "A", "AB", "C", "SUCCESS", "D"],
		initialState : "START",
		transitions : [
				["START","a","A"], ["START","~","AB"],
				["A","~","C"],
				["AB","b","SUCCESS"], ["AB","~","SUCCESS"],
				["C","~","SUCCESS"], ["C","d","C"],
				["SUCCESS","~","START"]
			],
		acceptStates : ["SUCCESS"]
	} |}

	let check f w =
		let msg = 
			if f w then "word was accepted" else "word was not accepted"
		in Util.println [msg]

	let testAcceptBF () =
		let fa = new FiniteAutomaton.model (Arg.Text faAccept) in
			check fa#acceptBreadthFirst [];
			check fa#acceptBreadthFirst (word "a");
			check fa#acceptBreadthFirst (word "ab");
			check fa#acceptBreadthFirst (word "b");
			check fa#acceptBreadthFirst (word "ba");
			check fa#acceptBreadthFirst (word "abb");
			check fa#acceptBreadthFirst (word "aba");
			check fa#acceptBreadthFirst (word "baa");
			check fa#acceptBreadthFirst (word "bab");
			Util.println []

	let testAcceptBF2 () =
		let fa = new FiniteAutomaton.model (Arg.Text faAccept2) in
			check fa#acceptBreadthFirst [];
			check fa#acceptBreadthFirst (word "a");
			check fa#acceptBreadthFirst (word "ad");
			check fa#acceptBreadthFirst (word "abad");
			check fa#acceptBreadthFirst (word "c");
			Util.println []

	let testAccept () =
		let fa = new FiniteAutomaton.model (Arg.Text faAccept) in
			check fa#accept [];
			check fa#accept (word "a");
			check fa#accept (word "ab");
			check fa#accept (word "b");
			check fa#accept (word "ba");
			check fa#accept (word "abb");
			check fa#accept (word "aba");
			check fa#accept (word "baa");
			check fa#accept (word "bab");
			Util.println []

	let testAccept2 () =
		let fa = new FiniteAutomaton.model (Arg.Text faAccept2) in
			check fa#accept [];
			check fa#accept (word "a");
			check fa#accept (word "ad");
			check fa#accept (word "abad");
			check fa#accept (word "c");
			Util.println []

	let testAccTrace () =
		let fa = new FiniteAutomaton.model (Arg.Predef "fa_abc") in
			fa#acceptWithTracing (word "abe")

	let faGenerate = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","b","S2"], ["S1","a","S3"], ["S1","~","S3"],
				["S2","~","S3"],
				["S3","~","S3"]
			],
		acceptStates : ["S3"]
	} |}

	let faGenerate2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1", "S2"],
		initialState : "S1",
		transitions : [
				["S1","a","S1"], ["S1","b","S2"],
				["S2","a","S2"], ["S2","b","S1"]

			],
		acceptStates : ["S2"]
	} |}

	let faGenerate3 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a"],
		states : ["S1"],
		initialState : "S1",
		transitions : [
				["S1","a","S1"]
			],
		acceptStates : ["S1"]
	} |}

	let faGenerate4 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a","b"],
		states : ["S1","S2"],
		initialState : "S1",
		transitions : [
				["S1","a","S1"], ["S1","b","S2"],
				["S2","a","S2"]
			],
		acceptStates : ["S1"]
	} |}

	let testGenerate () =
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate) in
			Util.println ["generated words size 0:"]; Util.printWords (fa#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (fa#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (fa#generate 2);
			Util.println ["generated words size 100:"]; Util.printWords (fa#generate 100);
			Util.println []

	let testGenerate2 () =
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate2) in
			Util.println ["generated words size 0:"]; Util.printWords (fa#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (fa#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (fa#generate 2);
			Util.println ["generated words size 3:"]; Util.printWords (fa#generate 3);
			Util.println ["generated words size 4:"]; Util.printWords (fa#generate 4);
			Util.println ["generated words size 18:"]; Util.printWords (fa#generate 18);

			Util.println []

	let testGenerate3 () =
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate3) in
			Util.println ["generated words size 0:"]; Util.printWords (fa#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (fa#generate 1);
			Util.println ["generated words size 10:"]; Util.printWords (fa#generate 10);
			Util.println ["generated words size 50:"]; Util.printWords (fa#generate 50);
			Util.println ["generated words size 100:"]; Util.printWords (fa#generate 100);
			Util.println ["generated words size 1000:"]; Util.printWords (fa#generate 1000);
			Util.println []

	let testGenerate4 () =
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate4) in
			Util.println ["generated words size 0:"]; Util.printWords (fa#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (fa#generate 1);
			Util.println ["generated words size 10:"]; Util.printWords (fa#generate 10);
			Util.println ["generated words size 100:"]; Util.printWords (fa#generate 100);
			Util.println []

	let testGenerateUntil () =
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate) in
			Util.println ["generated words size 5:"]; Util.printWords (fa#generateUntil 5);
			Util.println [];
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate2) in
			Util.println ["generated words size 5:"]; Util.printWords (fa#generateUntil 5);
			Util.println [];
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate3) in
			Util.println ["generated words size 5:"]; Util.printWords (fa#generateUntil 5);
			Util.println [];
		let fa = new FiniteAutomaton.model (Arg.Text faGenerate4) in
			Util.println ["generated words size 5:"]; Util.printWords (fa#generateUntil 5);
			Util.println []

	let faReach = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3"],
		initialState : "S1",
		transitions : [
			],
		acceptStates : ["S1"]
	} |}

	let faReach2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a","b"],
		states : ["S1","S2","S3","S4","S5","S6"],
		initialState : "S1",
		transitions : [
				["S1","~","S2"], ["S1","a","S3"],
				["S2","a","S2"],
				["S3","~","S4"],
				["S4","~","S5"],
				["S5","~","S3"], ["S5","b","S6"], ["S5","~","S5"]
			],
		acceptStates : ["S1"]
	} |}

	let testReachable () =
			let open FiniteAutomaton in
			let fa = new FiniteAutomaton.model (Arg.Text faReach) in
			let fa2 = new FiniteAutomaton.model (Arg.Text faReach2) in
			let start = fa#representation.initialState in
			let start2 = fa2#representation.initialState in
				Util.println ["reachable states:"]; Util.printStates (fa#reachable start); Util.println [];
				Util.println ["reachable states:"]; Util.printStates (fa#reachable start2); Util.println []

	let faProductive = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1","S2","S3","S4"],
		initialState : "S1",
		transitions : [
				["S1","a","S2"], ["S1","b","S3"],
				["S4","a","S2"], ["S4","b","S3"], ["S3","a","S3"]
			],
		acceptStates : ["S4"]
	} |}

	let faProductive2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1","S2","S3","S4","S5","S6","S7"],
		initialState : "S1",
		transitions : [
				["S1","~","S2"], ["S1","a","S2"], ["S1","~","S3"], ["S1","a","S3"], ["S1","~","S5"], ["S1","a","S5"],
				["S2","~","S1"], ["S2","a","S1"],
				["S4","~","S3"], ["S4","a","S3"],["S4","~","S4"], ["S4","a","S4"],
				["S5","~","S2"], ["S5","a","S2"],["S5","~","S6"], ["S5","a","S6"],
				["S6","~","S6"], ["S6","a","S6"],["S6","~","S7"], ["S6","a","S7"],
				["S7","~","S3"], ["S7","a","S3"],["S7","~","S5"], ["S7","a","S5"]
			],
		acceptStates : ["S2","S4"]
	} |}

	let testProductive () =
		let fa = new FiniteAutomaton.model (Arg.Text faProductive) in
		let fa2 = new FiniteAutomaton.model (Arg.Text faProductive2) in
			Util.println ["productive states:"]; Util.printStates fa#productive; Util.println [];
			Util.println ["productive states:"]; Util.printStates fa2#productive; Util.println []


	let faClean = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1","S2","S3","S4"],
		initialState : "S1",
		transitions : [
				["S1","a","S2"], ["S1","b","S3"],
				["S4","a","S2"], ["S4","b","S3"], ["S3","a","S3"]
			],
		acceptStates : ["S4"]
	} |}

	let faClean2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1","S2","S3","S4"],
		initialState : "S1",
		transitions : [
				["S1","a","S2"], ["S1","~","S3"],
				["S3","a","S2"], ["S3","~","S1"], ["S3","a","S4"]
			],
		acceptStates : ["S2"]
	} |}

	let testClean () =
		let fa = new FiniteAutomaton.model (Arg.Text faClean) in
		let fa2 = new FiniteAutomaton.model (Arg.Text faClean2) in
		let mfa = fa#cleanUselessStates in
		let mfa2 = fa2#cleanUselessStates in
		let j = mfa#toJSon in
		let j2 = mfa2#toJSon in
			JSon.show j; Util.println [];
			JSon.show j2; Util.println []

	let faIsDeter = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "isDeter",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","~","S2"], ["S1","a","S3"],
				["S2","a","S3"], ["S2","b","S2"]
			],
		acceptStates : ["S3"]
	} |}

	let faIsDeter2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "isDeter",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","~","S2"], ["S1","b","S3"],
				["S2","a","S4"], ["S4","b","S5"],
				["S3","b","S5"]
			],
		acceptStates : ["S5"]
	} |}

	let faIsDeter3 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "isDeter",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","a","S2"], ["S1","a","S3"],
				["S2","b","S4"],
				["S3","b","S4"]
			],
		acceptStates : ["S4"]
	} |}

	let faToDeter = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["0", "1"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","1","S2"], ["S1","1","S3"] , ["S1","0","S5"],
				["S2","~","S4"],
				["S4","0","S3"],
				["S5","1","S2"], ["S5","0","S3"], ["S5","0","S4"]
			],
		acceptStates : ["S3"]
	} |}

	let testIsDeterministic () =
		let fa = new FiniteAutomaton.model (Arg.Text faIsDeter) in
		let fa2 = new FiniteAutomaton.model (Arg.Text faIsDeter2) in
		let fa3 = new FiniteAutomaton.model (Arg.Text faIsDeter3) in
			if fa#isDeterministic then
				Util.println ["automata is deterministic"] else Util.println ["automata is non-deterministic"];
		if fa2#isDeterministic then
				Util.println ["automata is deterministic"] else Util.println ["automata is non-deterministic"];
			if fa3#isDeterministic then
				Util.println ["automata is deterministic"] else Util.println ["automata is non-deterministic"]



	let testToDeterministic () =
		let fa = new FiniteAutomaton.model (Arg.Text faToDeter) in
		let mfa = fa#toDeterministic in
		let j = mfa#toJSon in
			JSon.show j;
		let fa = new FiniteAutomaton.model (Arg.Text faIsDeter) in
		let mfa = fa#toDeterministic in
		let j = mfa#toJSon in
			JSon.show j


	let testEquivalence () =
		let fa = new FiniteAutomaton.model (Arg.Predef "fa_abc") in
		let s = fa#equivalencePartition in
			Set.iter (fun s -> Util.print ["set: "]; Util.printStates s) s


	let faMinimize = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b"],
		states : ["S1", "S2", "S3", "S4", "S5"],
		initialState : "S1",
		transitions : [
				["S1","a","S2"], ["S1","b","S3"],
				["S2","b","S4"], ["S2","a","S3"],
				["S3","a","S2"], ["S3","b","S4"],
				["S4","b","S3"], ["S4","a","S2"],
				["S4","a","S5"]
			],
		acceptStates : ["S4"]
	} |}

	let faMinimize2 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "min",
		alphabet : ["i", "c", "1", "2"],
		states : ["S01", "S02", "S03", "S04", "S05",
				"S06", "S07", "S08", "S09", "S10"],
		initialState : "S01",
		transitions : [
				["S01","i","S02"],
				["S02","1","S03"], ["S02","i","S02"],
				["S03","1","S04"], ["S03","i","S04"],
				["S04","1","S03"], ["S04","2","S05"], ["S04","i","S04"],
				["S05","i","S06"], ["S05","c","S07"],
				["S06","i","S06"], ["S06","1","S03"],
				["S07","1","S04"], ["S07","i","S08"],
				["S08","i","S08"], ["S08","1","S03"], ["S08","2","S09"],
				["S09","c","S03"], ["S09","i","S10"],
				["S10","1","S03"], ["S10","i","S10"]
			],
		acceptStates : ["S10"]
	} |}

	let faMinimize3 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["a", "b","c"],
		states : ["S0","S1", "S2", "S3", "S4", "S5"],
		initialState : "S0",
		transitions : [
				["S0","a","S1"], ["S0","b","S2"],
				["S1","b","S0"], ["S1","a","S1"], ["S1","c","S4"],
				["S2","b","S0"], ["S2","a","S2"], ["S2","c","S5"],
				["S3","b","S1"], ["S3","a","S3"], ["S3","c","S4"],
				["S4","b","S5"],
				["S5","b","S4"]
			],
		acceptStates : ["S4","S5"]
	} |}

	let faMinimize4 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["0", "1"],
		states : ["00","01", "10", "11"],
		initialState : "00",
		transitions : [
				["00","1","01"], ["00","0","10"],
				["01","1","00"], ["01","0","11"],
				["10","0","00"], ["10","1","11"],
				["11","1","10"], ["11","0","01"]
			],
		acceptStates : ["01"]
	} |}

	let testMinimize () =
		let fa = new FiniteAutomaton.model (Arg.Text faMinimize) in
		let mfa = fa#minimize in
		let j = mfa#toJSon in
			JSon.show j

	let testMinimize2 () =
		let fa = new FiniteAutomaton.model (Arg.Text faMinimize2) in
		let mfa = fa#minimize in
		let j = mfa#toJSon in
			JSon.show j

	let testMinimize3 () =
		let fa = new FiniteAutomaton.model (Arg.Text faMinimize3) in
		let mfa = fa#minimize in
		let j = mfa#toJSon in
			JSon.show j

	let testMinimize4 () =
		let fa = new FiniteAutomaton.model (Arg.Text faMinimize4) in
		let mfa = fa#minimize in
		let j = mfa#toJSon in
			JSon.show j
			
	let testExercice () =
		let e = new Exercise.exercise (Arg.Predef "exer_astar_fa") in
		let fa = new FiniteAutomaton.model (Arg.Predef "dfa_astar") in
		let (ins,outs,props) = fa#checkExerciseFailures e in
			e#show2;
			fa#show2;
			Exercise.showRes (ins,outs,props)

	let faMinimize4 = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "abc",
		alphabet : ["0", "1"],
		states : ["00","01", "10", "11"],
		initialState : "00",
		transitions : [
				["00","1","01"], ["00","0","10"],
				["01","1","00"], ["01","0","11"],
				["10","0","00"], ["10","1","11"],
				["11","1","10"], ["11","0","01"]
			],
		acceptStates : ["01"]
	} |}

	let runAll =
		if Util.testing active "FiniteAutomaton" then begin
			Util.sep (); test0 ();


(*
			
			Util.sep (); testExercice ();
			Util.sep (); testBug ();
			Util.sep (); testBug2 ();
			Util.sep (); testAcceptBF ();
			Util.sep (); testAcceptBF2 ();
			Util.sep (); testAccept ();
			Util.sep (); testAccept2 ();
			Util.sep (); testAccTrace () *)
		end
end

