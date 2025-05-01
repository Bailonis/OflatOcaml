(*
 * Examples.ml
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
 * dec/2020 (amd) - Collected the examples in a single module.
 * sep/2019 (jg) - Initial version, each example in an individual file.
 *)

(*
 * Description: A set of good predefined examples.
 *
 * TODO: Check if these examples are really good and improve.
 *)

module type ExamplesSig =
sig
	val examples : string list
	val example : string -> string
	val jsonExample : string -> JSon.t
	val see : string -> unit
end

module Examples : ExamplesSig =
struct
(* FA examples *)
	let dfa_1 = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "dfa_1",
			alphabet: ["a", "b"],
			states : ["START", "A", "B", "C"],
			initialState : "START",
			transitions : [
					["START", "a", "A"], ["A", "b", "B"], ["B", "a", "C"], ["C", "b", "B"],
					["C", "a", "A"]
				],
			acceptStates : ["START", "B", "C"]
		} |}

	let dfa_2 = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "dfa_2",
			alphabet: ["0", "1"],
			states : ["START", "1", "2", "3"],
			initialState : "START",
			transitions : [
				["START", "1", "1"], ["1", "1", "START"], ["1", "0", "2"], ["2", "0", "1"],
				["2", "1", "3"], ["3", "1", "2"], ["3", "0", "START"], ["START", "0", "3"]
			],
			acceptStates : ["1"]
			} |}

	let dfa_astar = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "dfa_astar",
			alphabet: ["a"],
			states : ["START"],
			initialState : "START",
			transitions : [
				["START", "a", "START"]
			],
			acceptStates : ["START"]
			} |}

	let fa_abc = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "fa_abc",
			alphabet : ["a", "b", "c", "d"],
			states : ["START", "A", "AB", "SUCCESS"],
			initialState : "START",
			transitions : [
					["START","a","A"], ["START","b","START"], ["START","c","START"], ["START","d","START"],
					["A","a","A"], ["A","b","AB"], ["A","c","START"], ["A","d","START"],
					["AB","a","A"], ["AB","b","START"], ["AB","c","SUCCESS"], ["AB","d","START"],
					["SUCCESS","a","SUCCESS"], ["SUCCESS","b","SUCCESS"], ["SUCCESS","c","SUCCESS"], ["SUCCESS","d","SUCCESS"]
				],
			acceptStates : ["SUCCESS"]
		} |}

	let fa_error = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "fa_error",
			alphabet : ["a"],
			states : ["A"],
			initialState : "START",
			transitions : [],
			acceptStates : ["SUCCESS"]
		} |}

	let nfa_1 = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "nfa_1",
			alphabet: ["a", "b"],
			states : ["START", "A", "B"],
			initialState : "START",
			transitions : [
					["START", "a", "A"], ["A", "b", "B"], ["A", "b", "START"], ["B", "a", "START"]
				],
			acceptStates : ["START"]
			} |}

	let nfa_2 = {| {
			kind : "finite automaton",
			description : "this is an example",
			name : "nfa_2",
			alphabet : ["a", "b", "c", "d", "e"],
			states : ["START", "A", "AB", "SUCCESS", "UNREACHABLE", "UNPRODUCTIVE"],
			initialState : "START",
			transitions : [
					["START","a","A"], ["START","b","START"], ["START","c","START"], ["START","d","START"],
					["A","a","A"], ["A","b","AB"], ["A","c","START"], ["A","d","START"],
					["AB","a","A"], ["AB","b","START"], ["AB","c","SUCCESS"], ["AB","d","START"],
					["SUCCESS","a","SUCCESS"], ["SUCCESS","b","SUCCESS"], ["SUCCESS","c","SUCCESS"], ["SUCCESS","d","SUCCESS"], ["A","a","AB"], ["UNREACHABLE", "a", "SUCCESS"],
					["SUCCESS", "e", "UNPRODUCTIVE"], ["UNPRODUCTIVE", "a", "UNPRODUCTIVE"]
				],
			acceptStates : ["SUCCESS"]
		} |}

(* RE examples *)
	let re_abc = {| {
			kind : "regular expression",
			description : "this is an example",
			name : "re_abc",
			re : "((a+b)*(cd)*)*"
		} |}

	let re_complex = {| {
			kind : "regular expression",
			description : "this is a complex example",
			name : "re_complex",
			re : "(a+(b(c+d)+ea))*f*g"
		} |}

	let re_convoluted = {| {
			kind : "regular expression",
			description : "this is a convoluted example",
			name : "re_convoluted",
			re : "((((a+b)*(cd)*)*+(e(f+gh*i)*jk)*+lmn)op+q)"
		} |}

	let re_simple = {| {
			kind : "regular expression",
			description : "this is a simple example",
			name : "re_simple",
			re : "a+a*+bc*"
		} |}

	let re_astar = {| {
			kind : "regular expression",
			description : "this is a simple example",
			name : "re_astar",
			re : "a*"
		} |}

(* FE examples *)
	let fe_colors = {| {
		kind : "finite enumeration",
		description : "this is an example",
		name : "fe_colors",
		words : ["Red", "Yellow", "Blue"]
	} |}

(* CFG examples *)
	let cfg_simple = {| {
			kind : "context free grammar",
			description : "this is an example",
			name : "cfg_simple",
			alphabet : ["0", "1"],
			variables : ["S", "P"],
			initial : "S",
			rules : [	"S -> 1S0 | P",
						"P -> 0P1 | ~" ]
		} |}
		
	let cfg_balanced = {| {
			kind : "context free grammar",
			description : "CFG: Language of balanced square bracket parentheses",
			name : "cfg_balanced",
			alphabet : ["[", "]"],
			variables : ["S"],
			initial : "S",
			rules : [ "S -> [S] | SS | ~"]
		} |}

(* LL parsing *)

	let cfg_ll_thesis_g1 = {| {
			kind : "context free grammar",
			description : "Grammar G1 from thesis document",
			name : "cfg_ll_thesis_g1",
			alphabet : ["a", "b", "c"],
			variables : ["A", "B", "C", "S"],
			initial : "S",
			rules : ["A -> a", "A -> aAB", "B -> Bb", "B -> C", "C -> c", "S -> ABC"]
		} |}

	let cfg_ll_thesis_g2 = {| {
			kind : "context free grammar",
			description : "Grammar G2 from thesis document",
			name : "cfg_ll_thesis_g2",
			alphabet : ["a", "b", "c"],
			variables : ["A", "B", "C", "D", "E", "S"],
			initial : "S",
			rules : ["A -> aD", "B -> CE", "C -> c", "D -> ", "D -> AB", "E -> ", "E -> bE", "S -> ABC"]
	} |}

	let cfg_ll_1 = {| {
			kind : "context free grammar",
			description : "Example from old pratical classes",
			name : "cfg_ll_1",
			alphabet : ["(", ")", "*", "+", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9"],
			variables : ["D", "E", "F", "I", "S", "T", "X", "Y", "Z"],
			initial : "S",
			rules : ["D -> 0", "D -> 1", "D -> 2", "D -> 3", "D -> 4", "D -> 5", "D -> 6", "D -> 7", "D -> 8", "D -> 9", "E -> TX", "F -> (E)", "F -> I", "I -> DZ", "S -> E", "T -> FY", "X -> ", "X -> +TX", "Y -> ", "Y -> *FY", "Z -> ", "Z -> DZ"]
		} |}

	let cfg_ll_2 = {| {
			kind : "context free grammar",
			description : "classic grammar",
			name : "cfg_ll_2",
			alphabet : ["*", "+", "0", "1"],
			variables : ["D", "E"],
			initial : "E",
			rules : ["D -> 0", "D -> 1", "E -> D", "E -> E*E", "E -> E+E"]
		} |}

	let cfg_ll_3 = {| {
			kind : "context free grammar",
			description : "_",
			name : "cfg_ll_3",
			alphabet : ["(", ")", "*", "+", "i"],
			variables : ["E", "F", "T"],
			initial : "E",
			rules : ["E -> E+T", "E -> T", "F -> (E)", "F -> i", "T -> F", "T -> T*F"]
		} |}

	let cfg_ll_4 = {| {
			kind : "context free grammar",
			description : "_",
			name : "cfg_ll_4",
			alphabet : ["a", "b", "d", "g", "h"],
			variables : ["A", "B", "C", "S"],
			initial : "S",
			rules : ["A -> BC", "A -> da", "B -> ", "B -> g", "C -> ", "C -> h", "S -> ACB", "S -> Ba", "S -> CbB"]
		} |}

	let cfg_ll_5 = {| {
			kind : "context free grammar",
			description : "_",
			name : "cfg_ll_5",
			alphabet : ["a", "b", "c", "d", "e"],
			variables : ["A", "B", "C", "D", "E", "S"],
			initial : "S",
			rules : ["A -> ", "A -> a", "B -> ", "B -> b", "C -> c", "D -> ", "D -> d", "E -> ", "E -> e", "S -> ABCDE"]	
		} |}

	let cfg_ll_6 = {| {
			kind : "context free grammar",
			description : "Exemplo 9",
			name : "cfg_ll_6",
			alphabet : ["a", "b"],
			variables : ["A", "B", "C", "N"],
			initial : "N",
			rules : ["A -> CAC", "A -> a", "B -> CBC", "B -> b", "C -> a", "C -> b", "N -> AB", "N -> BA"]	
		} |}

(* LR parsing *)
	let cfg_lr0_thesis = {| {
			kind : "context free grammar",
			description : "This is an example for LR0",
			name : "cfg_lr0_thesis",
			alphabet : ["a", "b", "$"],
			variables : ["S", "X", "A"],
			initial : "S",
			rules : [	"S -> X$",
						"X -> XA | A",
						"A -> aXb | ab" ]
		} |}
		
	let cfg_slr1 = {| {
			kind : "context free grammar",
			description : "This is another example for SLR1",
			name : "cfg_slr1",
			alphabet : ["a", "c", "d","z", "$"],
			variables : ["T", "S","A","B"],
			initial : "T",
			rules : [	"T -> S$",
						"S -> aAc | aBd",
						"A -> z",
						"B -> z"]
		} |}
		
	let cfg_lr0_thesis = {| {
			kind : "context free grammar",
			description : "This is the example for LR0 in the thesis",
			name : "cfg_lr0_thesis",
			alphabet : ["a", "b", "$"],
			variables : ["S", "X", "A"],
			initial : "S",
			rules : [	"S -> X$",
						"X -> XA | A",
						"A -> aXb | ab" ]
		} |}
		
	let cfg_slr1_thesis = {| {
			kind : "context free grammar",
			description : "This is the example for SLR1 in the thesis",
			name : "cfg_slr1_thesis",
			alphabet : ["$","a", "b", "c"],
			variables : ["T", "S", "A", "B", "C"],
			initial : "T",
			rules : [	"T -> S$",
						"S -> aBbA | aA",
						"A -> b | ~",
						"B -> b | bC",
						"C -> c" ]
		} |}
		
	let cfg_lr1_thesis = {| {
			kind : "context free grammar",
			description : "This is the example for LR1 in the thesis",
			name : "cfg_lr1_thesis",
			alphabet : ["a", "c", "d", "z", "$"],
			variables : ["S", "X", "A", "B"],
			initial : "S",
			rules : [	"S -> X$",
						"X -> aAc | aBd | Bc",
						"A -> z",
						"B -> z"]
		} |}
		
	let cfg_lalr1_thesis = {| {
			kind : "context free grammar",
			description : "This is the example for LALR1 in the thesis",
			name : "cfg_lalr1_thesis",
			alphabet : ["c", "d", "$"],
			variables : ["S", "X","C"],
			initial : "S",
			rules : [	"S -> X$",
						"X -> CC",
						"C -> cC | d"]
		} |}
		
	let cfg_onlylr1 = {| {
			kind : "context free grammar",
			description : "This is an example for a LR1-only grammar",
			name : "cfg_onlylr1",
			alphabet : ["$", "a", "c", "d", "b", "z"],
			variables : ["S", "X", "A", "B"],
			initial : "S",
			rules : ["S -> X$", "X -> aAc", "X -> aBd", "X -> bA", "X -> bBc", "A -> z", "B -> z"]
		} |}
		
	let cfg_notlr1 = {| {
			kind : "context free grammar",
			description : "This is an example for an LR2 Grammar, so it should return 'It's not LR1'",
			name : "cfg_notlr1",
			alphabet : ["a", "c", "d", "z", "$"],
			variables : ["S", "X", "A", "B"],
			initial : "S",
			rules : [	"S -> X$",
						"X -> aAc | aBcd",
						"A -> z",
						"B -> z"]
		} |}			

(* UG examples *)
	let ug_simple = {| {
			kind : "grammar",
			description : "this is an example",
			name : "ug_simple",
			alphabet : ["0", "1"],
			variables : ["S", "P"],
			initial : "S",
			rules : [	"S -> 1S0 | P",
						"1P0 -> 0P1 | ~" ]
		} |}
		

(* Pushdown Automata *)
	let pda_WW_1 = {| {
			kind: "pushdown automaton",
			description : "this is an example",
			name : "pda_WW-1",
			inputAlphabet : ["a","b"],
			stackAlphabet: ["z","a","b"],
			states : ["S1","S2","S3","S4"],
			initialState : "S1",
			initialStackSymbol: "z",
			transitions : [
					["S1","z","a","S2","az"], 
					["S1","z","b","S2","bz"],
					["S2","a","a","S2","aa"],
					["S2","a","a","S3",""],
					["S2","a","b","S2","ba"],
					["S2","b","a","S2","ab"],
					["S2","b","b","S2","bb"],
					["S2","b","b","S3",""],
					["S3","a","a","S3",""],
					["S3","b","b","S3",""],
					["S3","z","~","S4","z"]
				],
			acceptStates : ["S1","S4"],
			criteria: "true"
		} |}

	let pda_AABB = {| {
			kind: "pushdown automaton",
			description: "this is an example",
			name: "pda_AABB",
			inputAlphabet: ["a", "b"],
			stackAlphabet: ["a", "z"],
			states: ["S1", "S2", "S3"],
			initialState: "S1",
			initialStackSymbol: "z",
			transitions: [
				["S1", "z", "a", "S1", "az"],
				["S1", "a", "a", "S1", "aa"],
				["S1", "a", "~", "S2", "a"],
				["S2", "a", "b", "S2", ""],
				["S2", "z", "~", "S3", "z"]
			],
			acceptStates: ["S3"],
			criteria: "true"
		} |}

		let pda_Explode = {| {
			kind : "pushdown automaton",
			description : "_",
			name : "pda_Explode",
			inputAlphabet : ["a"],
			stackAlphabet : ["a", "b", "z"],
			states : ["START", "A"],
			initialState : "START",
			initialStackSymbol : "z",
			transitions : [
				["START", "z", "a", "START", "az"],
				["START", "a", "a", "START", "aa"],
				["A", "a", "a", "A", "bb"],
				["A", "b", "a", "A", "aa"],
				["START", "a", "a", "A", "a"],
				["START", "a", "a", "A", "b"],
				["A", "a", "a", "START", "ab"]
			],
			acceptStates : [],
			criteria : "true"
		} |}
		
(* Turing Machine *)

   (* AMD multifita test *)
	let tm_translate_lb = {| {
		kind: "turing machine",
		description: "this is an example",
		name: "tm_translate_lb",
		entryAlphabet: ["a", "b", "[", "]"],
		tapeAlphabet: ["a", "b", "B", "[", "]"],
		empty: "B",
		states: ["q1", "q2"],
		initialState: "q1",
		transitions: [
			["q1", ["a", "B"], "q1", ["b", "B"], ["R", "R"]],
			["q1", ["b", "B"], "q1", ["a", "B"], ["R", "R"]],
			["q1", ["B", "B"], "q2", ["B", "B"], ["L", "L"]],
			["q2", ["a", "B"], "q2", ["a", "B"], ["L", "L"]],
			["q2", ["b", "B"], "q2", ["b", "B"], ["L", "L"]]
		],
		acceptStates: [],
		criteria: "false",
		markers: ["[", "]"]
		} |}


   (* AMD multifita test *)
	let tm_translate = {| {
		kind: "turing machine",
		description: "this is an example",
		name: "tm_translate",
		entryAlphabet: ["a", "b"],
		tapeAlphabet: ["a", "b", "B"],
		empty: "B",
		states: ["q1", "q2"],
		initialState: "q1",
		transitions: [
			["q1", ["a", "B"], "q1", ["b", "B"], ["R", "L"]],
			["q1", ["b", "B"], "q1", ["a", "B"], ["R", "L"]],
			["q1", ["B", "B"], "q2", ["B", "B"], ["L", "L"]],
			["q2", ["a", "B"], "q2", ["a", "B"], ["L", "L"]],
			["q2", ["b", "B"], "q2", ["b", "B"], ["L", "L"]]
		],
		acceptStates: [],
		criteria: "false"
		} |}

	let tm_astar1 = {| {
		kind: "turing machine",
		description: "this is an example",
		name: "tm_astar1",
		entryAlphabet: ["a", "b"],
		tapeAlphabet: ["a", "b", "B"],
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
		markers: []
		} |}

	
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
		lbMarkers: []
		} |}

	let tm_astar3 = {| {
			kind: "turing machine",
			description: "this is an example changed",
			name: "tm_astar3",
			entryAlphabet: ["a", "b"],
			tapeAlphabet: ["a", "b", "B"],
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
			lbMarkers: []
			} |}

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
			lbMarkers: []
			} |}

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
			lbMarkers: []
			} |}

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
			lbMarkers: []
			} |}

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
			lbMarkers: []
			} |}

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
			lbMarkers: []
			} |}

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
			criteria: "true",
			lbMarkers: []
		} |}

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
		lbMarkers: []
		} |}

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
		lbMarkers: []
		} |}


(* Composition *)
	let comp_abc = {| {
			kind : "composition",
			description : "this is an example",
			name : "comp_abc",
			comp : "[tm_astar11]^[tm_astar11]"
	} |}


(* Exercises *)
	let exer_balanced_cfg = {| {
			kind : "exercise",
			description : "CFG: Create a CONTEXT FREE GRAMMAR that generates the language of balanced square bracket parentheses",
			name : "exer_balanced_cfg",
			problem : "CFG for the language of balanced parentheses",
			inside : ["","[]","[[]]","[][]","[[][][][[]]][]"],
			outside : ["[","][","[[]","[[]]]"],
			properties : ["context free grammar"]
		} |}

	let exer_astar_fa = {| {
			kind : "exercise",
			description : "FA: all sequences of 'a's",
			name : "exer_astar_fa",
			problem : "Create a deterministic FINITE AUTOMATON that recognizes all sequences of 'a's",
			inside : ["","a","aa","aaa","aaaaaaa"],
			outside : ["d","b","ava"],
			properties : ["finite automaton", "deterministic"]
		} |}

	let exer_astar_re = {| {
			kind : "exercise",
			description : "RE: all sequences of 'a's",
			name : "exer_astar_re",
			problem : "Create a REGULAR EXPRESSION that generates all sequences of 'a's",
			inside : ["","a","aa","aaa","aaaaaaa"],
			outside : ["d","b","ava"],
			properties : ["regular expression"]
		} |}

	let exer_abcd = {| {
			kind : "exercise",
			description : "this is an example",
			name : "exer_abcd",
			problem : "Convert the regular expression (a+b)*(c+d) to finite automaton.",
			inside : ["abc","c","abd","d","abac"],
			outside : ["","aba","bab","abba","baab","abcd"],
			properties : ["finite automaton"]
		} |}

	let exer_ab = {| {
			kind : "exercise",
			description : "this is an example",
			name : "exer_ab",
			problem : "Convert the regular expression ab*+ba* to finite automaton.",
			inside : ["a","ab","abb","abbbbbbbb","b","ba","baa","baaaaaa"],
			outside : ["","aba","bab","abba","baab","c"],
			properties : ["finite automaton"]
		} |}

	let exer_re2fa = {| {
			kind : "exercise",
			description : "this is an example",
			name : "exer_re2fa",
			problem : "Converta o autómato finito com alfabeto: [x, y, z], estados: [S, T, V], estado inicial: S, transições [[S, x, S], [S, y, T], [S, z, V], [T, x, T], [T, z, T], [T, y, V], [V, x, T]], e estados finais: [V] em expressão regular.",
			inside : ["z", "xz", "yy", "yzy", "xyy", "zxxy"],
			outside : ["x","y","xy", "xyz", "yyx", "xzxz", "xyxz"],
			properties : ["regular expression"]
		} |}

	let exer_readwrite = {| {
			kind : "exercise",
			description : "this is an example",
			name : "exer_readwrite",
			problem : "open,close,read,write",
			inside : ["","orc","owc","orwc","owwrwrrc","ocorwc"],
			outside : ["or","oo","o","w","r","c","orw","owrrww","corwc"],
			properties : ["finite automaton"]
		} |}

	let oflatExamplesTable = [
		("dfa_1", dfa_1);
		("dfa_2", dfa_2);
		("dfa_astar", dfa_astar);
		("fa_abc", fa_abc);
		("nfa_1", nfa_1);
		("nfa_2", nfa_2);

		("re_abc", re_abc);
		("re_complex", re_complex);
		("re_convoluted", re_convoluted);
		("re_simple", re_simple);
		("re_astar", re_astar);

		("fe_colors", fe_colors);

		("cfg_simple", cfg_simple);
		("cfg_balanced", cfg_balanced);
	
		("cfg_ll_thesis_g1", cfg_ll_thesis_g1);
		("cfg_ll_thesis_g2", cfg_ll_thesis_g2);
		("cfg_ll_1", cfg_ll_1);
		("cfg_ll_2", cfg_ll_2);
		("cfg_ll_3", cfg_ll_3);
		("cfg_ll_4", cfg_ll_4);
		("cfg_ll_5", cfg_ll_5);
		("cfg_ll_6", cfg_ll_6);	

		("cfg_lr0_thesis", cfg_lr0_thesis);
		("cfg_slr1_thesis", cfg_slr1_thesis);
		("cfg_slr1", cfg_slr1);
		("cfg_lr1_thesis", cfg_lr1_thesis);
		("cfg_lalr1_thesis", cfg_lalr1_thesis);
		("cfg_only_lr1", cfg_onlylr1);
		("cfg_not_lr1", cfg_notlr1);
		
		("ug_simple", ug_simple);

		("pda_WW_1", pda_WW_1);
		("pda_AABB", pda_AABB);
		("pda_Explode", pda_Explode);

		("tm_translate", tm_translate);
		("tm_translate_lb", tm_translate_lb);
		("tm_astar1", tm_astar1);
		("tm_astar2", tm_astar2);
		("tm_astar3", tm_astar3);
		("tm_astar4", tm_astar4);
		("tm_astar5", tm_astar5);
		("tm_astar6", tm_astar6);
		("tm_astar7", tm_astar7);
		("tm_astar8", tm_astar8);
		("tm_astar9", tm_astar9);
		("tm_astar10", tm_astar10);
		("tm_astar11", tm_astar11);
		
		("comp_abc", comp_abc);
		
		("exer_balanced_cfg", exer_balanced_cfg);
		("exer_astar_fa", exer_astar_fa);
		("exer_astar_re", exer_astar_re);
		("exer_abcd", exer_abcd);
		("exer_ab", exer_ab);
		("exer_re2fa", exer_re2fa);
		("exer_readwrite", exer_readwrite);

	]

	let examples =
		List.map fst oflatExamplesTable

	let example name =
		List.assoc name oflatExamplesTable

	let jsonExample name =
		let j = JSon.parse (example name) in
			if JSon.isNull j then
				Error.error "Invalid example" name ();
			j
			
	let see name =
		Util.println [example name]

	let validate () =
		List.iter (fun n -> ignore (jsonExample n)) examples

	let _ =
		if true then
			validate ()	
end
