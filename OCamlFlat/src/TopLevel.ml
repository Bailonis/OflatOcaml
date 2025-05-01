

(*
 * TopLevel.ml
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
 * feb/2021 (amd) - Added some missing functions.
 * feb/2020 (jg) - Initial version.
 *)

(*
 * Description: Set of functions with simple signatures to the used in the
 * ocaml toplevel system. In a sense, this provides a command-line interface
 * to most of the functionalities of the OCamlFLAT library.
 *
 * TODO: Improve.
 *)

(*

let f str =
	let r = fa_accept fa str in
	let q = stats() in
	let t = fa_acceptTrail fa str in
	let x = stats() in
	let p = fa_acceptPath fa str in
	let y = stats() in
	let (_,p1,t1) = fa_acceptFull fa str in
	let z = stats() in
	let w =  if t = t1 && p = p1 then "OK" else "BAD" in
		(r,q,x,y,z,w)
;;

#print_depth 10000;;
#print_length 10000;;


*)

open FiniteAutomatonTop


#ifdef ALLx

module TopLevel 5 5 =
struct
(* Toplevel types *)

	type finiteAutomaton = 
	{
			alphabet: symbol list;
			states: state list;
			initialState: state;
			transitions: transition??? list;
			acceptStates: state list
		}

	type regularExpression = string

	type contextFreeGrammar = {
			alphabet: symbol list;
			variables: symbol list;
			initial: symbol;
			rules: string list
		}

	type exercise = {
			inside: string list;
			outside: string list;
			properties : string list
		}


	(* Toplevel convertions *)

	let fa_convertTo (fa: FiniteAutomaton.t ) =
		{
			alphabet = Set.toList fa.alphabet;
			states = Set.toList fa.states;
			initialState = fa.initialState;
			transitions = Set.toList fa.transitions;
			acceptStates = Set.toList fa.acceptStates
		}

	let fa_convertFrom (fa: finiteAutomaton) : FiniteAutomaton.t =
		{
			alphabet = Set.make fa.alphabet;
			states = Set.make fa.states;
			initialState = fa.initialState;
			transitions = Set.make fa.transitions;
			acceptStates = Set.make fa.acceptStates
		}

	let re_convertTo re : regularExpression = RegExpSyntax.toString re

	let re_convertFrom re = RegExpSyntax.parse re

	let cfg_convertTo (cfg: ContextFreeGrammar.t ) =
		let alpha = Set.toList cfg.alphabet in
		let variables = Set.toList cfg.variables in
		let initial = cfg.initial in
		let rules = CFGSyntax.toStringList cfg.rules in
			{
				alphabet = alpha;
				variables = variables;
				initial = initial;
				rules = rules
			}

	let cfg_convertFrom (cfg: contextFreeGrammar) : ContextFreeGrammar.t =
			{
				alphabet = Set.make cfg.alphabet;
				variables = Set.make cfg.variables;
				initial = cfg.initial;
				rules = CFGSyntax.parse (Set.make cfg.rules)
			}

	let exer_convertTo (exer: ExerTypes.t): exercise =
		let inws = Set.map (fun w -> word2str w) exer.inside in
		let outws = Set.map (fun w -> word2str w) exer.outside in
			{
				inside = Set.toList inws;
				outside = Set.toList outws;
				properties = Set.toList exer.properties
			}

	let exer_convertFrom (exer: exercise) : ExerTypes.t =
		let inws = List.map (fun s -> str2word s) exer.inside in
		let outws = List.map (fun s -> str2word s) exer.outside in
			{
				problem = "";
				inside = Set.make inws;
				outside = Set.make outws;
				properties = Set.make exer.properties
			}

	let exer_convertFailures ins outs props =
		let ins = Set.map (fun w -> word2str w) ins in
		let outs = Set.map (fun w -> word2str w) outs in
			(Set.toList ins, Set.toList outs, Set.toList props)


	(* Automaton functions *)

	let fa_load file =
		let a = new FiniteAutomaton.model (Arg.File file) in
			fa_convertTo a#representation

	let fa_build text =
		let a = new FiniteAutomaton.model (Arg.Text text) in
			fa_convertTo a#representation

	let fa_json json =
		let a = new FiniteAutomaton.model (Arg.JSon json) in
			fa_convertTo a#representation

	let fa_predef name =
		fa_build (Examples.example name)

	let fa_accept fa w =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
		let w = str2word w in
			a#accept w

	let fa_traceAccept fa w =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
		let w = str2word w in
			a#acceptWithTracing w

	let fa_generate fa l =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
		let b = Set.map (fun w -> word2str w) (a#generate l) in
			Set.toList b

	let fa_reachable fa =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
		let start = fa.initialState in
			Set.toList (a#reachable start)

	let fa_productive fa =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
			Set.toList (a#productive)

	let fa_clean fa =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
		let b = a#cleanUselessStates in
			fa_convertTo b#representation


	let fa_toDeter fa =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
		let b = a#toDeterministic in
			fa_convertTo b#representation


	let fa_isDeter fa =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
			a#isDeterministic

	let fa_minimize fa =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
		let b = a#minimize in
			fa_convertTo b#representation

	let fa_isMin fa =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
			a#isMinimized

	let fa_toRegex fa =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
		let b = PolyModel.fa2re a in
			re_convertTo b#representation

	(* Regex functions *)

	let re_load file =
		let a = new RegularExpression.model (Arg.File file) in
			re_convertTo a#representation

	let re_build text =
		let a = new RegularExpression.model (Arg.Text text) in
			re_convertTo a#representation

	let re_json json =
		let a = new RegularExpression.model (Arg.JSon json) in
			re_convertTo a#representation

	let re_predef name =
		re_build (Examples.example name)

	let re_alphabet re =
		let re = re_convertFrom re in
		let a = new RegularExpression.model (Arg.Representation re) in
			Set.toList a#alphabet

	let re_accept re w =
		let re = re_convertFrom re in
		let a = new RegularExpression.model (Arg.Representation re) in
		let w = str2word w in
			a#accept w

	let re_trace re w =
		let re = re_convertFrom re in
		let a = new RegularExpression.model (Arg.Representation re) in
		let w = str2word w in
			a#allTrees w

	let re_generate re l =
		let re = re_convertFrom re in
		let a = new RegularExpression.model (Arg.Representation re) in
		let b = Set.map (fun w -> word2str w) (a#generate l) in
			Set.toList b

	let re_simplify re =
		let re = re_convertFrom re in
		let a = new RegularExpression.model (Arg.Representation re) in
		let b =	a#simplify in
			re_convertTo b#representation

	let re_toFA re =
		let re = re_convertFrom re in
		let a = new RegularExpression.model (Arg.Representation re) in
		let b =	PolyModel.re2fa a in
			fa_convertTo b#representation



	(* CFG functions *)

	let cfg_load file =
		let a = new ContextFreeGrammar.model (Arg.File file) in
			cfg_convertTo a#representation

	let cfg_build text =
		let a = new ContextFreeGrammar.model (Arg.Text text) in
			cfg_convertTo a#representation

	let cfg_json json =
		let a = new ContextFreeGrammar.model (Arg.JSon json) in
			cfg_convertTo a#representation

	let cfg_predef name =
		cfg_build (Examples.example name)

	let cfg_accept cfg w =
		let cfg = cfg_convertFrom cfg in
		let a = new ContextFreeGrammar.model (Arg.Representation cfg) in
		let w = str2word w in
			a#accept w

	let cfg_trace cfg w =
		let cfg = cfg_convertFrom cfg in
		let a = new ContextFreeGrammar.model (Arg.Representation cfg) in
		let w = str2word w in
			a#acceptWithTracing w

	let cfg_generate cfg l =
		let cfg = cfg_convertFrom cfg in
		let a = new ContextFreeGrammar.model (Arg.Representation cfg) in
		let b = Set.map (fun w -> word2str w) (a#generate l) in
			Set.toList b

	let cfg_toFA cfg =
		let cfg = cfg_convertFrom cfg in
		let a = new ContextFreeGrammar.model (Arg.Representation cfg) in
		let b =	PolyModel.cfg2fa a in
			fa_convertTo b#representation

	let cfg_toRe cfg =
		let cfg = cfg_convertFrom cfg in
		let a = new ContextFreeGrammar.model (Arg.Representation cfg) in
		let b =	PolyModel.cfg2re a in
			re_convertTo b#representation

  (* LL1 functions *)

  let ll1_toggleSimplified cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      a#toggleSimplified

  let ll1_first cfg w =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
    let w = str2word w in
		  Set.toList (a#first w)

  let ll1_follow cfg w =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
		  Set.toList (a#follow w)

  let ll1_lookahead cfg rl =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
		  Set.toList (a#lookahead rl)
		  
  let ll1_isLL1 cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
		  a#isLL1

  let ll1_isLeftRecursive cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
		  a#isLeftRecursive

  let ll1_createParsingTable cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      Set.toList a#createParsingTable

  let ll1_hasParsingTableConflict cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      a#hasParsingTableConflict

  let ll1_accept w cfg =
    let cfg = cfg_convertFrom cfg in
    let w = str2word w in
    let a = new LL1Grammar.model (Representation cfg) in
      a#acceptZ w

	let ll1_productiveSymbols cfg = 
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      Set.toList a#productiveSymbols

	let ll1_accessibleSymbols cfg = 
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      Set.toList a#accessibleSymbols

  let ll1_productiveRewrite cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      cfg_convertTo (a#productiveRewrite)#representation
      
  let ll1_accessibleRewrite cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      cfg_convertTo (a#accessibleRewrite)#representation
      
  let ll1_clean cfg =
    let cfg = cfg_convertFrom cfg in
	let open LL1Grammar in
    let a = new model (Representation cfg) in
      List.map (fun {tType = t; grammar = g} -> (t, cfg_convertTo g#representation)) a#clean

  let ll1_isFullyProductive cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      a#isFullyProductive
      
  let ll1_isFullyAccessible cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      a#isFullyAccessible
      
  let ll1_isClean cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      a#isClean

  let ll1_removeLeftRecursion cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      cfg_convertTo (a#removeLeftRecursion).grammar#representation

  let ll1_removeDirectLeftRecursion cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      cfg_convertTo (a#removeDirectLeftRecursion)#representation

  let ll1_leftFactoring cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      cfg_convertTo (a#leftFactoring).grammar#representation

  let ll1_isLeftFactoring cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      a#isLeftFactoring
      
  let ll1_leftCorner s cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      Set.toList (a#leftCorner s)
  
  let ll1_removeEmptyProductions cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      cfg_convertTo (a#removeEmptyProductions).grammar#representation

  let ll1_removeUnitProductions cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      cfg_convertTo (a#removeUnitProductions).grammar#representation
  
  let ll1_generateRecursiveDescendentParser lang cfg =
    let cfg = cfg_convertFrom cfg in
    let a = new LL1Grammar.model (Representation cfg) in
      Printf.printf "%s" (a#generateRecursiveDescendentParser lang)

  let ll1_transformToLL1 cfg =
    let cfg = cfg_convertFrom cfg in
	let open LL1Grammar in
    let a = new model (Representation cfg) in
      List.map ( fun {tType = t; grammar = g} -> 
        (t, cfg_convertTo g#representation)
               )a#transformToLL1

	(* Exercise functions *)

	let exer_load file =
		let e = new Exercise.exercise (Arg.File file) in
			exer_convertTo e#representation

	let exer_build text =
		let e = new Exercise.exercise (Arg.Text text) in
			exer_convertTo e#representation

	let exer_json json =
		let e = new Exercise.exercise (Arg.JSon json) in
			exer_convertTo e#representation

	let exer_predef name =
		exer_build (Examples.example name)

	let exer_testFA exer fa =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
		let exer = exer_convertFrom exer in
		let e = new Exercise.exercise (Arg.Representation exer) in
			a#checkExercise e

	let exer_testFAFailures exer fa =
		let fa = fa_convertFrom fa in
		let a = new FiniteAutomaton.model (Arg.Representation fa) in
		let exer = exer_convertFrom exer in
		let e = new Exercise.exercise (Arg.Representation exer) in
		let (ins,outs,props) = a#checkExerciseFailures e in
			exer_convertFailures ins outs props

	let exer_testRe exer re =
		let re = re_convertFrom re in
		let a = new RegularExpression.model (Arg.Representation re) in
		let exer = exer_convertFrom exer in
		let e = new Exercise.exercise (Arg.Representation exer) in
			a#checkExercise e

	let exer_testReFailures exer re =
		let re = re_convertFrom re in
		let a = new RegularExpression.model (Arg.Representation re) in
		let exer = exer_convertFrom exer in
		let e = new Exercise.exercise (Arg.Representation exer) in
		let (ins,outs,props) = a#checkExerciseFailures e in
			exer_convertFailures ins outs props

	let exer_testCfg exer cfg =
		let cfg = cfg_convertFrom cfg in
		let a = new ContextFreeGrammar.model (Arg.Representation cfg) in
		let exer = exer_convertFrom exer in
		let e = new Exercise.exercise (Arg.Representation exer) in
			a#checkExercise e

	let exer_testCfgFailures exer cfg =
		let cfg = cfg_convertFrom cfg in
		let a = new ContextFreeGrammar.model (Arg.Representation cfg) in
		let exer = exer_convertFrom exer in
		let e = new Exercise.exercise (Arg.Representation exer) in
		let (ins,outs,props) = a#checkExerciseFailures e in
			exer_convertFailures ins outs props
end

#endif
