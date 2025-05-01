(*
 * PolyModel.ml
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
 *  Written by Various
 *)

(*
 * ChangeLog:
 *
 * apr/2021 (amd) - Several new build functions.
 * jan/2021 (amd) - Created this module, collecting all the operation.
                    involving two or more kinds of models.
                    This allows to got rid of the mutual recursion between
                    modules, allowing storing each module in a different file.
 * dec/2019 (jg) - Initial code, across several modules in file "OCamlFlat.ml".
 *)

(*
 * Description: Poly-model operations.
 *
 * TODO: Cleanup.
 *)
 
open BasicTypes

(********************************************************************)
module RE2FA =
struct
	open RegularExpression
	open FiniteAutomaton

	(*auxiliary var for genName function*)
	let k = ref 0

	(*for each new state, generates a name that will distinguish it from all the other generated states *)
	let genName () =
		let n = !k in
		let () = k:= n + 1 in
			(*easy way of having all single digit state names have a zero before their actual number*)
			let name = if n > 9 then "new_St" ^ (string_of_int n)
						else "new_St0" ^ (string_of_int n) in
				str2state name

	let rec compile (re: RegularExpression.t) : FiniteAutomaton.t =
		match re with
			| Plus(l, r) ->
					let fa1 = compile l in
					let fa2 = compile r in
					let newStart = genName () in
					let newSts = Set.add newStart (Set.union fa1.states fa2.states) in
					let newAccSts = Set.union fa1.acceptStates fa2.acceptStates in
					let newTran1 = (newStart, epsilon, fa1.initialState) in
					let newTran2 = (newStart, epsilon, fa2.initialState) in
					let newTrans = Set.add newTran1 (Set.add newTran2
						(Set.union fa1.transitions fa2.transitions)) in
					let newAlf = Set.union fa1.alphabet fa2.alphabet in
						{alphabet = newAlf; states = newSts; initialState = newStart;
							transitions = newTrans; acceptStates = newAccSts}
			| Seq(l, r) ->
					let fa1 = compile l in
					let fa2 = compile r in
					let ist = fa1.initialState in
					let sts = Set.union fa1.states fa2.states in
					let asts = fa2.acceptStates in
					let newTrns = Set.map (fun x -> (x, epsilon, fa2.initialState) ) fa1.acceptStates in
					let trns = Set.union newTrns (Set.union fa1.transitions fa2.transitions) in
					let alf = Set.union fa1.alphabet fa2.alphabet in
						{alphabet = alf; states = sts; initialState = ist;
							transitions = trns; acceptStates = asts}
			| Star(r) ->
					let fa = compile r in
					let newStart = genName () in
					let newSts = Set.add newStart fa.states in
					let newTrns = Set.map (fun st -> (st, epsilon, newStart)) fa.acceptStates in
					let allNewTrns = Set.add (newStart, epsilon, fa.initialState) (Set.union newTrns fa.transitions) in
						{alphabet = fa.alphabet; states = newSts; initialState = newStart;
							transitions = allNewTrns; acceptStates = Set.make [newStart]}
			| Symb(c) ->
					let newStart = genName () in
					let newAcc = genName () in
					let newSts = Set.make [newStart; newAcc] in
					let newTrn = Set.make [(newStart, c, newAcc)] in
						{alphabet = Set.make [c]; states = newSts; initialState = newStart;
							transitions = newTrn; acceptStates = Set.make [newAcc]}
			| Empty ->
					let newStart = genName () in
							{alphabet = Set.empty; states = Set.make [newStart]; initialState = newStart;
								transitions = Set.empty; acceptStates = Set.make [newStart]}
			| Zero ->
					let newStart = genName () in
						{alphabet = Set.empty; states = Set.make [newStart]; initialState = newStart;
								transitions = Set.empty; acceptStates = Set.empty}
	
	let re2fa (re: RegularExpression.t): FiniteAutomaton.t =
		compile re
end

(********************************************************************)
module FA2RE =
struct
	open FiniteAutomaton
	open RegularExpression

	(* transforms the set of expressions into the regex: plus of all expressions of the set *)
	let plusSet reSet =
		let rec pls l =
			match l with
				[] -> Zero
				| x::xs -> if xs = [] then x else Plus (x, pls xs)
		in
			pls (Set.toList reSet)

	(* For the given i and j, returns the value of R when k is zero.
		Note that k will always be 0 when called inside this method *)
	let calczerok k i j trns =
		let ts = Set.filter (fun (a,_,b) -> i = a && j = b) trns in
		if ts <> Set.empty then
			if i <> j then
				let res = Set.map (fun (_,c,_) -> Symb c) ts in
					(k,i,j,plusSet res)
			else
				let res = Set.map (fun (_,c,_) -> Symb c) ts in
				let re = Plus(Empty, (plusSet res)) in
					(k,i,j,re)

		else (k,i,j,Zero)
		
	let getRij i j prvK =
		let r = Set.nth (Set.filter (fun (_,x,y,_) -> x = i && y = j) prvK) 0 in
			(fun (_,_,_,re) -> re) r

	let assembleRe st i j prvK =
		let rik = getRij i st prvK in
		let rkk = Star (getRij st st prvK) in
		let rkj = getRij st j prvK in
			Seq(rik, Seq(rkk,rkj))
				
	(* For the given i and j, returns the value of R when k is not zero. *)
	let calck k i j prvK sts =
		let rij = getRij i j prvK in
		let rikjs = Set.map (fun st -> assembleRe st i j prvK) sts in
		let rikj = plusSet rikjs in
			(k,i,j,Plus(rij,rikj))

	(* Main function that applies previous 2 functions to all possible i and j pairs *)
	let rec rkij k trns sts =
		if k < 1 then
			Set.map (fun (i,j) -> calczerok k i j trns) (Set.product sts sts)
		else
			let prvK = rkij (k-1) trns sts in
				Set.map (fun(i,j) -> calck k i j prvK sts) (Set.product sts sts)

	let fa2re (fa: FiniteAutomaton.t): RegularExpression.t =
		(* Since the algorithm only works for deterministic automaton, we first convert it
			to its deterministic equivalent *)
		let fa = FiniteAutomaton.toDeterministic fa in
		let sts = fa.states in
		let trns = fa.transitions in
		let allRks = rkij (Set.size sts) trns sts in
		let result = Set.filter (fun (_,i,j,_) -> i = fa.initialState && Set.belongs j fa.acceptStates ) allRks in
		let res = Set.map (fun (_,_,_,re) -> re) result in		
			plusSet res
		(*	simplify (plusSet res) *)
end

(********************************************************************)
module RE2CFG =
struct
	open RegularExpression
	open ContextFreeGrammarBasic
	
	(*auxiliary var for genVar function*)
	let k = ref 0

	(* generates new unused variable name for the cfg *)
	let genVar () =
		let n = !k in
		let () = k:= n + 1 in
		let ascii = 65 + n in
		if ascii < 65 || ascii > 90
		then char2symb 'A'
		else char2symb (Char.chr ascii)

	(*
	let convertPlsRules rl i1 i2 newInit =
		(* swaps the initial variables of both old cfgs for the new initial var *)
		let swapInits c = if c = i1 || c = i2 then newInit else c in

		let newBody b = List.map (fun c -> swapInits c) b in
		let newRule r = {head = swapInits r.head; body = newBody r.body} in

			Set.map (fun r -> newRule r) rl

	in
	*)
	(* create gcf rules for plus expression *)
	let convertPlsRules rl i1 i2 newInit =
		let newRule1 = {head = newInit; body = [i1]} in
		let newRule2 = {head = newInit; body = [i2]} in
			Set.add newRule1 (Set.add newRule2 rl)

	(* create gcf rules for seq expression *)
	let convertSeqRules lcfg rcfg =
		let rl1 = lcfg.rules in
		let rl2 = rcfg.rules in
		let alp1 = lcfg.alphabet in
		let rl = Set.union rl1 rl2 in
		let newBody r =
			let b = r.body in
				match b with
					| [c] when Set.belongs r rl1 && not (Set.belongs c alp1) && c <> epsilon -> b
					| [c] when Set.belongs r rl1 && Set.belongs c alp1 -> [c; rcfg.initial]
					| [epsilon] when Set.belongs r rl1 -> [epsilon; rcfg.initial]
					| b when Set.belongs r rl2 -> b
					| _ -> b
		in
		let newRule r = {head = r.head; body = newBody r} in
			Set.map (fun r -> newRule r) rl

	(* create gcf rules for star expression *)
	let convertStrRules cfg =
		let newBody b =
			match b with
				| [c] when Set.belongs c cfg.alphabet -> [c; cfg.initial]
				| _ -> b
		in
		let r0 = {head = cfg.initial; body = [epsilon]} in

		let newRule r = {head = r.head; body = newBody r.body} in
		let newRules = Set.map (fun r -> newRule r) cfg.rules in
			Set.add r0 newRules

	let rec compile re =
		match re with
			| Plus(l, r) ->
					let cl = compile l in
					let cr = compile r in
					let alp = Set.union cl.alphabet cr.alphabet in
					let init = genVar () in
					let vs = Set.add init (Set.union cl.variables cr.variables) in
					let rl = Set.union cl.rules cr.rules in
					let rl = convertPlsRules rl cl.initial cr.initial init in
						{alphabet = alp; variables = vs;
							initial = init; rules = rl}
			| Seq(l, r) ->
					let cl = compile l in
					let cr = compile r in
					let alp = Set.union cl.alphabet cr.alphabet in
					let init = cl.initial in
					let vs = Set.union cl.variables cr.variables in
					let rl = convertSeqRules cl cr in
						{alphabet = alp; variables = vs;
							initial = init; rules = rl}
			| Star(re) ->
					let cre = compile re in
					let alp = cre.alphabet in
					let init = cre.initial in
					let vs = cre.variables in
					let rl = convertStrRules cre in
						{alphabet = alp; variables = vs;
							initial = init; rules = rl}
			| Symb(c) ->
					let alp = Set.make [c] in
					let init = genVar () in
					let vars = Set.make [init] in
					let rules = Set.make [{head = init; body = [c]}] in
						{alphabet = alp; variables = vars;
							initial = init; rules = rules}
			| Empty ->
					let alp = Set.empty in
					let init = genVar () in
					let vars = Set.make [init] in
					let rules = Set.make [{head = init; body = [epsilon]}] in
						{alphabet = alp; variables = vars;
							initial = init; rules = rules}
			| Zero ->
					let alp = Set.empty in
					let init = genVar () in
					let var2 = genVar () in
					let vars = Set.make [init; var2] in
					let r1 = {head = init; body = [var2]} in
					let r2 = {head = var2; body = [init]} in
					let rules = Set.make [r1; r2] in
						{alphabet = alp; variables = vars;
								initial = init; rules = rules}

	let re2cfg (re: RegularExpression.t): ContextFreeGrammarBasic.t =
		compile re
end

(********************************************************************)
module FA2CFG =
struct
	let fa2cfg fa =
		let re = FA2RE.fa2re fa in
			RE2CFG.re2cfg re
end

(********************************************************************)
module CFG2FA = (* right-linear CFG *)
struct
	open ContextFreeGrammarBasic
	open FiniteAutomaton
	
	let toState sy = state (symb2str sy)

	let toStates ssy = Set.map toState ssy

	(* This name will always be unique in the generated automaton *)
	let accSt = state "AccSt"

	let ruleToTrans (cfg: ContextFreeGrammarBasic.t) rh rb =
		let alp = cfg.alphabet in
		let vrs = cfg.variables in
		match rb with
			| [s;v] when Set.belongs s alp && Set.belongs v vrs	-> Set.make [(toState rh, s, toState v)]
			| [v] when Set.belongs v vrs -> Set.make [(toState rh, epsilon, toState v)]
			| [s] when Set.belongs s alp -> Set.make [(toState rh, s, accSt)]
			| [e] when e = epsilon -> Set.make [(toState rh, epsilon, accSt)]
			| _ -> Set.empty

	let cfg2fa (cfg: ContextFreeGrammarBasic.t): FiniteAutomaton.t =
	{	alphabet = cfg.alphabet;
		states = Set.add accSt (toStates cfg.variables);
		initialState = toState cfg.initial;
		transitions = Set.flatMap (fun r -> ruleToTrans cfg r.head r.body) cfg.rules;
		acceptStates = Set.make [accSt]
	}
end

(********************************************************************)
module CFG2RE = (* right-linear CFG *)
struct
	let cfg2re (cfg: ContextFreeGrammarBasic.t): RegularExpression.t =
		let fa = CFG2FA.cfg2fa cfg in
			FA2RE.fa2re fa
end

(********************************************************************)
module PDA2FA =
struct
	let transitionsFa trns = Set.map ( fun (s1,_,a,s2,_) -> (s1,a,s2) ) trns
	
	let pda2fa (pda: PushdownAutomaton.t): FiniteAutomaton.t  =
	{	alphabet = pda.inputAlphabet;
		states = pda.states;
		initialState = pda.initialState;
		transitions = transitionsFa pda.transitions;
		acceptStates = pda.acceptStates
	}
end

(********************************************************************)
module FA2PDA =
struct
	let upgradeTransition (s1,symb,s2) =
			(s1,PushdownAutomaton.stackSpecialSymb,symb,s2,[PushdownAutomaton.stackSpecialSymb])
			
	let upgradeTransitions trns =
		Set.map upgradeTransition trns
		
	let fa2pda (fa: FiniteAutomaton.t): PushdownAutomaton.t =
	{	inputAlphabet = fa.alphabet;
		stackAlphabet = Set.make [PushdownAutomaton.stackSpecialSymb];
		states = fa.states;
		initialState = fa.initialState;
		initialStackSymbol = PushdownAutomaton.stackSpecialSymb;
		transitions = upgradeTransitions fa.transitions;
		acceptStates = fa.acceptStates;
		criteria = true
	}
end

(********************************************************************)
module RE2PDA =
struct
	let re2pda (re: RegularExpression.t): PushdownAutomaton.t =
		let fa = RE2FA.re2fa re in
			FA2PDA.fa2pda fa
end

(********************************************************************)
module PDA2RE =
struct
	let pda2re (pda: PushdownAutomaton.t): RegularExpression.t =
		let fa = PDA2FA.pda2fa pda in
			FA2RE.fa2re fa
end

(********************************************************************)
module CFG2PDA =
struct
	open ContextFreeGrammarBasic
	open PushdownAutomaton

	let computeState = state "q"
	
	let makeNewTransition symbToConsume topStackSymbol toPutInStack: transition =
		(computeState, topStackSymbol, symbToConsume, computeState, toPutInStack)

	let buildTransitions(cfg: ContextFreeGrammarBasic.t): transitions =
		let transitionsRules = Set.map (fun r -> makeNewTransition epsilon r.head r.body) cfg.rules in
		let transitionsFinalSymb = Set.map (fun alph -> makeNewTransition alph alph []) cfg.alphabet in
			Set.union transitionsRules transitionsFinalSymb

	let cfg2pda (cfg: ContextFreeGrammarBasic.t): PushdownAutomaton.t = 
	{	inputAlphabet = cfg.alphabet;
		stackAlphabet = Set.union cfg.alphabet cfg.variables;
		states = Set.make [computeState];
		initialState = computeState;
		initialStackSymbol = cfg.initial;
		transitions = buildTransitions cfg;
		acceptStates = Set.empty;
		criteria = false
	}
end

(********************************************************************)
module PDA2CFG = (* todo *)
struct
	let pda2cfg (pda: PushdownAutomaton.t): ContextFreeGrammarBasic.t =
		ContextFreeGrammarBasic.make (Arg.Text {|{}|})
end

(********************************************************************)
module PDA2TM =
struct
	let generateTransitionsToPD st alphEntr alphPD: TuringMachine.transitions =
		let allAlph = Set.add dollar (Set.union alphEntr alphPD) in
			Set.map (fun symb -> (st,[symb],st,[symb],[R])) allAlph 

	let generateTransitionsFromPD st alphEntr alphPD: TuringMachine.transitions =
		let allAlph = Set.add dollar (Set.union alphEntr alphPD) in
			Set.map (fun symb -> (st,[symb],st,[symb],[L])) allAlph 

	let insertSymbolsPD alphEntr (pda: PushdownAutomaton.t): states * TuringMachine.transitions =
		let alphPD = pda.stackAlphabet in
		let st1 = state (IdGenerator.gen("q")) in
		let st2 = state (IdGenerator.gen("q")) in
		let st3 = state (IdGenerator.gen("q")) in
		let newSts = Set.add st1 ( Set.add st2 ( Set.add st3 Set.empty)) in
		let newTrs1 = Set.union (generateTransitionsToPD st1 alphEntr alphPD) (generateTransitionsFromPD st3 alphEntr alphPD) in
		let newTrs2 = Set.add (st1,[empty],st2,[symb "$"],[R]) (Set.add (st2,[empty],st3,[pda.initialStackSymbol],[R]) ( Set.add (st3,[empty],pda.initialState,[empty],[R])  newTrs1 )) in
			(Set.union pda.states newSts) , newTrs2

	let rec fillStackTransition lastSt prevSt (trs: TuringMachine.transitions) wordL: TuringMachine.transitions =
		match wordL with
		| [] -> trs
		| x::y ->	let newState = if (Set.isEmpty (Set.make y)) then lastSt else IdGenerator.gen("q") in
							let dir = if (Set.isEmpty (Set.make y)) then L else R in
								fillStackTransition lastSt newState (Set.add (prevSt,[empty], newState, [x], [dir]) trs) y 

	let convertNormalTransition (tr: PushdownAutomaton.transition) alphEntr alphPD: states * TuringMachine.transitions =
		let (startState,unstackedSymbol,readSymbol,nextState,writeSymbolL) = tr in
		let st1 = state (IdGenerator.gen("q")) in
		let st2 = state (IdGenerator.gen("q")) in
		let st3 = state (IdGenerator.gen("q")) in
		let ftrs = (startState,[readSymbol],st1,[empty],[R]) in
		let trsTPD = Set.add ftrs (generateTransitionsToPD st1 alphEntr alphPD) in
		let trsRTOP = Set.add (st1,[empty],st2,[empty],[L]) trsTPD in
		let firstDirection = if ((List.length writeSymbolL) = 1) then L else R in
		let lastSt = if ((List.length writeSymbolL) = 1) then st3 else state (IdGenerator.gen("q")) in
		let replaceTop = Set.add (st2,[unstackedSymbol],st3, [List.hd writeSymbolL], [firstDirection]) trsRTOP in
		let additionalSymbolTrs = Set.union replaceTop (fillStackTransition lastSt st3 Set.empty (List.tl writeSymbolL)) in
		let trsFPD = Set.union additionalSymbolTrs (generateTransitionsFromPD lastSt alphEntr alphPD) in
		let trsLast = Set.add (lastSt,[empty],nextState,[empty],[R]) trsFPD in
			Set.add lastSt (Set.add st3 (Set.add st2 (Set.add st1 Set.empty))), trsLast

	let convertAcceptTransition (tr: PushdownAutomaton.transition) alphEntr alphPD initialStackSymb: states * TuringMachine.transitions =
		let (startState,unstackedSymbol,readSymbol,nextState,writeSymbolL) = tr in
		let st1 = state (IdGenerator.gen("q")) in
		let st2 = state (IdGenerator.gen("q")) in
		let st3 = state (IdGenerator.gen("q")) in
		let ftrs = Set.add (startState,[dollar],st1,[dollar],[R]) Set.empty in
		let checkInitSS = Set.add (st1,[initialStackSymb],st2,[empty],[R]) ftrs in
		let lastCheck = Set.add (st2,[empty],st3,[empty],[R]) checkInitSS in
			Set.add st3 (Set.add st2 (Set.add st1 Set.empty)), lastCheck

	let convertTransitionX (tr: PushdownAutomaton.transition) alphEntr alphPD initialStackSymb: states * TuringMachine.transitions = 
		let (_,_,readSymbol,_,_) = tr in
			if readSymbol == draftVar then convertAcceptTransition tr alphEntr alphPD initialStackSymb
			else convertNormalTransition tr alphEntr alphPD

	let rec convertTransitions newSts newTrs alphEntr (pda: PushdownAutomaton.t) (trs: PushdownAutomaton.transitions): states * TuringMachine.transitions = 
		let alphPD = pda.stackAlphabet in
		let initialStackSymb = pda.initialStackSymbol in
		if (Set.size trs) = 0 then newSts, newTrs
		else 
			let (nSts,nTrs) = convertTransitionX (Set.hd trs) alphEntr alphPD initialStackSymb in
				convertTransitions (Set.union nSts newSts) (Set.union nTrs newTrs) alphEntr pda (Set.tl trs)

	(*Se parar por pilha vazia 'e ncess'ario criar um estado final*)
	let getFinalStates trs: states =
		Set.map (fun (_,_,_,d,_) -> d) (Set.filter (fun (_,_,c,_,_) -> c = dollar) trs)

	let pda2tm (pda: PushdownAutomaton.t): TuringMachine.t =
		let pdaAlphabet = Set.remove draftVar pda.inputAlphabet in
		let (initialStates, initialTransitions) = insertSymbolsPD pdaAlphabet pda in
		let (convertedTransitionStates,convertedTransitions) =
			convertTransitions Set.empty Set.empty pdaAlphabet pda pda.transitions in
		let allAlphabet = Set.add dollar ( Set.union pdaAlphabet pda.stackAlphabet) in
		let allStates = Set.union initialStates convertedTransitionStates in
		let allTransitions = Set.union initialTransitions convertedTransitions in
		let allAcceptStates = Set.union pda.acceptStates (getFinalStates pda.transitions) in
			{ TuringMachine.tm_zero with
				entryAlphabet = pda.inputAlphabet;
				tapeAlphabet = allAlphabet;
				states = allStates;
				initialState = state "q00";
				transitions = allTransitions;
				acceptStates = allAcceptStates;
				criteria = true }
end

(********************************************************************)
module FA2TM = (* Carolina *)
struct
	let fa2tm (fa : FiniteAutomaton.t): TuringMachine.t = 
	{	entryAlphabet = fa.alphabet;
		tapeAlphabet = fa.alphabet;
		empty = empty;
		states = fa.states;
		initialState = fa.initialState;
		transitions = Set.map (fun (a,b,c) -> (a,[b],c,[b],[R])) fa.transitions;
		acceptStates = fa.acceptStates;
		criteria = true;
		lbMarkers = [];
		_nTapes = 1
	}
end

(********************************************************************)
module RE2TM =
struct
	let re2tm (re: RegularExpression.t): TuringMachine.t =
		let re = RE2FA.re2fa re in
			FA2TM.fa2tm re
end

(********************************************************************)
module CFG2TM = (* ??? *)
struct
	let cfg2tm (cfg: ContextFreeGrammarBasic.t): TuringMachine.t =
		let cfg = CFG2FA.cfg2fa cfg in
			FA2TM.fa2tm cfg
end

(********************************************************************)
module PolyBasic =
struct
	let re2fa = RE2FA.re2fa
	let pda2fa = PDA2FA.pda2fa
	let cfg2fa = CFG2FA.cfg2fa
	
	let fa2re = FA2RE.fa2re
	let pda2re = PDA2RE.pda2re
	let cfg2re = CFG2RE.cfg2re

	let fa2pda = FA2PDA.fa2pda
	let re2pda = RE2PDA.re2pda
	let cfg2pda = CFG2PDA.cfg2pda
	
	let fa2cfg = FA2CFG.fa2cfg
	let re2cfg = RE2CFG.re2cfg
	let pda2cfg = PDA2CFG.pda2cfg
	
	let fa2tm = FA2TM.fa2tm
	let re2tm = RE2TM.re2tm
	let pda2tm = PDA2TM.pda2tm
	let cfg2tm = CFG2TM.cfg2tm
end

(********************************************************************)
module PolyModel =
struct
	open PolyBasic
	
	let json2model (j: JSon.t): Model.model =
		let kind = JSon.fieldString j "kind" in
			if FiniteAutomaton.kind = kind then
				(new FiniteAutomaton.model (Arg.JSon j) :> Model.model)
			else if RegularExpression.kind = kind then
				(new RegularExpression.model (Arg.JSon j) :> Model.model)
			else if PushdownAutomaton.kind = kind then
				(new PushdownAutomaton.model (Arg.JSon j) :> Model.model)
			else if ContextFreeGrammarBasic.kind = kind then
				(new ContextFreeGrammarBasic.model (Arg.JSon j) :> Model.model)
			else if TuringMachine.kind = kind then
				(new TuringMachine.model (Arg.JSon j) :> Model.model)
			else if FiniteEnumeration.kind = kind then
				(new FiniteEnumeration.model (Arg.JSon j) :> Model.model)
			else if Exercise.kind = kind then (
				ignore (new Exercise.exercise (Arg.JSon j));			
				(new FiniteAutomaton.model (Arg.JSon FiniteAutomaton.example) :> Model.model)
			)
			else (* need to ignore Composition.kind *)
				(new FiniteAutomaton.model (Arg.JSon FiniteAutomaton.example) :> Model.model)
				
	let text2model (text: string): Model.model = json2model (JSon.parse text)
	
	let file2model (filename: string): Model.model = json2model (JSon.fromFile filename)
	
	let example2model (name: string): Model.model = text2model (Examples.example name)

	let fa2model (fa: FiniteAutomaton.t): FiniteAutomaton.model =
		new FiniteAutomaton.model (Arg.Representation fa)

	let re2model (re: RegularExpression.t): RegularExpression.model =
		new RegularExpression.model (Arg.Representation re)

	let pda2model (pda: PushdownAutomaton.t): PushdownAutomaton.model =
		new PushdownAutomaton.model (Arg.Representation pda)

	let cfg2model (cfg: ContextFreeGrammarBasic.t): ContextFreeGrammarBasic.model =
		new ContextFreeGrammarBasic.model (Arg.Representation cfg)

	let tm2model (tm: TuringMachine.t): TuringMachine.model =
		new TuringMachine.model (Arg.Representation tm)

	let model2fa (model: Model.model): FiniteAutomaton.t =
		if model#isFiniteAutomaton then FiniteAutomaton.make (Arg.JSon (model#toJSon))
		else Error.fatal "model2fa"
		
	let model2re (model: Model.model): RegularExpression.t =
		if model#isRegularExpression then RegularExpression.make (Arg.JSon (model#toJSon))
		else Error.fatal "model2re"
		
	let model2cfg (model: Model.model): ContextFreeGrammarBasic.t =
		if model#isContextFreeGrammar then ContextFreeGrammarBasic.make (Arg.JSon (model#toJSon))
		else Error.fatal "model2cfg"
		
	let model2pda (model: Model.model): PushdownAutomaton.t =
		if model#isPushdownAutomaton then PushdownAutomaton.make (Arg.JSon (model#toJSon))
		else Error.fatal "model2pda"
		
	let model2tm (model: Model.model): TuringMachine.t =
		if model#isTuringMachine then TuringMachine.make (Arg.JSon (model#toJSon))
		else Error.fatal "model2tm"

	(* Carolina *)
	let model2comp (model: Model.model): CompositionSupport.t =
		if model#isFiniteAutomaton then FA (model2fa model)
		else if model#isRegularExpression then RE (model2re model)
		else if model#isPushdownAutomaton then PDA (model2pda model)
		else if model#isContextFreeGrammar then CFG (model2cfg model)
		else if model#isTuringMachine then TM (model2tm model)
		else if model#isComposition then 
			!CompositionSupport.makeCompositionRef (Arg.JSon (model#toJSon))
		else Error.fatal "model2comp"

	let re2fa m = fa2model (re2fa m#representation)
	let pda2fa m = fa2model (pda2fa m#representation)
	let cfg2fa m = fa2model (cfg2fa m#representation)

	let fa2re m = re2model (fa2re m#representation)
	let pda2re m = re2model (pda2re m#representation)
	let cfg2re m = re2model (cfg2re m#representation)

	let fa2pda m = pda2model (fa2pda m#representation)
	let re2pda m = pda2model (re2pda m#representation)
	let cfg2pda m = pda2model (cfg2pda m#representation)

	let fa2cfg m = cfg2model (fa2cfg m#representation)
	let re2cfg m = cfg2model (re2cfg m#representation)
	let pda2cfg m = cfg2model (pda2cfg m#representation)
	
	let fa2tm m = tm2model (fa2tm m#representation)	
	let re2tm m = tm2model (re2tm m#representation)	
	let pda2tm m = tm2model (pda2tm m#representation)	
	let cfg2tm m = tm2model (cfg2tm m#representation)
end

module PolyCheckExamples: sig end =
struct
	open Examples
	open PolyModel

	let checkExamples = (* run immediately *)
		List.iter
			(fun name -> ignore (text2model (example name)))
			examples
end

(********************************************************************)
module PolyBasicTests: sig end =
struct
	open PolyBasic

	let active = false

	let testToFA () =
		let re = RegularExpression.make (Arg.Predef "re_abc") in
		let fa = re2fa re in
			JSon.show (FiniteAutomaton.toJSon fa)

	let testToFA2 () =
		let re = RegularExpression.make (Arg.Predef "re_simple") in
		let fa = re2fa re in
			JSon.show (FiniteAutomaton.toJSon fa)

	let testToFA3 () =
		let re = RegularExpression.make (Arg.Predef "re_complex") in
		let fa = re2fa re in
			JSon.show (FiniteAutomaton.toJSon fa)

	let testToFA4 () =
		let re = RegularExpression.make (Arg.Predef "re_convoluted") in
		let fa = re2fa re in
			JSon.show (FiniteAutomaton.toJSon fa)

	let fa_toRe = {| {
		kind : "finite automaton",
		description : "this is an example",
		name : "fa_toRe",
		alphabet : ["a","b"],
		states : ["1", "2"],
		initialState : "1",
		transitions : [
				["1","a","2"],["2","b","2"]
			],
		acceptStates : ["2"]
	} |}

	let testSimplify () =
		let fa = FiniteAutomaton.make (Arg.Text fa_toRe) in
		let re = fa2re fa in
			RegularExpression.show re;
			let rs =  RegularExpression.simplify re in
				RegularExpression.show rs

	let testToRe () =
		let fa = FiniteAutomaton.make (Arg.Text fa_toRe) in
		let re = fa2re fa in
			RegularExpression.show re

	let testToGrammar () =
		let re = RegularExpression.make (Arg.Predef "re_simple") in
		let cfg = re2cfg re in
			ContextFreeGrammarBasic.show cfg

	let testToAutomaton () =
		let cfg = ContextFreeGrammarBasic.make (Arg.Predef "cfg_abc") in
		let fa = cfg2fa cfg in
			FiniteAutomaton.show fa

	let testToRe () =
		let cfg = ContextFreeGrammarBasic.make (Arg.Predef "cfg_abc") in
		let re = cfg2re cfg in
			RegularExpression.show re

	let runAll =
		if Util.testing active "PolyModel" then begin
			testSimplify ()
		end
end
