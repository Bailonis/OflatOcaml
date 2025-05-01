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
 * mar/2023 (cf) - First release.
 * may/2022 (amd) - Initial skeleton.
 *)

(*
 * Description: Pushdown automata functionality.
 *)

open BasicTypes

module PushdownAutomatonPrivate =
struct
	open PushdownAutomatonSupport

	(* TYPES *)
	type configuration =
		  state
		* symbol list
	type configurations = configuration set

	type path = configuration list
	type paths = path list

	type stack = symbol list

	type configuration_ =
		  state
		* stack
		* word
	type configurations_ = configuration_ set

	type searchTreeRef =
		  	NotAcceptLeafRef of configuration_
    	| AcceptLeafRef of configuration_
      | NodeRef of configuration_ * searchTreeRef set ref

	type searchTree =
		  	NotAcceptLeaf of configuration_
    	| AcceptLeaf of configuration_
      | Node of configuration_ * searchTree set
      | BestNode of configuration_ * searchTree set

	(* CONSTANTS *)
	let stackSpecialSymb: symbol = symb "z"
	let stackConverterSymb: symbol = symb "$"

	exception TooManyTries
	let maxTries = 100


	(* AUXILIARY *)

	let transitionGet1 trns = Set.map ( fun (a,_,_,_,_) -> a ) trns
	let transitionGet2 trns = Set.map ( fun (_,b,_,_,_) -> b ) trns
	let transitionGet3 trns = Set.map ( fun (_,_,c,_,_) -> c ) trns
	let transitionGet4 trns = Set.map ( fun (_,_,_,d,_) -> d ) trns
	let transitionGet345 trns = Set.map ( fun (_,_,c,d,e) -> (c, d, e) ) trns
	let transitionGet45 trns = Set.map ( fun (_,_,_,d,e) -> (d, e) ) trns
	let transitionGet5 trns = Set.map ( fun (_,_,_,_,e) -> e ) trns
	let transitionGet5Flat trns = Set.flatten (Set.map ( fun (_,_,_,_,e) -> Set.make e ) trns)

	let getStackSymbols trns =
		let stackSymbtoPutInStack =
			Set.fold_left ( fun acc symbList ->
				Set.union acc (Set.make symbList)
			) Set.empty (transitionGet5 trns)
		in
			Set.union (transitionGet2 trns) stackSymbtoPutInStack

	let configurationGet1 configs = Set.map ( fun (a,_) -> a ) configs
	let configurationGet2 configs = Set.map ( fun (_,b) -> b ) configs

	let configuration_Get1 configs = Set.map ( fun (a,_,_) -> a ) configs
    let configuration_Get2 configs = Set.map ( fun (_,b,_) -> b ) configs
    let configuration_Get3 configs = Set.map ( fun (_,_,c) -> c ) configs

    
	let validate (name: string) (pda: t): unit = (

		(* the alphabet must not contain "~" *)
		let validAlphabet = not (Set.belongs epsilon pda.inputAlphabet) in

		(* does initial state belong to the set of all states *)
		let validInitSt = Set.belongs pda.initialState pda.states in

		(* does initial stack symbol belong to the stack alphabet *)
		let validInitStackSymbol = Set.belongs pda.initialStackSymbol pda.stackAlphabet in

		(* are all accepted states members of all states *)
		let validAccSts = Set.subset pda.acceptStates pda.states in

		let fromSt = transitionGet1 pda.transitions in
		let syfromStack = transitionGet2 pda.transitions in
		let sy = transitionGet3 pda.transitions in
		let toSt = transitionGet4 pda.transitions in
		let sysToStack = transitionGet5Flat pda.transitions in
		let alpha = Set.add epsilon pda.inputAlphabet in

		(* do all transitions have states belonging to all states, symbols belonging to the alphabet and stackSymbol belonging to stack alphabet *)
		let validTrns =
			(Set.subset fromSt pda.states) &&
			(Set.subset syfromStack pda.stackAlphabet) &&
			(Set.subset sy alpha) &&
			(Set.subset toSt pda.states) &&
			(Set.subset sysToStack pda.stackAlphabet)
		in

		if not validAlphabet then
			Error.error name
				"The alphabet contains epsilon '~', and it should not" ();
			if not validInitSt then
				Error.error name
					"The initial state does not belong to the set of all states" ();
			if not validInitStackSymbol then
				Error.error name
					"The initial stack symbol does not belong to the stack alphabet" ();
			if not validAccSts then
				Error.error name
					"Some accept states do not belong to the set of all states" ();
			if not validTrns then
				Error.error name
					"Some transitions are invalid" ()
		)

	let rec fixedPointN (f: 'a -> 'a)(x: 'a) (moves: int): 'a =
		if moves = 0 then raise TooManyTries;
		let next = f x in
			if x = next then x
			else fixedPointN f next (moves-1)

	let fixedPointMaxTries f x = fixedPointN f x maxTries

	let getValidNonEmptyTransitions currentState topStackSymb trns: transitions =
		Set.filter (fun (a,b,c,_,_) -> a = currentState && b = topStackSymb && c <> epsilon) trns

	let mapStepsToConfigurationAndSymbol steps stack: (configuration * symbol) set =
		Set.map (fun ((symb, nextState, toPutInStack)) -> ((nextState, toPutInStack @ stack), symb)) steps

	let getNextConfigurationsWithSymbols trns (currentState, stack): (configuration * symbol) set =
		match stack with
		|	[] -> Set.make []
		| topStackSymb::restStack ->
				let nextSteps = transitionGet345 (getValidNonEmptyTransitions currentState topStackSymb trns) in
					mapStepsToConfigurationAndSymbol nextSteps restStack

	let getNextConfigurationsWithSymbols trns configurations: (configuration * symbol) set =
		Set.flatMap (getNextConfigurationsWithSymbols trns) configurations

	let addSymbToWords (w: symbol) (words: words): words =
		Set.map (fun word -> w::word ) words


	let mapStepsToConfiguration steps stack: configurations =
		Set.map (fun ((nextState, toPutInStack)) -> (nextState, toPutInStack @ stack)) steps

	let getValidTransitions currentState topStackSymb w trns: transitions =
		Set.filter (fun (a,b,c,_,_) -> a = currentState && b = topStackSymb && (c = w)) trns

	let getNextConfigurationsFromConfig w trns (currentState, stack): configurations =
		match stack with
		|	[] -> Set.make []
		| topStackSymb::restStack ->
				let nextSteps = transitionGet45 (getValidTransitions currentState topStackSymb w trns) in
					mapStepsToConfiguration nextSteps restStack

	let getNextConfigurations w trns configurations: configurations =
		Set.flatMap (getNextConfigurationsFromConfig w trns) configurations

	let addNextConfigurations w trns configurations: configurations =
		let nextConfigs = getNextConfigurations w trns configurations in
		Set.union nextConfigs configurations

	let exploreEmptyTransitions trns configurations: configurations =
		fixedPointMaxTries (addNextConfigurations epsilon trns) configurations

	let isInAcceptState configs acceptStates criteria: bool =
		if criteria then Set.inter (configurationGet1 configs) acceptStates <> Set.empty
		else Set.exists (fun stack -> stack = []) (configurationGet2 configs)

	let tickComputation w configurations transitions: configurations =
			let nextConfigs = getNextConfigurations w transitions configurations in
				exploreEmptyTransitions transitions nextConfigs

	let getInitialConfig initialState initialStackSymbol transitions =
		let initialConfig = Set.make [(initialState, [initialStackSymbol])] in
			exploreEmptyTransitions transitions initialConfig

	let generate length pda: words = (* ! AMD TROCAR !!! *)
		let rec gen n configuration =
			let configs = exploreEmptyTransitions pda.transitions (Set.make [configuration]) in
			if n = 0 then
				if isInAcceptState configs pda.acceptStates pda.criteria then Set.make [[]] else Set.empty
			else
				let newConfigsAndSymbols = getNextConfigurationsWithSymbols pda.transitions configs in
					let genX symb n config = addSymbToWords symb (gen (n-1) config) in (*exprimentar uniao para n-1*)
						Set.flatMap (fun (config, symb) -> genX symb n config) newConfigsAndSymbols
		in
			let initialConfig = (pda.initialState, [pda.initialStackSymbol]) in
				gen length initialConfig

	let printConfig (state,stack,word) =
		let open Util in
		Printf.printf "(%s, " (state2str state);
		print (List.map symb2str stack); print_string ", ";
		print_string (word2str word); print_string ")\n"

	let rec printSearchTree = function
		| NotAcceptLeaf c -> print_string "NotAcceptLeaf "; printConfig c
		| AcceptLeaf c -> print_string "AcceptLeaf "; printConfig c
		| Node (c,nodes) -> print_string "Node ";printConfig c; Set.iter printSearchTree nodes
		| BestNode (c,nodes) -> print_string "BestNode ";printConfig c; Set.iter printSearchTree nodes

	let configIsInAcceptState_ acceptStates criteria (state, stack, word): bool =
			word = [] && (if criteria then Set.belongs state acceptStates else stack = [])

	let configsAreInAcceptState_ acceptStates criteria configs: bool =
		Set.exists (configIsInAcceptState_ acceptStates criteria) configs

	let advanceOneTransition transitions (state, stack, word): configurations_ =
		let getNextConfig restStack wordLeft (_,_,_,nextState,toPutInStack) = (nextState, toPutInStack@restStack, wordLeft) in
		let buildNewTransitions restStack restWord validTrns = Set.map (getNextConfig restStack restWord) validTrns in
		let getNextConfigs inputSymbol restWord topStack restStack =
			let validTransitions = getValidTransitions state topStack inputSymbol transitions in
				buildNewTransitions restStack restWord validTransitions
	in
		match stack, word with
		| [], _ -> Set.empty
		| s::ss, [] -> getNextConfigs epsilon [] s ss
		| s::ss, w::ww ->
			let nextConfigConsumed = getNextConfigs w ww s ss in
			let nextConfigNotConsumed = getNextConfigs epsilon (w::ww) s ss  in
				Set.union nextConfigConsumed nextConfigNotConsumed

	let accept pda word: bool =
		let rec acceptRec configurations: bool =
			Set.match_ configurations
			(fun () -> false)
			(fun _ _ ->
				if configsAreInAcceptState_ pda.acceptStates pda.criteria configurations then true
				else
					let nextConfigs = Set.flatMap (advanceOneTransition pda.transitions) configurations in
					if Set.equals configurations nextConfigs then false
					else acceptRec nextConfigs
			)
		in
			let getInitialConfig = Set.make [(pda.initialState, [pda.initialStackSymbol], word)] in
				acceptRec getInitialConfig

	let configHasNoSymbolToConsume (_,_,word) = word=[]

	let buildEndNode acceptStates criteria transitions config =
		if configIsInAcceptState_ acceptStates criteria config then AcceptLeafRef(config)
        else if configHasNoSymbolToConsume config && (advanceOneTransition transitions config) = Set.empty then NotAcceptLeafRef(config)
        else NodeRef(config, ref (Set.make[]))

	let foundAcceptConfig searchTreeSet =
		Set.exists (fun node -> match node with | AcceptLeafRef _ -> true | _ -> false) searchTreeSet

	let filterSearchNode searchTreeSet =
		Set.filter (fun node -> match node with | NodeRef _ -> true | _ -> false) searchTreeSet

	exception ShouldNotHappen
	let getNodeElements = function
		| NodeRef(config, setNodes) -> (config, setNodes)
		| _ -> raise ShouldNotHappen

	let getNextConfigsPair searchTreeSet transitions =
		Set.map (fun tree ->
			let (config, _) = getNodeElements tree in
			let nextConfigs = advanceOneTransition transitions config in
            	(tree, nextConfigs)
		) searchTreeSet

	let buildTree acceptStates criteria transitions pairTreesAndNextConfigs =
		Set.flatMap (fun (tree, nextConfigs) ->
			let (_, setNodes) = getNodeElements tree in
			let newNodes = Set.map (buildEndNode acceptStates criteria transitions) nextConfigs in
            setNodes := newNodes;
            	newNodes
		) pairTreesAndNextConfigs

	let buildSearchTree (word: word) pda: searchTreeRef =
		let rec buildSearchTree (forest: searchTreeRef set) =
			Set.match_ forest
			(fun () -> ())
			(fun _ _ ->
				let pairTreesAndNextConfigs = getNextConfigsPair forest pda.transitions in
				let nextNodes = buildTree pda.acceptStates pda.criteria pda.transitions pairTreesAndNextConfigs in
				if foundAcceptConfig nextNodes || Set.equals forest nextNodes then ()
				else buildSearchTree (filterSearchNode nextNodes)
			)
		in
			let initialConfig = (pda.initialState, [pda.initialStackSymbol], word) in
			if configIsInAcceptState_ pda.acceptStates pda.criteria initialConfig then AcceptLeafRef(initialConfig)
			else
				let searchTree: searchTreeRef = NodeRef(initialConfig, ref (Set.make [])) in
					buildSearchTree (Set.make [searchTree]);
					searchTree

	let isBestNode = function | AcceptLeaf _ -> true | BestNode _ -> true | _ -> false
	let hasBestPath searchTreeSet =
    	Set.exists isBestNode searchTreeSet

	let rec mapBestPath: searchTreeRef -> searchTree = function
		| AcceptLeafRef c -> AcceptLeaf(c)
		| NotAcceptLeafRef c -> NotAcceptLeaf(c)
		| NodeRef(c, treeSet) ->
			let nextLayer = Set.map mapBestPath !treeSet in
			if hasBestPath nextLayer then BestNode(c, nextLayer) else Node(c, nextLayer)

	let getSearchTree word pda =
		buildSearchTree word pda |> mapBestPath

	let transformConfig (state,stack,word) = (state,stack)

	let getWordFromNode = function
		| AcceptLeaf((_,_,word)) -> word
		| NotAcceptLeaf((_,_,word)) -> word
		| Node((_,_,word), _) -> word
		| BestNode((_,_,word), _) -> word

	let getBestNodeAndWord setNodes =
    	let node = Set.find isBestNode setNodes in
    		(node, getWordFromNode node)

	let rec buildBestPath: searchTree -> path = function
		| AcceptLeaf(c) -> [transformConfig c]
		| NotAcceptLeaf(c) -> []
		| Node(c, treeSet) -> []
		| BestNode((_,_,word) as c, treeSet) ->
					let (nextBestNode, nextWord) = getBestNodeAndWord treeSet in
					if (word = nextWord) then buildBestPath(nextBestNode)
					else (transformConfig c)::buildBestPath(nextBestNode)

	let getBestPath word pda =
			getSearchTree word pda |> buildBestPath

	let getConfigsAndNextNodes: searchTree -> configuration * searchTree set = function
			| AcceptLeaf(c) -> (transformConfig c, Set.empty)
			| NotAcceptLeaf(c) -> (transformConfig c, Set.empty)
			| Node(c, treeSet) -> (transformConfig c, treeSet)
			| BestNode(c, treeSet) -> (transformConfig c, treeSet)

	let getAllConfigsAndFilterNextNodesThatConsumeSymbol nodes =
		Set.fold_left (fun (configsAcc,treeSetAcc) tree ->
			let (c,treeSet) = getConfigsAndNextNodes tree in
			let word = getWordFromNode tree in
			let nextTreeSet = Set.filter (fun t -> word <> getWordFromNode t) treeSet in
				(Set.add c configsAcc, Set.union nextTreeSet treeSetAcc)
		) (Set.empty, Set.empty) nodes

	let getNextEpsilonNodes nodes =
		Set.fold_left (fun treeSetAcc tree ->
			let (_,treeSet) = getConfigsAndNextNodes tree in
			let word = getWordFromNode tree in
			let nextTreeSet = Set.filter (fun t -> word = getWordFromNode t) treeSet in
				Set.union nodes (Set.union nextTreeSet treeSetAcc)
		) Set.empty nodes

	let rec getConfigsBySymbolConsumedStep (forest: searchTree set): configurations list =
		Set.match_ forest
		(fun () -> [])
		(fun _ _ ->
			let closureNodes = Set.fixedPoint getNextEpsilonNodes forest in
			let (configs, nextNodes) = getAllConfigsAndFilterNextNodesThatConsumeSymbol closureNodes in
					configs::(getConfigsBySymbolConsumedStep nextNodes)
		)

	let getConfigsPathBySymbolConsumedAndBestPath word pda: configurations list * path =
		let searchTree = getSearchTree word pda in
			let bestPath = buildBestPath searchTree in
				let configsBySymbolConsumedStep = getConfigsBySymbolConsumedStep (Set.make [searchTree]) in
					(configsBySymbolConsumedStep, bestPath)



	let rec generateUntil length pda: words =
		if length < 0 then Set.empty
		else Set.union (generate length pda) (generateUntil (length-1) pda)

	let transformPdaToAcceptStates pda: t =
		let buildNewTransitions (si: state) (sf: state): transitions = (*si estado inicial, sf estado final*)
			let initialTrsn: transition =
				(si, stackConverterSymb, epsilon, pda.initialState, [pda.initialStackSymbol; stackConverterSymb]) in
			let buildTrasitionToFinalState s =
				(state s, stackConverterSymb, epsilon, sf, [stackConverterSymb]) in
			let buildTransitions states = Set.map buildTrasitionToFinalState states in
				Set.add initialTrsn (buildTransitions pda.states)
		in
		let convertedPda: t = {
			inputAlphabet = pda.inputAlphabet;
			stackAlphabet = Set.add stackConverterSymb pda.stackAlphabet;
			states = Set.union (pda.states) (Set.make [state "Si"; state "Sf"]);
			initialState = state "Si";
			initialStackSymbol = stackConverterSymb;
			transitions = Set.union (pda.transitions) (buildNewTransitions (state "Si") (state "Sf"));
			acceptStates = Set.make [(state "Sf")];
			criteria = true
			}
		in
			if pda.criteria then pda else convertedPda

	let transformPdaToAcceptEmptyStack pda: t =
		let newStackAlphabet = Set.add stackConverterSymb pda.stackAlphabet in
		let buildNewTransitions si sf: transitions = (*si estado inicial, sf estado final*)
			let initialTrsn: transition = (si, stackConverterSymb, epsilon, pda.initialState, [pda.initialStackSymbol; stackConverterSymb]) in
			let buildFinalTransitionsToConsumeStack stackAlphabet: transitions =
				Set.map ( fun symbStack -> (sf, symbStack, epsilon, sf, []) ) stackAlphabet
			in
			let buildTrasitionsFromAcceptState acceptState: transitions =
				let symbsStack = getStackSymbols pda.transitions in
					Set.map ( fun symbStack -> (acceptState, symbStack, epsilon, sf, [symbStack])) symbsStack
			in
			let buildTransitions states: transitions = Set.flatten (Set.map buildTrasitionsFromAcceptState pda.acceptStates) in
				Set.union (Set.add initialTrsn (buildTransitions pda.states)) (buildFinalTransitionsToConsumeStack newStackAlphabet)
		in
		let convertedPda: t = {
			inputAlphabet = pda.inputAlphabet;
			stackAlphabet = newStackAlphabet;
			states = Set.union (pda.states) (Set.make [state "Si"; state "Sf"]);
			initialState = state "Si";
			initialStackSymbol = stackConverterSymb;
			transitions = Set.union (pda.transitions) (buildNewTransitions (state "Si") (state "Sf"));
			acceptStates = Set.empty;
			criteria = false
			}
		in
			if pda.criteria then convertedPda else pda

	let pda2fa pda: FiniteAutomaton.model =
		let transitionsFa trns = Set.map ( fun (s1,_,a,s2,_) -> (s1,a,s2) ) trns in
		let fa: FiniteAutomaton.t = {
				alphabet = pda.inputAlphabet;
				states = pda.states;
				initialState = pda.initialState;
				transitions = transitionsFa pda.transitions;
				acceptStates = pda.acceptStates
			} in
		new FiniteAutomaton.model (Arg.Representation fa)

(* AMD repetido *)
	let fa2pda (fa : FiniteAutomaton.t ): t =
		let upgradeTransitions trns = Set.map ( fun (s1,symb,s2) -> (s1,stackSpecialSymb,symb,s2,[stackSpecialSymb]) ) trns in
			{
				inputAlphabet = fa.alphabet;
				stackAlphabet = Set.make [stackSpecialSymb];
				states = fa.states;
				initialState = fa.initialState;
				initialStackSymbol = stackSpecialSymb;
				transitions = upgradeTransitions fa.transitions;
				acceptStates = fa.acceptStates;
				criteria = true
			}

	let reachable s pda: states =
		let fa : FiniteAutomaton.model = pda2fa pda in
		fa#reachable (s)

	let productive pda: states =
		let pdaTransformed = transformPdaToAcceptStates pda in
		let fa : FiniteAutomaton.model = pda2fa pdaTransformed in
		Set.inter fa#productive pda.states

	let getUsefulStates pda: states =
		let pdaTransformed = transformPdaToAcceptStates pda in
		let fa : FiniteAutomaton.model = pda2fa pdaTransformed in
		Set.inter fa#getUsefulStates pda.states

	let getUselessStates pda: states =
		let pdaTransformed = transformPdaToAcceptStates pda in
		let fa : FiniteAutomaton.model = pda2fa pdaTransformed in
		Set.inter fa#getUselessStates pda.states


	let cleanUselessStates pda: t =
		let getEquivalentTransitions (s1,sym,s2) =
			Set.filter (fun (a,b,c,d,e) -> a = s1 && c = sym && d = s2 ) pda.transitions in
		let getCleanedTransitions faCleanedTransitions =
			Set.flatMap getEquivalentTransitions faCleanedTransitions in
		let pdaTransformed = transformPdaToAcceptStates pda in
		let fa : FiniteAutomaton.model = pda2fa pdaTransformed in
		let faClean: FiniteAutomaton.model = fa#cleanUselessStates in
			{
				inputAlphabet = pda.inputAlphabet;
				stackAlphabet = pda.stackAlphabet;
				states = Set.inter faClean#representation.states pda.states;
				initialState = pda.initialState;
				initialStackSymbol = pda.initialStackSymbol;
				transitions = getCleanedTransitions faClean#representation.transitions;
				acceptStates = Set.inter fa#representation.acceptStates pda.acceptStates;
				criteria = pda.criteria
			}

(*trocar para a positiva AMD*)
	let isDeterministic pda: bool =

		(*returns the trasitions for a given state, stackSymbol and inputSymbol, including epsilon transitions*)
		let trnsFromStateAndSymbs st stackSymb inputSymb =
			Set.filter (fun (s1,stackS,symb,_,_) -> (st = s1) && (stackSymb = stackS) && (symb = inputSymb || symb = epsilon)) pda.transitions
		in

		(*Validates if there is more than one transition possible for a given state, stackSymbol*)
		let isnotDeterministicForStateAndStackSymbol st stackSymb =
			Set.exists (fun symb -> Set.size (trnsFromStateAndSymbs st stackSymb symb) > 1) pda.inputAlphabet
		in

		(*Validates if a state is non deterministic*)
		let isStateNonDeterministic st =
			Set.exists (fun stackSymb -> isnotDeterministicForStateAndStackSymbol st stackSymb) pda.stackAlphabet
		in
			not (Set.exists (fun st -> isStateNonDeterministic st) pda.states)

	let isFiniteAutomaton pda: bool =
		let validateTransition (_,a,_,_,b) = [a] = b in
			Set.for_all validateTransition pda.transitions	
end

module PushdownAutomatonJoao =
struct
	open PushdownAutomatonSupport
	open PushdownAutomatonPrivate

	(*CODIGO JP*)
	
	type path_ = configuration_ list
	type trail = configurations_ list


	let initialConfigs (pda: t) (w: word) : configurations_ =
			Set.make [(pda.initialState, [pda.initialStackSymbol], w)]

	let nextConfigs (pda: t) (st, sa, w) : configurations_ =
	let stackLeft = List.tl sa in
	let stackTop = List.hd sa in
	match w with
	| [] ->
		let empty = Set.filter(fun (st1, sa1, sy, _, _)->
			st1 = st && sy = epsilon && sa1 = stackTop
			) pda.transitions in 
				Set.map (fun (_,_,_,st2, sa2) -> (st2, sa2@stackLeft, [])) empty
	| x :: xs ->
		let nonEmpty = Set.filter (fun (st1, sa1, sy, _, _) ->
			st1 = st && sy = x && sa1 = stackTop
			) pda.transitions
		in
		let empty = Set.filter(fun (st1, sa1, sy, _, _)->
			st1 = st && sy = epsilon && sa1 = stackTop
			) pda.transitions 
		in
		let res1 = Set.map (fun (_, _, _, st2, sa2) -> 
			(st2, sa2@stackLeft, xs)
			) nonEmpty in
		let res2 = Set.map (fun (_, _, _, st2, sa2) -> 
			(st2, sa2@stackLeft, w)
			) empty in
		Set.union res1 res2

	let isAcceptingConfig (pda: t) (st, sa, w) : bool =
		if (pda.criteria) then (
				 w = [] && Set.belongs st pda.acceptStates
		)
		else (w = [] && sa = [])

	let nextConfigs2 pda (len: int) (st, sa, w) = 
		let stackTop = List.hd sa in
		let stackLeft = List.tl sa in
			let selected = Set.filter (fun (st1, sa1, _, _, _) -> 
				st1 = st && sa1 = stackTop) pda.transitions in
			Set.map (fun (_, _, sy, st2, sa2) -> (st2, sa2@stackLeft, if sy = epsilon then w else sy::w)) selected

	let isAcceptingConfig2 pda (st, sa, _) =
		if (pda.criteria) then Set.belongs st pda.acceptStates else sa = []

	let accept (pda: t) (w: word) : bool =
		Model.accept pda w initialConfigs nextConfigs isAcceptingConfig
	
	let acceptFull (pda: t) (w: word) : bool * path_ * trail =
		Model.acceptFull pda w initialConfigs nextConfigs isAcceptingConfig

	let getWord (_, _, w) = List.rev w;;

	let generate (pda: t) (len: int): words =
		Model.generate pda len initialConfigs nextConfigs2 isAcceptingConfig2 getWord

	(*generate*)
	
end

module PushdownAutomaton =
struct
	include PushdownAutomatonSupport
	include PushdownAutomatonPrivate

	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
	let make (arg: t Arg.alternatives): t = make arg validate

	(* Exercices support *)
	let checkProperty (pda: t) (prop: string) =
		match prop with
			| "true" -> true
			| _ -> Model.checkProperty prop
	let checkExercise ex pda = Model.checkExercise ex (accept pda) (checkProperty pda)	
	let checkExerciseFailures ex pda = Model.checkExerciseFailures ex (accept pda) (checkProperty pda)

	(* Ops *)
	let accept = accept
	let generate = generate	
	
	(* Class *)
	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model (make2 arg) as super
		(* Representation *)
			method representation: t = representation
		(* Kind *)
			method isPushdownAutomaton : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Ops *)
			method accept (w: word): bool = accept representation w
			method acceptFull (w: word) : bool * PushdownAutomatonJoao.path_ * PushdownAutomatonJoao.trail = 
				PushdownAutomatonJoao.acceptFull representation w
			method generate (length: int): words = generate length representation
			method generateUntil (length: int): words = generateUntil length representation
			method getSearchTree (w: word): searchTree = getSearchTree w representation
			method getBestPath (w: word): path = getBestPath w representation

			method getConfigsPathBySymbolConsumedAndBestPath word: configurations list * path =
				getConfigsPathBySymbolConsumedAndBestPath word representation

			method transformPdaToAcceptStates: model =
				let pda = transformPdaToAcceptStates representation in
					new model (Arg.Representation pda)

			method transformPdaToAcceptEmptyStack: model =
				let pda = transformPdaToAcceptEmptyStack representation in
					new model (Arg.Representation pda)

			method reachable (s: state): states = reachable s representation
			method productive: states = productive representation
			method getUsefulStates: states = getUsefulStates representation
			method getUselessStates: states = getUselessStates representation
			method cleanUselessStates: model =
				let pda = cleanUselessStates representation in
					new model(Arg.Representation pda)
			method areAllStatesUseful: bool =
				let usefullStates = self#getUsefulStates in
					Set.size representation.states = Set.size usefullStates
			method isDeterministic: bool = isDeterministic representation
			method isFiniteAutomaton: bool = isFiniteAutomaton representation
		(* Exercices support *)
			method checkProperty (prop: string) = Util.println["WWW"]; checkProperty representation prop
		(* Learn-OCaml support *)
			method moduleName = moduleName
			method xTypeName = xTypeName
			method xTypeDeclString : string = prelude
			method toDisplayString (name: string): string = solution name self#representation
			method example : JSon.t = example
	end
end

#endif
