#ifdef ALL

(*
 * ContextFreeGrammarLR.ml
 *
 * This file is part of the OCamlFlat library
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
 *  Written by Bernardo Sousa (br)
 *)

(*
 * ChangeLog:
 * sep/2022 (br) - Bug fixes.
 * july/2022 (br) - Added step-by-step table creation.
 * may/2022 (br) - Most of the LR theory implemented.
 * mar/2022 (amd/br) - Skeleton.
 *)

(*
 * Description: A very simple parser for CFG syntax.
 *)
 
open BasicTypes
open ContextFreeGrammarBasic  

module LRAux =
struct
	let word s = str2word s
		
	let rec nats n = if n = 0 then [] else nats(n-1) @ [string_of_int (n-1)]
	
	let rec pop n l (*uses reverse stack and removes n heads from stack *)= 
		match l with
		| [] -> []
		| x::xs -> if(n>0) then pop (n-1) xs else x::pop n xs  
	
	
	let getTail l = (*remove head from list *)
		match l with
		| [] -> []
		|_::xs -> xs
		
	let rec rev l =
		match l with
		| [] -> []
		| x::xs -> (rev xs) @ x
	
	
end	

module LR0Grammar =
struct
	open LRAux
	type t = ContextFreeGrammarBasic.t

	type lr0Item = {head:symbol; body1:symbol list; body2:symbol list}		
	type lr0State = lr0Item set
	type lr0Diagram = lr0State set * (lr0State * symbol * lr0State ) set
	
	type stateName = string
	
	type lr0StateId = stateName * lr0State 
	type lr0DiagramId = lr0StateId set * (lr0StateId * symbol * lr0StateId ) set
	
	type lr0Action = Accept | Shift | Reduce of rule 
	type lr0TableEntry = stateName * (symbol * stateName) set * lr0Action
	type lr0Table = lr0TableEntry set
	
	let rule2Item (rule: rule) : lr0Item = (* converte uma regra num item novo, com o ponto á esquerda do corpo desse item *)
		{head = rule.head; body1 = []; body2 = rule.body} 
		
	
	let kernelAdvanceItem {head=h; body1=b1; body2=b2} = (* função auxiliar para avançar o ponto de um item em um simbolo para o nucleo do proximo estado. Ex: A ->.ab para A -> a.b *)
		match b2 with
		| [] -> Error.fatal "kernelAdvanceItem: Este caso nem deve ser alcançavel"
		| x::xs -> {head = h; body1 = b1 @ [x]; body2 = xs} 
	
	

	
		
	let getDirector {head=_; body1=_; body2=b2} = (* obtem o simbolo diretor de um item *)
		match b2 with 
			| [] -> epsilon (* epsilon, aka no symbol *) 
			| x::_ -> x	
			
			
		
			
	let getDirectors state = (* Aplica a função getDirector a todos os itens de um dado estado*)
		Set.filter (fun d-> d <> epsilon)(Set.map getDirector state)
	
		
		
	let getRulesWithThisHead rules director = (* recebe o conjunto de regras da gramática e filtra esse conjunto para obter as regras cuja cabeça tem aquele simbolo diretor *)
		Set.filter (fun {head = h; body =_} -> h = director) rules 
		
	
	let diagramsJoin2 (s0,t0) (s1,t1) = (Set.union s0 s1, Set.union t0 t1) (* juntar dois diagramas LR0 para obter um diagrama LR0 resultante da união *)	
	
	let rec diagramsJoinList l : lr0Diagram = (* Juntar um conjunto de diagramas para produzir o diagrama LR0, cada diagrama desta lista corresponde a um estado rescrito como diagrama *)
		match l with
		| [] -> (Set.empty , Set.empty) 
		| d::ds -> diagramsJoin2 d (diagramsJoinList ds)
	
	
	let isNextSymbolNotAVariable {head=h; body1=b1; body2=b2} (cfg:t)=
		if(List.length b2 = 0) then true
		else
			if(Set.belongs (List.hd b2) cfg.variables) then false else true
	
	let isCompleteItem {head=h; body1=b1; body2=b2} =
		b2 = []
	
	let isStateInConflict lr0State cfg = 
		let completeItems = Set.filter(isCompleteItem) lr0State in
		if(Set.size completeItems < 1 ) then false
		else if(Set.size completeItems > 1 ) then true
		else
			let itemsProneToConflict = Set.filter(fun it -> isNextSymbolNotAVariable it cfg) lr0State in
			if(Set.size itemsProneToConflict > 1) then true else false
	
	let makeLR0DiagramId diagram : lr0DiagramId (* Cria etiquetas para os estados e os mesmos estados contidos nas transições do diagrama*) =
		let (states,transitions) = diagram in
		let dictionary = List.combine (Set.toList states) (nats (Set.size states)) in
		let statesId = Set.map (fun s -> (List.assoc s dictionary,s) ) states in
		let transitionsId = Set.map (fun (a,b,c) -> ((List.assoc a dictionary, a), b,(List.assoc c dictionary, c))) transitions in
			(statesId, transitionsId)
	
	
	let makeLR0TableEntry (id, lr0State) (cfg:t) transitions = 
		let stateTransitions = Set.filter (fun ((a,_),_,_)-> a = id) transitions in
			if Set.size stateTransitions = 0 then
				let {head = h;body1 = b1;body2 = b2} = List.hd (Set.toList lr0State) in
					if h = cfg.initial then 
						(id,Set.empty,Accept)
					else
						(id,Set.empty,Reduce ({head = h;body = b1}))			
			else  
				let nextShifts = Set.map (fun (a,b,(cId,c)) -> (b,cId)) stateTransitions in
					(id, nextShifts, Shift)
		
	(* falta uma função para aceitar/recusar palavra usando a tabela *)
	
	(*pre: isLR0 cfg *)
	let makeLR0Table (labeledDiagram:lr0DiagramId) cfg : lr0Table = (* recebe um diagrama numerado e constroi a tabela de parsing a partir das transições *) 
		let (statesId, transitionsId) = labeledDiagram in
			Set.map (fun s -> makeLR0TableEntry s cfg transitionsId) statesId
	
	
	let startRules (cfg: t) =
		let initial = cfg.initial in
		let rules = cfg.rules in
			Set.filter (fun {head=h; body=_} -> h = initial) rules
			
		
		
	let lr0StateClosureStep (cfg: t) currentItems = (* Create items for current directors *)
		let directors = getDirectors currentItems in
		let varDirectors = Set.inter directors cfg.variables in
		let newRules = Set.flatMap (fun d -> getRulesWithThisHead cfg.rules d) varDirectors in
		let newItems = Set.map rule2Item newRules in
			Set.union currentItems newItems 
		
		
	let rec lr0StateClosure cfg currentItems : lr0State = (* Create all items for a singular state *)
		let next = lr0StateClosureStep cfg currentItems in
		let next2 = Set.union currentItems next in
			if Set.size next2 = Set.size currentItems then next2
			else lr0StateClosure cfg next2


		
	let makeSingularNextLR0Diagram (cfg:t) prevState symbol : lr0Diagram = (* Creates a diagram containing only 1 state using the previous state and the transition symbol*)
		let items4Kernel = Set.filter (fun it -> getDirector it = symbol) prevState in (* falta avançar o ponto *)
		let kernel = Set.map (kernelAdvanceItem) items4Kernel in
		let closure = lr0StateClosure cfg kernel in
			(Set.make [prevState; closure], Set.make [(prevState ,symbol , closure )])
					

	
	let makeNextLR0Diagram (cfg:t) prevState : lr0Diagram = (* For each director symbol on the previous state, create a diagram and join all obtained diagrams into a single diagram*)
		let dirs = getDirectors prevState in
		let diagrams = Set.map (fun d -> makeSingularNextLR0Diagram cfg prevState d) dirs in
			diagramsJoinList (Set.toList diagrams) 

			
		
	let makeNextLR0DiagramAll (cfg:t) states : lr0Diagram = (* build the diagram using the initial state, then use the makeNextLR0Diagram function to calculate all states obtainable from the initial state*)
		let diagrams = Set.map (fun s -> makeNextLR0Diagram cfg s) states in
			diagramsJoinList (Set.toList diagrams)
			
	
	let makeFirstLR0Diagram (cfg:t) : lr0Diagram = (* O primeiro estado tem um procedimento de criação um pouco differente *) 
		let kernel = Set.map rule2Item (startRules cfg) in
		let closure = lr0StateClosure cfg kernel in
		(Set.make [closure], Set.empty)
		
		(*Set.make [closure] (* apesar de ser criado um par, nesta função só se cria o conjunto de items, o conjunto vazio das transições vazias é criado no makeLR0Diagram *) *)
		

	
	let rec makeLR0DiagramX (cfg:t) diagram = (* função auxiliar que irá produzir o diagrama LR0 *)
		let (states,transitions) : lr0Diagram = diagram in 
		let next = makeNextLR0DiagramAll cfg states in
		let next2 = diagramsJoin2 next (states,transitions) in
		let (states2,transitions2) = next2 in
			if Set.size states = Set.size states2 && Set.size transitions = Set.size transitions2 then next2
			else makeLR0DiagramX cfg next2 
					 

	let makeLR0Diagram (cfg:t) = makeLR0DiagramX cfg (makeFirstLR0Diagram cfg)  (* ponto de partida na construlão do diagrama LR0 *)
	
	(*
	type stackEntry = StateEntry of stateName | SymbolEntry of symbol
	
	let getState e =
		match e with
		| StateEntry s -> s
		| _ -> Error.fatal "getState: desnecessário" 
		
	let getSymbol s =
		match s with
		| SymbolEntry s -> s
		| _ -> Error.fatal "getState: desnecessário" 
	*)	
	let rec parseOperationV2 lr0Table word revStack (cfg:t) = 
		let currentState = int_of_string (List.hd revStack) in 
		let (id,shifts,action) = Set.nth lr0Table currentState in (* get corresponding table entry *)	
		match action with
		| Shift -> 
			begin
				match word with
				| [] -> false
				| s::_ -> 
					if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
						let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
							if(Set.size targetShifts = 0) then false
							(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
							(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
							else
								let (nextSymbol,nextState) = Set.nth targetShifts 0 in
								let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
									parseOperationV2 lr0Table (getTail word) nextRevStack cfg
					else
						Error.fatal "singleParseOperation: este simbolo não pertence ao alfabeto desta gramatica"
			end
		| Accept -> 
			word = [dollar]	
		| Reduce({head = h;body = b}) -> 
			let popNumber = List.length b in
			let nextRevStack = pop (popNumber*2) revStack in
			let wordWithAddedHead = [h] @ word in
				parseOperationV2 lr0Table (wordWithAddedHead) nextRevStack cfg (*Add the variable, aka head of the reduction rule, to the word being processed *)
					
	
	(* pre: isLR0 cfg 
	   pre: isWordValid word cfg *)
	let acceptWordLR0V2 (word:symbol list) cfg : bool = 
		let lr0Table = makeLR0Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg in
		let revStack = ["0"] in (*char list due to mix of numbers and symbols *) 
			parseOperationV2 lr0Table (word @ [dollar]) revStack cfg	
		

	(* let nextStack = [StateEntry nextState; StateSymbol nextSymbol] @ stack in *)
	
	let rec parseOperation lr0Table word stateStack symbolStack (cfg:t) = 
		let currentState = int_of_string (List.hd stateStack) in 
		let (id,shifts,action) = Set.nth lr0Table currentState in (* get corresponding table entry *)	
		match action with
		| Shift -> 
			begin
				match word with
				| [] -> false
				| s::_ -> 
					if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
						let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
							if(Set.size targetShifts = 0) then false
							(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
							(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
							else
								let (nextSymbol,nextState) = Set.nth targetShifts 0 in
								let nextStateStack = [nextState] @ stateStack in
								let nextSymbolStack = [nextSymbol] @ symbolStack in
									parseOperation lr0Table (getTail word) nextStateStack nextSymbolStack cfg
					else
						Error.fatal "singleParseOperation: este simbolo não pertence ao alfabeto desta gramatica"
			end
		| Accept -> 
			word = [dollar]	
		| Reduce({head = h;body = b}) -> 
			let popNumber = List.length b in
			let nextStateStack = (pop popNumber stateStack) in
			let nextSymbolStack = (pop popNumber symbolStack) in
			let wordWithAddedHead = [h] @ word in
				parseOperation lr0Table (wordWithAddedHead) nextStateStack nextSymbolStack cfg (*Add the variable, aka head of the reduction rule, to the word being processed *)
					
	
	(* pre: isLR0 cfg 
	   pre: isWordValid word cfg *)
	let acceptWordLR0 (word:symbol list) cfg : bool = 
		let lr0Table = makeLR0Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
			parseOperation lr0Table (word @ [dollar]) stateRevStack symbolRevStack cfg
			
	(* Added functions to provide a step-by step LR0 visualization of accepting *)

	type lr0TableStep = symbol list * string list * symbol list * lr0Table * bool
	
	let acceptWordLR0Init (word:symbol list) cfg : lr0TableStep =
		let lr0Table = makeLR0Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
		let valid = true in
		let initStep = ((word @ [dollar]),stateRevStack,symbolRevStack,lr0Table,valid) in
			initStep
	
	let parseStepLR0Operation (step:lr0TableStep) (cfg:t) : lr0TableStep = 
		let (word, stateStack, symbolStack, lr0Table, valid) = step in
		let currentState = int_of_string (List.hd stateStack) in 
		let (id,shifts,action) = Set.nth lr0Table currentState in (* get corresponding table entry *)	
		match action with
		| Shift -> 
			begin
				match word with
				| [] -> (word, stateStack, symbolStack, lr0Table, false)
				| s::_ -> 
					if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
						let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
							if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, lr0Table, false)
							(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
							(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
							else
								let (nextSymbol,nextState) = Set.nth targetShifts 0 in
								let nextStateStack = [nextState] @ stateStack in
								let nextSymbolStack = [nextSymbol] @ symbolStack in
								let nextStep = ((getTail word), nextStateStack, nextSymbolStack, lr0Table, valid) in
									nextStep
					else
						Error.fatal "singleParseOperation: este simbolo não pertence ao alfabeto desta gramatica"
			end
		| Accept -> 
			if (word = [dollar]) then
					((getTail word), stateStack, symbolStack, lr0Table, valid)
				else 
					((getTail word), stateStack, symbolStack, lr0Table, false)
		| Reduce({head = h;body = b}) -> 
			let popNumber = List.length b in
			let nextStateStack = (pop popNumber stateStack) in
			let nextSymbolStack = (pop popNumber symbolStack) in
			let wordWithAddedHead = [h] @ word in
			let nextStep = (wordWithAddedHead, nextStateStack, nextSymbolStack, lr0Table, valid) in
				nextStep
		
	
	
	
		
	let acceptWordLR0Step (step:lr0TableStep) cfg : lr0TableStep = 
			parseStepLR0Operation step cfg
			
			
	(* updated acceptStep, you can use the previous version if you want to split the stack contaning both state and symbols*)
	
	type truelr0TableStep = symbol list * string list * lr0Table * string
	
	let acceptWordLR0InitV2 (word:symbol list) cfg : truelr0TableStep =
		let lr0Table = makeLR0Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg in
		let revStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let valid = "Ongoing" in
		let initStep = ((word @ [dollar]),revStack,lr0Table,valid) in
			initStep
	
	let parseStepLR0OperationV2 (step:truelr0TableStep) (cfg:t) : truelr0TableStep = 
		let (word, revStack, lr0Table, valid) = step in (* if you want to print use this: print_string (List.hd revStack ^ "\n"); *)
		let currentState = int_of_string (List.hd revStack) in 
		let (id,shifts,action) = Set.nth lr0Table currentState in (* get corresponding table entry *)	
		match action with
		| Shift -> 
			begin
				match word with
				| [] -> (word, revStack, lr0Table, "Rejeitada")
				| s::_ -> 
					if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
						let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
							if(Set.size targetShifts = 0) then (word, revStack, lr0Table, "Rejeitada")
							(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
							(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
							else
								let (nextSymbol,nextState) = Set.nth targetShifts 0 in
								let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
								let nextStep = ((getTail word), nextRevStack, lr0Table, valid) in
									nextStep
					else
						(word, revStack, lr0Table, "Rejeitada")
			end
		| Accept -> 
			if (word = [dollar]) then
					((getTail word), [symb2str cfg.initial], lr0Table, "Aceite")
				else 
					((word), revStack, lr0Table, "Rejeitada")
		| Reduce({head = h;body = b}) -> 
			let popNumber = List.length b in
			let nextRevStack = pop (popNumber*2) revStack in
			let wordWithAddedHead = [h] @ word in
			let nextStep = (wordWithAddedHead, nextRevStack, lr0Table, valid) in
				nextStep
	
		
	let acceptWordLR0StepV2 (step:truelr0TableStep) cfg : truelr0TableStep = 
			parseStepLR0OperationV2 step cfg
			
		
	let isLR0 cfg = (* verificar se a gramatica é lr0, ou seja, em todos os estados com items completos, não existem simbolos não terminais á direita de um ponto (item não completo *)
		let (states,transitions) = makeLR0Diagram cfg in
		let conflictItemStates = Set.filter(fun s -> isStateInConflict s cfg) states in
			if(Set.size conflictItemStates > 0) then false else true
	
	let getLR0DiagramId cfg : lr0DiagramId =
		makeLR0DiagramId (makeLR0Diagram cfg)
		
	let getLR0Table cfg : lr0Table =
		makeLR0Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg 
		
	(* -------extended LR0 for clarity----------- Allows LR0 Tables to display multiple actions in each state line.*)	
	
	let isCompleteLR0Item (it:lr0Item) =
		it.body2 = []

	let countCompleteLR0Items lr0State = 
		let completeItems = Set.filter(isCompleteLR0Item) lr0State in
			Set.size completeItems	
	
	let buildLR0ReductionActionsForOne item cfg = (* Warning, input must only contain complete items *)
		if(isCompleteItem item) then
			Reduce ({head = item.head;body = item.body1})
		else
			Shift (* this should not happen *)

	let buildLR0ReductionActions completeItems cfg = 
		Set.map(fun it -> (buildLR0ReductionActionsForOne it cfg) ) completeItems
	
			
	let buildLR0MixedActionsForOne item cfg = 
		if(isCompleteItem item) then
			Reduce ({head = item.head;body = item.body1})
		else
			Shift
	

	let buildLR0MixedActions (items:lr0State) cfg =
		Set.map(fun it -> (buildLR0MixedActionsForOne it cfg) ) items
	
	
	
	
	type lr0TableEntryExt = stateName * (symbol * stateName) set * lr0Action set
	type lr0TableExt = lr0TableEntryExt set
		
	let makeLR0TableEntryExt (id, lr0State) (cfg:t) transitions = 
		let stateTransitions = Set.filter (fun ((a,_),_,_)-> a = id) transitions in
			if Set.size stateTransitions = 0 then
				let {head = h;body1 = b1;body2 = b2} = List.hd (Set.toList lr0State) in
					if h = cfg.initial then 
							(id,Set.empty,Set.make [Accept])
					else
						let lr0Actions : lr0Action set = buildLR0ReductionActions lr0State cfg in
							(id,Set.empty, lr0Actions)	
			else  
				let nextShifts = Set.map (fun (a,b,(cId,c)) -> (b,cId)) stateTransitions in
					if(countCompleteLR0Items lr0State = 0) then (* Não existem reducoes *)
							(id, nextShifts, Set.make[Shift])
					else (* Existem reducoes e transferencias *)
						let lr0Actions = buildLR0MixedActions lr0State cfg in
							(id, nextShifts, lr0Actions)	
		

	let makeLR0TableExt (labeledDiagram:lr0DiagramId) cfg : lr0TableExt = (* recebe um diagrama numerado e constroi a tabela de parsing a partir das transições *) 
		let (statesId, transitionsId) = labeledDiagram in
			Set.map (fun s -> makeLR0TableEntryExt s cfg transitionsId) statesId
			
	let getLR0TableExt cfg : lr0TableExt =
		makeLR0TableExt (makeLR0DiagramId (makeLR0Diagram cfg)) cfg 

		
end		
	(* ----- SLR1 -----*)
module SLR1Grammar =
struct
	open LRAux
	open LR0Grammar
	type t = ContextFreeGrammarBasic.t
	
(*
	type lr0Item = LR0Grammar.lr0Item		
	type lr0State = LR0Grammar.lr0State	
	type lr0Diagram = LR0Grammar.lr0Diagram	
	
	type stateName = LR0Grammar.stateName
	
	type lr0StateId = LR0Grammar.lr0StateId	
	type lr0DiagramId = LR0Grammar.lr0DiagramId		
*)
	
	type slr1Action = Accept | Shift | Reduce of rule 
	type slr1TableEntry = stateName * (symbol * stateName) set * (symbol * slr1Action set ) set
	type slr1Table = slr1TableEntry set
	
	let kernelAdvanceItem {head=h; body1=b1; body2=b2} = (* função auxiliar para avançar o ponto de um item em um simbolo para o nucleo do proximo estado. Ex: A ->.ab para A -> a.b *)
		match b2 with
		| [] -> Error.fatal "kernelAdvanceItem: Este caso nem deve ser alcançavel"
		| x::xs -> {head = h; body1 = b1 @ [x]; body2 = xs} 
	
	let getNextSymbolForLR0Item (it:lr0Item)  =
		match it.body2 with
		| [] -> epsilon
		| x::xs -> x
	
	(*
	let follow w = (* Injected follow to test SLR1 grammars*)
		match w with
		| [] -> Set.make [dollar] (* Não deve acontecer*)
		| x::xs -> 
			if(x = symb "A") then Set.make [symb "c"]
			else if(x = symb "B") then Set.make [symb "d"]
			else if(x = symb "X") then Set.make [dollar]
			else Set.make [dollar]
    *)
			
	let followSetForSLR1Item it cfg =
		ContextFreeGrammarBasic.follow it.head false cfg
		
	let isCompleteLR0Item (it:lr0Item) =
		it.body2 = []

	let countCompleteLR0Items lr0State = 
		let completeItems = Set.filter(isCompleteLR0Item) lr0State in
			Set.size completeItems	
			
	let buildSLR1ReductionActionsForOne completeItems symbol cfg = (* Warning, input must only contain complete items *)
		let reductionItems = Set.filter(fun it -> Set.belongs symbol (followSetForSLR1Item it cfg)) completeItems in
			Set.map (fun it -> Reduce ({head = it.head;body = it.body1}) ) reductionItems	
			


	let buildSLR1ReductionActions completeItems alphabet cfg= 
		Set.map(fun symbol -> (symbol, buildSLR1ReductionActionsForOne completeItems symbol cfg) ) alphabet
	
	
	
	let buildSLR1ShiftActionsForOne items symbol : slr1Action set = 
		let shiftItems = Set.filter(fun it -> (getNextSymbolForLR0Item it) = symbol) items in
		if(Set.size shiftItems > 0) then
			Set.make [Shift]
		else
			Set.empty
			


	let buildSLR1ShiftActions completeItems alphabet = 
		Set.map(fun symbol -> (symbol, buildSLR1ShiftActionsForOne completeItems symbol) ) alphabet
	
			
	let buildSLR1MixedActionsForOne items symbol cfg= 
		let reductionItems = Set.filter(fun it -> (Set.belongs symbol (followSetForSLR1Item it cfg)) && isCompleteLR0Item it) items in
		let fixedreductionItems = Set.filter (fun it-> it.head != cfg.initial) reductionItems in (* Porque este fixed? R: Porque os items de accept podem ser interpretados como reduções. logo vamos ter de separar estes items *)
		let acceptItems = Set.filter (fun it -> it.head = cfg.initial && symbol = dollar && isCompleteLR0Item it && (Set.belongs it fixedreductionItems) = false) items in
		let shiftItems = Set.filter(fun it -> (getNextSymbolForLR0Item it) = symbol) items in
		let reductionEntries = Set.map (fun it -> Reduce ({head = it.head;body = it.body1}) ) fixedreductionItems in
		
		if(Set.size acceptItems > 0) then
			if(Set.size shiftItems > 0) then
				Set.union (Set.union (Set.make [Shift]) reductionEntries) (Set.make [Accept])
			else
				Set.union reductionEntries (Set.make [Accept])
		else	
			if(Set.size shiftItems > 0) then
				Set.union (Set.make [Shift]) reductionEntries
			else
				reductionEntries

	let buildSLR1MixedActions (items:lr0State) alphabet cfg= (* True build function - prototype *) (* transformar na forma do buildLR1ReductionActions *)
		Set.map(fun symbol -> (symbol, buildSLR1MixedActionsForOne items symbol cfg) ) alphabet
	
			
			
	let makeSLR1TableEntry (id, lr0State) (cfg:t) transitions = 
		let stateTransitions = Set.filter (fun ((a,_),_,_)-> a = id) transitions in
			if Set.size stateTransitions = 0 then
				let {head = h;body1 = b1;body2 = b2} = List.hd (Set.toList lr0State) in
					if h = cfg.initial then 
						let slr1Actions : (symbol * slr1Action set) set = Set.make [dollar,Set.make [Accept]] in
							(id,Set.empty,slr1Actions)
					else
						let completeAlphabet = Set.add dollar cfg.alphabet in (* Se o $, final da palavra, não estiver no alfabeto da gramática *)
						let slr1Actions : (symbol * slr1Action set) set = buildSLR1ReductionActions lr0State completeAlphabet cfg in
							(id,Set.empty, slr1Actions)	
			else  
				let nextShifts = Set.map (fun (a,b,(cId,c)) -> (b,cId)) stateTransitions in
					if(countCompleteLR0Items lr0State = 0) then (* Não existem reducoes *)
						let slr1Actions = buildSLR1ShiftActions lr0State cfg.alphabet in
							(id, nextShifts, slr1Actions)
					else (* Existem reducoes e transferencias *)
						let completeAlphabet = Set.add dollar cfg.alphabet in (* Se o $, final da palavra, não estiver no alfabeto da gramática *)
						let slr1Actions = buildSLR1MixedActions lr0State completeAlphabet cfg in
							(id, nextShifts, slr1Actions)	
		
	
	(*pre: isLR1 cfg *)

	let makeSLR1Table (labeledDiagram:lr0DiagramId) cfg : slr1Table = (* recebe um diagrama numerado e constroi a tabela de parsing a partir das transições *) 
		let (statesId, transitionsId) = labeledDiagram in
			Set.map (fun s -> makeSLR1TableEntry s cfg transitionsId) statesId
			
			
		
		
	let rec parseOperationSLR1 slr1Table word stateStack symbolStack (cfg:t) = 
		let currentState = int_of_string(List.hd stateStack) in 
		let (id,shifts,actionSet) = Set.nth slr1Table currentState in (* get corresponding table entry *)
		let topSymbol = List.nth word 0 in
			if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
				let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
					if(Set.size targetShifts = 0) then false
					else
						let (nextSymbol,nextState) = Set.nth targetShifts 0 in
						let nextStateStack = [nextState] @ stateStack in
						let nextSymbolStack = [nextSymbol] @ symbolStack in
							parseOperationSLR1 slr1Table (getTail word) nextStateStack nextSymbolStack cfg
			else 
				let peekedSymbol = List.nth word 0 in
				let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
				let nEntries = Set.size peekedsymbolAndActions in
					if nEntries = 0 then 
						false
					else if nEntries > 1 then
						Error.fatal "ParseOperationLR1: conflito"
					else
						let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
						let action = Set.hd actions in
						match action with
						| Shift -> 
							begin
								match word with
								| [] -> false
								| s::_ -> 
									if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
										let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
											if(Set.size targetShifts = 0) then false
											(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
											(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
											else
												let (nextSymbol,nextState) = Set.nth targetShifts 0 in
												let nextStateStack = [nextState] @ stateStack in
												let nextSymbolStack = [nextSymbol] @ symbolStack in
													parseOperationSLR1 slr1Table (getTail word) nextStateStack nextSymbolStack cfg
									else
										Error.fatal "ParseOperationSLR1: este simbolo não pertence ao alfabeto desta gramatica"
							end
						| Accept -> 
							word = [dollar]	
						| Reduce({head = h;body = b}) -> 
							let popNumber = List.length b in
							let nextStateStack = (pop popNumber stateStack) in
							let nextSymbolStack = (pop popNumber symbolStack) in
							let wordWithAddedHead = [h] @ word in
								parseOperationSLR1 slr1Table (wordWithAddedHead) nextStateStack nextSymbolStack cfg (*Add the variable, aka head of the reduction rule, to the word being processed *)
			
	(* pre: isSLR1 cfg 
	   pre: isWordValid word cfg *)
	let acceptWordSLR1 (word:symbol list) cfg : bool = 
		let slr1Table = makeSLR1Table (LR0Grammar.makeLR0DiagramId (LR0Grammar.makeLR0Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
			parseOperationSLR1 slr1Table (word @ [dollar]) stateRevStack symbolRevStack cfg	
			
	(* Added functions to provide a step-by step SLR1 visualization of accepting *)

	type slr1TableStep = symbol list * string list * symbol list * slr1Table * bool
	
	let acceptWordSLR1Init (word:symbol list) cfg : slr1TableStep =
		let slr1Table = makeSLR1Table (LR0Grammar.makeLR0DiagramId (LR0Grammar.makeLR0Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
		let valid = true in
		let initStep = ((word @ [dollar]),stateRevStack,symbolRevStack,slr1Table,valid) in
			initStep
	
	let parseStepSLR1Operation (step:slr1TableStep) (cfg:t) : slr1TableStep = 
		let (word, stateStack, symbolStack, slr1Table, valid) = step in
		let currentState = int_of_string(List.hd stateStack) in 
		let (id,shifts,actionSet) = Set.nth slr1Table currentState in (* get corresponding table entry *)
		let topSymbol = List.nth word 0 in
			if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
				let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
					if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, slr1Table, false)
					else
						let (nextSymbol,nextState) = Set.nth targetShifts 0 in
						let nextStateStack = [nextState] @ stateStack in
						let nextSymbolStack = [nextSymbol] @ symbolStack in
						let nextStep = ((getTail word), nextStateStack, nextSymbolStack, slr1Table, valid) in
							nextStep
			else 
				let peekedSymbol = List.nth word 0 in
				let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
				let nEntries = Set.size peekedsymbolAndActions in
					if nEntries = 0 then 
						(word, stateStack, symbolStack, slr1Table, false)
					else if nEntries > 1 then
						Error.fatal "parseStepSLR1Operation: conflito"
					else
						let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
						let action = Set.hd actions in
						match action with
						| Shift -> 
							begin
								match word with
								| [] -> (word, stateStack, symbolStack, slr1Table, false)
								| s::_ -> 
									if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
										let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
											if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, slr1Table, false)
											(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
											(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
											else
												let (nextSymbol,nextState) = Set.nth targetShifts 0 in
												let nextStateStack = [nextState] @ stateStack in
												let nextSymbolStack = [nextSymbol] @ symbolStack in
												let nextStep = ((getTail word), nextStateStack, nextSymbolStack, slr1Table, valid) in
													nextStep
									else
										Error.fatal "parseStepSLR1Operation: este simbolo não pertence ao alfabeto desta gramatica"
							end
						| Accept -> 
							if (word = [dollar]) then
								((getTail word), stateStack, symbolStack, slr1Table, valid)
							else 
								((getTail word), stateStack, symbolStack, slr1Table, false)
						| Reduce({head = h;body = b}) -> 
							let popNumber = List.length b in
							let nextStateStack = (pop popNumber stateStack) in
							let nextSymbolStack = (pop popNumber symbolStack) in
							let wordWithAddedHead = [h] @ word in
							let nextStep = (wordWithAddedHead, nextStateStack, nextSymbolStack, slr1Table, valid) in
								nextStep
		
	
	
	
		
	let acceptWordSLR1Step (step:slr1TableStep) cfg : slr1TableStep = 
			parseStepSLR1Operation step cfg
					
			
	(* updated accept *)
	type trueslr1TableStep = symbol list * string list * slr1Table * string
	
	let acceptWordSLR1InitV2 (word:symbol list) cfg : trueslr1TableStep =
		let slr1Table = makeSLR1Table (LR0Grammar.makeLR0DiagramId (LR0Grammar.makeLR0Diagram cfg)) cfg in
		let revStack = ["0"] in 
		let valid = "Ongoing" in
		let initStep = ((word @ [dollar]),revStack,slr1Table,valid) in
			initStep
	
	let parseStepSLR1OperationV2 (step:trueslr1TableStep) (cfg:t) : trueslr1TableStep = 
		let (word, revStack, slr1Table, valid) = step in
		(*print_string (List.hd revStack ^ "\n");
		print_string (valid); *)
		let currentState = int_of_string(List.hd revStack) in 
		let (id,shifts,actionSet) = Set.nth slr1Table currentState in (* get corresponding table entry *)
		(* print_string ((word2str word) ^ "\n"); *)
		if(List.length word = 0) then
			(word, revStack, slr1Table, "Rejeitada")
		else
			let topSymbol = List.nth word 0 in
				if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
					let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
						if(Set.size targetShifts = 0) then (word, revStack, slr1Table, "Rejeitada")
						else
							let (nextSymbol,nextState) = Set.nth targetShifts 0 in
							let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
							let nextStep = ((getTail word), nextRevStack, slr1Table, valid) in
								nextStep
				else 
					let peekedSymbol = List.nth word 0 in
					let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
					let nEntries = Set.size peekedsymbolAndActions in
						if nEntries = 0 then 
							(word, revStack, slr1Table, "Rejeitada")
						else if nEntries > 1 then
							(word, revStack, slr1Table, "Conflito")
						else
							let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
							(* Durante o accept, se encontrar um conflito, para imediatamente e retorna "... Conflito ..." AMD *)
							if Set.size actions > 1 then (* NEW *)
								(word, revStack, slr1Table, "Conflito")
							else
						
							let action = Set.hd actions in
							match action with
							| Shift -> 
								begin
									match word with
									| [] -> (word, revStack, slr1Table, "Rejeitada")
									| s::_ -> 
										if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
											let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
												if(Set.size targetShifts = 0) then (word, revStack, slr1Table, "Rejeitada")
												(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
												(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
												else
													let (nextSymbol,nextState) = Set.nth targetShifts 0 in
													let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
													let nextStep = ((getTail word), nextRevStack, slr1Table, valid) in
														nextStep
										else
											(word, revStack, slr1Table, "Simbolo Inválido")
								end
							| Accept -> 
								if (word = [dollar]) then
									((getTail word), [symb2str cfg.initial], slr1Table, "Aceite")
								else 
									((word), revStack, slr1Table, "Rejeitada")
							| Reduce({head = h;body = b}) -> 
								let popNumber = List.length b in
								let nextRevStack = pop (popNumber*2) revStack in
								let wordWithAddedHead = [h] @ word in
								let nextStep = (wordWithAddedHead, nextRevStack, slr1Table, valid) in
									nextStep
		
	
	
	
		
	let acceptWordSLR1StepV2 (step:trueslr1TableStep) cfg : trueslr1TableStep = 
			parseStepSLR1OperationV2 step cfg
						
			
			
			
	
	let entryHasConflict slr1TableEntry : bool =
		let (id,shifts,actionSet) = slr1TableEntry in
		let entryConflicts = Set.filter ( fun (_, actions) -> Set.size actions > 1) actionSet in
			not (Set.isEmpty entryConflicts)
	
	let isSLR1 cfg : bool =
		let slr1Table = makeSLR1Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg in
		let conflicts = Set.filter (entryHasConflict) slr1Table in
			Set.isEmpty conflicts
			
			
	let getSLR1DiagramId cfg : lr0DiagramId = (* igual ao LR0 *)
		makeLR0DiagramId (makeLR0Diagram cfg)
		
	let getSLR1Table cfg : slr1Table =
		makeSLR1Table (makeLR0DiagramId (makeLR0Diagram cfg)) cfg 

end
	(* ----- LR1 -----*)
module LR1Grammar =
struct
	open LRAux
	type t = ContextFreeGrammarBasic.t
	
	type lr1Item = {head:symbol; body1:symbol list; body2:symbol list; lookahead:symbols}	
	type lr1State = lr1Item set
	type lr1Diagram = lr1State set * (lr1State * symbol * lr1State ) set
	
	type stateName = string
	type lr1StateId = stateName * lr1State 
	type lr1DiagramId = lr1StateId set * (lr1StateId * symbol * lr1StateId ) set
	

	type lr1Action = Accept | Shift | Reduce of rule
	type lr1TableEntry = stateName * (symbol * stateName) set * (symbol * lr1Action set ) set (* talvez seja (symbol * lr1Action set ) set *)
	type lr1Table = lr1TableEntry set
	
	let isCompleteLR1Item {head=h; body1=b1; body2=b2;lookahead=l} =
		b2 = []

	let countCompleteLR1Items lr1State = 
		let completeItems = Set.filter(isCompleteLR1Item) lr1State in
			Set.size completeItems
			
			
	let getNextSymbolForLR1Item {head=h; body1=b1; body2=b2;lookahead=l}  =
		match b2 with
		| [] -> epsilon
		| x::xs -> x
		
	let getDirectorLR1 {head=_; body1=_; body2=b2; lookahead=l} = (* obtem o simbolo diretor de um item *)
		match b2 with 
			| [] -> epsilon (* epsilon, aka no symbol *) 
			| x::_ -> x
			
	(*
	let first symbols = (* Injected first to test LR1 grammars lookahead - Luis Monteiro *)
		match symbols with
		| [] -> Set.make ['$'] (* Não deve acontecer*)
		| x::xs -> 
			if(x = 'A') then ['$';'a';'b']
			else if(x = 'B') then ['a';'b']
			else if(x = 'a') then ['a']
			else ['b']
	*)		
	(*		
	let first symbols = (* Injected first to test LALR1 grammars lookahead - Luis Monteiro *)
		match symbols with
		| [] -> Set.make [dollar] (* Não deve acontecer*)
		| x::xs -> 
			if(x = symb "X") then Set.make [symb "c"; symb "d"]
			else if(x = symb "C") then Set.make [symb "c"; symb "d"]
			else if(x = symb "c") then Set.make [symb "c"]
			else Set.make [symb "d"]
	*)
	let getDirectorWithLookaheadLR1 {head=_; body1=_; body2=b2; lookahead=l} cfg = (* obtem o simbolo diretor de um item *)
		match b2 with 
			| [] -> (epsilon,Set.empty) (* epsilon, aka no symbol *) 
			| x::xs -> if(List.length b2 > 1) then (x,ContextFreeGrammarBasic.first xs true cfg) else (x,l)	
			
			
	let getDirectorsLR1 state = (* Aplica a função getDirector a todos os itens de um dado estado*)
		Set.filter (fun d-> d <> epsilon)(Set.map getDirectorLR1 state)
			
	(* função auxiliar para avançar o ponto de um item em um simbolo para
	    o nucleo do proximo estado. Ex: A ->.ab para A -> a.b *)
	let kernelAdvanceLR1Item {head=h; body1=b1; body2=b2;lookahead = l} =
		match b2 with
		| [] -> Error.fatal "kernelAdvanceItem: Este caso nem deve ser alcançavel"
		| x::xs -> {head = h; body1 = b1 @ [x]; body2 = xs;lookahead = l} 
			
	let buildLR1Item {head=h; body1=b1; body2=b2; lookahead=_} lookahead =
		{head=h; body1=b1; body2=b2; lookahead=lookahead}
				
	let getDirectorsWithLookaheadLR1 (state:lr1State) cfg = (* Aplica a função getDirectorWithLookaheadLR1 a todos os itens de um dado estado*)
		Set.filter (fun (d,l)-> d <> epsilon)(Set.map (fun it -> getDirectorWithLookaheadLR1 it cfg) state) 
		
	let hasSameCore {head=h1; body1=b1; body2=b2; lookahead=l1} {head=h2; body1=b21; body2=b22; lookahead=l2} = 
		(h1 = h2 && b1 = b21 && b2 = b22)
		
	let mergeTwoItemsWithSameCore {head=h1; body1=b1; body2=b2; lookahead=l1} {head=h2; body1=b21; body2=b22; lookahead=l2} =
		let combinedLookahead = Set.union l1 l2 in
		{head=h1; body1=b1;body2=b2;lookahead=combinedLookahead}
		
	let mergeOneItem item currentItems = (* careful with the args order*)
		let (a,b) = Set.partition (fun i -> hasSameCore item i ) currentItems in
			if Set.size a = 0 then Set.add item currentItems
			else Set.add (mergeTwoItemsWithSameCore (Set.hd a) item) b	
			
	(*
	let mergeItems2 currentItems newItems =
		let rec process currentItems newItems =
			match newItems with
			| [] -> currentItems 
			| i::is -> process (mergeOneItem i currentItems) is 
		in
			process currentItems (Set.toList newItems) 		
	*)
	
			
	let rec mergeItems currentItems newItems =
		if Set.isEmpty newItems then
			currentItems
		else
			let (i,is) = Set.cut newItems in
				mergeItems (mergeOneItem i currentItems) is 
	
	(*			
	let rec mergeItems currentItems newItems =
		Set.match_ newItems 
			(fun () -> currentItems)
			(fun i is -> mergeItems (mergeOneItem i currentItems) is)
	*)
	
	let rule2ItemLR1 (rule: rule) lookahead =
		{head = rule.head; body1 = []; body2 = rule.body; lookahead = lookahead} 
	
	let generateItemsForVarDirectorWithLookahead director rules lookahead = 
		let itemRules = Set.filter (fun {head = h; body =_} -> h = director) rules in 
		let items = Set.map (fun r -> rule2ItemLR1 r lookahead) itemRules in	
			items
			
	let diagramsJoin2LR1 (s0,t0) (s1,t1) = (Set.union s0 s1, Set.union t0 t1) (* juntar dois diagramas LR0 para obter um diagrama LR0 resultante da união *)	
	
	let rec diagramsJoinListLR1 l : lr1Diagram = (* Juntar um conjunto de diagramas para produzir o diagrama LR0, cada diagrama desta lista corresponde a um estado rescrito como diagrama *)
		match l with
		| [] -> (Set.empty , Set.empty) 
		| d::ds -> diagramsJoin2LR1 d (diagramsJoinListLR1 ds)
	
	
	
	let makeLR1DiagramId diagram : lr1DiagramId (* Cria etiquetas para os estados e os mesmos estados contidos nas transições do diagrama*) =
		let (states,transitions) = diagram in
		let dictionary = List.combine (Set.toList states) (nats (Set.size states)) in
		let statesId = Set.map (fun s -> (List.assoc s dictionary,s) ) states in
		let transitionsId = Set.map (fun (a,b,c) -> ((List.assoc a dictionary, a), b,(List.assoc c dictionary, c))) transitions in
			(statesId, transitionsId)
	



	let buildLR1ReductionActionsForOne completeItems symbol = (* Warning, input must only contain complete items *)
		let reductionItems = Set.filter(fun it -> Set.belongs symbol it.lookahead) completeItems in
			Set.map (fun it -> Reduce ({head = it.head;body = it.body1}) ) reductionItems	
			


	let buildLR1ReductionActions completeItems alphabet = 
		Set.map(fun symbol -> (symbol, buildLR1ReductionActionsForOne completeItems symbol) ) alphabet
	
	
	let buildLR1ShiftActionsForOne items symbol : lr1Action set = 
		let shiftItems = Set.filter(fun it -> (getNextSymbolForLR1Item it) = symbol) items in
		if(Set.size shiftItems > 0) then
			Set.make [Shift]
		else
			Set.empty
			


	let buildLR1ShiftActions completeItems alphabet = 
		Set.map(fun symbol -> (symbol, buildLR1ShiftActionsForOne completeItems symbol) ) alphabet
	
	

	let buildLR1MixedActionsForOne cfgInitial items symbol = 
		let reductionItems = Set.filter(fun it -> (Set.belongs symbol it.lookahead) && isCompleteLR1Item it) items in
		let fixedreductionItems = Set.filter (fun it-> it.head != cfgInitial) reductionItems in
		let acceptItems = Set.filter (fun it -> it.head = cfgInitial && symbol = dollar && isCompleteLR1Item it && (Set.belongs it fixedreductionItems) = false) items in
		let shiftItems = Set.filter(fun it -> (getNextSymbolForLR1Item it) = symbol) items in
		let reductionEntries = Set.map (fun it -> Reduce ({head = it.head;body = it.body1}) ) fixedreductionItems in
	
		if(Set.size acceptItems > 0) then
			if(Set.size shiftItems > 0) then
				Set.union (Set.union (Set.make [Shift]) reductionEntries) (Set.make [Accept])
			else
				Set.union reductionEntries (Set.make [Accept])
		else	
			if(Set.size shiftItems > 0) then
				Set.union (Set.make [Shift]) reductionEntries
			else
				reductionEntries
				
				
				

	let buildLR1MixedActions cfgInitial (items:lr1State) alphabet = (* True build function - prototype *) (* transformar na forma do buildLR1ReductionActions *)
		Set.map(fun symbol -> (symbol, buildLR1MixedActionsForOne cfgInitial items symbol) ) alphabet
		
			
	let makeLR1TableEntry (id, lr1State) (cfg:t) transitions = (* possivelmente dar merge aos buildLR1Actions?*)
		let stateTransitions = Set.filter (fun ((a,_),_,_)-> a = id) transitions in
			if Set.size stateTransitions = 0 then (* this part seems fine *)
				let {head = h;body1 = b1;body2 = b2;lookahead = l} = List.hd (Set.toList lr1State) in
					if h = cfg.initial then 
						let lr1Actions : (symbol * lr1Action set) set = Set.make [dollar,Set.make [Accept]] in
							(id,Set.empty,lr1Actions)
					else
						let completeAlphabet = Set.add dollar cfg.alphabet in (* Se o $, final da palavra, não estiver no alfabeto da gramática *)
						let lr1Actions : (symbol * lr1Action set) set = buildLR1ReductionActions lr1State completeAlphabet in
							(id,Set.empty, lr1Actions)		
			else  (* Existem Shifts e possivelmente tambem reducoes *)
				let nextShifts = Set.map (fun (a,b,(cId,c)) -> (b,cId)) stateTransitions in
					if(countCompleteLR1Items lr1State = 0) then (* Não existem reducoes *)
						let lr1Actions = buildLR1ShiftActions lr1State cfg.alphabet in
							(id, nextShifts, lr1Actions)
					else (* Existem reducoes e transferencias *)
						let completeAlphabet = Set.add dollar cfg.alphabet in (* Se o $, final da palavra, não estiver no alfabeto da gramática *)
						let lr1Actions = buildLR1MixedActions cfg.initial lr1State completeAlphabet in
							(id, nextShifts, lr1Actions)
					
	
	(*pre: isLR1 cfg *)
	let makeLR1Table (labeledDiagram:lr1DiagramId) cfg : lr1Table = (* recebe um diagrama numerado e constroi a tabela de parsing a partir das transições *) 
		let (statesId, transitionsId) = labeledDiagram in
			Set.map (fun s -> makeLR1TableEntry s cfg transitionsId) statesId


	
		
	let lr1StateClosureStep (cfg: t) currentItems = (* Create items for current directors *)
		let directorsWithLookahead : (symbol * symbols) set = getDirectorsWithLookaheadLR1 currentItems cfg in
		
		let varDirectorsWithLookahead = Set.filter (fun (d,_) -> Set.belongs d cfg.variables) directorsWithLookahead in
		let newItems = Set.flatMap (fun (d,l) -> generateItemsForVarDirectorWithLookahead d cfg.rules l) varDirectorsWithLookahead in
		let mergedItems = mergeItems currentItems newItems in
			mergedItems
		
		
	let rec lr1StateClosure cfg currentItems : lr1State = (* Create all items for a singular state *)
		let next = lr1StateClosureStep cfg currentItems in
			if Set.subset next currentItems then next
			else lr1StateClosure cfg next
			
			
	
	let makeSingularNextLR1Diagram (cfg:t) prevState symbol : lr1Diagram = (* Creates a diagram containing only 1 state using the previous state and the transition symbol*)
		let items4Kernel = Set.filter (fun it -> getDirectorLR1 it = symbol) prevState in (* falta avançar o ponto *)
		let kernel = Set.map (kernelAdvanceLR1Item) items4Kernel in
		let closure = lr1StateClosure cfg kernel in
			(Set.make [prevState; closure], Set.make [(prevState ,symbol , closure )])
					

	
	let makeNextLR1Diagram (cfg:t) prevState : lr1Diagram = (* For each director symbol on the previous state, create a diagram and join all obtained diagrams into a single diagram*)
		let dirs = getDirectorsLR1 prevState in
		let diagrams = Set.map (fun d -> makeSingularNextLR1Diagram cfg prevState d) dirs in
			diagramsJoinListLR1 (Set.toList diagrams) 

			
		
	let makeNextLR1DiagramAll (cfg:t) states : lr1Diagram = (* build the diagram using the initial state, then use the makeNextLR0Diagram function to calculate all states obtainable from the initial state*)
		let diagrams = Set.map (fun s -> makeNextLR1Diagram cfg s) states in
			diagramsJoinListLR1 (Set.toList diagrams)

		
		
	let rec makeLR1DiagramX (cfg:t) diagram = (* função auxiliar que irá produzir o diagrama LR1 *)
		let (states,transitions) : lr1Diagram = diagram in 
		let next = makeNextLR1DiagramAll cfg states in
		let next2 = diagramsJoin2LR1 next (states,transitions) in
		let (states2,transitions2) = next2 in
			if Set.size states = Set.size states2 && Set.size transitions = Set.size transitions2 then next2
			else makeLR1DiagramX cfg next2 
			
			
	let makeFirstLR1Diagram (cfg:t) : lr1Diagram = (* O primeiro estado tem um procedimento de criação um pouco differente *) 
		let kernel = Set.map (fun r -> rule2ItemLR1 r (Set.make [dollar])) (LR0Grammar.startRules cfg) in	
		(*let kernelWithLookahead : lr1Item = buildLR1KernelItems kernel '$' in *)
		let closure = lr1StateClosure cfg kernel in
			(Set.make [closure], Set.empty)	
	
	let makeLR1Diagram (cfg:t) = makeLR1DiagramX cfg (makeFirstLR1Diagram cfg)  (* ponto de partida na construção do diagrama LR1 *)
	
	
	let rec parseOperationLR1 lr1Table word stateStack symbolStack (cfg:t) = 
		let currentState = int_of_string(List.hd stateStack) in 
		let (id,shifts,actionSet) = Set.nth lr1Table currentState in (* get corresponding table entry *)
		let topSymbol = List.nth word 0 in
			if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
				let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
					if(Set.size targetShifts = 0) then false
					else
						let (nextSymbol,nextState) = Set.nth targetShifts 0 in
						let nextStateStack = [nextState] @ stateStack in
						let nextSymbolStack = [nextSymbol] @ symbolStack in
							parseOperationLR1 lr1Table (getTail word) nextStateStack nextSymbolStack cfg
			else 
				let peekedSymbol = List.nth word 0 in
				let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
				let nEntries = Set.size peekedsymbolAndActions in
					if nEntries = 0 then 
						false
					else if nEntries > 1 then
						Error.fatal "ParseOperationLR1: conflito"
					else
						let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
						let action = Set.hd actions in
						match action with
						| Shift -> 
							begin
								match word with
								| [] -> false
								| s::_ -> 
									if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
										let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
											if(Set.size targetShifts = 0) then false
											(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
											(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
											else
												let (nextSymbol,nextState) = Set.nth targetShifts 0 in
												let nextStateStack = [nextState] @ stateStack in
												let nextSymbolStack = [nextSymbol] @ symbolStack in
													parseOperationLR1 lr1Table (getTail word) nextStateStack nextSymbolStack cfg
									else
										Error.fatal "ParseOperationLR1: este simbolo não pertence ao alfabeto desta gramatica"
							end
						| Accept -> 
							word = [dollar]	
						| Reduce({head = h;body = b}) -> 
							let popNumber = List.length b in
							let nextStateStack = (pop popNumber stateStack) in
							let nextSymbolStack = (pop popNumber symbolStack) in
							let wordWithAddedHead = [h] @ word in
								parseOperationLR1 lr1Table (wordWithAddedHead) nextStateStack nextSymbolStack cfg (*Add the variable, aka head of the reduction rule, to the word being processed *)
								
	
	(* pre: isLR1 cfg 
	   pre: isWordValid word cfg *)
	let acceptWordLR1 (word:symbol list) cfg : bool = 
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLR1Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
			parseOperationLR1 lr1Table (word @ [dollar]) stateRevStack symbolRevStack cfg
			
			
	(* Added functions to provide a step-by step LR1 visualization of accepting *)

	type lr1TableStep = symbol list * string list * symbol list * lr1Table * bool
	
	let acceptWordLR1Init (word:symbol list) cfg : lr1TableStep =
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLR1Diagram cfg)) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
		let valid = true in
		let initStep = ((word @ [dollar]),stateRevStack,symbolRevStack,lr1Table,valid) in
			initStep
	
	let parseStepLR1Operation (step:lr1TableStep) (cfg:t) : lr1TableStep = 
		let (word, stateStack, symbolStack, lr1Table, valid) = step in
		let currentState = int_of_string(List.hd stateStack) in 
		let (id,shifts,actionSet) = Set.nth lr1Table currentState in (* get corresponding table entry *)
		let topSymbol = List.nth word 0 in
			if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
				let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
					if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, lr1Table, false)
					else
						let (nextSymbol,nextState) = Set.nth targetShifts 0 in
						let nextStateStack = [nextState] @ stateStack in
						let nextSymbolStack = [nextSymbol] @ symbolStack in
						let nextStep = ((getTail word), nextStateStack, nextSymbolStack, lr1Table, valid) in
							nextStep
			else 
				let peekedSymbol = List.nth word 0 in
				let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
				let nEntries = Set.size peekedsymbolAndActions in
					if nEntries = 0 then 
						(word, stateStack, symbolStack, lr1Table, false)
					else if nEntries > 1 then
						Error.fatal "parseStepLR1Operation: conflito"
					else
						let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
						let action = Set.hd actions in
						match action with
						| Shift -> 
							begin
								match word with
								| [] -> (word, stateStack, symbolStack, lr1Table, false)
								| s::_ -> 
									if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
										let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
											if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, lr1Table, false)
											(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
											(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
											else
												let (nextSymbol,nextState) = Set.nth targetShifts 0 in
												let nextStateStack = [nextState] @ stateStack in
												let nextSymbolStack = [nextSymbol] @ symbolStack in
												let nextStep = ((getTail word), nextStateStack, nextSymbolStack, lr1Table, valid) in
													nextStep
									else
										Error.fatal "parseStepLR1Operation: este simbolo não pertence ao alfabeto desta gramatica"
							end
						| Accept -> 
							if (word = [dollar]) then
								((getTail word), stateStack, symbolStack, lr1Table, valid)
							else 
								((getTail word), stateStack, symbolStack, lr1Table, false)
						| Reduce({head = h;body = b}) -> 
							let popNumber = List.length b in
							let nextStateStack = (pop popNumber stateStack) in
							let nextSymbolStack = (pop popNumber symbolStack) in
							let wordWithAddedHead = [h] @ word in
							let nextStep = (wordWithAddedHead, nextStateStack, nextSymbolStack, lr1Table, valid) in
								nextStep
		
	
	
	
		
	let acceptWordLR1Step (step:lr1TableStep) cfg : lr1TableStep = 
			parseStepLR1Operation step cfg
			
			
	(* updated accept *)
	type truelr1TableStep = symbol list * string list * lr1Table * string
	
	let acceptWordLR1InitV2 (word:symbol list) cfg : truelr1TableStep =
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLR1Diagram cfg)) cfg in
		let revStack = ["0"] in 
		let valid = "Ongoing" in
		let initStep = ((word @ [dollar]),revStack,lr1Table,valid) in
			initStep
	
	let parseStepLR1OperationV2 (step:truelr1TableStep) (cfg:t) : truelr1TableStep = 
		let (word, revStack, lr1Table, valid) = step in
		let currentState = int_of_string(List.hd revStack) in 
		let (id,shifts,actionSet) = Set.nth lr1Table currentState in (* get corresponding table entry *)
		if(List.length word = 0) then
			(word, revStack, lr1Table, "Rejeitada")
		else
			let topSymbol = List.nth word 0 in
				if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
					let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
						if(Set.size targetShifts = 0) then (word, revStack, lr1Table, "Rejeitada")
						else
							let (nextSymbol,nextState) = Set.nth targetShifts 0 in
							let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
							let nextStep = ((getTail word), nextRevStack, lr1Table, valid) in
								nextStep
				else 
					let peekedSymbol = List.nth word 0 in
					let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
					let nEntries = Set.size peekedsymbolAndActions in
						if nEntries = 0 then 
							(word, revStack, lr1Table, "Rejeitada")
						else if nEntries > 1 then
							(word, revStack, lr1Table, "Conflito")
						else
							let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
							(*Durante o accept, se encontrar um conflito, para imediatamente e retorna "... Conflito ..."
								Uma possibilidade possivel. Se há conflitos, só ficam ativos os botões de Accept que sejam imunes a esses conflitos.
								*)
	
							if Set.size actions > 1 then (* NEW *)
								(word, revStack, lr1Table, "Conflito")
							else

						let action = Set.hd actions in
							match action with
							| Shift -> 
								begin
									match word with
									| [] -> (word, revStack, lr1Table, "Rejeitada")
									| s::_ -> 
										if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
											let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
												if(Set.size targetShifts = 0) then (word, revStack, lr1Table, "Rejeitada")
												(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
												(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
												else
													let (nextSymbol,nextState) = Set.nth targetShifts 0 in
													let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
													let nextStep = ((getTail word), nextRevStack, lr1Table, valid) in
														nextStep
										else
											(word, revStack, lr1Table, "Simbolo Inválido")
								end
							| Accept -> 
								if (word = [dollar]) then
									((getTail word), [symb2str cfg.initial], lr1Table, "Aceite")
								else 
									((getTail word), revStack, lr1Table, "Rejeitada")
							| Reduce({head = h;body = b}) -> 
								let popNumber = List.length b in
								let nextRevStack = pop (popNumber*2) revStack in
								let wordWithAddedHead = [h] @ word in
								let nextStep = (wordWithAddedHead, nextRevStack, lr1Table, valid) in
									nextStep
		
	
	
	
		
	let acceptWordLR1StepV2 (step:truelr1TableStep) cfg : truelr1TableStep = 
			parseStepLR1OperationV2 step cfg
			
			
			
			
			
	
	let entryHasConflict lr1TableEntry : bool =
		let (id,shifts,actionSet) = lr1TableEntry in
		let entryConflicts = Set.filter ( fun (_, actions) -> Set.size actions > 1) actionSet in
			Set.size entryConflicts > 0
	
	let isLR1 cfg : bool =
		let slr1Table = makeLR1Table (makeLR1DiagramId (makeLR1Diagram cfg)) cfg in
		let conflicts = Set.filter (entryHasConflict) slr1Table in
			Set.size conflicts = 0
			
			
	let getLR1DiagramId cfg : lr1DiagramId =
		makeLR1DiagramId (makeLR1Diagram cfg)
		
	let getLR1Table cfg : lr1Table =
		makeLR1Table (makeLR1DiagramId (makeLR1Diagram cfg)) cfg 
	
end	
	(* ----- LALR1 -----*)
module LALR1Grammar =
	struct
	open LRAux
	open LR0Grammar	
	open LR1Grammar	
		
		
	let itemsSameCores it1 it2 =
		it1.head = it2.head && it1.body1 = it2.body1 && it1.body2 = it2.body2
		
	let itemsJoinLookahead it1 it2 =
		{head = it1.head; body1 = it1.body1; body2 = it1.body2; lookahead = (Set.union it1.lookahead it2.lookahead)}
	
	
	let getStateCore (state:lr1State) =
		Set.map (fun it -> {head = it.head; body1 = it.body1; body2 = it.body2}) state
	
	
	let haveSameCores lr1state1 lr1state2 =
		let state1Core = getStateCore lr1state1 in
		let state2Core = getStateCore lr1state2 in
			Set.equals state1Core state2Core
				
	(*pre: hasSameCores state1 state2 *)
	let mergeLR1States state1 state2 =
		Set.map (fun it -> 
			let fit = Set.find (fun it2 -> itemsSameCores it it2) state2 in itemsJoinLookahead it fit) state1 
	
	
	
	type lr1StateId = stateName * lr1State 
	type lr1DiagramId = lr1StateId set * (lr1StateId * symbol * lr1StateId ) set
		
	let rec lr1StateFusionId statesId  = (* Esta deve ser a função a aplicar na versão final, a differença é que esta função trabalha com o diagrama diretamente (a parte dos estados identificados) *)
		match statesId with
		| [] -> []
		| (id,x)::xs -> 
			let ss = lr1StateFusionId xs in
			let (a,b) = List.partition (fun (_,y)-> haveSameCores x y) ss in 
				match a with
				| [] -> (id,x)::ss 
				| [(id2,y)] -> (id^","^id2,mergeLR1States x y)::b(* fundir x com y*)
				| _ -> Error.fatal "lr1StateFusionFail"	
		
				
	
	let rec lr1StateFusion states  =
		match states with
		| [] -> []
		| x::xs -> 
			let ss = lr1StateFusion xs in
			let (a,b) = List.partition (haveSameCores x) ss in 
				match a with
				| [] -> x::ss 
				| [y] -> mergeLR1States x y::b(* fundir x com y*)
				| _ -> Error.fatal "lr1StateFusionFail"
		
	let translate state fstates =
		Set.find (fun s -> haveSameCores state s) fstates
		
				
	let lr1TransFusion trans fstates =
		Set.map (fun (s1,sym,s2) -> (translate s1 fstates,sym,translate s2 fstates)) trans
				
	
	let makeLALR1FromLR1 diagram =
		let (states,transitions) : lr1Diagram = diagram in 
		let fstates = lr1StateFusion (Set.toList states) in
		let ftrans = lr1TransFusion transitions (Set.make fstates) in
		let lalr1Diagram : lr1Diagram = ((Set.make fstates),ftrans) in
			lalr1Diagram
			
			
	(* pre: isLR1 cfg 
	   pre: isWordValid word cfg *)
	let acceptWordLALR1 (word: word) cfg : bool = 
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
			parseOperationLR1 lr1Table (word @ [dollar]) stateRevStack symbolRevStack cfg
			
			
	(* Added functions to provide a step-by step LR1 visualization of accepting *)

	type lr1TableStep = symbol list * string list * symbol list * lr1Table * bool
	
	let acceptWordLALR1Init (word:symbol list) cfg : lr1TableStep =
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))) cfg in
		let stateRevStack = ["0"] in (*char list due to mix of numbers and symbols *) 
		let symbolRevStack : symbol list = [] in
		let valid = true in
		let initStep = ((word @ [dollar]),stateRevStack,symbolRevStack,lr1Table,valid) in
			initStep
	
	let parseStepLALR1Operation (step:lr1TableStep) (cfg:t) : lr1TableStep = 
		let (word, stateStack, symbolStack, lr1Table, valid) = step in
		let currentState = int_of_string(List.hd stateStack) in 
		let (id,shifts,actionSet) = Set.nth lr1Table currentState in (* get corresponding table entry *)
		let topSymbol = List.nth word 0 in
			if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
				let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
					if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, lr1Table, false)
					else
						let (nextSymbol,nextState) = Set.nth targetShifts 0 in
						let nextStateStack = [nextState] @ stateStack in
						let nextSymbolStack = [nextSymbol] @ symbolStack in
						let nextStep = ((getTail word), nextStateStack, nextSymbolStack, lr1Table, valid) in
							nextStep
			else 
				let peekedSymbol = List.nth word 0 in
				let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
				let nEntries = Set.size peekedsymbolAndActions in
					if nEntries = 0 then 
						(word, stateStack, symbolStack, lr1Table, false)
					else if nEntries > 1 then
						Error.fatal "parseStepLR1Operation: conflito"
					else
						let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)
						let action = Set.hd actions in
						match action with
						| Shift -> 
							begin
								match word with
								| [] -> (word, stateStack, symbolStack, lr1Table, false)
								| s::_ -> 
									if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
										let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
											if(Set.size targetShifts = 0) then (word, stateStack, symbolStack, lr1Table, false)
											(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
											(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
											else
												let (nextSymbol,nextState) = Set.nth targetShifts 0 in
												let nextStateStack = [nextState] @ stateStack in
												let nextSymbolStack = [nextSymbol] @ symbolStack in
												let nextStep = ((getTail word), nextStateStack, nextSymbolStack, lr1Table, valid) in
													nextStep
									else
										Error.fatal "parseStepLR1Operation: este simbolo não pertence ao alfabeto desta gramatica"
							end
						| Accept -> 
							if (word = [dollar]) then
								((getTail word), stateStack, symbolStack, lr1Table, valid)
							else 
								((getTail word), stateStack, symbolStack, lr1Table, false)
						| Reduce({head = h;body = b}) -> 
							let popNumber = List.length b in
							let nextStateStack = (pop popNumber stateStack) in
							let nextSymbolStack = (pop popNumber symbolStack) in
							let wordWithAddedHead = [h] @ word in
							let nextStep = (wordWithAddedHead, nextStateStack, nextSymbolStack, lr1Table, valid) in
								nextStep
		
	
	
	
		
	let acceptWordLALR1Step (step:lr1TableStep) cfg : lr1TableStep = 
			parseStepLALR1Operation step cfg		
			
			
	(* updated accept *)
	
	let acceptWordLALR1InitV2 (word:symbol list) cfg : truelr1TableStep =
		let lr1Table = makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))) cfg in
		let revStack = ["0"] in 
		let valid = "Ongoing" in
		let initStep = ((word @ [dollar]),revStack,lr1Table,valid) in
			initStep
	
	let parseStepLALR1OperationV2 (step:truelr1TableStep) (cfg:t) : truelr1TableStep = 
		let (word, revStack, lr1Table, valid) = step in
		let currentState = int_of_string(List.hd revStack) in 
		let (id,shifts,actionSet) = Set.nth lr1Table currentState in (* get corresponding table entry *)
		if(List.length word = 0) then
			(word, revStack, lr1Table, "Rejeitada")
		else
			let topSymbol = List.nth word 0 in
				if(Set.belongs topSymbol cfg.variables) then (*Fazemos um Shift com uma variavel*)
					let targetShifts = Set.filter (fun (a,b) -> a = topSymbol) shifts in
						if(Set.size targetShifts = 0) then (word, revStack, lr1Table, "Rejeitada")
						else
							let (nextSymbol,nextState) = Set.nth targetShifts 0 in
							let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
							let nextStep = ((getTail word), nextRevStack, lr1Table, valid) in
								nextStep
				else 
					let peekedSymbol = List.nth word 0 in
					let peekedsymbolAndActions = Set.filter( fun (s,a) -> s = peekedSymbol && Set.size a > 0 ) actionSet in
					let nEntries = Set.size peekedsymbolAndActions in
						if nEntries = 0 then 
							(word, revStack, lr1Table, "Rejeitada")
						else if nEntries > 1 then
							(word, revStack, lr1Table, "Conflito")
						else
							let (symbol,actions) = Set.hd peekedsymbolAndActions in (* atualmente está a falhar aqui, com hd failure *)

							(*Durante o accept, se encontrar um conflito, para imediatamente e retorna "... Conflito ..."*)
							if Set.size actions > 1 then (* NEW *)
								(word, revStack, lr1Table, "Conflito")
							else
				
							
							let action = Set.hd actions in
							match action with
							| Shift -> 
								begin
									match word with
									| [] -> (word, revStack, lr1Table, "Rejeitada")
									| s::_ -> 
										if(Set.belongs s cfg.alphabet || Set.belongs s cfg.variables) then
											let targetShifts = Set.filter (fun (a,b) -> a = s) shifts in
												if(Set.size targetShifts = 0) then (word, revStack, lr1Table, "Rejeitada")
												(* Error.fatal (String.of_seq (List.to_seq ([char_of_int ((int_of_char '0') + currentState)] @ [s]))) *)
												(* para testar Error.fatal (String.of_seq (List.to_seq [s])) (* Casos corretos estão a ir parar aqui por alguma razão, provavelmente após uma redução *) *)
												else
													let (nextSymbol,nextState) = Set.nth targetShifts 0 in
													let nextRevStack = [nextState] @ [symb2str nextSymbol] @ revStack in
													let nextStep = ((getTail word), nextRevStack, lr1Table, valid) in
														nextStep
										else
											(word, revStack, lr1Table, "Simbolo Inválido")
								end
							| Accept -> 
								if (word = [dollar]) then
									((getTail word), [symb2str cfg.initial], lr1Table, "Aceite")
								else 
									((getTail word), revStack, lr1Table, "Rejeitada")
							| Reduce({head = h;body = b}) -> 
								let popNumber = List.length b in
								let nextRevStack = pop (popNumber*2) revStack in
								let wordWithAddedHead = [h] @ word in
								let nextStep = (wordWithAddedHead, nextRevStack, lr1Table, valid) in
									nextStep
		
	
	
	
		
	let acceptWordLALR1StepV2 (step:truelr1TableStep) cfg : truelr1TableStep = 
			parseStepLALR1OperationV2 step cfg
					
			
			
			
			
	let entryHasConflict slr1TableEntry : bool =
		let (id,shifts,actionSet) = slr1TableEntry in
		let entryConflicts = Set.filter ( fun (_, actions) -> Set.size actions > 1) actionSet in
			not (Set.isEmpty entryConflicts)
	
	let isLALR1 cfg : bool =
		let lalr1Table = makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))) cfg in
		let conflicts = Set.filter (entryHasConflict) lalr1Table in
			Set.isEmpty conflicts
			
			
	let getLALR1DiagramId cfg : lr1DiagramId =
		 makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))
		
	let getLALR1Table cfg : lr1Table =
		makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram cfg))) cfg
end

module ContextFreeGrammarLR =
struct
	type t = ContextFreeGrammarBasic.t
	open LR0Grammar
	open SLR1Grammar
	open LR1Grammar
	open LALR1Grammar
	
	class model (arg: t Arg.alternatives) =
		object(self) inherit ContextFreeGrammarLL1.model arg as super
		
				
			method isLR0 : bool =
				isLR0 (self#representation)
				
			method getLR0DiagramId : LR0Grammar.lr0DiagramId =
				getLR0DiagramId (self#representation)
				
			method getLR0Table : LR0Grammar.lr0Table =
				getLR0Table (self#representation)
				
			method getLR0TableExt : LR0Grammar.lr0TableExt =
				getLR0TableExt (self#representation)
				
		(* SLR1 *)
			method isSLR1 : bool =
				isSLR1 (self#representation)
				
			method getSLR1Table : SLR1Grammar.slr1Table =
				getSLR1Table (self#representation)
				
		(* LR1 *)	
		
			method isLR1 : bool =
				isLR1 (self#representation)
			
			method getLR1DiagramId : LR1Grammar.lr1DiagramId =
				getLR1DiagramId (self#representation)
			
			method getLR1Table : LR1Grammar.lr1Table =
				getLR1Table (self#representation)
				
		(* LALR1 *)		
			method isLALR1 : bool =
				isLALR1 (self#representation)
			
			method getLALR1DiagramId : LR1Grammar.lr1DiagramId =
				getLALR1DiagramId (self#representation)
				
			method getLALR1Table : LR1Grammar.lr1Table =
				getLALR1Table (self#representation)
	end
end

#endif
