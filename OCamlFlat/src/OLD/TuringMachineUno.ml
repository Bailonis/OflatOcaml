(*
 * TuringMachine.ml
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
 * ???/2022 (ml) - ???.
 * jun/2022 (amd) - Initial skeleton.
 *)

(*
 * Description: Turing machine functionality.
 *)

open BasicTypes

module TuringMachineAccept = (* ML + AMD *)
struct
	open TuringMachineSupport
	
	let initialConfigs tm w: configuration set =
		Set.make [(tm.initialState, [empty], w@[empty])]

	let isAcceptingConfig tm (s,l,r): bool =
		let curr = List.hd r in
		let belongs = Set.belongs curr tm.tapeAlphabet in
		let ts = tm.transitions in	
		let isHalting = Set.isEmpty (Set.filter (fun (a,b,_,_,_) -> a = s && b = curr) ts) in
			if tm.criteria then
				belongs && isHalting && Set.belongs s tm.acceptStates
			else
				belongs && isHalting

	let fixr tape =
		match tape with
		| [] -> [empty; empty]
		| [x] -> [x; empty]
		| _ -> tape

	let fixl tape =
		match tape with
		| [] -> [empty]
		| _ -> tape

	let nextConfigs (a,b,c,d,e) (s,l,r) =
		match l, r with
		| l::ls, r::rs ->
			if a = s && b = r then
				if e = R then Set.make [(c,d::l::ls,fixr rs)]
				else Set.make [(c,fixl ls,l::d::rs)]
			else Set.empty
		| _, _ -> Error.fatal "next"

	let nextConfigs tm (s,l,r): configuration set = 
		Set.flatMap (fun (a,b,c,d,e) -> nextConfigs (a,b,c,d,e) (s,l,r)) tm.transitions

	let accept tm w =
		ignore (Model.checkWord tm.entryAlphabet w true);
		Model.accept tm w
		initialConfigs
		 nextConfigs
		  isAcceptingConfig

	let acceptFull tm w = 
		ignore (Model.checkWord tm.entryAlphabet w true);
		Model.acceptFull tm w initialConfigs nextConfigs isAcceptingConfig
end

module TuringMachineGenerate = (* ML + AMD *)
struct
	open TuringMachineSupport
	open TuringMachineAccept
	
	let getWord (s,l,r) = word "_"
	
	let generate tm length = 
		Model.generateDumb tm tm.entryAlphabet length initialConfigs nextConfigs isAcceptingConfig
end


module TuringMachineLB = (* ML *)
struct
	open TuringMachineSupport
	open TuringMachineAccept

	let getMarkers rep = (Set.nth rep.markers 0, Set.nth rep.markers 1)

	let isLB rep = 
		let hasMarkers = (Set.size rep.markers) = 2 in
			if hasMarkers then
				let (leftMarker, rightMarker) = getMarkers rep in
				let boundedDirection mark rev = Set.exists (fun (_,b,_,d,e) -> b = mark && (d != mark || e != rev)) rep.transitions in
				let bounded = (boundedDirection leftMarker R) && (boundedDirection rightMarker L) in
					bounded
			else
				hasMarkers

	let acceptLB w rep = 
		if isLB rep then
			let (leftMarker, rightMarker) = getMarkers rep in
			let newWord = [leftMarker]@w@[rightMarker] in
				accept rep newWord
		else
			false

	let acceptFullLB w rep =
		if isLB rep then
			let (leftMarker, rightMarker) = getMarkers rep in
			let newWord = [leftMarker]@w@[rightMarker] in
				acceptFull rep newWord
		else
			(false,[],[])
end

module TuringMachinePrivate =
struct
	open TuringMachineSupport

	let getDefaultMachine = {
		entryAlphabet = Set.empty;
		tapeAlphabet = Set.add empty Set.empty;	
		empty = empty;
		states = Set.add "START" Set.empty;
		initialState = "START";
		transitions = Set.empty;
		acceptStates = Set.empty;
		criteria = false;
		markers = Set.empty
	}
	
	let transitionGet1 trns = Set.map ( fun (a,_,_,_,_) -> a ) trns
	let transitionGet2 trns = Set.map ( fun (_,b,_,_,_) -> b ) trns
	let transitionGet3 trns = Set.map ( fun (_,_,c,_,_) -> c ) trns
  let transitionGet4 trns = Set.map ( fun (_,_,_,d,_) -> d ) trns
	let configurationGet1 configs =  Set.map ( fun (a,_,_) -> a ) configs
	let configurationGet2 configs =  Set.map ( fun (_,b,_) -> b ) configs
	let configurationGet3 configs =  Set.map ( fun (_,_,c) -> c ) configs

	let printConfiguration config =
		let (state, left, right) = config in
		Util.print ["("; state2str state; ", "];
		List.iter (fun x -> Util.print [symb2str x]) left;
		Util.print [", "];
		List.iter (fun x -> Util.print [symb2str x]) right;
		Util.print [")"]

	let printConfigurations configs = 
		Util.println ["printing configs"];
		Set.iter (fun x -> printConfiguration x) configs;
		Util.println [string_of_int (Set.size configs)]	
	
	let transitionsTm2Fa trns = Set.map ( fun (a,b,c,_,_) -> (a,b,c) ) trns
	let transitionGetSymbs trns = Set.union (Set.map (fun (_,b,_,_,_) -> b) trns) (Set.map (fun (_,_,_,d,_) -> d) trns)

	let rec acceptX left right st trs seen limit = 
		if limit = 0 then 
			state "~"
		else
			let newLimit = limit - 1 in
			let config = (List.rev left)@[symb (state2str st)]@right in
				if Set.belongs config seen then state "~"
				else
					let newSeen = Set.add config seen in
					match left, right with
					| [], [] -> st
					| [], x::xs -> acceptX [empty] right st trs newSeen newLimit
					| x::xs, [] -> acceptX left [empty] st trs newSeen newLimit
					| x::xs, y::ys -> let getTransi = Set.filter (fun (a,b,_,_,_) -> st = a && y = b) trs in
														if Set.isEmpty getTransi then st
														else 
															let (_,_,nst,nsymb,dir) = Set.nth getTransi 0 in
																if dir = R then
																	let newLeft = nsymb::left in
																		acceptX newLeft ys nst trs newSeen newLimit;
																else
																	let newRight = x::nsymb::right in
																		acceptX xs newRight nst trs	newSeen newLimit

	let acceptOld w rp =
		let bWord = w@[empty] in
			let lastST: state = acceptX [empty] bWord rp.initialState rp.transitions Set.empty 100 in
				if rp.criteria then Set.exists (fun x -> x = lastST) rp.acceptStates
				else if lastST = state "~" then false
				else true



	let validate (name: string) (rep: t) = (

		let validInitSt = Set.belongs rep.initialState rep.states in

		let validAccSts = Set.subset rep.acceptStates rep.states in

		let currentSt = transitionGet1 rep.transitions in
		let readSy = transitionGet2 rep.transitions in
		let newSt = transitionGet3 rep.transitions in
		let writeSy = transitionGet4 rep.transitions in

		let alpha = Set.union (Set.make [empty]) rep.tapeAlphabet in
	
		let validTrns = (Set.subset currentSt rep.states) &&
								(Set.subset newSt rep.states) && 
								(Set.subset readSy alpha) &&
								(Set.subset writeSy alpha) in

		let emptyInAlph = Set.belongs empty rep.tapeAlphabet in

		let emptyIsEmpty = rep.empty = empty in

		let markersSize = ((Set.size rep.markers) = 2 || (Set.size rep.markers) = 0) in 

		if not validInitSt then
			Error.error name
				"The initial state does not belong to the set of all states" ()
		;

		if not validAccSts then
			Error.error name
				"Some accept states do not belong to the set of all states" ()
		;

		if not validTrns then
			Error.error name
				"Some transitions are invalid" ()
		;

		if not emptyInAlph then
			Error.error name
				"Empty symbol isn't in the tape alphabet" ()
		;

		if not emptyIsEmpty then
			Error.error name
				"The empty symbol is not correct, change it to 'B'" ()
		;
		if not markersSize then
			Error.error name
				"Too little or too many markers given" ()
		)

	let downgradeModelToFiniteAutomaton rep = 
		let alphaB = Set.union (Set.make [empty]) rep.tapeAlphabet in
		let fa: FiniteAutomaton.t = {
				alphabet = alphaB;
				states = rep.states;
				initialState = rep.initialState;
				transitions = transitionsTm2Fa rep.transitions;
				acceptStates = rep.acceptStates
			} in
		new FiniteAutomaton.model (Arg.Representation fa)

	let reachable s rep = 
		let fa = downgradeModelToFiniteAutomaton rep in
			fa#reachable s

	let productive rep =
		if rep.criteria then
			let fa = downgradeModelToFiniteAutomaton rep in
				fa#productive
		else rep.states
		
	let getUsefulStates rep =
		Set.inter (productive rep) (reachable rep.initialState rep)

	let getUselessStates rep =
		Set.diff rep.states (getUsefulStates rep)

	let isDeterministic rep =
		let fa = downgradeModelToFiniteAutomaton rep in
			fa#isDeterministic

	let cleanUselessStates rep =
		let usfSts = getUsefulStates rep in
		let usfTrs = Set.filter (fun (a,_,c,_,_) -> Set.belongs a usfSts && Set.belongs c usfSts) rep.transitions in
		let tapeAlf = Set.add empty (transitionGetSymbs usfTrs) in
		let entryAlf = Set.inter tapeAlf rep.entryAlphabet in
		let newAccSts = Set.inter rep.acceptStates usfSts in
			{
				entryAlphabet = entryAlf;
				tapeAlphabet = tapeAlf;
				empty = rep.empty;
				states = usfSts;
				initialState = rep.initialState;
				transitions = usfTrs;
				acceptStates = newAccSts;
				criteria = rep.criteria;
				markers = rep.markers
			} 

	let areAllStatesUseful rep =
		let fa = downgradeModelToFiniteAutomaton rep in
			fa#areAllStatesUseful

	let convertToStopCriteriaOld rep =
		let stEnd = state "END" in
		let endState = stEnd in
		let completeStates = Set.union (rep.states) (Set.make [endState]) in

		let newAlph = Set.union (rep.tapeAlphabet) (Set.make [empty]) in
		let nonAcceptStates =  Set.filter (fun x -> not (Set.exists (fun y -> y = x) rep.acceptStates)) rep.states in

		let missingSymbols st = Set.filter (fun x -> not (Set.exists (fun (a,b,_,_,_) -> a = st && b = x) rep.transitions)) newAlph in
		let createTransitions st = Set.map (fun x -> (st,x,endState,x,R)) (missingSymbols st) in
		let newTransList = Set.flatten (Set.map (fun x -> createTransitions x) nonAcceptStates) in
		let fullTransitions = Set.union (rep.transitions) (newTransList) in
			{
				entryAlphabet = rep.entryAlphabet;
				tapeAlphabet = rep.tapeAlphabet;
				empty = rep.empty;
				states = completeStates;
				initialState = rep.initialState;
				transitions = fullTransitions;
				acceptStates = Set.empty;
				criteria = false;
				markers = rep.markers
			}

	let convertToStopCriteria rep =
		{
			entryAlphabet = rep.entryAlphabet;
			tapeAlphabet = rep.tapeAlphabet;
			empty = rep.empty;
			states = rep.states;
			initialState = rep.initialState;
			transitions = rep.transitions;
			acceptStates = Set.empty;
			criteria = false;
			markers = rep.markers
		}

	let hasState st rep = 
		Set.belongs st rep.states

	let hasTransition trs rep =
		Set.belongs trs rep.transitions

	let isFinal st rep = 
		Set.belongs st rep.acceptStates

	let isInitial st rep = 
		st = rep.initialState
	
	let addState s rep =
		{
			entryAlphabet = rep.entryAlphabet;
			tapeAlphabet = rep.tapeAlphabet;
			empty = rep.empty;
			states = Set.add s rep.states;
			initialState = rep.initialState;
			transitions = rep.transitions;
			acceptStates = rep.acceptStates;
			criteria = rep.criteria;
			markers = rep.markers
		}
			
	let addInitialState s rep =
		{
			entryAlphabet = rep.entryAlphabet;
			tapeAlphabet = rep.tapeAlphabet;
			empty = rep.empty;
			states = Set.add s rep.states;
			initialState = s;
			transitions = rep.transitions;
			acceptStates = rep.acceptStates;
			criteria = rep.criteria;
			markers = rep.markers
		}

	let addFinalState s rep =
		{
			entryAlphabet = rep.entryAlphabet;
			tapeAlphabet = rep.tapeAlphabet;
			empty = rep.empty;
			states = Set.add s rep.states;
			initialState = rep.initialState;
			transitions = rep.transitions;
			acceptStates = Set.add s rep.acceptStates;
			criteria = true;
			markers = rep.markers
		}

	let removeState s rep =
		if s != rep.initialState then
			{
				entryAlphabet = rep.entryAlphabet;
				tapeAlphabet = rep.tapeAlphabet;
				empty = rep.empty;
				states = Set.remove s rep.states;
				initialState = rep.initialState;
				transitions = Set.filter (fun (a,_,c,_,_) -> a = s || c = s) rep.transitions;
				acceptStates = Set.remove s rep.acceptStates;
				criteria = rep.criteria;
				markers = rep.markers
			}
		else 
			rep

	let changeStateToInitial s rep =
		{
			entryAlphabet = rep.entryAlphabet;
			tapeAlphabet = rep.tapeAlphabet;
			empty = rep.empty;
			states = rep.states;
			initialState = s;
			transitions = rep.transitions;
			acceptStates = rep.acceptStates;
			criteria = rep.criteria;
			markers = rep.markers
		}

	let changeStateFromFinal s rep =
		let newAcceptSts = Set.remove s rep.acceptStates in
		{
			entryAlphabet = rep.entryAlphabet;
			tapeAlphabet = rep.tapeAlphabet;
			empty = rep.empty;
			states = rep.states;
			initialState = rep.initialState;
			transitions = rep.transitions;
			acceptStates = newAcceptSts;
			criteria = if (Set.size newAcceptSts) = 0 then false else true;
			markers = rep.markers
		}

	let changeStateToFinal s rep =
		{
			entryAlphabet = rep.entryAlphabet;
			tapeAlphabet = rep.tapeAlphabet;
			empty = rep.empty;
			states = rep.states;
			initialState = rep.initialState;
			transitions = rep.transitions;
			acceptStates = Set.add s rep.acceptStates;
			criteria = true;
			markers = rep.markers
		}

	let renameState st name rep =
		let initial = if st = rep.initialState then name else rep.initialState in
		let newStates = Set.remove st (Set.add name rep.states) in
		let newTransitions = Set.map (fun (s,a,t,b,c) -> 
			if s = st && t = st then (name,a,name,b,c) 
			else if s = st then (name,a,t,b,c) 
			else if t = st then (s,a,name,b,c) 
			else (s,a,t,b,c)
		) rep.transitions in
		let newAcceptStates = Set.map (fun s -> if s = st then name else s) rep.acceptStates in
			{
				entryAlphabet = rep.entryAlphabet;
				tapeAlphabet = rep.tapeAlphabet;
				empty = rep.empty;
				states = newStates;
				initialState = initial;
				transitions = newTransitions;
				acceptStates = newAcceptStates;
				criteria = true;
				markers = rep.markers
			}

	let addTransition trs rep =
		{
			entryAlphabet = rep.entryAlphabet;
			tapeAlphabet = rep.tapeAlphabet;
			empty = rep.empty;
			states = rep.states;
			initialState = rep.initialState;
			transitions = Set.add trs rep.transitions;
			acceptStates = rep.acceptStates;
			criteria = rep.criteria;
			markers = rep.markers
		}

	let removeTransition trs rep =
		{
			entryAlphabet = rep.entryAlphabet;
			tapeAlphabet = rep.tapeAlphabet;
			empty = rep.empty;
			states = rep.states;
			initialState = rep.initialState;
			transitions = Set.remove trs rep.transitions;
			acceptStates = rep.acceptStates;
			criteria = rep.criteria;
			markers = rep.markers
		}
end

module TuringMachine =
struct
	include TuringMachineSupport
	open TuringMachineAccept
	open TuringMachineGenerate
	open TuringMachineLB
	open TuringMachinePrivate

	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
	let make (arg: t Arg.alternatives): t = make arg validate

	(* Exercices support *)
	let checkProperty (fa: t) (prop: string) =
		match prop with
			| "turing machine" -> true
			| _ -> Model.checkProperty prop		
	let checkExercise ex tm = Model.checkExercise ex (accept tm) (checkProperty tm)
	let checkExerciseFailures ex tm = Model.checkExerciseFailures ex (accept tm) (checkProperty tm)

	(* Ops *)
	let stats = Model.stats
	let accept = accept
	let acceptFull = acceptFull
	let generate = generate
	let configurationGet1 = configurationGet1

	(* Class *)
	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model arg kind as super
			val representation: t = Entity.create arg fromJSon
			(* placement of the initializer is crucial - after representation *)
			initializer Entity.endCreation self#id self#representation kind validate
		(* Representation *)
			method representation: t = representation
		(* Kind *)
			method isTuringMachine : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 self#id representation
			method show: unit = show representation
			method show2: unit = show2 self#id representation
		(* Ops *)

(*		VER BEM!	method toJSon: JSon.t =
				JSon.append (super#toJSon) (toJSon representation) *)
				
			method acceptOld(w: word): bool =
				acceptOld w representation

			method accept (w: word): bool =
				accept representation w

			method acceptFull (w:word): bool * 'c list * 'c set list =
				acceptFull representation w

			method generate (length: int): words =
				generate representation length

			method reachable (s:state): states =
				reachable s representation

			method productive : states =
				productive representation
				
			method getUsefulStates: states =
				getUsefulStates representation

			method getUselessStates: states =
				getUselessStates representation

			method isDeterministic: bool =
				isDeterministic representation

			method cleanUselessStates: t =
				cleanUselessStates representation

			method areAllStatesUseful: bool =
				areAllStatesUseful representation

			method acceptLB (w: word) : bool =
				acceptLB w representation

			method acceptFullLB (w: word) : bool * 'c list * 'c set list =
				acceptFullLB w representation

			method isLB : bool = 	
				isLB representation

			method convertToStopCriteria: model =
				let tm = convertToStopCriteria representation in
					new model (Arg.Representation tm)

			method hasState(s: state): bool =
				hasState s representation

			method hasTransition (trs: transition): bool =
				hasTransition trs representation

			method isFinal (st: state): bool =
				isFinal st representation

			method isInitial (st: state): bool =
				isInitial st representation

			method addState (s: state) : t =
				addState s representation

			method addInitialState (s: state) : t =
				addInitialState s representation

			method addFinalState (s: state) : t =
				addFinalState s representation
		
			method removeState (s: state) : t =
				removeState s representation

			method changeStateToInitial (s: state) : t =
				changeStateToInitial s representation

			method changeStateToFinal (s: state) : t =
				changeStateToFinal s representation

			method changeStateFromFinal (s: state) : t =
				changeStateFromFinal s representation
			
			method renameState (s:state) (newS:state): t =
				renameState s newS representation

			method addTransition (trs:transition) : t =
				addTransition trs representation

			method removeTransition (trs:transition) : t =
				removeTransition trs representation

			method downgradeModelToFiniteAutomaton: FiniteAutomaton.model =
				downgradeModelToFiniteAutomaton representation
			
			method checkProperty prop =
				match prop with
					| "deterministic" -> self#isDeterministic
					| "linear bounded" -> self#isLB
					| "acceptance by states" -> representation.criteria
					| "acceptance by stop" -> not representation.criteria
					| "turing machine" -> true
					| _ -> super#checkProperty prop
		
		(* Learn-OCaml support *)
		(* incomplete *)
			method moduleName =
				"TuringMachine"

			method xTypeName =
				"turingMachine"
				
			method xTypeDeclString : string = ""

			method toDisplayString (name: string): string = ""

			method example : JSon.t =
				JSon.parse {|
				{
					kind : "turing machine"
				}
			|}
	end
end

module TuringMachineTop =
struct
	open TuringMachine
	open TuringMachineX

	let tmI tm = internalize tm
	let tmX tm = externalize tm

	let tm_load file = tmX (make (Arg.File file))
	let tm_text text = tmX (make (Arg.Text text))
	let tm_json json = tmX (make (Arg.JSon json))
	let tm_predef name = tm_text (Examples.example name)

	let confX (s, tl, tr) =
		state2str s, word2str (List.rev tl)
		^ "[" ^ symb2str (List.hd tr) ^ "]"
		^ word2str (List.tl tr)
	let pathX (p: path) = pathX confX p
	let trailX (t: trail) = trailX confX t
	
	let stats () = RuntimeControl.stats ()

	let tm_accept tm w = accept (tmI tm) (wordI w)

	let tm_path tm w =
		let (r,p,t) = acceptFull (tmI tm) (wordI w) in
			pathX p

	let tm_trail tm w =
		let (r,p,t) = acceptFull (tmI tm) (wordI w) in
			trailX t

	let tm_generate tm len = wordsX (generate (tmI tm) len)
end

open TuringMachineTop

(*

--------------------
let tm = tm_predef "tm_astar2";;

tm_generate tm 4;;

tm_accept tm "abab";;
tm_accept tm "abcab";;

tm_path tm "abab";;
tm_path tm "abcab";;

tm_trail tm "abab";;
--------------------

*)
