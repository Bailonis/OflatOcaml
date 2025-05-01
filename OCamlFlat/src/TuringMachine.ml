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
 * jan/2025 (amd) - Adapted for multitape TMs and also reorganized.
 * ???/2023 (ml) - Implementation of singletape TMs.
 * jun/2022 (amd) - Initial skeleton.
 *)

(*
 * Description: Multi-tape Turing machine functionality.
 *)

open BasicTypes

module TuringMachineAcceptPrivate =
struct
	open TuringMachineSupport

	let initialConfigs (tm: t) (w: word): configurations =
		let n = nTapes tm in
		let emptyTape = ([empty], [empty]) in
		let firstTape = ([empty], w@[empty]) in
		let emptyTapes = List.init (n-1) (fun _ -> emptyTape) in
		let conf = (tm.initialState, firstTape::emptyTapes) in
			Set.make [conf]

	let getCurr (ps: tapes): symbolM =
		List.map (fun (l,r) -> List.hd r) ps
	
	let isAcceptingConfig (tm: t) ((s,ps): configuration): bool =
		let curr = getCurr ps in
		let ts = tm.transitions in
		let triggered = Set.filter (fun (a,b,_,_,_) -> a = s && b = curr) ts in
		let stops = Set.isEmpty triggered in
			if tm.criteria then
				stops && Set.belongs s tm.acceptStates
			else
				stops

	let fix (p: halfTape): halfTape =	
		match p with
		| [] -> [empty]
		| _ -> p

	let updateTape (p: tape) (d: symbol) (e: direction): tape =
		match p with
		| l::ls, _::rs ->
			(match e with
			| R -> (d::l::ls, fix rs)
			| L -> (fix ls, l::d::rs)
			| S -> (l::ls, d::rs))
		| _, _ -> failwith "nextTape"
	
	let rec map3 f l l1 l2 =
		match l, l1, l2 with
		| [], [], [] -> []
		| x::xs, y::ys, z::zs -> f x y z:: map3 f xs ys zs
		| _, _, _ -> failwith "map3"

	let nextConfig (tm: t) (tr: transition) (conf: configuration): configurations =
		match tr, conf with
		| (a,b,c,d,e), (s,ps) when a = s && b = getCurr ps ->
			let ps2 = map3 updateTape ps d e in
				Set.make [(c, ps2)]
		| _, _ -> Set.empty

	let nextConfigs (tm: t) (config: configuration): configurations = 
		Set.flatMap (fun tr -> nextConfig tm tr config) tm.transitions

	let accept (tm: t) (w: word): bool =
		Model.checkWord tm.entryAlphabet w
		&&
		Model.accept tm w
				initialConfigs
				nextConfigs
				isAcceptingConfig

	let acceptFull (tm: t) (w: word): bool * path * trail = 
		if Model.checkWord tm.entryAlphabet w then
			Model.acceptFull tm w
						initialConfigs nextConfigs isAcceptingConfig
		else
			(false, [], [])
end

module TuringMachineGeneratePrivate =
struct
	open TuringMachineSupport
	open TuringMachineAcceptPrivate

	let generate (tm: t) length =
		Model.generateDumb tm tm.entryAlphabet
				length initialConfigs nextConfigs isAcceptingConfig
end

module TuringMachineLBPrivate =
struct
	open TuringMachineSupport
	open TuringMachineAcceptPrivate

	let isLB (rep: t) = 
		List.length rep.lbMarkers = 2

	let validateLB (name: string) (rep: t) =
		(* pre: List.length rep.lbMarkers > 0 && validMarkers *)
		let lbMarkers = Set.make rep.lbMarkers in
		
		let inEntryAlph =
			Set.subset lbMarkers rep.entryAlphabet in
	
		let validSymbolM (s: symbolM) =
			let t = Set.make s in
			let i = Set.inter t lbMarkers in
			let withoutMarker =  Set.isEmpty i in
				withoutMarker || Set.size t = 1 in
		
		let validSymbolMs =
			Set.for_all validSymbolM (getTransSymbolMs rep) in
			
		let isLeftSafe  =
			let leftM = multi rep (lbLeft rep) in
			let lM = multi rep L in
			let safeT (_,b,_,d,e) = b <> leftM || (d = leftM && e <> lM) in
				Set.for_all safeT rep.transitions in

		let isRightSafe =
			let rightM = multi rep (lbRight rep) in
			let rM = multi rep R in
			let safeT (_,b,_,d,e) = b <> rightM || (d = rightM && e <> rM) in
				Set.for_all safeT rep.transitions in

		if not inEntryAlph then
			Error.error name
				"The LB markers must belong to the entry alphabet" ()
		;	
		if not validSymbolMs then	
			Error.error name
				"Each LB marker cannot be mixed with other symbols in a transition" ()
		;
		if not isLeftSafe then
			Error.error name
				"Some transition does not respect the left mark" ()
		;
		if not isRightSafe then
			Error.error name
				"Some transition does not respect the right mark" ()

	let checkLB rep: bool =
		let ok = isLB rep in
		let mesg = "Not a LB Turing machine" in
			if not ok then Error.warning mesg;
			ok

	let acceptLB w rep =
		checkLB rep
		&&
		accept rep ([lbLeft rep]@w@[lbRight rep])

	let acceptFullLB w rep =
		if checkLB rep then
			acceptFull rep ([lbLeft rep]@w@[lbRight rep])
		else
			(false, [], [])
end

module TuringMachinePrivate =
struct
	open TuringMachineSupport

(*
	let getDefaultMachine: t = {
		entryAlphabet = Set.empty;
		tapeAlphabet = Set.add empty Set.empty;	
		empty = empty;
		states = Set.add "START" Set.empty;
		initialState = "START";
		transitions = Set.empty;
		acceptStates = Set.empty;
		criteria = false;
		lbMarkers = Set.empty
	}
*)

	let validate (name: string) (rep: t) =
		let trns = rep.transitions in
		let trns1 = Set.map (fun (a,_,_,_,_) -> a) trns in
		let trns2 = Set.map (fun (_,b,_,_,_) -> b) trns in
		let trns3 = Set.map (fun (_,_,c,_,_) -> c) trns in
		let trns4 = Set.map (fun (_,_,_,d,_) -> d) trns in
		let trns5 = Set.map (fun (_,_,_,_,e) -> e) trns in
		let alpha = Set.add empty rep.tapeAlphabet in
		
		let validInitSt =
			Set.belongs rep.initialState rep.states in
		let validAccSts =
			Set.subset rep.acceptStates rep.states in

		let validEntryAlph =
			Set.subset rep.entryAlphabet rep.tapeAlphabet in	
		let emptyInAlph =
			Set.belongs empty rep.tapeAlphabet
			&& not (Set.belongs empty rep.entryAlphabet) in
		let emptyIsEmpty =
			rep.empty = empty in
			
		let nTapes = nTapes rep in
		
		let validLengths =
			Set.for_all (fun s -> List.length s = nTapes) trns2
			&& Set.for_all (fun s -> List.length s = nTapes) trns4
			&& Set.for_all (fun s -> List.length s = nTapes) trns5 in

		let validTrns =
			Set.subset trns1 rep.states
			&& Set.subset trns3 rep.states
			&& Set.subset (getTransSymbols rep) alpha
			&& Set.subset (getTransDirections rep) allDirections in

		let validMarkers =
			if List.length rep.lbMarkers = 2 then
				let l = List.nth rep.lbMarkers 0 in
				let r = List.nth rep.lbMarkers 1 in
					l <> r
			else
				List.length rep.lbMarkers = 0 in

		let validCriteria =
			rep.criteria || Set.size rep.acceptStates = 0 in

		if not validInitSt then
			Error.error name
				"The initial state does not belong to the set of all states" ()
		;
		if not validAccSts then
			Error.error name
				"Some accept states do not belong to the set of all states" ()
		;
		if not validEntryAlph then
			Error.error name
				"The entry alphabel must be contained in the tape alphabet" ()
		;
		if not validLengths then
			Error.error name
				"Some transitions have elements with inconsistent lengths" ()
		;
		if not validTrns then
			Error.error name
				"Some transitions are invalid" ()
		;
		if not emptyInAlph then
			Error.error name (
				"The empty symbol must be in the tape alphabet"
				^ " but not in the entry alphabet") ()
		;
		if not emptyIsEmpty then
			Error.error name
				"The empty symbol is not correct, change it to 'B'" ()
		;
		if not validCriteria then
			Error.error name
				"A TM that uses the stop criteria cannot have accept states" ()
		;
		if List.length rep.lbMarkers > 0 && validMarkers then
			TuringMachineLBPrivate.validateLB name rep

	let downgradeModelToFiniteAutomaton rep = 
		let alphaB = Set.union (Set.make [empty]) rep.tapeAlphabet in
		let transitionsTm2Fa = Set.map (fun (a,b,c,_,_) -> (a,List.hd b,c)) in
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
		let ts = rep.transitions in
		let usfSts = getUsefulStates rep in
		let usfTrs = Set.filter (fun (a,_,c,_,_)
				-> Set.belongs a usfSts && Set.belongs c usfSts) ts in
		let tapeAlf = Set.add empty (getTransSymbols rep) in
		let entryAlf = Set.inter tapeAlf rep.entryAlphabet in
		let newAccSts = Set.inter rep.acceptStates usfSts in
			{ rep with
				entryAlphabet = entryAlf;
				tapeAlphabet = tapeAlf;
				states = usfSts;
				transitions = usfTrs;
				acceptStates = newAccSts }
			(* This and all the other updates of a TM need
				to be analysed, to check for the validity
				of the resulting TM. - AMD  *)

	let areAllStatesUseful rep =
		let fa = downgradeModelToFiniteAutomaton rep in
			fa#areAllStatesUseful

(*	let convertToStopCriteria rep =
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
				lbMarkers = rep.lbMarkers
			}
*)

	let convertToStopCriteria rep =
		{ rep with
			acceptStates = Set.empty;
			criteria = false }

	let hasState st rep = 
		Set.belongs st rep.states

	let hasTransition trs rep =
		Set.belongs trs rep.transitions

	let isFinal st rep = 
		Set.belongs st rep.acceptStates

	let isInitial st rep = 
		st = rep.initialState
	
	let addState s rep =
		{ rep with
			states = Set.add s rep.states }
			
	let addInitialState s rep =
		{ rep with
			states = Set.add s rep.states;
			initialState = s }

	let addFinalState s rep =
		{ rep with
			states = Set.add s rep.states;
			acceptStates = Set.add s rep.acceptStates;
			criteria = true }

	let removeState s rep =
		if s = rep.initialState then
			rep
		else
		{ rep with
			states = Set.remove s rep.states;
			transitions = Set.filter (fun (a,_,c,_,_) ->
							a <> s || c <> s) rep.transitions;
			acceptStates = Set.remove s rep.acceptStates }

	let changeStateToInitial s rep =
		{ rep with
			initialState = s }

	let changeStateFromFinal s rep =
		let newAcceptSts = Set.remove s rep.acceptStates in
		{ rep with
			acceptStates = newAcceptSts;
			criteria = Set.size newAcceptSts <> 0 }

	let changeStateToFinal s rep =
		{ rep with
			acceptStates = Set.add s rep.acceptStates;
			criteria = true }

	let renameState st name rep =
		let initial = if st = rep.initialState then name else rep.initialState in
		let newStates = Set.remove st (Set.add name rep.states) in
		let newTransitions = Set.map
					(fun (s,a,t,b,c) -> 
						if s = st && t = st then (name,a,name,b,c)
						else if s = st then (name,a,t,b,c)
						else if t = st then (s,a,name,b,c)
						else (s,a,t,b,c)
					) rep.transitions in
		let newAcceptStates =
			Set.map (fun s -> if s = st then name else s) rep.acceptStates in
				{ rep with
					states = newStates;
					initialState = initial;
					transitions = newTransitions;
					acceptStates = newAcceptStates;
					criteria = true }

	let addTransition trs rep =
		{ rep with
			transitions = Set.add trs rep.transitions }

	let removeTransition trs rep =
		{ rep with
			transitions = Set.remove trs rep.transitions }
end

module TuringMachine =
struct
	include TuringMachineSupport
	open TuringMachineAcceptPrivate
	open TuringMachineGeneratePrivate
	open TuringMachineLBPrivate
	open TuringMachinePrivate

	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
	let make (arg: t Arg.alternatives): t = make arg validate

	(* Exercices support *)
	let checkProperty (tm: t) (prop: string) =
		match prop with
			| "turing machine" -> true
			| _ -> Model.checkProperty prop		
	let checkExercise ex (tm: t) = Model.checkExercise ex (accept tm) (checkProperty tm)
	let checkExerciseFailures ex (tm: t) = Model.checkExerciseFailures ex (accept tm) (checkProperty tm)

	(* Ops *)
	let stats = Model.stats
	let accept = accept
	let acceptFull = acceptFull
	let generate = generate
	let isLB = isLB
	let initialConfigs = initialConfigs

	(* Class *)
	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model (make2 arg) as super
		(* Representation *)
			method representation: t = representation
		(* Kind *)
			method isTuringMachine : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Ops *)				
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
				
			method xTypeDeclString : string = "todo"

			method toDisplayString (name: string): string = "todo"

			method example : JSon.t =
				JSon.parse {|
				{
					kind : "turing machine todo"
				}
			|}

	end

end

module TuringMachineTop =
struct
	open TuringMachine
	open TuringMachineX

	let tm_load file = tmX (make (Arg.File file))
	let tm_text text = tmX (make (Arg.Text text))
	let tm_json json = tmX (make (Arg.JSon json))
	let tm_predef name = tm_text (Examples.example name)

	let tm_ntapes tmx =
		nTapes (tmI tmx)

	let tm_init tmx w =
		let is = initialConfigs (tmI tmx) (wordI w) in
			confsX is

	let stats () = RuntimeControl.stats ()

	let tm_accept tm w = accept (tmI tm) (wordI w)

	let tm_path tm w =
		let (r,p,t) = acceptFull (tmI tm) (wordI w) in
			pathX p

	let tm_trail tm w =
		let (r,p,t) = acceptFull (tmI tm) (wordI w) in
			trailX t

	let tm_generate tm len = wordsX (generate (tmI tm) len)


	open TuringMachineS
	let tm_init tmx w =
		let is = initialConfigs (tmI tmx) (wordI w) in
			confsS is

end

open TuringMachineTop

(*

--------------------

#print_depth 10000;;
#print_length 10000;;

let tm = tm_predef "tm_translate";;
let w = "aba";;
tm_ntapes tm;;
tm_init tm w;;
tm_accept tm "aba";;
tm_accept tm "abac";;
tm_path tm "aba";;
tm_trail tm "aba";;

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
