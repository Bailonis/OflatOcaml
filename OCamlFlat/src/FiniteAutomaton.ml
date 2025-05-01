(*
 * FiniteAutomaton.ml
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
 * set/2022 (amd) - Full restructuration.
 * jul/2021 (amd) - Improved Learn-OCaml support and error handling.
 * jun/2021 (amd) - Added checks for epsilon ('~') in the #validate method.
 * may/2021 (amd) - Added support for an extern representation.
 * jan/2021 (amd) - Module in an independent file and some cleanup.
 * dec/2019 (jg) - Main functionalities.
 * jun/2019 (amd) - Initial skeleton, inside the big file "OCamlFlat.ml".
 *)

(*
 * Description: Finite automata functionality.
 *
 * TODO: More cleanup.
 *)

open BasicTypes

module FiniteAutomatonAccept = (* AMD *)
struct
	open FiniteAutomatonSupport

	let initialConfigs fa w : configurations =
		Set.make [(fa.initialState,w)]

	let isAcceptingConfig fa (st,w) : bool =
		Set.belongs st fa.acceptStates && w = []

	let nextConfigs fa (st,w) : configurations =
		match w with
		| [] ->
			let empty = Set.filter (fun (st1,sy,_) -> st1 = st && sy = epsilon) fa.transitions in
				Set.map (fun (_,_,st2) -> (st2,[])) empty
		| x::xs -> 
			let nonEmpty = Set.filter (fun (st1,sy,_) -> st1 = st && sy = x) fa.transitions in
			let empty = Set.filter (fun (st1,sy,_) -> st1 = st && sy = epsilon) fa.transitions in
			let res1 = Set.map (fun (_,_,st2) -> (st2,xs)) nonEmpty in
			let res2 = Set.map (fun (_,_,st2) -> (st2,w)) empty in
				Set.union res1 res2

	let accept (fa: t) (w: word) : bool =
		ignore (Model.checkWord fa.alphabet w);
		Model.accept fa w initialConfigs nextConfigs isAcceptingConfig

	let acceptFull (fa: t) (w: word) : bool * path * trail =
		ignore (Model.checkWord fa.alphabet w);
		Model.acceptFull fa w initialConfigs nextConfigs isAcceptingConfig
end

module FiniteAutomatonGenerate = (* AMD *)
struct
	open FiniteAutomatonSupport
	open FiniteAutomatonAccept

	let nextConfigs2 fa _ (st,w) =
		let selected = Set.filter (fun (st1,_,_) -> st1 = st) fa.transitions in
			Set.map (fun (_,sy,st2) -> (st2,if sy = epsilon then w else sy::w)) selected

	let isAcceptingConfig2 fa (st,_) =
		Set.belongs st fa.acceptStates

	let getWord (_,w) = List.rev w;;

	let generate (fa: t) (len: int): words =
		Model.generate fa len initialConfigs nextConfigs2 isAcceptingConfig2 getWord

	let generateDumb (fa: t) (len: int): words = 
		Model.generateDumb fa fa.alphabet len initialConfigs nextConfigs isAcceptingConfig
end

module FiniteAutomatonPrivate =
struct
	open FiniteAutomatonSupport

	(*------Auxiliary functions---------*)

	(* get starting state, symbol, and/or end state of all transitions in set *)
	let transitionGet1 trns = Set.map ( fun (a,_,_) -> a ) trns
	let transitionGet2 trns = Set.map ( fun (_,b,_) -> b ) trns
	let transitionGet3 trns = Set.map ( fun (_,_,c) -> c ) trns
	let transitionGet23 trns = Set.map (fun (_,b,c) -> (b,c)) trns

	(* fuse all states into a new state *)
	let fuseStates sts =
		let l = List.map state2str sts in
			state (String.concat "_" l)

	(* checks if set ts has at least one transition from state st through symbol sy *)
	let hasTrans st sy ts = Set.exists (fun (x,y,_) -> x = st && y = sy) ts

	(* returns the set of state st and all its states reachable by an epsilon transition *)
	let nextEpsilon1 st ts =
		let trns = Set.filter (fun (a,b,c) -> st = a && b = epsilon) ts in
		let nextStates = transitionGet3 trns in
			Set.add st nextStates

	(* returns the set of states sts and all states reachable from sts through epsilon transitions *)
	let rec closeEmpty sts t =
		let ns = Set.flatMap (fun st -> nextEpsilon1 st t) sts in
			if (Set.subset ns sts) then ns else closeEmpty (Set.union sts ns) t

	(* futuro
		let rec closeEmpty sts t =
			Set.fixedPoint (Set.flatMap (fun st -> nextEpsilon1 st t)) sts
	*)

	(* returns states reachable from st through symbol sy *)
	let nextStates st sy t =
		let n = Set.filter (fun (a,b,c) -> st = a && sy = b) t in
			transitionGet3 n

	(**
	* This function verifies if the automaton is valid.
	* An automaton is considered valid if its initial and acceptance states belong to the set of all its states
	* and if all its transitions have states and symbols belonging to the set of all its states and its alphabet respectively.
	*
	* Desc: If the automaton is invalid, the cause could derive from any combination of the following
	* three options: either the initial state, one of the acceptance states, or one of the transitions does not follow the
	* previously discussed predicate. This method will print to the console stating which combination of these options caused
	* the automaton to be invalid
	*)
	let validate (name: string) (fa: t): unit =
	(* the alphabet must not contain " " *)
		let validAlphabet = not (Set.belongs epsilon fa.alphabet) in
	(* does initial state belong to the set of all states *)
		let validInitSt = Set.belongs fa.initialState fa.states in
	(* are all accepted states members of all states *)
		let validAccSts = Set.subset fa.acceptStates fa.states in
		let fromSt = transitionGet1 fa.transitions in
		let sy = transitionGet2 fa.transitions in
		let toSt = transitionGet3 fa.transitions in
		let alpha = Set.add epsilon fa.alphabet in
	(* do all transitions have states belonging to all states and symbols belonging to the alphabet *)
		let validTrns = (Set.subset fromSt fa.states)
					&& (Set.subset sy alpha) && (Set.subset toSt fa.states) in
			if not validAlphabet then
				Error.error name "The alphabet contains epsilon '~', and it should not" ();
			if not validInitSt then
				Error.error name "The initial state does not belong to the set of all states" ();
			if not validAccSts then
				Error.error name "Some accept states do not belong to the set of all states" ();
			if not validTrns then
				Error.error name "Some transitions are invalid" ()

	(**
	* This function verifies if the given word is accepted by the automaton
	* @param w:word -> word to be tested for acceptance
	* @returns bool -> true if w is accepted and false otherwise
	* Desc: Checks if the automaton accepts word w using configurations (that is, pairs formed by a state and
	* a remaining word) and a breadth-first approach as to deal with potential non-termination
	*)
	let acceptBreadthFirst (fa: t) (w: word): bool = false
	(*
		let rec acc cf t sta =
			match cf with
				[] -> false
				|(st,[])::ls ->
					let accepts = (Set.inter (closeEmpty (Set.make [st]) t) sta) <> Set.empty in
						accepts || acc ls t sta
				|(st,x::xs)::ls ->
					let n = nextStates st x t in
					let cfn = Set.map (fun c -> (c,xs)) n in
					let n2 = nextStates st epsilon t in
					let cfn2 = Set.map (fun c -> (c,x::xs)) n2 in
						acc (Set.flatten (Set.make [ls;cfn;cfn2])) t sta in
		acc (Set.make [(fa.initialState,w)]) fa.transitions fa.acceptStates
	*)

	

	(**
	* This function verifies if the given word is accepted by the automaton
	* @param w:word -> word to be accepted
	* @returns bool -> true if w is accepted and false otherwise
	* Desc: Checks if the automaton accepts word w using functions over sets of states
	*)
	let accept_disabled (fa: t) (w: word): bool =
		let transition sts sy t =
			let nsts = Set.flatMap (fun st -> nextStates st sy t) sts in
				Set.union nsts (closeEmpty nsts t) in
		let rec acceptX sts w t =
			match w with
				[] -> (Set.inter sts fa.acceptStates) <> Set.empty
				|x::xs -> let nextSts = transition sts x t in
					nextSts <> Set.empty && acceptX nextSts xs t in
		let i = closeEmpty (Set.make [fa.initialState]) fa.transitions in
			acceptX i w fa.transitions


	let acceptWithTracing (fa: t) (w:word): unit =
		let transition sts sy t =
			let nsts = Set.flatMap (fun st -> nextStates st sy t) sts in
				Set.union nsts (closeEmpty nsts t) in
		let rec acceptX sts w t =
			match w with
				[] -> [(w,sts)]
				|x::xs -> let nextSts = transition sts x t in
							let res = acceptX nextSts xs t in
								(w,sts)::res in
		let i = closeEmpty (Set.make [fa.initialState]) fa.transitions in
		let res = acceptX i w fa.transitions in
		let printRes w sts =
			Util.print ["('"; word2str w; "',["];
			Set.iter (fun st -> Util.print [state2str st; ";"]) sts;
			Util.print ["])"]
		in List.iter (fun (w,sts) -> printRes w sts; Util.print [";"]) res; Util.println []

	(**
	* This function generates all words of the given size which are accepted by the automaton
	* Precondition -> length >= 0
	* @param length:int -> size of all words to be generated
	* @returns words -> the set of all words with size length
	*)
	let generate_disabled (fa: t) (length: int): words =
		(* adds symbol to the left of all words *)
		let addSyToRWords symb ws = Set.map (fun l -> symb::l) ws in
		let hasAcceptState sts accSts = Set.exists (fun st -> Set.belongs st accSts) sts in
		let nxtNonEmptyTrns st ts = Set.filter (fun (a,b,_) -> a = st && b <> epsilon) ts in
		let rec gen n state transitions accSts =
			let clsEmpty = (closeEmpty (Set.make [state]) transitions) in
			if n = 0 then
				if hasAcceptState clsEmpty accSts then Set.make [[]] else Set.empty
			else
				let trnsSet = Set.flatMap (fun st -> nxtNonEmptyTrns st transitions ) clsEmpty in
				let rwords st1 l1 = gen (l1-1) st1 transitions accSts in
				let genX sy st l = addSyToRWords sy (rwords st l) in
						Set.flatMap (fun (_,sy,st) -> genX sy st n) trnsSet
		in
			gen length fa.initialState fa.transitions fa.acceptStates


	(**
	* This function generates all words up to a given size which are accepted by the automaton
	* Precondition -> length >= 0
	* @param length:int -> maximum size of all words to be generated
	* @returns words -> the set of all words with size length or less
	*)
	let generateUntil (fa: t) (length: int): words =
		(* adds symbol to the left of all words *)
		let addSyToRWords symb ws = Set.map (fun l -> symb::l) ws in
		let hasAcceptState sts accSts = Set.exists (fun st -> Set.belongs st accSts) sts in
		let nxtNonEmptyTrns st ts = Set.filter (fun (a,b,_) -> a = st && b <> epsilon) ts in
		let rec gen n state transitions accSts =
			let clsEmpty = (closeEmpty (Set.make [state]) transitions) in
			if n = 0 then
				if hasAcceptState clsEmpty accSts then Set.make [[]] else Set.empty
			else
				let trnsSet = Set.flatMap (fun st -> nxtNonEmptyTrns st transitions ) clsEmpty in
				let genX sy st l = addSyToRWords sy (gen (l-1) st transitions accSts) in
				let lenOneOrMore = Set.flatMap (fun (_,sy,st) -> genX sy st n) trnsSet in
				let lenZero = if hasAcceptState clsEmpty accSts then Set.make [[]] else Set.empty in
					Set.union lenOneOrMore lenZero
		in
			gen length fa.initialState fa.transitions fa.acceptStates


	(**
	* This function generates all states that are reachable from the given state. A state is reachable from s if there
	* exists a word that starting on s will lead to that state
	* @param s:state -> the given state
	* @returns states -> the set of all states reachable from s.
	*)
	let reachable (fa: t) (s:state): states =
		let neighbourSts st t = transitionGet3 (Set.filter (fun (a,_,_) -> a = st) t) in
		let nextStates sts t = Set.flatMap (fun st -> neighbourSts st t) sts in
		let remain s t = Set.filter (fun (a,_,_) -> not (Set.belongs a s)) t in
		let rec reach visited s t = if visited = s then Set.empty else Set.union s ( reach s (nextStates s t) (remain s t) ) in
			reach Set.empty (Set.make [s]) fa.transitions



	(**
	* This function generates all productive states. A state is productive if there exists a word that will lead said state
	* to an acceptance state
	* @returns states -> the set of all productive states
	* Desc: For each state of the automaton, this method applies the reachable method and checks if any of the resulting
	* states is an acceptance state, and if it is then that state will belong to the resulting set of productive states
	*)
	let productive (fa: t): states =
		let reachsAccSt st = Set.exists (fun s -> Set.belongs s fa.acceptStates ) (reachable fa st) in
			Set.filter (fun st -> reachsAccSt st) fa.states

	(**
	* This function generates the set of all useful states
	* @returns states -> the set of all useful states
	*)
	let getUsefulStates (fa: t): states =
		Set.inter (productive fa) (reachable fa fa.initialState)

	(**
	* This function generates the set of all non useful states
	* @returns states -> the set of all non useful states
	*)
	let getUselessStates (fa: t): states =
		Set.diff fa.states (getUsefulStates fa)

	(**
	* This function creates the equivalent automaton where all states are useful
	* @returns FiniteAutomaton.model -> the new equivalent automaton where all states are useful
	* Desc: The new automaton is created by eliminating from the original automaton all its non useful states, all transitions
	* that have a non useful state, and all symbols of the alphabet that only appear in said transitions
	*)
	let cleanUselessStates (fa: t): t =
		let usfSts = getUsefulStates fa in
		let usfTrs = Set.filter
						(fun (a,_,c) -> Set.belongs a usfSts && Set.belongs c usfSts)
						fa.transitions in
		let alf = transitionGet2 usfTrs in
		let usfAlf = Set.diff alf (Set.make [epsilon]) in
		let newAccSts = Set.inter fa.acceptStates usfSts in
		let usfSts = Set.add fa.initialState usfSts in
			{
				alphabet = usfAlf;
				states = usfSts;
				initialState = fa.initialState;
				transitions = usfTrs;
				acceptStates = newAccSts
			}

	(**
	* This function verifies if all the automaton's states are useful
	* @returns bool -> true if all states of the automaton are useful, false otherwise
	*)
	let areAllStatesUseful (fa: t): bool =
		let usfSts = getUsefulStates fa in
			Set.size fa.states = Set.size usfSts

	(**
	* This function converts the non-deterministic automaton into its deterministic equivalent
	*
	* @returns FiniteAutomaton.model -> the new deterministic automaton
	*
	* Desc: If the automaton to determinize is already deterministic,
	* the resulting automaton will be equal to the original
	*)
	let toDeterministic (fa: t): t =

		let move sts sy ts = Set.flatMap (fun st -> nextStates st sy ts ) sts in

		(* generates the set of states reachable from the given state set though the given symbol *)
		let newR oneR sy ts =
			let nxtSts = move oneR sy ts in
			let clsempty = closeEmpty nxtSts ts in
			Set.union nxtSts clsempty in

		(* creates all transitions (given state set, a given symbol, states reachable from set through given symbol) *)
		let rToTs r =
			let nxtTrans = Set.map (fun sy -> (r,sy,newR r sy fa.transitions)) fa.alphabet in
				Set.filter (fun (_,_,z) -> not (z = Set.empty)) nxtTrans in

		(* applies previous function to all state sets until no new set is generated *)
		let rec rsToTs stsD rD trnsD alph =
			let nxtTs = Set.flatMap (fun stSet -> rToTs stSet ) rD in
			let nxtRs = Set.map (fun (_,_,z) -> z) nxtTs in
			let newRs = Set.filter (fun r -> not (Set.belongs r stsD)) nxtRs in
			if newRs = Set.empty then (Set.union trnsD nxtTs) else
				rsToTs (Set.union newRs stsD) newRs (Set.union trnsD nxtTs) alph in


		let r1 = closeEmpty (Set.make [fa.initialState]) fa.transitions in

		(* all transitions of the new deterministic automaton *)
		let trnsD = rsToTs (Set.make [r1]) (Set.make [r1]) Set.empty fa.alphabet in

		let tds = Set.map (fun (a,b,c) -> (fuseStates (Set.toList a), b, fuseStates (Set.toList c))) trnsD in

		let newInitialState = fuseStates (Set.toList r1) in

		let stSet1 = Set.map (fun (a,_,_) -> a) trnsD in
		let stSet2 = Set.map (fun (_,_,c) -> c) trnsD in
		let stSet = Set.union stSet1 stSet2 in

		let isAccepState st = Set.belongs st fa.acceptStates in
		let hasAnAccepSt set = Set.exists (fun st -> isAccepState st ) set in
		let newAccStsSet = Set.filter (fun set -> hasAnAccepSt set) stSet in

		let newAllSts = Set.map (fun set -> fuseStates (Set.toList set)) stSet in
		let newAccSts = Set.map (fun set -> fuseStates (Set.toList set)) newAccStsSet in
			{
				alphabet = fa.alphabet;
				states = newAllSts;
				initialState = newInitialState;
				transitions = tds;
				acceptStates = newAccSts
			}

	(**
	* This function verifies if the automaton is deterministic
	* @returns bool -> true if automaton is deterministic, false otherwise
	* Desc: For each state s, this method checks if there exists 2 or more transitions with the same symbol from any
	* state belonging to closeempty of s, independently of the state which said transitions will lead to.
	* If there is no state for which this property is true, then the automaton is deterministic
	*)
	let isDeterministic (fa: t): bool =
		let trnsFromSt st ts = Set.filter (fun (st1,sy,_) -> st1 = st && sy <> epsilon) ts in
		let isStDeter st ts =
			let allSts = closeEmpty (Set.make [st]) ts in
			let allTs = Set.flatMap (fun st -> trnsFromSt st ts) allSts in
			let sys = transitionGet2 allTs in
				Set.size allTs = Set.size sys in
		let hasNondeterSt = Set.exists (fun st -> not (isStDeter st fa.transitions) )
								fa.states in
			not hasNondeterSt


	(* partition states by equivalence *)
	let equivalencePartition (fa: t): states set =
		let fa = toDeterministic fa in
		let fa = cleanUselessStates fa in
		let (inF, notF) = Set.partition (fun x -> Set.belongs x fa.acceptStates) fa.states in
		let distI1 = Set.product inF notF in

		let hasTransMulti sts sy ts = Set.partition (fun st -> hasTrans st sy ts) sts in
		let distI2 = Set.flatMap (fun sy -> Util.distrib2 Set.product
											(hasTransMulti fa.states sy fa.transitions))
						fa.alphabet in


		let distI = Set.union distI1 distI2 in

		let stsXSts = Set.product fa.states fa.states in

		(* generates all pairs of states that can reach the pair (st1,st2) through a transition with symbol sy *)
		let reachingSts st1 st2 sy p =
			let t1 = Set.filter (fun (_,y,z) -> z = st1 && y = sy) fa.transitions in
			let t2 = Set.filter (fun (_,y,z) -> z = st2 && y = sy) fa.transitions in
			let s1 = transitionGet1 t1 in
			let s2 = transitionGet1 t2 in
				Set.diff (Set.product s1 s2) p in

		let findAR p q = Set.flatMap (fun (a,b) -> Set.flatMap (fun sy -> reachingSts a b sy p) fa.alphabet) q in

		let distA = findAR distI distI in

		let rec aped p q = if (q = Set.empty || (Set.union p q) = stsXSts) then Set.union p q
			else aped (Set.union p q) (findAR (Set.union p q) q ) in

		let dist = aped distI distA in


		(* given for example states a b c d generates (a,a) (a,b) (a,c) (a,d) (b,b) (b,c) (b,d) (c,c) (c,d) (d,d) *)
		let rec halfCombs sts =
			match sts with
				[] -> Set.empty
				|x::xs -> Set.union (Set.product (Set.make [x]) (Set.make sts)) (halfCombs xs) in

		let halfTriang = halfCombs (Set.toList fa.states) in

		(* given set of equivalent states dicti, substitutes state st for its leftmost equivalent state according to dicti *)
		let rec translate st dicti =
			match dicti with
				[] -> st
				|(eq1,eq2)::xs -> if eq2 = st then eq1 else translate st xs in

		(* the set of equivalent state pairs are those not present in the set of distinct state pairs *)
		let equiv = Set.filter ( fun (a,b) -> not (Set.belongs (a,b) dist) &&
												not (Set.belongs (b,a) dist) ) halfTriang in

		let equivList = Set.toList equiv in
		let hasAny st1 st2 sta stb = (translate st1 equivList) = sta || (translate st2 equivList) = sta
									|| (translate st1 equivList) = stb || (translate st2 equivList) = stb in


		let rec agroup eq =
			match eq with
				| [] -> Set.empty
				| (a,b)::ls ->
					let (part1,part2) = Set.partition (fun (x,y) -> hasAny x y a b) (Set.make eq) in
					let gRemain = Set.flatMap (fun (c,d) -> Set.make [c;d]) part1 in
						Set.add (Set.union (Set.make [a;b]) gRemain) (agroup (Set.toList part2))
		in

		agroup equivList



	(**
	* This function minimizes the automaton
	* @returns FiniteAutomaton.model -> the new minimal equivalent automaton
	* Desc: The given automaton is minimized according to the process described in lecture a15.
	*)
	let minimize (fa: t): t =
		let fa = toDeterministic fa in
		let fa = cleanUselessStates fa in

		let (inF, notF) = Set.partition (fun x -> Set.belongs x fa.acceptStates) fa.states in
		let distI1 = Set.product inF notF in

		let hasTransMulti sts sy ts = Set.partition (fun st -> hasTrans st sy ts) sts in
		let distI2 = Set.flatMap (fun sy -> Util.distrib2 Set.product
											(hasTransMulti fa.states sy fa.transitions))
						fa.alphabet in


		let distI = Set.union distI1 distI2 in

		let stsXSts = Set.product fa.states fa.states in

		(* generates all pairs of states that can reach the pair (st1,st2) through a transition with symbol sy *)
		let reachingSts st1 st2 sy p =
			let t1 = Set.filter (fun (_,y,z) -> z = st1 && y = sy) fa.transitions in
			let t2 = Set.filter (fun (_,y,z) -> z = st2 && y = sy) fa.transitions in
			let s1 = transitionGet1 t1 in
			let s2 = transitionGet1 t2 in
				Set.diff (Set.product s1 s2) p in

		let findAR p q = Set.flatMap (fun (a,b) -> Set.flatMap (fun sy -> reachingSts a b sy p) fa.alphabet) q in

		let distA = findAR distI distI in

		let rec aped p q = if (q = Set.empty || (Set.union p q) = stsXSts) then Set.union p q
			else aped (Set.union p q) (findAR (Set.union p q) q ) in

		let dist = aped distI distA in


		(* given for example states a b c d generates (a,b) (a,c) (a,d) (b,c) (b,d) (c,d) *)
		let rec halfCombs sts =
			match sts with
				[] -> Set.empty
				|x::xs -> Set.union (Set.product (Set.make [x]) (Set.make xs)) (halfCombs xs) in
		let halfTriang = halfCombs (Set.toList fa.states) in

		(* given set of equivalent states dicti, substitutes state st for its leftmost equivalent state according to dicti *)
		let rec translate st dicti =
			match dicti with
				[] -> st
				|(eq1,eq2)::xs -> if eq2 = st then eq1 else translate st xs in

		(* the set of equivalent state pairs are those not present in the set of distinct state pairs *)
		let equiv = Set.filter ( fun (a,b) -> not (Set.belongs (a,b) dist) &&
												not (Set.belongs (b,a) dist) ) halfTriang in

		let equivList = Set.toList equiv in

		let eq = Set.map (fun (a,b) -> b) equiv in
		let newSts = Set.diff fa.states eq in
		let newInitSt = translate fa.initialState equivList in
		let newAccSts = Set.inter fa.acceptStates newSts in
		let newTrans = Set.map (fun (x,y,z) -> (translate x equivList,y,translate z equivList) ) fa.transitions in
			{
				alphabet = fa.alphabet;
				states = newSts;
				initialState = newInitSt;
				transitions = newTrans;
				acceptStates = newAccSts
			}

	(**
	* This function verifies if the automaton is minimal
	* @returns boolean -> true if automaton is minimal, false otherwise
	* Desc: The given automaton is considered minimal if the result of minimizing it is an automaton with the same
	* number of states
	*)
	let isMinimized (fa: t): bool =
		let min = minimize fa in
			Set.size fa.states = Set.size min.states
end

module FiniteAutomaton =
struct
	include FiniteAutomatonSupport
	open FiniteAutomatonAccept
	open FiniteAutomatonGenerate
	open FiniteAutomatonPrivate

	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
	let make (arg: t Arg.alternatives): t = make arg validate

	(* Exercices support *)
	let checkProperty (fa: t) (prop: string) =
		match prop with
			| "deterministic" -> isDeterministic fa
			| "minimized" -> isMinimized fa
			| "finite automaton" -> true
			| _ -> Model.checkProperty prop
	let checkExercise ex fa = Model.checkExercise ex (accept fa) (checkProperty fa)	
	let checkExerciseFailures ex fa = Model.checkExerciseFailures ex (accept fa) (checkProperty fa)

	(* Ops *)
	let stats = Model.stats
	let accept = accept
	let acceptFull = FiniteAutomatonAccept.acceptFull
	let generate = generate	
	let toDeterministic = toDeterministic	

	(* Class *)
	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model (make2 arg) as super	
		(* Representation *)
			method representation = representation
		(* Kind *)
			method isFiniteAutomaton : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Ops *)
			method acceptBreadthFirst (w: word): bool = acceptBreadthFirst representation w
			method accept (w: word): bool = accept representation w
			method acceptFull (w: word) : bool * path * trail = acceptFull representation w

			method acceptWithTracing (w:word): unit = acceptWithTracing representation w
			method generate (length: int): words = generate representation length
			method generateUntil (length: int): words = generateUntil representation length

			method reachable (s:state): states = reachable representation s
			method productive: states = productive representation
			method getUsefulStates: states = getUsefulStates representation
			method getUselessStates: states = getUselessStates representation
			method cleanUselessStates: model =
				let fa = cleanUselessStates representation in
					new model (Arg.Representation fa)
			method areAllStatesUseful: bool = areAllStatesUseful representation

			method toDeterministic: model =
				let fa = toDeterministic representation in
					new model (Arg.Representation fa)
			method isDeterministic: bool = isDeterministic representation

			method equivalencePartition: states set = equivalencePartition representation
			method minimize: model =
				let fa = minimize representation in
					new model (Arg.Representation fa)
			method isMinimized: bool = isMinimized representation
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

module FiniteAutomatonTop =
struct
	open FiniteAutomaton
	open FiniteAutomatonX

	let faI fa = internalize fa
	let faX fa = externalize fa

	let fa_load file = faX (make (Arg.File file))
	let fa_text text = faX (make (Arg.Text text))
	let fa_json json = faX (make (Arg.JSon json))
	let fa_predef name = fa_text (Examples.example name)


	let confX (s, w) = (state2str s, word2str w)
	let pathX (p: path) = pathX confX p
	let trailX (t: trail) = trailX confX t
	
	let stats () = RuntimeControl.stats ()

	let fa_accept fa w = accept (faI fa) (wordI w)

	let fa_path fa w =
		let (r,p,t) = acceptFull (faI fa) (wordI w) in
			pathX p

	let fa_trail fa w =
		let (r,p,t) = acceptFull (faI fa) (wordI w) in
			trailX t

	let fa_generate fa len = wordsX (generate (faI fa) len)

end

open FiniteAutomatonTop


(*

--------------------
let fa = fa_predef "dfa_astar";;

fa_generate fa 8;;

fa_accept fa "aaaa";;
fa_accept fa "aaaca";;

fa_path fa "aaaa";;
fa_path fa "aaaca";;

fa_trail fa "aaaa";;
--------------------

#print_depth 10000;;
#print_length 10000;;



let fa_astar = {| {
		kind : "finite automaton2",
		description : "this is an example",
		name : "dfa_astar",
		alphabet: ["a"],
		states : ["START", "Z1"],
		initialState : "START",
		transitions : [
			["START", "a", "START"],
			["START", "~", "START"],			
			["START", "~", "Z"],			
			["Z", "a", "Z"],
			["START", "a", "Z"]
		],
		acceptStates : ["START", "Z"]
		} |}
;;
let fa = fa_text fa_astar;;


fa_accept fa "aaa";;
fa_accept fa "aab";;

fa_path fa "aaa";;
fa_trail fa "aaa";;


let rec str n =
	if n = 0 then ""
	else "a" ^ str (n-1)
;;

let res (r,p,t) = r;;



let n = 10;;
let big = str 20;;
let bign = (str 10) ^ "b" ^ (str 10);;
let big3 = str (2*n);;
let bign3 = (str n) ^ "b" ^ (str n);;


let z = 1500 ;;
let r = fa_accept fa ((str z));;
stats ();;
let r = res (fa_acceptFull fa (str z));;
stats ();;





let a = fa_accept fa bign;;
stats ();;
let t = fa_acceptTrail fa  bign;;
stats ();;
let p = fa_acceptPath fa  bign;;
stats ();;
let (r,p,t) = fa_acceptFull fa  bign;;
stats ();;

*)

