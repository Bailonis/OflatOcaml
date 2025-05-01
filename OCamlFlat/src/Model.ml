(*
 * Model.ml
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
 *  Written by Artur Miguel Dias (amd)
 *)

(*
 * ChangeLog:
 *
 * jun/2023 (amd) - Added generic 'accept' and 'generate' methods.
 * set/2022 (amd) - Full restructuration.
 * jul/2021 (amd) - Improved Learn-OCaml support.
 * mar/2021 (amd) - Added support for semantic constrains (properties) in
 *                  the exercises, in this class and in all its subclasses.
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlat.ml".
 *)

(*
 * Description: Abstract FLAT model.
 *
 * TODO: Probably add a new method "canonical" to generate a
 * normalized/simplified version of the FLAT model.
 *)

open BasicTypes

module ModelBasics =
struct
end

module ModelExercises =
struct
	let checkProperty (prop: string) =
		match prop with
			| "fail" | "false" -> false
			| "true" -> true
			| _ ->
				let mesg = "checkProperty: unknown property ("
								^ prop ^ ")" in
					Error.fatal mesg

	let checkExercise (ex: Exercise.t) accept checkProperty =
		   Set.for_all accept ex.inside
		&& Set.for_all (fun w -> not (accept w)) ex.outside
		&& Set.for_all checkProperty ex.properties

	let checkExerciseFailures (ex: Exercise.t) ac cp = (
		Set.filter (fun w -> not (ac w)) ex.inside,
		Set.filter ac ex.outside,
		Set.filter (fun w -> not (cp w)) ex.properties
	)
end

module ModelSupport =
struct
	include ModelBasics
	include ModelExercises
end

module ModelPrivate =
struct
	let stats () =
		RuntimeControl.stats ()

	let checkWord (alphabet: symbols) (w: word): bool =
		let ok = Set.subset (Set.make w) alphabet in
		let str = word2str w in
		let mesg = "Word \"" ^ str ^ "\" contains symbols not belonging to the alphabet" in
			if not ok then Error.warning mesg;
			ok

	(* The result is true is the word is accepted. *)
	let accept (m: 'm) (w: word)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): bool =
		let rec acceptX (configs: 'c set) (seen: 'c set): bool =
			let newConfigs = Set.diff configs seen in
			let newSeen = Set.unionUnsafe newConfigs seen in
			let _ = RuntimeControl.update (Set.size newConfigs) in
			if Set.isEmpty newConfigs then
				false
			else if Set.exists (isAccepting m) newConfigs then
				true
			else if RuntimeControl.giveUp () then
				false
			else
				let nextConfigs = Set.flatMap (next m) newConfigs in
					acceptX nextConfigs newSeen
		in	
		let _ = RuntimeControl.start () in
		let initialConfigs = initial m w in
			acceptX initialConfigs Set.empty

	(* The result is a triple: acceptance, one path, trail with all the alternatives.  *)
	let acceptFull (m: 'm) (w: word)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): bool * 'c path * 'c trail =
		let base (r: bool) (configs: 'c set): bool * 'c path * 'c trail =
			let accepting = Set.filter (isAccepting m) configs in
			let c = Set.hd (if Set.isEmpty accepting then configs else accepting) in
				(r, [c], [configs])
		in
		let rec acceptX (configs: 'c set) (seen: 'c set) : bool * 'c path * 'c trail =
			let newConfigs = Set.diff configs seen in
			let newSeen = Set.unionUnsafe newConfigs seen in
			let _ = RuntimeControl.update (Set.size newConfigs) in
			if Set.isEmpty newConfigs then
				(false, [], [])
			else if Set.exists (isAccepting m) newConfigs then
				base true newConfigs
			else if RuntimeControl.giveUp () then
				base false newConfigs
			else
				let nextConfigs = Set.flatMap (next m) newConfigs in
				let (r,p,t) = acceptX nextConfigs newSeen in
					match p with
					| [] ->
						base r newConfigs
					| x::_ ->
						let c = Set.find (fun c -> Set.belongs x (next m c)) newConfigs in
							(r, c::p, newConfigs::t)
		in
		let _ = RuntimeControl.start () in
		let initialConfigs = initial m w in
			acceptX initialConfigs Set.empty
	
	(* invariant - for_all c in seen: c <= len *)
	let generate (m: 'm) (len: int)
				(initial: 'm -> word -> 'c set)
				(next2: 'm -> int -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool)
				(getWord: 'c -> word): words =

		let strict = len < 0 in
		let len = abs len in
		let lenWord c = List.length (getWord c) in
		let isNew seen c = lenWord c <= len && not (Set.belongs c seen) in
		let isExpanding c = lenWord c < len || not (isAccepting m c) in
		let finalSelection =
			if strict then (fun c -> isAccepting m c && lenWord c = len) 
					else (fun c -> isAccepting m c) 
		in
		let rec generateX (configs: 'c set) (seen: 'c set): 'c set =
			let newConfigs = Set.filter (isNew seen) configs in
			let newSeen = Set.union newConfigs seen in
			let _ = RuntimeControl.update (Set.size newConfigs) in (* ???, e também stack overflow, reutime controlo tem de ter varias instancias *) (* comparar o accept e o generate do joao *)
			let toExpand = Set.filter isExpanding newConfigs in
				if Set.isEmpty toExpand || RuntimeControl.giveUp () then
					newSeen
				else
					let nextConfigs = Set.flatMap (next2 m len) toExpand in
						if RuntimeControl.giveUp () then
							newSeen
						else
							generateX nextConfigs newSeen
		in
		let _ = RuntimeControl.start () in
		let initialConfigs = initial m (word "") in
		let collected = generateX initialConfigs Set.empty in
		let selected = Set.filter finalSelection collected in
			Set.map getWord selected

	(* generate and test. Will be improved.
	   Used for TMs because the "rest of the word" is not part of the configuration *)
	let generateDumb (m: 'm) (alphabet : symbols) (len: int)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): words =
				
		let addAll symb = List.map (fun l -> symb::l) in
		let rec combinations n l =
			if n = 0 then [[]]
			else let p = combinations (n-1) l in
					List.flatten (List.map  (fun x -> addAll x p) l)
		in
		let rec combinations2 n l =
			if n = 0 then [[]] else combinations2 (n-1) l @ combinations n l in
		let strict = len < 0 in
		let len: int = abs len in
		let s: word = Set.toList alphabet in
		let comb: word list = if strict then combinations len s else combinations2 len s in
		let accept w: bool = accept m w initial next isAccepting in
		let selected: word list = List.filter accept comb in
			Set.make selected

end

module Model =
struct
	include ModelSupport

	let stats = ModelPrivate.stats
	let checkWord = ModelPrivate.checkWord
	let accept = ModelPrivate.accept
	let acceptFull = ModelPrivate.acceptFull
	let generate = ModelPrivate.generate	
	let generateDumb =  ModelPrivate.generateDumb

	class virtual model (data: Entity.t * 'r) =
		object(self) inherit Entity.entity data

			method virtual accept: word -> bool
			(*method virtual acceptFull: 'c. word ->  bool * 'c path * 'c trail*)
			method virtual generate: int -> words
			(*method virtual generateDumb: int -> words*)
		
		(* Exercices support *)
			method checkProperty (prop: string) = checkProperty prop
			method checkExercise (exercise: Exercise.exercise) =
				checkExercise exercise#representation self#accept self#checkProperty
			method checkExerciseFailures (exercise: Exercise.exercise) =
				checkExerciseFailures exercise#representation self#accept self#checkProperty

		(* Learn-OCaml support *)
			method virtual moduleName: string
			method virtual xTypeName: string
			method virtual xTypeDeclString : string
			method virtual toDisplayString: string -> string
			method virtual example : JSon.t
	end

end

(*

(* this is only a test *)
class virtual cModel (arg: 'r Arg.alternatives) (expectedKind: string) =
	let open Model in
	object(self) inherit Entity.entity arg expectedKind

		method virtual accept: word -> bool
		method virtual acceptFull: 'c. word ->  bool * 'c path * 'c trail
		method virtual generate: int -> words
		method virtual generateDumb: int -> words
		
	(* Exercices support *)
		method checkProperty (prop: string) = checkProperty prop
		method checkExercise (exercise: Exercise.exercise) =
			checkExercise exercise#representation self#accept self#checkProperty
		method checkExerciseFailures (exercise: Exercise.exercise) =
			checkExerciseFailures exercise#representation self#accept self#checkProperty

	(* Learn-OCaml support *)
		method virtual moduleName: string
		method virtual xTypeName: string
		method virtual xTypeDeclString : string
		method virtual toDisplayString: string -> string
		method virtual example : JSon.t
end

*)

(*
SAVE- old versions that might be useful again

	(* trail alone *)
	let acceptTrail (m: 'm) (w: word)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): bool * 'c trail =

		let rec acceptX (configs: 'c set) (seen: 'c set) (trail: 'c trail): bool * 'c trail =
			let newConfigs = Set.diff configs seen in
			let newSeen = Set.unionUnsafe newConfigs seen in
			let newTrail = newConfigs::trail in
			if Set.isEmpty newConfigs then (false, trail)
			else if Set.exists (isAccepting m) newConfigs then (true, newTrail)
			else if RuntimeControl.giveUp (Set.size newSeen) then (false, newTrail)
			else
				let nextConfigs = Set.flatMap (next m) newConfigs in
					acceptX nextConfigs newSeen newTrail
		in
		let _ = RuntimeControl.start () in
		let initialConfigs = initial m w in
		let (b, trail) = acceptX initialConfigs Set.empty [] in
			(b, List.rev trail)

	(* path calculated from the trail *)
	let acceptPath (m: 'm) (w: word)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): 'c path =

		let rec acceptX (trail: 'c trail): 'c path =
			match trail with
			| [] -> Error.fatal "acceptX"
			| [c] ->
				let a = Set.filter (isAccepting m) c in
					[Set.hd (if Set.isEmpty a then c else a)]
			| c::cs ->
				(match acceptX cs with
				| [] ->  Error.fatal "acceptX"
				| p::ps ->
					let n = Set.find (fun c -> Set.belongs p (next m c)) c in
						n::p::ps)
		in
		let (_, trail) = acceptTrail m w initial next isAccepting in
			acceptX trail

			let acceptPaths (m: 'm) (w: word)
				(initial: 'm -> word -> 'c)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): 'c path set =


	(* all the paths alone *)
		let rec acceptX (paths: 'c path set) (seen: 'c set): 'c path set =
			let configs = Set.map List.hd paths in
			let newConfigs = Set.diff configs seen in				(* select the new *)
			let seen = Set.unionUnsafe newConfigs seen in			(* build new seen *)
			if Set.isEmpty newConfigs then							(* case repetition *)
				Set.map List.tl paths
			else if Set.exists (isAccepting m) newConfigs then		(* case accept *)
				Set.filter (fun p -> isAccepting m (List.hd p)) paths
			else
				let isNewPath p = Set.belongs (List.hd p) newConfigs in
				let nextPathsOne p = Set.map (fun c -> c::p) (next m (List.hd p))  in
				let newPaths = Set.filter isNewPath paths in
				let nextPaths = Set.flatMap nextPathsOne newPaths in
				if Set.size nextPaths = 0 then paths				(* case no-followup *)
				else	acceptX nextPaths seen
		in	
		let initialConfig = initial m w in
		let paths = acceptX (Set.make [[initialConfig]]) Set.empty in
			Set.map List.rev paths
	let acceptPath (m: 'm) (w: word)
				(initial: 'm -> word -> 'c)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): 'c path =
		let ps = acceptPaths m w initial next isAccepting in
		let min p1 p2 = if List.length p1 <= List.length p2 then p1 else p2 in
			Set.fold_left min (Set.hd ps) (Set.tl ps)

	(* trail and all the paths  *)
	let acceptFull (m: 'm) (w: word)
				(initial: 'm -> word -> 'c set)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): bool * 'c path * 'c trail =

		let rec acceptX (paths: 'c path set) (trail: 'c trail) (seen: 'c set)
													: bool * 'c path set * 'c trail =
			let configs = Set.map List.hd paths in
				if Set.exists (isAccepting m) configs then			(* case accept *)
					(true, paths, trail)
				else if RuntimeControl.giveUp (Set.size seen) then
					(false, paths, trail)
				else
					let nextConfigsOne p = next m (List.hd p) in
					let newConfigsOne p = Set.diff (nextConfigsOne p) seen in
					let newPathsOne p = Set.map (fun c -> c::p) (newConfigsOne p) in
					let newPaths = Set.flatMap newPathsOne paths in
					let newConfigs = Set.map List.hd newPaths in
					let newTrail = newConfigs::trail in
					let newSeen = Set.unionUnsafe newConfigs seen in
						if Set.isEmpty newConfigs then				(* case reject *)
							(false, paths, trail)
						else
							acceptX newPaths newTrail newSeen
		in
		let _ = RuntimeControl.start () in
		let initialConfigs = initial m w in
		let initialPaths = Set.map (fun c -> [c]) initialConfigs in
		let initialTrail = [initialConfigs] in
		let initialSeen = initialConfigs in
		let (r, ps, t) = acceptX initialPaths initialTrail initialSeen in
		let (r, ps, t) = (r, Set.map List.rev ps, List.rev t) in
		let fps = Set.filter (fun p -> isAccepting m (List.hd p)) ps in
			(r, Set.hd (if Set.isEmpty fps then ps else fps), t)

	(* full from trail and path  *)
	let acceptFull (m: 'm) (w: word)
				(initial: 'm -> word -> 'c)
				(next: 'm -> 'c -> 'c set)
				(isAccepting: 'm -> 'c -> bool): bool * 'c path * 'c trail =
		let p = acceptPath m w initial next isAccepting in
		let (r,t) = acceptTrail m w initial next isAccepting in
			(r, p, t)
*)
