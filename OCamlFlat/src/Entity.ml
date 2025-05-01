(*
 * Entity.ml
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
 * set/2022 (amd) - Full restructuration.
 * jul/2021 (amd) - Improved error handling.
 * may/2021 (amd) - Added support for an extern representation.
 * may/2021 (amd) - Centralized the handling of kind/description/name.
 * feb/2021 (amd) - Added the alternative Predef.
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlat.ml".
 *)

(*
 * Description: An entity is a named instance of a concept. As now, the entities
 * are the exercises and the FLAT models. The type "alternatives" is to allow
 * the constructor to be used with several kind of parameter forms.
 *)

module Arg =
struct	
	type 'r alternatives =
		| JSon of JSon.t
		| Text of string
		| File of string
		| Predef of string
		| Representation of 'r

	let fromAlternatives alt =
		match alt with
		| JSon j -> j
		| Text str -> JSon.parse str
		| File str -> JSon.fromFile str 
		| Predef str -> JSon.parse (Examples.example str)
		| _ -> JSon.JNull
end

module EntityBasics =
struct
	type t = {
		kind : string;
		description : string;
		name : string
	}
	type tx =
		t 
end

module EntityConversions =
struct
	open EntityBasics

	let dummyId (k: string): t = {
		kind = k;
		description = "_";
		name = "_"
	}

	let fromJSon (j: JSon.t) (kind: string): t =
		if JSon.isNull j then (
			dummyId kind )
		else (
		 {
			kind = JSon.fieldString j "kind";
			description = JSon.fieldString j "description";
			name = JSon.fieldString j "name"
		})
		
	let toJSon (rep: t): JSon.t =
		JSon.makeAssoc [
			("kind", JSon.makeString rep.kind);
			("description", JSon.makeString rep.description);
			("name", JSon.makeString rep.name)
		]
end

module EntitySupport =
struct
	include EntityBasics
	include EntityConversions
end

module EntityPrivate =
struct
	include EntitySupport

	let startCreation () =
		Error.startGroup ()
	
	let createId (arg: 'r Arg.alternatives) (kind: string): t =
		startCreation ();
		match arg with
		| Arg.Representation r -> dummyId kind
		| _ -> fromJSon (Arg.fromAlternatives arg) kind

	let create (arg: 'r Arg.alternatives) fromJSon: 'r =
		match arg with
			| Arg.Representation r -> r
			| _ -> fromJSon (Arg.fromAlternatives arg)

	let endCreation (id: t) rep kind validate: unit =
		if id.kind <> kind then
			Error.error id.kind "Wrong kind" ();
		validate id.name rep;
		ignore (Error.endGroup kind id.name)
end

module Entity =
struct
	open EntityPrivate
	include EntitySupport

	let make2 (arg: 'r Arg.alternatives) (fromJSon: JSon.t -> 'r)
			(kind: string) (validate: string -> 'r -> unit): t * 'r =
		let id = createId arg kind in
		let m = create arg fromJSon in
			endCreation id m kind validate;
			(id, m)

	class virtual entity (data: t * 'r) =
		object(self)
			val id: t = fst data
			val representation: 'r = snd data
			val errors = Error.get ()
		(* Representation *)
			method id: t = id
			method errors: string list = errors
		(* Kind *)
			method isFiniteAutomaton : bool = false
			method isRegularExpression : bool = false
			method isGrammar : bool = false
			method isContextFreeGrammar : bool = false
			method isPushdownAutomaton : bool = false
			method isTuringMachine : bool = false
			method isExercise : bool = false
			method isComposition : bool = false
		(* Show *)			
			method virtual toJSon: JSon.t
			method virtual toJSon2: JSon.t
			method virtual show : unit
			method virtual show2 : unit
	end
end

module EntityTests : sig end =
struct
	let active = false

	let test0 () =
		()

	let runAll =
		if Util.testing active "Entity" then begin
			test0 ()
		end
end
