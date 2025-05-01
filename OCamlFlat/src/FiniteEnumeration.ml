(*
 * FiniteEnumeration.ml
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
 * may/2021 (amd) - Added support for an extern representation.
 * mar/2021 (amd) - New module
 *)

(*
 * Description: Finite language, directly defined as a set of words.
 *)

open BasicTypes

module FiniteEnumerationPrivate =
struct
	open FiniteEnumerationSupport
	
	let validate (name: string) (rep: t): unit =
		()

	let accept (fe: t) (w: word): bool =
		Set.belongs w fe

	let generate (fe: t) (length: int): words =
		Set.filter (fun w -> List.length w == length) fe
end

module FiniteEnumeration =
struct
	include FiniteEnumerationSupport
	open FiniteEnumerationPrivate

	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t =
		make2 arg validate

	let make (arg: t Arg.alternatives): t =
		make arg validate

	(* Exercices support *)
	let checkProperty (fe: t) (prop: string) =
		match prop with
			| "finite enumeration" -> true
			| _ -> Model.checkProperty prop

	let checkExercise ex fe =
		Model.checkExercise ex (accept fe) (checkProperty fe)	

	let checkExerciseFailures ex fe =
		Model.checkExerciseFailures ex (accept fe) (checkProperty fe)	

	(* Ops *)
	let accept = accept
	let generate = generate	

	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model (make2 arg) as super
		(* Representation *)
			method representation: t = representation
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Ops *)				
			method accept (w: word): bool = accept representation w
			method generate (length: int): words = generate representation length
		(* Exercices support *)
			method checkProperty (prop: string) = checkProperty representation prop
		(* Learn-OCaml support *)
			method moduleName = moduleName
			method xTypeName = xTypeName
			method xTypeDeclString : string = prelude
			method toDisplayString (name: string): string = solution name self#representation
			method example : JSon.t = example
		end
end
