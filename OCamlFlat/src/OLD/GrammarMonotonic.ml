(*
 * GrammarMonotonic.ml
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
 *  Written by Pedro Carlos (p.carlos)
 *)

(*
 * ChangeLog:
 *
 * jul/2024 (amd) - New file.
 *)

(*
 * Description: Monotonic grammar functionality.
 *
 * TODO: More cleanup.
 *)

open BasicTypes

module GrammarMonotonicPrivate =
struct
	open GrammarSupport

	let isMonotonic (gram: t): bool =
		false (* TODO *)

	let isNonContracting (gram: t): bool =
		isMonotonic gram

	let isContextSensitive (gram: t): bool =
		false (* TODO *)

	let asContextSensitive (gram: t): t =
		gram (* TODO *)
end

module GrammarMonotonic =
struct
	include GrammarSupport
	open GrammarMonotonicPrivate

	(* Make *)
	let make2 = GrammarUnrestricted.make2
	let make = GrammarUnrestricted.make

	(* Ops *)
	let isMonotonic = isMonotonic
	let isNonContracting = isNonContracting
	let isContextSensitive = isContextSensitive
	let asContextSensitive = asContextSensitive
	let accept = GrammarUnrestricted.accept
	let generate = GrammarUnrestricted.generate	

	(* Exercices support *)
	let checkProperty (gram: t) (prop: string) =
		match prop with
		| "monotonic grammar" -> isMonotonic gram
		| "noncontracting grammar" -> isNonContracting gram
		| "context sensitive grammar" -> isContextSensitive gram
		| _ -> GrammarUnrestricted.checkProperty gram prop
	let checkExercise ex re = Model.checkExercise ex (accept re) (checkProperty re)	
	let checkExerciseFailures ex re = Model.checkExerciseFailures ex (accept re) (checkProperty re)
end
