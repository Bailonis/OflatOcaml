(*
 * Exercise.ml
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
 * jul/2021 (amd) - Improved error handling.
 * mar/2021 (amd) - Added semantic constrains (properties) to the exercises.
 * jan/2021 (amd) - Module in an independent file.
 * set/2019 (amd) - Initial version, inside the big file "OCamlFlat.ml"
 *)

(*
 * Description: Support to pedagogical exercises. The solutions are validated
 * using unit tests.
 *)

open BasicTypes

module Exercise =
struct
	include ExerciseSupport
		
	(* Make *)
	let validate (name: string) (rep: t): unit =
		()

	let make2 (arg: t Arg.alternatives): Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives): t =
		snd (make2 arg)

	class exercise (arg: t Arg.alternatives) =
		object(self) inherit Entity.entity (make2 arg) as super
		(* Representation *)
			method representation = representation
			method representationx = externalize representation
		(* Kind *)
			method isExercise : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Learn-OCaml support *)				
			method moduleName =
				"Exercice"
	end
end

module ExerciseTests : sig end =
struct
	let active = false

	let test0 () =
		let e = Exercise.make (Arg.Predef "exer_balanced_cfg") in
			Exercise.show e

	let test1 () =
		let (id, e) = Exercise.make2 (Arg.Predef "exer_balanced_cfg") in
			Exercise.show2 id e

	let test2 () =
		let e = new Exercise.exercise (Arg.Predef "exer_balanced_cfg") in
		let j = e#toJSon2 in
			JSon.show j

	let runAll =
		if Util.testing active "Exercice" then begin
			test0 ();
			test1 ();
			test2 ()
		end
end


