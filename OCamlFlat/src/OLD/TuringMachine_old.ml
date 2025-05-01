#ifdef ALL

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

module TuringMachine =
struct
	include TuringMachineSupport

	(* Make *)
	let validate (name: string) (rep: t): unit =
		Error.error name "The alphabet contains epsilon '~', and it should not" ()

	let make2 (arg: (t,tx) Arg.alternatives): Entity.t * t =
		let id = Entity.createId arg kind in
		let rep = Entity.create arg fromJSon internalize in
			Entity.endCreation id rep kind validate;
			(id, rep)

	let make (arg: (t,tx) Arg.alternatives): t =
		snd (make2 arg)

	class model (arg: (t,tx) Arg.alternatives) =
		object(self) inherit Model.model arg kind as super
			val representation = Entity.create arg fromJSon
			(* placement of the initializer is crucial - after representation *)
			initializer Entity.endCreation self#id self#representation kind validate

		(* Representation *)
			method representation = representation
			method representationx = externalize representation
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 self#id representation
			method show: unit = show representation
			method show2: unit = show2 self#id representation
		(* Ops *)
			method accept(w: word): bool =
				false

			method generate (length: int): words =
				Set.empty	
		
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

#endif
