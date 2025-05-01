(*
 * Composition.ml
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
 *  Written by Carolina Duarte (cd)
 *)

(*
 * ChangeLog:
 *
 *)

(*
 * Description: Model composition testing.
 *
 *)
 
open BasicTypes

module CompositionTests : sig end =
struct
	open Composition

	let active = false

	let comp_abc = {| {
			kind : "composition",
			description : "this is an example",
			name : "comp_abc",
			comp : "[dfa_astar]^[dfa_astar]"
	} |}
	
	let test0 () =
		let comp = new Composition.model (Arg.Text comp_abc) in
			comp#show2

	let checkWord comp s =
		if comp#accept (str2word s) then "ACCEPT" else "REJECT"

	let checkWords comp l =
		List.iter (fun s -> Printf.printf "\"%s\" %s\n" s (checkWord comp s)) l

	let test1 () =
		let comp = new Composition.model (Arg.Text comp_abc) in
			checkWords comp ["aa"; "bb"]

	let runAll =
		if Util.testing active "Composition" then begin
			Util.sep (); test0();
			Util.sep (); test1();
			
		end
end



