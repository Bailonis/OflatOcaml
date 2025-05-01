(*
 * Tests.ml
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
 * jan/2021 (amd) - Initial version.
 *)

(*
 * Description: Set of unit tests for checking the library from time to time.
 *
 * TODO: This is only a starting point. There are already many (disabled) unit
 * tests in several modules and this stuff needs to be reviewed.
 *)

module Tests : sig end =
struct
	open Examples

	let active = false

(*
	open TopLevel



	let test1 () =
		let a = fa_predef "dfa_1" in
			Util.println [if fa_accept a "ab" then "OK" else "ERROR"] *)

	let runAll =
		if Util.testing active "Tests" then begin

		end
end
