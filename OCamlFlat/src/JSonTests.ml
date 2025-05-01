(*
 * JSonTests.ml
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
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: JSon parser tests.
 *)

open BasicTypes

module JSonTests : sig end =
struct
	let active = false

	let jsonSample = {| {
		name: {
			first: "aa",
			last: "22",
			fullname: "33"
		},
		age: "33",
		hobbies: [ "44", "55" ]
	} |}
	
	let jsonSample2 = {| "aa" |}
	
	let test0 () =
		let json = JSon.parse jsonSample in
		let json2 = JSon.parse jsonSample2 in
			JSon.show json; JSon.show json2
	
	let oonSample = {| {
		alphabet = ['a';'b'];
		states = ["START"; "33"];
		initialState = "START";
		transitions = [("START", 'a', "START"); ("START", 'a', "START")];
		acceptStates = ["START"]
	} |}
	
	let oonSample2 = {| "z*" |}

	let oonSample3 = {| ("START", ["ee"], "yu") |}

	let test1 () =
		let oon = JSon.parseOon oonSample in
		let oon2 = JSon.parseOon oonSample2 in
		let oon3 = JSon.parseOon oonSample3 in
			JSon.show oon; JSon.show oon2; JSon.show oon3

	let test () =
		let oon2 = JSon.parseOon oonSample2 in
			JSon.show oon2

	let runAll =
		if Util.testing active "JSon" then begin
			test ()
		end

end
