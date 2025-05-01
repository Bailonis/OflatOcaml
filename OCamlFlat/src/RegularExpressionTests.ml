(*
 * RegularExpressionTests.ml
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
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: Regular expressions testing.
 *)

open BasicTypes

module RegularExpressionTests: sig end =
struct
	let active = false

	let test0 () =
		let m = new RegularExpression.model (Arg.Predef "re_abc") in
			let j = m#toJSon in
				JSon.show j

	let test1 () =
		let re = new RegularExpression.model (Arg.Predef "re_abc") in
			let j = re#toJSon in
				JSon.show j

	let testAlphabet () =
		let re = new RegularExpression.model (Arg.Predef "re_abc") in
			Util.println ["alphabet: "]; Util.printAlphabet re#alphabet;
			Util.println []

	let testAlphabet2 () =
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
			Util.println ["alphabet: "]; Util.printAlphabet re#alphabet;
			Util.println []

	let testAlphabet3 () =
		let re = new RegularExpression.model (Arg.Predef "re_complex") in
			Util.println ["alphabet: "]; Util.printAlphabet re#alphabet;
			Util.println []

	let testAlphabet4 () =
		let re = new RegularExpression.model (Arg.Predef "re_convoluted") in
			Util.println ["alphabet: "]; Util.printAlphabet re#alphabet;
			Util.println []

	let testQuasiLang () =
		let re = new RegularExpression.model (Arg.Predef "re_abc") in
			let ws = re#quasiLanguage in
			Util.printWords ws

	let testQuasiLang2 () =
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
			let ws = re#quasiLanguage in
			Util.printWords ws

	let testQuasiLang3 () =
		let re = new RegularExpression.model (Arg.Predef "re_complex") in
			let ws = re#quasiLanguage in
			Util.printWords ws

	let testQuasiLang4 () =
		let re = new RegularExpression.model (Arg.Predef "re_convoluted") in
			let ws = re#quasiLanguage in
			Util.printWords ws

	let check f w =
		let msg = 
			if f w then "word was accepted" else "word was not accepted"
		in Util.println [msg]

	let testAccept () =
		let m = new RegularExpression.model (Arg.Predef "re_abc") in
			check m#accept (word "aa")

	let testAccept2 () =
		let m = new RegularExpression.model (Arg.Predef "re_simple") in
			check m#accept (word "aa")

	let testAccept3 () =
		let m = new RegularExpression.model (Arg.Predef "re_complex") in
			check m#accept (word "aa")

	let testAccept4 () =
		let m = new RegularExpression.model (Arg.Predef "re_convoluted") in
			check m#accept (word "aa")

	let testGenerate () =
		let re = new RegularExpression.model (Arg.Predef "re_abc") in
			Util.println ["generated words size 0:"]; Util.printWords (re#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (re#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (re#generate 2);
			Util.println ["generated words size 3:"]; Util.printWords (re#generate 3);
			Util.println ["generated words size 4:"]; Util.printWords (re#generate 4);
			Util.println []

	let testGenerate2 () =
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
			Util.println ["generated words size 0:"]; Util.printWords (re#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (re#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (re#generate 2);
			Util.println ["generated words size 3:"]; Util.printWords (re#generate 3);
			Util.println ["generated words size 4:"]; Util.printWords (re#generate 4);
			Util.println []

	let testGenerate3 () =
		let re = new RegularExpression.model (Arg.Predef "re_complex") in
			Util.println ["generated words size 0:"]; Util.printWords (re#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (re#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (re#generate 2);
			Util.println ["generated words size 3:"]; Util.printWords (re#generate 3);
			Util.println ["generated words size 4:"]; Util.printWords (re#generate 4);
			Util.println []

	let testGenerate4 () =
		let re = new RegularExpression.model (Arg.Predef "re_convoluted") in
			Util.println ["generated words size 0:"]; Util.printWords (re#generate 0);
			Util.println ["generated words size 1:"]; Util.printWords (re#generate 1);
			Util.println ["generated words size 2:"]; Util.printWords (re#generate 2);
			Util.println ["generated words size 3:"]; Util.printWords (re#generate 3);
			Util.println ["generated words size 4:"]; Util.printWords (re#generate 4);
			Util.println []

	let testSimplify2 () =
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
		let res = re#simplify in
			JSon.show res#toJSon

	let testEnum () =
		let e = new Exercise.exercise (Arg.Predef "exer_re2fa") in
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
		let result = re#checkExercise e in
			if result then Util.print ["it works"] else Util.print ["it does not work"]

	let testTrace () =
		let re = new RegularExpression.model (Arg.Predef "re_simple") in
			re#allTrees (word "acbacb")
	
	let re_more = {| {
			kind : "regular expression",
			description : "this is an example",
			name : "re_more",
			re : "a*"
	} |}
				
	let testMore () =
		let re = new RegularExpression.model (Arg.Text re_more) in
			re#allTrees (word "aa")

	let runAll =
		if Util.testing active "RegularExpression" then begin
			testMore ()
		end
end
