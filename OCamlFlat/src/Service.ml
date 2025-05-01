(*
 * Service.ml
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
 * may/2022 (amd) - Initial version.
 *)

let warnings = "-w +a-26-27"
let warnings = "-w +a-4-7-27-32-33-36-40-41-42-44-45-70"

let makeItem a n small =
	if small then
		print_string ("ocamlc -c " ^ warnings ^ " -pp cppo")
	else
		print_string ("ocamlc -c " ^ warnings ^ " -pp \"cppo -D ALL\"");
	for i = 2 to n-1 do
		Printf.printf " -open %s" a.(i)
	done;
	Printf.printf " %s.ml" a.(n)

let makeItems a n small =
(*	print_string "cd src && "; *)
	for i = 2 to n do
		makeItem a i small;
		if i <> n then print_string " && ";
	done

let service () =
	let a = Sys.argv in
	let n = Array.length a in
	let command = if n > 1 then a.(1) else "" in
		match command with
		| "make" -> if n > 2 then makeItems a (n-1) false
		| "make_small" -> if n > 2 then makeItems a (n-1) true
		| _ -> ()
;;

service ()
