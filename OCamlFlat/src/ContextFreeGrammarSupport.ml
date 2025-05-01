(*
 * ContextFreeGrammarSupport.ml
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
 * sep/2022 (amd) - New submodules CFGConversions and CFGLearnOCaml
 * jul/2021 (amd) - Now this module is client of the Scanner module and
 *                  the erros are registered using the Error module.
 * jan/2021 (amd) - Module moved to an independent file.
 * dec/2019 (amd) - Initial version, inside the big file "OCamlFlatSupport.ml".
 *)

(*
 * Description: Support types and functions for CFGs including a parser for CFGs.
 *)
 
open BasicTypes

module ContextFreeGrammarBasics =
struct
	type rule = { head : symbol; body : word }
	type rules = rule set

	type t = {
		alphabet : symbols;
		variables : variables;
		initial : variable;
		rules : rules
	}
	
	type configuration =
		symbol list * word
	type configurations =
		configuration set

	type path =
		configuration Path.path
	type trail =
		configuration Trail.trail

	type cfgTree =
		  Leaf of symbol
		| Root of symbol * cfgTree list

	let kind = "context free grammar"

	let cfg_zero: t = {
		alphabet = Set.empty;
		variables = Set.make [draftVar];
		initial = draftVar;
		rules = Set.empty;
	}
end

module type ContextFreeGrammarSyntaxSig =
sig
	open ContextFreeGrammarBasics

	val parse : string set -> rules
	val parseLine : string -> rules
	val toStringList : rules -> string list
	val (-->) : symbol -> string -> rule
	val rule2str : rule -> string
	val showRules : rules -> unit
end

module ContextFreeGrammarSyntax: ContextFreeGrammarSyntaxSig =
struct
	open Scanner
	open ContextFreeGrammarBasics

	let isWhite c =
		List.mem c [' '; '\t']

	let parseString delim =
		skip();	(* skip quotation mark *)
		let tk = getUntil delim in
			match peek () with
				| x when x = delim -> skip(); ("<" ^ tk ^ ">")
				| err -> expecting ("closing '" ^ (Char.escaped delim) ^ "'") err
	
	let parseHead () : symbol =
		match peek() with
			| ' ' -> invalid "Premature end of expression\n"
			| '<' -> str2symb (parseString '>')
			| c -> skip() ; char2symb c
			
	let parseNeck (): unit =
		match peek() with
			| ' ' -> invalid "Premature end of expression\n"
			| '-' -> skip();
					if peek() = '>' then skip()
					else invalid "Bad neck\n"
			| _ -> invalid "Bad neck\n"

	let rec parseBody (): word list =
		match peek() with
			| ' ' -> [[]]
			| '|' -> skip(); []::parseBody ()
			| '~' -> skip(); parseBody ()
			| '<' ->
				(let symb = str2symb (parseString '>') in
					match parseBody () with
						| [] -> invalid "never happens"
						| x::xs -> (symb::x)::xs)		
			| c -> skip();
					match parseBody () with
						| [] -> invalid "never happens"
						| x::xs -> ((char2symb c)::x)::xs

	let parseLine line: rules =
		if String.trim line = "" then
			Set.empty
		else (
			Scanner.start "ContextFreeGrammarSyntax" line;
			try
				let finish l = if l = [] then [epsilon] else l in
				let h = parseHead () in
				let _ = parseNeck () in
				let bs = Set.make (parseBody ()) in
					Set.map (fun b -> {head=h; body=finish b}) bs
			with Not_found ->
				Set.empty
		)

	let parse rs: rules =
		Set.flatMap parseLine rs
	
	let rule2str {head=h; body=b} =
		let b = if b = [] then [epsilon] else b in
			(symb2str h) ^ " -> " ^ (word2str b)

	let toString rs: string =
		let rl = Set.toList rs in
		String.concat "\n" (List.map rule2str rl)

	let toStringList rs: string list =
		let rl = Set.toList rs in
			List.map rule2str rl
	
	let (-->) h b : rule =
		{ head = h; body = str2word b } ;;

	let showRules rs =
		Util.println [toString rs]
end

module ContextFreeGrammarConversions =
struct
	open ContextFreeGrammarBasics
	open ContextFreeGrammarSyntax

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			cfg_zero
		else {
			alphabet = JSon.fieldSymbolSet j "alphabet";
			variables = JSon.fieldSymbolSet j "variables";
			initial = JSon.fieldSymbol j "initial";
			rules = ContextFreeGrammarSyntax.parse (JSon.fieldStringSet j "rules");
		}

	let toJSon0 (rep: t): JSon.t =
		JSon.makeAssoc [
			("alphabet", JSon.makeSymbolSet rep.alphabet);
			("variables", JSon.makeSymbolSet rep.variables);
			("initial", JSon.makeSymbol rep.initial);
			("rules", JSon.makeStringSet (Set.map rule2str rep.rules))
		]
	
	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 rep)

	let toJSon (rep: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) rep
end

module ContextFreeGrammarBasicFunctions =
struct
	open ContextFreeGrammarBasics
	open ContextFreeGrammarConversions

	let make2 (arg: t Arg.alternatives) validate: Entity.t * t =
		Entity.make2 arg fromJSon kind validate

	let make (arg: t Arg.alternatives) validate: t =
		snd (make2 arg validate)

	let show (rep: t): unit =
		let j = toJSon rep in
			JSon.show j

	let show2 (id: Entity.t) (rep: t): unit =
		let j = toJSon2 id rep in
			JSon.show j
end

module ContextFreeGrammarBasicsX =
struct
	open ContextFreeGrammarBasics

	type tx = {
		alphabet : symbolX list;
		variables : variableX list;
		initial : variableX;
		rules : string list
	}

	let internalize (cfg: tx): t = {
		alphabet = symbolsI cfg.alphabet;
		variables = symbolsI cfg.variables;
		initial = symbI cfg.initial;
		rules = ContextFreeGrammarSyntax.parse (Set.make cfg.rules)
	}

	let externalize (cfg: t): tx = {
		alphabet = symbolsX cfg.alphabet;
		variables = symbolsX cfg.variables;
		initial = symbX cfg.initial;
		rules = ContextFreeGrammarSyntax.toStringList cfg.rules
	}
end

module ContextFreeGrammarLearnOCaml =
struct
	open ContextFreeGrammarBasics
	open ContextFreeGrammarBasicsX

	let moduleName =
		"ContextFreeGrammar"

	let xTypeName =
		"contextFreeGrammar"

	let solution (name: string) (rep: t): string =
		let repx = externalize rep in
		Printf.sprintf {zzz|
		%s{
			alphabet = %s;
			variables = %s;
			initial = %s;
			rules = %s
		}
		|zzz}	(* please, do not change this line *)
			(FiniteEnumerationLearnOCaml.displayHeader name xTypeName)
			(symbolsXD repx.alphabet)
			(symbolsXD repx.variables)
			(symbXD repx.initial)
			(stringsD repx.rules)

	let prelude : string =
		Printf.sprintf {zzz|
			type symbol = %s
			type variable = %s
			type rule = string
			type contextFreeGrammar = {
				alphabet : symbol list;
				variables : variable list;
				initial : variable;
				rules : rule list
			}
		|zzz}	(* please, do not change this line *)
				symbolTypeName symbolTypeName

		let example : JSon.t =
			JSon.parse {| {
				kind : "context free grammar",
				description : "this is an example",
				name : "cfg_simple",
				alphabet : ["0", "1"],
				variables : ["S", "X"],
				initial : "S",
				rules : [ "S -> 1S0 | X", "X -> 0X1 | ~" ]
			}
			|}	(* please, do not change this line *)
end

module ContextFreeGrammarSupport =
struct
	include ContextFreeGrammarBasics
	include ContextFreeGrammarSyntax
	include ContextFreeGrammarConversions
	include ContextFreeGrammarBasicFunctions
	include ContextFreeGrammarLearnOCaml
end

module ContextFreeGrammarSyntaxTests : sig end =
struct
	let active = false

	let test0 () =
		let cfg = Set.make [ "S -> aTb | ~"; "T -> aSb" ] in
		let rules = ContextFreeGrammarSyntax.parse cfg in
			ContextFreeGrammarSyntax.showRules rules

	let test1 () =
		let cfg = Set.make ["S -> aSb | ~"] in
		let rules = ContextFreeGrammarSyntax.parse cfg in
			ContextFreeGrammarSyntax.showRules rules

	let runAll =
		if Util.testing active "ContextFreeGrammarSyntax" then begin
			Util.header "test0";
			test0 ();
			Util.header "test1";
			test1 ();
			Util.header ""
		end
end
