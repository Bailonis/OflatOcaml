(*
 * AttributeGrammarSupport.ml
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
 * mar/2025 (amd) - New module
 *)

(*
 * Description: Support types and functions for FAs.
 *)

open BasicTypes

module AttributeGrammarBasics =
struct
	type attribute = symbol
	type attributes = attribute set
	type attrArg = variable * int
	type expression =
		| Int of int
		| String of string
		| Bool of bool
		| Apply of attribute * attrArg
		| Expr of string * expression * expression
	type equation = expression * expression
	type equations = equation set
	type condition = expression 
	type conditions = condition set

	(*
 * condition: tem que ser booleano
 * equation do lado esquerdo é um apply
 *)

	type rule = {
		head : symbol;
		body : word;
		equations : equations;
		conditions : conditions
	}
	type rules = rule set

	type t = {
		alphabet : symbols;
		variables : variables;
		synthesized : attributes;
		inherited : attributes;
		initial : variable;
		rules : rules
	}
	
	type parseTree =
		  Leaf of symbol
		| Root of symbol * parseTree list

	let kind = "attribute grammar"

	let ag_zero: t = {
		alphabet = Set.empty;
		variables = Set.make [draftVar];
		inherited = Set.empty;
		synthesized = Set.empty;
		initial = draftVar;
		rules = Set.empty;
	}
end

module ExpressionSyntax =
struct
	open CharType
	open Scanner
	open AttributeGrammarBasics

(* Literals: T, F, 1, 10, 100, "", "ola"
   Ops: [<, <=, <>, >, >=, =] [+] [*]
*)
	let parseApply (): expression =
		let attr = getAlpha () in
		let _ = getChar '(' in
		let v, i = getCharInt () in
		let _ = getChar ')' in
			Apply (char2symb attr, (char2symb v, i))
		
	let rec parseExp3 (): expression =
		match peek () with
		| c when isDigit c -> Int (getInt ())
		| '\'' -> String (getDelim '\'' '\'')
		| 'T' -> skip (); Bool true
		| 'F' -> skip (); Bool false
		| '(' -> let _ = getChar '(' in
				let e = parseExp0 () in
				let _ = getChar ')' in
					Expr ("(", e, Int 0)
		| _ -> parseApply ()

	and parseExp2 (): expression =
		let l = parseExp3 () in
		let c = peek () in
			if c = '*' then (
				skip();
				Expr ("*", l, parseExp2 ())
			)
			else
				l
		
	and parseExp1 (): expression =
		let l = parseExp2 () in
		let c = peek () in
			if c = '+' then (
				skip();
				Expr ("+", l, parseExp1 ())
			)
			else
				l
	
	and parseExp0 (): expression =
		let l = parseExp1 () in
			match peek () with
			| '<' ->
				skip();
				(match peek () with
				| '=' -> skip (); Expr ("<=", l, parseExp0 ())
				| '>' -> skip (); Expr ("<>", l, parseExp0 ())
				| _ -> Expr ("<", l, parseExp0 ()))
			| '=' ->
				skip(); Expr ("=", l, parseExp0 ())
			| '>' ->
				skip();
				(match peek () with
				| '=' -> skip (); Expr (">=", l, parseExp0 ())
				| _ -> Expr (">", l, parseExp0 ()))
			| _ ->
				l
		
	let parseExpression (): expression =
		parseExp0 ()
	
	let rec expression2str e =
		match e with
		| Int i ->
			string_of_int i
		| String s ->
			"\"" ^ s ^ "\""
		| Bool b ->
			if b then "T" else "F"
		| Apply (attr, (var, i)) when i = -1 ->
			symb2str attr ^ "(" ^ symb2str var ^ ")"
		| Apply (attr, (var, i)) ->
			symb2str attr ^ "(" ^ symb2str var ^ string_of_int i ^ ")"
		| Expr ("(", l, _) ->
			"(" ^ expression2str l ^ ")"
		| Expr (op, l, r) ->
			expression2str l ^ " " ^ op ^ " " ^ expression2str r
end

module EquationsSyntax =
struct
	open CharType
	open Scanner
	open AttributeGrammarBasics
	
	let parseEquation (): equation =
		let l = ExpressionSyntax.parseApply () in
			let _ = getChar '=' in
			let r = ExpressionSyntax.parseExpression () in
				(l, r)

	let rec parseEquationsX (): equations =
		match peek() with
			| '}' -> Set.empty
			| _ ->
				let e = parseEquation () in
					match peek () with
					| ';' -> skip (); Set.cons e (parseEquationsX ())
					| '}' -> Set.make [e]
					| _ -> rubbish "at the end of equation"

	let parseEquations (): equations =
		match peek() with
			| '{' -> skip();
					let res = parseEquationsX () in
					let _ = getChar '}' in
						res
			| _ -> Set.empty

	let equation2str (l, r) =
		ExpressionSyntax.expression2str l
		^ " = "
		^ ExpressionSyntax.expression2str r
end

module ConditionsSyntax =
struct
	open CharType
	open Scanner
	open AttributeGrammarBasics

	let parseCondition (): condition =
		ExpressionSyntax.parseExpression ()

	let rec parseConditionsX (): conditions =
		match peek() with
		| ']' -> Set.empty
		| _ ->
			let e = parseCondition () in
				match peek () with
				| ';' -> skip (); Set.cons e (parseConditionsX ())
				| ']' -> Set.make [e]
				| _ -> rubbish "at the end of condition"
			
	let parseConditions (): conditions =
		match peek() with
		| '[' -> skip();
				let res = parseConditionsX () in
				let _ = getChar ']' in
					res
		| _ -> Set.empty

	let condition2str c =
		ExpressionSyntax.expression2str c
end	

module AttributeGrammarSyntax =
struct
	open CharType
	open Scanner
	open AttributeGrammarBasics

	let parseSymbol () : symbol =
		if peek () = '<' then
			let str = getDelim '<' '>' in 
				str2symb ("<" ^ str ^ ">")
		else
			char2symb (get ())
						
	let parseHead (): symbol =
		match peek() with
		| ' ' -> invalid "Empty rule"
		| _ -> parseSymbol ()
		
	let parseNeck (): unit =
		getStr "->"

	let rec parseBody (): word =
		match peek() with
		| ' ' | '{' -> []
		| _ -> let sy = parseSymbol () in
					sy::parseBody ()

	let parseFinish (): unit =
		match peek() with
		| ' ' -> ()
		| _ -> 	rubbish "at the end of rule"

	let parseLine line: rules =
		if String.trim line = "" then
			Set.empty
		else begin
			Scanner.start "AttributeGrammarSyntax" line;
			try
				let h = parseHead () in
				let _ = parseNeck () in
				let b = parseBody () in
				let b = if b = [] then [epsilon] else b in
				let e = EquationsSyntax.parseEquations () in
				let c = ConditionsSyntax.parseConditions () in
				let _ = parseFinish () in
					Set.make [{head=h; body=b;
						equations=e; conditions=c}]
			with Not_found ->
				Set.empty
		end

	let parse rs: rules =
		Set.flatMap parseLine rs
					
	let rule2str {head=h; body=b; equations=eqs; conditions=conds} =
		let rule = (symb2str h) ^ " -> " ^ (word2str b) in
		let eqs = Set.toList eqs in
		let eqs = String.concat "; " (List.map EquationsSyntax.equation2str eqs) in
		let eqs = if eqs = "" then "" else " {" ^ eqs ^ "}" in
		let conds = Set.toList conds in
		let conds = String.concat "; " (List.map ConditionsSyntax.condition2str conds) in
		let conds = if conds = "" then "" else " [" ^ conds ^ "]" in
			rule ^  eqs ^ conds

	let toString rs: string =
		let rl = Set.toList rs in
			String.concat "\n" (List.map rule2str rl)

	let toStringList rs: string list =
		let rl = Set.toList rs in
			List.map rule2str rl
	
	let (-->) h b : rule =
		{ head = h; body = str2word b;
		equations=Set.empty; conditions=Set.empty }

	let show rs =
		Util.println [toString rs]
end


module AttributeGrammarJSon =
struct
end

module AttributeGrammarConversions =
struct
	open AttributeGrammarBasics
	open AttributeGrammarSyntax

	let fromJSon (j: JSon.t): t =
		if JSon.isNull j || not (JSon.hasField j "kind") then
			ag_zero
		else {
			alphabet = JSon.fieldSymbolSet j "alphabet";
			variables = JSon.fieldSymbolSet j "variables";
			inherited = JSon.fieldSymbolSet j "inherited";
			synthesized = JSon.fieldSymbolSet j "synthesized";
			initial = JSon.fieldSymbol j "initial";
			rules = AttributeGrammarSyntax.parse (JSon.fieldStringSet j "rules");
		}

	let toJSon0 (rep: t): JSon.t =
		JSon.makeAssoc [
			("alphabet", JSon.makeSymbolSet rep.alphabet);
			("variables", JSon.makeSymbolSet rep.variables);
			("inherited", JSon.makeSymbolSet rep.inherited);
			("synthesized", JSon.makeSymbolSet rep.synthesized);
			("initial", JSon.makeSymbol rep.initial);
			("rules", JSon.makeStringSet (Set.map rule2str rep.rules))
		]
	
	let toJSon2 (id: Entity.t) (rep: t): JSon.t =
		 JSon.append (Entity.toJSon id) (toJSon0 rep)

	let toJSon (rep: t): JSon.t =
		 toJSon2 (Entity.dummyId kind) rep
end

module AttributeGrammarBasicFunctions =
struct
	open AttributeGrammarBasics
	open AttributeGrammarConversions

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

module AttributeGrammarX =
struct
	open AttributeGrammarBasics
end

module AttributeGrammarLearnOCaml =
struct
	open AttributeGrammarBasics
	open AttributeGrammarX

	let moduleName =
		"AttributeGrammar"

	let xTypeName =
		"AttributeGrammar"

	let solution (name: string) (rep: t): string =
		""

	let prelude : string =
		""

	let example : JSon.t =
		JNull
end

module AttributeGrammarSupport =
struct
	include AttributeGrammarBasics
	include AttributeGrammarConversions
	include AttributeGrammarBasicFunctions
	include AttributeGrammarLearnOCaml
end
