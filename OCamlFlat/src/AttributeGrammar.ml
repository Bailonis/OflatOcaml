(*
 * AttributeGrammar.ml
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
 *  Written by Pedro Bailão (pb)
 *)

(*
 * ChangeLog:
 *
 * mar/2025 (pb) - validateAG implementation method.
 * feb/2025 (amd) - New file "AttributeGrammar.ml".
 *)

(*
 * Description: Attribute grammar functionality.
 *
 * TODO: More cleanup.
 *)

	open BasicTypes
	open Set  (* Ensure the Set module is opened *)
	
	module AttributeGrammarPrivate =
	struct
		open AttributeGrammarSupport
	
		let howMany (w: word) (v: variable) =
			List.lenght (List.filter (fun x-> x = v) w)

		let ag2cfg (rep: t): ContextFreeGrammarBasic.t =
			ContextFreeGrammarBasic.cfg_zero
		
		let validateAttrArg (ag:t) (r:rule) (v,i) =
			if i = 0 then 
				r.head = v && Set.belongs v ag.inherited
		else 
			let counter = howMany r.body v in 
				counter >= i 


(* adicionar a regra *)
		let rec validateExp (ag: t) (r: rule) (e: expression) : string =
			
			let attr_exists attr =
				(* usar o belongs em vez de listas*)
				Set.subset attr (Set.union ag.synthesized ag.inherited)
				
			in
			let vars_exists vars =
				Set.subset vars ag.variables
			in

			match e with
			| Int _ -> "int"
			| String _ -> "string"
			| Bool _ -> "bool"
			| Apply (attr, (var, i)) ->
					if attr_exists attr then
						if vars_exists var then 
						if validateAttrArg ag r (var,i) then "int"
						else "erro: variável não encontrada" (* mudar para mecanismo de erros*)
					else  "erro: atributo não encontrado"

			| Expr (op, l, r) ->
					let tl = validateExp ag l in
					let tr = validateExp ag r in
					if tl = tr then
						match op with
						| "+" | "*" ->
								if tl <> "string" then tl
								else "erro: incompatibilidade de tipos"
						| "<" | ">" | "<=" | ">=" | "=" | "<>" ->
								if tl = "int" then "bool"
								else "erro: incompatibilidade de tipos"
						| _ -> "erro: operador desconhecido"
					else "erro: incompatibilidade de tipos"
		
		let validateEquation (ag: t) ((lhs, rhs): equation): string =
			match lhs with
			| Apply _ ->
					let lhs_type = validateExp ag lhs in
					let rhs_type = validateExp ag rhs in
					if lhs_type = "int" && rhs_type = "int" then "valid"
					else "erro: incompatibilidade de tipos na equação"
			| _ -> "erro: lado esquerdo da equação deve ser Apply"
				
					
		let validate (name: string) (rep: AttributeGrammarSupport.t): unit = ()
			

		let accept (rep: t) (w: word): bool =
			false
	
	end
	
	module AttributeGrammar =
	struct
		include AttributeGrammarSupport
		open AttributeGrammarPrivate
	
		(* Make *)
		let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
		let make (arg: t Arg.alternatives): t = make arg validate
	
		(* Exercices support *)
		let checkProperty (fa: t) (prop: string) =
			match prop with
				| _ -> Model.checkProperty prop
		let checkExercise ex fa = Model.checkExercise ex (accept fa) (checkProperty fa)	
		let checkExerciseFailures ex fa = Model.checkExerciseFailures ex (accept fa) (checkProperty fa)
	
		(* Ops *)
		let stats = Model.stats
		let accept = accept
	end
	
	module AttributeGrammarTop =
	struct
		open AttributeGrammar
	end
	
	open AttributeGrammarTop
	
	module AttributeGrammarSupportTests : sig end =
	struct
		open AttributeGrammar
		open AttributeGrammarPrivate
		
		let active = true
		
		let ag = {| {
					kind : "attribute grammar",
					description : "",
					name : "ag",
					alphabet : ["[", "]"],
					variables : ["S"],
					inherited : [],
					synthesized : [],
					initial : "S",
					rules : [ "S -> [S] {l(S) = 2; l(S) = 'ole'; l(S0) = l(S1)} [123 + 56; 56; 'ola']",
										"S -> SS {l(S) = l(S1) + 3 + 'ola' + l(S12345)}",
										"S -> ~ {l(S0) = 6}",
										"S -> ~ {l(S0) = 1+2*3<T>F<=T>=5=T<>T+(1*2)}"
									]
	} |}

		let test0 () =
			let j = JSon.parse ag in
			let g = fromJSon j in
			let h = toJSon g in
				JSon.show h

		let test1 () =
			let g = make (Arg.Text ag) in
			let h = toJSon g in
			validate "ag" g;
			JSon.show h
					

		let runAll =
			if Util.testing active "AttributeGrammarSupport" then begin
				Util.header "test0";
				test0 ();
				Util.header "test1";
				test1 ();
			end
	end

