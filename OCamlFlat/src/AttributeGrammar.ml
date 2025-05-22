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
	open Set

	module AttributeGrammarPrivate =
	struct
		open AttributeGrammarSupport

		let howMany (body: word) (v: variable) =
			List.length (List.filter (fun x-> x = v) body)

		let ag2cfg (rep: t): ContextFreeGrammarBasic.t =
			ContextFreeGrammarBasic.cfg_zero

		let validateAttrArg (ag:t) (r:rule) (v,i) =
			if i = 0 then
				r.head = v && Set.belongs v ag.inherited
		else
			let counter = howMany r.body v in
				counter >= i


		let rec validateExp (name: string) (ag: t) (r: rule) (e: expression) : string =
					  let attr_exists attr =
					    Set.belongs attr (Set.union ag.synthesized ag.inherited)
					  in

					  let vars_exists vars =
					    Set.belongs vars ag.variables
					  in

					  match e with
					  | Int _ -> "int"
					  | String _ -> "string"
					  | Bool _ -> "bool"
					  | Apply (attr, (var, i)) ->
					      if attr_exists attr then
					        if vars_exists var then
					          if validateAttrArg ag r (var, i) then "int"
					          else Error.error name  "Variável não encontrada" "error"
					        else  Error.error name  "Variável não encontrada" "error"
					      else Error.error name  "Atributo não encontrado" "error"
					  | Expr (op, l, r_expr) ->
					      let tl = validateExp name ag r l in  (* Pass `r` explicitly *)
					      let tr = validateExp name ag r r_expr in  (* Pass `r` explicitly *)
					      if tl = tr then
					        match op with
					        | "+" | "*" ->
					            if tl <> "string" then tl
					            else Error.error name "Incompatibilidade de tipos" "error"
					        | "<" | ">" | "<=" | ">=" | "=" | "<>" ->
					            if tl = "int" then "bool"
					            else Error.error name "Incompatibilidade de tipos" "error"
					        | _ -> Error.error name "Operador desconhecido" "error"
					      else Error.error name "Incompatibilidade de tipos" "error"

		let validateEquation (name: string) (ag: t) ((lhs, rhs): equation) (r: rule): unit =
		    match lhs with
		    | Apply _ ->
		        let lhs_type = validateExp name ag r lhs in
		        let rhs_type = validateExp name ag r rhs in
		        if lhs_type = rhs_type && lhs_type <> "erro" then ()
		        else Error.error name "Incompatibilidade de tipos na equaçao" () (* passar os erros para ingles*)
		    | _ -> Error.error name "Lado esquerdo da equação deve ser Apply" ()

		    (*fazer vadildação das condições, fazer validar da expr e ver se é booleano*)
		    (*passo seguinte calcular os atributos utilizando a tree??*)
		    (*começar com atributos sintetizados*)

        let validateCondition (name: string) (ag: t) (cond: condition) (rule: rule): unit =
           if validateExp name ag rule cond = "bool" then ()
           else Error.error name "Condição deve ser booleana" ()


		let accept (rep: t) (w: word): bool =
			false

        let ag_to_cfg (ag: t): ContextFreeGrammar.t =
          {
            alphabet = ag.alphabet;
            variables = ag.variables;
            initial = ag.initial;
            rules = Set.map (fun r ->
              {
                ContextFreeGrammar.head = r.head;
                body = r.body
              }
            ) ag.rules
          }



        let cfg_to_ag (cfg: ContextFreeGrammar.t): t =
          {
            alphabet = cfg.alphabet;
            variables = cfg.variables;
            synthesized = Set.empty;
            inherited = Set.empty;
            initial = cfg.initial;
            rules = Set.map (fun (r: ContextFreeGrammar.rule) ->
              {
                head = r.head;
                body = r.body;
                equations = Set.empty;
                conditions = Set.empty
              }
            ) cfg.rules
          }

        let validateEquations (name: string) (rep: t): unit =
            Set.iter (fun r ->
                Set.iter (fun eq ->
                    validateEquation name rep eq r
                ) r.equations
            ) rep.rules

        let validateConditions (name: string) (rep: t): unit =
            Set.iter (fun r ->
                Set.iter (fun eq ->
                    validateCondition name rep eq r
                ) r.conditions
            ) rep.rules

        let validate (name: string) (rep: t): unit =
            let cfg = ag2cfg rep in
                ContextFreeGrammarPrivate.validate name cfg;
                validateEquations name rep;
                validateConditions name rep


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


        let test_ag_to_cfg () =
            let ag = make (Arg.Text ag) in
            let cfg = ag_to_cfg ag in
            let converted_ag = cfg_to_ag cfg in
            let h = toJSon converted_ag in
                JSon.show h

        let test_cfg_to_ag () =
          let ag = make (Arg.Text ag) in
          let cfg = ag_to_cfg ag in
          let converted_ag = cfg_to_ag cfg in
          (* Add assertions to verify the converted AG *)
          JSon.show (toJSon converted_ag)

        let runAll =
          if Util.testing active "AttributeGrammarSupport" then begin
            Util.header "test0";
            test0 ();
            Util.header "test1";
            test1 ();
            Util.header "test_ag_to_cfg";
            test_ag_to_cfg ();
            Util.header "test_cfg_to_ag";
            test_cfg_to_ag ();
          end
	end

