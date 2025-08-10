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

		let validateAttrArg (ag:t) (r:rule) (attr: attribute) (v,i) =
			if i = 0 then
				r.head = v && Set.belongs attr (Set.union ag.synthesized ag.inherited)
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
					  | Const (Int _) -> "int"
					  | Const (String _) -> "string"
					  | Const (Bool _) -> "bool"
					  | Apply (attr, (var, i)) ->
					      if attr_exists attr then
					        if vars_exists var then
					          if validateAttrArg ag r attr (var, i) then "int"
					          else Error.error name  "Argumento do Atributo invalido" "error"
					        else  Error.error name  "Variável não encontrada" "error"
					      else Error.error name  "Atributo não encontrado" "error"
					  | Expr (op, l, r_expr) ->
					      let tl = validateExp name ag r l in
					      let tr = validateExp name ag r r_expr in
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

        let rec collectFromExpression (exp: expression): attributes =
          match exp with
            | Apply (attr, _) -> Set.make [attr]
            | Expr (_, l, r) -> Set.union (collectFromExpression l) (collectFromExpression r)
            | _ -> Set.empty

        let collectFromEquation (eq: equation): attributes =
            let (lhs, rhs) = eq in
            Set.union (collectFromExpression lhs) (collectFromExpression rhs)

        let collectFromCondition (cond: condition): attributes =
            collectFromExpression cond

        let collectFromRule (r: rule): attributes =
            let fromEquations = Set.flat_map collectFromEquation r.equations in
            let fromConditions = Set.flat_map collectFromCondition r.conditions in
            Set.union fromEquations fromConditions

        let removeUnusedAttributes (rep: t): t =
            let used = Set.flat_map collectFromRule rep.rules in
            let newSynthesized = Set.inter rep.synthesized used in
            let newInherited = Set.inter rep.inherited used in
           {
              rep with
              synthesized = newSynthesized;
              inherited = newInherited;
            }

        let collectVarsFromRule (r: rule) (vars: variables): variables =
          Set.inter vars (Set.make r.body)

        let removeUnusedRulesAndVariables (rep: t) =
          let rec collectUsedVariables rules used =
            match rules with
            | [] -> used
            | rule :: rest ->
                let usedInBody = List.fold_left (fun acc sym -> Set.cons sym acc) used rule.body in
                collectUsedVariables rest (Set.cons rule.head usedInBody)
          in
          let usedVariables = collectUsedVariables (Set.toList rep.rules) (Set.make [rep.initial]) in
          let newVariables = Set.filter (fun var -> Set.belongs var usedVariables) rep.variables in
          let newRules =
            Set.filter
              (fun rule ->
                Set.belongs rule.head newVariables &&
                List.for_all (fun sym -> Set.belongs sym newVariables || Set.belongs sym rep.alphabet) rule.body
              )
              rep.rules
          in
          { rep with variables = newVariables; rules = newRules }

        let getRoot (pt: parseTree): node =
                match pt with
                | Leaf ((s,e)) -> (s,e)
                | Node ((s,e), _) -> (s,e)

        let getRootSymbol (pt: parseTree): symbol =
            getRoot pt |> fst

        let getRule (ag: t) (head: variable) (body: word): rule =
          try
            Set.find (fun r ->
             r.head = head && r.body = body) ag.rules
          with Not_found ->

            failwith (Printf.sprintf "No matching rule found for head: %s and body: %s"
              (symb2str head)
              (String.concat ", " (List.map symb2str body)))

       let rec associ key i l =
           Printf.printf "Searching for key: %s, index: %d in list: [%s]\n"
             (symb2str key) i
             (String.concat "; " (List.map (fun (a, _) -> symb2str a) l));
           match l with
           | [] ->
               failwith (Printf.sprintf "associ: Key '%s' with index %d not found in the list" (symb2str key) i)
           | (a, b) :: xs when a = key ->
               if i = 1 || i = -1 then b
               else associ key (i - 1) xs
           | (a, b) :: xs ->
               associ key i xs

        let evaluateOp (op: string) (l: value) (r:value): value =
            match op with
                | "+" ->(
                    match (l, r) with
                    | Int li, Int ri -> Int (li + ri)
                    | String ls, String rs -> String (ls ^ rs)
                    | _ -> failwith "Invalid expression in evaluation"
                )
                | "*" -> (
                    match (l, r) with
                    | Int li, Int ri -> Int (li * ri)
                    | _ -> failwith "Invalid expression in evaluation"
                )

                (* acabar isto com os outros valores  -> *)
                | _ -> failwith "Unknown operator in evaluation"

       let rec evaluate (e: expression) (nodes: node list): value =
            match e with
            | Const v -> v
            | Apply (attr, (var, i)) ->
                let evals = associ var i nodes in
                let (_,b) = Set.find (fun (a, _) -> a = attr) evals in
                b
            | Expr (op, left, right) ->
                let l = evaluate left  nodes in
                let r = evaluate right nodes in
                evaluateOp op l r


        let rec update a b l =
            match l with
            | [] -> [(a, b)]
            | (x, y) :: xs when x = a -> (x, b) :: xs
            | x :: xs -> x :: update a b xs

        (* Evaluate an equation and update the list of evaluations *)
       let eval (e: equation) (nodes: node list): node list =
            match e with
            | (Apply (attr, (var, _)), expr) ->
            (try
                let ev = (attr, evaluate expr nodes) in
                let evs = List.assoc var nodes in
                let new_evs = Set.cons ev evs in
                update var new_evs nodes
            with _ ->
                nodes
             )
            | _ -> failwith "Invalid equation in evaluation"

        let printAllHeadsAndBodies (ag: t): unit =
          Set.iter (fun r ->
            Printf.printf "Head: %s\n" (symb2str r.head);
            Printf.printf "Body: %s\n" (String.concat ", " (List.map symb2str r.body))
          ) ag.rules

        let rec print_parse_tree pt =
         match pt with
         | Leaf (symbol, _) ->
             Printf.printf "Leaf: %s\n" (symb2str symbol)
         | Node ((symbol, evals), children) ->
             Printf.printf "Node: %s\n" (symb2str symbol);
             Set.iter (fun (attr, value) ->
               match value with
               | Int v -> Printf.printf "  Attribute: %s = %d\n" (symb2str attr) v
               | String s -> Printf.printf "  Attribute: %s = %s\n" (symb2str attr) s
               | Bool b -> Printf.printf "  Attribute: %s = %b\n" (symb2str attr) b
             ) evals;
             List.iter print_parse_tree children

      let updateRoot a n =
            match a with
            | Leaf _ -> Leaf n
            | Node (_, children) ->
                   Node (n, children)

      let rec calcAtributes (ag: t) (pt: parseTree): parseTree =
        match pt with
        | Leaf n ->
            Leaf n
        | Node (_, children) ->
            let head = getRootSymbol pt in
            let body = List.map getRootSymbol children in
            let rule = getRule ag head body in

            let children = List.map (calcAtributes ag) children in
            let all = pt::children in
            let nodes = List.map getRoot all in
            let nodes = Set.fold_left (fun a e ->  eval e a) nodes rule.equations in
            let all = List.map2 (fun a n -> updateRoot a n) all nodes in
            let result = Node (getRoot (List.hd all), List.tl all) in
            Printf.printf "Current parse tree:\n";
            print_parse_tree result;
            result



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

		let ag0 = {| {
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

        let ag = {| {
                            kind : "attribute grammar",
                            description : "",
                            name : "ag",
                            alphabet : ["[", "]"],
                            variables : ["S"],
                            inherited : ["l"],
                            synthesized : ["l"],
                            initial : "S",
                            rules : [ "S -> [S] {l(S) = 2; l(S) = 'ole'; l(S0) = l(S1)} [123 + 56; 56; 'ola']",
                                                "S -> SS {l(S) = l(S1) + 3 + 'ola' + l(S1)}",
                                                "S -> ~ {l(S0) = 6}",
                                                "S -> ~ {l(S0) = 1+2*3<T>F<=T>=5=T<>T+(1*2)}"
                                            ]
            } |}

         let ag1 = {| {
                                    kind : "attribute grammar",
                                    description : "",
                                    name : "ag1",
                                    alphabet : ["[", "]"],
                                    variables : ["S","E","F"],
                                    inherited : [""],
                                    synthesized : ["v"],
                                    initial : "S",
                                    rules : [ "S -> E {v(S) = v(E)}",
                                                "E -> E * F {v(E0) = v(E1) * v(F)}",
                                                "E -> F {v(E) = v(F)}",
                                                "F -> 0 {v(F) = 0}",
                                                "F -> 1 {v(F) = 1}",
                                                "F -> 2 {v(F) = 2}",
                                                "F -> 3 {v(F) = 3}",
                                                "F -> 4 {v(F) = 4}",
                                                "F -> 5 {v(F) = 5}",
                                                "F -> 6 {v(F) = 6}",
                                                "F -> 7 {v(F) = 7}",
                                                "F -> 8 {v(F) = 8}",
                                                "F -> 9 {v(F) = 9}"
                                                ]
                    } |}
        let ag2 = {| {
                                            kind : "attribute grammar",
                                            description : "",
                                            name : "ag2",
                                            alphabet : ["[", "]"],
                                            variables : ["S","E","F","X"],
                                            inherited : ["d"],
                                            synthesized : ["v", "r"],
                                            initial : "S",
                                            rules : [ "S -> E {v(S) = v(E)}",
                                                        "E -> F X {v(E) = r(X) ; d(X) = v(F)}",
                                                        "X -> + F X {r(X0) = r(X1) ; d(X1) = d(X0) + v(F)}",
                                                        "X -> ~ {r(X) = d(X)}",
                                                        "F -> 0 {v(F) = 0}",
                                                        "F -> 1 {v(F) = 1}",
                                                        "F -> 2 {v(F) = 2}",
                                                        "F -> 3 {v(F) = 3}",
                                                        "F -> 4 {v(F) = 4}",
                                                        "F -> 5 {v(F) = 5}",
                                                        "F -> 6 {v(F) = 6}",
                                                        "F -> 7 {v(F) = 7}",
                                                        "F -> 8 {v(F) = 8}",
                                                        "F -> 9 {v(F) = 9}"
                                                        ]
                            } |}


        let e s = (symb s, Set.empty);;

        let pt =
          Node (e "S", [
              Node (e "E", [
                  Node (e "E", [
                      Node (e "F", [
                          Leaf (e "3")
                      ])
                  ]);
                  Leaf (e "*");
                  Node (e "F", [
                      Leaf (e "2")
                  ])
              ])
          ])

         let parse_tree =
           Node (e "S", [
               Node (e "E", [
                   Node (e "F", [
                       Leaf (e "3")
                   ]);
                   Node (e "X", [
                       Leaf (e "+");
                       Node (e "F", [
                           Leaf (e "2")
                       ]);
                       Node (e "X", [
                           Leaf (e "+");
                           Node (e "F", [
                               Leaf (e "9")
                           ]);
                           Node (e "X", [
                               Leaf (e "~")
                           ])
                       ])
                   ])
               ])
           ])

		let test0 () =
			let j = JSon.parse ag2 in
			let g = fromJSon j in
			let h = toJSon g in
				JSon.show h

		let test1 () =
			let g = make (Arg.Text ag1) in
			let newTree = calcAtributes g pt in
			print_parse_tree newTree


	    let test2 () =
            let g = make (Arg.Text ag2) in
            let newTree = calcAtributes g parse_tree in
            print_parse_tree newTree

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
            Util.header "test2";
            test2();
          end
	end

