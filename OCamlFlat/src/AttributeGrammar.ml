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

    module SetUtil = struct
      let to_list s =
        Set.fold_left (fun acc x -> x :: acc) [] s |> List.rev
    end

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

       (* ***************************************************************** *)
       let set_filter pred (s : 'a Set.t) : 'a Set.t =
         Set.fold_left (fun acc x -> if pred x then Set.cons x acc else acc) (Set.make []) s

       (* Split the evaluation environment into (head, children).
          'nodes' is built as [head :: children] upstream. *)
       let split_env (nodes: node list) : node * node list =
         match nodes with
         | [] -> failwith "split_env: empty nodes"
         | head :: children -> (head, children)

       (* Replace or insert an attribute in an eval set, ensuring uniqueness by attr.
          We avoid Set.filter (in case your Set doesn’t have it) and rebuild via fold. *)
       let replace_attr (attr: symbol) (value: value) (evs: (symbol * value) Set.t)
         : (symbol * value) Set.t =
         let empty = Set.make [] in
         let without_attr =
           Set.fold_left
             (fun acc (a, v) -> if a = attr then acc else Set.cons (a, v) acc)
             empty
             evs
         in
         Set.cons (attr, value) without_attr

       (* Find evals for (var, i) with the correct semantics:
          - i = 0  -> head (must match var)
          - i = -1 -> first occurrence of 'var' among CHILDREN
          - i > 0  -> i-th occurrence (1-based) of 'var' among CHILDREN
       *)
       let find_evals (var: symbol) (i: int) (nodes: node list) : (symbol * value) Set.t =
         let (head, children) = split_env nodes in
         let (head_sym, head_evs) = head in
         match i with
         | 0 ->
             if head_sym = var then head_evs
             else failwith "find_evals: i=0 refers to head but head symbol != var"
         | -1 ->
             let rec first = function
               | [] -> failwith "find_evals: var not found among children"
               | (s, evs) :: xs -> if s = var then evs else first xs
             in
             first children
         | k when k > 0 ->
             let matches = List.filter (fun (s, _) -> s = var) children in
             if k > List.length matches then
               failwith "find_evals: var occurrence out of range among children"
             else
               let (_, evs) = List.nth matches (k - 1) in
               evs
         | _ ->
             failwith "find_evals: invalid index (use 0 for head, -1 for first child, or positive nth child)"

       (* Update the correct target occurrence on the LHS with (attr := value) *)
       let update_target (var: symbol) (i: int) (attr: symbol) (value: value) (nodes: node list)
         : node list =
         match nodes with
         | [] -> failwith "update_target: empty nodes"
         | (head_sym, head_evs) :: children ->
             let update_child k =
               let rec aux seen acc xs =
                 match xs with
                 | [] -> failwith "update_target: var not found in children"
                 | ((s, evs) as n) :: tl ->
                     if s = var then
                       if seen + 1 = k then
                         List.rev acc @ ((s, replace_attr attr value evs) :: tl)
                       else
                         aux (seen + 1) (n :: acc) tl
                     else
                       aux seen (n :: acc) tl
               in
               aux 0 [] children
             in
             match i with
             | 0 ->
                 if head_sym <> var then
                   failwith "update_target: i=0 targets head, but head symbol != var"
                 else
                   (head_sym, replace_attr attr value head_evs) :: children
             | -1 ->
                 let children' = update_child 1 in
                 (head_sym, head_evs) :: children'
             | k when k > 0 ->
                 let children' = update_child k in
                 (head_sym, head_evs) :: children'
             | _ ->
                 failwith "update_target: invalid index (use 0 for head, -1 first child, or positive nth child)"


       let getRoot (pt: parseTree): node =
                match pt with
                | Leaf ((s,e)) -> (s,e)
                | Node ((s,e), _) -> (s,e)

       let getRootSymbol (pt: parseTree): symbol =
            getRoot pt |> fst

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

       let string_of_value = function
         | Int i -> Printf.sprintf "Int(%d)" i
         | String s -> Printf.sprintf "String(%S)" s
         | Bool b -> Printf.sprintf "Bool(%b)" b

       let type_err op l r expected =
         failwith (Printf.sprintf "Type error: operator %S on %s and %s; expected %s"
                     op (string_of_value l) (string_of_value r) expected)

       let evaluateOp (op : string) (l : value) (r : value) : value =
         match op, l, r with
         (* Parentheses/grouping *)
         | "(", v, _ -> v

         (* Addition *)
         | "+", Int a, Int b -> Int (a + b)
         | "+", String a, String b -> String (a ^ b)
         | "+", _, _ -> type_err "+" l r "Int+Int or String+String"

         (* Subtraction *)
         | "-", Int a, Int b -> Int (a - b)
         | "-", _, _ -> type_err "-" l r "Int-Int"

         (* Multiplication *)
         | "*", Int a, Int b -> Int (a * b)
         | "*", _, _ -> type_err "*" l r "Int*Int"

         (* Division *)
         | "/", Int a, Int b ->
             if b = 0 then failwith "Division by zero"
             else Int (a / b)
         | "/", _, _ -> type_err "/" l r "Int/Int"

         (* Equality *)
         | "=", Int a, Int b -> Bool (a = b)
         | "=", String a, String b -> Bool (a = b)
         | "=", Bool a, Bool b -> Bool (a = b)
         | "=", _, _ -> type_err "=" l r "same type (Int/String/Bool)"

         (* Inequality *)
         | "<>", Int a, Int b -> Bool (a <> b)
         | "<>", String a, String b -> Bool (a <> b)
         | "<>", Bool a, Bool b -> Bool (a <> b)
         | "<>", _, _ -> type_err "<>" l r "same type (Int/String/Bool)"

         (* Order comparisons *)
         | "<",  Int a, Int b -> Bool (a < b)
         | "<=", Int a, Int b -> Bool (a <= b)
         | ">",  Int a, Int b -> Bool (a > b)
         | ">=", Int a, Int b -> Bool (a >= b)
         | "<",  String a, String b -> Bool (a < b)
         | "<=", String a, String b -> Bool (a <= b)
         | ">",  String a, String b -> Bool (a > b)
         | ">=", String a, String b -> Bool (a >= b)

         (* Disallow Bool ordering *)
         | ("<" | "<=" | ">" | ">="), Bool _, _
         | ("<" | "<=" | ">" | ">="), _, Bool _ ->
             type_err op l r "Int<Int or String<String"

         (* Unknown operator *)
         | _ ->
             failwith (Printf.sprintf "Unknown operator or invalid operands: op=%S, left=%s, right=%s"
                         op (string_of_value l) (string_of_value r))


       (* Normalize default index: if i = -1 and var = head_sym, use head (0); else keep *)
       let normalize_default_index (head_sym : symbol) (var : symbol) (i : int) : int =
         if i = -1 && var = head_sym then 0 else i

       let is_inherited_eq_for (head_sym : symbol) (eq : equation) : bool =
        match eq with
        | (Apply (_attr, (var, i)), _rhs) ->
            (* Normalize: if i = -1 and var = head, treat as i = 0 (head) *)
            let i' = normalize_default_index head_sym var i in
            i' <> 0
        | _ ->
            false  (* or fail if you never expect other LHS forms *)

       let rec evaluate (head_sym : symbol) (e: expression) (nodes: node list): value =
         match e with
         | Const v -> v
         | Apply (attr, (var, i)) ->
             let i' = normalize_default_index head_sym var i in
             let evals =
               try find_evals var i' nodes with
               | Failure msg ->
                   failwith (Printf.sprintf "evaluate: cannot resolve %s(%s[%d]) – %s"
                               (symb2str attr) (symb2str var) i' msg)
             in
             (try
                let (_, b) = Set.find (fun (a, _) -> a = attr) evals in
                b
              with _ ->
                failwith (Printf.sprintf "evaluate: attribute '%s' not found on %s[%d]"
                            (symb2str attr) (symb2str var) i'))
         | Expr (op, left, right) ->
             let l = evaluate head_sym left nodes in
             let r = evaluate head_sym right nodes in
             evaluateOp op l r

       (* Evaluate an equation and update the node list *)
       let eval (head_sym : symbol) (e: equation) (nodes: node list): node list =
         match e with
         | (Apply (attr, (var, i)), expr) ->
             let i' = normalize_default_index head_sym var i in
             let value =
               try evaluate head_sym expr nodes with
               | Failure msg ->
                   failwith (Printf.sprintf "eval %s.%s[%d]: %s"
                               (symb2str var) (symb2str attr) i' msg)
             in
             update_target var i' attr value nodes
         | _ ->
             failwith "Invalid equation in evaluation"



       let rec update a b l =
            match l with
            | [] -> [(a, b)]
            | (x, y) :: xs when x = a -> (x, b) :: xs
            | x :: xs -> x :: update a b xs

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


      let getChildren (pt: parseTree): parseTree list =
        match pt with
         | Leaf _ -> []
         | Node (_, children) -> children

      let getRootRule (ag: t) (pt: parseTree): AttributeGrammarSupport.rule =
        match pt with
         | Leaf _ ->
            failwith "getRootRule"
         | Node (_, children) ->
			let head = getRootSymbol pt in
			let body = List.map getRootSymbol children in
			try
               Set.find (fun r -> r.head = head && r.body = body) ag.rules
            with _ -> failwith (symb2str head)

      let updateRoot a n =
            match a with
            | Leaf _ -> Leaf n
            | Node (_, children) ->
                   Node (n, children)

      let apply_equations_at_head
          (head_sym : symbol)
          (nodes    : node list)
          (equations : equation list)
        : node list =
        (* Sanity: env must be [head :: children] and match head_sym *)
        let () =
          match nodes with
          | [] ->
              failwith "apply_equations_at_head: empty environment (nodes)"
          | (hs, _) :: _ when hs = head_sym -> ()
          | (hs, _) :: _ ->
              failwith
                (Printf.sprintf
                   "apply_equations_at_head: head symbol mismatch (expected %s, got %s)"
                   (symb2str head_sym) (symb2str hs))
        in
        List.fold_left
          (fun acc_nodes eq -> eval head_sym eq acc_nodes)
          nodes
          equations

      (* Convert Set.t to list deterministically (in insertion-like order) *)
      module SetUtil = struct
        let to_list s = Set.fold_left (fun acc x -> x :: acc) [] s |> List.rev
      end

      (* Update the nth (0-based) element in a list *)
      let rec list_update_at n x = function
        | [] -> failwith "list_update_at: index out of bounds"
        | _ :: xs when n = 0 -> x :: xs
        | y :: xs -> y :: list_update_at (n - 1) x xs

      (* Count occurrences of a symbol among children up to and including position [pos] (0-based).
         Returns the 1-based occurrence index of children.(pos) among all children with the same symbol. *)
      let occurrence_index (child_syms : symbol list) (pos : int) : int =
        let target = List.nth child_syms pos in
        let rec loop i cnt =
          if i > pos then cnt
          else
            let s = List.nth child_syms i in
            let cnt' = if s = target then cnt + 1 else cnt in
            loop (i + 1) cnt'
        in
        loop 0 0

      (* Decide if an equation’s LHS targets the *head* (synthesized at parent) after normalizing -1 *)
      let lhs_targets_head (head_sym : symbol) (eq : equation) : bool =
        match eq with
        | (Apply (_attr, (var, i)), _rhs) ->
            let i' = normalize_default_index head_sym var i in
            i' = 0
        | _ -> false

      (* Decide if an equation’s LHS targets a specific child at position [pos] (0-based) *)
      let lhs_targets_child_at
          (head_sym : symbol)
          (child_syms : symbol list)
          (pos : int)
          (eq : equation)
        : bool =
        match eq with
        | (Apply (_attr, (var, i)), _rhs) ->
            (* Child position -> which symbol & its occurrence index among peers up to this pos *)
            let child_sym = List.nth child_syms pos in
            if var <> child_sym then
              false
            else
              (* Normalize child index: -1 means first occurrence among children *)
              let target_occ =
                match i with
                | -1 -> 1
                | k when k > 0 -> k
                | 0 ->
                    (* i=0 would be the head; not a child *)
                    false |> ignore; 0
                | _ -> failwith "lhs_targets_child_at: invalid child index"
              in
              if target_occ = 0 then false
              else
                let occ_here = occurrence_index child_syms pos in
                occ_here = target_occ
        | _ -> false

      let rec calcAtributes (ag: t) (pt: parseTree): parseTree =
        match pt with
        | Leaf n ->
            Leaf n

        | Node (_, _) ->
            (* 0) Get rule and ordered equations *)
            let rule = getRootRule ag pt in
            let equations : equation list = SetUtil.to_list rule.equations in

            let head_sym = getRootSymbol pt in
            let children0 = getChildren pt in
            let child_syms = List.map getRootSymbol children0 in

            (* Build environment [head :: children] as nodes *)
            let env0 : node list = List.map getRoot (pt :: children0) in

            (* We will walk children left-to-right, threading env and building new children *)
            let rec eval_children_left_to_right env acc_children pos =
              if pos >= List.length children0 then
                (* All children processed left-to-right *)
                List.rev acc_children, env
              else
                let child_pt = List.nth children0 pos in

                (* 1) Apply *inherited* equations that target THIS child position *)
                let inh_for_child =
                  List.filter (lhs_targets_child_at head_sym child_syms pos) equations
                in
                let env_after_inh = apply_equations_at_head head_sym env inh_for_child in

                (* 2) Update this child's root node in its parse tree before recursion *)
                let child_node_after_inh = List.nth env_after_inh (pos + 1) in
                let child_pt_inh = updateRoot child_pt child_node_after_inh in

                (* 3) Recurse into this child so its synthesized attrs become available *)
                let child_pt_done = calcAtributes ag child_pt_inh in

                (* 4) Reflect the child's synthesized attrs back into the environment
                      so the next child (to the right) can depend on them *)
                let child_node_done = getRoot child_pt_done in
                let env_after_child =
                  list_update_at (pos + 1) child_node_done env_after_inh
                in

                eval_children_left_to_right env_after_child (child_pt_done :: acc_children) (pos + 1)
            in

            let (children_done, env_after_children) =
              eval_children_left_to_right env0 [] 0
            in

            (* 5) Apply *synthesized* equations that target the HEAD (after all children done) *)
            let syn_for_head = List.filter (lhs_targets_head head_sym) equations in
            let env_final = apply_equations_at_head head_sym env_after_children syn_for_head in

            (* 6) Rebuild final parse tree: updated head + fully evaluated children *)
            let new_head_node = List.hd env_final in
            let result = Node (new_head_node, children_done) in

            (* Printf.printf "Current parse tree:\n"; *)
            (* print_parse_tree result; *)

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
        let e s = (symb s, Set.empty);;

        let ag1 = {| {
                        kind : "attribute grammar",
                        description : "",
                        name : "ag3",
                        alphabet : ["[", "]"],
                        variables : ["S","E"],
                        inherited : ["d"],
                        synthesized : ["v"],
                        initial : "S",
                        rules : [ "S -> E {v(S) = v(E) ; d(E) = 'Funciona '}",
                                  "E -> ~ {v(E) = d(E) + 'bem!'}"
                                    ]
                            } |}

        let pt1 =
                        Node (e "S", [
                            Node (e "E", [
                              Leaf (e "~")
                            ])
                        ])

		let test0 () =
			let j = JSon.parse ag1 in
			let g = fromJSon j in
			let h = toJSon g in
				JSon.show h

		let test1 () =
			let g = make (Arg.Text ag1) in
			let newTree = calcAtributes g pt1 in
			Printf.printf "Final parse tree:\n";
			print_parse_tree newTree

        let runAll =
          if Util.testing active "AttributeGrammarSupport" then begin
            Util.header "test1";
            test1 ();
          end
	end