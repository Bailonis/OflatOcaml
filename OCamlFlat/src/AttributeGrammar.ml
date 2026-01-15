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
                if tl <> tr then Error.error name "Incompatibilidade de tipos" "error" else
                match op, tl with
                | "(", _ -> tl
                | "+", "int" -> "int"
                | "+", "string" -> "string"               (* allow concat *)
                | "+", _ -> Error.error name "Tipos inválidos para +" "error"
                | "-", "int" -> "int"
                | "-", _ -> Error.error name "Tipos inválidos para -" "error"
                | "*", "int" -> "int"
                | "*", _ -> Error.error name "Tipos inválidos para *" "error"
                | "/", "int" -> "int"
                | "/", _ -> Error.error name "Tipos inválidos para /" "error"
                | ("=" | "<>"), _ -> "bool"               (* same-type equality already ensured *)
                | ("<" | "<=" | ">" | ">="), ("int" | "string") -> "bool"
                | ("<" | "<=" | ">" | ">="), _ -> Error.error name "Tipos inválidos para comparação" "error"
                | _ -> Error.error name "Operador desconhecido" "error"


        let normalize_default_index (head_sym: symbol) (var: symbol) (i: int): int =
                  if i = -1 && var = head_sym then 0 else i

		let occurs_in_body (r: rule) (v: symbol) : int =
          List.length (List.filter (fun x -> x = v) r.body)

        let is_head_ref (head_sym: symbol) (var,i) =
          normalize_default_index head_sym var i = 0

        let is_child_ref (head_sym: symbol) (var,i) =
          not (is_head_ref head_sym (var,i))

        let is_inherited (ag: t) (attr: attribute) = Set.belongs attr ag.inherited
        let is_synthesized (ag: t) (attr: attribute) = Set.belongs attr ag.synthesized

        let validate_lhs_direction (name:string) (ag:t) (r:rule) (lhs: expression) : unit =
          match lhs with
          | Apply (attr, (var, i)) ->
              let head_sym = r.head in
              let idx = normalize_default_index head_sym var i in
              if idx = 0 then begin
                if not (is_synthesized ag attr) then
                  Error.error name "LHS to head must be synthesized attribute" ()
              end else begin
                if not (is_inherited ag attr) then
                  Error.error name "LHS to child must be inherited attribute" ()
              end
          | _ -> Error.error name "LHS must be Apply (internal)" ()

        let validateEquation (name: string) (ag: t) ((lhs, rhs): equation) (r: rule): unit =
          match lhs with
          | Apply (attr, (var, i)) ->
              let i' = normalize_default_index r.head var i in
              if i' = 0 then
                if var <> r.head then
                  Error.error name "LHS refers head but head symbol mismatch" ()
              else
                let c = occurs_in_body r var in
                if c < i' then
                  Error.error name "LHS child index out of range" ();

              if not (Set.belongs var ag.variables) then
                Error.error name "LHS variable is not a grammar variable" ();

              validate_lhs_direction name ag r lhs;

              let lhs_type = validateExp name ag r lhs in
              let rhs_type = validateExp name ag r rhs in
              if lhs_type = rhs_type && lhs_type <> "error" then ()
              else Error.error name "Type mismatch in equation" ()
          | _ -> Error.error name "LHS of equation must be Apply" ()


        let validateCondition (name: string) (ag: t) (cond: condition) (rule: rule): unit =
           if validateExp name ag rule cond = "bool" then ()
           else Error.error name "Condição deve ser booleana" ()

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

        let split_env (nodes: node list): node * node list =
          match nodes with
          | [] -> failwith "split_env: empty nodes"
          | head :: children -> (head, children)

        let replace_attr (attr: symbol) (value: value) (evs: (symbol * value) Set.t): (symbol * value) Set.t =
          let without_attr =
            Set.fold_left (fun acc (a, v) -> if a = attr then acc else Set.cons (a, v) acc) (Set.make []) evs
          in
          Set.cons (attr, value) without_attr

        let find_evals (var: symbol) (i: int) (nodes: node list): (symbol * value) Set.t =
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
                let (_, evs) = List.nth matches (k - 1) in evs
          | _ ->
              failwith "find_evals: invalid index"

        let update_target (var: symbol) (i: int) (attr: symbol) (value: value) (nodes: node list): node list =
          match nodes with
          | [] -> failwith "update_target: empty nodes"
          | (head_sym, head_evs) :: children ->
              let update_child k =
                let rec aux seen acc xs =
                  match xs with
                  | [] -> failwith "update_target: var not found in children"
                  | ((s, evs) as n) :: tl ->
                      if s = var then
                        if seen + 1 = k then List.rev acc @ ((s, replace_attr attr value evs) :: tl)
                        else aux (seen + 1) (n :: acc) tl
                      else aux seen (n :: acc) tl
                in
                aux 0 [] children
              in
              match i with
              | 0 ->
                  if head_sym <> var then failwith "update_target: i=0 targets head, but head symbol != var"
                  else (head_sym, replace_attr attr value head_evs) :: children
              | -1 -> (head_sym, head_evs) :: update_child 1
              | k when k > 0 -> (head_sym, head_evs) :: update_child k
              | _ -> failwith "update_target: invalid index"



        let is_inherited_eq_for (head_sym: symbol) (eq: equation): bool =
          match eq with
          | Apply (_, (var, i)), _ -> normalize_default_index head_sym var i <> 0
          | _ -> false

        let string_of_value = function
            | Int i    -> Printf.sprintf "Int(%d)" i
            | String s -> Printf.sprintf "String(%S)" s
            | Bool b   -> Printf.sprintf "Bool(%b)" b

        let type_err op l r expected =
          failwith (Printf.sprintf "Type error: operator %S on %s and %s; expected %s"
                      op (string_of_value l) (string_of_value r) expected)

    let evaluateOp (op: string) (l: value) (r: value): value =
        match op, l, r with
        | "(", v, _ -> v
        | "+", Int a, Int b -> Int (a + b)
        | "+", String a, String b -> String (a ^ b)
        | "+", _, _ -> type_err "+" l r "Int+Int or String+String"
        | "-", Int a, Int b -> Int (a - b)
        | "-", _, _ -> type_err "-" l r "Int-Int"
        | "*", Int a, Int b -> Int (a * b)
        | "*", _, _ -> type_err "*" l r "Int*Int"
        | "/", Int a, Int b -> if b = 0 then failwith "Division by zero" else Int (a / b)
        | "/", _, _ -> type_err "/" l r "Int/Int"
        | "=",  Int a,    Int b    -> Bool (a = b)
        | "=",  String a, String b -> Bool (a = b)
        | "=",  Bool a,   Bool b   -> Bool (a = b)
        | "=",  _, _ -> type_err "=" l r "same type"
        | "<>", Int a,    Int b    -> Bool (a <> b)
        | "<>", String a, String b -> Bool (a <> b)
        | "<>", Bool a,   Bool b   -> Bool (a <> b)
        | "<>", _, _ -> type_err "<>" l r "same type"
        | "<",  Int a,    Int b -> Bool (a <  b)
        | "<=", Int a,    Int b -> Bool (a <= b)
        | ">",  Int a,    Int b -> Bool (a >  b)
        | ">=", Int a,    Int b -> Bool (a >= b)
        | "<",  String a, String b -> Bool (a <  b)
        | "<=", String a, String b -> Bool (a <= b)
        | ">",  String a, String b -> Bool (a >  b)
        | ">=", String a, String b -> Bool (a >= b)
        | ("<" | "<=" | ">" | ">="), Bool _, _
        | ("<" | "<=" | ">" | ">="), _, Bool _ -> type_err op l r "Int or String comparison"
        | _ ->
        failwith (Printf.sprintf "Unknown operator or invalid operands: op=%S, left=%s, right=%s"
                 op (string_of_value l) (string_of_value r))

        let rec evaluate (head_sym: symbol) (e: expression) (nodes: node list): value =
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
                 let (_, b) = Set.find (fun (a, _) -> a = attr) evals in b
               with _ ->
                 failwith (Printf.sprintf "evaluate: attribute '%s' not found on %s[%d]"
                             (symb2str attr) (symb2str var) i'))
          | Expr (op, left, right) ->
              let l = evaluate head_sym left nodes in
              let r = evaluate head_sym right nodes in
              evaluateOp op l r

        let as_bool (v: value) : bool =
                  match v with
                  | Bool b -> b
                  | _ -> failwith "Condition must evaluate to Bool"

                let check_conditions_at_node
                  (head_sym : symbol)
                  (conds    : condition Set.t)
                  (env      : node list)
                  : unit =
                  Set.iter (fun cond ->
                    let v = evaluate head_sym cond env in
                    if not (as_bool v) then
                      failwith (Printf.sprintf
                        "Condition failed at node %s"
                        (symb2str head_sym))
                  ) conds

        let eval (head_sym: symbol) (e: equation) (nodes: node list): node list =
          match e with
          | Apply (attr, (var, i)), expr ->
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

        let getRoot (pt: parseTree): node =
          match pt with
          | Leaf n -> n
          | Node (n, _) -> n

        let getRootSymbol (pt: parseTree): symbol =
          getRoot pt |> fst
        let getChildren (pt: parseTree): parseTree list =
          match pt with
          | Leaf _ -> []
          | Node (_, children) -> children

        let getRootRule (ag: t) (pt: parseTree): rule =
          match pt with
          | Leaf _ -> failwith "getRootRule: leaf has no rule"
          | Node (_, children) ->
              let head = getRootSymbol pt in
              let body = List.map getRootSymbol children in
              try Set.find (fun r -> r.head = head && r.body = body) ag.rules with
              | _ ->
                  let candidates =
                    ag.rules
                    |> SetUtil.to_list
                    |> List.filter (fun r -> r.head = head)
                    |> List.map (fun r ->
                         Printf.sprintf "- %s -> %s"
                           (symb2str r.head)
                           (String.concat " " (List.map symb2str r.body)))
                    |> String.concat "\n"
                  in
                  failwith (Printf.sprintf
                    "getRootRule: no rule matches head=%s, body=[%s]\nCandidates with same head:\n%s"
                    (symb2str head)
                    (String.concat " " (List.map symb2str body))
                    (if candidates = "" then "(none)" else candidates))

        let updateRoot (pt: parseTree) (n: node): parseTree =
          match pt with
          | Leaf _ -> Leaf n
          | Node (_, children) -> Node (n, children)

        type target =
          | Head
          | Child of symbol * int  (* 1-based occurrence *)

        let target_of_ref (head_sym : symbol) ((var, i) : symbol * int) : target =
          if i = 0 then Head
          else if i = -1 then
            if var = head_sym then Head else Child (var, 1)
          else if i > 0 then Child (var, i)
          else failwith "target_of_ref: invalid index"

        let stable_eq_order (head_sym: symbol) (equations: equation Set.t): equation list =
          let key_of (eq: equation) =
            match eq with
            | Apply (attr, (var, i)), _rhs ->
                begin match target_of_ref head_sym (var, i) with
                | Head -> (0, "", 0, symb2str attr)
                | Child (sym, occ) -> (1, symb2str sym, occ, symb2str attr)
                end
            | _ -> (2, "", max_int, "")
          in
          equations
          |> SetUtil.to_list
          |> List.sort (fun a b -> compare (key_of a) (key_of b))

        let apply_equations_at_head
            (head_sym  : symbol)
            (nodes     : node list)
            (equations : equation Set.t)
          : node list =
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
          let eqs = stable_eq_order head_sym equations in
          List.fold_left
            (fun acc_nodes eq -> eval head_sym eq acc_nodes)
            nodes
            eqs

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
                | Int v    -> Printf.printf "  Attribute: %s = %d\n" (symb2str attr) v
                | String s -> Printf.printf "  Attribute: %s = %s\n" (symb2str attr) s
                | Bool b   -> Printf.printf "  Attribute: %s = %b\n" (symb2str attr) b
              ) evals;
              List.iter print_parse_tree children

        let rec list_update_at n x = function
          | [] -> failwith "list_update_at: index out of bounds"
          | _ :: xs when n = 0 -> x :: xs
          | y :: xs -> y :: list_update_at (n - 1) x xs

        let set_filter (pred : 'a -> bool) (s : 'a Set.t) : 'a Set.t =
          Set.fold_left (fun acc x -> if pred x then Set.cons x acc else acc) (Set.make []) s

        let eq_targets_head (head_sym : symbol) (eq : equation) : bool =
          match eq with
          | (Apply (_attr, (var, i)), _rhs) ->
              begin match target_of_ref head_sym (var, i) with
              | Head -> true
              | Child _ -> false
              end
          | _ -> false

        let eq_targets_child (head_sym : symbol) ((child_sym, k) : symbol * int) (eq : equation) : bool =
          match eq with
          | (Apply (_attr, (var, i)), _rhs) ->
              begin match target_of_ref head_sym (var, i) with
              | Head -> false
              | Child (sym, occ) -> sym = child_sym && occ = k
              end
          | _ -> false

        let child_occurrences (children : parseTree list) : (symbol * int) list =
          let rec loop counts acc = function
            | [] -> List.rev acc
            | pt :: tl ->
                let (s, _) = getRoot pt in
                let seen = try List.assoc s counts with Not_found -> 0 in
                let k = seen + 1 in
                let counts' = (s, k) :: List.remove_assoc s counts in
                loop counts' ((s, k) :: acc) tl
          in
          loop [] [] children

        let pick_child_node_by_occ ((sym, k) : symbol * int) (env_tail : node list) : node =
          let rec aux occ = function
            | [] ->
                failwith (Printf.sprintf
                  "pick_child_node_by_occ: could not find %s[%d] among children in environment"
                  (symb2str sym) k)
            | ((s, _) as n) :: tl ->
                if s = sym then
                  let occ' = occ + 1 in
                  if occ' = k then n else aux occ' tl
                else
                  aux occ tl
          in
          aux 0 env_tail

        let rec zip_update_children (children : parseTree list) (env_tail : node list) : parseTree list =
          match children, env_tail with
          | [], [] -> []
          | c :: cs, e :: es -> updateRoot c e :: zip_update_children cs es
          | _ ->
              failwith (Printf.sprintf
                "zip_update_children: arity mismatch (children=%d, env_tail=%d)"
                (List.length children) (List.length env_tail))

        let rec calcAtributes (ag : t) (pt : parseTree) : parseTree =
          match pt with
          | Leaf _ ->
              pt

          | Node (((head_sym, _) as head), children) ->
              let rule = getRootRule ag (Node (head, children)) in

              let children' = eval_children_left_to_right ag head rule.equations children in

              let head_eqs = set_filter (eq_targets_head head_sym) rule.equations in
              let env2 = head :: List.map getRoot children' in
              let env3 = apply_equations_at_head head_sym env2 head_eqs in
              check_conditions_at_node head_sym rule.conditions env3;

              match env3 with
              | (new_head_sym, new_head_evs) :: child_envs ->
                  let children'' = zip_update_children children' child_envs in
                  Node ((new_head_sym, new_head_evs), children'')
              | [] ->
                  failwith "calcAtributes: empty environment after synthesized equations"

        and eval_children_left_to_right
            (ag       : t)
            (head     : node)
            (eqs      : equation Set.t)
            (children : parseTree list)
          : parseTree list =
          let head_sym = fst head in
          let occs = child_occurrences children in

          let rec loop
              (processed   : parseTree list)        (* already evaluated children, in reverse order *)
              (remaining   : parseTree list)        (* children yet to process, in order *)
              (remaining_o : (symbol * int) list)   (* their (sym,occ) *)
            : parseTree list =
            match remaining, remaining_o with
            | [], [] ->
                List.rev processed

            | child :: rest, occ :: occs_rest ->
                let processed_nodes = List.rev processed |> List.map getRoot in
                let env_before = head :: (processed_nodes @ (List.map getRoot (child :: rest))) in

                let inh_eqs = set_filter (eq_targets_child head_sym occ) eqs in
                let env_after_inh = apply_equations_at_head head_sym env_before inh_eqs in

                let child_node_after_inh =
                  match env_after_inh with
                  | _head_after :: env_tail -> pick_child_node_by_occ occ env_tail
                  | [] -> failwith "calcAtributes: empty environment after inherited equations"
                in
                let child_with_inh = updateRoot child child_node_after_inh in

                let child_evaluated = calcAtributes ag child_with_inh in

                loop (child_evaluated :: processed) rest occs_rest

            | _ ->
                failwith "calcAtributes: internal error (children/occurrences mismatch)"
          in
          loop [] children occs


        let is_terminal (ag: t) (s: symbol) = Set.belongs s ag.alphabet
        let is_variable (ag: t) (s: symbol) = Set.belongs s ag.variables

        let rules_by_head (ag: t) : (symbol, word list) Hashtbl.t =
          let tbl = Hashtbl.create 97 in
          Set.iter (fun (r: rule) ->
            let bodies = try Hashtbl.find tbl r.head with Not_found -> [] in
            Hashtbl.replace tbl r.head (r.body :: bodies)
          ) ag.rules;
          tbl

        let normalize_body (body: word) : word =
          List.filter (fun s -> s <> epsilon) body

        let is_A_to_a (ag: t) (body: word) : bool =
          match normalize_body body with
          | [a] when is_terminal ag a -> true
          | _ -> false

        let is_A_to_BC (ag: t) (body: word) : bool =
          match normalize_body body with
          | [b; c] when is_variable ag b && is_variable ag c -> true
          | _ -> false

        let bodies_of (tbl: (symbol, word list) Hashtbl.t) (a: symbol) : word list =
          try Hashtbl.find tbl a with Not_found -> []

        let accept_ag_with_tree (ag: t) (pt: parseTree) : bool =
          try
            let _final = calcAtributes ag pt in
            true
          with Failure _ -> false

        let is_all_terminals (ag: t) (sf: word) : bool =
          List.for_all (is_terminal ag) (normalize_body sf)

        let expand_once (ag: t) (sf: word) : word list =
          let tbl = rules_by_head ag in
          let rec aux left right =
            match right with
            | [] -> []
            | x::xs ->
                if is_variable ag x then
                  let bodies = bodies_of tbl x in
                  List.map (fun b -> List.rev left @ (normalize_body b) @ xs) bodies
                else
                  aux (x::left) xs
          in
          aux [] sf

        let generate ?(max_depth=5) ?(max_words=50) (ag: t) : word list =
          let start = [ag.initial] in
          let q = Queue.create () in
          Queue.add (start, 0) q;
          let acc = ref [] in
          let seen = Hashtbl.create 10007 in
          let mark sf =
            let key = String.concat " " (List.map symb2str sf) in
            if Hashtbl.mem seen key then true else (Hashtbl.add seen key (); false)
          in
          while (not (Queue.is_empty q)) && (List.length !acc < max_words) do
            let (sf, d) = Queue.take q in
            if not (mark sf) then begin
              if is_all_terminals ag sf then
                acc := sf :: !acc
              else if d < max_depth then
                List.iter (fun sf' -> Queue.add (sf', d+1) q) (expand_once ag sf)
            end
          done;
          List.rev !acc


        let ga_to_cfg (ag: t): ContextFreeGrammarBasic.t =
          let rules =
            let rules_set = ref Set.empty in
            Set.iter (fun r ->
              let head_sym = r.head in
              let body_syms = r.body in
              let rule = { ContextFreeGrammarBasic.head = head_sym; body = body_syms } in
              rules_set := Set.add rule !rules_set
            ) ag.rules;
            !rules_set
          in
          {
            alphabet = ag.alphabet;
            variables = ag.variables;
            initial = ag.initial;
            rules;
          }

        let cfg_to_ga (cfg: ContextFreeGrammarBasic.t): t =
          {
            alphabet = cfg.alphabet;
            variables = cfg.variables;
            synthesized = Set.empty; (* Default value for synthesized attributes *)
            inherited = Set.empty;   (* Default value for inherited attributes *)
            initial = cfg.initial;
            rules = (Set.map (fun (r: ContextFreeGrammarBasic.rule) ->
              {
                head = r.head;
                body = r.body;
                equations = Set.empty; (* Default value for equations *)
                conditions = Set.empty; (* Default value for conditions *)
              }
            ) cfg.rules : AttributeGrammarSupport.rules); (* Correct placement of type annotation *)
          }

          let validate (name: string) (rep: t): unit =
                      let cfg = ga_to_cfg rep in
                          ContextFreeGrammarPrivate.validate name cfg;
                          validateEquations name rep;
                          validateConditions name rep


		let accept (ag: t) (w: word): bool =
          let cfg = ga_to_cfg ag in
          ContextFreeGrammarBasic.accept cfg w

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
        let accept_ag_with_tree = accept_ag_with_tree
        let generate ?max_depth ?max_words = generate ?max_depth ?max_words

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
                name : "ag1",
                alphabet : ["0","1","2","3","4","5","6","7","8","9","*"],
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

        let pt1 =
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
                  ] )
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

        let test_accept_with_tree_ok () =
          let g = make (Arg.Text ag1) in
          let ok = accept_ag_with_tree g pt1 in
          Printf.printf "accept_ag_with_tree(pt1) = %b\n" ok

        let test_accept_words () =
          let g = AttributeGrammar.make (Arg.Text ag1) in

          let cfg : ContextFreeGrammarBasic.t =
            AttributeGrammarPrivate.ga_to_cfg g
          in
          let sym = BasicTypes.str2symb in
          let three = sym "3" and star = sym "*" and two = sym "2" in
          let w = [three; star; two] in

          let r = ContextFreeGrammarBasic.accept cfg w in
          Printf.printf "AG->CFG.accept %s = %b (expected: true)\n"
            (BasicTypes.word2str w) r
        ;;

        let runAll =
          if Util.testing active "AttributeGrammarSupport" then begin
            Util.header "test1";
            test1 ();

            Util.header "test_accept_with_tree_ok";

            Util.header "test_accept_words";
          end
	end