(*
 * ChomskyNormalForm.ml
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
 *  Written by Guilherme Fernandes (gf)
 *)

(*
 * ChangeLog:
 *
 * sep/2022 (amd) - Adapted the Guilherme code to the context of OCamlFLAT
 * jul/2022 (gf) - New module (original code inside the "contributions" dir)
 *)

(*
 * Description: Conversion of CFG to Chomsky Normal Form
 *)
 
open BasicTypes

module type ChomskyNormalFormSig =
sig
	open ContextFreeGrammarBasics

	val chomsky : t -> t	
	val cykAccept : t -> word -> bool	
	val accept : t -> word -> bool	
end

module ChomskyNormalForm : ChomskyNormalFormSig =
struct
	open ContextFreeGrammarBasics
	
	(*Remove rule rule from grammar cfg
	  and return a new grammar*)
	let removeRule (rule : rule) (cfg : t) : t = 
	  let newRules = Set.filter (fun x -> x <> rule) cfg.rules in 
	  {alphabet = cfg.alphabet;
	  variables = cfg.variables;
	  initial = cfg.initial;
	  rules = newRules
	  }
	;;

	(*Generate a random char*)
	let randVar (forbiddenSymbols : symbols) : symbol =
		let var = ref (Char.uppercase_ascii (Char.chr (97 + (Random.int 26)))) in
		while Set.belongs (char2symb !var) forbiddenSymbols do 
			var := Char.uppercase_ascii (Char.chr (97 + (Random.int 26))) 
		done;
		char2symb !var
	;;

	(* return the symbols used in grammar cfg *)
	let usedSymbols (cfg : t) : symbols = 
		Set.union cfg.variables cfg.alphabet
	;;

	(* return the direct derivations of the 
	   variable var in grammar cfg*)
	let directDeriv (var : symbol) (cfg : t) : rules =
		Set.filter ( fun x -> x.head = var) cfg.rules
	;;

	(* return the number of direct derivations
	 of the variable var in grammar cfg*)
	let numberOfProdVar (var : symbol) (cfg : t) : int = 
		Set.size (directDeriv var cfg)
	;;


	(*returns the rule with a body equal to bdy and,
	  if it does not exist, generates a new one with the body bdy*)
	  (* in rulesWithSameBdy it is necessary to check
		if numberOfProdVar x.head is equal to 1
		because if not, we may be changing
		the grammar ex: S -> a
		S -> b
		if we look for bdy 'a' we will find the S
		but we will also add production b
		the grammar
		 *)   
	let getRule (bdy : word) (cfg : t) : rule = 
		let rulesWithSameBdy =
				Set.filter ( fun x -> x.body = bdy && numberOfProdVar x.head cfg = 1) cfg.rules in
			if Set.size rulesWithSameBdy > 0 then 
				Set.hd rulesWithSameBdy
			else
				{head = randVar (usedSymbols cfg); body = bdy}
	;;


	(*checks if there is a rule in grammar cfg that 
	  contains the initial variable on the right-hand side*)
	let containsSInRHS (cfg : t) : bool = 
		Set.exists (fun x -> List.mem cfg.initial x.body) cfg.rules
	;;

	(* adds a new rule to grammar cfg and sSymb indicates if 
	  variable in the left-hand side is the initial variable*)
	let addRule (rule : rule) (cfg : t) (sSymb : bool): t = 
	  {alphabet = cfg.alphabet;
	  variables = Set.union (Set.make [rule.head]) cfg.variables;
	  initial = if sSymb then rule.head else cfg.initial;
	  rules = Set.cons rule cfg.rules
	  }
	;;

	(*START*)
	(*Eliminate the start symbol from right-hand side *)
	let delSFromRHS (cfg : t) : t = 
	  if containsSInRHS cfg then 
		let newS = randVar (usedSymbols cfg) in
		addRule {head = newS; body = [cfg.initial]} cfg true
	  else cfg
	;;

	(*------------------------------------------------------------------------------------------------*)

	(*checks if symbol var is a cfg grammar variable*)
	let isVariable (var : symbol) (cfg : t) : bool = 
	  Set.belongs var cfg.variables
	;;

	(*checks if symbol symbol is a terminal symbol*)
	let isTerminalSymbol (symbol : symbol) (cfg : t) : bool = 
	  Set.belongs symbol cfg.alphabet
	;;
	(*checks if var produces the word in grammar cfg
	  and seen are the rules already parsed*)
	let rec prodWord (var : symbol) (word : word) (cfg : t) (seen : rules): bool = 
	  let direct = directDeriv var cfg in 
	  let words = Set.map (fun x -> x.body) direct in 
			Set.belongs word words 
		|| Set.exists (fun x -> not (Set.belongs x seen) 
			&& List.for_all (fun y -> prodWord y word cfg (Set.cons x seen)) x.body) direct
	;; 

	(*checks if var produces the word in grammar cfg*)
	let varProdWord (var : symbol) (word : word) (cfg : t) : bool = 
	  prodWord var word cfg Set.empty
	;;

	(*checks if var produces the empty word in grammar cfg*)
	let prodEpsilon (var : symbol) (cfg : t) : bool =
	  varProdWord var [] cfg 
	;;

	(*generates all possible words by applying the epsilon
	  transformation, if the variable we are analyzing derives epsilon*)
	let rec epsilonProdsCombs (word : word) (cfg : t) : words = 
	  match word with
	  | [] -> Set.make [[]]
	  | hd::tl -> let a = epsilonProdsCombs tl cfg in
				  if prodEpsilon hd cfg then 
					let b = Set.map ( fun x -> hd::x) a in
					if numberOfProdVar hd cfg > 1 then
					  Set.union a b
					else a
				  else
					Set.map (fun x -> hd::x) a
	;;


	(*test*)
	let rec print rules =
	  match rules with
	  | [] -> Format.printf "\n"
	  | hd::tl ->
			Format.printf "{head = %s; body = " (symb2str hd.head); 
			List.iter (fun x -> Format.printf "%s" (symb2str x)) hd.body;
			Format.printf "}\n";
			Format.print_flush ();
			print tl
	;;

	(*for each element x in bodies 
	  add a rule with head leftSide and body x*)
	let rec addNewRules (leftSide : symbol) (bodies : words) (cfg : t) : t =
		Set.match_ bodies
			(fun () -> cfg)
			(fun hd tl ->
				let nCfg = addNewRules leftSide tl cfg in
				  if hd <> [leftSide] then
					addRule {head = leftSide; body = hd} nCfg false
				  else nCfg)
	  ;;

	(*verifies if symb is the cfg grammar start symbol *)
	let isStartSymbol (symb : symbol) (cfg : t) : bool = 
	  symb = cfg.initial
	;;

	(*Eliminate ε-rules of cfgRules
	  and returns a new grammar without ε-rules *)
	  let rec delEpsilonRules (cfgRules: rules) (cfg : t) : t =
		Set.match_ cfgRules
			(fun () -> cfg)
			(fun hd tl ->
				let nCfg = delEpsilonRules tl cfg in
				  let epsilonProd = epsilonProdsCombs hd.body cfg in 
				  let cfgWithRules = addNewRules hd.head epsilonProd nCfg in
				  if isStartSymbol hd.head cfgWithRules then 
					cfgWithRules 
				  else 
					removeRule {head = hd.head; body = []} cfgWithRules)
	;;




	(*DEL*)
	(*Eliminate ε-rules of cfg grammar*)
	let cleanEpsilonRules (cfg : t) : t = 
	  delEpsilonRules cfg.rules cfg 
	;;





	(*------------------------------------------------------------------------------------------------*)

	(*checks if rule derivates only one variable*)
	let isAnUnitProduction (rule : rule) (cfg : t) : bool = 
	  List.length rule.body = 1 && isVariable (List.hd rule.body) cfg
	;;

	let rec addRules (rules : rules ) (cfg : t) : t =
		Set.match_ rules
			(fun () -> cfg)
			(fun hd tl -> addRules tl (addRule hd cfg false))

	(*UNIT*)
	(*let unitFor1 (seen : rules) (rule : rule) (cfg : t) : rules * cfg = 
	  let nCfg = removeRule rule cfg in
	  let direct = directDeriv (List.hd rule.body) nCfg in 
	  let words = List.map (fun x -> x.body) direct in
	  let nW = List.filter( fun x -> not(List.mem {head = rule.head; body = x} seen)) words in
	  let analyzed = List.map( fun x-> {head = rule.head; body = x})nW in
	  (analyzed, addNewRules rule.head nW nCfg)
	;;

	(* Eliminate unit rules and seen
	  are the rules already parsed*)
	let rec processUnitProduction (seen : rules) (cfgRules: rules) (cfg : t) : t = 
	  match cfgRules with
	  | [] -> cfg
	  | hd::tl -> if isAnUnitProduction hd cfg then
					let (a, b) = unitFor1 seen hd cfg in
					processUnitProduction (seen@a) b.rules b
				  else 
					processUnitProduction seen tl cfg
	;;*)
	let unitFor1 (seen : rules) (rule : rule) (cfg : t) : rules  = 
	  let direct = directDeriv (List.hd rule.body) cfg in 
	  let words = Set.map (fun x -> x.body) direct in
	  let nW = Set.filter ( fun x -> not (Set.belongs {head = rule.head; body = x} seen)) words in
	  Set.map ( fun x-> {head = rule.head; body = x}) nW 
	;;

	(* Eliminate unit rules and seen
	  are the rules already parsed*)
	let rec processUnitProduction (seen : rules) (cfgRules: rules) (cfg : t) : t = 
		Set.match_ cfgRules
			(fun () -> cfg)
			(fun hd tl ->
				let nCfg = processUnitProduction seen tl cfg in
				  if isAnUnitProduction hd nCfg then
					let sdnCfg = removeRule hd nCfg in
					let rules = unitFor1 seen hd sdnCfg in
					processUnitProduction (Set.union rules seen) rules (addRules rules sdnCfg)
				  else 
					nCfg)
	;;

	(*UNIT*)  
	(*Eliminate unit rules from cfg grammar*)
	let delUnitProductions (cfgRules: rules) (cfg : t) : t = 
	  processUnitProduction Set.empty cfgRules cfg;;

	(*------------------------------------------------------------------------------------------------*)

	(*checks if the right-hand side of the 
	  rule has one isolated terminal symbol*)
	let isNonSolitaryTerminalsRule (rule : rule) (cfg : t) : bool = 
	  let terminals = List.filter ( fun x -> isTerminalSymbol x cfg) rule.body in
			List.length terminals > 1 
		||  (List.length terminals > 0 && List.length rule.body > 1)
	;;

	(*removes the non solitary terminal symbols from word and
	  add a new rule to cfg grammar for each one
	  and returns a ( new word * new grammar)*)
	let rec addRulesFromNonSolitary (bdy : word) (cfg : t) : word * t = 
	  match bdy with
	  | [] -> (bdy, cfg)
	  | hd::tl -> let (a, b) = addRulesFromNonSolitary tl cfg in
				  if isTerminalSymbol hd b then
					let rule = getRule [hd] b in
					let nCfg = addRule rule b false in
					(rule.head::a, nCfg)
				  else
					(hd::a, b)
	;;

	(*TERM*)
	(*Eliminate rules with nonsolitary terminals*)
	(*let rec delRulesNonSolitaryTerminals (cfgRules: rules) (cfg : t) : t = (*trocar nome*)
	  match cfgRules with
	  | [] -> cfg
	  | hd::tl -> if isNonSolitaryTerminalsRule hd cfg then 
					let (a, b) = cleanNonSolitary hd.body cfg in
					let nCfg = addRule {head = hd.head; body = a} b false in
					delRulesNonSolitaryTerminals tl (removeRule hd nCfg)
				  else
					delRulesNonSolitaryTerminals tl cfg

	;;*)


	let rec processRulesWithNonSolitaryTerminals (cfgRules: rules) (cfg : t) : t = 
		Set.match_ cfgRules
			(fun () -> cfg)
			(fun hd tl ->
				let nCfg = processRulesWithNonSolitaryTerminals tl cfg in
				  if isNonSolitaryTerminalsRule hd nCfg then 
					let (a, b) = addRulesFromNonSolitary hd.body nCfg in
					addRule {head = hd.head; body = a} (removeRule hd b) false 
				  else
					nCfg)
	;;


	(*------------------------------------------------------------------------------------------------*)
	(* checks if the rule has more than 2 
	  non terminal symbols in right-hand side*)
	let hasMoreThan2NonTerminalsInRHS (rule : rule) (cfg : t) : bool = 
		let nonTerminalsInRHS = List.filter ( fun x -> isVariable x cfg) rule.body in
		List.length nonTerminalsInRHS > 2
	;;

	(* split the word when it finds the first variable*)
	let rec splitBodyByVariables (body:word) (cfg : t) : word * word = 
		match body with
		| [] -> ([], [])
		| hd::tl -> let (a, b) = splitBodyByVariables tl cfg in
								if isVariable hd cfg then 
									([hd], tl)
								else
									(hd::a, b)
	;;

	(*let binFor1 (rule : rule) (cfg : t) : t = 
	  let cfgWithoutHd = removeRule rule cfg in 
	  let (a, b) = splitBodyByVariables rule.body cfgWithoutHd in
	  let var = randVar (usedSymbols cfgWithoutHd) in 
	  let nCfg = addRule {head = rule.head; body = a@[var]} cfgWithoutHd false in
	  addRule {head = var; body = b} nCfg false
	;;*)


	let binFor1 (rule : rule) (cfg : t) : rules = 
	  let (a, b) = splitBodyByVariables rule.body cfg in
	  let var = randVar (usedSymbols cfg) in 
		Set.make [{head = rule.head; body = a@[var]}; {head = var; body = b}]
	;;

	let rec processRHSwithMoreThan2NonTerminals (cfgRules: rules) (cfg : t) : t = 
		Set.match_ cfgRules
			(fun () -> cfg)
			(fun hd tl ->
				let nCfg = processRHSwithMoreThan2NonTerminals tl cfg in
				  if hasMoreThan2NonTerminalsInRHS hd nCfg then 
					let cfgWithoutHd = removeRule hd nCfg in 
					let rules = binFor1 hd cfgWithoutHd in
					let sdCfg = addRules rules cfgWithoutHd in
					processRHSwithMoreThan2NonTerminals rules sdCfg
				  else
					nCfg)
	;;

	(*BIN*)
	(*Eliminate right-hand sides with more than 2 nonterminals*)
	(*let rec processRHSwithMoreThan2NonTerminals (cfgRules: rules) (cfg : t) : t = 
	  match cfgRules with
	  | [] -> cfg
	  | hd::tl -> if hasMoreThan2NonTerminalsInRHS hd cfg then 
					let sdCfg = binFor1 hd cfg in
					processRHSwithMoreThan2NonTerminals sdCfg.rules sdCfg
				  else
					processRHSwithMoreThan2NonTerminals tl cfg
	;;*)

	(*let rec delRHSwithMoreThan2NonTerminals (cfgRules: rules) (cfg : t) : t = 
	  match cfgRules with
	  | [] -> cfg
	  | hd::tl -> let nCfg = delRHSwithMoreThan2NonTerminals tl cfg in 
				  if hasMoreThan2NonTerminalsInRHS hd nCfg then 
					binFor1 hd nCfg   // It doesn't work because we need to
									  // analyze the new rules added in binFor1
				  else
					nCfg

				
	;;*)



	(*------------------------------------------------------------------------------------------------*)
	(*Convert cfg grammar to Chomsky normal form*)
	let chomsky (cfg: t) : t =
	  let start = delSFromRHS cfg in
	  let term = processRulesWithNonSolitaryTerminals start.rules start in
	  let bin = processRHSwithMoreThan2NonTerminals term.rules term in 
	  let del = cleanEpsilonRules bin in
	  let unit = delUnitProductions del.rules del in
	  unit 
	;;

	(* IMPERATIVE code - https://www.geeksforgeeks.org/cocke-younger-kasami-cyk-algorithm/ *)
	(* pre: rule is in chomsky form *)
	let prodVars (rule : rule) : bool =
		List.length rule.body = 2

	let cykAccept (cfg: t) (w: word) =
	  if w = [] then
		prodEpsilon cfg.initial cfg
	  else
		let n = List.length w in
		let matrix = Array.make_matrix n n (Set.empty) in
		for j = 0 to (n-1) do
		  let vars = Set.filter(fun x -> List.length x.body = 1 && List.nth x.body 0 = List.nth w j) cfg.rules in
		  let lhs = Set.map ( fun x -> x.head) vars in
		  matrix.(j).(j) <- Set.union matrix.(j).(j) lhs;
		  for i = j downto 0 do 
			for k = i to (j-1) do
			  let vars = Set.filter(fun x -> prodVars x && Set.belongs (List.nth x.body 0) matrix.(i).(k)
											  && Set.belongs (List.nth x.body 1) matrix.(k+1).(j)) cfg.rules in
			  let lhs = Set.map ( fun x -> x.head) vars in
			  matrix.(i).(j) <- Set.union matrix.(i).(j) lhs
			done
		  done
		done; 
		Set.belongs cfg.initial matrix.(0).(n-1)

	let accept (cfg: t) (w: word) =
		cykAccept (chomsky cfg) w

end
