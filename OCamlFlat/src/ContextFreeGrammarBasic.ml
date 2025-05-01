(*
 * ContextFreeGrammarBasic.ml
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
 * jul/2021 (amd) - Improved Learn-OCaml support and error handling.
 * jun/2021 (amd) - Added checks for '~' in the #validate method.
 * may/2021 (amd) - Added support for an extern representation.
 * jan/2021 (amd) - Module in an independent file and some cleanup.
 * feb/2020 (jg) - Main functionalities.
 * dec/2019 (amd) - Initial skeleton, inside the big file "OCamlFlat.ml".
 *)

(*
 * Description: Context-free grammar functionality.
 *
 * TODO: More cleanup.
 *)

open BasicTypes

module ContextFreeGrammarPrivate =
struct
	open ContextFreeGrammarSupport

	(*------Auxiliary functions---------*)

	(* given a head, returns the set of all its bodies according to the cfg's rules *)
	let bodiesOfHead h rl =
		let rls = Set.filter (fun r -> r.head = h) rl in
			Set.map (fun r -> r.body) rls


	(* given 2 sets of words, to each word of the left set, appends each word of the right set *)
	let concatWords lws rws =
		if lws = Set.empty then rws
		else if rws = Set.empty then lws
		else
			let pairs = Set.product lws rws in
				Set.map (fun (x,y) -> x@y) pairs

	(* tests if the number of symbols in the given word exceeds the given lenght *)
	let exceedsMaxLen w l alph =
		let cleanWord = List.filter (fun c -> Set.belongs c alph) w in
			(List.length cleanWord) > l



	let subX h rws rl =
		let bs = bodiesOfHead h rl in
			concatWords bs rws


	(* applies the cfg's rules to the given word *)
	let rec subVar w vs rs =
		match w with
			| [] -> Set.make [[]]
			| x::xs -> if (Set.belongs x vs) then subX x (subVar xs vs rs) rs
				else concatWords (Set.make [[x]]) (subVar xs vs rs)


	(* removes the empty symbol from all non-empty words *)
	let removeEpsi w = List.filter (fun c -> c <> epsilon) w


	(* filters out all words that have variables and cleans any unnecessary epsilon *)
	let cleanNonWords ws vs =
		let hasVar w = List.exists (fun c -> Set.belongs c vs) w in
		let ws = Set.filter (fun w -> not (hasVar w)) ws in
			Set.map (fun w -> removeEpsi w) ws

  let removeEpsilonFromWord w =
    List.filter (fun c -> c <> epsilon) w

  let removeDollarFromWord w =
    List.filter (fun c -> c <> dollar) w

  let rec doWordGenerateEmptyX w seen (rep:t) =
    let doGenerateEmpty x =
      if List.mem x seen
      then false
      else(
		    let bodies = bodiesOfHead x rep.rules in
		    Set.exists (fun b -> doWordGenerateEmptyX b (x::seen) rep) bodies 
		  )
		in      
      List.for_all doGenerateEmpty w

  let doWordGenerateEmpty w (rep:t) =
    doWordGenerateEmptyX (removeDollarFromWord w) [] rep

  let rec firstX testWord seen simple (rep:t) =
    match testWord with
		  | [] -> Set.empty
			| [x] when Set.belongs x rep.variables -> 
					let bodies = bodiesOfHead x rep.rules in
					if Set.belongs x seen 
					  then Set.empty
					  else let result = Set.flatMap ( fun b ->
					          let result = firstX b (Set.add x seen) simple rep in
                    let empty = if b = []
                                then Set.make [epsilon]
                                else Set.empty in
					          Set.union empty result
					        ) bodies
					        in
                  if Set.exists (fun b -> doWordGenerateEmpty b rep) bodies 
                    then Set.union result (Set.make [epsilon])
                    else Set.make (removeEpsilonFromWord (Set.toList result))
			| x::xs when Set.belongs x rep.alphabet -> 
					Set.make [x]
			| x::xs -> Set.union 
		  						(firstX [x] seen simple rep) 
									(if doWordGenerateEmpty [x] rep then firstX xs seen simple rep else Set.empty)  

  let first2 (testWord:word) simple (rep:t) =
    firstX testWord Set.empty simple rep

  let first (testWord:word) simple (rep:t) =
    let first = first2 testWord simple rep in
    if simple then Set.filter (fun c -> c <> epsilon) first else first

	let getFollowRules (testSymbol:symbol) (rep:t) =
	  Set.filter (fun r -> Set.belongs testSymbol (Set.make r.body) ) rep.rules

  let rec getFollowInfo2 testSymbol h b =
    match b with
      | [] -> []
      | x::xs when x = testSymbol -> (h, xs) :: getFollowInfo2 testSymbol h xs
      | x::xs -> getFollowInfo2 testSymbol h xs

  (* given a variable X, returns the pairs (Y,w2) *)
  let getFollowInfo testSymbol rep =
    let rules = Set.toList (getFollowRules testSymbol rep) in
    List.flatten (List.map (fun r -> getFollowInfo2 testSymbol r.head r.body) rules )

    
  let rec followX (testSymbol:symbol) seen simple (rep:t) =
    let pairs = Set.make (getFollowInfo testSymbol rep) in
    let dollar = if testSymbol = rep.initial
                  then Set.make [dollar]
                  else Set.empty
    in
    let set = Set.flatMap (fun (y,w) -> 
          Set.union 
            (Set.filter (fun s -> s <> epsilon) (first w simple rep))
            (if (not (Set.belongs y seen) && doWordGenerateEmpty w rep) 
              then followX y (Set.add testSymbol seen) simple rep
              else Set.empty
            )
    ) pairs 
    in
    Set.union set dollar
    
  let follow2 testSymbol simple rep =
    followX testSymbol (Set.make []) simple rep
  
  let follow testSymbol simple rep =
    let follow = follow2 testSymbol simple rep in
    if simple then Set.filter (fun c -> c <> dollar) follow else follow


  let lookahead rule simple (rep:t) =
    let x = rule.head in
    let w = rule.body in
      Set.filter (
        fun c -> c <> epsilon 
      ) (Set.union (first2 w simple rep) (if doWordGenerateEmpty w rep then follow2 x simple rep else Set.empty))

	(* Make *)
	let validate (name: string) (rep: t): unit =
		(* the alphabet must not contain epsilon ('~') *)
		let isValidAlphabet = not (Set.belongs epsilon rep.alphabet) in
		(* the variables must not contain epsilon ('~') *)
		let isValidVariables = not (Set.belongs epsilon rep.variables) in
		let isIntersectionValid = (Set.inter rep.variables rep.alphabet) = Set.empty in
		let isInitialValid = Set.belongs rep.initial rep.variables in
		let areRuleHeadsValid =
			let hs = Set.map (fun r -> r.head) rep.rules in
				Set.subset hs rep.variables
		in
		let areRuleBodiesValid =
			let allBodySymbols = Set.flatMap (fun r -> Set.make r.body) rep.rules in
			let allValidSymbs = Set.add epsilon (Set.union rep.alphabet rep.variables) in
				Set.subset allBodySymbols allValidSymbs
		in
		if not isValidAlphabet then
			Error.error name
				"The alphabet contains epsilon '~', and it should not" ();
		if not isValidVariables then
			Error.error name
				"The variables contain epsilon '~', and it should not" ();
		if not isIntersectionValid then
			Error.error name
				"The intersection between the alphabet and the variables is not empty" ();
		if not isInitialValid then
			Error.error (symb2str rep.initial)
				"The initial symbol is not a declared variable" ();
		if not areRuleHeadsValid then
			Error.error name
				"Some rule heads are not declared variables" ();
		if not areRuleBodiesValid then
			Error.error name
				"Some rule bodies are not declared symbols" ()
				
	let accept (fe: t) (w: word): bool =
		false (* TODO *)

	let generate (fe: t) (length: int): words =
		Set.empty (* TODO *)

(* ----------------------------------------------------------------------------*)

	(*CODIGO JP*)

	(*checks if symbol var is a cfg grammar variable*)
	let isVariable (var : symbol) (cfg : t) : bool = 
		Set.belongs var cfg.variables
	;;
	
		(*checks if symbol symbol is a terminal symbol*)		
	let isTerminalSymbol (symbol : symbol) (cfg : t) : bool = 
		Set.belongs symbol cfg.alphabet
	;;

	let isTerminalSymbol2 (symbol: symbol) : bool =
		not ("A" <= (symb2str symbol) && (symb2str symbol) <= "Z" )

	let hasEmpty body =
		body = [epsilon]

	let rec expandsEmpty sym cfg =
		let xRules = Set.filter(fun r -> r.head = sym) cfg.rules in
		let xBodies = Set.map (fun r -> r.body) (Set.filter (fun r -> List.length r.body == 1) xRules) in
		Set.for_all(fun b -> hasEmpty b || List.for_all (fun sy -> expandsEmpty sy cfg && isVariable sy cfg) b) xBodies
				
	let rec calcSymExpansions cfg sym seen =
		let xRules = Set.filter(fun r -> r.head == sym) cfg.rules in
		let xBodies = Set.toList (Set.map (fun r -> r.body) xRules) in
		let rec minBody bodies min seen =
			match bodies with
			| [] -> (min, seen)
			| ba :: bb -> 
				let terminalLength = List.length (List.filter (fun sy -> isTerminalSymbol sy cfg) ba) in
				let nonTerms = List.filter (fun sy -> isVariable sy cfg && sy != sym) ba in
				let sameSymLength = List.length (List.filter (fun sy -> sy == sym) ba) in
				let rec expandNonTerms terms seen =
					match terms with
					| [] -> (0, seen)
					| sa :: sb ->
						if (Set.exists(fun (sy, value) -> sy == sa) seen)
							then
						let (_, kValue) = Set.find(fun (sy, value) -> sy == sa) seen in
							let (value, newSeen) = expandNonTerms sb seen in
							(kValue + value, newSeen)
						else (
							let (_, saValue, newSymSeen) = calcSymExpansions cfg sa seen in
							let newSymSeen2 = Set.add (sa, saValue) newSymSeen in
							let (ntValue, newNonTermSeen) = expandNonTerms sb newSymSeen2 in
							let unionSeen = Set.unionUnsafe newSymSeen2 newNonTermSeen in
							(saValue + ntValue, unionSeen)
						)					
				in
				let (value, newSeen) = expandNonTerms nonTerms seen in
				if (sameSymLength != 0) then
					let (minVal, newSeen) = minBody bb min seen in
					if (minVal < min) then
						let bodyLength = terminalLength + value + (sameSymLength * minVal) in
						if (bodyLength < min) then
							let (minVal2, newSeen) = minBody bb bodyLength seen in
								(minVal2, newSeen)
						else (
							let (minVal, newSeen) = minBody bb min seen in
								(minVal, newSeen)
						)
					else (
						let (minVal2, newSeen) = minBody bb min seen in
						(minVal2, newSeen)
					)
				else(
					let bodyLength = terminalLength + value in
					if (bodyLength < min) then
						let (minVal, newSeen) = minBody bb bodyLength seen in
							(minVal, newSeen)
					else (
						let (minVal, newSeen) = minBody bb min seen in
							(minVal, newSeen)
					)
				)
				
			in
			let (minValue, newSeen) = minBody xBodies (Int.max_int) seen in
			(sym, minValue, newSeen)


	let calcExpans cfg =
		let vars = Set.toList (cfg.variables) in
		let seen = Set.make ([]) in
		let rec buildPairs vars seen =
			match vars with
			| [] -> []
			| va :: vb -> 
				if not (Set.exists(fun (sy, value) -> sy == va) seen)
					then
						let (_, minValue, newSeen) = calcSymExpansions cfg va seen in
						let newSeen2 = Set.add (va, minValue) newSeen in 
						(va, minValue) :: buildPairs vb newSeen2
				else (
					let pair = Set.find(fun (sy, value) -> sy == va) seen in
					pair :: buildPairs vb seen
					)
		in
		buildPairs vars seen
	
	let verifyLength2 cfg sf body len pairs =
		let terminalLengthSf = List.length (List.filter(fun sy -> isTerminalSymbol sy cfg) sf) in
		let terminalLengthBody = List.length (List.filter(fun sy -> isTerminalSymbol sy cfg) body) in
		let rec sumMinExpansions syms =
			match syms with
			| [] -> 0
			| sa :: sb ->
				let (_, value) = List.find(fun (sy, value) -> sy == sa) pairs in
				value + sumMinExpansions sb
		in
		let sfVars = List.filter(fun sy -> isVariable sy cfg) sf in 
		let bodyVars = List.filter(fun sy -> isVariable sy cfg) body in
		terminalLengthSf + terminalLengthBody + (sumMinExpansions sfVars) + (sumMinExpansions bodyVars) - 1 <= len
	

	let verifyLength cfg sf body len =
		let lengthSf = List.length (sf) in
		let lengthBody = List.length (body) in
		let sfVars = List.length (List.filter(fun sy -> isVariable sy cfg && expandsEmpty sy cfg) sf) in 
		let bodyVars = List.length (List.filter(fun sy -> isVariable sy cfg && expandsEmpty sy cfg) body) in
		lengthSf + lengthBody - sfVars - bodyVars - 1 <= len


		(*
			4
			2 -> 5
			2 -> 4	 
		*)

	let initialConfig (cfg: t) (w: word) : configurations =
		Set.make [([cfg.initial], w)]


	let rec expand (cfg: t) (sf,w) : configurations =
		match sf with
			| [] -> Set.make [([],w)]
			| x::xs ->
				let ySet = expand cfg (xs, w) in
					if isTerminalSymbol x cfg then
						Set.map (fun (fs, w) -> (x::fs, w)) ySet
					else
						let xRules = Set.filter(fun r -> r.head = x) cfg.rules in
						let xBodies = Set.map (fun r -> r.body) xRules in
						let res = Set.flatMap (fun (fs1, w) -> Set.map (fun fs2 -> (fs2@fs1, w)) xBodies) ySet in
						res

	let rec expandGenerate (cfg: t) (len: int) (sf,w) : configurations =
		match sf with
			| [] -> Set.make [([],[])]
			| x::xs ->
				let ySet = expandGenerate cfg len (xs, w) in
					if isTerminalSymbol x cfg then
						Set.map (fun (fs, w) -> (x :: fs, w)) ySet
					else
						let xRules = Set.filter(fun r -> r.head = x) cfg.rules in
						let xBodies = Set.map (fun r -> r.body) (Set.filter(fun r -> hasEmpty r.body || verifyLength cfg sf r.body len) xRules) in
						let res = Set.flatMap (fun (fs1, w) -> Set.map (fun fs2 -> (fs2@fs1, w)) xBodies) ySet in
						res
				
		(* 0P1, 0P1*)
		(* *)


	let nextConfigs (cfg: t) (sf, w) : configurations =
		Util.show("Starting nextConfigs for: "^word2str sf);
		let res = expand cfg (sf,w) in
			Set.iter(fun (sf, w) -> Util.show("[" ^ word2str sf ^ "," ^ word2str w ^ "]")) res;
			res

	let nextConfigs2 (cfg: t) (len: int) (sf, w) : configurations =
		Util.show("Starting nextConfigs for: "^word2str sf);
		let res = expandGenerate cfg len (sf,w) in
			Set.iter(fun (sf, w) -> Util.show("[" ^ word2str sf ^ "," ^ word2str w ^ "]")) res;
			res

		

	let isAcceptingConfig (cfg: t) (rl, w) : bool =
		rl = w

	
	let accept (cfg: t) (w: word) : bool =
			Model.accept cfg w initialConfig nextConfigs isAcceptingConfig
		
	let acceptFull (cfg: t) (w: word) : bool * path * trail =
			Model.acceptFull cfg w initialConfig nextConfigs isAcceptingConfig
	
	let isAcceptingConfig2 (cfg: t) (sf, w) : bool =
		List.for_all(fun sym -> isTerminalSymbol sym cfg) sf
	
	

	let getWord (sf, _) = List.filter (fun symb -> isTerminalSymbol2 symb) sf

	let generate (cfg: t) (len: int) : words =
		
		Model.generate cfg len initialConfig nextConfigs2 isAcceptingConfig2 getWord


(* ----------------------------------------------------------------------------*)



end

module ContextFreeGrammarBasic =
struct
	include ContextFreeGrammarSupport
	open ContextFreeGrammarPrivate

	(* Make *)
	let make2 (arg: t Arg.alternatives): Entity.t * t = make2 arg validate
	let make (arg: t Arg.alternatives): t = make arg validate

	(* Exercices support *)
	let checkProperty (re: t) (prop: string) =
		match prop with
		| "regular" -> false (* TODO self#isRegular *)
		| "context free grammar" -> true
		| _ -> Model.checkProperty prop
	let checkExercise ex re = Model.checkExercise ex (accept re) (checkProperty re)	
	let checkExerciseFailures ex re = Model.checkExerciseFailures ex (accept re) (checkProperty re)	

	(* Ops *)
	let lookahead = lookahead
	let follow = follow
	let first = first
	let accept = accept
	let generate = generate	

	class model (arg: t Arg.alternatives) =
		object(self) inherit Model.model (make2 arg) as super
			val mutable simplified = false
		(* Representation *)
			method representation = representation
		(* Kind *)
			method isContextGrammar : bool = true
			method isContextFreeGrammar : bool = true
		(* Show *)			
			method toJSon: JSon.t = toJSon representation
			method toJSon2: JSon.t = toJSon2 id representation
			method show: unit = show representation
			method show2: unit = show2 id representation
		(* Ops *)
			(* This method checks if the grammar is regular
			*
			* @returns bool -> true if regular, false otherwise
			*)
			method isRegular : bool =

				let vs = representation.variables in
				let alp = representation.alphabet in

				let bs = Set.map (fun r -> r.body) representation.rules in

				let isRightLinear bs =
					let isRightLinearX b =
						match b with
							| [a] -> (Set.belongs a alp) || a = epsilon
							| [a; v] -> (Set.belongs a alp) && (Set.belongs v vs)
							| _ -> false
					in
						Set.for_all (fun b -> isRightLinearX b) bs
				in

				let isLeftLinear bs =
					let isLeftLinearX b =
						match b with
							| [a] -> (Set.belongs a alp) || a = epsilon
							| [v; a] -> (Set.belongs v vs) && (Set.belongs a alp)
							| _ -> false
					in
						Set.for_all (fun b -> isLeftLinearX b) bs
				in
					isRightLinear bs || isLeftLinear bs


      method first testWord = first testWord simplified self#representation
      method follow testSymbol = follow testSymbol simplified self#representation
      method lookahead rule = lookahead rule simplified self#representation

			(* This method checks if the given word is accepted by the grammar
			*
			* @param testWord -> word to be tested
			*
			* @returns bool -> true if it accepts the word, false otherwise
			*)


			method accept (testWord:word) : bool =
				ChomskyNormalForm.accept (self#representation) testWord

				method acceptFull (w: word) : bool * path * trail = acceptFull representation w
				
			method private acceptXXX (testWord:word) : bool =

				(* any word with a symbol not from the cfg alphabet will not be accepted
				if not (Set.subset (Set.make testWord) representation.alphabet) then false else
				*)

				let vs = representation.variables in


				(* for word wa, get subword to the left of its first variable *)
				let rec getPrefix wa =
					match wa with
						| [] -> []
						| x::xs -> if Set.belongs x vs then [] else x::(getPrefix xs)
				in

				(* for word wa, get subword to the rigth of its last variable *)
				let getSuffix wa =
					let rec getSuffixX wa sfx =
						match wa with
							| [] -> sfx
							| x::xs -> let auxSfx = sfx@[x] in
										if Set.belongs x vs then getSuffixX xs []
											else getSuffixX xs auxSfx
					in
						getSuffixX wa []
				in

				let rec firstNElements w n =
					match w with
						| [] -> []
						| x::xs -> if n > 0 then x::(firstNElements xs (n-1)) else []
				in

				let rec lastNElements w n =
					match w with
						| [] -> []
						| x::xs -> if n < (List.length w) then lastNElements xs n else w
				in

				(* a word can be discarded if its prefix does not match the leftmostmost part of word w *)
				let keepByPrefix genW testW =
					let pgw = getPrefix genW in
					let ptw = firstNElements testW (List.length pgw) in
						pgw = [] || pgw = ptw
				in


				(* a word can be discarded if its suffix does not match the rightmost part of word w *)
				let keepBySufix genW testW =
					let sgw = getSuffix genW in
					let stw = lastNElements testW (List.length sgw) in
						sgw = [] || sgw = stw
				in

				(* the word inst discarded only if it cant be discarded by neither its prefix nor its suffix *)
				let toKeep w tw = (w = [] && tw = []) || (keepByPrefix w tw && keepBySufix w tw) in


				let alph = representation.alphabet in
				let vs = representation.variables in
				let rs = representation.rules in
				let l = List.length testWord in

				let nextGeneration ws =
					let subsWs = Set.flatMap (fun w -> subVar w vs rs) ws in
					let rws = Set.filter (fun w -> not (exceedsMaxLen w l alph)) subsWs in
					let rws = Set.map (fun w -> removeEpsi w) rws in
						Set.filter (fun w -> toKeep w testWord ) rws

				in

				let start = Set.make [[representation.initial]] in

				let res = Set.historicalFixedPoint nextGeneration start in
					Set.exists (fun x -> x = testWord ) res




			method acceptWithTracing (testWord:word) =



				let vs = representation.variables in


				(* for word wa, get subword to the left of its first variable *)
				let rec getPrefix wa =
					match wa with
						| [] -> []
						| x::xs -> if Set.belongs x vs then [] else x::(getPrefix xs)
				in

				(* for word wa, get subword to the rigth of its last variable *)
				let getSuffix wa =
					let rec getSuffixX wa sfx =
						match wa with
							| [] -> sfx
							| x::xs -> let auxSfx = sfx@[x] in
										if Set.belongs x vs then getSuffixX xs []
											else getSuffixX xs auxSfx
					in
						getSuffixX wa []
				in

				let rec firstNElements w n =
					match w with
						| [] -> []
						| x::xs -> if n > 0 then x::(firstNElements xs (n-1)) else []
				in

				let rec lastNElements w n =
					match w with
						| [] -> []
						| x::xs -> if n < (List.length w) then lastNElements xs n else w
				in

				(* a word can be discarded if its prefix does not match the leftmostmost part of word w *)
				let keepByPrefix genW testW =
					let pgw = getPrefix genW in
					let ptw = firstNElements testW (List.length pgw) in
						pgw = [] || pgw = ptw
				in


				(* a word can be discarded if its suffix does not match the rightmost part of word w *)
				let keepBySufix genW testW =
					let sgw = getSuffix genW in
					let stw = lastNElements testW (List.length sgw) in
						sgw = [] || sgw = stw
				in

				(* the word inst discarded only if it cant be discarded by neither its prefix nor its suffix *)
				let toKeep w tw = (w = [] && tw = []) || (keepByPrefix w tw && keepBySufix w tw) in


				let alph = representation.alphabet in
				let vs = representation.variables in
				let rs = representation.rules in
				let l = List.length testWord in

				let nextGeneration ws =
					let subsWs = Set.flatMap (fun w -> subVar w vs rs) ws in
					let rws = Set.filter (fun w -> not (exceedsMaxLen w l alph)) subsWs in
					let rws = Set.map (fun w -> removeEpsi w) rws in
						Set.filter (fun w -> toKeep w testWord ) rws

				in

				let start = Set.make [[representation.initial]] in

				let res = Set.historicalFixedPointTracing nextGeneration start in


				let trimRes l =
					match l with
					| [] -> []
					| x::xs -> if Set.belongs testWord x then xs
								else l
				in

				let res2 = List.rev (trimRes (List.rev res)) in


				let printWset ws =
					Util.print ["["];
					Set.iter (fun w -> Util.print [word2str w; ";"]) ws;
					Util.println ["]"];
				in

					List.iter (fun ws -> printWset ws) res2




			(* This method generates all words up the the given lenght that belong to the grammars language
			*
			* @ param lenght -> the max lenght of generated words
			*
			* @returns words -> the set of generated words
			*)
			method generate (length:int) : words =

				let alph = representation.alphabet in
				let vs = representation.variables in
				let rs = representation.rules in


				let nextGeneration ws =
					let subsWs = Set.flatMap (fun w -> subVar w vs rs) ws in
						Set.filter (fun w -> not (exceedsMaxLen w length alph)) subsWs
				in

				let start = Set.make [[representation.initial]] in

				let res = Set.historicalFixedPoint nextGeneration start in

					cleanNonWords res vs

		(* Exercices support *)
			method checkProperty (prop: string) = checkProperty representation prop

		(* Learn-OCaml support *)
			method moduleName = moduleName
			method xTypeName = xTypeName
			method xTypeDeclString : string = prelude
			method toDisplayString (name: string): string = solution name self#representation
			method example : JSon.t = example
		end
end

module ContextFreeGrammarTop =
struct
	open ContextFreeGrammarBasic
	open ContextFreeGrammarBasicsX

	let cfgI cfg = internalize cfg
	let cfgX cfg = externalize cfg
	
	let cfg_load file = cfgX (make (Arg.File file))
	let cfg_text text = cfgX (make (Arg.Text text))
	let cfg_json json = cfgX (make (Arg.JSon json))
	let cfg_predef name = cfg_text (Examples.example name)

(*	let confX (s, w) = (state2str s, word2str w)
	let pathX (p: path) = pathX confX p
	let trailX (t: trail) = trailX confX t *)
	
	let stats () = RuntimeControl.stats ()

	let cfg_accept cfg w = accept (cfgI cfg) (wordI w)

(*
	let cfg_path cfg w =
		let (r,p,t) = acceptFull (cfgI cfg) (wordI w) in
			pathX p

	let cfg_trail cfg w =
		let (r,p,t) = acceptFull (cfgI cfg) (wordI w) in
			trailX t
		*)

	let cfg_generate cfg len = wordsX (generate (cfgI cfg) len)
end

open ContextFreeGrammarTop

     (* Adds a sufix to a variable name name *)
     let addSufixCFG (v: symbol)(sufix: string): symbol =
       str2symb((symb2str v)^"_"^sufix)


(* addSufix a que? *)
    let addSufixList  body sufix =
        List.map(fun s -> addSufixCFG  s sufix) body

       (* Renames all the variables in one gramatic adding a sufix *)	
     let renameVariablesCFG (cfg: ContextFreeGrammarBasic.t) (sufix: string): ContextFreeGrammarBasic.t =
       let open ContextFreeGrammarBasic in 
       {alphabet = cfg.alphabet;
       variables =	Set.map (fun v -> addSufixCFG v sufix) cfg.variables;
       initial = addSufixCFG cfg.initial sufix;
       rules = Set.map (fun {head= h;body = b} -> {head=(addSufixCFG h sufix);body= addSufixList b sufix}) cfg.rules
       }


(*

--------------------

let cfg_balanced = {| {
		kind : "context free grammar",
		description : "CFG: Language of balanced square bracket parentheses",
		name : "cfg_balanced",
		alphabet : ["[", "]"],
		variables : ["<Start>"],
		initial : "<Start>",
		rules : [ "<Start> -> [<Start>] | <Start><Start> | ~"]
	} |};;

let cfg = cfg_text cfg_balanced;;

let cfg2 = cfgX cfg;;





















let cfg2 = renameVariablesCFG (cfgI cfg) "ola";;





let cfg = cfg_predef "cfg_simple";;

let cfg2 = renameVariablesCFG (cfgI cfg) "ola";;



let cfg2 = cfgX (renameVariablesCFG (cfgI cfg) "ola");;

fa_generate fa 8;;

fa_accept fa "aaaa";;
fa_accept fa "aaaca";;

fa_path fa "aaaa";;
fa_path fa "aaaca";;

fa_trail fa "aaaa";;
--------------------

#print_depth 10000;;
#print_length 10000;;




--------------------
let fa = fa_predef "dfa_astar";;

fa_generate fa 8;;

fa_accept fa "aaaa";;
fa_accept fa "aaaca";;

fa_path fa "aaaa";;
fa_path fa "aaaca";;

fa_trail fa "aaaa";;
--------------------

#print_depth 10000;;
#print_length 10000;;



let fa_astar = {| {
		kind : "finite automaton2",
		description : "this is an example",
		name : "dfa_astar",
		alphabet: ["a"],
		states : ["START", "Z1"],
		initialState : "START",
		transitions : [
			["START", "a", "START"],
			["START", "~", "START"],			
			["START", "~", "Z"],			
			["Z", "a", "Z"],
			["START", "a", "Z"]
		],
		acceptStates : ["START", "Z"]
		} |}
;;
let fa = fa_text fa_astar;;

let fa_astar = {| {
		kind : "finite automaton2",
		description : "this is an example",
		name : "dfa_astar",
		alphabet: ["a"],
		states : ["START", "Z1"],
		initialState : "START",
		transitions : [
			["START", "a", "START"],
			["START", "~", "START"],			
			["START", "~", "Z"],			
			["Z", "a", "Z"],
			["START", "a", "Z"]
		],
		acceptStates : ["START", "Z"]
		} |}
;;
let fa = fa_text fa_astar;;

*)
