#ifdef ALL

open BasicTypes
open ContextFreeGrammarBasic  

module ContextFreeGrammarLL1 =
struct
  open RDParserC
  open RDParserOCaml
  open RDParserJava
   
  type syntaxTable = { term : symbol option; var : symbol option; rBody : word option }
  type acceptTable = { input : string; stack: string; production: string }
  type recognized = { recog : string; left : string }
	type acceptStep = {
    syntaxTable : syntaxTable;
    acceptedString: string;
    acceptTable : acceptTable;
    recognized : recognized;
    accepted: bool option;
    nodes: cfgTree list
  }
  
  let bodiesOfHead = RDParser.bodiesOfHead
  
  let leftRecursionRemovalTransform = "Remove left recursion"
  let leftFactoringTransform = "Left factoring"
  let cleanProductiveTransform = "Clean unproductive symbols"
  let cleanAccessibleTransform = "Clean inaccessible symbols"
  let unitRemovalTransform = "Unit productions removal"
  let epsilonRemovalTransform = "Epsilon productions removal"
  let ll1Transform = "LL1 transformation"
  
  type transformation = { tType : string; grammar : ContextFreeGrammarBasic.model }
  
  let newStep ?(term = None) ?(var = None) ?(rBody = None)
              ?(acceptedString = "") 
              ?(input = "") ?(stack = "") ?(production = "") 
              ?(recog = "") ?(left = "") 
              ?(accepted = None) ?(nodes = []) simple =
    (* let dollar = String.make 1 dollar in
    let input = if simple then input else input ^ dollar in
    let stack = if simple then stack else stack ^ dollar in *)
    {
      syntaxTable = {term; var; rBody};
      acceptedString = acceptedString;
      acceptTable = {input; stack; production};
      recognized = {recog; left};
      accepted = accepted;
      nodes = nodes
    }
    
  
  (*type rule = CFGSyntax.rule*)
  

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

  let removeEpsilonFromWord w =
    List.filter (fun c -> c <> epsilon) w

  let removeDollarFromWord w =
    List.filter (fun c -> c <> dollar) w

  let doWordGenerateEmpty w (rep:t) =
    doWordGenerateEmptyX (removeDollarFromWord w) [] rep
    
  let printRepresentation (rep:t) =
    Printf.printf "Alphabet = "; Util.printAlphabet rep.alphabet;
    Printf.printf "Variables = "; Util.printAlphabet rep.variables;
    Printf.printf "Initial = %s\n" (symb2str rep.initial);
    Printf.printf "Rules {\n"; Set.iter (fun {head=h; body=b} -> Printf.printf "\t%s -> %s\n" (symb2str h) (word2str b)) rep.rules;
    Printf.printf "}\n\n"

  let rec print_tuples = (*TEST*)
    function
    | [] -> ()
    | (a, b) :: rest ->
      Printf.printf "%c -> " a;
      Util.printAlphabet b;
      print_tuples rest
      
  let rec print_list = (*TEST*)
    function
    | [] -> Printf.printf "";
    | x::xs ->
      Printf.printf "%c" x;
      print_list xs  
  
  (*Given a variable, returns all rules with variable as head*)
  let sameHeadRules (testSymbol:symbol) (rep:t) =
	  Set.toList (Set.filter (fun r -> testSymbol = r.head) rep.rules)

  let rec pairs l =
    match l with
      | [] -> []
      | x::xs -> List.map (fun v -> (x,v)) xs :: pairs xs

  (*Given a word and variable, returns the word behind the variable*)
  let rec behindSymbol (word:word) (var:variable) = 
    match word with
    | [] -> []
    | x::xs -> if x <> var then x::behindSymbol xs var else []


  let rec leftRecursionTest initial (seen: variables) (rep:t) =
    if Set.belongs initial rep.alphabet then false else (*rule starting with a terminal symbol can't be left recursive*)
      let ruleBodies = Set.toList (bodiesOfHead initial rep.rules) in (* example: rulesBodies = [['B';'a']; ['b']*)
(*        Printf.printf "initial = %c\n" initial;*)
      let leftRecursionTest2 head body seen (rep:t) =
        let wordBehind = behindSymbol body head in
        let behindGenerateEmpty = doWordGenerateEmpty wordBehind rep in
        let body = if behindGenerateEmpty 
                     then List.filter (fun x -> not (List.mem x wordBehind)) body 
                     else body
        in
        
        match body with
        | [] -> false
        | x::xs when x = head || Set.belongs x seen -> true
        | x::xs -> leftRecursionTest x (Set.cons x seen) rep in
        
      List.exists (fun x -> x = true) (List.map (fun x -> leftRecursionTest2 initial x seen rep) ruleBodies)

      
  let isLeftRecursive (rep:t) = 
    Set.exists (fun x -> x = true) (Set.map (fun v -> leftRecursionTest v Set.empty rep) rep.variables)

  let isLL1Deterministic simple (rep:t) =
    let variables = rep.variables in
    let pairsSet = Set.map (fun v -> Set.make (List.flatten (pairs (sameHeadRules v rep)))) variables in
    let lookaheadInterSet = Set.flatMap (fun v -> Set.map (fun (p1,p2) -> Set.inter (lookahead p1 simple rep) (lookahead p2 simple rep)) v) pairsSet in
      Set.for_all (fun x -> Set.size x = 0) lookaheadInterSet

  let isLL1 simple (rep:t) = 
    isLL1Deterministic simple rep
  
  (*given a production X->a, does lookahead(X->a), b, and returns pair ((X,b),a)*)
  let lookahead2Tuple rule simple (rep:t) =
    let lookahead = lookahead rule simple rep in 
      Set.map (fun l -> ((rule.head, l), rule.body)) lookahead
  
  let createParsingTable simple (rep:t) = 
    let lookaheadSet = Set.flatMap (fun r -> lookahead2Tuple r simple rep) rep.rules in
      lookaheadSet
  
  let hasParsingTableConflict simple (rep:t) =
    let parsingTable = createParsingTable simple rep in
    let repeatsTbl = Hashtbl.create (Set.size parsingTable) in
    let getRepeatNum c repeatsTbl =
      let repeat = Hashtbl.find_opt repeatsTbl c in
      match repeat with
      | None -> Hashtbl.add repeatsTbl c 1; false
      | Some a -> true
    in
    let boolResults = Set.map (fun ( (v,t), _ ) -> getRepeatNum (v,t) repeatsTbl ) parsingTable in
    Set.exists (fun r -> r) boolResults
    
  
  (*accept*)
  
(*  let printParsingInfo entry stack sub isSub =*)
(*    Printf.printf "\t"; print_list entry;*)
(*    Printf.printf "\t"; print_list stack;*)
(*    if isSub*)
(*      then (Printf.printf "\t%c->" (List.nth stack 0); print_list sub;)*)
(*      else Printf.printf "\t";*)
(*    Printf.printf "\n"*)
(*  *)
(*  (*given the entry, stack and parsingTable, rewrites the leftmost*)*)
(*  (*variable on the stack with its respective parsingTable rule*)*)
(*  let ruleRewrite (entry:word) (stack:word) parsingTable =*)
(*    let entryChar = List.nth entry 0 in*)
(*    let stackChar = List.nth stack 0 in*)
(*    let parsingTableList = Set.toList parsingTable in*)
(*    let substitution = List.assoc (stackChar, entryChar) parsingTableList in*)
(*      match stack with*)
(*      | [] -> []*)
(*      | x::xs ->*)
(*                printParsingInfo entry stack substitution true;*)
(*                substitution@xs*)
(*  *)
(*  let rec acceptX entry stack parsingTable (rep:t) =*)
(*    match entry with*)
(*    | [] -> if doWordGenerateEmpty stack rep then true else false*)
(*    | x::xs -> match stack with*)
(*                | [] -> false*)
(*                | x2::xs2 -> if Set.belongs x2 rep.variables*)
(*                             then*)
(*                                let newStack = ruleRewrite entry stack parsingTable in*)
(*                                acceptX entry newStack parsingTable rep*)
(*                             else if x=x2 *)
(*                                  then (printParsingInfo entry stack [] false;*)
(*                                       acceptX xs xs2 parsingTable rep )*)
(*                                  else false*)
(*  *)
(*  let acceptZ word rep = *)
(*    Printf.printf "\t"; Printf.printf "Entry: ";*)
(*    Printf.printf "\t"; Printf.printf "Stack: ";*)
(*    Printf.printf "\t"; Printf.printf "Rule: \n";*)
(*    let parsingTable = createParsingTable rep in*)
(*      try (acceptX word [rep.initial] parsingTable rep) *)
(*        with Not_found -> Printf.printf "\t\t\tApplicable rule not found!\n"; false*)

  let word2tree w (rep:t) =
    let rec word2tree2 w =
    match w with
    | [] -> []
    | x::xs -> (if Set.belongs x rep.alphabet
                then Leaf x
                else Root(x,[]))
                :: word2tree2 xs
    in
    
    if List.length w = 0
    then [Leaf epsilon]
    else word2tree2 w

  let rec acceptX entry stack parsingTable (currPerm:symbol list) simple (rep:t) =
    match entry with
    | [] -> [] (*Not supposed to happen*)
    | x::xs when x = dollar ->
          (match stack with
          | [] -> [] (*Not supposed to happen*)
          | x::xs -> if doWordGenerateEmpty [x] rep
                      then
                        (
                          if x = dollar
                          then [newStep ~acceptedString:(word2str currPerm)
                               ~input:(word2str entry)
                               ~stack:(word2str stack)
                               ~recog:(word2str (currPerm))
                               ~accepted:(Some true)
                                simple]
                          else (newStep ~var:(Some (List.hd stack))
                              ~term:(Some dollar)
                              ~rBody:(Some [])
                              ~acceptedString:(word2str currPerm)
                              ~input:(word2str entry)
                              ~stack:(word2str stack) 
                              ~production:(symb2str (List.hd stack) ^ " -> " ^ "") 
                              ~recog:(word2str currPerm)
                              ~nodes:(word2tree [] rep)
                              simple) :: acceptX entry xs parsingTable currPerm simple rep
                        )
                      else [newStep ~var:(Some (List.hd stack))
                      ~term:(Some dollar)
                      ~rBody:(Some [])
                      ~acceptedString:(word2str currPerm) 
                      ~input:(word2str entry)
                      ~stack:(word2str stack)
                      ~recog:(word2str currPerm) ~left:(word2str (removeDollarFromWord stack))
                      ~accepted:(Some false)
                      simple]
             )
    | x::xs -> match stack with
                | [] -> [] (*Not supposed to happen*)
                | [epsilon] -> [newStep ~acceptedString:(word2str currPerm)
                                ~input:(word2str entry)
                                ~stack:(word2str stack)
                                ~recog:(word2str currPerm) ~left:(word2str (removeDollarFromWord stack))
                                ~accepted:(Some false)
                                simple]
                | x2::xs2 -> if Set.belongs x2 rep.variables
                             then
                                let entryChar = List.nth entry 0 in
                                let stackChar = List.nth stack 0 in
                                let parsingTableList = Set.toList parsingTable in
                                let substitution = List.assoc_opt (stackChar, entryChar) parsingTableList in
                                match substitution with
                                  | None -> [newStep ~term:(Some entryChar) ~var:(Some stackChar)
                                                     ~acceptedString:(word2str currPerm)
                                                     ~input:(word2str entry) ~stack:(word2str stack)
                                                     ~recog:(word2str currPerm) ~left:(word2str (removeDollarFromWord stack))
                                                     ~accepted:(Some false)
                                                     simple]
                                  | Some s -> let newStack = 
                                                match stack with
                                                | [] -> []
                                                | x::xs -> s@xs 
                                              in
                                              (newStep ~term:(Some entryChar) ~var:(Some stackChar) ~rBody:(Some s)
                                                       ~acceptedString:(word2str currPerm)
                                                       ~input:(word2str entry) ~stack:(word2str stack) ~production:(symb2str (List.nth stack 0) ^ " -> " ^ word2str s)
                                                       ~recog:(word2str currPerm) ~left:(word2str (removeDollarFromWord stack))
                                                       ~nodes:(word2tree s rep)
                                                       simple) :: acceptX entry newStack parsingTable currPerm simple rep
                              else if x=x2 
                                  then
                                    let newCurrPerm = currPerm @ [x] in
                                    (newStep ~acceptedString:(word2str newCurrPerm)
                                             ~input:(word2str entry) ~stack:(word2str stack)
                                             ~recog:(word2str newCurrPerm) ~left:(word2str (List.tl (removeDollarFromWord stack)))
                                             simple) :: acceptX xs xs2 parsingTable newCurrPerm simple rep 
                                  else [newStep ~acceptedString:(word2str currPerm)
                                                ~input:(word2str entry) ~stack:(word2str stack) 
                                                ~recog:(word2str currPerm) ~left:(word2str (removeDollarFromWord stack))
                                                ~accepted:(Some false)
                                                simple]
  
  let acceptZ word simple (rep:t) = 
    let word = word @ [dollar] in
    let initial = [rep.initial] @ [dollar] in
    let parsingTable = createParsingTable simple rep in
      (newStep ~input:(word2str word) ~stack:(word2str initial) ~nodes:[Root(rep.initial,[])] simple)
      ::acceptX word initial parsingTable [] simple rep

  let rec acumFixedPoint (f: 'a set -> 'a set) (x: 'a set): 'a set =
    let next = Set.union x (f x) in
      if x = next then x
      else acumFixedPoint f next
  
  (*productive symbols*)
  
  (*given a rule and a set of productive variables, verifies if given*)
  (*rule is productive*)
  let isRuleProductive r prodVars (rep:t) =
(*    Printf.printf "\t\t\tisRuleProductive - Prod = %s   prodVars = %s\n" (word2str r) (word2str (Set.toList prodVars));*)
    List.for_all (fun c -> Set.belongs c rep.alphabet || Set.belongs c prodVars) r
      
  (*given a variable and a set of productive variables, verifies if given *)
  (*variable is productive*)
  let isSymbolProductive h prodVars (rep:t) =
    let rules = bodiesOfHead h rep.rules in
      Set.exists (fun r -> 
(*                          Printf.printf "\t\tProduction = %c -> %s\n" h (word2str r);*)
                          isRuleProductive r prodVars rep
                  ) rules
      
        
  let productiveSymbolsFP (rep:t) varP =
    Set.filter (fun v -> (*Printf.printf "\tVar %c\n" v;*) isSymbolProductive v varP rep) (Set.diff rep.variables varP)
  
  (*show the productive symbols of the current grammar*)
  let productiveSymbols (rep:t) =
    acumFixedPoint (productiveSymbolsFP rep) Set.empty
  
  (*show the simplified grammar with only productive symbols*)
  (*TODO Confirm correct new model*)
  let productiveGrammarRewrite (rep:t) =
    let prodSyms = productiveSymbols rep in
(*    Printf.printf "Productive Symbols:\n";*)
(*    Set.iter (fun s -> Printf.printf "\t%c\n" s) prodSyms;*)
(*    Printf.printf "\n";*)
    let unprodSyms = Set.diff rep.variables prodSyms in
(*    Printf.printf "Unproductive Symbols:\n";*)
(*    Set.iter (fun s -> Printf.printf "\t%c\n" s) unprodSyms;*)
(*    Printf.printf "\n";*)
    let newRules = Set.filter (fun r -> Set.belongs r.head prodSyms && List.for_all (fun c -> not (Set.belongs c unprodSyms)) r.body) rep.rules in
(*    Printf.printf "New productions:\n";*)
(*    Set.iter (fun {head=h;body=b} -> Printf.printf "\t%c -> %s\n" h (word2str b)) newRules;*)
      new ContextFreeGrammarBasic.model (Arg.Representation {
								alphabet = rep.alphabet; (*TODO Get productive alphabet*)
								variables = prodSyms;
								initial = rep.initial;
								rules = newRules
						} )

  
  (*accessible symbols*)
  
  (*given a rule and a set of accessible symbols, adds all symbols from the*)
  (*rule to the set*)
  let ruleAccessibleSymbols r aSymbols =
    Set.flatten (Set.make (List.map (fun s -> Set.cons s aSymbols) r))

  let rulesAccessibleSymbols h aSymbols (rep:t) =
    let rules = bodiesOfHead h rep.rules in
      Set.flatMap (fun r -> ruleAccessibleSymbols r aSymbols) rules
  
  let accessibleSymbolsX (rep:t) aSymbols =
    let vars = Set.filter (fun v -> Set.belongs v rep.variables) aSymbols in (*Remove terminals*)
      Set.flatMap (fun v -> rulesAccessibleSymbols v aSymbols rep) vars
  
  (*show the accessible symbols of the current grammar*)
  let accessibleSymbols (rep:t) = 
    Util.fixedPoint (accessibleSymbolsX rep) (Set.make [rep.initial])
  
  (*TODO Confirm correct new model*)
  let accessibleGrammarRewrite (rep:t) =
    let accessSymbs = accessibleSymbols rep in
    let accessTerms = Set.filter (fun s -> Set.belongs s rep.alphabet) accessSymbs in
    let accessVars = Set.filter (fun s -> Set.belongs s rep.variables) accessSymbs in
    let rules = Set.filter (fun r -> Set.belongs r.head accessVars) rep.rules in
      new ContextFreeGrammarBasic.model (Arg.Representation {
								alphabet = accessTerms;
								variables = accessVars;
								initial = rep.initial;
								rules = rules
						} )

  let clean (rep:t) =
    let prodRewrite = {tType = cleanProductiveTransform; grammar = productiveGrammarRewrite rep} in
    let accessRewrite = {tType = cleanAccessibleTransform; grammar = accessibleGrammarRewrite prodRewrite.grammar#representation} in
    [prodRewrite; accessRewrite]
(*    accessibleGrammarRewrite (productiveGrammarRewrite rep)#representation*)

  let isCFGFullyProductive (rep:t) =
    Set.equals (productiveSymbols rep) (rep.variables)

  let isCFGFullyAccessible (rep:t) =
    Set.equals (accessibleSymbols rep) (Set.union rep.variables rep.alphabet)
    
  let isClean (rep:t) =
    isCFGFullyProductive rep && isCFGFullyAccessible rep
  
  let getNewVar vs =
    let chars = Set.make ['A'; 'B'; 'C'; 'D'; 'E'; 'F'; 'G'; 'H'; 'I'; 'J'; 'K'; 'L'; 'M'; 'N'; 'O'; 'P'; 'Q'; 'R'; 'S'; 'T'; 'U'; 'V'; 'W'; 'X'; 'Y'; 'Z'] in
    let symbs = Set.map char2symb chars in
    let acceptableVars = Set.diff symbs vs in
      Set.nth acceptableVars 0


  let rec leftCorner2 symbol seen (rep: t) =
    match symbol with
    | [] -> Set.empty
    | x::xs ->
      if Set.belongs x seen 
      then Set.make [x]
      else 
        if Set.belongs x rep.alphabet
        then Set.make [x]
        else Set.union 
              (Set.make [x])
              (Set.flatMap (fun b -> (leftCorner2 b (Set.cons x seen) rep)) (bodiesOfHead x rep.rules))

  let leftCorner symbol rep =
    leftCorner2 [symbol] Set.empty rep

    
  (*left recursion removal*)

  let sortLeftCorner l =
    let sortFun e1 e2 =
      let (_, e1) = e1 in
      let (_, e2) = e2 in
      if List.length e1 > List.length e2 then -1
      else (if List.length e1 < List.length e2 then 1 else 0)
    in
    List.sort sortFun l

  let addToMap map varL =
    let rec addToMap2 map varL value =
      match varL with
      | [] -> ()
      | x::xs -> (*Printf.printf "Adding var %c with value %d\n" x value;*)
                  Hashtbl.add map x value; addToMap2 map xs (value+1)
    in
    addToMap2 map varL 0

(* TODO Util.printWord does not exist anymore *)
(*  let rec print_rules r =*)
(*    match r with*)
(*    | [] -> Printf.printf "\n"*)
(*    | x::xs -> Printf.printf " - %c ->" x.head; Util.printWord x.body; print_rules xs*)


  let removeDirectLeftRecursion (rep:t) = 
    let hasRuleDirectLeftRecursion r =
      match r.body with
      | [] -> false
      | x::xs when x = r.head -> true
      | x::xs -> false
    in
    
    let recursiveRuleRewrite r nV =
      let body =
        match r.body with
        | [] -> [epsilon] (*Not reacheable*)
        | x::xs -> xs@[nV]
      in
      { head = nV; body = body }
    in
      
    let nRecursiveRuleRewrite r nV =
      let body = r.body@[nV] in
        { head = r.head; body = body }
    in
    
    let rec removeDLRFromVar v drs ndrs nV =
      if v = Set.empty then Set.empty
      else let (x,xs) = Set.cut v in
(*        Printf.printf "\tRemoving direct left recursion from variable %c\n" x;*)
        let recursiveRs = Set.filter (fun r -> r.head = x) drs in
        let nRecursiveRs = Set.filter (fun r -> r.head = x) ndrs in
        let newVar = getNewVar nV in
(*        Printf.printf "\tNew variable is %c\n" newVar;*)
        let recRulesRewriteTmp = Set.map (fun r -> recursiveRuleRewrite r newVar) recursiveRs in
        let recRulesRewrite = Set.cons ( {head = newVar; body = []} ) recRulesRewriteTmp in
        let nRecRulesRewrite = Set.map (fun r -> nRecursiveRuleRewrite r newVar) nRecursiveRs in
        let newRules = Set.union recRulesRewrite nRecRulesRewrite in
(*        print_rules (Set.toList newRules);*)
          Set.union newRules (removeDLRFromVar xs drs ndrs (Set.cons newVar nV))
    in
    
    let leftRecursiveRules = Set.filter (fun r -> hasRuleDirectLeftRecursion r) rep.rules in
(*        print_rules (Set.toList leftRecursiveRules);*)
    let leftRecursiveVars = Set.map (fun r -> r.head) leftRecursiveRules in
    let nonLeftRecursiveRules = Set.diff rep.rules leftRecursiveRules in
(*        print_rules (Set.toList nonLeftRecursiveRules);*)
    let nonLeftRecursiveRulesClean = Set.filter (fun {head = h; body = _} -> not (Set.belongs h leftRecursiveVars)) nonLeftRecursiveRules in
    let newRules = Set.union nonLeftRecursiveRulesClean (removeDLRFromVar leftRecursiveVars leftRecursiveRules nonLeftRecursiveRules rep.variables) in
(*      print_rules (Set.toList newRules);*)
    let newVars = Set.union rep.variables (Set.map (fun r -> r.head) newRules) in
      new ContextFreeGrammarBasic.model (Arg.Representation {
		    alphabet = rep.alphabet;
		    variables = newVars;
			  initial = rep.initial;
			  rules = newRules
		  } )


  let rec removeIndirectLeftRecursion map varL (rep:t) = 
    match varL with
    | [] -> new ContextFreeGrammarBasic.model (Arg.Representation {
		          alphabet = rep.alphabet;
		          variables = rep.variables;
			        initial = rep.initial;
			        rules = rep.rules
		        } )
    | var::xs -> 
      let perVarIndirectRemoval map var (rep:t) =
        let perVarProdIndirectRemoval prodHead iVal prodBody rhsValues (rep:t) =
          let results = Set.flatMap (
            fun (jVal, rhsBody) ->
              match jVal with
              | None -> Set.make [{head = prodHead; body = rhsBody}]
              | Some jVal -> 
                if iVal > jVal
                then (
                  let rhsVar = (List.hd rhsBody) in
                  let rhsVarBodies = bodiesOfHead rhsVar rep.rules in
                  let replaceRules = Set.flatMap (fun rhsBody ->
                    if List.length prodBody >= 1
                    then (
                      if List.hd prodBody = rhsVar
                      then Set.make [{head = prodHead; body = rhsBody@(if List.length prodBody >= 1 then List.tl prodBody else prodBody)}]
                      else Set.make []
                    )
                    else Set.make [] 
                  ) rhsVarBodies 
                  in
                  replaceRules
                )
                else  Set.make [{head = prodHead; body = rhsBody}]
          ) rhsValues in
          results
        in
        let iVal = Hashtbl.find_opt map var in
        match iVal with
        | None -> Set.filter (fun {head=h;body=_} -> h=var) rep.rules
        | Some iVal -> (
          let varRules = bodiesOfHead var rep.rules in
          let rhsValues = Set.map (
            fun b -> 
              if List.length b >= 1 
              then (Hashtbl.find_opt map (List.hd b), b)
              else (None, b)
          ) varRules
          in
          Set.flatMap (fun b ->
            let r = perVarProdIndirectRemoval var iVal b rhsValues rep in
            r
          ) varRules)
      in
      let newProds = Set.flatMap (fun v -> perVarIndirectRemoval map v rep) rep.variables in
      let newGrammar = new ContextFreeGrammarBasic.model (Arg.Representation {
         alphabet = rep.alphabet;
         variables = rep.variables;
         initial = rep.initial;
         rules = newProds
       } ) in
      let newGrammar = removeDirectLeftRecursion newGrammar#representation in
      removeIndirectLeftRecursion map xs newGrammar#representation


  let removeLeftRecursion (rep:t) =
    let map = Hashtbl.create (Set.size rep.variables) in
    let leftCornerTest = List.map (fun v -> (v, (Set.toList (leftCorner v rep))) ) (Set.toList rep.variables) in
    let sortedLeftCornerTest = sortLeftCorner leftCornerTest in
    addToMap map (List.map (fun (v,_) -> v) sortedLeftCornerTest);
    let sortedVars = List.map (fun (s,_) -> s) sortedLeftCornerTest in
    let result = removeIndirectLeftRecursion map sortedVars rep in
      {tType = leftRecursionRemovalTransform; grammar = result}
      
  (*left factoring*)
  
  let rec lcp l1 l2 =
    match l1 with
    | [] -> []
    | x1::xs1 -> match l2 with
                | [] -> []
                | x2::xs2 -> if x1=x2 then [x1]@(lcp xs1 xs2) else []
  
  let perVarLCP v rs =
    let rules = Set.filter (fun r -> r.head = v) rs in
    let combos = List.flatten (pairs (Set.toList rules)) in
    let lcpList = List.map ( fun (r1,r2) -> lcp r1.body r2.body) combos in
    let lcpList = List.filter (fun l -> l <> []) lcpList in
      Set.toList (Set.make lcpList) (*Remove repeats*)
  
  let rec sameRuleFactoring nV p rb =
    match p with
    | [] -> [nV]
    | x::xs -> match rb with
              | [] -> []
              | x2::xs2 -> [x2]@sameRuleFactoring nV xs xs2
      
  let rec newRuleFactoring rb p =
    match rb with
    | [] -> []
    | x::xs -> match p with
              | [] -> [x]@newRuleFactoring xs p
              | x2::xs2 -> []@newRuleFactoring xs xs2
      
  let rec ruleHasPrefix r p rb =
    match p with
    | [] ->true
    | x::xs -> match rb with
              |[] -> false
              |x2::xs2 -> if x = x2 then ruleHasPrefix r xs xs2 else false
     
  let rec getSmallestLCP l currSmallest =
    match l with
    | [] -> currSmallest
    | x::xs -> if (x <> [] && List.length x < List.length currSmallest)
               then getSmallestLCP xs x
               else getSmallestLCP xs currSmallest
      
  let rec getBiggestList ll currBiggest =
    match ll with
    | [] -> currBiggest
    | x::xs -> let length = List.length x in
                if length > currBiggest
                then getBiggestList xs length
                else getBiggestList xs currBiggest
      
  let rec createLargeList size =
    match size with
    | 0 -> []
    | _ -> [symb "a"] @ createLargeList (size-1)
      
  let rec perVarFactoring pair allVars (rep:t) = (* pair = ('A', ['a']) *)
    if pair = Set.empty then Set.empty
    else let (x,xs) = Set.cut pair in
      let var = fst x in
      let prefix = snd x in
(*     Printf.printf "prefix = "; print_list prefix; Printf.printf "\n";*)
      let varRules = Set.filter (fun r -> r.head = var) rep.rules in
      let prefixedRules = Set.filter (fun r -> ruleHasPrefix r prefix r.body) varRules in
(*     Printf.printf "prefixedRules = "; Util.println (CFGSyntax.toStringList prefixedRules);*)
      let nonPrefixedRules = Set.filter (fun r -> not (ruleHasPrefix r prefix r.body)) varRules in
(*     Printf.printf "nonPrefixedRules = "; Util.println (CFGSyntax.toStringList nonPrefixedRules);*)
      let newVar = getNewVar allVars in
(*     Printf.printf "newVar = %c\n" newVar;*)
      let newSameHeadRulesSet = Set.map (fun r -> { head = var; body = sameRuleFactoring newVar prefix r.body } ) prefixedRules in
      let newHeadRulesSet = Set.map (fun r -> { head = newVar; body = newRuleFactoring r.body prefix } ) prefixedRules in
      let rules = Set.union nonPrefixedRules (Set.union newSameHeadRulesSet newHeadRulesSet) in
(*     print_rules (Set.toList rules);*)
        Set.union rules (perVarFactoring xs (Set.cons newVar allVars) rep)
  
  let getPerVarLCPResult (rep:t) = 
    let perVarLCPResult = Set.map (fun v -> (v, perVarLCP v rep.rules)) rep.variables in
    let perVarLCPResult = Set.filter (fun (_,l) -> l <> []) perVarLCPResult in
      Set.map ( fun (v,l) -> (v, getSmallestLCP l (createLargeList ((getBiggestList l 0)+1))) ) perVarLCPResult

  let isLeftFactoring (rep:t) =
    Set.map (fun (v,l) -> v) (getPerVarLCPResult rep) <> Set.empty

  let rec leftFactoring (rep:t) =
    let perVarLCPResult = getPerVarLCPResult rep in
(*    Printf.printf "perVarLCPResult = "; Set.iter (fun (v,l) -> Printf.printf "%c, " v; print_list l) perVarLCPResult; Printf.printf "\n";*)
    let variablesToFactorize = Set.map (fun (v,l) -> v) perVarLCPResult in
(*    Printf.printf "Variables to factorize = "; print_list (Set.toList variablesToFactorize); Printf.printf "\n";*)
    let unchangedVariables = Set.diff rep.variables variablesToFactorize in
(*    Printf.printf "Unchanged variables = "; print_list (Set.toList unchangedVariables); Printf.printf "\n";*)
    let unchangedRules = Set.filter (fun {head = h; body = _} -> Set.belongs h unchangedVariables) rep.rules in
    let newRules = perVarFactoring perVarLCPResult rep.variables rep in
    let newVars = Set.map (fun ({head=v;body=_}) -> v ) newRules in
    let newGrammar = new ContextFreeGrammarBasic.model (Arg.Representation {
	      alphabet = rep.alphabet;
	      variables = Set.union rep.variables newVars;
	      initial = rep.initial;
	      rules = Set.union newRules unchangedRules
	    } ) in
    if isLeftFactoring newGrammar#representation 
    then leftFactoring newGrammar#representation 
    else {tType = leftFactoringTransform; grammar = newGrammar}

  let hasEmptyProductions (rep:t) =
    let nullableVars = Set.filter (fun v -> doWordGenerateEmpty [v] rep) rep.variables in
    Set.size nullableVars <> 0

  let removeEmptyProductions2 (rep:t) = 
    let rec combi vars body =
      match body with
      | [] -> Set.make [[]]
      | x::xs -> let res = combi vars xs in
                  (*Printf.printf "Current body symbol is %c\n" x;
                  Printf.printf "res = \n";
                  Set.iter (fun l -> Printf.printf "\t%s\n" (word2str l)) res;*)
                  Set.flatMap (fun v ->
                                (*(if x = v
                                then (
                                  Printf.printf "\tx = v (%c = %c)\n" x v;
                                  Set.iter (fun p -> Printf.printf "\t\t{%s}\n" (word2str p)) (Set.union res (Set.map (fun l -> v::l) res))
                                )
                                else (
                                  Printf.printf "\tx =/= v (%c =/= %c)\n" x v;
                                  Set.iter (fun p -> Printf.printf "\t\t{%s}\n" (word2str p)) (Set.map (fun l -> x::l) res)
                                ));*)
                                if x = v
                                then Set.union res (Set.map (fun l -> v::l) res)
                                else Set.map (fun l -> x::l) res
                  ) vars
    in
    let changeProds vars prod = 
      let {head=h; body=b} = prod in
      if List.length b = 0 then Set.empty
      else (
        let prodBodiesSet = Set.filter (fun p -> List.length p <> 0) (combi vars b) in
        Set.map (fun b -> {head = h; body = b} ) prodBodiesSet
      )
    in
    let nullableVars = Set.filter (fun v -> doWordGenerateEmpty [v] rep) rep.variables in
    if Set.size nullableVars = 0 
    then (
      new ContextFreeGrammarBasic.model (Arg.Representation {
	        alphabet = rep.alphabet;
	        variables = rep.variables;
	        initial = rep.initial;
	        rules = rep.rules
	      })
    )
    else (
      let toChangeProds = Set.filter (fun {head=h;body=b} -> 
                                        Set.exists (
                                          fun v -> List.length b >= 1 && List.mem v b
                                        ) nullableVars
                           ) rep.rules 
      in
      let unchangedProds = Set.filter (
                            fun p -> List.length p.body >= 1
                           ) (Set.diff rep.rules toChangeProds) in
      let newProds = Set.flatMap (changeProds nullableVars) toChangeProds in
(*      Set.iter (fun p -> Printf.printf "{%c;%s}\n" p.head (word2str p.body) ) newProds;*)
(*      if Set.belongs rep.initial nullableVars
      then (
        let newInitial = getNewVar rep.variables in
        let newInitialProds = Set.make [ { head = newInitial; body = []}; { head = newInitial; body = [rep.initial]} ] in
        let newProds = Set.union newInitialProds newProds in
        new ContextFreeGrammarBasic.model (Arg.Representation {
	        alphabet = rep.alphabet;
	        variables = Set.cons newInitial rep.variables;
	        initial = newInitial;
	        rules = Set.union newProds unchangedProds
	      } )
      ) else ( *)
        new ContextFreeGrammarBasic.model (Arg.Representation {
	        alphabet = rep.alphabet;
	        variables = rep.variables;
	        initial = rep.initial;
	        rules = Set.union newProds unchangedProds
	      } (* ) *)
      )
    )
    
  
  let removeEmptyProductions (rep:t) =
    { tType = epsilonRemovalTransform; grammar = removeEmptyProductions2 rep }
  

  let isUnitProd body (rep:t) =
    let rec isUnitProd2 cS cB p =
      match cB with
      | [] -> false
      | x::xs -> if doWordGenerateEmpty cB rep && doWordGenerateEmpty p rep
                  then true
                  else isUnitProd2 x xs (p@[cS])
    in
    let isUnitProdAux r (rep:t) =
      match r with
      | [] -> false
      | x::xs -> isUnitProd2 x xs []
    in
    if (List.length body = 1 && Set.belongs (List.hd body) rep.variables) 
    then true 
    else (
      if List.length body > 1 && List.for_all ( fun c -> Set.belongs c rep.variables ) body
        then isUnitProdAux body rep 
        else false
      )

  let hasUnitProductions (rep:t) =
    Set.size (Set.filter (fun {head = _; body = b} -> isUnitProd b rep ) rep.rules) <> 0


  let rec findUnitPair2 cS cB p (rep:t) =
    match cB with
    | [] -> []
    | x::xs -> if doWordGenerateEmpty cB rep && doWordGenerateEmpty p rep
                then [cS]
                else findUnitPair2 x xs (p@[cS]) rep

  let findUnitPairAux r (rep:t) =
    match r with
    | [] -> []
    | x::xs -> findUnitPair2 x xs [] rep
             
  let rec findUnitPairX origVar var seen (rep:t) =
    if Set.belongs var seen then [] else (
      let rules = bodiesOfHead var rep.rules in
      let results = List.flatten (
                      List.map (fun r -> 
                          if List.length r = 1 && Set.belongs (List.hd r) rep.variables
                          then (
                            if Set.belongs (List.hd r) seen
                            then []@findUnitPairX origVar (List.hd r) (Set.cons var seen) rep
                            else r@findUnitPairX origVar (List.hd r) (Set.cons var seen) rep
                          )
                          else  findUnitPairAux r rep 
                      ) (Set.toList rules)
                    ) 
      in
      results
    )
    
  let findUnitPair var (rep:t) =
    let results = List.map (fun r -> (var, r)) (findUnitPairX var var Set.empty rep) in
    [(var, var)] @ results
(*    (var,(findUnitPairX var Set.empty rep))*)

  (*Used to sort unit pair lists by biggest length to lowest length*)
  let compareUnitPairList l1 l2 =
    if List.length l1 > List.length l2 then -1
    else (if List.length l1 < List.length l2 then 1
    else 0)  
   
  let getNonUnitProductions var (rep:t) = 
    let prods = bodiesOfHead var rep.rules in
(*    Printf.printf "var = %c\n" var;*)
(*    Set.iter (fun p -> Printf.printf "\tIs %c -> %s unit? %b\n" var (word2str p) (isUnitProd p rep)) prods;*)
(*    Printf.printf "\n";*)
    Set.filter (fun p -> not (isUnitProd p rep)) prods

  let removeUnitProductions (rep:t) = 
    let perVarPair pair (rep:t) =
      let (h,b) = pair in
      let nUnitProds = getNonUnitProductions b rep in
(*      Set.iter (fun p -> Printf.printf "%c -> %s\n" h (word2str p)) nUnitProds;*)
      Set.toList (Set.map (fun p -> {head = h; body = p}) nUnitProds)
    in
    let perVar pairs (rep:t) =
      List.flatten (List.map (fun p -> perVarPair p rep) pairs)
    in
    let unitPairs = List.map (fun v -> findUnitPair v rep) (Set.toList rep.variables) in
    (*let unitPairs = List.sort compareUnitPairList unitPairs in*)
    let newProds = List.flatten (
                    List.map (fun l ->
                      perVar l rep
                     ) unitPairs 
                   ) in
    let result = new ContextFreeGrammarBasic.model (Arg.Representation {
	      alphabet = rep.alphabet;
	      variables = rep.variables;
	      initial = rep.initial;
	      rules = Set.make newProds
	    } )
	  in
	    {tType = unitRemovalTransform; grammar = result}

    
    
  let generateRecursiveDescendentParser lang (rep:t) =
    match String.lowercase_ascii lang with
      | "c" -> let parser = new RDParserC.parser in parser#build rep
      | "ocaml" -> let parser = new RDParserOCaml.parser in parser#build rep
      | "java" -> let parser = new RDParserJava.parser in parser#build rep
      | _ -> "Language " ^ lang ^ " is not supported.\n"


  let transformToLL1 (rep:t) =
    let transform1 = {tType = epsilonRemovalTransform; grammar = (removeEmptyProductions rep).grammar} in
    let transform2 = {tType = unitRemovalTransform; grammar = (removeUnitProductions transform1.grammar#representation).grammar} in
    let cleanResult = clean transform2.grammar#representation in
    let transform3 = {tType = cleanProductiveTransform; grammar = (List.nth cleanResult 0).grammar} in
    let transform4 = {tType = cleanAccessibleTransform; grammar = (List.nth cleanResult 1).grammar} in
    let transform5 = {tType = leftRecursionRemovalTransform; grammar = (removeLeftRecursion transform4.grammar#representation).grammar} in
    let transform6 = {tType = leftFactoringTransform; grammar = (leftFactoring transform5.grammar#representation).grammar} in
    [transform1; transform2; transform3; transform4; transform5; transform6]
  

  class model (arg: t Arg.alternatives) =
    object(self) inherit ContextFreeGrammarBasic.model arg as super
    
    method isSimplified = simplified
    method rdparserOpts = [ "OCaml"; "C"; "Java"; "Rust" ]
    method toggleSimplified = Printf.printf "simplified is %b toggling to %b\n" simplified (not simplified);
                              simplified <- not simplified
    
    method follow testSymbol = follow testSymbol simplified self#representation
    method lookahead rule = lookahead rule simplified self#representation
    method isLL1 = isLL1 simplified self#representation
    method isLeftRecursive = isLeftRecursive self#representation
    method createParsingTable = createParsingTable simplified self#representation
    method hasParsingTableConflict = hasParsingTableConflict simplified self#representation
    method acceptZ w = acceptZ w simplified self#representation
    method productiveSymbols = productiveSymbols self#representation
    method accessibleSymbols = accessibleSymbols self#representation
    method productiveRewrite = productiveGrammarRewrite self#representation
    method accessibleRewrite = accessibleGrammarRewrite self#representation
    method clean = clean self#representation
    method isFullyProductive = isCFGFullyProductive self#representation
    method isFullyAccessible = isCFGFullyAccessible self#representation
    method isClean = isClean self#representation
    method removeLeftRecursion = removeLeftRecursion self#representation
    method removeDirectLeftRecursion = removeDirectLeftRecursion self#representation
    method leftFactoring = leftFactoring self#representation
    method isLeftFactoring = isLeftFactoring self#representation
    method leftCorner s = leftCorner s self#representation
    method hasEmptyProductions = hasEmptyProductions self#representation
    method removeEmptyProductions = removeEmptyProductions self#representation
    method hasUnitProductions = hasUnitProductions self#representation
    method removeUnitProductions = removeUnitProductions self#representation
    method generateRecursiveDescendentParser pLang = generateRecursiveDescendentParser pLang self#representation
    method transformToLL1 = transformToLL1 self#representation
  end
end

#endif
