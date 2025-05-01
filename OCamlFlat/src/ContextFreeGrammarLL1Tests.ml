#ifdef ALL

open BasicTypes
open ContextFreeGrammarBasic  

module ContextFreeGrammarLL1Tests : sig end =
struct
	let active = false

  let example1 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 1",
	  name : "G1",
	  alphabet : ["a", "b", "c", "d", "e"],
	  variables : ["S", "A", "B", "C", "D", "E"],
	  initial : "S",
    rules : ["S -> ABCDE", "A -> a | ", "B -> b | ", "C -> c", "D -> d | ", "E -> e | "]
  } |}

  let example2 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 2",
	  name : "G2",
	  alphabet : ["a", "b", "c", "d"],
	  variables : ["S", "B", "C"],
	  initial : "S",
    rules : ["S -> Bb | Cd", "B -> aB | ", "C -> cC | "]
  } |}
  
  let example3 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 3",
	  name : "G3",
	  alphabet : ["+", "*", "(", ")", "i"],
	  variables : ["E", "D", "T", "U", "F"],
	  initial : "E",
    rules : ["E -> TD", "D -> +TD | ", "T -> FU", "U -> *FU | ", "F -> i | (E)"]
  } |}
  
  let example4 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 4",
	  name : "G4",
	  alphabet : ["a", "b", "c", "f", "g", "h"],
	  variables : ["S", "B", "C", "D", "E", "F"],
	  initial : "S",
    rules : ["S -> aBDh", "B -> cC", "C -> bC | ", "D -> EF", "E -> g | ", "F -> f | "]
  } |}

  let example5 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 5",
	  name : "G5",
	  alphabet : ["n", "+", "*"],
	  variables : ["E", "A", "B"],
	  initial : "E",
    rules : ["E -> nA", "A -> EB | ", "B -> +A | *A"]
  } |}
  
  let example6 = {| {
	  kind : "context free grammar", 
	  description : "Exemple 6",
	  name : "G6",
	  alphabet : ["a", "b"],
	  variables : ["N", "A", "B", "C"],
	  initial : "N",
    rules : ["N -> AB | BA", "A -> a | CAC", "B -> b | CBC", "C -> a | b"]
  } |}
  
  let cfg_dissertation = {| {
	  kind : "context free grammar", 
	  description : "dissertation example",
	  name : "G2",
	  alphabet : ["a", "b", "c"],
	  variables : ["S", "A", "B", "C", "D", "E"],
	  initial : "S",
    rules : ["S -> ABC", "A -> aD", "B -> CE", "C -> c", "D -> AB | ", "E -> bE | "]
  } |}

  let non_deterministic_grammar = {| {
	  kind : "context free grammar", 
	  description : "Non deterministic grammar",
	  name : "N",
	  alphabet : ["a", "b", "d", "g", "h"],
	  variables : ["S", "A", "B", "C"],
	  initial : "S",
    rules : ["S -> ACB | CbB | Ba", "A -> da | BC", "B -> g | ", "C -> h | "]
  } |}

  let accessible_symbols1 = {| {
	  kind : "context free grammar", 
	  description : "Accessible symbols example",
	  name : "AS1",
	  alphabet : ["a", "b"],
	  variables : ["A", "B", "C", "D", "E"],
	  initial : "A",
    rules : ["A -> aBb | bBa", "B -> Cb | bC", "C -> a | aC", "D -> E | Db", "E -> aE | Da"]
  } |}
  
  let accessible_symbols2 = {| {
	  kind : "context free grammar", 
	  description : "Accessible symbols example",
	  name : "AS2",
	  alphabet : ["a", "b"],
	  variables : ["S", "B"],
	  initial : "S",
    rules : ["S -> a", "B -> b"]
  } |}
  
  let productive_symbols1 = {| {
	  kind : "context free grammar", 
	  description : "Productive symbols example",
	  name : "PS1",
	  alphabet : ["a", "b"],
	  variables : ["A", "B", "C", "D", "E"],
	  initial : "A",
    rules : ["A -> aBb | bBa", "B -> CD | aC | Ab", "C -> a | aC", "D -> E | DA", "E -> aE | Da"]
  } |}

  let productive_symbols2 = {| {
	  kind : "context free grammar", 
	  description : "Productive symbols example",
	  name : "PS2",
	  alphabet : ["a", "b"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> a | A", "A -> AB", "B -> b"]
  } |}
  
  let clean_grammar1 = {| {
	  kind : "context free grammar", 
	  description : "Clean example from https://www.cs.scranton.edu/~mccloske/courses/cmps260/cfg_remove_useless.html",
	  name : "Clean1",
	  alphabet : ["a", "b", "c", "d"],
	  variables : ["S", "A", "B", "C", "D"],
	  initial : "S",
    rules : ["S -> aSa | bB | bAA", "A -> a | SbA | aB", "B -> AB | CaB", "C -> cC | Sa | bD", "D -> dD | "]
  } |}

  let direct_left_recursion_grammar1 = {| {
	  kind : "context free grammar", 
	  description : "Direct Left-recursion example 1",
	  name : "DR1",
	  alphabet : ["a", "b"],
	  variables : ["A"],
	  initial : "A",
    rules : ["A -> Aa | b"]
  }  |}
  
  let direct_left_recursion_grammar2 = {| {
	  kind : "context free grammar", 
	  description : "Direct Left-recursion example 2",
	  name : "DR2",
	  alphabet : ["a", "b"],
	  variables : ["B"],
	  initial : "B",
    rules : ["B -> a | Bb"]
  } |}
  
  let indirect_left_recursion_grammar1 = {| {
	  kind : "context free grammar", 
	  description : "Indirect Left-recursion example 1",
	  name : "IR1",
	  alphabet : ["a"],
	  variables : ["S", "A"],
	  initial : "S",
    rules : ["S -> A | a", "A -> S"]
  }  |}

  let indirect_left_recursion_grammar2 = {| {
	  kind : "context free grammar", 
	  description : "Indirect Left-recursion example 2",
	  name : "IR2",
	  alphabet : ["a"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> A | B", "A -> a", "B -> S"]
  }  |}
  
  let indirect_left_recursion_grammar3 = {| {
	  kind : "context free grammar", 
	  description : "Indirect Left-recursion example 2",
	  name : "IR3",
	  alphabet : ["a", "b", "c"],
	  variables : ["S", "A", "B", "C"],
	  initial : "S",
    rules : ["S -> ABCS", "A -> a | ", "B -> b | ", "C -> c | "]
  }  |} 
  
  let indirect_left_recursion_grammar4 = {| {
	  kind : "context free grammar", 
	  description : "Indirect Left-recursion example",
	  name : "IR4",
	  alphabet : ["a", "b", "d", "e", "f", "g"],
	  variables : ["A", "B", "C", "D"],
	  initial : "A",
    rules : ["A -> Ba | b", "B -> Cd | e", "C-> Df | g", "D -> Df | Aa | Cg"]
  }  |}

  let indirect_left_recursion_grammar5 = {| {
	  kind : "context free grammar", 
	  description : "Indirect Left-recursion example 2",
	  name : "IR3",
	  alphabet : ["a"],
	  variables : ["S", "A"],
	  initial : "S",
    rules : ["S -> AS", "A -> a | "]
  }  |}

  let left_factoring_example = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF1",
	  alphabet : ["a", "b", "e", "i", "t"],
	  variables : ["S", "E"],
	  initial : "S",
    rules : ["S -> iEtS | iEtSeS | a", "E -> b"]
  } |}

  let left_factoring_example2 = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF2",
	  alphabet : ["a", "c"],
	  variables : ["A", "B"],
	  initial : "A",
    rules : ["A -> aAB | aBc | aAc", "B ->"]
  } |}

  let left_factoring_example3 = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF3",
	  alphabet : ["a", "b"],
	  variables : ["S"],
	  initial : "S",
    rules : ["S -> bSSaaS | bSSaSb | bSb | a"]
  } |}

  let left_factoring_example4 = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF4",
	  alphabet : ["a", "b"],
	  variables : ["S"],
	  initial : "S",
    rules : ["S -> aSSbS | aSaSb | abb | b"]
  } |}
  
  let left_factoring_example5 = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF5",
	  alphabet : ["a", "b", "c", "d"],
	  variables : ["S"],
	  initial : "S",
    rules : ["S -> a | ab | abc | abcd"]
  } |}
  
  let left_factoring_example6 = {| {
	  kind : "context free grammar", 
	  description : "Left Factoring example",
	  name : "LF6",
	  alphabet : ["a", "b", "c", "d"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> aAd | aB", "A -> a | ab", "B -> ccd | ddc"]
  } |}
  
  let unit_removal_example1 = {| {
	  kind : "context free grammar", 
	  description : "unit removal example",
	  name : "UR1",
	  alphabet : ["a", "b"],
	  variables : ["E", "T", "F", "I"],
	  initial : "E",
    rules : ["E -> T", "T -> F", "F -> I", "I -> a | b | Ia | Ib"]
  } |}

  let unit_removal_example2 = {| {
	  kind : "context free grammar", 
	  description : "unit removal example 2",
	  name : "UR2",
	  alphabet : ["a", "b", "c"],
	  variables : ["A", "B", "C"],
	  initial : "A",
    rules : ["A -> B | a", "B -> C | b", "C -> A | c"]
  } |}
  
  let unit_removal_example3 = {| {
	  kind : "context free grammar", 
	  description : "unit removal example 3",
	  name : "UR3",
	  alphabet : ["a", "b", "c"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> Aa | B | c", "A -> a | bc | B", "B -> A | bb"]
  } |}
  
  let unit_removal_example4 = {| {
	  kind : "context free grammar", 
	  description : "unit removal example 4",
	  name : "UR4",
	  alphabet : ["a", "b", "d"],
	  variables : ["S", "A", "B", "C", "D", "E"],
	  initial : "S",
    rules : ["S -> AC", "A -> a", "B -> D", "C -> B | d", "D -> E", "E -> b"]
  } |}
  
  let unit_removal_example5 = {| {
	  kind : "context free grammar", 
	  description : "unit removal example 5",
	  name : "UR5",
	  alphabet : ["a", "b", "0", "1", "(", ")", "+", "*"],
	  variables : ["I", "F", "T", "E"],
	  initial : "E",
    rules : ["E -> T | E+T", "T -> F | T*F", "F -> I | (E)", "I -> a | b | Ia | Ib | I0 | I1"]
  } |}

  let epsilon_removal_example1 = {| {
	  kind : "context free grammar", 
	  description : "epsilon removal example",
	  name : "ER1",
	  alphabet : ["a", "b", "d"],
	  variables : ["S", "A", "B", "C", "D"],
	  initial : "S",
    rules : ["S -> ABaC", "A -> BC", "B -> b | ", "C -> D | ", "D -> d"]
  } |}
  
  let epsilon_removal_example2 = {| {
	  kind : "context free grammar", 
	  description : "epsilon removal example 2",
	  name : "ER2",
	  alphabet : ["a", "b"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> AB", "A -> AaA | ", "B -> BbB | "]
  } |}
  
  let epsilon_removal_example3 = {| {
	  kind : "context free grammar", 
	  description : "epsilon removal example 3",
	  name : "ER3",
	  alphabet : ["a", "b"],
	  variables : ["S", "A", "B"],
	  initial : "S",
    rules : ["S -> AB", "A -> aAA | ", "B -> bBB | "]
  } |}

  let firstPairConversion_old l = Set.make (List.map (fun (a,b) -> (a, Set.make b)) l)
  let followPairConversion_old l = Set.make (List.map (fun (a,b) -> (a, Set.make b)) l)
  let lookaheadPairConversion_old l = Set.make (List.map (fun (a,b) -> ContextFreeGrammarBasic.parseLine a, Set.make b) l)

  let firstPairConversion l = Set.make (List.map (fun (a,b) -> (symb a, Set.make (List.map char2symb b))) l)
  let followPairConversion l = Set.make (List.map (fun (a,b) -> (char2symb a, Set.make (List.map char2symb b))) l)
  let lookaheadPairConversion l = Set.make (List.map (fun (a,b) -> (Set.nth (ContextFreeGrammarBasic.parseLine a) 0), Set.make (List.map char2symb b)) l)

  let printRepresentation (rep: t) =
    Printf.printf "Alphabet = "; Util.printAlphabet rep.alphabet;
    Printf.printf "Variables = "; Util.printAlphabet rep.variables;
    Printf.printf "Initial = %s\n" (symb2str rep.initial);
    Printf.printf "Rules {\n"; Set.iter (fun {head=h; body=b} -> Printf.printf "\t%s -> %s\n" (symb2str h) (word2str b)) rep.rules;
    Printf.printf "}\n\n"

  let rec testFunction2 f l c =
    if l = Set.empty then ()
    else let ((t,r),xs) = Set.cut l in
      if (f t = r) then () else Printf.printf "\t\tTest %i fails!\n" c;
      testFunction2 f xs (c+1)


	let colorRed = "\027[31m"
	let colorGreen = "\027[32m"
	let colorOff = "\027[0m"

(*	let colorRed = ""*)
(*	let colorGreen = ""*)
(*	let colorOff = ""*)

  let failPrint str =
    Printf.printf "%s" (colorRed ^ str ^ colorOff)
    
  let okPrint str =
    Printf.printf "%s" (colorGreen ^ str ^ colorOff)

  let printResult r =
    if r
    then okPrint "O"
    else failPrint "X"
  
  let printFirstTest t =
    Set.iter (fun (v,s) -> 
      Printf.printf "(%s, [" v;
      Set.iter (fun v -> Printf.printf "%c " v) s;
      Printf.printf "%s" "]) "
    ) t
    
  let compareTheseSets s1 s2 =
    Set.for_all (fun (h1,r1) ->
      Set.exists (fun (h2,r2) -> h1 = h2 && Set.equals r1 r2) s2
    ) s1 && Set.size s1 = Set.size s2

  let testFirst g r =
    let allResults = Set.map (fun v -> (v, g#first [v])) (g#representation : t).variables in
(*    Printf.printf "\n\tComparing:";*)
(*    Set.iter (fun (v,b) -> Printf.printf "\n\t\t%s->\t" (symb2str v); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) b) r;*)
(*    Printf.printf "\n\twith:";*)
(*    Set.iter (fun (v,b) -> Printf.printf "\n\t\t%s->\t" (symb2str v); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) b) allResults;*)
(*    Printf.printf "\n";*)
(*    r = allResults*)
    compareTheseSets r allResults

  let testFollow g r =
    let allResults = Set.map (fun v -> (v, g#follow v)) (g#representation : t).variables in
(*    Printf.printf "\n\tComparing:";*)
(*    Set.iter (fun (v,b) -> Printf.printf "\n\t\t%s->\t" (symb2str v); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) b) r;*)
(*    Printf.printf "\n\twith:";*)
(*    Set.iter (fun (v,b) -> Printf.printf "\n\t\t%s->\t" (symb2str v); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) b) allResults;*)
(*    Printf.printf "\n";*)
(*    r = allResults*)
    compareTheseSets r allResults
    
  let testLookahead g r =
    let rep = (g#representation : t) in
    let allResults = 
      Set.flatMap (fun v -> 
        let rules = Set.filter (fun {head=h; _} -> h = v ) rep.rules in
        Set.map (fun r -> 
          (r, g#lookahead r)
        ) rules
      ) rep.variables 
    in
(*    Printf.printf "\n\tComparing:";*)
(*    Set.iter (fun ({head=h;body=b},r) -> Printf.printf "\n\t\t%s->%s\t" (symb2str h) (word2str b); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) r) r;*)
(*    Printf.printf "\n\twith:";*)
(*    Set.iter (fun ({head=h;body=b},r) -> Printf.printf "\n\t\t%s->%s\t" (symb2str h) (word2str b); Set.iter (fun s ->  Printf.printf " %s " (symb2str s)) r) allResults;*)
(*    Printf.printf "\n";*)
(*    r = allResults*)
    compareTheseSets r allResults

  let testFunction1 f r =
    f = r



(*	let test0 () =*)
(*		let m = new ContextFreeGrammarLL1.model (Arg.Text cfg_simple) in*)
(*		let j = m#toJSon in*)
(*			JSon.show j*)

	let dollar = '$'
	let epsilon = '~'

  let testExample1 () =
    Printf.printf "Example1 test: [";
    let first = [ ("S", ['a'; 'b'; 'c']); ("A", ['a'; '~']); ("B", ['b'; '~']); ("C", ['c']); ("D", ['d'; '~']); ("E", ['e'; '~']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', ['$']); ('A', ['b'; 'c']); ('B', ['c']); ('C', ['d'; 'e'; '$']); ('D', ['e'; '$']); ('E', ['$']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->ABCDE", ['a'; 'b'; 'c']); 
                      ("A->a", ['a']); ("A->", ['b'; 'c']);
                      ("B->b", ['b']); ("B->", ['c']); 
                      ("C->c", ['c']); 
                      ("D->d", ['d']); ("D->", ['e'; dollar]); 
                      ("E->e", ['e']); ("E->", [dollar]) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
	  printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testExample2 () =
    Printf.printf "Example2 test: [";
    let first = [ ("S", ['a'; 'b'; 'c'; 'd']); ("B", ['a'; epsilon]); ("C", ['c'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('B', ['b']); ('C', ['d']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->Bb", ['a'; 'b']); ("S->Cd", ['c'; 'd']);
                      ("B->aB", ['a']); ("B->", ['b']);
                      ("C->cC", ['c']); ("C->", ['d']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testExample3 () =
    Printf.printf "Example3 test: [";
    let first = [ ("U", ['*'; epsilon]); ("D", ['+'; epsilon]); ("E", ['('; 'i']); ("F", ['('; 'i']); ("T", ['('; 'i']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('U', [')'; '+'; dollar]); ('D', [')'; dollar]); ('E', [')'; dollar]); ('F', [')'; '*'; '+'; dollar]); ('T', [')'; '+'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("U->*FU", ['*']); ("U->", [')'; '+'; dollar]); 
                      ("D->+TD", ['+']); ("D->", [')'; dollar]); 
                      ("E->TD", ['('; 'i']); 
                      ("F->i", ['i']); ("F->(E)", ['(']);
                      ("T->FU", ['('; 'i']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example3) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testExample4 () =
    Printf.printf "Example4 test: [";
    let first = [ ("S", ['a']); ("B", ['c']); ("C", ['b'; epsilon]); ("D", ['f'; 'g'; epsilon]); ("E", ['g'; epsilon]); ("F", ['f'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('B', ['f'; 'g'; 'h']); ('C', ['f'; 'g'; 'h']); ('D', ['h']); ('E', ['f'; 'h']); ('F', ['h']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->aBDh", ['a']);
                      ("B->cC", ['c']);
                      ("C->bC", ['b']); ("C->", ['f'; 'g'; 'h']); 
                      ("D->EF", ['f'; 'g'; 'h']);
                      ("E->g", ['g']); ("E->", ['f'; 'h']);
                      ("F->f", ['f']); ("F->", ['h']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example4) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testExample5 () =
    Printf.printf "Example5 test: [";
    let first = [ ("E", ['n']); ("A", ['n'; epsilon]); ("B", ['*'; '+']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('E', ['*'; '+'; dollar]); ('A', ['*'; '+'; dollar]); ('B', ['*'; '+'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("E->nA", ['n']);
                      ("A->EB", ['n']); ("A->", ['*'; '+'; dollar]);
                      ("B->+A", ['+']); ("B->*A", ['*']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example5) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testExample6 () =
    Printf.printf "Example6 test: [";
    let first = [ ("N", ['a'; 'b']); ("A", ['a'; 'b']); ("B", ['a'; 'b']); ("C", ['a'; 'b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('N', [dollar]); ('A', ['a'; 'b'; dollar]); ('B', ['a'; 'b'; dollar]); ('C', ['a'; 'b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("N->AB", ['a'; 'b']); ("N->BA", ['a'; 'b']);
                      ("A->a", ['a']); ("A->CAC", ['a'; 'b']);
                      ("B->b", ['b']); ("B->CBC", ['a'; 'b']); 
                      ("C->a", ['a']); ("C->b", ['b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text example6) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"

  let testDissertation () =
    Printf.printf "%s" (Printf.sprintf "Dissertation test: [");
    let first = [ ("S", ['a']); ("A", ['a']); ("B", ['c']); ("C", ['c']); ("D", ['a'; epsilon]); ("E", ['b'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['c']); ('B', ['c']); ('C', ['b'; 'c'; dollar]); ('D', ['c']); ('E', ['c']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->ABC", ['a']); 
                      ("A->aD", ['a']); 
                      ("B->CE", ['c']);
                      ("C->c", ['c']); 
                      ("D->AB", ['a']); ("D->", ['c']);
                      ("E->bE", ['b']); ("E->", ['c']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text cfg_dissertation) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"
    
  let testNFGrammar () =
    Printf.printf "Non deterministic grammar test: [";
    let first = [ ("S", ['a'; 'b'; 'd'; 'g'; 'h'; epsilon]); ("A", ['d'; 'g'; 'h'; epsilon]); ("B", ['g'; epsilon]); ("C", ['h'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['g'; 'h'; dollar]); ('B', ['a'; 'g'; 'h'; dollar]); ('C', ['b'; 'g'; 'h'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->ACB", ['d'; 'g'; 'h'; dollar]); ("S->CbB", ['b'; 'h']); ("S->Ba", ['a'; 'g']);
                      ("A->da", ['d']); ("A->BC", ['g'; 'h'; dollar]); 
                      ("B->g", ['g']); ("B->", ['a'; 'g'; 'h'; dollar]); 
                      ("C->h", ['h']); ("C->", ['b'; 'g'; 'h'; dollar]); ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text non_deterministic_grammar) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 m#isLeftRecursive false);
    Printf.printf "]\n"

  let testAccessible1 () =
    Printf.printf "%s" (Printf.sprintf "Remove inaccessible symbols test 1: [");
    let first = [ ("A", ['a'; 'b']); ("B", ['a'; 'b']); ("C", ['a']); ("D", ['a']); ("E", ['a']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', [dollar]); ('B', ['a'; 'b']); ('C', ['a'; 'b']); ('D', ['a'; 'b']); ('E', ['a'; 'b']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("A->aBb", ['a']); ("A->bBa", ['b']); 
                      ("B->Cb", ['a']); ("B->bC", ['b']);
                      ("C->a", ['a']); ("C->aC", ['a']); 
                      ("D->E", ['a']); ("D->Db", ['a']);
                      ("E->aE", ['a']); ("E->Da", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text accessible_symbols1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 m#isFullyAccessible false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#accessibleRewrite#representation) in
(*      printRepresentation m#representation;*)
(*      printRepresentation transformed#representation;*)
      printResult (testFunction1 transformed#isFullyAccessible true);
    Printf.printf "]\n"
    
  let testAccessible2 () =
    Printf.printf "%s" (Printf.sprintf "Remove inaccessible symbols test 2: [");
    let first = [ ("S", ['a']); ("B", ['b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('B', []) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->a", ['a']); 
                      ("B->b", ['b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text accessible_symbols2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive false);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isFullyAccessible false);
      printResult (testFunction1 m#isFullyProductive true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#accessibleRewrite#representation) in
      printResult (testFunction1 transformed#isFullyAccessible true);
      printResult (testFunction1 transformed#isFullyProductive true);
    Printf.printf "]\n"

  let testProductive1 () =
    Printf.printf "%s" (Printf.sprintf "Remove unproductive symbols test 1: [");
    let first = [ ("A", ['a'; 'b']); ("B", ['a'; 'b']); ("C", ['a']); ("D", ['a']); ("E", ['a']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', ['a'; 'b'; dollar]); ('B', ['a'; 'b']); ('C', ['a'; 'b']); ('D', ['a'; 'b']); ('E', ['a'; 'b']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("A->aBb", ['a']); ("A->bBa", ['b']); 
                      ("B->CD", ['a']); ("B->aC", ['a']); ("B->Ab", ['a'; 'b']);
                      ("C->a", ['a']); ("C->aC", ['a']); 
                      ("D->E", ['a']); ("D->DA", ['a']);
                      ("E->aE", ['a']); ("E->Da", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text productive_symbols1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring true);
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 m#isFullyProductive false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#productiveRewrite#representation) in
      printResult (testFunction1 transformed#isFullyProductive true);
    Printf.printf "]\n"

  let testProductive2 () =
    Printf.printf "%s" (Printf.sprintf "Remove unproductive symbols test 2: [");
    let first = [ ("S", ['a']); ("A", []); ("B", ['b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['b'; dollar]); ('B', ['b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->a", ['a']); ("S->A", []); 
                      ("A->AB", []);
                      ("B->b", ['b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text productive_symbols2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 true);
      printResult (testFunction1 m#isFullyAccessible true);
      printResult (testFunction1 m#isFullyProductive false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#productiveRewrite#representation) in
      printResult (testFunction1 transformed#isFullyAccessible false);
      printResult (testFunction1 transformed#isFullyProductive true);
    let fullyTransformed =  new ContextFreeGrammarLL1.model (Arg.Representation (List.nth m#clean 1).grammar#representation) in
      printResult (testFunction1 fullyTransformed#isFullyAccessible true);
      printResult (testFunction1 fullyTransformed#isFullyProductive true);
    Printf.printf "]\n"

  let cleanGrammar1 () = 
    Printf.printf "%s" (Printf.sprintf "Clean grammar test 1: [");
    let first = [ ("S", ['a'; 'b']); ("A", ['a'; 'b']); ("B", ['a'; 'b'; 'c']); ("C", ['a'; 'b'; 'c']); ("D", ['d'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', ['a'; 'b'; dollar]); ('A', ['a'; 'b'; 'c'; dollar]); ('B', ['a'; 'b'; 'c'; dollar]); ('C', ['a']); ('D', ['a']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->aSa", ['a']); ("S->bB", ['b']); ("S->bAA", ['b']);
                      ("A->a", ['a']); ("A->SbA", ['a'; 'b']); ("A->aB", ['a']);
                      ("B->AB", ['a'; 'b']); ("B->CaB", ['a'; 'b'; 'c']);
                      ("C->cC", ['c']); ("C->Sa", ['a'; 'b']); ("C->bD", ['b']);
                      ("D->dD", ['d']); ("D->", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text clean_grammar1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive false);
      printResult (testFunction1 m#isLeftFactoring true);
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 m#isFullyAccessible true);
      printResult (testFunction1 m#isFullyProductive false);
    let fullyTransformed =  new ContextFreeGrammarLL1.model (Arg.Representation (List.nth m#clean 1).grammar#representation) in
      printResult (testFunction1 fullyTransformed#isFullyAccessible true);
      printResult (testFunction1 fullyTransformed#isFullyProductive true);
    Printf.printf "]\n"
    
  let testDirectRecursion1 () =
    Printf.printf "Direct recursion test 1: [";
    let first = [ ("A", ['b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', ['a'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("A->Aa", ['b']); ("A->b", ['b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text direct_left_recursion_grammar1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeLeftRecursion.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
    Printf.printf "]\n"

  let testDirectRecursion2 () =
    Printf.printf "Direct recursion test 2: [";
    let first = [ ("B", ['a']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('B', ['b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("B->a", ['a']); ("B->Bb", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text direct_left_recursion_grammar2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeLeftRecursion.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
    Printf.printf "]\n"

  let testIndirectRecursion1 () =
    Printf.printf "Indirect recursion test 1: [";
    let first = [ ("A", ['a']); ("S", ['a']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', [dollar]); ('S', [dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->A", ['a']); ("S->a", ['a']); ("A->S", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text indirect_left_recursion_grammar1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are unit productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
      printResult (testFunction1 transformed#isClean false);
    (*Grammar can be cleaned yet.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation (List.nth transformed#clean 1).grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
      printResult (testFunction1 transformed#isClean true);
    Printf.printf "]\n"
    
  let testIndirectRecursion2 () = (*FIXME Trying to clean grammar right away fails*)
    Printf.printf "Indirect recursion test 2: [";
    let first = [ ("S", ['a']); ("A", ['a']); ("B", ['a']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', [dollar]); ('B', [dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->A", ['a']); ("S->B", ['a']);
                      ("A->a", ['a']);
                      ("B->S", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text indirect_left_recursion_grammar2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are epsilon productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive true);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are unit productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation transformed#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
    (*Grammar can be cleaned yet.*)
      printResult (testFunction1 transformed#isClean false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation (List.nth transformed#clean 1).grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
      printResult (testFunction1 transformed#isClean true);
    Printf.printf "]\n"

  let testIndirectRecursion3 () =
    Printf.printf "Indirect recursion test 3: [";
    let first = [ ("S", ['a'; 'b'; 'c']); ("A", ['a'; epsilon]); ("B", ['b'; epsilon]); ("C", ['c'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a'; 'b'; 'c']); ('B', ['a'; 'b'; 'c']); ('C', ['a'; 'b'; 'c']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->ABCS", ['a'; 'b'; 'c']);
                      ("A->a", ['a']); ("A->", ['a'; 'b'; 'c']); 
                      ("B->b", ['b']); ("B->", ['a'; 'b'; 'c']); 
                      ("C->c", ['c']); ("C->", ['a'; 'b'; 'c']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text indirect_left_recursion_grammar3) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are epsilon productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive true);
      printResult (testFunction1 transformed#isLeftFactoring true);
      printResult (testFunction1 transformed#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are unit productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation transformed#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring true);
      printResult (testFunction1 transformed#isLL1 false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation transformed#leftFactoring.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 false); (*This grammar is not LL(1)*)
    Printf.printf "]\n"
    
  let testIndirectRecursion4 () =
    Printf.printf "Indirect recursion test 4: [";
    let first = [ ("A", ['b'; 'e'; 'g']); ("B", ['b'; 'e'; 'g']); ("C", ['b'; 'e'; 'g']); ("D", ['b'; 'e'; 'g']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', ['a'; dollar]); ('B', ['a']); ('C', ['d'; 'g']); ('D', ['f']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("A->Ba", ['b'; 'e'; 'g']); ("A->b", ['b']);
                      ("B->Cd", ['b'; 'e'; 'g']); ("B->e", ['e']);
                      ("C->Df", ['b'; 'e'; 'g']); ("C->g", ['g']);
                      ("D->Df", ['b'; 'e'; 'g']); ("D->Aa", ['b'; 'e'; 'g']); ("D->Cg", ['b'; 'e'; 'g']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text indirect_left_recursion_grammar4) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeLeftRecursion.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring true);
      printResult (testFunction1 transformed#isLL1 false);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation transformed#leftFactoring.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 false);
    Printf.printf "]\n"

  let testIndirectRecursion5 () =
    Printf.printf "Indirect recursion test 5: [";
    let first = [ ("S", ['a']); ("A", ['a'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a']) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->AS", ['a']);
                      ("A->a", ['a']); ("A->", ['a']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text indirect_left_recursion_grammar5) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#isLeftRecursive true);
      printResult (testFunction1 m#isLeftFactoring false);
      printResult (testFunction1 m#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are epsilon productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive true);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 false);
    (*Left recursion cannot be solved with #removeLeftRecursion. There are unit productions that need to be removed first.*)
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation transformed#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#isLeftRecursive false);
      printResult (testFunction1 transformed#isLeftFactoring false);
      printResult (testFunction1 transformed#isLL1 true);
    Printf.printf "]\n"

  let testLeftFactoring1 () =
    Printf.printf "Left factoring test 1: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 false);
    Printf.printf "]\n"
    
  let testLeftFactoring2 () =
    Printf.printf "Left factoring test 2: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example2) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 false);
    Printf.printf "]\n"
    
  let testLeftFactoring3 () =
    Printf.printf "Left factoring test 3: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example3) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 false);
    Printf.printf "]\n"
    
  let testLeftFactoring4 () =
    Printf.printf "Left factoring test 4: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example4) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 false);
    Printf.printf "]\n"
    
  let testLeftFactoring5 () =
    Printf.printf "Left factoring test 5: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example5) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 true);
    Printf.printf "]\n"
    
  let testLeftFactoring6 () =
    Printf.printf "Left factoring test 6: [";
    let m = new ContextFreeGrammarLL1.model (Arg.Text left_factoring_example6) in
    let transformedM = new ContextFreeGrammarLL1.model (Arg.Representation m#leftFactoring.grammar#representation) in
      printResult (testFunction1 m#isLL1 false);
      printResult (testFunction1 transformedM#isLeftFactoring false);
      printResult (testFunction1 transformedM#isLL1 true);
    Printf.printf "]\n"

  let testUnitRemoval1 () =
    Printf.printf "Unit production removal test 1: [";
    let first = [ ("E", ['a'; 'b']); ("T", ['a'; 'b']); ("F", ['a'; 'b']); ("I", ['a'; 'b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('E', [dollar]); ('T', [dollar]); ('F', [dollar]); ('I', ['a'; 'b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("E->T", ['a'; 'b']);
                      ("T->F", ['a'; 'b']); 
                      ("F->I", ['a'; 'b']);
                      ("I->a", ['a']); ("I->b", ['b']); ("I->Ia", ['a'; 'b']); ("I->Ib", ['a'; 'b'])] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text unit_removal_example1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasUnitProductions true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasUnitProductions false);
    Printf.printf "]\n"

  let testUnitRemoval2 () =
    Printf.printf "Unit production removal test 2: [";
    let first = [ ("A", ['a'; 'b'; 'c']); ("B", ['a'; 'b'; 'c']); ("C", ['a'; 'b'; 'c']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('A', [dollar]); ('B', [dollar]); ('C', [dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("A->B", ['a'; 'b'; 'c']); ("A->a", ['a']);
                      ("B->C", ['a'; 'b'; 'c']); ("B->b", ['b']);
                      ("C->A", ['a'; 'b'; 'c']); ("C->c", ['c'])] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text unit_removal_example2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasUnitProductions true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasUnitProductions false);
    Printf.printf "]\n"

  let testUnitRemoval3 () =
    Printf.printf "Unit production removal test 3: [";
    let first = [ ("S", ['a'; 'b'; 'c']); ("A", ['a'; 'b']); ("B", ['a'; 'b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a'; dollar]); ('B', ['a'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->Aa", ['a'; 'b']); ("S->B", ['a'; 'b']); ("S->c", ['c']);
                      ("A->a", ['a']); ("A->bc", ['b']); ("A->B", ['a'; 'b']); 
                      ("B->A", ['a'; 'b';]); ("B->bb", ['b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text unit_removal_example3) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasUnitProductions true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasUnitProductions false);
    Printf.printf "]\n"

  let testUnitRemoval4 () =
    Printf.printf "Unit production removal test 4: [";
    let first = [ ("S", ['a']); ("A", ['a']); ("B", ['b']); ("C", ['b'; 'd']); ("D", ['b']); ("E", ['b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['b'; 'd']); ('B', [dollar]); ('C', [dollar]); ('D', [dollar]); ('E', [dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->AC", ['a']);
                      ("A->a", ['a']); 
                      ("B->D", ['b']);
                      ("C->B", ['b']); ("C->d", ['d']);
                      ("D->E", ['b']);
                      ("E->b", ['b'])] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text unit_removal_example4) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasUnitProductions true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasUnitProductions false);
    Printf.printf "]\n"
    
  let testUnitRemoval5 () =
    Printf.printf "Unit production removal test 5: [";
    let first = [ ("E", ['a'; 'b'; '(']); ("T", ['a'; 'b'; '(']); ("F", ['a'; 'b'; '(']); ("I", ['a'; 'b']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('E', [')'; '+'; dollar]); ('T', [')'; '*'; '+'; dollar]); ('F', [')'; '*'; '+'; dollar]); ('I', ['0'; 'a'; '1'; 'b'; ')'; '*'; '+'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("E->T", ['a'; 'b'; '(']); ("E->E+T", ['a'; 'b'; '(']);
                      ("T->F", ['a'; 'b'; '(']); ("T->T*F", ['a'; 'b'; '(']); 
                      ("F->I", ['a'; 'b']); ("F->(E)", ['(']);
                      ("I->a", ['a']); ("I->b", ['b']); ("I->Ia", ['a'; 'b']); ("I->Ib", ['a'; 'b']); ("I->I0", ['a'; 'b']); ("I->I1", ['a'; 'b']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text unit_removal_example5) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasUnitProductions true);
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeUnitProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasUnitProductions false);
    Printf.printf "]\n"

  let testEmptyRemoval1 () =
    Printf.printf "Empty production removal test 1: [";
    let first = [ ("S", ['a'; 'b'; 'd']); ("A", ['b'; 'd'; epsilon]); ("B", ['b'; epsilon]); ("C", ['d'; epsilon]); ("D", ['d']) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a'; 'b']); ('B', ['a'; 'b'; 'd']); ('C', ['a'; 'b'; dollar]); ('D', ['a'; 'b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->ABaC", ['a'; 'b'; 'd']);
                      ("A->BC", ['a'; 'b'; 'd']); 
                      ("B->b", ['b']); ("B->", ['a'; 'b'; 'd']);
                      ("C->D", ['d']); ("C->", ['a'; 'b'; dollar]); 
                      ("D->d", ['d']) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text epsilon_removal_example1) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasEmptyProductions true); 
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasEmptyProductions false); 
    Printf.printf "]\n"
    
  let testEmptyRemoval2 () =
    Printf.printf "Empty production removal test 2: [";
    let first = [ ("S", ['a'; 'b'; epsilon]); ("A", ['a'; epsilon]); ("B", ['b'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a'; 'b'; dollar]); ('B', ['b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->AB", ['a'; 'b'; dollar]);
                      ("A->AaA", ['a']); ("A->", ['a'; 'b'; dollar]); 
                      ("B->BbB", ['b']); ("B->", ['b'; dollar]) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text epsilon_removal_example2) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasEmptyProductions true); 
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasEmptyProductions false); 
    Printf.printf "]\n"
    
  let testEmptyRemoval3 () =
    Printf.printf "Empty production removal test 3: [";
    let first = [ ("S", ['a'; 'b'; epsilon]); ("A", ['a'; epsilon]); ("B", ['b'; epsilon]) ] in
    let first2 = firstPairConversion first in
    let follow = [ ('S', [dollar]); ('A', ['a'; 'b'; dollar]); ('B', ['b'; dollar]) ] in
    let follow2 = followPairConversion follow in
    let lookahead = [ ("S->AB", ['a'; 'b'; dollar]);
                      ("A->aAA", ['a']); ("A->", ['a'; 'b'; dollar]); 
                      ("B->bBB", ['b']); ("B->", ['b'; dollar]) ] in
    let lookahead2 = lookaheadPairConversion lookahead in
    let m = new ContextFreeGrammarLL1.model (Arg.Text epsilon_removal_example3) in
      printResult (testFirst m first2);
      printResult (testFollow m follow2);
      printResult (testLookahead m lookahead2);
      printResult (testFunction1 m#hasEmptyProductions true); 
    let transformed = new ContextFreeGrammarLL1.model (Arg.Representation m#removeEmptyProductions.grammar#representation) in
      printResult (testFunction1 transformed#hasEmptyProductions false);
    Printf.printf "]\n"
    ;;
    
	let runAll =
		if Util.testing active "ContextFreeGrammarLL1" then begin
			testExample1 ();
			testExample2 ();
			testExample3 ();
			testExample4 ();
			testExample5 ();
			testExample6 ();
			testDissertation ();
			testNFGrammar ();
			testAccessible1 ();
			testAccessible2 ();
			testProductive1 ();
			testProductive2 ();
			cleanGrammar1 ();
			testDirectRecursion1 ();
			testDirectRecursion2 ();
			testIndirectRecursion1 ();
			testIndirectRecursion2 ();
			testIndirectRecursion3 ();
			testIndirectRecursion4 ();
			testIndirectRecursion5 ();
			testLeftFactoring1 ();
			testLeftFactoring2 ();
			testLeftFactoring3 ();
			testLeftFactoring4 ();
			testLeftFactoring5 ();
			testLeftFactoring6 ();
			testUnitRemoval1 ();
			testUnitRemoval2 ();
			testUnitRemoval3 ();
			testUnitRemoval4 ();
			testUnitRemoval5 ();
			testEmptyRemoval1 ();
			testEmptyRemoval2 ();
			testEmptyRemoval3 ()
		end
end

#endif
