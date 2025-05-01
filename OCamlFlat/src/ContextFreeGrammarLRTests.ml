#ifdef ALL

(*
 * ContextFreeGrammarLRTests.ml
 *
 * This file is part of the OCamlFlat library
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
 *  Written by Bernardo Sousa (br)
 *)

(*
 * ChangeLog:
 *
 * apr/2023 (amd) - New file.
 *)

(*
 * Description: Context-free grammar testing.
 *)
 
open BasicTypes
open ContextFreeGrammarBasic  

module ContextFreeGrammarLRTests : sig end =
struct
	let active = false

	open LR0Grammar
	open SLR1Grammar
	open LR1Grammar
	open LALR1Grammar

	let (lr1grammar:t) = (* basic LR1 with no First usage *)
	{alphabet = symbols "01";
	variables = symbols "SXA" ;
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X"; "X -> A"; "A -> 0" ; "A -> 1"])
	} ;;

	let (lr1grammar2:t) = (* basic LR1 with basic First usage *)
	{alphabet = symbols "01";
	variables = symbols "SXA" ;
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X"; "X -> A01"; "A -> 0" ; "A -> 1"])
	} ;;

	let ttLR1 () = (* Full grammar *)
		makeLR1Diagram lr1grammar;;

	let (lr1grammarX:t) = (* exemplo do professor Luis Monteiro *) 
	{alphabet = symbols "ab";
	variables = symbols "SAB";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> A"; "A -> BA"; "A -> ~" ; "B -> aB"; "B -> b"; ])
	} ;; (* Resumindo esta gramatica: (B)^n, onde B = (a)^m b *)
	(* (a*b)* *)

	let (lr0htmlgrammar:t) = (* teste de html *) 
	{alphabet = symbols "abcde";
	variables = symbols "SABCDE";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> ABCDE"; "A -> a | "; "B -> b | "; "C -> c"; "D -> d | "; "E -> e | "])
	} 

	let ttisLR0 () =
		isLR0 lr0htmlgrammar;;

	let ttLR1X () = (* Full grammar *)
		makeLR1Diagram lr1grammarX;;
		
	let ttLR1Id () = 
		makeLR1DiagramId (makeLR1Diagram lr1grammarX) ;;
		
	let ttLR1Table () =
		makeLR1Table (makeLR1DiagramId (makeLR1Diagram lr1grammarX)) lr1grammarX ;; 
		
	let ttLR1Word () = (* simple test *)
		acceptWordLR1 (word "ab") lr1grammarX ;;
		
		
		
	let ttLR1Word2 () = (* long simple test *)
		acceptWordLR1 (word "bbbbbbbb") lr1grammarX ;;
		
	let ttLR1Word3 () = (* long complex test *)
		acceptWordLR1 (word "aaaaaaaaabbbbbbbb") lr1grammarX ;;
		
	let ttLR1Word4 () = (* empty test *)
		acceptWordLR1 [] lr1grammarX ;;
		
	let ttLR1Word5 () = (* combination test *)
		acceptWordLR1 (word "ababababababababaaaaaaaaabbbbbbbb") lr1grammarX ;;
		
	let ttLR1WordFail () = (* falha mas da erro em vez de false *)
		acceptWordLR1 (word "bbbbbbbba") lr1grammarX ;;
		
		
	(*----- Test functions LALR1-----*)


	let (lalr1grammar:t) = (* basic SLR1 with Follow usage *)
		{alphabet = symbols "cd";
		variables = symbols "SXC";
		initial = symb "S";
		rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X"; "X -> CC"; "X -> ~"; "C -> cC" ; "C -> d"])
	} ;;

	let ttLALR1 () = (* Full grammar *)
		makeLALR1FromLR1 (makeLR1Diagram lalr1grammar);;	
		
	let ttLR1Table () =
		makeLR1Table (makeLR1DiagramId (makeLR1Diagram lalr1grammar)) lalr1grammar ;; 
		
	let ttLALR1Table () =
		makeLR1Table (makeLR1DiagramId (makeLALR1FromLR1 (makeLR1Diagram lalr1grammar))) lalr1grammar ;; 	

	let ttLALR1Word () = (* simple test *)
		acceptWordLALR1 [] lalr1grammar ;;
		
	let ttLALR1Word2 () = (* simple test *)
		acceptWordLALR1 (word "dd" ) lalr1grammar ;;
		
		
	let ttLALR1WordFail () = (* simple test *)
		acceptWordLALR1 (word "cd" )  lalr1grammar ;;
		
	let ttIsLALR1 () = isLALR1 lalr1grammar ;;

	let ttIsLR1 () = isLR1 lalr1grammar ;;

		
		
	(*----- Test functions SLR1-----*)

	let (slr1grammar:t) = (* basic SLR1 with Follow usage *)
		{alphabet = symbols "acdz";
		variables = symbols "SXAB";
		initial = symb "S";
		rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X"; "X -> aAc"; "X -> aBd"; "A -> z" ; "B -> z"])
	} ;;


	let (slr1grammarFail:t) = (* basic SLR1 with Follow usage *)
		{alphabet = symbols "acdz";
		variables = symbols "SXAB";
		initial = symb "S";
		rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X"; "X -> aAd"; "X -> aBd"; "A -> z" ; "B -> z"])
	} ;;

	let ttSLR1Table () =
		makeSLR1Table (makeLR0DiagramId (makeLR0Diagram slr1grammar)) slr1grammar ;; 

	let ttSLR1Word() =
		acceptWordSLR1 (word "azc") slr1grammar ;;
		
	let ttSLR1Word2() =
		acceptWordSLR1 (word "azd") slr1grammar ;;
		
	let ttSLR1WordFail() =
		acceptWordSLR1 (word "") slr1grammar ;;
		
	let ttSLR1WordFail2() =
		acceptWordSLR1 (word "azcd") slr1grammar ;;
		
	let ttSLR1WordFail3() =
		acceptWordSLR1 (word "az") slr1grammar ;;
		
	let ttSLR1WordFail4() =
		acceptWordSLR1 (word "azc$") slr1grammar ;;
		
	let ttIsSLR1() = isSLR1 slr1grammar ;;

	let ttIsSLR1Fail() = isSLR1 slr1grammarFail ;; (* é preciso alterar o follow para testar fails... dor *)
		


	(*----- Test functions LR0-----*)

	let showLR0States (cfg:t) =
		let diagram = makeLR0Diagram cfg in
		let (states,transitions) : lr0Diagram = diagram in
		states
		
	let showLR0Transitions (cfg:t) =
		let diagram = makeLR0Diagram cfg in
		let (states,transitions) : lr0Diagram = diagram in
		transitions


	let (grammar:t) = 
	{alphabet = symbols "01";
	variables = symbols "SX";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 1S0"; "S -> X"; "X -> 0X1" ; "X -> ~"])
	} ;;

	let tt () = (* Full grammar *)
		makeLR0Diagram grammar;;


	let (grammar2:t) = 
	{alphabet = symbols "1";
	variables = symbols "S";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 1"])
	} ;;

	let tt2 () (* Single State Grammar *) =
		makeLR0Diagram grammar2;;
		

	let (grammar3:t)  = 
	{alphabet = symbols "01";
	variables = symbols "S";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 111111"])
	} ;;

	let tt3 () (* Multiple State/Single Rule Grammar *)=
		makeLR0Diagram grammar3;;


	let (grammar4:t)  = 
	{alphabet = symbols "01";
	variables = symbols "S";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 111111"; "S -> 000000"])
	} ;;

	let tt4 () (* Multiple State/Multiple Rule Grammar *) =
		makeLR0Diagram grammar4;;


	let (grammar5:t)  = 
	{alphabet = symbols "01";
	variables = symbols "SA";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 111111"; "S -> 0X1"; "X -> 01" ])
	} ;;

	let (grammar5v2:t) (* Copy to test sorting in sets *) = 
	{alphabet = symbols "01";
	variables = symbols "SA";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 111111"; "S -> 0A1"; "A -> 01" ])
	} ;;

	let tt5 () (* Multiple Variables/Multiple State/Multiple Rule Grammar *) =
		makeLR0Diagram grammar5;;


	let (grammar6:t) = 
	{alphabet = symbols "01";
	variables = symbols "SXA";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> 1X0"; "X -> A"; "A -> 0A1"; "A -> 01"])
	} ;;

	let tt6 () (* Almost Full Grammar\No rule containing only epsilon *) =
		makeLR0Diagram grammar6;;

	let (grammar7:t) = 
	{alphabet = symbols "ab$";
	variables = symbols "SXA";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X$"; "X -> XA"; "X -> A"; "A -> aXb"; "A -> ab"])
	} ;;

	let tt7 () (* Gramática LR0 do exemplo de Luis Monteiro *) =
		makeLR0Diagram grammar7;;

		
	let tt7Count () : bool (* Gramática LR0 do exemplo de Luis Monteiro *) =
		let (a,b) :lr0Diagram = makeLR0Diagram grammar7 in
		if (Set.size a = 9 && Set.size b = 13) then true else false
		
		
	let (grammar7f:t) = 
	{alphabet = symbols "abc$";
	variables = symbols "SXA";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X$"; "X -> XA"; "X -> A"; "A -> aXb"; "A -> ab";"A -> abc"])
	} ;;

	let (grammar7alt:t) = 
	{alphabet = symbols "ab$";
	variables = symbols "SXAF";
	initial = symb "S";
	rules = ContextFreeGrammarBasic.parse (Set.make ["S -> X$"; "X -> XA"; "X -> A"; "A -> aXb"; "A -> ab";"A -> abF"; "F -> FA" ])
	} ;;
		
	let tt7LR0 () (* Gramática LR0 do exemplo de Luis Monteiro *) =
		isLR0 grammar7;;
		
	let ttLR0Fail () (* Deve dar falso devido a dois items completos *) =
		isLR0 grammar7f;;
		
	let ttLR0Alt () (* Devia dar verdadeiro com um item completo e um item incompleto que espera uma variavel, mas na prática isto é impossivel, porque é preciso calcular o fecho para essa variavel, esse fecho novo causa um conflito, a menos que a variavel não tenha uma regra respectiva, sendo nesse caso uma variavel inutil *) =
		isLR0 grammar7alt;;

	let ttIncon1 () = makeLR0Diagram grammar5;;

	let ttIncon2 () = makeLR0Diagram grammar5v2;;


	let ttId () = makeLR0DiagramId (makeLR0Diagram grammar7) ;;
			
	let ttx () =
		makeLR0Table (makeLR0DiagramId (makeLR0Diagram grammar7)) grammar7 ;; 
		
	let ttx2 () =
		makeLR0Table (makeLR0DiagramId (makeLR0Diagram grammar5)) grammar5 ;; 


	let ttWord () = 
		acceptWordLR0V2 (word "1") grammar2 ;;
		
	let ttWordFail () = 
		acceptWordLR0V2 (word "10") grammar2 ;;
		
	let ttWord2 () = 
		acceptWordLR0V2 (word "111111") grammar5 ;;
		
	let ttWord2Fail () = 
		acceptWordLR0V2 (word "1111111") grammar5 ;;	
		
	let ttWord3 () = 
		acceptWordLR0V2 (word "0011") grammar5 ;;
		
	let ttWord3Fail () = 
		acceptWordLR0V2 (word "00111") grammar5 ;;
		
	let ttWord4 () = 
		acceptWordLR0V2 (word "100110") grammar6 ;;
		
	let ttWord4Fail () = 
		acceptWordLR0V2 (word "10011") grammar6 ;;
		
	let ttWordX () =
		acceptWordLR0V2 (word "aaabbb$") grammar7 ;;
		
	let ttWordXFail () =
		acceptWordLR0V2 (word "aaabbb") grammar7 ;;
		
	let tt3LR0 () (* bug test *) =
		isLR0 grammar5;;	
		
	let lr0DiagnosticTest () =
		ttWord() && ttWord2() && ttWord3() && ttWord4() && ttWordX()
		
	let lr0DiagnosticFailTest () =
		ttWordFail() && ttWord2Fail() && ttWord3Fail() && ttWord4Fail() && ttWordXFail()	

	let runAll =
		if Util.testing active "ContextFreeGrammarLR" then begin
			ignore (tt3LR0 ())
		end		
end	

#endif
