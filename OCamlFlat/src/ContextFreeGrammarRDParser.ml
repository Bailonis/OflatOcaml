#ifdef ALL

open BasicTypes
open ContextFreeGrammarBasic

module RDParser =
struct

  (* given a head, returns the set of all its bodies according to the cfg's rules *)
	let bodiesOfHead h rl =
	  let open ContextFreeGrammarBasic in
		let rls = Set.filter (fun r -> r.head = h) rl in
			Set.map (fun r -> r.body) rls

  let rec tabCreator tabLevel =
    if tabLevel > 0 then "\t"^ tabCreator (tabLevel - 1) else ""

  class virtual parser =
    object(self)

    val arrayVar = "word"
    val currentCharVar = "currentChar"
    val currentIndexVar = "wordIndex"
      
    val getCharFun = "getChar"
    val parseErrorFun = "parseError"
    val matchCharFun = "matchChar"

    val virtual equality : string
    val virtual orOp : string
    val virtual functionArgsOpen : string
    val virtual functionArgsClose : string
    val virtual ifOpen : string 
    val virtual ifClose : string
    val virtual ifElseGuardOpen : string
    val virtual ifElseGuardClose : string
    val virtual expressionTermination : string
    val virtual return : string

    (* Method that will print includes/imports needed for the parser *)
    method virtual setupIncludes : string
    
    
    (* Method used to setup the variables for the parser. *)
  	(* Use values arrayVar, currentCharVar and currentIndexVar *)
  	(* to get correct variable names. *)
    method virtual setupVariables : string
    
    
    (* Method that prints the getCharFunction. *)
    (* This function consumes a symbol while parsing. *)
    method virtual getCharFunction : string
    
    
    (* Method that prints the match function. *)
    (* This function verifies if symbols match. *)
    (* Consumes the symbol if there is a match. *)
    (* Otherwise, calls error function. *)
    method virtual matchFunction : string
    
    
    (* Method that prints the error function. *)
    (* This function exists the program when called symbols match. *)
    method virtual errorFunction : string
    

    method printFunctions vars rep =
      if vars = Set.empty then ""
      else let (x,xs) = Set.cut vars in
        self#symbolFunction x rep ^
        (self#printFunctions xs rep)
 
    (* Method that prints the programs main function. *)
    method virtual mainFunction : symbol -> string
    

    method virtual createFun : string -> string -> string


    (*TODO Move to lower level*)
    method createFunCalls funs (rep: t) =
      match funs with
      | [] -> []
      | x::xs when Set.belongs x rep.alphabet -> [matchCharFun ^ functionArgsOpen ^ "\'" ^ symb2str x ^ "\'" ^ functionArgsClose ^ expressionTermination] @ self#createFunCalls xs rep
      | x::xs when Set.belongs x rep.variables -> [symb2str x ^ functionArgsOpen ^ functionArgsClose ^ expressionTermination] @ self#createFunCalls xs rep
      | x::xs -> []

    (*TODO Move to lower level*)
    method createIfConds conditions =
      let p = String.make 1 '\'' in
      match conditions with
      | [] -> ""
      | [x] -> currentCharVar ^ equality ^ p ^ symb2str x ^ p
      | x::xs -> currentCharVar ^ equality ^ p ^ symb2str x ^ p ^ " " ^ orOp ^ " " ^ self#createIfConds xs
      
    (*TODO Move to lower level*)
    method createIf ifList tabLevel = 
      let rec createIf2 first ifList tabLevel =
        let rec createExpr exprList tabLevel =
          match exprList with 
          | [] -> ""
          | x::xs -> (tabCreator tabLevel) ^ x ^ "\n" ^ createExpr xs tabLevel
        in
        let tab = (tabCreator tabLevel) in
        match ifList with
        | [] -> ""
        | [(c,e)] -> tab ^ "else" ^ ifElseGuardOpen ^ "\n" ^ (createExpr e (tabLevel+1)) ^ tab ^ ifElseGuardClose
        | (c,e)::xs -> tab ^ (if first then "if" else "else if") ^ ifOpen ^ c ^ ifClose ^ ifElseGuardOpen ^ "\n" ^ 
                       (createExpr e (tabLevel+1)) ^
                       tab ^ (ifElseGuardClose) ^ "\n" ^ createIf2 false xs tabLevel
      in
      createIf2 true ifList tabLevel

  
    method symbolFunction s (rep: t) =
      let open ContextFreeGrammarBasic in
      let getNextTerminals rule = 
(*        Printf.printf "\tGetting lookahead for rules";*)
(*        List.iter (fun r -> Printf.printf " %s " r) (CFGSyntax.toStringList (Set.make [rule]));*)
(*        Printf.printf "\n";*)
(*        Set.iter (fun r -> Printf.printf "\tGot result %s\n" (symb2str r)) (ContextFreeGrammarBasic.lookahead rule false rep);*)
        ContextFreeGrammarBasic.lookahead rule false rep
      in

      let rules = Set.filter (fun {head;body} -> head = s) rep.rules in
      let funCalls = (List.map (fun {head;body} -> self#createFunCalls body rep) (Set.toList rules)) in
      let lookaheads = Set.map (getNextTerminals) rules in
      let mergedMap = List.map2 (fun a b -> (self#createIfConds (Set.toList a),b)) (Set.toList lookaheads) funCalls in
(*      Printf.printf "Current Var: %s\n" (symb2str s);*)
(*      List.iter (fun (a,b) -> Printf.printf "\t%s" a;*)
(*                              Printf.printf "\n";*)
(*                              List.iter (fun c -> Printf.printf "\t\t%s\n" c) b*)
(*      ) mergedMap;*)
      let mergedMap = mergedMap @ [("",[(parseErrorFun ^ functionArgsOpen ^ functionArgsClose ^  expressionTermination)])] in
      self#createFun (symb2str s) (self#createIf mergedMap 1)


    method virtual build : t -> string

  end
end


module RDParserWithDeclarations =
struct

  class virtual parser =
    object(self) inherit RDParser.parser as super
    
  end

end


module RDParserWithoutDeclarations =
struct

  class virtual parser =
    object(self) inherit RDParser.parser as super
    
      method build (rep: t) =
        self#setupIncludes ^
        self#setupVariables ^
        self#getCharFunction ^
        self#errorFunction ^
        self#matchFunction ^
        (self#printFunctions rep.variables rep) ^
        (self#mainFunction rep.initial)
    
  end
end


module RDParserNeedFunDeclaration =
struct

  class virtual parser =
    object(self) inherit RDParserWithDeclarations.parser as super
    
      (* Method that prints function declarations *)
      method functionDeclarations vars =
        let rec printDecl vars =
          if vars = Set.empty then ""
          else let (x,xs) = Set.cut vars in
            Printf.sprintf {|void %s();|} (symb2str x) ^ "\n" ^ printDecl xs
          in
      printDecl vars ^ "\n"
    
      method build (rep: t) =
        Util.stripHead (self#setupIncludes ^
        self#setupVariables ^
        self#functionDeclarations rep.variables ^
        self#getCharFunction ^
        self#errorFunction ^
        self#matchFunction ^
        (self#printFunctions rep.variables rep) ^
        (self#mainFunction rep.initial))
    
  end

end


module RDParserNeedRecursiveFunDeclaration =
struct

  class virtual parser =
    object(self) inherit RDParserWithDeclarations.parser as super
    
      method printFunctions vars rep =
        let first = true in
        let rec printFunctionsX vars rep first =
          if vars = Set.empty then ""
          else let (x,xs) = Set.cut vars in
            (if first then "let rec " else "and ") ^
            self#symbolFunction x rep ^
            (printFunctionsX xs rep false)
        in
        printFunctionsX vars rep first
    
      method build (rep: t) =
        Util.stripHead (self#setupIncludes ^
        self#setupVariables ^
        self#getCharFunction ^
        self#errorFunction ^
        self#matchFunction ^
        (self#printFunctions rep.variables rep) ^
        (self#mainFunction rep.initial))
    
  end

end


module RDParserC =
struct

  class parser =
    object(self) inherit RDParserNeedFunDeclaration.parser as super

    val equality = "=="
    val orOp = "||"
    val functionArgsOpen = "("
    val functionArgsClose = ")"
    val ifOpen = "("
    val ifClose = ")"
    val ifElseGuardOpen = "{"
    val ifElseGuardClose = "}"
    val expressionTermination = ";"
    val return = "return"


    method setupIncludes =
  	  Printf.sprintf {|
		\#include <stdio.h>
		\#include <stdlib.h>
		\#include <string.h>
      |}
    
    
    method setupVariables =
      Printf.sprintf {|
		char* %s;
		char %s;
		int %s;
		|} arrayVar currentCharVar currentIndexVar
    
    
    method getCharFunction =
      Printf.sprintf {|
		char %s(){
			return %s[%s++];
		}
      |} (getCharFun) (arrayVar) (currentIndexVar)
    
    
    method matchFunction =
      Printf.sprintf {|
		void %s(char t) {
			if(%s == t) {
				%s = %s();
			}
			else {
				%s();
			}
		}
      |} (matchCharFun) (currentCharVar) (currentCharVar) (getCharFun) (parseErrorFun)
    
    
    method errorFunction = 
      Printf.sprintf {|
		void %s() {
			printf("Error parsing! %s = %%c\n", %s);
			exit(1);
		}
      |} (parseErrorFun) (currentCharVar) (currentCharVar)
    
      
    method mainFunction initialVar = 
      Printf.sprintf {|
		int main(int argc, char* argv[]){
		  char termChar = '$'; 
		  char* tmp = strcat( argv[1], &termChar);
			%s = tmp;
			%s = %s();
			%s();
			if(%s == '$'){
				printf("Parsing OK!\n");
			} else {
				%s();
			}
			return 0;
		}
    |} (arrayVar) (currentCharVar) (getCharFun) (symb2str initialVar) (currentCharVar) (parseErrorFun)
    

    method createFun name contents =
      Printf.sprintf {|
        void %s() {
        %s
        }
      |} name contents

  end
end


module RDParserOCaml =
struct

	let tabCreator = RDParser.tabCreator

  class parser =
    object(self) inherit RDParserNeedRecursiveFunDeclaration.parser as super

    val equality = "="
    val orOp = "||"
    val functionArgsOpen = "("
    val functionArgsClose = ")"
    val ifOpen = "("
    val ifClose = ")"
    val ifElseGuardOpen = "("
    val ifElseGuardClose = ")"
    val expressionTermination = ";"
    val return = "()"
    
    method setupIncludes = ""


    method setupVariables = 
      Printf.sprintf {|
        let %s = ref [||]
        let %s = ref 'l'
        let %s = ref 0
      |} arrayVar currentCharVar currentIndexVar
      
    
    method getCharFunction = 
      Printf.sprintf {|
        let %s() =
          if ( !%s < (Array.length !%s) - 1 )
          then %s := !%s + 1;
          %s := !%s.(!%s)
              |} (getCharFun)
                (currentIndexVar) (arrayVar)
                (currentIndexVar) (currentIndexVar)
                currentCharVar (arrayVar) (currentIndexVar)
        
        
    method createFunCalls funs (rep: t) =
      match funs with
      | [] -> []
      | x::xs when Set.belongs x rep.alphabet -> [matchCharFun ^ functionArgsOpen ^ "\'" ^ (symb2str x) ^ "\'" ^ functionArgsClose ^ expressionTermination] @ self#createFunCalls xs rep
      | x::xs when Set.belongs x rep.variables -> [String.lowercase_ascii (symb2str x) ^ functionArgsOpen ^ functionArgsClose ^ expressionTermination] @ self#createFunCalls xs rep
      | x::xs -> []


    method matchFunction = 
      Printf.sprintf {|
		let %s t =
			if (!%s = t)
			then (%s())
			else (%s())
      |} matchCharFun currentCharVar getCharFun parseErrorFun

      
    method errorFunction = 
      Printf.sprintf {|
		let %s() =
			Printf.printf "Error parsing! %s = %%c\n" !%s;
			exit 1
      |} parseErrorFun currentCharVar currentCharVar


    method createIfConds conditions =
      let p = String.make 1 '\'' in
      match conditions with
      | [] -> ""
      | [x] -> "!" ^ currentCharVar ^ equality ^ p ^ symb2str x ^ p
      | x::xs -> "!" ^ currentCharVar ^ equality ^ p ^ symb2str x ^ p ^ " " ^ orOp ^ " " ^ self#createIfConds xs
      

    method createIf ifList tabLevel = 
      let rec createIf2 first ifList tabLevel =
        let rec createExpr exprList tabLevel =
          match exprList with 
          | [] -> ""
          | x::xs -> (tabCreator tabLevel) ^ x ^ "\n" ^ createExpr xs tabLevel
        in
        let tab = (tabCreator tabLevel) in
        match ifList with
        | [] -> ""
        | [(c,e)] -> tab ^ "else" ^ ifElseGuardOpen ^ "\n" ^ (createExpr e (tabLevel+1)) ^ tab ^ ifElseGuardClose
        | (c,e)::xs -> tab ^ (if first then "if" else "else if") ^ ifOpen ^ c ^ ifClose ^ " then " ^ ifElseGuardOpen ^ "\n" ^ 
                       (createExpr e (tabLevel+1)) ^
                       tab ^ (ifElseGuardClose) ^ "\n" ^ createIf2 false xs tabLevel
      in
      createIf2 true ifList tabLevel
    
    
    method mainFunction i = 
      Printf.sprintf {|
		let explode s = List.init (String.length s) (String.get s)

		let main () =
			%s := Array.of_list (explode Sys.argv.(1));
			%s := Array.append (!%s) ([|'$'|]);
			%s := !%s.(0);
			%s();
			if !%s = '$'
			then Printf.printf "Parsing OK!"
			else %s();
			exit 0

		let _ = main()
	  |} arrayVar arrayVar arrayVar
                  currentCharVar arrayVar
                  (String.lowercase_ascii (symb2str i))
                  currentCharVar
                  parseErrorFun

    method createFun name contents =
      (* Does not need let, inherited class deals with it *)
      Printf.sprintf {|
		%s () =
			%s
      |} (String.lowercase_ascii name) contents

  end
end

module RDParserJava =
struct

  class parser =
    object(self) inherit RDParserWithoutDeclarations.parser as super

    val equality = "=="
    val orOp = "||"
    val functionArgsOpen = "("
    val functionArgsClose = ")"
    val ifOpen = "("
    val ifClose = ")"
    val ifElseGuardOpen = "{"
    val ifElseGuardClose = "}"
    val expressionTermination = ";"
    val return = "return"

    method setupIncludes = ""
    
    method setupVariables =
  	  Printf.sprintf {|
		static char[] %s;
		static char %s;
		static int %s;
      |} arrayVar currentCharVar currentIndexVar
 

    method getCharFunction =
      Printf.sprintf {|
		static char %s() {
			return %s[%s++];
		}
      |} (getCharFun) (arrayVar) (currentIndexVar)
    
    method matchFunction =
      Printf.sprintf {|
		static void %s(char t) {
			if(%s == t)
				%s = %s();
			else %s();
		}
      |} (matchCharFun) (currentCharVar) (currentCharVar) (getCharFun) (parseErrorFun)
    
    
    method errorFunction = 
      Printf.sprintf {|
		static void %s() {
			System.out.println("Error parsing! %s = " + %s);
			System.exit(1);
		}
      |} (parseErrorFun) (currentCharVar) (currentCharVar)


    method mainFunction initialVar = 
      Printf.sprintf {|
		public static void main(String[] args) {
			%s = 0;
			%s = (args[0].toString()+'$').toCharArray(); //Add terminal symbol
			%s = %s();
			%s();
			if(%s == '$')
				System.out.println("Parsing OK!");
			else %s();
		}
    |} currentIndexVar arrayVar (currentCharVar) (getCharFun) (symb2str initialVar) (currentCharVar) (parseErrorFun)


    method createFun name contents =
      Printf.sprintf {|
		static void %s () {
			%s
		}
      |} name contents

	method build (rep: t) =
		"public class Main {" ^
			super#build rep ^
		"}"

  end
end

#endif
