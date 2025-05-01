open Examples


(*
type symbol = char
type finiteAutomaton = FiniteAutomatonX.tx
type regularExpression = RegularExpression.tx
type contextFreeGrammar = ContextFreeGrammarBasic.tx
type finiteEnumeration = FiniteEnumeration.tx
*)

(* CHECKING *)

(*

let _: finiteAutomaton =
{
	alphabet = ['a'];
	states = ["START"];
	initialState = "START";
	transitions = [("START", 'a', "START")];
	acceptStates = ["START"]
}

let _: contextFreeGrammar =
{
	alphabet = ['['; ']'];
	variables = ['S'];
	initial = 'S';
	rules = ["S -> [S]"; "S -> SS"; "S -> ~"]
}
*)
