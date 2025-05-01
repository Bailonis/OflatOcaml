(*
 * Composition.ml
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
 *  Written by Carolina Duarte (cd)
 *)

(*
 * ChangeLog:
 *
 *)

(*
 * Description: Composition of models.
 *
 *)

 open BasicTypes

 module Repository = struct 
   type t = CompositionSupport.t
 
   let data : (string * t) list ref = ref []
   
   let exists (name:string) : bool =
     List.mem_assoc name !data 
   
 
   let delete (name:string) : unit =
     data := List.remove_assoc name !data
   
   
   let update (name:string) (model: t) : unit =
     delete name;
     data := (name,model)::!data
 
   let getExample (name:string) : t  =  
       let j = Examples.jsonExample name in
       let kind = JSon.fieldString j "kind" in
         if FiniteAutomaton.kind = kind then
           (FA (FiniteAutomaton.make (Arg.JSon j)))
         else if RegularExpression.kind = kind then
           (RE (RegularExpression.make (Arg.JSon j)))
         else if ContextFreeGrammar.kind = kind then
           (CFG (ContextFreeGrammarBasic.make (Arg.JSon j)))
         else if PushdownAutomaton.kind = kind then
           (PDA (PushdownAutomaton.make (Arg.JSon j)))
         else if TuringMachine.kind = kind then
           (TM (TuringMachine.make (Arg.JSon j)))
         else Error.fatal "test"
       
 
   let get (name:string) : t  =
     try
       List.assoc name !data 
     with Not_found -> getExample name

   let getText (name:string) : string =
    try
      let m = List.assoc name !data in
      match m with
      | Plus (a,b) ->
        JSon.toString (CompositionSupport.toJSon m)
      (*| Intersect (a,b) ->
       
      | Seq (a,b) ->
        
      | Star t ->*)
      | FA fa ->
        JSon.toString (FiniteAutomaton.toJSon fa)
      | RE re ->
        JSon.toString (PolyModel.re2model re)#toJSon
      | CFG cfg ->
        JSon.toString (PolyModel.cfg2model cfg)#toJSon
      | PDA pda ->
        JSon.toString (PolyModel.pda2model pda)#toJSon
      | TM tm ->
        JSon.toString (PolyModel.tm2model tm)#toJSon
      | FAO fao ->
        JSon.toString fao#toJSon 
      | REO reo ->
        JSon.toString reo#toJSon 
      | CFGO cfgo ->
        JSon.toString cfgo#toJSon 
      | PDAO pdao ->
        JSon.toString pdao#toJSon 
      |TMO tmo ->
        JSon.toString tmo#toJSon
      | _ -> Error.fatal "getText"
    with Not_found -> Examples.example name
 end
 
 (*not use
 module Repository2 = struct 
 
   type 'a t = (string * 'a) list
   let rep: 'a t = []
 
   let r = ref rep
 
   let f (x: 'a t) = x
 
   let exists (name:string) : bool = 
     List.exists (fun (n,_) -> n=name) !r
   
   let get (name:string) =
     let c = List.find_opt (fun (n,_) -> n = name) !r in
     match c with
       | None -> None
       | Some (n,m) -> Some m
 
   let delete (name:string) =
     r := List.filter (fun (n,_) -> n != name) !r
 
 
   let update (name:string) (model: 'a) =
     delete (name);
     r := (name,model)::!r
   end*)
 
 
 module Composition =
 struct
 
   include CompositionSupport
 
 
 
 (*let repository : t Repository.t ref = ref [] 
 
   let xx = 
     repository := Repository.update "ola" (Rep "ole")*)
 
 
   (* example *)
   let fa_empty = {| {
       kind : "finite automaton",
       description : "empty finite automaton",
       name : "fa_empty",
       alphabet: ["a"],
       states : ["START"],
       initialState : "START",
       transitions : [
         ["START", "a", "START"]
       ],
       acceptStates : []
       } |}
 
   let emptyFA =
     FiniteAutomaton.make (Arg.Text fa_empty)
 
 
 
 
   (** aux *)
   let rec decompositions l =
     match l with
       [] -> [([], [])]
       | x::xs -> let lp = decompositions xs in
         ([], l) :: List.map (fun (a,b) -> (x::a,b)) lp
   ;;
 
 
   (* Try to recognize a word *)
   let rec accept (c: t) (w: word) : bool =
     match c with
     | Plus (a,b) ->
       accept a w || accept b w
     | Intersect (a,b) ->
       accept a w && accept b w
     | Seq (a,b) ->
       let list = Set.make(decompositions w) in
       Set.exists (fun (p0,p1) -> (accept a p0) && (accept b p1)) list
       (*false*)
     | Star t ->
       w = []
       || (let list = Set.remove ([],w) (Set.make(decompositions w)) in
           Set.exists (fun (p0,p1) -> (accept t p0) && (accept (Star t) p1)) list)
       (*false*)
     | FA fa ->
       FiniteAutomaton.accept fa w
     | RE re ->
       RegularExpressionPrivate.accept re w
     | CFG cfg ->
       ContextFreeGrammarBasic.accept cfg w
     | PDA pda ->
       PushdownAutomaton.accept pda w
     | TM tm ->
       TuringMachine.accept tm w
     | FAO fao ->
         FiniteAutomaton.accept fao#representation w 
     | REO reo ->
         RegularExpressionPrivate.accept reo#representation w
     | CFGO cfgo ->
         ContextFreeGrammarBasic.accept cfgo#representation w
     | PDAO pdao ->
         PushdownAutomaton.accept pdao#representation w
     |TMO tmo ->
         TuringMachine.accept tmo#representation w
     |Rep rep ->
      (try
        let m = Repository.get rep in
          accept m w
      with Not_found -> Error.fatal "Composition with invalid repository name")
       
     | _ -> Error.fatal "accept"
       
   (* Concat  *)
   let concatAllS w s =
     Set.map (fun l -> w@l) s
 
 
   (* Generate all the accepted word with maximum length *)
   let rec generate (c: t) (len: int) : words =
     match c with
     | Plus (a,b) ->
       Set.union (generate a len)  (generate b len)
     | Intersect (a,b) ->
       Set.inter (generate a len) (generate b len)
     | Seq (a,b) ->
       let left = generate a len in
       let rigth w = generate b (len - (List.length w)) in
       let conc w = concatAllS w (rigth w) in
         Set.flatMap (fun lw -> conc lw) left
     
     | Star t ->
       let exp = generate t len in
         Set.star exp len
     | FA fa ->
       FiniteAutomaton.generate fa len
     | RE re ->
       RegularExpressionPrivate.generate re len
     | CFG cfg ->
       ContextFreeGrammarBasic.generate cfg len
     | PDA pda ->
       PushdownAutomaton.generate len pda
     | TM tm ->
       TuringMachine.generate tm len
     | FAO fao ->
         FiniteAutomaton.generate fao#representation len 
     | REO reo ->
         RegularExpressionPrivate.generate reo#representation len
     | CFGO cfgo ->
         ContextFreeGrammarBasic.generate cfgo#representation len
     | PDAO pdao ->
         PushdownAutomaton.generate len pdao#representation
     |TMO tmo ->
         TuringMachine.generate tmo#representation len
     |Rep rep ->
      (try
        let m = Repository.get rep in
          generate m len
      with Not_found -> Error.fatal "Composition with invalid repository name")
     | _ -> Error.fatal "generate"
 
     (* Adds a sufix to a state name *)
     let addSufixFA (st: state)(sufix: string): state =
       str2state ((state2str st)^"_"^sufix)  
 
     (* Adds a sufix to a variable name name *)
     let addSufixCFG (v: symbol)(sufix: string): symbol =
       str2symb((symb2str v)^"_"^sufix)
     
 
     (* Renames all the states in one automaton adding a sufix *)	
     let renameStatesFA(fa: FiniteAutomaton.t) (sufix: string): FiniteAutomaton.t =
 
       {
         alphabet = fa.alphabet; 
         states = Set.map (fun st -> addSufixFA st sufix) fa.states;
         initialState = addSufixFA fa.initialState sufix;
         transitions = Set.map (fun (s1,sy,s2) -> (addSufixFA s1 sufix,sy,addSufixFA s2 sufix)) fa.transitions;
         acceptStates = Set.map (fun st -> addSufixFA st sufix) fa.acceptStates
       }
 
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
     
     let renameStatesPDA (pda: PushdownAutomaton.t) (sufix: string): PushdownAutomaton.t =
       
       {
         inputAlphabet = pda.inputAlphabet;
         stackAlphabet = Set.map (fun s -> addSufixCFG s sufix) pda.stackAlphabet;
         states = Set.map (fun st -> addSufixFA st sufix) pda.states;
         initialState = addSufixFA pda.initialState sufix;
         initialStackSymbol = addSufixCFG pda.initialStackSymbol sufix;
         transitions = Set.map (fun (q1,s1,sy,q2,s2) -> (addSufixFA q1 sufix,addSufixCFG s1 sufix,sy,addSufixFA q2 sufix,addSufixList s2 sufix )) pda.transitions;
         acceptStates = Set.map (fun st -> addSufixFA st sufix) pda.acceptStates;
         criteria = true
       }
 
     let renameStatesTM (tm: TuringMachine.t) (sufix: string): TuringMachine.t =
       {
       entryAlphabet = tm.entryAlphabet;
       tapeAlphabet = tm.tapeAlphabet;
       empty = empty;
       states = Set.map (fun st -> addSufixFA st sufix) tm.states;
       initialState = addSufixFA tm.initialState sufix;
       transitions = Set.map (fun (s1,symb1,s2,symb2,d) -> (addSufixFA s1 sufix,symb1,addSufixFA s2 sufix,symb2,d )) tm.transitions;
       acceptStates = Set.map (fun st -> addSufixFA st sufix) tm.acceptStates;
       criteria = true;
       markers = tm.markers
     }
   
 
   
     let rec rename (c: t): t =
     match c with
     | Plus (a,b) ->
         Plus(rename a,rename b)
     | Seq (a,b) ->
         Seq(rename a,rename b)
     | Intersect (a,b) ->
         Intersect(rename a,rename b)
     | Star t ->
         Star(rename t)
     | FA fa ->
         FA (renameStatesFA fa (IdGenerator.gen("")))
     | RE re ->
       RE re
     | CFG cfg ->
       CFG (renameVariablesCFG cfg (IdGenerator.gen("")))
     | PDA pda ->
       PDA (renameStatesPDA pda (IdGenerator.gen("")))
     | TM tm ->
       TM (renameStatesTM tm (IdGenerator.gen("")))
     | _ -> Error.fatal "rename"
     
 
     (* calculate a composite finite automaton resulting from a plus operation *)	
     let evalPlusFA (fa: FiniteAutomaton.t) 
                   (fb: FiniteAutomaton.t): FiniteAutomaton.t = 
 
       let qI = str2state (IdGenerator.gen("q")) in
       let ta = (qI, epsilon,fa.initialState) in
       let tb = (qI,epsilon,fb.initialState) in
       {
         alphabet = Set.union fa.alphabet fb.alphabet; 
         states = Set.add qI (Set.union fa.states fb.states);
         initialState = qI;
         transitions = Set.add tb (Set.add ta (Set.union fa.transitions fb.transitions));
         acceptStates = Set.union fa.acceptStates fb.acceptStates
       }
 
     (* Creates a transition between two states in a Finite Automata*)
     let addTransitionFA firstState secondState =
       (firstState, epsilon,secondState) 
 
     (* calculate a composite finite automaton resulting from a sequence operation *)	
     let evalSeqFA (fa: FiniteAutomaton.t) (fb: FiniteAutomaton.t): FiniteAutomaton.t = 
         
       let t = Set.map (fun st -> addTransitionFA st fb.initialState) fa.acceptStates in
       {
         alphabet = Set.union fa.alphabet fb.alphabet; 
         states = Set.union fa.states fb.states;
         initialState = fa.initialState;
         transitions = Set.union t (Set.union fa.transitions fb.transitions);
         acceptStates = fb.acceptStates
       }
 
 
     (*Transforms 2 strings in one string *)
     let makeName2 a b = a^"_#_"^b
 
     (*finds the transions for the 2 states and symbol of the alphabet*)
     let findTransitions a b s transA transB  : FiniteAutomaton.transition3 set = 
 
       let ab = makeName2 a b in
 
       let at = Set.filter (fun (x,s1,y) -> x = a && s1 = s  ) transA in
 
       let bt = Set.filter (fun (x,s1,y) -> x = b && s1 = s  ) transB in
 
       let abt = Set.product at bt in
 
       Set.map (fun ((x1,s1,y1),(x2,s2,y2)) -> (ab,s,makeName2 y1 y2)) abt
 
     let createEmptyTransition a b transA transB  : FiniteAutomaton.transition3 set = 
 
       let ab = makeName2 a b in
       let at = Set.filter (fun (x,s,y) -> x = a && s = epsilon ) transA in
       let bt = Set.filter (fun (x,s,y) -> x = b && s = epsilon ) transB in
       let abt = Set.product at bt in
 
       let emptyAB = Set.map (fun ((x1,s1,y1),(x2,s2,y2)) -> (ab,epsilon,makeName2 y1 y2)) abt in
       let emptyA = Set.map (fun (x,s,y) -> ab,epsilon,makeName2 y b) at in
       let emptyB = Set.map (fun (x,s,y) -> ab,epsilon,makeName2 a y) bt in
 
       Set.union emptyAB (Set.union emptyA emptyB)
 
 
 
     (*performs findTransitions for every symbol of the alphabet*)
     let findTransitions2 a b  transA transB alphabet  : FiniteAutomaton.transition3 set = 
 
       let t = Set.flat_map (fun s -> findTransitions a b s transA transB) alphabet in
       let emptyt = createEmptyTransition a b transA transB in
       Set.union t emptyt
 
     (* calculate a composite finite automaton resulting from a intersection operation *)	
     let evalIntersectFA (fa: FiniteAutomaton.t) (fb: FiniteAutomaton.t): FiniteAutomaton.t =
 
       let s = Set.product fa.states fb.states in
       let newAlphabet = Set.inter fa.alphabet fb.alphabet in
       let trans = Set.flat_map (fun (a,b) -> findTransitions2 a b fa.transitions fb.transitions newAlphabet ) s in
       let newStates = Set.map (fun (a,b) -> makeName2 a b) s in
       let s1 = Set.product fa.acceptStates fb.acceptStates in
       let newAccept = Set.map (fun (a,b)  -> makeName2 a b) s1 in
       {
         alphabet = newAlphabet; 
         states =  newStates;
         initialState = makeName2 fa.initialState fb.initialState;
         transitions =  trans;
         acceptStates = newAccept
       }
 
 
     (* calculate a composite finite automaton resulting from a star operation *)	
     let evalStarFA (ft: FiniteAutomaton.t) : FiniteAutomaton.t = 
         
       let qI = str2state (IdGenerator.gen("q")) in
       let ta = (qI, epsilon,ft.initialState) in
       let t = Set.map (fun st -> addTransitionFA st ft.initialState) ft.acceptStates in
       {
         alphabet = ft.alphabet; 
         states = Set.add qI ft.states;
         initialState = qI;
         transitions = Set.add ta (Set.union t ft.transitions);
         acceptStates = Set.add ft.initialState ft.acceptStates
       }
 
 
     
      
   
   (* calculate a composite finite automaton *)
   (*Pre: c already renamed*)
   let rec calcEvalFA (c: t): FiniteAutomaton.t =
     match c with
     | Plus (a,b) ->
         let fa = calcEvalFA a in 
         let fb = calcEvalFA b in
           evalPlusFA fa fb
     | Seq (a,b) ->
         let fa = calcEvalFA a in
         let fb = calcEvalFA b in
         evalSeqFA fa fb	
     | Intersect (a,b) ->
       let fa = calcEvalFA a in
       let fb = calcEvalFA b in
       evalIntersectFA fa fb
     | Star t ->
         let ft = calcEvalFA t in
         evalStarFA ft
     | FA fa ->
       fa
     |  _ ->
       Error.fatal "calcEvalFA"
 
 
   (* calculate a composite regular expression resulting from a plus operation *)	
   let evalPlusRE (ra: RegularExpression.t) (rb: RegularExpression.t) : RegularExpression.t =
     Plus(ra, rb)
 
   
 
   (* calculate a composite regular expression resulting from a sequence operation *)	
   let evalSeqRE (ra: RegularExpression.t) (rb: RegularExpression.t) : RegularExpression.t =
     Seq(ra, rb)
 
   
   (* calculate a composite regular expression resulting from a intersection operation *)	
   let evalIntersectRE (ra: RegularExpression.t) (rb: RegularExpression.t) : RegularExpression.t =
     let fa = PolyBasic.re2fa ra in
     let fb = PolyBasic.re2fa rb in
     let faComp = evalIntersectFA fa fb in
      PolyBasic.fa2re faComp
 
   (* calculate a composite regular expression resulting from a star operation *)	
   let evalStarRE (rt: RegularExpression.t) : RegularExpression.t =
     Star rt
 
   (* calculate a composite Regular Expression *)
   let rec calcEvalRE (c: t): RegularExpression.t =
     match c with
     | Plus (a,b) ->
         let ra = calcEvalRE a in 
         let rb = calcEvalRE b in
           evalPlusRE ra rb
     | Seq (a,b) ->
         let ra = calcEvalRE a in
         let rb = calcEvalRE b in
         evalSeqRE ra rb
     | Intersect (a,b) ->
       let ra = calcEvalRE a in
       let rb = calcEvalRE b in
       evalIntersectRE  ra rb
     | Star t ->
         let rt = calcEvalRE t in
         evalStarRE rt
     | RE re ->
       re
     |  _ ->
       Error.fatal "calcEvalRE"
 
 
   (* calculate a composite context free grammar resulting from a plus operation *)	
   let evalPlusCFG (ca: ContextFreeGrammarBasic.t) (cb: ContextFreeGrammarBasic.t) : ContextFreeGrammarBasic.t =
 
     let open ContextFreeGrammarBasic in 
      let s =  str2symb (IdGenerator.gen("s")) in
     let r1 = {head = s; body = [ca.initial]} in
     let r2 = {head = s; body = [cb.initial]} in
     {alphabet = Set.union ca.alphabet cb.alphabet;
     variables =	Set.add s (Set.union ca.variables cb.variables);
     initial = s;
     rules = Set.add r1 (Set.add r2 (Set.union ca.rules cb.rules))
     }
   
 
 
   (* calculate a composite context free grammar resulting from a sequence operation *)	
   let evalSeqCFG (ca: ContextFreeGrammarBasic.t) (cb: ContextFreeGrammarBasic.t) : ContextFreeGrammarBasic.t =
 
     let open ContextFreeGrammarBasic in 
      let s =  str2symb (IdGenerator.gen("s")) in
     let r1 = {head = s; body = [ca.initial; cb.initial]} in
     {alphabet = Set.union ca.alphabet cb.alphabet;
     variables =	Set.add s (Set.union ca.variables cb.variables);
     initial = s;
     rules =Set.add r1 (Set.union ca.rules cb.rules)
     }
   
 
   (* calculate a composite context free grammar resulting from a star operation *)	
   let evalStarCFG (ct: ContextFreeGrammarBasic.t)  : ContextFreeGrammarBasic.t =
 
     let open ContextFreeGrammarBasic in 
      let s =  str2symb (IdGenerator.gen("s")) in
     let r1 = {head = s; body = [s;ct.initial]} in
     let r2 = {head = s; body = [epsilon]} in
     {alphabet = ct.alphabet;
     variables =	Set.add s ct.variables;
     initial = s;
     rules = Set.add r1 (Set.add r2 ct.rules)
     }		
 
   (* calculate a composite Context Free Grammar *)
   let rec calcEvalCFG (c: t): ContextFreeGrammarBasic.t =
     match c with
     | Plus (a,b) ->
         let ca = calcEvalCFG a in 
         let cb = calcEvalCFG b in
         evalPlusCFG ca cb
     | Seq (a,b) ->
         let ca = calcEvalCFG a in
         let cb = calcEvalCFG b in
         evalSeqCFG ca cb	
     | Star t ->
         let ct = calcEvalCFG t in
         evalStarCFG ct
     | CFG cfg ->
       cfg
     |  _ ->
       Error.fatal "calcEvalCFG"
 
 
   (* calculate a composite pushdown automata resulting from a plus operation *)	
   let evalPlusPDA (pa: PushdownAutomaton.t) (pb: PushdownAutomaton.t) : PushdownAutomaton.t =
     
     let qI = str2state (IdGenerator.gen("q")) in
     let sI = str2symb (IdGenerator.gen("s")) in
     let t1 = (qI,sI,epsilon,pa.initialState,[pa.initialStackSymbol]) in
     let t2 = (qI,sI,epsilon,pb.initialState,[pb.initialStackSymbol]) in
     {
       inputAlphabet = Set.union pa.inputAlphabet pb.inputAlphabet;
       stackAlphabet = Set.add sI (Set.union pa.stackAlphabet pb.stackAlphabet);
       states = Set.add qI (Set.union pa.states pb.states);
       initialState = qI;
       initialStackSymbol = sI;
       transitions = Set.add t2 (Set.add t1 (Set.union pa.transitions pb.transitions));
       acceptStates = Set.union pa.acceptStates pb.acceptStates;
       criteria = true
     }
 
   (* Creates a transition between two states in a pushdowm automata *)
   let addTransitionPDA firstState secondState stackSymbol symbolstackAlphabet =
       
     Set.map(fun s -> (firstState,s,epsilon,secondState, [stackSymbol])) symbolstackAlphabet
     
   
   (* calculate a composite pushdown automata resulting from a sequence operation *)	
   let evalSeqPDA (pa: PushdownAutomaton.t) (pb: PushdownAutomaton.t) : PushdownAutomaton.t =
     
     let t = Set.flatten (Set.map (fun st -> addTransitionPDA st pb.initialState pb.initialStackSymbol pb.stackAlphabet) pa.acceptStates) in
     {
       inputAlphabet = Set.union pa.inputAlphabet pb.inputAlphabet;
       stackAlphabet = Set.union pa.stackAlphabet pb.stackAlphabet;
       states = Set.union pa.states pb.states;
       initialState = pa.initialState;
       initialStackSymbol = pa.initialStackSymbol;
       transitions = Set.union t (Set.union pa.transitions pb.transitions);
       acceptStates = pb.acceptStates;
       criteria = true
     }
 
 
   (* calculate a composite pushdown automata resulting from a star operation *)	
   let evalStarPDA (pt: PushdownAutomaton.t)  : PushdownAutomaton.t =
     
     let qI = str2state (IdGenerator.gen("q")) in
     let sI = str2symb (IdGenerator.gen("s")) in
     let t1 = (qI,sI,epsilon,pt.initialState,[pt.initialStackSymbol]) in
     let t = Set.flatten (Set.map (fun st -> addTransitionPDA st pt.initialState pt.initialStackSymbol pt.stackAlphabet) pt.acceptStates) in
     {
       inputAlphabet = pt.inputAlphabet;
       stackAlphabet = pt.stackAlphabet;
       states = pt.states;
       initialState = qI;
       initialStackSymbol = sI;
       transitions = Set.add t1 (Set.union t pt.transitions);
       acceptStates = Set.add pt.initialState pt.acceptStates;
       criteria = true
     }
 
 
 
   (* calculate a composite Pushdown Automata *)
   let rec calcEvalPDA (c: t): PushdownAutomaton.t =
     match c with
     | Plus (a,b) ->
         let pa = calcEvalPDA a in 
         let pb = calcEvalPDA b in
         evalPlusPDA pa pb
     | Seq (a,b) ->
         let pa = calcEvalPDA a in
         let pb = calcEvalPDA b in
         evalSeqPDA pa pb
     | Star t ->
         let pt = calcEvalPDA t in
         evalStarPDA pt
     | PDA pda ->
       pda
     |  _ ->
       Error.fatal "calcEvalPDA";;
 
   (* calculate a composite turing machine resulting from a plus operation *)	
   let evalPlusTM (ta: TuringMachine.t) (tb: TuringMachine.t): TuringMachine.t =
 
     let qI = str2state (IdGenerator.gen("q")) in
     let t1 = (qI,empty,ta.initialState,empty,R) in
     let t2 = (ta.initialState,empty,ta.initialState,empty,L) in
     let t3 = (qI,empty,tb.initialState,empty,R) in
     let t4 = (tb.initialState,empty,tb.initialState,empty,L) in
     let t = Set.make [t1;t2;t3;t4] in
     {
       entryAlphabet = Set.union ta.entryAlphabet tb.entryAlphabet;
       tapeAlphabet = Set.union ta.tapeAlphabet tb.tapeAlphabet;
       empty = empty;
       states = Set.add qI (Set.union ta.states tb.states);
       initialState = qI;
       transitions = Set.union t (Set.union ta.transitions tb.transitions);
       acceptStates = Set.union ta.acceptStates tb.acceptStates;
       criteria = true;
       markers = ta.markers
     }
 
   
 
   (* Creates a transition between two states in a Turing Machine*)
   let addTransitionTM firstState secondState tapeAlphabetTA =
       
     Set.map(fun s -> (firstState,s,secondState,s,R)) tapeAlphabetTA
 
   (* calculate a composite turing machine resulting from a sequence operation *)	
   let evalSeqTM (ta: TuringMachine.t) (tb: TuringMachine.t): TuringMachine.t =
 
     let t = Set.flatten (Set.map (fun st -> addTransitionTM st tb.initialState ta.tapeAlphabet) ta.acceptStates) in
     
     {
       entryAlphabet = Set.union ta.entryAlphabet tb.entryAlphabet;
       tapeAlphabet = Set.union ta.tapeAlphabet tb.tapeAlphabet;
       empty = empty;
       states = Set.union ta.states tb.states;
       initialState = ta.initialState;
       transitions = Set.union t (Set.union ta.transitions tb.transitions);
       acceptStates = tb.acceptStates;
       criteria = true;
       markers = ta.markers
     }
 
   (* calculate a composite turing machine resulting from a star operation *)	
   let evalStarTM (tt: TuringMachine.t) : TuringMachine.t =
     let t = Set.flatten (Set.map (fun st -> addTransitionTM st tt.initialState tt.tapeAlphabet) tt.acceptStates) in
     
     {
       entryAlphabet = tt.entryAlphabet;
       tapeAlphabet = tt.tapeAlphabet;
       empty = empty;
       states = tt.states;
       initialState = tt.initialState;
       transitions = Set.union t tt.transitions;
       acceptStates = tt.acceptStates;
       criteria = true;
       markers = tt.markers
     }
   
   (* Auxiliar function *)
   let direction2direction3 dir : direction3 = if dir = L then L else R
   (*creates the transions for the 2 states *)
   let createsTransitions (a: state) (b: state) (transA: TuringMachine.transitions) (transB: TuringMachine.transitions)  : TurMachMultiTypes.transition set = 
 
     let ab = makeName2 a b in
 
     let at = Set.filter (fun (sa,x,s,y,d) -> sa = a ) transA in
 
     let bt = Set.filter (fun (sb,x,s,y,d) -> sb = b ) transB in
 
     let abt = Set.product at bt in
 
     Set.map (fun ((sa,x1,s1,y1,d1),(sb,x2,s2,y2,d2)) -> (ab,[x1;x2],makeName2 s1 s2,[y1;y2],[direction2direction3 d1; direction2direction3 d2])) abt
 
   
   let evalIntersectTM (ta: TuringMachine.t) (tb: TuringMachine.t): TurMachMultiTypes.t =
 
     let s = Set.product ta.states tb.states in
     let newEntryAlphabet = Set.inter ta.entryAlphabet tb.entryAlphabet in
     let trans = Set.flat_map (fun (a,b) -> createsTransitions a b ta.transitions tb.transitions ) s in
     let newStates = Set.map (fun (a,b) -> makeName2 a b) s in
     let acceptS = Set.product ta.acceptStates tb.acceptStates in
     let newAccept = Set.map (fun (a,b)  -> makeName2 a b) acceptS in
 
     {
       entryAlphabet = newEntryAlphabet;
       tapeAlphabet = Set.union ta.tapeAlphabet tb.tapeAlphabet;
       empty = empty;
       states = newStates;
       initialState = makeName2 ta.initialState tb.initialState;
       transitions = trans;
       acceptStates = newAccept;
       criteria = true; (* true = acceptStates | false = stop *)
       markers = ta.markers
     }
 
   (* calculate a composite Turing Machine *)
   let rec calcEvalTM (c: t): TuringMachine.t =
     match c with
     | Plus (a,b) ->
         let ta = calcEvalTM a in 
         let tb = calcEvalTM b in
         evalPlusTM ta tb
     | Seq (a,b) ->
         let ta = calcEvalTM a in
         let tb = calcEvalTM b in
         evalSeqTM ta tb
    (*| Intersect (a,b)->
         let ta = calcEvalTM a in
         let tb = calcEvalTM b in
         evalIntersectTM ta tb*)
     | Star t ->
         let tt = calcEvalTM t in
         evalStarTM tt
     | TM tm ->
       tm
     |  _ ->
       Error.fatal "calcEvalTM"
 
 
   (* tranforms a composition of elements to a composition of finite automaton *)
   (*Pre: c isFAConvertivel*)		
   let rec comp2facomp (c: t): t =
     match c with
       | Plus (a,b) ->
           Plus (comp2facomp a, comp2facomp b)
       | Seq (a,b) ->
           Seq (comp2facomp a, comp2facomp b)
       | Intersect (a,b) ->
           Intersect (comp2facomp a, comp2facomp b)
       | Star t ->
           Star (comp2facomp t)
       | FA fa ->
           FA fa
       | RE re ->
           FA (PolyBasic.re2fa re)
       | CFG cfg ->
         FA (PolyBasic.cfg2fa cfg)			
       | PDA pda ->
         FA (PolyBasic.pda2fa pda)
       | TM tm ->
         let tmobj = new TuringMachine.model (Representation tm) in
         FA (tmobj#downgradeModelToFiniteAutomaton)#representation	
       | _ -> Error.fatal "comp2facomp"
 
   
 
   (* tranforms a composition of elements to a composition of regular expressions *)
   (*Pre: c isREConvertivel*)		
   let rec comp2recomp (c: t): t =
     match c with
       | Plus (a,b) ->
           Plus (comp2recomp a, comp2recomp b)
       | Seq (a,b) ->
           Seq (comp2recomp a, comp2recomp b)
       | Intersect (a,b) ->
           Intersect (comp2recomp a, comp2recomp b)
       | Star t ->
           Star (comp2recomp t)
       | RE re ->
           RE re
       | FA fa ->
           RE (PolyBasic.fa2re fa)
       | CFG cfg ->
           RE (PolyBasic.cfg2re cfg)
       | PDA pda ->
           RE (PolyBasic.pda2re pda)
       | TM tm ->
         let tmobj = new TuringMachine.model (Representation tm) in
         RE (PolyModel.fa2re (tmobj#downgradeModelToFiniteAutomaton))#representation			
       | _ -> Error.fatal "comp2recomp"
     
   (* tranforms a composition of elements to a composition of Context Free Grammar *)
   (*Pre: c isCFGConvertivel*)		
   let rec comp2CFGcomp (c: t): t =
     match c with
       | Plus (a,b) ->
           Plus (comp2CFGcomp a, comp2CFGcomp b)
       | Seq (a,b) ->
           Seq (comp2CFGcomp a, comp2CFGcomp b)
       | Intersect (a,b) ->
           Intersect (comp2CFGcomp a, comp2CFGcomp b)
       | Star t ->
           Star (comp2CFGcomp t)
       | CFG cfg ->
           CFG cfg 
       | PDA pda ->
           CFG (PolyBasic.pda2cfg pda)
       | FA fa ->
           CFG (PolyBasic.fa2cfg fa)
       | RE re ->
           CFG (PolyBasic.re2cfg re)
       | _ -> Error.fatal "comp2CFGcomp"
 
   (* tranforms a composition of elements to a composition of Pushdown Automata *)
   (*Pre: c isPDAConvertivel*)		
   let rec comp2PDAcomp (c: t): t =
     match c with
       | Plus (a,b) ->
           Plus (comp2PDAcomp a, comp2PDAcomp b)
       | Seq (a,b) ->
           Seq (comp2PDAcomp a, comp2PDAcomp b)
       | Intersect (a,b) ->
           Intersect (comp2PDAcomp a, comp2PDAcomp b)
       | Star t ->
           Star (comp2PDAcomp t)
       | CFG cfg ->
           PDA (PolyBasic.cfg2pda cfg)
       | PDA pda ->
           PDA pda
       | FA fa ->
           PDA (PolyBasic.fa2pda fa)		
       | RE re ->
           PDA (PolyBasic.re2pda re)				
       | _ -> Error.fatal "comp2PDAcomp"
   
   (* tranforms a composition of elements to a composition of Turing Machine*)
   (*Pre: c isTMConvertivel*)		
   let rec comp2TMcomp (c: t): t =
     match c with
       | Plus (a,b) ->
           Plus (comp2TMcomp a, comp2TMcomp b)
       | Seq (a,b) ->
           Seq (comp2TMcomp a, comp2TMcomp b)
       | Intersect (a,b) ->
           Intersect (comp2TMcomp a, comp2TMcomp b)
       | Star t ->
           Star (comp2TMcomp t)
       | CFG cfg ->
           TM (PolyBasic.cfg2tm cfg)					
       | PDA pda ->
           TM (PolyBasic.pda2tm pda)	
       | FA fa ->
           TM (PolyBasic.fa2tm fa)	
       | RE re ->
           TM (PolyBasic.re2tm re)
       | TM tm ->
         TM tm			
       | _ -> Error.fatal "comp2PDAcomp"
       
   
   (* calculate a composition of elements into a finite automaton *)
   let evalMixFA (c:t) : FiniteAutomaton.t = 
     let c1  = comp2facomp c in
     let c2 = rename c1 in
     calcEvalFA c2
 
   (* calculate a composition of elements into a Regular Expression *)
   let evalMixRE (c:t) : RegularExpression.t = 
     let c1  = comp2recomp c in
     calcEvalRE c1
 
   (* calculate a composition of elements into a Context Free Grammar *)
   let evalMixCFG (c:t) : ContextFreeGrammarBasic.t = 
     let c1  = comp2CFGcomp c in
     calcEvalCFG c1
 
   (* calculate a composition of elements into a Pushdown Automata *)
   let evalMixPDA (c:t) : PushdownAutomaton.t = 
     let c1  = comp2PDAcomp c in
     calcEvalPDA c1
 
   (* calculate a composition of elements into a Turing Machine *)
   let evalMixTM (c:t) : TuringMachine.t = 
     let c1  = comp2TMcomp c in
     calcEvalTM c1
   
 
   (*auxiliar function*)
   let isTM2FA (tm : TuringMachine.t) : bool =
     Set.for_all (fun (s,symb,nextS,nextSymb,dir) -> symb == nextSymb && dir == R) tm.transitions
 
   (* checks if a composition of elements is convertivel to Finite Automaton *)
   let rec isFAConvertivel(c:t): bool =
     match c with
       | Plus (a,b) ->
         isFAConvertivel a && isFAConvertivel b
       | Seq (a,b) ->
         isFAConvertivel a && isFAConvertivel b
       | Intersect (a,b) ->
         isFAConvertivel a && isFAConvertivel b
       | Star t ->
         isFAConvertivel t
       | FA fa -> 
         true
       | RE re ->
         true
       | CFG cfg ->
         let cfgobj = new ContextFreeGrammarBasic.model (Representation cfg) in
         cfgobj#isRegular
       | PDA pda ->
         let pdaobj = new PushdownAutomaton.model (Representation pda) in
         pdaobj#isFiniteAutomaton
       | TM tm ->
         isTM2FA tm
       | _ -> 
         false
 
   (* checks if a composition of elements is convertivel to Regular Expression *)			
   let rec isREConvertivel(c:t): bool =
     match c with
       | Plus (a,b) ->
         isREConvertivel a && isREConvertivel b
       | Seq (a,b) ->
         isREConvertivel a && isREConvertivel b
       | Intersect (a,b) ->
         isREConvertivel a && isREConvertivel b
       | Star t ->
         isFAConvertivel t
       | FA fa -> 
         true
       | RE re ->
         true
       | CFG cfg -> 
         let cfgobj = new ContextFreeGrammarBasic.model (Representation cfg) in
         cfgobj#isRegular
       | PDA pda ->
         let pdaobj = new PushdownAutomaton.model (Representation pda) in
         pdaobj#isFiniteAutomaton
       | TM tm ->
         isTM2FA tm
       | _ -> 
         false
 
   (* checks if a composition of elements is convertivel to Context free grammar *)
   let rec isCFGConvertivel(c:t): bool =
     match c with
       | Plus (a,b) ->
         isCFGConvertivel a && isCFGConvertivel b
       | Seq (a,b) ->
         isCFGConvertivel a && isCFGConvertivel b
       | Intersect (a,b) ->
         isCFGConvertivel a && isCFGConvertivel b
       | Star t ->
         isCFGConvertivel t
       | CFG fa -> 
         true
       | PDA re ->
         true
       | FA fa ->
         true
       | RE re ->
         true
       | _ -> 
         false
 
   (* checks if a composition of elements is convertivel to pushdown automata *)
   let rec isPDAConvertivel(c:t): bool =
     match c with
       | Plus (a,b) ->
         isPDAConvertivel a && isPDAConvertivel b
       | Seq (a,b) ->
         isPDAConvertivel a && isPDAConvertivel b
       | Intersect (a,b) ->
         isPDAConvertivel a && isPDAConvertivel b
       | Star t ->
         isPDAConvertivel t
       | CFG cfg -> 
         true
       | PDA re ->
         true
       | FA fa ->
         true
       | RE re ->
         true
       | _ -> 
         false
   
   (* checks if a composition of elements is convertivel to turing machine *)
   let rec isTMConvertivel(c:t): bool =
     match c with
       | Plus (a,b) ->
         isTMConvertivel a && isTMConvertivel b
       | Seq (a,b) ->
         isTMConvertivel a && isTMConvertivel b
       | Intersect (a,b) ->
         isTMConvertivel a && isTMConvertivel b
       | Star t ->
         isTMConvertivel t
       | CFG cfg -> 
         true
       | PDA re ->
         true
       | FA fa ->
         true
       | RE re ->
         true
       | TM tm ->
         true
       | _ -> 
         false
 
 
 
   let isFA (c:t) : bool =
     match c with 
       | FA _ -> true
       | _ -> false
 
   (*transforms everything in type t *)
   let rec transformt (c: t) : t =
     match c with
       | Plus (a,b) ->
         Plus (transformt a, transformt b)
       | Seq (a,b) ->
         Seq (transformt a, transformt b)
       | Intersect (a,b) ->
         Intersect (transformt a, transformt b)
       | Star t ->
         Star (transformt t)
       | FA fa -> 
         FA fa
       | RE re ->
         RE re
       | CFG cfg -> 
         CFG cfg
       | PDA pda ->
         PDA pda
       | FAO fao ->
         FA fao#representation
       | REO reo ->
         RE reo#representation
       | CFGO cfgo ->
         CFG cfgo#representation
       |	PDAO pdao ->
         PDA pdao#representation 
       | Rep str ->
         (try
           let m = Repository.get str in
             transformt m
         with Not_found -> Error.fatal "Composition with invalid repository name")
       | _ -> 
         Error.fatal "transformt"
 
 
   
   (* calculate a composite finite automaton given a composition of elements *)		
   let evalFA (c: t) : FiniteAutomaton.t  =
     let c1 = transformt c in
     match isFAConvertivel c1 with
       | true -> evalMixFA c1 
       | false -> Error.fatal "evalFA"
 
   (* calculate a composite regular expression given a composition of elements *)		
   let evalRE (c: t) : RegularExpression.t  =
     let c1 = transformt c in
     match isREConvertivel c1 with
       | true -> evalMixRE c1
       | false -> Error.fatal "evalRE"
 
   (* calculate a composite context free grammar given a composition of elements *)		
   let evalCFG (c: t) : ContextFreeGrammarBasic.t  =
     let c1 = transformt c in
     match isCFGConvertivel c1 with
       | true -> evalMixCFG c1
       | false -> Error.fatal "evalCFG"
 
   (* calculate a composite pushdown automata given a composition of elements *)		
   let evalPDA (c: t) : PushdownAutomaton.t  =
     let c1 = transformt c in
     match isPDAConvertivel c1 with
       | true -> evalMixPDA c1											
       | false -> Error.fatal "evalPDA"
 
   (* calculate a composite turing machine given a composition of elements *)
   let evalTM (c: t) : TuringMachine.t  =
     let c1 = transformt c in
     match isTMConvertivel c1 with
       | true -> evalMixTM c1											
       | false -> Error.fatal "evalTM"
 
   let setRep (c: t) (name: string) : unit  = 
     Repository.update name c
   
   let getRep (name: string) : t =
     try
       Repository.get name
     with Not_found -> Error.fatal "getRep"
 
         
   let findRep (name: string ) : bool = 
     Repository.exists name
 
   let validate (name: string) (comp: t) : unit = ()
 
   (* Class *)
   class model (arg: t Arg.alternatives) =
     object(self) inherit Model.model arg kind as super	
       val representation = Entity.create arg fromJSon
       (* placement of the initializer is crucial - after representation *)
       initializer Entity.endCreation self#id self#representation kind validate
     (* Representation *)
       method representation = representation
     (* Show *)			
       method toJSon: JSon.t = toJSon representation 
       method toJSon2: JSon.t = toJSon2 self#id representation
       method show: unit = show representation
       method show2: unit = show2 self#id representation
 
       method accept (w: word): bool = accept representation w
 
       method generate (length: int): words = generate representation length
    
       method evalFA : FiniteAutomaton.t = evalFA representation

       method evalPDA : PushdownAutomaton.t = evalPDA representation

       method evalRE : RegularExpression.t = evalRE representation

       method evalCFG : ContextFreeGrammarBasic.t = evalCFG representation

     (* Ops *)(*
       method acceptBreadthFirst (w: word): bool = acceptBreadthFirst representation w
       method accept (w: word): bool = accept representation w
       method acceptFull (w: word) : bool * path * trail = acceptFull representation w
 
       method acceptWithTracing (w:word): unit = acceptWithTracing representation w
       method generate (length: int): words = generate representation length
       method generateUntil (length: int): words = generateUntil representation length
 
       method reachable (s:state): states = reachable representation s
       method productive: states = productive representation
       method getUsefulStates: states = getUsefulStates representation
       method getUselessStates: states = getUselessStates representation
       method cleanUselessStates: model =
         let fa = cleanUselessStates representation in
           new model (Arg.Representation fa)
       method areAllStatesUseful: bool = areAllStatesUseful representation
 
       method toDeterministic: model =
         let fa = toDeterministic representation in
           new model (Arg.Representation fa)
       method isDeterministic: bool = isDeterministic representation
 
       method equivalencePartition: states set = equivalencePartition representation
       method minimize: model =
         let fa = minimize representation in
           new model (Arg.Representation fa)
       method isMinimized: bool = isMinimized representation
     (* Exercices support *)
       method checkProperty (prop: string) = Util.println["WWW"]; checkProperty representation prop
       
       *)
     (* Learn-OCaml support *)
       method moduleName = ""
       method xTypeName = ""
       method xTypeDeclString : string = ""
       method toDisplayString (name: string): string = ""
       method example : JSon.t = JNull
       
     end
               
    
 end
 
 
