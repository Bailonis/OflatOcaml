module AttributeGrammarSupportTests : sig end =
	struct
		open AttributeGrammar
        open AttributeGrammarPrivate
        open BasicTypes

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

        let ag2 = {| {
                kind : "attribute grammar",
                description : "",
                name : "ag2",
                alphabet : ["0","1","2","3","4","5","6","7","8","9","+", ""],
                variables : ["S","E","F","X"],
                inherited : ["d"],
                synthesized : ["v", "r"],
                initial : "S",
                rules : [ "S -> E {v(S) = v(E)}",
                            "E -> F X {v(E) = r(X) ; d(X) = v(F)}",
                            "X -> + F X {r(X0) = r(X1) ; d(X1) = d(X0) + v(F)}",
                            "X -> ~ {r(X) = d(X)}",
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

        let pt2 =
                Node (e "S", [
                    Node (e "E", [
                        Node (e "F", [
                            Leaf (e "3")
                        ]);
                        Node (e "X", [
                            Leaf (e "+");
                            Node (e "F", [
                                Leaf (e "2")
                            ]);
                            Node (e "X", [
                                Leaf (e "+");
                                Node (e "F", [
                                    Leaf (e "9")
                                ]);
                                Node (e "X", [
                                    Leaf (e "~")
                                ])
                            ])
                        ])
                ])
        ])

        let ag3 = {| {
                kind : "attribute grammar",
                description : "",
                name : "ag3",
                alphabet : ["[", "]"],
                variables : ["S","E"],
                inherited : ["d"],
                synthesized : ["v"],
                initial : "S",
                rules : [ "S -> E {v(S) = v(E) ; d(E) = 5}",
                          "E -> ~ {v(E) = d(E) + 1}"
                            ]
                    } |}

        let pt3 =
               Node (e "S", [
                   Node (e "E", [
                     Leaf (e "~")
                   ])
               ])

        let ag4 = {| {
          kind : "attribute grammar",
          description : "boolean + boolean should fail at evaluation",
          name : "ag_bool_plus",
          alphabet : ["x","y","+"],
          variables : ["S","A","B"],
          inherited : [""],
          synthesized : ["b"],
          initial : "S",
          rules : [
            "S -> A B { b(S) = b(A) + b(B) }",
            "A -> x { b(A) = T }",
            "B -> y { b(B) = F }"
          ]
        } |}

        let pt4 =
          Node (e "S", [
            Node (e "A", [ Leaf (e "x") ]);
            Node (e "B", [ Leaf (e "y") ])
          ])

        let ag5 = {| {
                kind : "attribute grammar",
                description : "division by zero must fail at evaluation",
                name : "ag_div_zero",
                alphabet : ["0","1","/"],
                variables : ["S","E","F"],
                inherited : [""],
                synthesized : ["v"],
                initial : "S",
                rules : [ "S -> E {v(S) = v(E)}",
                                  "E -> E / F {v(E0) = v(E1) / v(F)}",
                                  "E -> F {v(E) = v(F)}",
                                  "F -> 0 {v(F) = 0}",
                                  "F -> 1 {v(F) = 1}"
                                  ]
                      } |}

        let pt5 =
                Node (e "S", [
                    Node (e "E", [
                         Node (e "E", [
                             Node (e "F", [
                                  Leaf (e "1")
                            ])
                        ]);
                        Leaf (e "/");
                        Node (e "F", [
                            Leaf (e "0")
                        ])
                  ] )
                ])

        let ag6 = {| {
          kind : "attribute grammar",
          description : "A's inherited depends on B's synthesized (future sibling)",
          name : "ag_lattr_violation",
          alphabet : ["a"],
          variables : ["S","A","B"],
          inherited : ["d"],
          synthesized : ["v"],
          initial : "S",
          rules : [
            "S -> A B { d(A) = v(B) ; v(S) = v(A) + v(B) }",
            "A -> a { v(A) = d(A) }",
            "B -> a { v(B) = 1 }"
          ]
        } |}

        let pt6 =
          Node (e "S", [
            Node (e "A", [ Leaf (e "a") ]);
            Node (e "B", [ Leaf (e "a") ])
          ])

        let ag7 = {| {
          kind : "attribute grammar",
          description : "default child index + explicit C1/C2 occurrences",
          name : "ag_default_index",
          alphabet : ["n","m"],
          variables : ["S","C"],
          inherited : ["d"],
          synthesized : ["v"],
          initial : "S",
          rules : [
            "S -> C C { d(C) = 1 ; d(C2) = 3 ; v(S) = v(C1) + v(C2) }",
            "C -> n { v(C) = d(C) }",
            "C -> m { v(C) = d(C) }"
          ]
        } |}

        let pt7 =
          Node (e "S", [
            Node (e "C", [ Leaf (e "n") ]);
            Node (e "C", [ Leaf (e "m") ])
          ])

        let ag8 = {| {
                  kind : "attribute grammar",
                  description : "boolean flags",
                  name : "ag_boolean_flags",
                  alphabet : ["x","y"],
                  variables : ["S","A","B"],
                  inherited : [""],
                  synthesized : ["b"],
                  initial : "S",
                  rules : [
                    "S -> A B { b(S) = b(A) = b(B) }",
                    "A -> x { b(A) = T }",
                    "A -> y { b(A) = F }",
                    "B -> x { b(B) = T }",
                    "B -> y { b(B) = F }"
                  ]
                } |}

        let pt8 =
          Node (e "S", [
            Node (e "A", [ Leaf (e "x") ]);
            Node (e "B", [ Leaf (e "y") ])
          ])

        let ag9 = {| {
                kind : "attribute grammar",
                description : "compute length of a list of items",
                name : "ag_list_length",
                alphabet : ["a",","],
                variables : ["L","I"],
                inherited : [""],
                synthesized : ["v"],
                initial : "L",
                rules : [
                  "L -> L , I { v(L0) = v(L1) + v(I) }",
                  "L -> I { v(L) = v(I) }",
                  "I -> a { v(I) = 1 }"
                ]
              } |}

        let rec make_list n =
                  if n = 1 then
                    Node (e "L", [ Node (e "I", [ Leaf (e "a") ]) ])
                  else
                    Node (e "L", [
                      make_list (n - 1);
                      Leaf (e ",");
                      Node (e "I", [ Leaf (e "a") ])
                    ])

        let pt9 = make_list 30

        let ag10 = {| {
                    kind : "attribute grammar",
                    description : "inherited default index and synthesized result",
                    name : "ag_inherited_default",
                    alphabet : ["n","m"],
                    variables : ["S","C","F"],
                    inherited : ["d"],
                    synthesized : ["v"],
                    initial : "S",
                    rules : [
                      "S -> C F { d(C) = 0; d(F) = 0 ; v(S) = v(C) + v(F) }",
                      "C -> n { v(C) = d(C) + 1 }",
                      "F -> m { v(F) = d(F) + 2 }"
                    ]
                  } |}

        let pt10 =
                Node (e "S", [
                  Node (e "C", [ Leaf (e "n") ]);
                  Node (e "F", [ Leaf (e "m") ])
                ])

        let ag11 = {| {
          kind : "attribute grammar",
          description : "reference to nonexistent child occurrence in RHS",
          name : "ag_out_of_range_ref",
          alphabet : ["a"],
          variables : ["S","A"],
          inherited : [""],
          synthesized : ["v"],
          initial : "S",
          rules : [
            "S -> A { v(S) = v(A2) }",
            "A -> a { v(A) = 1 }"
          ]
        } |}

        let pt11 =
          Node (e "S", [ Node (e "A", [ Leaf (e "a") ]) ])

        let ok_ag = {| {
          kind : "attribute grammar",
          description : "acyclic sanity",
          name : "ok_ag",
          alphabet : ["a","+"],
          variables : ["S","F"],
          inherited : [""],
          synthesized : ["v"],
          initial : "S",
          rules : [
            "S -> F { v(S) = v(F) }",
            "F -> a { v(F) = 1 }"
          ]
        } |}

        let cyc_ag = {| {
          kind : "attribute grammar",
          description : "deliberate cycle",
          name : "cyc_ag",
          alphabet : ["a"],
          variables : ["S","F"],
          inherited : [""],
          synthesized : ["v"],
          initial : "S",
          rules : [
            "S -> F { v(S0) = v(F0) }",
            "F -> S { v(F0) = v(S0) }"
          ]
        } |}

        let test_ag1_simple_synthesized () =
            Util.header "ag1_simple_synthesized";
            let g = AttributeGrammar.make (Arg.Text ag1) in
            let newTree = calcAttributes g pt1 in
            Printf.printf "Final parse tree (ag1):\n";
            print_parse_tree newTree;
            Printf.printf "Expected: v(S) = 6 \n"

        let test_ag2_simple_synthesized_and_inherited () =
            Util.header "ag2_simple_synthesized_and_inherited";
            let g = AttributeGrammar.make (Arg.Text ag2) in
            let newTree = calcAttributes g pt2 in
            Printf.printf "Final parse tree (ag2):\n";
            print_parse_tree newTree;
            Printf.printf "Expected: v(S) = 14 \n"

        let test_ag3_simpler_synthesized_and_inherited () =
            Util.header "ag3_simpler_synthesized_and_inherited";
            let g = AttributeGrammar.make (Arg.Text ag3) in
            let newTree = calcAttributes g pt3 in
            Printf.printf "Final parse tree (ag3):\n";
            print_parse_tree newTree;
            Printf.printf "Expected: v(S) = 6 \n"

        let test_ag4_type_mismatch () =
             Util.header "ag4_type_mismatch";
             let g = AttributeGrammar.make (Arg.Text ag4) in
             try
               let _ = calcAttributes g pt4 in
               Printf.printf "UNEXPECTED: evaluation succeeded (should fail with type error)\n"
             with Failure msg ->
               Printf.printf "Expected failure: %s\n" msg

        let test_ag5_div_zero () =
            Util.header "ag5_div_zero";
            let g = AttributeGrammar.make (Arg.Text ag5) in
            try
              let _ = calcAttributes g pt5 in
              Printf.printf "UNEXPECTED: evaluation succeeded (should fail: division by zero)\n"
            with Failure msg ->
              Printf.printf "Expected failure: %s\n" msg

        let test_ag6_lattr_violation () =
             Util.header "ag6_lattr_violation";
             let g = AttributeGrammar.make (Arg.Text ag6) in
             try
               let _ = calcAttributes g pt6 in
               Printf.printf "UNEXPECTED: evaluation succeeded (should fail reading v(B) before B is evaluated)\n"
             with Failure msg ->
               Printf.printf "Expected failure (L-attributed violation at runtime): %s\n" msg

        let test_ag7_default_index () =
              Util.header "ag7_default_index";
              let g = AttributeGrammar.make (Arg.Text ag7) in
              let t = calcAttributes g pt7 in
              Printf.printf "Final parse tree (ag7):\n";
              print_parse_tree t;
              Printf.printf "OK: evaluated with normalized/default indices\n"

        let test_ag8_boolean_flags () =
              Util.header "ag8_boolean_flags";
              let g = AttributeGrammar.make (Arg.Text ag8) in
              let t = calcAttributes g pt8 in
              Printf.printf "Final parse tree (ag8):\n";
              print_parse_tree t

        let test_ag9_list_length () =
              Util.header "ag9_list_length";
              let g = AttributeGrammar.make (Arg.Text ag9) in
              let t = calcAttributes g pt9 in
              Printf.printf "Final parse tree (ag9):\n";
              print_parse_tree t;
              Printf.printf "Expected: length = 30 (v at root)\n"

        let test_ag10_inherited_default () =
              Util.header "ag10_inherited_default";
              let g = AttributeGrammar.make (Arg.Text ag10) in
              let t = calcAttributes g pt10 in
              Printf.printf "Final parse tree (ag10):\n";
              print_parse_tree t;
              Printf.printf "Expected: v(S) = 3 (since d(C)=0 -> v(C)=1, d(F)=0 -> v(F)=2)\n"

        let test_ag11_out_of_range_ref () =
              Util.header "ag11_out_of_range_ref";
              try
                let g = AttributeGrammar.make (Arg.Text ag11) in
                let _ = calcAttributes g pt11 in
                Printf.printf "UNEXPECTED: validation/evaluation succeeded (should fail on A2)\n"
              with _ ->
                Printf.printf "Expected failure: child occurrence out of range\n"

        let test_has_cycles_ok () =
              Util.header "has_cycles_ok";
              let g = AttributeGrammarSupport.fromJSon (JSon.parse ok_ag) in
              let r = has_cycles g in
              Printf.printf "has_cycles(ok_ag) = %b (expected false)\n" r

        let test_has_cycles_detected () =
              Util.header "has_cycles_detected";
              let g = AttributeGrammarSupport.fromJSon (JSon.parse cyc_ag) in
              let r = has_cycles g in
              Printf.printf "has_cycles(cyc_ag) = %b (expected true)\n" r

        let test_accept_with_tree_ok () =
              Util.header "test_accept_with_tree_ok";
              let g = AttributeGrammar.make (Arg.Text ag1) in
              let ok = accept_ag_with_tree g pt3 in
              Printf.printf "accept_ag_with_tree(pt1) = %b\n" ok

        let test_accept_words () =
              Util.header "test_accept_words";
              let g = AttributeGrammar.make (Arg.Text ag1) in

              let cfg : ContextFreeGrammarBasic.t =
                AttributeGrammarPrivate.ga_to_cfg g
              in
              let sym = BasicTypes.str2symb in
              let three = sym "9" and star = sym "-" and two = sym "2" in
              let w = [three; star; two] in

              let r = ContextFreeGrammarBasic.accept cfg w in
              Printf.printf "AG->CFG.accept %s = %b\n"
                (BasicTypes.word2str w) r

        let generate_words () =
              Util.header "test_generate_words";
              let g = AttributeGrammar.make (Arg.Text ag1) in
              let words = AttributeGrammar.generate ~max_depth:5 ~max_words:100 g in
              Printf.printf "generate: produced %d words (max_depth=5, max_words=10)\n"
                (List.length words);
              List.iter
                (fun w -> Printf.printf "  %s\n" (BasicTypes.word2str w))
                words
            ;;

        let ag_expr_ext = {| {
              kind : "attribute grammar",
              description : "arithmetic with + - * / and parentheses; computes value, pretty string, and a height metric",
              name : "ag_expr_ext",
              alphabet : ["0","1","2","3","4","5","6","7","8","9","+","-","*","/","(",")"],
              variables : ["S","E","T","F","N"],
              inherited : [""],
              synthesized : ["v","s","h"],
              initial : "S",
              rules : [
                "S -> E { v(S) = v(E) ; s(S) = s(E) ; h(S) = h(E) }",

                "E -> E + T { v(E0) = v(E1) + v(T) ; s(E0) = s(E1) + '+' + s(T) ; h(E0) = h(E1) + h(T) + 1 }",
                "E -> E - T { v(E0) = v(E1) - v(T) ; s(E0) = s(E1) + '-' + s(T) ; h(E0) = h(E1) + h(T) + 1 }",
                "E -> T     { v(E)  = v(T)         ; s(E)  = s(T)              ; h(E)  = h(T) }",

                "T -> T * F { v(T0) = v(T1) * v(F) ; s(T0) = s(T1) + '*' + s(F) ; h(T0) = h(T1) + h(F) + 1 }",
                "T -> T / F { v(T0) = v(T1) / v(F) ; s(T0) = s(T1) + '/' + s(F) ; h(T0) = h(T1) + h(F) + 1 }",
                "T -> F     { v(T)  = v(F)         ; s(T)  = s(F)               ; h(T)  = h(F) }",

                "F -> ( E ) { v(F) = v(E) ; s(F) = '(' + s(E) + ')' ; h(F) = h(E) + 1 }",
                "F -> N     { v(F) = v(N) ; s(F) = s(N)             ; h(F) = h(N) }",

                "N -> 0 { v(N) = 0 ; s(N) = '0' ; h(N) = 1 }",
                "N -> 1 { v(N) = 1 ; s(N) = '1' ; h(N) = 1 }",
                "N -> 2 { v(N) = 2 ; s(N) = '2' ; h(N) = 1 }",
                "N -> 3 { v(N) = 3 ; s(N) = '3' ; h(N) = 1 }",
                "N -> 4 { v(N) = 4 ; s(N) = '4' ; h(N) = 1 }",
                "N -> 5 { v(N) = 5 ; s(N) = '5' ; h(N) = 1 }",
                "N -> 6 { v(N) = 6 ; s(N) = '6' ; h(N) = 1 }",
                "N -> 7 { v(N) = 7 ; s(N) = '7' ; h(N) = 1 }",
                "N -> 8 { v(N) = 8 ; s(N) = '8' ; h(N) = 1 }",
                "N -> 9 { v(N) = 9 ; s(N) = '9' ; h(N) = 1 }"
              ]
            } |}

        let pt_expr_ext =
              Node (e "S", [
                Node (e "E", [
                  Node (e "E", [
                    Node (e "E", [
                      Node (e "T", [
                        Node (e "F", [ Node (e "N", [ Leaf (e "3") ]) ])
                      ])
                    ]);
                    Leaf (e "+");
                    Node (e "T", [
                      Node (e "T", [
                        Node (e "T", [
                          Node (e "F", [ Node (e "N", [ Leaf (e "2") ]) ])
                        ]);
                        Leaf (e "*");
                        Node (e "F", [
                          Leaf (e "(");
                          Node (e "E", [
                            Node (e "E", [
                              Node (e "T", [
                                Node (e "F", [ Node (e "N", [ Leaf (e "9") ]) ])
                              ])
                            ]);
                            Leaf (e "-");
                            Node (e "T", [
                              Node (e "F", [ Node (e "N", [ Leaf (e "5") ]) ])
                            ])
                          ]);
                          Leaf (e ")");
                        ])
                      ]);
                      Leaf (e "/");
                      Node (e "F", [ Node (e "N", [ Leaf (e "2") ]) ])
                    ])
                  ]);
                  Leaf (e "-");
                  Node (e "T", [
                    Node (e "F", [ Node (e "N", [ Leaf (e "1") ]) ])
                  ])
                ])
              ])

        let test_ag_expr_ext () =
              Util.header "ag_expr_ext";
              let g = AttributeGrammar.make (Arg.Text ag_expr_ext) in
              let t = calcAttributes g pt_expr_ext in
              let ((_, evs), _) =
                match t with
                | Node (n, children) -> (n, children)
                | Leaf n -> (n, [])
              in
              let find a = snd (Set.find (fun (attr,_) -> attr = symb a) evs) in
              let vS = find "v" and sS = find "s" and hS = find "h" in
              let show_v = match vS with Int n -> n | _ -> failwith "v(S) not Int" in
              let show_s = match sS with String s -> s | _ -> failwith "s(S) not String" in
              let show_h = match hS with Int n -> n | _ -> failwith "h(S) not Int" in
              Printf.printf "v(S) = %d (expected 6)\n" show_v;
              Printf.printf "s(S) = %s (expected 3+2*(9-5)/2-1)\n" show_s;
              Printf.printf "h(S) = %d\n" show_h

        let runAll =
              if Util.testing active "AttributeGrammarSupport" then begin

                test_ag1_simple_synthesized ();
                test_ag2_simple_synthesized_and_inherited ();
                test_ag3_simpler_synthesized_and_inherited ();
                test_ag4_type_mismatch ();
                test_ag5_div_zero ();
                test_ag6_lattr_violation ();
                test_ag7_default_index ();
                test_ag8_boolean_flags ();
                test_ag9_list_length ();
                test_ag10_inherited_default ();
                test_ag11_out_of_range_ref ();
                (*test_accept_with_tree_ok ();*)
                (*generate_words ();*)
                (*test_accept_words ();*)
                (*test_has_cycles_ok ();*)
                (*test_has_cycles_detected ();*)
                test_ag_expr_ext ()

              end
	end