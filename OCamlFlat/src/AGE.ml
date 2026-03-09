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
  synthesized : ["v"],
  initial : "S",
  rules : [
    "S -> A B { v(S) = v(A) + v(B) }",
    "A -> x { v(A) = T }",
    "B -> y { v(B) = F }"
  ]
} |}

let pt4 =
  Node (e "S", [
    Node (e "A", [ Leaf (e "x") ]);
    Node (e "B", [ Leaf (e "y") ])
  ])

let ag5 = {| {
  kind : "attribute grammar",
  description : "LHS head must be synthesized, not inherited",
  name : "ag_head_inh_lhs",
  alphabet : ["a"],
  variables : ["S","F"],
  inherited : ["d"],
  synthesized : ["v"],
  initial : "S",
  rules : [
    "S -> F { d(S) = v(F) }",
    "F -> a { v(F) = 1 }"
  ]
} |}

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
          synthesized : ["v"],
          initial : "S",
          rules : [
            "S -> A B { v(S) = v(A) = v(B) }",
            "A -> x { v(A) = T }",
            "A -> y { v(A) = F }",
            "B -> x { v(B) = T }",
            "B -> y { v(B) = F }"
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
