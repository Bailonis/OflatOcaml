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