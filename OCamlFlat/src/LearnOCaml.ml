(*
 * LearnOCaml.ml
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
 *  Written by Artur Miguel Dias, Rita Macedo (amd, rm)
 *)

(*
 * ChangeLog:
 *
 * jul/2021 (amd) - Added semantic validation of the student's solution.
 * jun/2021 (amd) - Added support for typed student answers in the file
 *                  "template.ml". Many improvements in the implementation,
 *                  and managed to get rid of many technical
 *                  complexities in the file "template.ml".
 * mar/2021 (amd, rm) - Initial version
 *)

(*
 * Description: This module helps in the use of the OCamlFLAT library
 * inside Learn-OCaml (the platform for learning the OCaml language). The goal
 * is to support FLAT related exercises inside Learn-OCaml. 
 *  
 * As for FLAT exercises developed for current text-based interaction of
 * Learn-OCaml, our current approach is to avoid changing Learn-OCaml
 * itself.
 * 
 * The current solution comprehends:
 *
 * - A technique that allows the OCamlFLAT library to be available inside the
 *   exercise environment of Learn-OCaml (via the file "prepare.ml").
 *   
 * - The idea of reducing FLAT model analysis to OCaml function analysis. This
 *   allows us to represent FLAT exercises using what is available in
 *   Learn-OCaml, without changing anything in Learn-OCaml.
 *   
 * - This module, which supplies some functions that helps in
 *   the creation by hand of FLAT exercises following the conventions
 *   of Learn-OCaml.
 *   
 * - A translator from the OCamlFLAT exercise format to the Learn-OCaml
 *   exercise format. The translator generates a directory containing all
 *   the usual files: "template.ml", "solution.ml", "meta.json", etc.
 *)

open BasicTypes

module type LearnOCamlSig =
sig
	val setOCamlFlatDir : string -> unit
	val setExercicesDir : string -> unit
	val setExerciceName : string -> unit
	val processAnswer : Model.model
					-> Exercise.exercise -> (string * int) list
	val decl2json : string -> JSon.t
	val generateExerciseDir : JSon.t -> JSon.t -> bool -> unit
end

module LearnOCaml : LearnOCamlSig =
struct
	(* ----- Dir/File management ----- *)
	let oCamlFlatDir = ref ""
	let exercicesDir = ref ""
	let exerciceName = ref ""		

	let setOCamlFlatDir dirname =
		oCamlFlatDir := Util.handleHomeDir dirname

	let setExercicesDir dirname =
		exercicesDir := Util.handleHomeDir dirname

	let setExerciceName filename =
		exerciceName := filename

	let initialize () =
		if !oCamlFlatDir = "" then
			begin
				setOCamlFlatDir
					"~/work/OCamlFlat";
				setExercicesDir
					"~/work/learn-test/my-learn-ocaml-repository/exercises";
				setExerciceName
					"default"
			end

	let libFile () =
		!oCamlFlatDir ^ "/lib/OCamlFlat.ml"

	let targetDir () =
		!exercicesDir ^ "/" ^ !exerciceName
	
	let targetFile fileName =
		targetDir () ^ "/" ^ fileName
	
	let adjust txt =
		Util.stripHead txt
 
	let createTargetDir () =
		ignore (Sys.command ("mkdir -p " ^ targetDir ()) )

	let createTargetFile fileName text =
		let co = open_out (targetFile fileName) in
		let text = adjust text in
		begin
			output_string co text;
			close_out co
		end

	let getExerciceDirContents () =
		Array.to_list (Sys.readdir !exercicesDir)
	
	(* ----- Utility functions ----- *)
	let processUnitTest m expected w =
			(word2str w, expected, m#accept w = expected)

	let semanticValidation (m: Model.model) =
		m#errors

	let convertSemanticValidationResult mesg =
			(mesg, 0)

	let processUnitTests (m: Model.model) (e: Exercise.exercise) =
		let open Exercise in
		let rep = e#representation in
			List.map (processUnitTest m true) (Set.toList rep.inside)
			@
			List.map (processUnitTest m false) (Set.toList rep.outside)
			
	let convertUnitTestResult (word, acceptance, passed) =
		let ar = if acceptance then "Acceptance" else "Rejection" in
		let pf = if passed then "passed" else "failed" in
		let points = if passed then 1 else 0 in
			(ar ^ " of word \"" ^ word ^ "\" " ^ pf, points)

	let processProperty m p =
		(p, m#checkProperty p)
	
	let processProperties (m: Model.model) (e: Exercise.exercise) =
		let open Exercise in
		let rep = e#representation in
		let props = Set.toList rep.properties in
			List.map (processProperty m) props	
		
	let convertPropertyResult (property, passed) =
		let pf = if passed then "passed" else "failed" in
		let points = if passed then 3 else 0 in
			("Property \"" ^ property ^ "\" " ^ pf, points)

	let finalResult0 res =
		[("###  Checking for static semantic errors...", -999)]
		@ res
		@ [("### Errors found", -999)]

	let finalResult1 res1 res2 =
		[]
		@ [("###  Checking for static semantic errors...", -999)]
		@ [("### Checking unit tests...", -999)]
		@ res1
		@ [("### Checking properties...", -999)]
		@ res2
		@ [("### Done", -999)]

	let processAnswer (m: Model.model) (e: Exercise.exercise) =
		let semanticValidationResults = semanticValidation m in
		let res0 = List.map convertSemanticValidationResult semanticValidationResults in
		if res0 <> [] then
			finalResult0 res0
		else
			let unitTestsResults = processUnitTests m e in
			let res1 = List.map convertUnitTestResult unitTestsResults in
			let propertyResults = processProperties m e in
			let res2 = List.map convertPropertyResult propertyResults in
				finalResult1 res1 res2

	let stdKind kind =
		match kind with
		| "finiteAutomaton" | "FiniteAutomaton.tx" ->
			FiniteAutomaton.kind
		| "regularExpression" | "RegularExpression.tx" ->
			RegularExpression.kind
		| "ContextFreeGrammarBasic" | "ContextFreeGrammarBasic.tx" ->
			ContextFreeGrammarBasic.kind
		| "finiteEnumeration" | "FiniteEnumeration.tx" ->
			FiniteEnumeration.kind
		| _ ->
			"*** invalid ***"

	let completeJSon kind j  =
		match kind with
		| "regularExpression" | "RegularExpression.tx" ->
			JSon.makeAssoc [("re", j)]
		| "finiteEnumeration" | "FiniteEnumeration.tx" ->
			JSon.makeAssoc [("words", j)]
		| _ ->
			j

	let decl2json s =
		try
			let a = String.index_from s 0 ':' in
			let b = String.index_from s a '=' in
			let kind = String.trim (String.sub s (a+1) (b-a-1)) in
			let ocamlExp = String.sub s (b+1) (String.length s -b-1) in
			let jExp = JSon.parseOon ocamlExp in
			let mainJSon = completeJSon kind jExp in
			let jHead = Entity.toJSon (Entity.dummyId (stdKind kind)) in
				JSon.append jHead mainJSon
		with _ ->
			JSon.JNull
	
	(* ----- FILE descr.html ----- *)
	let fileName =
		"descr.html"
	
	let contents (exercise: JSon.t) =
		Printf.sprintf
{ooo_descr_html_ooo|
		<h3> %s </h3>
		<p> %s </p>
|ooo_descr_html_ooo}
		(JSon.fieldString exercise "description")
		(JSon.fieldString exercise "problem")
	
	let generateFile_Descr (exercise: JSon.t) =
		let text = contents exercise in
			createTargetFile fileName text

	(* ----- FILE meta.json ----- *)
	let fileName =
		"meta.json"
		
	let contents (exercise: JSon.t) =
		Printf.sprintf
	{ooo_meta_json_ooo|
		{
		  "learnocaml_version" : "1",
		  "kind" : "exercise",
		  "stars" : 0,
		  "title" : "%s"
		}
	|ooo_meta_json_ooo}
		(JSon.fieldString exercise "description")
	
	let generateFile_Meta (exercise: JSon.t) =
		let text = contents exercise in
			createTargetFile fileName text

	(* ----- FILE prelude.ml ----- *)
	let fileName =
		"prelude.ml"

	let generateFile_Prelude (solution: Model.model) =
		let text = solution#xTypeDeclString in
			createTargetFile fileName text
	
	(* ----- FILE prepare.ml ----- *)
	let fileName =
		"prepare.ml"

	let generateFile_Prepare () =
		let cmd = "cp -a " ^ libFile () ^ " " ^ targetFile fileName in
			ignore (Sys.command cmd)

	(* ----- FILE solution.ml ----- *)
	let fileName =
		"solution.ml"

	let contentsJSon (solution: Model.model) =
		Printf.sprintf
	{ooo_solution_ml_ooo|
		let solution = {| %s |}
	|ooo_solution_ml_ooo}
		(JSon.toStringN 2 solution#toJSon)

	let contents (solution: Model.model) =
		let signature = "\n\t\t(* OCamlFlat exercise *)" in
		let body = solution#toDisplayString "solution" in
			signature ^ body
	
	let generateFile_Solution (solution: Model.model) useJSon =
		let text =
			if useJSon then contentsJSon solution
			else contents solution
		in
			createTargetFile fileName text

	(* ----- FILE template.ml ----- *)
	let fileName =
		"template.ml"

	let contentsJSon (solution: Model.model) =
		Printf.sprintf
	{ooo_template_ml_json_ooo|
		(* Write your solution below, by using the provided example as a template *)

		let solution = {| %s |}
	|ooo_template_ml_json_ooo}
		(JSon.toStringN 2 solution#example)

	let contents (solution: Model.model) =
		Printf.sprintf
	{ooo_template_ml_ooo|
		(* Write your solution below, by using the provided example as a template *)
		%s|ooo_template_ml_ooo}	(* please, do not change this *)
		((PolyModel.json2model solution#example)#toDisplayString "solution")

	let generateFile_Template (solution: Model.model) useJSon =
		let text =
			if useJSon then contentsJSon solution
						else contents solution
		in
			createTargetFile fileName text

	(* ----- FILE test.ml ----- *)
	let fileName =
		"test.ml"
	
	let exercisePart (exercise: JSon.t) =
		Printf.sprintf
	{ooo_exercise_ooo|
		let exercise = {| %s |}
	|ooo_exercise_ooo}
		(JSon.toStringN 2 exercise)

	let handleAnswerPartJSon =
		Printf.sprintf
	{ooo_handle_answer_json_ooo|
		let handleAnswer (): Learnocaml_report.t =
			test_variable_property
				[%%ty: string]
				"solution"
				(fun solution ->
					checkAnswer
						(PolyModel.text2model solution)
						(new Exercise.exercise (Arg.Text exercise))
				)
	|ooo_handle_answer_json_ooo}
	
	let handleAnswerPart (solution: Model.model) =
		Printf.sprintf
	{ooo_handle_answer_ooo|
		let handleAnswer (): Learnocaml_report.t =
			test_variable_property
				[%%ty: %s]
				"solution"
				(fun solution ->
					checkAnswer
						((new %s.model (Arg.Representation (%s.internalize solution))):
										%s.model :> Model.model)
						(new Exercise.exercise (Arg.Text exercise))
				)
	|ooo_handle_answer_ooo}
	solution#xTypeName
	solution#moduleName
	solution#moduleName
	solution#moduleName
		
	let contents exerciseText handleAnswerText =
		Printf.sprintf
	{ooo_test_ml_ooo|
		open Test_lib
		open Report
		%s
		let convertResult (diagnostic, points) =
			match points with
			| _ when points > 0 ->
				Message ([Text diagnostic], Success points)
			| -999 ->
				Message ([Break; Text diagnostic], Informative)
			| _ ->
				Message ([Text diagnostic], Failure)
		
		let checkAnswer (m: Model.model) (e: Exercise.exercise) =
			let res = LearnOCaml.processAnswer m e in
				List.map convertResult res
		%s
		let () =
			set_result @@
			ast_sanity_check code_ast @@
			handleAnswer
	|ooo_test_ml_ooo}
		exerciseText
		handleAnswerText

	let generateFile_Test (exercise: JSon.t) (solution: Model.model) useJSon =
		let ex = exercisePart exercise in
		let hs =
			if useJSon then handleAnswerPartJSon
			else handleAnswerPart solution
		in
		let text = contents ex hs
		in
			createTargetFile fileName text	

	(* ----- FILE index.json ----- *)
	let fileName =
		"../index.json"
		
	let contents (l: string list) =
		Printf.sprintf
	{ooo_index_json_ooo|
		{
		  "learnocaml_version" : "1",
		  "groups" : { "OCamlFLAT": {
		    "title": "OCamlFLAT exercise pack for Learn-OCaml",
		    "exercises": %s
		  } }
		}
	|ooo_index_json_ooo}
		(stringsD l)
	
	let generateFile_Index () =
		let l = getExerciceDirContents () in
		let l = List.filter (fun x -> x <> "index.json") l in
		let text = contents l in
		let text = String.map (fun x -> if x = ';' then ',' else x) text in
			createTargetFile fileName text

	(* ----- generateExerciseDir ----- *)
	
	let generateExerciseDir exercise solution useJSon =
		let solution: Model.model = PolyModel.json2model solution in
			initialize ();
			createTargetDir ();
			generateFile_Descr exercise;
			generateFile_Meta exercise;
			generateFile_Prelude solution;
			generateFile_Prepare ();
			generateFile_Solution solution useJSon;
			generateFile_Template solution useJSon;
			generateFile_Test exercise solution useJSon;
			generateFile_Index ()
end

(*
Learnocaml_report.t:

	type report = item list

	and item =
	  | Section of text * report
	  (** A titled block that groups subreports *)
	  | Message of text * status
	  (** Basic report block *)

	and status =
	  | Success of int (** With given points *)
	  | Failure (** With missed points *)
	  | Warning (** A student error without influence on the grade *)
	  | Informative (** A message for the student *)
	  | Important (** An important message *)

	and text = inline list

	and inline =
	  | Text of string (** A word *)
	  | Break (** Line separator *)
	  | Code of string (** For expressions *)
	  | Output of string (** For output *)
*)
