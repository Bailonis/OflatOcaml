(*
 * Error.ml
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
 *  Written by Artur Miguel Dias (amd)
 *)

(*
 * ChangeLog:
 *
 * jan/2024 (amd) - Error groupings and support for setting of viewer.
 * jul/2021 (amd) - Simplified module.
 * jan/2021 (amd) - Module in an independent file.
 * jun/2019 (amd) - Initial version, inside the big file "OCamlFlatSupport.ml".
 *)

(*
 * Description: Supports a log of errors. Probably, a text-based application
 * will use the error log differently from a graphical-based application.
 * The errors are handled in a imperative style to simplify the signature of
 * many functions - this modules implements a kind of error log monad.
 *)


module ErrorViewer =
struct
	let errorViewer: (string -> unit) ref =
		ref print_string

	let quietViewer (_: string): unit =
		()

	let defaultViewer (mesg: string): unit =
		print_string mesg

	let setViewer (f: string -> unit): unit =
		errorViewer := f

	let adjust (mesg: string) =
		let len = String.length mesg in
		let last = if len > 0 then mesg.[len-1] else ' ' in
			if len = 0 then
				"EMPTY MESG"
			else if last = '.' then
				mesg ^ "\n"
			else
				mesg ^ ".\n"

	let view (mesg: string): unit =
		if Configuration.diagnosticsOn () then
			!errorViewer (adjust mesg)
		
	let fatal (mesg: string) =
		view ("FATAL ERROR - " ^ mesg);
		failwith mesg

	let warning (mesg: string) =
		view ("WARNING - " ^ mesg);
end


module ErrorGrouping =
struct
	open ErrorViewer

	let gouping: bool ref =
		ref false

	let errors: string list ref =
		ref []

	let startGroup (): unit =
		gouping := true;
		errors := []

	let makeMesg (culprit: string) (str: string) =
		if !gouping || culprit = "" || culprit = "_" then " - " ^ str ^ "\n"
		else culprit ^ " - " ^ str ^ "\n"

	let error (culprit: string) (str: string) (res: 'a): 'a =
		let mesg = makeMesg culprit str in
			(if !gouping then
				errors := !errors @ [mesg]
			else
				view mesg);
			res

	let endGroup (expectedKind: string) (name: string): bool =
		gouping := false;
		if !errors = [] then
			true
		else
			let mesg =
				  "--------------------------\n"
				^ expectedKind^" \""^name^ "\" has errors:\n"
				^ String.concat "" !errors
				^ "--------------------------\n"
			in view mesg;
			errors := [];
			false

	let get (): string list =
		!errors
end

module Error =
struct
	open ErrorViewer
	open ErrorGrouping

	let quietViewer = quietViewer
	let defaultViewer = defaultViewer
	let setViewer = setViewer

	let startGroup = startGroup
	let error = error
	let endGroup = endGroup
	let get = get
		
	let fatal = fatal
	let warning = warning
end
