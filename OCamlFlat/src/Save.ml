-------------------
TM

	let confX (s, tl, tr) =
		state2str s, word2str (List.rev tl)
		^ "[" ^ symb2str (List.hd tr) ^ "]"
		^ word2str (List.tl tr)
	let pathX (p: path) = pathX confX p
	let trailX (t: trail) = trailX confX t

	let nTapesJ (j: JSon.t): int =
		match j |> getField "transitions" with
		| JList (JList [a; b; c; d; e]::_) ->
			List.length (asOptionalSymbolList b "transitions")
		| _ -> 1

	let nTapesX (tmx: tx): int =
		match tmx.transitions with
		| [] -> 1
		| (_,b,_,_,_)::_ -> List.length b


	type tape = symbolM list
	type configuration = state * tape * tape
	type configurations = configuration set
	type path = configuration list
	type trail = configurations list

	let wordToTape (tm: t) (w: word): tape =
		let emptyM1 = List.tl (emptyM tm) in
			List.map (fun sy -> sy::emptyM1) w	

	let initialConfigs (tm: t) (w: word): configurations =
		let eM = emptyM tm in
		let conf = (tm.initialState, [eM], wordToTape tm w @[eM]) in
			Set.make [conf]

	let rec zip3 x y z =
		match x, y, z with
		| [], [], [] -> []
		| x::xs, y::ys, z::zs -> (x,y,z)::zip3 xs ys zs
		| _, _, _ -> failwith "zip3"
	
	let mBelongs (w: word) (s: symbol Set.t): bool =
		Set.subset (Set.make w) s

	let isAcceptingConfig (tm: t) ((s,l,r): configuration): bool =
		let curr = List.hd r in
		let ts = tm.transitions in
		let triggered = Set.filter (fun (a,b,_,_,_) -> a = s && b = curr) ts in
		let stops = Set.isEmpty triggered in
			if tm.criteria then
				stops && Set.belongs s tm.acceptStates
			else
				stops

	let fix (tm: t) tape =	
		match tape with
		| [] -> [emptyM tm]
		| _ -> tape
	
	let rec allTheSame l =
		match l with
		| [] -> true
		| [x] -> true
		| x::y::xs -> x = y && allTheSame (y::xs)
	
	let allTheSame l v =
		List.for_all (fun x -> x=v) l
	
	let rec shiftRightHeads ll v =
		match ll with
		| [x::xs] -> [v::xs]
		| (x::xs)::ls -> (v::xs)::shiftRightHeads ls x
		| _ -> failwith "shiftRightHeads"
	;;
	
	let rec shiftLeftHeads ll =
		match ll with
		| [x::xs] -> [0::xs]
		| (x::xs)::(y::ys)::ls -> (y::xs)::shiftLeftHeads ((y::ys)::ls)
		| _ -> failwith "shiftLeftHeads"
	;;

	let z = shiftRightHeads [[5;6;1]; [7;8;2]; [9;10;3]] 0 ;;
	let z = shiftLeftHeads [[5;6;1]; [7;8;2]; [9;10;3]] ;;

	let rec shift ll ml v =
		match ll, ml with
		| [x::xs], ['R'::ms] -> [v::xs]
		| [x::xs], ['L'::ms] -> [0::xs]
		| (x::xs)::(y::ys)::ls, ['L'::ms] -> (y::xs)::shiftLeftHeads ((y::ys)::ls)
		| _ -> failwith "shiftLeftHeads"
	;;

	let z = shift [[5;6;1]; [7;8;2]; [9;10;3]] ['L';'R';'L'] ;;
	
		let rec shiftRightHeads ll v =
		match ll with
		| [x::xs] -> [v::xs]
		| (x::xs)::ls -> (v::xs)::shiftRightHeads ls x
		| _ -> failwith "shiftRightHeads"
	;;

	let nextConfigs (tm: t) (tr: transition) (conf: configuration): configurations =
		match tr, conf with
		| (a,b,c,d,e), (s,l::ls,r::rs) when a = s && b = r ->
			if allTheSame e R then
				Set.make [(c, d::l::ls, fix tm rs)]
			else if allTheSame e L then
				Set.make [(c,fix tm ls, l::d::rs)]
			else if allTheSame e S then
				Set.make [(c, l::ls, d::rs)]
			else
			
				Set.make [(c, l::ls, d::rs)]
		| _, _ -> Set.empty

	let nextConfigs (tm: t) (config: configuration): configurations = 
		Set.flatMap (fun tr -> nextConfigs tm tr config) tm.transitions
		
	type tapeX = symbolXM list
	type configurationX =  tapeX * state * tapeX
	type configurationsX = configurationX list

	let confX ((s,l,r): configuration): configurationX =
		(List.rev (List.map symbolMX l), s, List.map symbolMX r)

	let confsX (c: configurations): configurationsX =
		List.map confX (Set.toList c)


i
nfiguration (conf: configuration): unit =
		let (state, left, right) = config in
		Util.print ["("; state2str state; ", "];
		List.iter (fun x -> Util.print [symb2str x]) left;
		Util.print [", "];
		List.iter (fun x -> Util.print [symb2str x]) right;
		Util.print [")"]

	let printConfigurations configs = 
		Util.println ["printing configs"];
		Set.iter (fun x -> printConfiguration x) configs;
		Util.println [string_of_int (Set.size configs)]	
	

	let rec acceptX left right st trs seen limit = 
		if limit = 0 then 
			state "~"
		else
			let newLimit = limit - 1 in
			let config = (List.rev left)@[symb (state2str st)]@right in
				if Set.belongs config seen then state "~"
				else
					let newSeen = Set.add config seen in
					match left, right with
					| [], [] -> st
					| [], x::xs -> acceptX [empty] right st trs newSeen newLimit
					| x::xs, [] -> acceptX left [empty] st trs newSeen newLimit
					| x::xs, y::ys ->
						let getTransi =
						Set.filter (fun (a,b,_,_,_) ->
							st = a && y = b) trs in
								if Set.isEmpty getTransi then st
								else 
									let (_,_,nst,nsymb,dir) = Set.nth getTransi 0 in
										if dir = R then
											let newLeft = nsymb::left in
												acceptX newLeft ys nst trs newSeen newLimit;
										else
											let newRight = x::nsymb::right in
												acceptX xs newRight nst trs	newSeen newLimit

	let acceptOld w rp =
		let bWord = w@[empty] in
			let lastST: state = acceptX [empty] bWord rp.initialState rp.transitions Set.empty 100 in
				if rp.criteria then Set.exists (fun x -> x = lastST) rp.acceptStates
				else if lastST = state "~" then false
				else true


	let copy (tm: t)
			?(entryAlphabet = tm.entryAlphabet)
			?(tapeAlphabet = tm.tapeAlphabet)
			?(states = tm.states)
			?(initialState = tm.initialState)
			?(transitions = tm.transitions)
			?(acceptStates = tm.acceptStates)
			?(criteria = tm.criteria)
			()
		= {
			entryAlphabet = entryAlphabet;
			tapeAlphabet = tapeAlphabet;	
			empty = tm.empty;
			states = states;
			initialState = initialState;
			transitions = transitions;
			acceptStates = acceptStates;
			criteria = criteria;
			lbMarkers = tm.lbMarkers;
			_nTapes = tm._nTapes
		}			

