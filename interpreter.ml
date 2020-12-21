type ide = string;;

(* etichette denotanti i nomi dei tipi *)
type typename = BooleanType | IntegerType | StringType

(* aggiunte le espressioni relative alle stringhe e i set *)
type exp = Eint of int | Ebool of bool | Estring of string | Den of ide | Esingleton of exp | Etypename of typename | Eemptyset of exp | Concat of exp * exp | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | IsEmptyStr of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp | AddToSet of exp * exp | BelongsToSet of exp * exp | RemoveFromSet of exp * exp |
	MaxValue of exp | MinValue of exp | Union of exp * exp | Intersection of exp * exp | Difference of exp * exp |
	Forall of exp * exp | Exists of exp * exp | Map of exp * exp | Filter of exp * exp | IsEmptySet of exp | IsSubset of exp * exp
;;

(* environment *)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(* dichiarazione del tipo di dato algebrico set_ *)
type set_ = Empty of typename | Set of evT list * typename
and evT = Int of int | Bool of bool | String of string | Unbound | FunVal of evFun | RecFunVal of ide * evFun | SetVal of set_
and evFun = ide * exp * evT env;;

(*rts*)
(* restituisce il tipo del parametro se esso è un tipo esprimibile consumabile dalle funzioni di set *)
let typeof (v: evT) : typename = match v with
	Int(_) -> IntegerType |
	Bool(_) -> BooleanType |
	String(_) -> StringType |
	_ -> failwith("not an expressable value")

(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	(* estensione *)
	"string" -> (match v with
		String(_) -> true |
		_ -> false) |
	"set" -> (match v with
		(SetVal(_)) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error prod");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error sum");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error diff");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error eq");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error minus");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error isz");;

(* verifica stringa vuota *)
let isEmptyString s = if (typecheck "string" s)
	then (match s with
		String(s) -> Bool(s="")
	) else failwith("Type error isem");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error vel");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error et");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error non");;

(* concatenazione di stringhe *)
let concat s t = if (typecheck "string" s) && (typecheck "string" t)
	then (match (s, t) with
		(String(s), String(t)) -> String(s^t)
	) else failwith("Type error cat");;

(* type checker aggiuntivo per ottenere le etichette di tipo *)
let exp_to_label = function
	Etypename(BooleanType) -> BooleanType |
	Etypename(IntegerType) -> IntegerType |
	Etypename(StringType) -> StringType |
	_ -> failwith("not a type label");;

(* restituisce un'espressione che valuta all'evT passato *)
(* utilizzata per chiamare dinamicamente le funzioni passate a exists, forall, map e filter *)
let evTToExp e =
	match e with
	(Bool b) -> (Ebool b) |
	(Int i) -> (Eint i) |
	(String s) -> (Estring s) |
	_ -> failwith("unintended use")
;;

(* operazioni su set_ *)
(* appartenenza all'insieme*)
let rec belongsToSet (v : evT) (s : evT) : evT = 
	match s with
		SetVal(ls) ->
			let exptype = typeof v in
					(match ls with
						Empty(_) -> (Bool false) |
						Set(lst, typelabel) -> if exptype <> typelabel then failwith("incompatible types")
							else
								match lst with
								[] -> (Bool false) |
								h::t -> if h = v then (Bool true) else belongsToSet v (SetVal(Set(t, typelabel)))
					)
		| _ -> failwith("calling belongsToSet on a non-set value");;

(* relazione di sottoinsieme *)
let isSubset (s : evT) (t : evT) : evT =
	match (s, t) with
		(SetVal(Empty(t1)), SetVal(Set(_, t2))) |  (SetVal(Empty(t1)), SetVal(Empty(t2))) -> if t1 = t2 then (Bool true) else failwith("incompatible types") |
		(SetVal(Set(_, t2)), SetVal(Empty(t1))) -> if t1 = t2 then (Bool false) else failwith("incompatible types") |
		(SetVal(Set(_, t1)), SetVal(Set(_, t2))) ->
			if t1 <> t2 then failwith("incompatible types")
			else let rec aux q r =
				match (q, r) with
					(SetVal(Empty(_)), _)|(SetVal(Set([], _)), _) -> (Bool true) | (* caso base, ho verificato tutti gli elementi e ho terminato il sottoinsieme *)
					(_, SetVal(Empty(_)))|(_, SetVal(Set([],_ ))) -> (Bool false) | (* caso base, il primo insieme ha cardinalità maggiore del secondo e quindi non può essere un suo sottoinsieme *)
					(SetVal(Set(h::t, ty)), SetVal(Set(u::v, _))) -> et (belongsToSet h r) (aux (SetVal(Set(t, ty))) (SetVal(Set(v, ty))))
			in
				aux s t
;;

(* aggiunta elemento all'insieme *)
let addToSet (v : evT) (s : evT) : evT =
		match s with
			SetVal(Empty(tl)) -> if typeof v != tl then failwith("incompatible types") else SetVal(Set([v], typeof v)) |
			SetVal(Set(lst, tl)) -> if typeof v != tl then failwith("incompatible types") else
				if (belongsToSet v s) = (Bool true) then s (* controllo duplicati *)
				else SetVal(Set(v::lst, tl))
			| _ -> failwith("calling addToSet on a non-set value");;

(* verifica insieme vuoto *)
let isEmpty (s : evT) : evT =
	match s with
		SetVal(Empty(_))|SetVal(Set([], _)) -> (Bool true) |
		SetVal(_) -> (Bool false) |
		_ -> failwith("calling isEmpty on a non-set value");;

(* massimo dell'insieme *)
let maxValue (s : evT) : evT option =
	let rec aux rem currmax =
		match rem with
			SetVal(Empty(_))|SetVal(Set([], _)) -> Some(currmax) |
			SetVal(Set(h::t, l)) -> let r = (SetVal(Set(t, l))) in
					if h > currmax then aux r h else aux r currmax
	in
		match s with
			SetVal(Set(_, t)) -> (* utilizzo il rispettivo elemento neutro dell'operatore di max come valore di partenza *)
				if t = IntegerType then aux s (Int min_int)
				else if t = BooleanType then aux s (Bool false)
				else aux s (String "") |
			(* l'uso degli optional permette di non dover lanciare eccezioni se la funzione viene chiamata su un insieme vuoto *) 
			(* (che non è di per sé un utilizzo scorretto della funzione e quindi non richiederebbe l'uso di eccezioni) *)
			SetVal(Empty(_)) -> None |
			_ -> failwith("calling maxValue on a non-set value")
;;

(* minimo dell'insieme *)
let minValue (s : evT) : evT option =
	let rec aux rem currmax =
		match rem with
			SetVal(Empty(_))|SetVal(Set([], _)) -> Some(currmax) |
			SetVal(Set(h::t, l)) -> let r = (SetVal(Set(t, l))) in
					if h < currmax then aux r h else aux r currmax
	in
		match s with
		(* a differenza di maxValue, qui viene scelta la testa della lista come valore di partenza poiché non è possibile *)
		(* identificare l'elemento neutro dell'operatore di min per le stringhe (stringa di lunghezza massima composta solo dal carattere di valore massimo?) *)
			SetVal(Set(h::t, _)) -> aux s h |
			SetVal(Empty(_))|SetVal(Set([], _)) -> None |
			_ -> failwith("calling minValue on a non-set value")
;;

(* rimozione elemento dall'insieme *)
let remove (v : evT) (s : evT) : evT =
		match s with
			SetVal(Empty(l))|SetVal(Set([], l)) -> if l = (typeof v) then s else failwith("incompatible types") |
			SetVal(Set(lst, l)) ->
				if (typeof v) <> l then failwith("incompatible types")
				else
					let rec aux k = (* rimozione *)
						match k with
							[] -> [] |
							h::t -> if h = v then t else h::(aux t)
					in
					let res = (aux lst) in
						match res with (* questo match viene eseguito per evitare di restituire un set con lista vuota anziché un empty set *)
							[] -> SetVal(Empty(l)) |
							_ -> SetVal(Set(res, l))
		| _ -> failwith("calling remove on a non-set value")
;;

(* unione insiemistica *)
let union (s : evT) (t : evT) : evT =
	match (s, t) with 
	(SetVal(Empty(type1)), SetVal(Set(_, type2))) -> if type1 = type2 then t else failwith("incompatible types") |
	(SetVal(Set(_, type1)), SetVal(Empty(type2))) -> if type1 = type2 then s else failwith("incompatible types") |
	(* dovendo controllare la corrispondenza tra i tipi, serve matchare esplicitamente tutti i casi *)
	(* senza questo vincolo, il caso empty-empty non sarebbe servito, venendo coperto dai pattern (Empty(_), _) e (_, Empty(_)) *)
	(SetVal(Empty(type1)), SetVal(Empty(type2))) -> if type1 = type2 then s else failwith("incompatible types") |
	(SetVal(Set(lst1, type1)), SetVal(Set(lst2, type2))) ->
		if type1 <> type2 then failwith("incompatible types")
		else let rec aux list acc =
			match list with
				[] -> acc |
				h::ls -> aux ls (addToSet h acc)
			in aux lst1 t
;;

(* intersezione insiemistica *)
let intersection (s : evT) (t : evT) : evT =
	match (s, t) with 
	(SetVal(Empty(type1)), SetVal(Set(_, type2))) -> if type1 = type2 then s else failwith("incompatible types") |
	(SetVal(Set(_, type1)), SetVal(Empty(type2))) -> if type1 = type2 then t else failwith("incompatible types") |
	(* dovendo controllare la corrispondenza tra i tipi, serve matchare esplicitamente tutti i casi *)
	(* senza questo vincolo, il caso empty-empty non sarebbe servito, venendo coperto dai pattern (Empty(_), _) e (_, Empty(_)) *)
	(SetVal(Empty(type1)), SetVal(Empty(type2))) -> if type1 = type2 then s else failwith("incompatible types") |
	(SetVal(Set(lst1, type1)), SetVal(Set(lst2, type2))) ->
		if type1 <> type2 then failwith("incompatible types")
		else let rec aux list acc =
			match list with
				[] -> acc |
				h::ls -> if (belongsToSet h t) = (Bool true) then aux ls (addToSet h acc) else aux ls acc
			in aux lst1 (SetVal(Empty(type1)))
;;

(* differenza insiemistica *)
let difference (s : evT) (t : evT) : evT =
	match (s, t) with 
	(SetVal(Empty(type1)), SetVal(Set(_, type2))) -> if type1 = type2 then s else failwith("incompatible types") |
	(SetVal(Set(_, type1)), SetVal(Empty(type2))) -> if type1 = type2 then s else failwith("incompatible types") |
	(* dovendo controllare la corrispondenza tra i tipi, serve matchare esplicitamente tutti i casi *)
	(* senza questo vincolo, il caso empty-empty non sarebbe servito, venendo coperto dai pattern (Empty(_), _) e (_, Empty(_)) *)
	(SetVal(Empty(type1)), SetVal(Empty(type2))) -> if type1 = type2 then s else failwith("incompatible types") |
	(SetVal(Set(lst1, type1)), SetVal(Set(lst2, type2))) ->
		if type1 <> type2 then failwith("incompatible types")
		else let rec aux list acc =
			match list with
				[] -> acc |
				h::ls -> if (belongsToSet h t) = (Bool true) then aux ls acc else aux ls (addToSet h acc)
			in aux lst1 (SetVal(Empty(type1)))
;;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	Estring s -> String s |
	Etypename t -> String "" |
	Eemptyset l ->
		let typelabel = exp_to_label l in
			SetVal(Empty(typelabel)) |
	Esingleton s -> 
		let v = eval s r in 
			SetVal(Set([v], typeof v)) |
	AddToSet(el, set) ->
		let v = eval el r in
			let s = eval set r in
				addToSet v s |
	RemoveFromSet(el, set) ->
		let v = eval el r in
			let s = eval set r in
				remove v s |
	BelongsToSet(el, set) ->
		let v = eval el r in
			let s = eval set r in
				belongsToSet v s |
	IsZero a -> iszero (eval a r) |
	IsEmptyStr s -> isEmptyString (eval s r) |
	IsEmptySet s -> isEmpty (eval s r) |
	MaxValue s -> 
		let m = maxValue (eval s r) in
			(match m with 
			None -> failwith("Empty set has no max value ") |
			Some(d) -> d) |
	MinValue s ->
		let m = minValue (eval s r) in
			(match m with 
			None -> failwith("Empty set has no min value ") |
			Some(d) -> d) |
	Union(s, t) -> 
		let s1 = eval s r in
			let s2 = eval t r in
				union s1 s2 |
	Intersection(s, t) -> 
	let s1 = eval s r in
		let s2 = eval t r in
		intersection s1 s2 |
	Difference(s, t) -> 
		let s1 = eval s r in
			let s2 = eval t r in
				difference s1 s2 |
	Forall(p, s) ->
			let set = eval s r in
				forAll p set |
	Exists(p, s) ->
			let set = eval s r in
				exists p set |
	Filter(p, s) ->
			let set = eval s r in
				setFilter p set |
	Map(f, s) ->
			let set = eval s r in
				setMap f set |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Concat(s, t) -> concat (eval s r) (eval t r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
        Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
								_ -> failwith("non functional def"))
(* definizione di forall, exists, map, filter effettuata in questo modo per risolvere la dipendenza circolare con eval *)
and forAll (p : exp) (s : evT) : evT =
	match s with
	SetVal(Empty(_))|SetVal(Set([], _)) -> (Bool true) | (* caso base: proprietà vacuamente vera *)
	SetVal(Set(lst, _)) ->
		match p with
			Fun(_, _) -> (* Fun(arg, fBody) *)
				let env0 = emptyenv Unbound in
					let rec aux (l : evT list) acc =
						match l with
							[] -> acc |
							h::t -> aux t ((eval (FunCall(p, (evTToExp h))) env0)::acc)
				in
					let mapped =  aux lst [] (* applico il predicato a tutti gli elementi dell'insieme *)
					in List.fold_left et (Bool true) mapped (* metto in 'and' i risultati *)
(* un'alternativa sarebbe stata valutare il predicato su un elemento alla volta e continuare ricorsivamente solo se true *)
(* il vantaggio è la possibilità di fare short-circuiting e restituire subito false se il predicato fallisce *)
(* asintoticamente non cambia la complessità della funzione, ma la soluzione con map e fold risulta più elegante e affine ai principi di programmazione funzionale *)
and setMap (p : exp) (s : evT) : evT =
	match s with
	SetVal(Empty(_))|SetVal(Set([], _)) -> (s) | (* caso base: insieme vuoto *)
	SetVal(Set(lst, ty)) ->
		match p with
			Fun(_, _) -> (* Fun(arg, fBody) *)
				let env0 = emptyenv Unbound in
					let rec aux (l : evT list) acc =
						match l with
							[] -> acc |
							h::t -> aux t ((eval (FunCall(p, (evTToExp h))) env0)::acc)
				in
					SetVal(Set((aux lst []), ty)) (* applico la funzione a tutti gli elementi dell'insieme *)
and setFilter (p : exp) (s : evT) : evT =
	match s with
	SetVal(Empty(_))|SetVal(Set([], _)) -> s | (* caso base: insieme vuoto *)
	SetVal(Set(lst, ty)) ->
		match p with
			Fun(_, _) ->
				let env0 = emptyenv Unbound in
					let rec aux (l : evT list) acc =
						match l with
							[] -> acc |
							h::t -> if (eval (FunCall(p, (evTToExp h))) env0) = Bool(true) then aux t (h::acc) else aux t acc
				in
					let res = SetVal(Set((aux lst []), ty)) in (* effettuo un ulteriore pattern matching per restituire empty anziché un insieme contenente [] *)
						match res with
						SetVal(Set([], ty)) -> SetVal(Empty(ty)) |
						_ -> res
and exists (p : exp) (s : evT) : evT =
	match s with
	SetVal(Empty(_))|SetVal(Set([], _)) -> (Bool false) | (* caso base: proprietà vacuamente falsa *)
	SetVal(Set(lst, _)) ->
		match p with
			Fun(_, _) ->
				let env0 = emptyenv Unbound in
					let rec aux (l : evT list) acc =
						match l with
							[] -> acc |
							h::t -> aux t ((eval (FunCall(p, (evTToExp h))) env0)::acc)
				in
					let mapped =  aux lst [] (* applico il predicato a tutti gli elementi dell'insieme *)
					in List.fold_left vel (Bool false) mapped (* metto in 'or' i risultati *)
(* stesse considerazioni di forall sulla possibilità di implementare la funzione in maniera alternativa *)
;;

(* test dell'interprete - nel file testcases.ml sono presenti test più approfonditi sulle varie funzioni *)

let env0 = emptyenv Unbound;;

(* creazione espressione per l'insieme vuoto di interi *)
let es = Eemptyset(Etypename(IntegerType));;
(* valutazione dell'espressione *)
let emptysetvalue = eval es env0;;

(* creazione espressione per il singleton di interi *)
let ss = Esingleton(Eint(22));;
(* valutazione dell'espressione *)
let singletonvalue = eval ss env0;;

(* espressione per insieme di due elementi a partire dal singleton *)
let twoElementSetExp = AddToSet(Eint 11, ss);;

(* set contenente [0; 1; 5; 22] costruito ricorsivamente a partire da singleton *)
let setAExp = (AddToSet(Eint 5, AddToSet(Eint 0, AddToSet(Eint 1, ss))));;
let setA = eval setAExp env0;;

(* test appartenenza *)
eval (BelongsToSet(Eint 5, setAExp)) env0;; (* true *)
eval (BelongsToSet(Eint 15, setAExp)) env0;; (* false *)

(* test rimozione *)
eval (RemoveFromSet(Eint 22, setAExp)) env0;; (* rimuovo l'elemento 22 *)
eval (RemoveFromSet(Eint 21, setAExp)) env0;; (* set inalterato *)

(* test massimo e minimo *)
eval (MaxValue(setAExp)) env0;; (* 22 *)
eval (MinValue(setAExp)) env0;; (* 0 *)
eval (MinValue(Eemptyset(Etypename(StringType)))) env0;; (* exception *)

(* test insieme vuoto *)
eval(IsEmptySet(setAExp)) env0;; (* false *)
eval(IsEmptySet(es)) env0;; (* true *)

let setBExp = (AddToSet(Eint 5, AddToSet(Eint 2, AddToSet(Eint 1, ss))));;

(* test intersezione, unione, differenza *)
eval(Intersection(setAExp, setBExp)) env0;; (* 22, 1, 5 *)
eval(Union(setAExp, setBExp)) env0;; (* 0, 2, 22, 1, 5 *)
eval(Difference(setAExp, setBExp)) env0;; (* 0 *)

let pred = Fun("x", Ifthenelse(IsZero(Den "x"), Ebool true, Ebool false));;
let f = Fun("x", Prod(Den "x", Den "x"));;
let g = Fun("x", Concat(Den "x", Estring "issimo"));;
let setCExp = (AddToSet(Estring "bell", AddToSet(Estring "fort", Eemptyset(Etypename(StringType)))));;


(* test forall, exists, map, filter *)
eval(Forall(pred, setAExp)) env0;; (* false *)
eval(Exists(pred, setAExp)) env0;; (* true *)
eval(Filter(pred, setAExp)) env0;; (* 0 *)
eval(Map(f, setAExp)) env0;; (* 484, 1, 0, 25 *)
eval(Map(g, setCExp)) env0;; (* "bellissimo", "fortissimo" *)
