(* IMPORTARE IL CODICE DELL'INTERPRETE PRIMA DI ESEGUIRE I TEST IN QUESTO FILE *)
(* creazione ambiente vuoto*)
let env0 = emptyenv Unbound;;

(* seguono i test effettuati direttamente sugli evT per semplicità *)
(* ----------------------------------------------------------------------------- *)
(* test di appartenenza *)
belongsToSet (Eint(22)) emptysetvalue env0;; (* true *)
belongsToSet (Eint(2)) singletonvalue env0;; (* false *)
belongsToSet (Eint(22)) emptysetvalue env0;; (* false *)

(* ----------------------------------------------------------------------------- *)
(* test aggiunta elementi *)
addToSet (Eint(3)) emptysetvalue env0;; (* SetVal (Set ([Int 3], IntegerType)) *)
addToSet (Eint(3)) singletonvalue env0;; (* SetVal (Set ([Int 3; Int 22], IntegerType)) *)
addToSet (Eint(22)) singletonvalue env0;; (* SetVal (Set ([Int 22], IntegerType)) *)

(* ----------------------------------------------------------------------------- *)
(* test vuoto *)
isEmpty (SetVal(Set([Int 8], IntegerType)));; (* false *)
isEmpty (SetVal(Empty BooleanType));; (* true *)

(* ----------------------------------------------------------------------------- *)
(* test max *)
maxValue (SetVal(Empty(IntegerType)));; (* none *)
maxValue (SetVal(Set([Int 1;Int 22;Int 91;Int (-15)], IntegerType)));; (* some 91 *)
maxValue (SetVal(Set([Bool true; Bool false], BooleanType)));; (* some true *)
maxValue (SetVal(Set([String "aaaa"; String "12345"; String "zzzz"; String ""], StringType)));; (* some "zzzz "*)
maxValue (SetVal(Set([Int 1; Int 2], IntegerType)));; (* some 2 *)

(* ----------------------------------------------------------------------------- *)
(* test min *)
minValue (SetVal(Empty(IntegerType)));; (* none *)
minValue (SetVal(Set([Int 1;Int 22;Int 91;Int (-15)], IntegerType)));; (* some -15 *)
minValue (SetVal(Set([Bool true; Bool false], BooleanType)));; (* some false *)
minValue (SetVal(Set([String "aaaa"; String "12345"; String "zzzz"; String ""], StringType)));; (* some "" *)
minValue (SetVal(Set([Int 1; Int 2], IntegerType)));; (* some 1 *)

(* ----------------------------------------------------------------------------- *)
(* test sottoinsieme *)
isSubset (SetVal(Empty(IntegerType))) (SetVal(Set([Int 1], IntegerType)));; (* true *)
isSubset (SetVal(Set([Int 1], IntegerType))) (SetVal(Empty(IntegerType)));; (* false *)
isSubset (SetVal(Set([Int 1], IntegerType))) (SetVal(Set([Int 1; Int 2; Int 3], IntegerType)));; (* true *)
isSubset (SetVal(Set([Int 5], IntegerType))) (SetVal(Set([Int 1; Int 2; Int 3], IntegerType)));; (* false *)
isSubset (SetVal(Empty(IntegerType))) (SetVal(Empty(IntegerType)));; (* true *)
isSubset (SetVal(Empty(IntegerType))) (SetVal(Set([String "a"], StringType)));; (* incompatible types *)
isSubset (SetVal(Set([Bool true], BooleanType))) (SetVal(Set([Bool true], BooleanType)));; (* true *)

(* ----------------------------------------------------------------------------- *)
(* test rimozione *)
remove (Int 1) (SetVal(Set([String "a"], StringType)));; (* incompatible types *)
remove (Int 1) (SetVal(Empty(StringType)));; (* incompatible types *)
remove (Int 1) (SetVal(Empty(IntegerType)));; (* empty *)
remove (Int 1) (SetVal(Set([Int 1], IntegerType)));; (* empty *)
remove (Int 2) (SetVal(Set([Int 3], IntegerType)));; (* unchanged *)
remove (Int 2) (SetVal(Set([Int 1; Int 3], IntegerType)));; (* [1; 3] *)
remove (String "bye") (SetVal(Set([String "aaaa"; String "xyz"; String "bye"], StringType)));; (* ["aaaa"; "xyz"] *)
remove (Bool true) (SetVal(Set([Bool false; Bool true], BooleanType)));; (* [false] *)

(* ----------------------------------------------------------------------------- *)
(* test forall *)
(* per ogni x in set, x = 0 *)
forAll (Fun("x", Ifthenelse(IsZero(Den "x"), Ebool true, Ebool false))) (SetVal(Set([Int 1; Int 0; Int 0; Int 2], IntegerType)));; (* false *)
forAll (Fun("x", Ifthenelse(IsZero(Den "x"), Ebool true, Ebool false))) (SetVal(Set([Int 0; Int 0], IntegerType)));; (* true *)

(* per ogni x in set, x è la stringa vuota *)
forAll (Fun("x", Ifthenelse(IsEmptyStr(Den "x"), Ebool true, Ebool false))) (SetVal(Set([String "a"], StringType)));; (* false *)
forAll (Fun("x", Ifthenelse(IsEmptyStr(Den "x"), Ebool true, Ebool false))) (SetVal(Set([String ""; String ""], StringType)));; (* true *)

(* per ogni x in set, x ≠ 2 *)
forAll (Fun("x", Ifthenelse(Eq(Den "x", Eint 2), Ebool false, Ebool true))) (SetVal(Set([Int 1; Int 0; Int 0], IntegerType)));; (* true *)
forAll (Fun("x", Ifthenelse(Eq(Den "x", Eint 2), Ebool false, Ebool true))) (SetVal(Set([Int 2; Int 1; Int 1; Int 1], IntegerType)));; (* false *)

(* predicati composti *)
(* per ogni x in set, x = 0 oppure x = 5 *)
forAll (Fun("x", Ifthenelse(Or(IsZero(Den "x"), Eq(Den "x", Eint 5)), Ebool true, Ebool false))) (SetVal(Set([Int 0; Int 5], IntegerType)));; (* true *)
forAll (Fun("x", Ifthenelse(Or(IsZero(Den "x"), Eq(Den "x", Eint 5)), Ebool true, Ebool false))) (SetVal(Set([Int 1], IntegerType)));; (* false *)

(* ----------------------------------------------------------------------------- *)
(* test exists *)
(* esiste un x in set, x = 0 *)
exists (Fun("x", Ifthenelse(IsZero(Den "x"), Ebool true, Ebool false))) (SetVal(Set([Int 1; Int 0; Int 0; Int 2], IntegerType)));; (* true *)
exists (Fun("x", Ifthenelse(IsZero(Den "x"), Ebool true, Ebool false))) (SetVal(Set([Int 1; Int 1], IntegerType)));; (* false *)

(* esiste un x in set, x è la stringa vuota *)
exists (Fun("x", Ifthenelse(IsEmptyStr(Den "x"), Ebool true, Ebool false))) (SetVal(Set([String "a"], StringType)));; (* false *)
exists (Fun("x", Ifthenelse(IsEmptyStr(Den "x"), Ebool true, Ebool false))) (SetVal(Set([String ""; String "a"], StringType)));; (* true *)

(* esiste un x in set, x ≠ 2 *)
exists (Fun("x", Ifthenelse(Eq(Den "x", Eint 2), Ebool false, Ebool true))) (SetVal(Set([Int 2; Int 2; Int 2], IntegerType)));; (* false *)
exists (Fun("x", Ifthenelse(Eq(Den "x", Eint 2), Ebool false, Ebool true))) (SetVal(Set([Int 2; Int 1; Int 1; Int 1], IntegerType)));; (* true *)

(* predicati composti *)
(* esiste un x in set, x = 0 oppure x = 5 *)
exists (Fun("x", Ifthenelse(Or(IsZero(Den "x"), Eq(Den "x", Eint 5)), Ebool true, Ebool false))) (SetVal(Set([Int 0; Int 5], IntegerType)));; (* true *)
exists (Fun("x", Ifthenelse(Or(IsZero(Den "x"), Eq(Den "x", Eint 5)), Ebool true, Ebool false))) (SetVal(Set([Int 1], IntegerType)));; (* false *)

(* ----------------------------------------------------------------------------- *)
(* test unione *)
union (SetVal(Set([Int 0;Int 1;Int 2;Int 3], IntegerType))) (SetVal(Set([Int 2;Int 3;Int 4;Int 5], IntegerType)));; (* 0, 1, 2, 3, 4, 5 *)
(* elemento neutro dell'unione *)
union (SetVal(Empty(IntegerType))) (SetVal(Set([Int 2;Int 3;Int 4;Int 5], IntegerType)));;
union (SetVal(Set([String "c"], StringType))) (SetVal(Set([String "b";String "a"], StringType)));; (* "a", "b", "c" *)

(* ----------------------------------------------------------------------------- *)
(* test intersezione *)
intersection (SetVal(Set([Int 0;Int 1;Int 2;Int 3], IntegerType))) (SetVal(Set([Int 2;Int 3;Int 4;Int 5], IntegerType)));; (* 2, 3 *)
(* elemento assorbente dell'intersezione *)
intersection (SetVal(Empty(IntegerType))) (SetVal(Set([Int 2;Int 3;Int 4;Int 5], IntegerType)));;
(* intersezione vuota *)
intersection (SetVal(Set([String "c"], StringType))) (SetVal(Set([String "b";String "a"], StringType)));;

(* ----------------------------------------------------------------------------- *)
(* test differenza *)
difference (SetVal(Empty(StringType))) (SetVal(Set([String "a"; String "b"], StringType)));; (* empty *)
difference (SetVal(Set([String "a"; String "b"], StringType))) (SetVal(Empty(StringType)));; (* "a", "b" *)
difference (SetVal(Set([Int 22; Int 11], IntegerType))) (SetVal(Set([Int 11], IntegerType)));; (* 22 *)
difference (SetVal(Set([Int 11], IntegerType))) (SetVal(Set([Int 22; Int 11], IntegerType)));; (* empty *)

(* ----------------------------------------------------------------------------- *)
(* test setFilter *)
(* filtra gli x in set tali che x = 0 oppure x = 5 *)
setFilter (Fun("x", Ifthenelse(Or(IsZero(Den "x"), Eq(Den "x", Eint 5)), Ebool true, Ebool false))) (SetVal(Set([Int (-1); Int 0; Int 5; Int 13], IntegerType)));; (* 0; 5 *)
setFilter (Fun("x", Ifthenelse(Or(IsZero(Den "x"), Eq(Den "x", Eint 5)), Ebool true, Ebool false))) (SetVal(Set([Int (-1); Int 13], IntegerType)));; (* empty *)

(* filtra tutti gli x in set tali che x*x = 25 *)
setFilter (Fun("x", Ifthenelse(Eq(Prod(Den "x", Den "x"), Eint 25), Ebool true, Ebool false))) (SetVal(Set([Int (-5); Int 1; Int 45; Int 5], IntegerType)));; (* -5; 5 *)
setFilter (Fun("x", Ifthenelse(Eq(Prod(Den "x", Den "x"), Eint 25), Ebool true, Ebool false))) (SetVal(Set([Int 1; Int 45], IntegerType)));; (* empty *)

(* filtra tutti gli x in set tali che x non è la stringa vuota *)
setFilter (Fun("x", Ifthenelse(IsEmptyStr(Den "x"), Ebool false, Ebool true))) (SetVal(Set([String "aaa"; String ""; String "bbb"], StringType)));; (* "aaa"; "bbb" *)

(* ----------------------------------------------------------------------------- *)
(* test setMap*)
(* quadrato di tutti gli elementi dell'insieme *)
setMap (Fun("x", Prod(Den "x", Den "x"))) (SetVal(Set([Int 0;Int 1;Int 2;Int 3], IntegerType)));; (* 0; 1; 4; 9 *)

(* doppio più uno di tutti gli elementi dell'insieme *)
setMap (Fun("x", Sum(Prod(Den "x", Eint 2), Eint 1))) (SetVal(Set([Int 0;Int 1;Int 2;Int 3], IntegerType)));; (* 1; 3; 5; 7 *)

(* negazione logica dell'insieme *)
setMap (Fun("x", Not(Den "x"))) (SetVal(Set([Bool false], BooleanType)));; (* true *)
setMap (Fun("x", Not(Den "x"))) (SetVal(Empty(BooleanType)));; (* empty *)

(* concatenazione di tutti gli elementi con la stringa "issimo" *)
setMap (Fun("x", Concat(Den "x", Estring "issimo"))) (SetVal(Set([String "bell"; String "fort"], StringType)));; (* "bellissimo"; "fortissimo" *)

(* esempi di input malformati: gestiti automaticamente dal type checker *)
setMap (Fun("x", Sum(Prod(Den "x", Eint 2), Eint 1))) (SetVal(Set([String "bell"; String "fort"], StringType)));;
setMap (Fun("x", Concat(Den "x", Estring "issimo"))) (SetVal(Set([Int 0;Int 1;Int 2;Int 3], IntegerType)));;
setMap (Fun("x", Not(Den "x"))) (SetVal(Set([Int 0;Int 1;Int 2;Int 3], IntegerType)));;
