(*
 * Assign9-starter.sml
 *
 * David Kauchak
 * 11/20/15
 *
 * This file includes code to help you implement exhaustive search
 * and backtracking branch and bound search.  All of this code was
 * copied from examples we looked at in class.  I have excluded
 * a few of the functions that we looked at in class that I thought
 * it was unlikely you would use, but feel free to copy them into
 * your code if you find them useful
 *
 *
 * Adam Stapelmann
 * Juan Zamudio
 * CS52, Assignment 9
 * 4-25-16
 *)


(*
 * Relevant lazy list functions from class.
 *)
exception LazyEmpty;

datatype 'a lazy_list =
           LazyNil
         | LazyCons of 'a * (unit -> 'a lazy_list);

fun lazyFirst LazyNil          = raise LazyEmpty
  | lazyFirst (LazyCons(x, _)) = x;

fun lazyRest LazyNil           = raise LazyEmpty
  | lazyRest (LazyCons(_, xs)) = xs ();

fun lazyMap _ LazyNil = LazyNil
  | lazyMap f (LazyCons(x, xs)) =
    LazyCons(f x, (lazyMap f) o xs);

fun lazyFilter _ LazyNil           = LazyNil
  | lazyFilter f (LazyCons(x, xs)) =
    if f x then
        LazyCons(x, (lazyFilter f) o xs)
    else
        lazyFilter f (xs ());

fun lazyToList LazyNil          = []
  | lazyToList (LazyCons(x, xs)) = x :: lazyToList (xs ());


(* 
 * Functions for producing lazy list state spaces 
 *)
fun odometerNextState []      = NONE
  | odometerNextState (x::xs) =
    if x = 5 then
        case odometerNextState xs of
             NONE   => NONE
           | SOME v => SOME (1::v)
    else
        SOME ((x+1)::xs);

fun odometerList NONE         = LazyNil
  | odometerList (SOME state) =
    LazyCons (state, fn () => odometerList (odometerNextState state));

fun producer _         NONE         = LazyNil
  | producer nextState (SOME state) =
    LazyCons(state, fn () => producer nextState (nextState state));

(*
 * Relevant functions for branch and bound search from class.
 *)
datatype bbResult = CORRECT | PENDING | INCORRECT;

datatype 's bbSearch = BBEmpty
                     | BBValue of 's
                                * (unit -> 's bbSearch)
                                * (unit -> 's bbSearch);

fun bbSolve bbPred BBEmpty                         = []
  | bbSolve bbPred (BBValue(s, increment, extend)) =
       case bbPred s of
            CORRECT   => s::(bbSolve bbPred (increment ()))
          | PENDING   => bbSolve bbPred (extend ())
          | INCORRECT => bbSolve bbPred (increment ());

fun bbProducer _     _     NONE     = BBEmpty
  | bbProducer bbinc bbext (SOME s) =
        BBValue(s,
                fn () => bbProducer bbinc bbext (bbinc s),
                fn () => bbProducer bbinc bbext (bbext s));

fun bbOdoIncr _   []      = NONE
  | bbOdoIncr top (x::xs) =
    if x < top then
        SOME ((x+1)::xs)
    else
        bbOdoIncr top xs;

fun bbOdoExt lst = SOME (1::lst);




(*
 *
 * Problem 1
 *
 * roomer problem
 *)

(* nextState function *)
fun nextRoomer [] = NONE
  | nextRoomer (x::xs) =
    if x = 5 then
        case nextRoomer xs of
            NONE => NONE
          | SOME v => SOME (1::v)
    else
        SOME ((x+1)::xs);

(* determines if a solution is good or not *)
fun isValidRoomer [] = false
  | isValidRoomer (5::xs) = false
  | isValidRoomer (x::y::5::xs) = false
  | isValidRoomer (x::y::1::xs) = false
  | isValidRoomer (b::c::f::m::s::[]) =
    if (b=c) orelse (b=f) orelse (b=m) orelse (b=s) orelse (c=f) orelse (c=m) orelse (c=s) orelse (f=m) orelse (f=s) orelse (m=s) then
        false
    else
        if c > m then
            false
        else
            if f = (c+1) orelse f = (c-1) then
                false
            else
                if s = (f+1) orelse s = (f-1) then
                    false
                else
                    true
  | isValidRoomer _ = false;

(* generate a lazy list of all possible solutions *)
fun roomerGen NONE = LazyNil
  | roomerGen (SOME k) = LazyCons(k, fn () => roomerGen (nextRoomer k));

(* Applies names to solutions *)
fun roomerNames (b::c::f::m::s::[]) = [("Baker",b), ("Cooper",c), ("Fletcher",f), ("Miller",m), ("Smith",s)]
  | roomerNames (x::xs) = [("Invalid", x)]
  | roomerNames [] = [("Invalid", 0)];

fun addAllNames lst = lazyMap roomerNames lst;

(* gives a lazylist of all solutions *)
val roomer1 = addAllNames (lazyFilter isGoodRoomer (roomerGen (SOME [1,1,1,1,1])));
val roomer2 = lazyRest roomer1;
val roomer3 = lazyRest roomer2;
val roomer4 = lazyRest roomer3;

(*
 * Problem 2
 *
 * Liars
 *)

(* nextState function *)
fun nextLiar [] = NONE
  | nextLiar (x::xs) =
    if x = 5 then
        case nextLiar xs of
            NONE => NONE
          | SOME v => SOME (1::v)
    else
        SOME ((x+1)::xs);

(* generate a lazy list of all possible solutions *)
fun liarGen NONE = LazyNil
  | liarGen (SOME k) = LazyCons(k, fn () => liarGen (nextLiar k));

(* will be helpful later *)
fun xor a b = ((a orelse b) andalso not(a andalso b));

(* Determines if the list is valid *)
fun isValidLiar [] = false
   |isValidLiar (d::n::r::t::w::[]) =
    let
        val d1 = (d=1);
        val d2 = (t=2);
        val n1 = (n=2);
        val n2 = (t=4);
        val r1 = (n=2);
        val r2 = (r=3);
        val t1 = (t=3);
        val t2 = (w=5);
        val w1 = (r=1);
        val w2 = (w=4);
    in
        if (d=n) orelse (d=r) orelse (d=t) orelse (d=w) orelse (n=r) orelse (n=t) orelse (n=w) orelse (r=t) orelse (r=w) orelse (t=w) then
            false
        else
            if (xor d1 d2) andalso (xor n1 n2) andalso (xor r1 r2) andalso (xor t1 t2) andalso (xor w1 w2) then
                true
            else
                false
    end
  | isValidLiar _ = false;

(* Adds names to answer *)
fun liarNames (d::n::r::t::w::[]) = [("Daxter",d), ("Navi",n), ("Raiden",r), ("Tingle",t), ("Waluigi",w)]
  | liarNames (x::xs) = [("Invalid", x)]
  | liarNames [] = [("Invalid", 0)];


fun addLiarNames lst = lazyMap liarNames lst;

(* gives a lazylist of all solutions *)
val liar = addLiarNames (lazyFilter isValidLiar (liarGen (SOME [1,1,1,1,1])));

(*
 * Problem 3
 *
 * N Queens
 *)

(* generate a list of n 1s *)
fun lenNList 0 = []
  | lenNList n = 1::(lenNList (n-1));

(* nextState function *)
fun nextQueen [] n = NONE
  | nextQueen (x::xs) n =
    if x = n then
        case nextQueen xs n of
            NONE => NONE
          | SOME v => SOME (1::v)
    else
        SOME ((x+1)::xs);

(* generate a lazylist of all possible solutions *)
fun queenGen NONE _ = LazyNil
  | queenGen (SOME k) n = LazyCons(k, fn () => queenGen (nextQueen k n) n);

(* returns true if the list contains two diagonal queens*)
fun containsBadDiagonal (u,v) [(w,x)] = (u+v)=(w+x) orelse (u-v)=(w-x)
  | containsBadDiagonal (u,v) (x::xs) =
    if (containsBadDiagonal (u,v) [x]) then
        true
    else
        (containsBadDiagonal (u,v) xs) orelse (containsBadDiagonal x xs)
  | containsBadDiagonal _ [] = false;

(* returns true if two queens are in the same row *)
fun containsBadRow (u,v) [(w,x)] = (v=x)
  | containsBadRow (u,v) (x::xs) =
    if (containsBadRow (u,v) [x]) then
        true
    else
        (containsBadRow (u,v) xs) orelse (containsBadRow x xs)
  | containsBadRow _ [] = false;

(* turns a list into a list of tuples *)
local
    fun helper _ [] = []
      | helper n (x::xs) = ((n,x)::(helper (n+1) xs))
in
fun listToTuples lst = helper 2 lst
end;

(* returns true if the arrangement is valid *)
fun isValidQueen [] = true
  | isValidQueen (x::xs) = not((containsBadRow (1,x) (listToTuples xs)) orelse (containsBadDiagonal (1,x) (listToTuples xs)));

(* returns all solutions for an n x n board *)
fun NQueens n = lazyFilter isValidQueen (queenGen (SOME (lenNList n)) n);

(* Answers *)
val a = NQueens 3;
val b = NQueens 5;
val b1 = lazyRest b;
val b2 = lazyRest b1;
val b3 = lazyRest b2;
val b4 = lazyRest b3;
val b5 = lazyRest b4;
val b6 = lazyRest b5;
val b7 = lazyRest b6;
val b8 = lazyRest b7;
val b9 = lazyRest b8;
val b10 = lazyRest b9;

(* Number of solns for n=8 *)
val c = 92;

(*
 * Problem 4
 *
 * Yachts
 *)

(* nextState function *)
fun nextYacht [] = NONE
  | nextYacht (x::xs) =
    if x = 5 then
        case nextYacht xs of
            NONE => NONE
          | SOME v => SOME (1::v)
    else
        SOME ((x+1)::xs);

(* generate a lazy list of all possible solutions *)
fun yachtGen NONE = LazyNil
  | yachtGen (SOME k) = LazyCons(k, fn () => yachtGen (nextYacht k));

(* checks if the string contains duplicate values *)
fun containsDuplicate [] = false
  | containsDuplicate (x::y::xs) =
    if (x=y) then
        true
    else
        (containsDuplicate (x::xs)) orelse (containsDuplicate (y::xs))
  | containsDuplicate _ = false;        

(* determines if the list is valid *)
fun isValidYacht [] = false
  | isValidYacht (bd::md::hd::cd::pd::by::my::hy::cy::py::[]) =
    if (by=1) andalso (my=2) andalso (hy=3) andalso (cy=4) andalso (py=5) andalso (bd=4) andalso (hd=5) andalso (pd<>1) andalso (pd<>5) andalso (md<>2) andalso (cd<>4) andalso ((md=1) orelse (cd=1)) andalso ((pd=2) orelse (pd=4)) andalso (cd<>1) andalso not(containsDuplicate [bd,md,hd,cd,pd]) andalso not(containsDuplicate [by,my,hy,cy,py])
    then
        true
    else
        false
  | isValidYacht _ = false;

(* Groups information with fathers *)
fun fatherNames (bd::md::hd::cd::pd::by::my::hy::cy::py::[]) = [("Sir Barnacle", bd, by), ("Mr. Moore",md, my), ("Mr. Hall",hd, hy), ("Colonel Downing",cd, cy), ("Dr. Parker",pd, py)]
  | fatherNames (x::xs) = [("Invalid", "", "")]
  | fatherNames [] = [("Invalid", "", "")];

(* Converts from a number to the corresponding daughter *)
fun toDaughter n =
    if n = 1 then
        "Gabrielle"
    else if n = 2 then
        "Lorna"
    else if n=3 then
        "Rosalind"
    else if n=4 then
        "Melissa"
    else
        "Mary Ann";

(* Adds information to list of numbers *)
fun addFatherNames lst = lazyMap (fatherNames o (map toDaughter)) lst;

val yachts = addFatherNames (lazyFilter isValidYacht (yachtGen (SOME [1,1,1,1,1,1,1,1,1,1])));

(*
 * Problem 5
 *
 * NQueens (again)
 *
 *)

(* generate a list of n 1s *)
fun lenNList 0 = []
  | lenNList n = 1::(lenNList (n-1));

(* Predicate function *)
fun queenPred n [] = PENDING
  | queenPred n x =
    if (isValidQueen x) then
        if length x = n then
            CORRECT
        else
            PENDING
    else
        INCORRECT;

(* Solves the queen problem via brach and bound *)
fun queenSolve n = bbSolve (queenPred n) (bbProducer (bbOdoIncr n) bbOdoExt (SOME (lenNList n)));

(* Outputs for sample values *)
val queens3 = queenSolve 3;
val queens5 = queenSolve 5;
val queens8 = queenSolve 8;

(*
 * Problem 6
 *
 * Halloween
 *
 *
 * state representation
 * 
 * first 5 elements: Ghost, ghost, wizard, batman, robin
 * second 5 elements: 63, 77, 83, 54, 84
 * third 5 elements: bubblesort, insertionsort, quicksort, mergesort, hash table
 *)

(* Returns the ghost with less candy *)
local
    fun scan x [a,b,c,d,e] =
        if x=a then
            63
        else if x=b then
            77
        else if x=c then
            83
        else if x=d then
            54
        else
            84
      | scan _ lst = 0
in
fun ghost a1 a2 [b1,b2,b3,b4,b5] =
    let
        val a = scan a1 [b1,b2,b3,b4,b5];
        val b = scan a2 [b1,b2,b3,b4,b5];
    in
        if a<b then
            a1
        else
            a2
    end
  | ghost a1 a2 lst = a1
end;

(* Halloween predicate function *)
fun halloweenPred [] = PENDING
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5] = in15 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4] = in14 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3] = in13 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2] = in12 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1] = in11 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5] = in10 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4] = in9 [a1,a2,a3,a4,a5,b1,b2,b3,b4]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3] = in8 [a1,a2,a3,a4,a5,b1,b2,b3]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2] = in7 [a1,a2,a3,a4,a5,b1,b2]
  | halloweenPred [a1,a2,a3,a4,a5,b1] = in6 [a1,a2,a3,a4,a5,b1]
  | halloweenPred [a1,a2,a3,a4,a5] = in5 [a1,a2,a3,a4,a5]
  | halloweenPred [a1,a2,a3,a4] = in4 [a1,a2,a3,a4]
  | halloweenPred [a1,a2,a3] = in3 [a1,a2,a3]
  | halloweenPred [a1,a2] = in2 [a1,a2]                         
  | halloweenPred [a1] = PENDING
  | halloweenPred _ = INCORRECT

and in2 [c4,c5] =
    if (not(containsDuplicate [c4,c5]) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in2 _ = INCORRECT

and in3 [c3,c4,c5] =
    if (not(containsDuplicate [c3,c4,c5]) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in3 _ = INCORRECT

and in4 [c2,c3,c4,c5] =
    if (not(containsDuplicate [c2,c3,c4,c5]) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in4 _ = INCORRECT

and in5 [c1,c2,c3,c4,c5] =
    if (not(containsDuplicate [c1,c2,c3,c4,c5]) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in5 _ = INCORRECT

and in6 [b5,c1,c2,c3,c4,c5] =
    if (not(containsDuplicate [c1,c2,c3,c4,c5]) andalso ((b5=c2)  orelse (b5=3)) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in6 _ = INCORRECT

and in7 [b4,b5,c1,c2,c3,c4,c5] =
    if (not((containsDuplicate [b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4,c5])) andalso ((b5=c2)  orelse (b5=3)) andalso (b4=c1) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in7 _ = INCORRECT

and in8 [b3,b4,b5,c1,c2,c3,c4,c5] =
    if (not((containsDuplicate [b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4,c5])) andalso ((b5=c2)  orelse (b5=3)) andalso (b4=c1) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in8 _ = INCORRECT

and in9 [b2,b3,b4,b5,c1,c2,c3,c4,c5] =
    if (not((containsDuplicate [b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4,c5])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso (b4=c1) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in9 _ = INCORRECT

and in10 [b1,b2,b3,b4,b5,c1,c2,c3,c4,c5] =
    if (not((containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4,c5])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso (b4=c1) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in10 _ = INCORRECT

and in11 [a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5] =
    if (not((containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4,c5])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in11 _ = INCORRECT

and in12 [a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5] =
    if (not((containsDuplicate [a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4,c5])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in12 _ = INCORRECT

and in13 [a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5] =
    if (not((containsDuplicate [a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4,c5])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in13 _ = INCORRECT

and in14 [a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5] =
    if (not((containsDuplicate [a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4,c5])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in14 _ = INCORRECT
                          
and in15 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5] =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4,c5])) andalso ((c5=a1) orelse (c5=a2)) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3) andalso (c4=1) andalso ((ghost a1 a2 [b1,b2,b3,b4,b5])=c5)) then
        CORRECT
    else
        INCORRECT
  | in15 _ = INCORRECT;


(* Adds information to output string *)
local
    fun costumeSearch n [a,b,c,d,e] =
        if a=n orelse b=n then
            "Ghost"
        else if c=n then
            "Wizard"
        else if d=n then
            "Batman"
        else
            "Robin"
      | costumeSearch _ _ = "Null"
    fun candySearch n [a,b,c,d,e] =
        if a = n then
            "63"
        else if b = n then
            "77"
        else if c = n then
            "83"
        else if d = n then
            "54"
        else
            "84"
      | candySearch _ _ = "Null"                              
    fun algSearch n [a,b,c,d,e] =
        if a = n then
            "BubbleSort"
        else if b = n then
            "InsertionSort"
        else if c = n then
            "QuickSort"
        else if d = n then
            "MergeSort"
        else
            "Hash Table"
      | algSearch _ _ = "Null"                            
in
fun halloweenNames [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5] = 
    let
        val cst = [a1,a2,a3,a4,a5];
        val cdy = [b1,b2,b3,b4,b5];
        val alg = [c1,c2,c3,c4,c5];
    in
        [("Bruce", (costumeSearch 1 cst), (candySearch 1 cdy), (algSearch 1 alg)), ("Bull", (costumeSearch 2 cst),(candySearch 2 cdy), (algSearch 2 alg)), ("Chen", (costumeSearch 3 cst),(candySearch 3 cdy),(algSearch 3 alg)), ("Greenberg",(costumeSearch 4 cst),(candySearch 4 cdy),(algSearch 4 alg)), ("Wu", (costumeSearch 5 cst),(candySearch 5 cdy),(algSearch 5 alg))]
    end
  | halloweenNames _ = [("Null", "Null", "Null", "Null")]
end;

(* Solves the branch and bound problem (numerically) *)
val halloweenSolve = bbSolve halloweenPred (bbProducer (bbOdoIncr 5) bbOdoExt (SOME (lenNList 15)));

(* Puts the numerical answer into words *)
val halloween = map halloweenNames halloweenSolve;


(*
 * Problem 7
 *
 *
 * Time for one test = 10^-6 = One microsecond/test
 * 
 * Number of tests total = (5^5)^3 = 30,517,578,125 tests
 *
 * Total time = [10^-6][(5^5)^3] = 30,518 seconds
 *
 * 30,518 seconds = 8hrs 29mins
 *
 *
 *)
