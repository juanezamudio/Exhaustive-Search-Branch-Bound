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
fun isGoodRoomer [] = false
  | isGoodRoomer (5::xs) = false
  | isGoodRoomer (x::y::5::xs) = false
  | isGoodRoomer (x::y::1::xs) = false
  | isGoodRoomer (b::c::f::m::s::[]) =
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
  | isGoodRoomer _ = false;

(* generate a lazy list of all possible solutions *)
fun roomerGen NONE = LazyNil
  | roomerGen (SOME k) = LazyCons(k, fn () => roomerGen (nextRoomer k));

fun roomerNames (b::c::f::m::s::[]) = [("Baker",b), ("Cooper",c), ("Fletcher",f), ("Miller",m), ("Smith",s)]
  | roomerNames (x::xs) = [("Invalid", x)]
  | roomerNames [] = [("Invalid", 0)];


fun addAllNames lst = lazyMap roomerNames lst;

(* gives a lazylist of all solutions *)
val roomer = addAllNames (lazyFilter isGoodRoomer (roomerGen (SOME [1,1,1,1,1])));





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
val c = 92;

<<<<<<< HEAD



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

fun queenSolve n = bbSolve (queenPred n) (bbProducer (bbOdoIncr n) bbOdoExt (SOME (lenNList n)));


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

fun containsDuplicate [] = false
  | containsDuplicate (x::y::xs) =
    if (x=y) then
        true
    else
        (containsDuplicate (x::xs)) orelse (containsDuplicate (y::xs))
  | containsDuplicate _ = false;

(*
fun halloweenPred [] = PENDING
  | halloweenPred [a1] = PENDING
  | halloweenPred [a1,a2] =
    if (not(containsDuplicate [a1,a2])) then
        PENDING
    else
        INCORRECT
  | halloweenPred [a1,a2,a3] =
    if (not(containsDuplicate [a1,a2,a3])) then
        PENDING
    else
        INCORRECT
  | halloweenPred (a1::a2::a3::a4::[]) =
    if (not(containsDuplicate [a1,a2,a3,a4])) then
        PENDING
    else
        INCORRECT
  | halloweenPred (a1::a2::a3::a4::a5::[]) =
    if (not(containsDuplicate [a1,a2,a3,a4,a5])) then
        PENDING
    else
        INCORRECT
  | halloweenPred (a1::a2::a3::a4::a5::b1::[]) =
    if (not((containsDuplicate [a1,a2,a3,a4,a5])) andalso ((b1=5) orelse (b1=2))) then
        PENDING
    else
        INCORRECT
  | halloweenPred (a1::a2::a3::a4::a5::b1::b2::[]) =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2])) andalso ((b2=2) orelse (b2=3)) andalso ((b2=a1) orelse (b2=a2)) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5))) then
        PENDING
    else
        INCORRECT
  | halloweenPred (a1::a2::a3::a4::a5::b1::b2::b3::[]) =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3])) andalso ((b2=2) orelse (b2=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5))) then
        PENDING
    else
        INCORRECT
  | halloweenPred (a1::a2::a3::a4::a5::b1::b2::b3::b4::[]) =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4])) andalso ((b2=2) orelse (b2=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5))) then
        PENDING
    else
        INCORRECT
  | halloweenPred (a1::a2::a3::a4::a5::b1::b2::b3::b4::b5::[]) =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5])) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3)) then
        PENDING
    else
        INCORRECT
  | halloweenPred (a1::a2::a3::a4::a5::b1::b2::b3::b4::b5::c1::[]) =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5])) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3)) then
        PENDING
    else
        INCORRECT
  | halloweenPred (a1::a2::a3::a4::a5::b1::b2::b3::b4::b5::c1::c2::[]) =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3)) then
        PENDING
    else
        INCORRECT
  | halloweenPred (a1::a2::a3::a4::a5::b1::b2::b3::b4::b5::c1::c2::c3::[]) =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3)) then
        PENDING
    else
        INCORRECT
    | halloweenPred (a1::a2::a3::a4::a5::b1::b2::b3::b4::b5::c1::c2::c3::c4::[]) =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | halloweenPred (a1::a2::a3::a4::a5::b1::b2::b3::b4::b5::c1::c2::c3::c4::c5::[]) =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4,c5])) andalso ((c5=a1) orelse (c5=a2)) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3) andalso (c4=1)) then
        CORRECT
    else
        INCORRECT
  | halloweenPred _ = INCORRECT;



val halloweenSolve = bbSolve halloweenPred (bbProducer (bbOdoIncr 5) bbOdoExt (SOME (lenNList 15)));
*)


fun halloweenPred [] = PENDING
  | halloweenPred [a1] = PENDING
  | halloweenPred [a1,a2] = in2 [a1,a2]
  | halloweenPred [a1,a2,a3] = in3 [a1,a2,a3]
  | halloweenPred [a1,a2,a3,a4] = in4 [a1,a2,a3,a4]
  | halloweenPred [a1,a2,a3,a4,a5] = in5 [a1,a2,a3,a4,a5]
  | halloweenPred [a1,a2,a3,a4,a5,b1] = in6 [a1,a2,a3,a4,a5,b1]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2] = in7 [a1,a2,a3,a4,a5,b1,b2]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3] = in8 [a1,a2,a3,a4,a5,b1,b2,b3]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4] = in9 [a1,a2,a3,a4,a5,b1,b2,b3,b4]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5] = in10 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1] = in11 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2] = in12 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3] = in13 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4] = in14 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4]
  | halloweenPred [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5] = in15 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5]
  | halloweenPred _ = INCORRECT

and in2 [a1,a2] =
    if a1=a2 then
        INCORRECT
    else
        PENDING
  | in2 _ = INCORRECT

and in3 [a1,a2,a3] =
    if (not(containsDuplicate [a1,a2,a3])) then
        PENDING
    else
        INCORRECT
  | in3 _ = INCORRECT

and in4 [a1,a2,a3,a4] =
    if (not(containsDuplicate [a1,a2,a3,a4])) then
        PENDING
    else
        INCORRECT
  | in4 _ = INCORRECT

and in5 [a1,a2,a3,a4,a5] =
    if (not(containsDuplicate [a1,a2,a3,a4,a5])) then
        PENDING
    else
        INCORRECT
  | in5 _ = INCORRECT

and in6 [a1,a2,a3,a4,a5,b1] =
    if (not((containsDuplicate [a1,a2,a3,a4,a5])) andalso ((b1=5) orelse (b1=2))) then
        PENDING
    else
        INCORRECT
  | in6 _ = INCORRECT

and in7 [a1,a2,a3,a4,a5,b1,b2] =
     if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (b1=b2)) andalso ((b2=2) orelse (b2=3)) andalso ((b2=a1) orelse (b2=a2)) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5))) then
        PENDING
    else
        INCORRECT
  | in7 _ = INCORRECT

and in8 [a1,a2,a3,a4,a5,b1,b2,b3] =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3])) andalso ((b2=2) orelse (b2=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b3=a5) andalso ((b1=2) orelse (b1=5)) andalso ((b2=2) orelse (b2=5))) then
        PENDING
    else
        INCORRECT
  | in8 _ = INCORRECT

and in9 [a1,a2,a3,a4,a5,b1,b2,b3,b4] =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4])) andalso ((b2=2) orelse (b2=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5))) then
        PENDING
    else
        INCORRECT
  | in9 _ = INCORRECT
3
and in10 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5] =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5])) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3)) then
        PENDING
    else
        INCORRECT
  | in10 _ = INCORRECT

and in11 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1] =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5])) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3)) then
        PENDING
    else
        INCORRECT
  | in11 _ = INCORRECT

and in12 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2] =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3)) then
        PENDING
    else
        INCORRECT
  | in12 _ = INCORRECT

and in13 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3] =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3)) then
        PENDING
    else
        INCORRECT
  | in13 _ = INCORRECT

and in14 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4] =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4])) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3) andalso (c4=1)) then
        PENDING
    else
        INCORRECT
  | in14 _ = INCORRECT

and in15 [a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5] =
    if (not((containsDuplicate [a1,a2,a3,a4,a5]) orelse (containsDuplicate [b1,b2,b3,b4,b5]) orelse (containsDuplicate [c1,c2,c3,c4,c5])) andalso ((c5=a1) orelse (c5=a2)) andalso (b5=c2) andalso ((b2=2) orelse (b5=2)) andalso ((b2=3) orelse (b5=3)) andalso ((b2=a1) orelse (b2=a2)) andalso (b4=c1) andalso (b3=a5) andalso ((b2=2) orelse (b1=2)) andalso ((b2=5) orelse (b1=5)) andalso (b5=a3) andalso (c4=1)) then
        CORRECT
    else
        INCORRECT
  | in15 _ = INCORRECT;

val halloweenSolve = bbSolve halloweenPred (bbProducer (bbOdoIncr 5) bbOdoExt (SOME (lenNList 15)));

>>>>>>> e4985c082e3241ddbf0f94a2cb77a53f312fd4a5
