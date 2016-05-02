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

(*
 * Problem 4
 *
 * Yachts
 *)

(* nextState function *)
fun nextDaughter [] = NONE
  | nextDaughter (x::xs) =
    if x = 5 then
        case nextDaughter xs of
            NONE => NONE
          | SOME v => SOME (1::v)
    else
        SOME ((x+1)::xs);

(* generate a lazy list of all possible solutions *)
fun daughterGen NONE = LazyNil
  | daughterGen (SOME k) = LazyCons(k, fn () => daughterGen (nextDaughter k));

(* determines if the list is valid *)
fun isValidDaughter [] = false
  | isValidDaughter (b::m::h::d::p::[]) = 
    
        
