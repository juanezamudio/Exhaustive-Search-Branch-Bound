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
