open BasicAst
open Datatypes
open PCUICAst
open PCUICAstUtils
open Universes0
open Utils

type __ = Obj.t

val term_forall_mkApps_ind :
  (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> (term, 'a1) coq_All
  -> 'a1) -> (universe -> 'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> 'a1)
  -> (name -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (name -> term -> 'a1 ->
  term -> 'a1 -> term -> 'a1 -> 'a1) -> (term -> term list -> __ -> 'a1 ->
  (term, 'a1) coq_All -> 'a1) -> (char list -> Level.t list -> 'a1) ->
  (inductive -> Level.t list -> 'a1) -> (inductive -> nat -> Level.t list ->
  'a1) -> ((inductive * nat) -> term -> 'a1 -> term -> 'a1 -> (nat * term)
  list -> (term, 'a1) tCaseBrsProp -> 'a1) -> (projection -> term -> 'a1 ->
  'a1) -> (term mfixpoint -> nat -> (term, 'a1, 'a1) tFixProp -> 'a1) ->
  (term mfixpoint -> nat -> (term, 'a1, 'a1) tFixProp -> 'a1) -> term -> 'a1
