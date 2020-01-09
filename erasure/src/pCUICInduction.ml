open BasicAst
open Datatypes
open PCUICAst
open PCUICAstUtils
open Universes0
open Utils

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val term_forall_mkApps_ind :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> (term, 'a1)
    coq_All -> 'a1) -> (universe -> 'a1) -> (name -> term -> 'a1 -> term ->
    'a1 -> 'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (name ->
    term -> 'a1 -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (term -> term list
    -> __ -> 'a1 -> (term, 'a1) coq_All -> 'a1) -> (char list -> Level.t list
    -> 'a1) -> (inductive -> Level.t list -> 'a1) -> (inductive -> nat ->
    Level.t list -> 'a1) -> ((inductive * nat) -> term -> 'a1 -> term -> 'a1
    -> (nat * term) list -> (term, 'a1) tCaseBrsProp -> 'a1) -> (projection
    -> term -> 'a1 -> 'a1) -> (term mfixpoint -> nat -> (term, 'a1, 'a1)
    tFixProp -> 'a1) -> (term mfixpoint -> nat -> (term, 'a1, 'a1) tFixProp
    -> 'a1) -> term -> 'a1 **)

let rec term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 = function
| Coq_tRel n -> x n
| Coq_tVar i -> x0 i
| Coq_tEvar (n, l) ->
  x1 n l
    (let rec auxt' l0 auxt =
       match l0 with
       | [] -> All_nil
       | t1 :: l1 ->
         All_cons (t1, l1, (auxt t1 __), (auxt' l1 (fun y _ -> auxt y __)))
     in auxt' l (fun y _ ->
          term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
            x13 y))
| Coq_tSort u -> x2 u
| Coq_tProd (na, t1, t2) ->
  x3 na t1
    (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      t1) t2
    (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      t2)
| Coq_tLambda (na, t1, t2) ->
  x4 na t1
    (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      t1) t2
    (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      t2)
| Coq_tLetIn (na, t1, t2, t3) ->
  x5 na t1
    (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      t1) t2
    (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      t2) t3
    (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      t3)
| Coq_tApp (t1, t2) ->
  let p = decompose_app (Coq_tApp (t1, t2)) in
  let (t3, l) = p in
  x6 t3 l __
    (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      t3)
    (let rec f = function
     | [] -> All_nil
     | y :: l1 ->
       All_cons (y, l1,
         (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
           x13 y), (f l1))
     in f l)
| Coq_tConst (k, ui) -> x7 k ui
| Coq_tInd (ind, ui) -> x8 ind ui
| Coq_tConstruct (ind, n, ui) -> x9 ind n ui
| Coq_tCase (indn, t1, t2, brs) ->
  x10 indn t1
    (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      t1) t2
    (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      t2) brs
    (let rec auxt' l auxt =
       match l with
       | [] -> All_nil
       | p :: l0 ->
         All_cons (p, l0, (auxt (snd p) __),
           (auxt' l0 (fun y _ -> auxt y __)))
     in auxt' brs (fun y _ ->
          term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
            x13 y))
| Coq_tProj (p, t1) ->
  x11 p t1
    (term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      t1)
| Coq_tFix (mfix, idx) ->
  x12 mfix idx
    (let rec auxt' l auxt =
       match l with
       | [] -> All_nil
       | d :: l0 ->
         All_cons (d, l0, ((auxt d.dtype __), (auxt d.dbody __)),
           (auxt' l0 (fun y _ -> auxt y __)))
     in auxt' mfix (fun y _ ->
          term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
            x13 y))
| Coq_tCoFix (mfix, idx) ->
  x13 mfix idx
    (let rec auxt' l auxt =
       match l with
       | [] -> All_nil
       | d :: l0 ->
         All_cons (d, l0, ((auxt d.dtype __), (auxt d.dbody __)),
           (auxt' l0 (fun y _ -> auxt y __)))
     in auxt' mfix (fun y _ ->
          term_forall_mkApps_ind x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
            x13 y))
