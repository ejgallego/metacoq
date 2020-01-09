(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.CRelationClasses ProofIrrelevance.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUtils.

From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.

Local Set Keyed Unification.
Set Equations With UIP.

Require Import ssreflect ssrbool.

Definition max_list (u : list universe) v : universe :=
  List.fold_left (fun u v => Universe.sort_of_product v u) u v.

Require Import Morphisms.
Section UniverseLemmas.
  Context {cf:checker_flags}.

  Lemma NEL_forallb_app {A:Set} (P : A -> bool) l l' :
    NEL.forallb P (NEL.app l l') =
    NEL.forallb P l && NEL.forallb P l'.
  Proof.
    induction l.
    - reflexivity.
    - cbn. rewrite IHl. apply andb_assoc.
  Qed.

  Lemma is_prop_sup u s :
    Universe.is_prop (Universe.sup u s)
    = Universe.is_prop u && Universe.is_prop s.
  Proof.
    apply NEL_forallb_app.
  Qed.

  Ltac unfold_eq_universe
    := unfold eq_universe in *; destruct check_univs; [intros v Hv|trivial].

  Lemma sort_of_product_idem φ s
    : eq_universe φ (Universe.sort_of_product s s) s.
  Proof.
    unfold Universe.sort_of_product. destruct (Universe.is_prop s).
    - reflexivity.
    - unfold_eq_universe. rewrite val_sup; lia.
  Qed.

  Lemma eq_universe_sup_assoc φ s1 s2 s3 :
    eq_universe φ (Universe.sup s1 (Universe.sup s2 s3))
                  (Universe.sup (Universe.sup s1 s2) s3).
  Proof.
    unfold_eq_universe. rewrite !val_sup; lia.
  Qed.

  Lemma eq_universe_sup_idem φ s :
    eq_universe φ (Universe.sup s s) s.
  Proof.
    unfold_eq_universe. rewrite !val_sup; lia.
  Qed.

  Instance sup_eq_universe φ :
    Proper (eq_universe φ ==> eq_universe φ ==> eq_universe φ) Universe.sup.
  Proof.
    intros s1 s1' H1 s2 s2' H2.
    unfold_eq_universe. specialize (H1 v Hv). specialize (H2 v Hv).
    rewrite !val_sup; lia.
  Qed.

  Lemma sort_of_product_twice φ u s :
    eq_universe φ (Universe.sort_of_product u (Universe.sort_of_product u s))
                (Universe.sort_of_product u s).
  Proof.
    unfold Universe.sort_of_product. case_eq (Universe.is_prop s).
    intros ->. reflexivity.
    intro e. rewrite is_prop_sup e andb_false_r.
    rewrite eq_universe_sup_assoc.
    rewrite eq_universe_sup_idem.
    reflexivity.
  Qed.

End UniverseLemmas.