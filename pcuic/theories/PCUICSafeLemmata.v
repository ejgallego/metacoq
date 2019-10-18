(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.CRelationClasses ProofIrrelevance.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICCumulativity PCUICSR PCUICPosition PCUICEquality PCUICNameless
     PCUICAlpha PCUICNormal PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion PCUICValidity
     PCUICParallelReductionConfluence PCUICWeakeningEnv
     PCUICClosed PCUICPrincipality PCUICSubstitution
     PCUICWeakening PCUICGeneration PCUICUtils.

From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.
Derive Signature for red.
Import MonadNotation.

Local Set Keyed Unification.
Set Equations With UIP.
Derive Signature for typing_spine.

Set Default Goal Selector "!".



Definition nodelta_flags := RedFlags.mk true true true false true true.

(* TODO MOVE *)
Lemma All2_app_inv_both :
  forall A B (P : A -> B -> Type) l1 l2 r1 r2,
    #|l1| = #|r1| ->
    All2 P (l1 ++ l2) (r1 ++ r2) ->
    All2 P l1 r1 × All2 P l2 r2.
Proof.
  intros A B P l1 l2 r1 r2 e h.
  apply All2_app_inv in h as [[w1 w2] [[e1 h1] h2]].
  assert (e2 : r1 = w1 × r2 = w2).
  { apply All2_length in h1. rewrite h1 in e.
    clear - e e1.
    induction r1 in r2, w1, w2, e, e1 |- *.
    - destruct w1. 2: discriminate.
      intuition eauto.
    - destruct w1. 1: discriminate.
      simpl in e. apply Nat.succ_inj in e.
      simpl in e1. inversion e1. subst.
      eapply IHr1 in e. 2: eassumption.
      intuition eauto. f_equal. assumption.
  }
  destruct e2 as [? ?]. subst.
  intuition auto.
Qed.

Lemma strengthening `{cf : checker_flags} :
  forall {Σ Γ Γ' Γ'' t T},
    wf Σ.1 ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'
    |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T ->
    Σ;;; Γ ,,, Γ' |- t : T.
Admitted.

Section Lemmata.
  Context {cf : checker_flags}.
  Context (flags : RedFlags.t).

  Lemma eq_term_zipc_inv :
    forall φ u v π,
      eq_term φ (zipc u π) (zipc v π) ->
      eq_term φ u v.
  Proof.
    intros Σ u v π h.
    induction π in u, v, h |- *.
    all: try solve [
             simpl in h ; try apply IHπ in h ;
             cbn in h ; inversion h ; subst ; assumption
           ].
    - simpl in h. apply IHπ in h.
      inversion h. subst.
      match goal with
      | h : All2 _ _ _ |- _ => rename h into a
      end.
      apply All2_app_inv_both in a. 2: reflexivity.
      destruct a as [_ a]. inversion a. subst.
      intuition eauto.
    - simpl in h. apply IHπ in h.
      inversion h. subst.
      match goal with
      | h : All2 _ _ _ |- _ => rename h into a
      end.
      apply All2_app_inv_both in a. 2: reflexivity.
      destruct a as [_ a]. inversion a. subst.
      intuition eauto.
    - simpl in h. apply IHπ in h.
      inversion h. subst.
      match goal with
      | h : All2 _ _ _ |- _ => rename h into a
      end.
      apply All2_app_inv_both in a. 2: reflexivity.
      destruct a as [_ a]. inversion a. subst.
      intuition eauto.
  Qed.

  Lemma eq_term_zipx_inv :
    forall φ Γ u v π,
      eq_term φ (zipx Γ u π) (zipx Γ v π) ->
      eq_term φ u v.
  Proof.
    intros Σ Γ u v π h.
    eapply eq_term_zipc_inv.
    eapply eq_term_it_mkLambda_or_LetIn_inv.
    eassumption.
  Qed.

  Lemma eq_term_upto_univ_zipc :
    forall Re u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Re Re u v ->
      eq_term_upto_univ Re Re (zipc u π) (zipc v π).
  Proof.
    intros Re u v π he h.
    induction π in u, v, h |- *.
    all: try solve [
               simpl ; try apply IHπ ;
               cbn ; constructor ; try apply eq_term_upto_univ_refl ; assumption
             ].
    - assumption.
    - simpl. apply IHπ. constructor.
      apply All2_app.
      + apply All2_same.
        intros. split ; auto. split. all: apply eq_term_upto_univ_refl.
        all: assumption.
      + constructor.
        * simpl. intuition eauto. reflexivity.
        * apply All2_same.
          intros. split ; auto. split. all: apply eq_term_upto_univ_refl.
          all: assumption.
    - simpl. apply IHπ. constructor.
      apply All2_app.
      + apply All2_same.
        intros. split ; auto. split. all: apply eq_term_upto_univ_refl.
        all: assumption.
      + constructor.
        * simpl. intuition eauto. reflexivity.
        * apply All2_same.
          intros. split ; auto. split. all: apply eq_term_upto_univ_refl.
          all: assumption.
    - simpl. apply IHπ. destruct indn as [i n].
      constructor.
      + assumption.
      + apply eq_term_upto_univ_refl. all: assumption.
      + eapply All2_same.
        intros. split ; auto. apply eq_term_upto_univ_refl. all: assumption.
    - simpl. apply IHπ. destruct indn as [i n].
      constructor.
      + apply eq_term_upto_univ_refl. all: assumption.
      + assumption.
      + eapply All2_same.
        intros. split ; auto. apply eq_term_upto_univ_refl. all: assumption.
    - simpl. apply IHπ. destruct indn as [i n].
      constructor.
      + apply eq_term_upto_univ_refl. all: assumption.
      + apply eq_term_upto_univ_refl. all: assumption.
      + apply All2_app.
        * eapply All2_same.
          intros. split ; auto. apply eq_term_upto_univ_refl. all: assumption.
        * constructor.
          -- simpl. intuition eauto.
          -- eapply All2_same.
             intros. split ; auto. apply eq_term_upto_univ_refl.
             all: assumption.
  Qed.

  Lemma eq_term_zipc :
    forall (Σ : global_env_ext) u v π,
      eq_term (global_ext_constraints Σ) u v ->
      eq_term (global_ext_constraints Σ) (zipc u π) (zipc v π).
  Proof.
    intros Σ u v π h.
    eapply eq_term_upto_univ_zipc.
    - intro. eapply eq_universe_refl.
    - assumption.
  Qed.

  Lemma eq_term_upto_univ_zipp :
    forall Re u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Re Re u v ->
      eq_term_upto_univ Re Re (zipp u π) (zipp v π).
  Proof.
    intros Re u v π he h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    eapply eq_term_upto_univ_mkApps.
    - assumption.
    - apply All2_same. intro. reflexivity.
  Qed.

  Lemma eq_term_zipp :
    forall (Σ : global_env_ext) u v π,
      eq_term (global_ext_constraints Σ) u v ->
      eq_term (global_ext_constraints Σ) (zipp u π) (zipp v π).
  Proof.
    intros Σ u v π h.
    eapply eq_term_upto_univ_zipp.
    - intro. eapply eq_universe_refl.
    - assumption.
  Qed.

  Lemma eq_term_upto_univ_zipx :
    forall Re Γ u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Re Re u v ->
      eq_term_upto_univ Re Re (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Re Γ u v π he h.
    eapply eq_term_upto_univ_it_mkLambda_or_LetIn ; auto.
    eapply eq_term_upto_univ_zipc ; auto.
  Qed.

  Lemma eq_term_zipx :
    forall φ Γ u v π,
      eq_term φ u v ->
      eq_term φ (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Σ Γ u v π h.
    eapply eq_term_upto_univ_zipx ; auto.
    intro. eapply eq_universe_refl.
  Qed.


  (* red is the reflexive transitive closure of one-step reduction and thus
     can't be used as well order. We thus define the transitive closure,
     but we take the symmetric version.
   *)
  Inductive cored Σ Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  Derive Signature for cored.

  Hint Resolve eq_term_upto_univ_refl : core.

  Lemma fresh_global_nl :
    forall Σ k,
      fresh_global k Σ ->
      fresh_global k (map (on_snd nl_global_decl) Σ).
  Proof.
    intros Σ k h. eapply Forall_map.
    eapply Forall_impl ; try eassumption.
    intros x hh. cbn in hh.
    destruct x ; assumption.
  Qed.

  (* Lemma conv_context : *)
  (*   forall Σ Γ u v ρ, *)
  (*     wf Σ.1 -> *)
  (*     Σ ;;; Γ ,,, stack_context ρ |- u == v -> *)
  (*     Σ ;;; Γ |- zipc u ρ == zipc v ρ. *)
  (* Proof. *)
  (*   intros Σ Γ u v ρ hΣ h. *)
  (*   induction ρ in u, v, h |- *. *)
  (*   - assumption. *)
  (*   - simpl. eapply IHρ. eapply conv_App_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Case_c ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Proj_c ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Prod_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Prod_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Lambda_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Lambda_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (* Qed. *)

  Context (Σ : global_env_ext).

  Inductive welltyped Σ Γ t : Prop :=
  | iswelltyped A : Σ ;;; Γ |- t : A -> welltyped Σ Γ t.

  Arguments iswelltyped {Σ Γ t A} h.

  Definition wellformed Σ Γ t :=
    welltyped Σ Γ t \/ ∥ isWfArity typing Σ Γ t ∥.

  (* Here we use use the proof irrelevance axiom to show that wellformed is really squashed.
     Using SProp would avoid this.
   *)

  Lemma wellformed_irr :
    forall {Σ Γ t} (h1 h2 : wellformed Σ Γ t), h1 = h2.
  Proof. intros. apply proof_irrelevance. Qed.

  Context (hΣ : ∥ wf Σ ∥).

  Lemma welltyped_alpha Γ u v :
      welltyped Σ Γ u ->
      eq_term_upto_univ eq eq u v ->
      welltyped Σ Γ v.
  Proof.
    intros [A h] e.
    destruct hΣ.
    exists A. eapply typing_alpha ; eauto.
  Qed.

  Lemma wellformed_alpha Γ u v :
      wellformed Σ Γ u ->
      eq_term_upto_univ eq eq u v ->
      wellformed Σ Γ v.
  Proof.
    destruct hΣ as [hΣ'].
    intros [X|X] e; [left|right].
    - destruct X as [A Hu]. eexists. eapply typing_alpha; tea.
    - destruct X. constructor.
      now eapply isWfArity_alpha.
  Qed.

  Lemma wellformed_nlctx Γ u :
      wellformed Σ Γ u ->
      wellformed Σ (nlctx Γ) u.
  Proof.
    destruct hΣ as [hΣ'].
    assert (Γ ≡Γ nlctx Γ) by apply upto_names_nlctx.
    intros [[A hu]|[[ctx [s [X1 X2]]]]]; [left|right].
    - exists A. eapply context_conversion'. all: try eassumption.
      1:{ eapply wf_local_alpha with Γ. all: try eassumption.
          eapply typing_wf_local. eassumption.
      }
      eapply upto_names_conv_context. assumption.
    - constructor. exists ctx, s. split; tas.
      eapply wf_local_alpha; tea.
      now eapply eq_context_upto_cat.
  Qed.


  Lemma red_cored_or_eq :
    forall Γ u v,
      red Σ Γ u v ->
      cored Σ Γ v u \/ u = v.
  Proof.
    intros Γ u v h.
    induction h.
    - right. reflexivity.
    - destruct IHh.
      + left. eapply cored_trans ; eassumption.
      + subst. left. constructor. assumption.
  Qed.

  Lemma cored_it_mkLambda_or_LetIn :
    forall Γ Δ u v,
      cored Σ (Γ ,,, Δ) u v ->
      cored Σ Γ (it_mkLambda_or_LetIn Δ u)
               (it_mkLambda_or_LetIn Δ v).
  Proof.
    intros Γ Δ u v h.
    induction h.
    - constructor. apply red1_it_mkLambda_or_LetIn. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + apply red1_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma cored_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      cored (fst Σ) Γ v u ->
      welltyped Σ Γ v.
  Proof.
    destruct hΣ as [wΣ]; clear hΣ.
    intros Γ u v h r.
    revert h. induction r ; intros h.
    - destruct h as [A h]. exists A.
      eapply sr_red1 ; eauto with wf.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply sr_red1 ; eauto with wf.
  Qed.

  Lemma cored_trans' :
    forall {Γ u v w},
      cored Σ Γ u v ->
      cored Σ Γ v w ->
      cored Σ Γ u w.
  Proof.
    intros Γ u v w h1 h2. revert w h2.
    induction h1 ; intros z h2.
    - eapply cored_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  (* This suggests that this should be the actual definition.
     ->+ = ->*.->
   *)
  Lemma cored_red_trans :
    forall Γ u v w,
      red Σ Γ u v ->
      red1 Σ Γ v w ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert w h2. induction h1 ; intros w h2.
    - constructor. assumption.
    - eapply cored_trans.
      + eapply IHh1. eassumption.
      + assumption.
  Qed.

  Lemma cored_case :
    forall Γ ind p c c' brs,
      cored Σ Γ c c' ->
      cored Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof.
    intros Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Lemma welltyped_context :
    forall Γ t,
      welltyped Σ Γ (zip t) ->
      welltyped Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ [t π] h. simpl.
    destruct h as [T h].
    induction π in Γ, t, T, h |- *.
    - cbn. cbn in h. eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_Fix in h as hh. 2: assumption.
      destruct hh as [decl [? [? [hw [? ?]]]]].
      clear - hw wΣ.
      rewrite fix_context_fix_context_alt in hw.
      rewrite map_app in hw. simpl in hw.
      unfold def_sig at 2 in hw. simpl in hw.
      unfold fix_context_alt in hw.
      rewrite mapi_app in hw.
      rewrite rev_app_distr in hw.
      simpl in hw.
      rewrite !app_context_assoc in hw.
      apply wf_local_app in hw.
      match type of hw with
      | context [ List.rev ?l ] =>
        set (Δ := List.rev l) in *
      end.
      assert (e : #|Δ| = #|mfix1|).
      { subst Δ. rewrite List.rev_length.
        rewrite mapi_length. rewrite map_length.
        reflexivity.
      }
      rewrite map_length in hw. rewrite <- e in hw.
      clearbody Δ. clear e.
      replace (#|Δ| + 0) with #|Δ| in hw by lia.
      set (Γ' := Γ ,,, stack_context π) in *.
      clearbody Γ'. clear Γ. rename Γ' into Γ.
      rewrite <- app_context_assoc in hw.
      inversion hw. subst.
      match goal with
      | hh : lift_typing _ _ _ _ _ |- _ => rename hh into h
      end.
      simpl in h. destruct h as [s h].
      exists (tSort s).
      eapply @strengthening with (Γ' := []). 1: assumption.
      exact h.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_Fix in h as hh. 2: assumption.
      destruct hh as [decl [? [? [? [ha ?]]]]].
      clear - ha wΣ.
      apply All_app in ha as [_ ha].
      inversion ha. subst.
      intuition eauto. simpl in *.
      match goal with
      | hh : _ ;;; _ |- _ : _ |- _ => rename hh into h
      end.
      rewrite fix_context_length in h.
      rewrite app_length in h. simpl in h.
      rewrite fix_context_fix_context_alt in h.
      rewrite map_app in h. simpl in h.
      unfold def_sig at 2 in h. simpl in h.
      rewrite <- app_context_assoc in h.
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct indn.
      apply inversion_Case in h as hh ; auto.
      destruct hh as [uni [args [mdecl [idecl [ps [pty [btys
                                 [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct indn.
      apply inversion_Case in h as hh ; auto.
      destruct hh as [uni [args [mdecl [idecl [ps [pty [btys
                                 [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct indn.
      apply inversion_Case in h as hh ; auto.
      destruct hh as [uni [args [mdecl [idecl [ps [pty [btys
                                 [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]].
      apply All2_app_inv in a as [[? ?] [[? ?] ha]].
      inversion ha. subst.
      intuition eauto. simpl in *.
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Proj in h
        as [uni [mdecl [idecl [pdecl [args [? [? [? ?]]]]]]]] ; auto.
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Prod in h as hh ; auto.
      destruct hh as [s1 [s2 [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Prod in h as hh ; auto.
      destruct hh as [s1 [s2 [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Lambda in h as hh ; auto.
      destruct hh as [s1 [B [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Lambda in h as hh ; auto.
      destruct hh as [s1 [B [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [U h].
      apply inversion_LetIn in h as [s [A [? [? [? ?]]]]]. 2: auto.
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [U h].
      apply inversion_LetIn in h as [s [A [? [? [? ?]]]]]. 2: auto.
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [U h].
      apply inversion_LetIn in h as [s [A [? [? [? ?]]]]]. 2: auto.
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
  Qed.

  Lemma wellformed_context :
    forall Γ t,
      wellformed Σ Γ (zip t) ->
      wellformed Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ [t π] [[A h]|h].
    - destruct (welltyped_context Γ (t, π) (iswelltyped h)) as [? ?].
      left. econstructor. eassumption.
    - simpl. induction π in t, h |- *.
      all: try (specialize (IHπ _ h)).
      all: simpl in *.
      1: right ; assumption.
      all: destruct IHπ as [[A' h'] | [[Δ [s [h1 h2]]]]] ; [| try discriminate].
      all: try solve [
        apply inversion_App in h' ; auto ;
        rdestruct h' ;
        left ; econstructor ; eassumption
      ].
      + apply inversion_Fix in h'. 2: assumption.
        destruct h' as [decl [? [? [hw [? ?]]]]].
        clear - hw wΣ.
        rewrite fix_context_fix_context_alt in hw.
        rewrite map_app in hw. simpl in hw.
        unfold def_sig at 2 in hw. simpl in hw.
        unfold fix_context_alt in hw.
        rewrite mapi_app in hw.
        rewrite rev_app_distr in hw.
        simpl in hw.
        rewrite !app_context_assoc in hw.
        apply wf_local_app in hw.
        match type of hw with
        | context [ List.rev ?l ] =>
          set (Δ := List.rev l) in *
        end.
        assert (e : #|Δ| = #|mfix1|).
        { subst Δ. rewrite List.rev_length.
          rewrite mapi_length. rewrite map_length.
          reflexivity.
        }
        rewrite map_length in hw. rewrite <- e in hw.
        clearbody Δ. clear e.
        replace (#|Δ| + 0) with #|Δ| in hw by lia.
        set (Γ' := Γ ,,, stack_context π) in *.
        clearbody Γ'. clear Γ. rename Γ' into Γ.
        rewrite <- app_context_assoc in hw.
        inversion hw. subst.
        match goal with
        | hh : lift_typing _ _ _ _ _ |- _ => rename hh into h
        end.
        simpl in h. destruct h as [s h].
        left. exists (tSort s).
        eapply @strengthening with (Γ' := []). 1: assumption.
        exact h.
      + apply inversion_Fix in h'. 2: assumption.
        destruct h' as [decl [? [? [? [ha ?]]]]].
        clear - ha wΣ.
        apply All_app in ha as [_ ha].
        inversion ha. subst.
        intuition eauto. simpl in *.
        match goal with
        | hh : _ ;;; _ |- _ : _ |- _ => rename hh into h
        end.
        rewrite fix_context_length in h.
        rewrite app_length in h. simpl in h.
        rewrite fix_context_fix_context_alt in h.
        rewrite map_app in h. simpl in h.
        unfold def_sig at 2 in h. simpl in h.
        rewrite <- app_context_assoc in h.
        left. eexists. eassumption.
      + destruct indn.
        apply inversion_Case in h' ; auto. cbn in h'. rdestruct h'.
        left. econstructor. eassumption.
      + destruct indn.
        apply inversion_Case in h' ; auto. cbn in h'. rdestruct h'.
        left. econstructor. eassumption.
      + destruct indn.
        apply inversion_Case in h' ; auto. cbn in h'. rdestruct h'.
        match goal with
        | h : All2 _ _ _ |- _ => rename h into a
        end.
        apply All2_app_inv in a as [[? ?] [[? ?] ha]].
        inversion ha. subst. intuition eauto.
        simpl in *.
        left. econstructor. eassumption.
      + apply inversion_Proj in h' ; auto.
        cbn in h'. rdestruct h'.
        left. eexists. eassumption.
      + apply inversion_Prod in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. left. rewrite app_context_assoc in h2. cbn in *.
        apply wf_local_app in h2. inversion h2. subst. cbn in *.
        destruct X0. eexists. eassumption.
      + apply inversion_Prod in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. right. constructor. exists Δ', s.
        rewrite app_context_assoc in h2. cbn in h2.
        split ; eauto.
      + apply inversion_Lambda in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + apply inversion_Lambda in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + apply inversion_LetIn in h'. 2: auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. rewrite app_context_assoc in h2. simpl in h2.
        left. apply wf_local_app in h2.
        inversion h2. subst. cbn in *.
        eexists. eassumption.
      + apply inversion_LetIn in h'. 2: auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. rewrite app_context_assoc in h2. simpl in h2.
        left. apply wf_local_app in h2.
        inversion h2. subst. cbn in *.
        match goal with
        | h : ∃ s : universe, _ |- _ =>
          destruct h
        end.
        eexists. eassumption.
      + apply inversion_LetIn in h'. 2: auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. rewrite app_context_assoc in h2. simpl in h2.
        right. constructor. exists Δ', s.
        split. all: auto.
  Qed.

  Lemma cored_red :
    forall Γ u v,
      cored Σ Γ v u ->
      ∥ red Σ Γ u v ∥.
  Proof.
    intros Γ u v h.
    induction h.
    - constructor. econstructor.
      + constructor.
      + assumption.
    - destruct IHh as [r].
      constructor. econstructor ; eassumption.
  Qed.

  Lemma cored_context :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π h. induction h.
    - constructor. eapply red1_context. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  Lemma cored_zipx :
    forall Γ u v π,
      cored Σ (Γ ,,, stack_context π) u v ->
      cored Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply cored_it_mkLambda_or_LetIn.
    eapply cored_context.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma red_zipx :
    forall Γ u v π,
      red Σ (Γ ,,, stack_context π) u v ->
      red Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply red_it_mkLambda_or_LetIn.
    eapply red_context.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma cumul_zippx :
    forall Γ u v ρ,
      Σ ;;; (Γ ,,, stack_context ρ) |- u <= v ->
      Σ ;;; Γ |- zippx u ρ <= zippx v ρ.
  Proof.
    intros Γ u v ρ h.
    induction ρ in u, v, h |- *.
    all: try solve [
      unfold zippx ; simpl ;
      eapply cumul_it_mkLambda_or_LetIn ;
      assumption
    ].
    - cbn. assumption.
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      apply IHρ.
      eapply cumul_App_l. assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_LetIn_bo. assumption.
  Qed.

  Lemma conv_alt_it_mkLambda_or_LetIn :
    forall Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) |- u == v ->
      Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u == it_mkLambda_or_LetIn Γ v.
  Proof.
    intros Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply conv_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply conv_Lambda_r. assumption.
  Qed.

  Lemma conv_alt_it_mkProd_or_LetIn :
    forall Δ Γ B B',
      Σ ;;; (Δ ,,, Γ) |- B == B' ->
      Σ ;;; Δ |- it_mkProd_or_LetIn Γ B == it_mkProd_or_LetIn Γ B'.
  Proof.
    intros Δ Γ B B' h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply conv_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply conv_Prod_r. assumption.
  Qed.

  Lemma conv_zipp :
    forall Γ u v ρ,
      Σ ;;; Γ |- u == v ->
      Σ ;;; Γ |- zipp u ρ == zipp v ρ.
  Proof.
    intros Γ u v ρ h.
    unfold zipp.
    destruct decompose_stack.
    induction l in u, v, h |- *.
    - assumption.
    - simpl.  eapply IHl. eapply conv_App_l. assumption.
  Qed.

  Lemma cumul_zipp :
    forall Γ u v π,
      Σ ;;; Γ |- u <= v ->
      Σ ;;; Γ |- zipp u π <= zipp v π.
  Proof.
    intros Γ u v π h.
    unfold zipp.
    destruct decompose_stack as [l ρ].
    induction l in u, v, h |- *.
    - assumption.
    - simpl.  eapply IHl. eapply cumul_App_l. assumption.
  Qed.

  Lemma conv_zipp' :
    forall leq Γ u v π,
      conv leq Σ Γ u v ->
      conv leq Σ Γ (zipp u π) (zipp v π).
  Proof.
    intros leq Γ u v π h.
    destruct leq.
    - destruct h. constructor. eapply conv_zipp. assumption.
    - destruct h. constructor. eapply cumul_zipp. assumption.
  Qed.

  Lemma conv_alt_zippx :
    forall Γ u v ρ,
      Σ ;;; (Γ ,,, stack_context ρ) |- u == v ->
      Σ ;;; Γ |- zippx u ρ == zippx v ρ.
  Proof.
    intros Γ u v ρ h.
    revert u v h. induction ρ ; intros u v h.
    all: try solve [
      unfold zippx ; simpl ;
      eapply conv_alt_it_mkLambda_or_LetIn ;
      assumption
    ].
    - cbn. assumption.
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      apply IHρ.
      eapply conv_App_l. assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_LetIn_bo. assumption.
  Qed.

  Lemma conv_zippx :
    forall Γ u v ρ,
      Σ ;;; Γ ,,, stack_context ρ |- u == v ->
      Σ ;;; Γ |- zippx u ρ == zippx v ρ.
  Proof.
    intros Γ u v ρ uv. eapply conv_alt_zippx ; assumption.
  Qed.

  Lemma conv_zippx' :
    forall Γ leq u v ρ,
      conv leq Σ (Γ ,,, stack_context ρ) u v ->
      conv leq Σ Γ (zippx u ρ) (zippx v ρ).
  Proof.
    intros Γ leq u v ρ h.
    destruct leq.
    - cbn in *. destruct h as [h]. constructor.
      eapply conv_alt_zippx ; assumption.
    - cbn in *. destruct h. constructor.
      eapply cumul_zippx. assumption.
  Qed.


  Lemma cored_nl :
    forall Γ u v,
      cored Σ Γ u v ->
      cored Σ (nlctx Γ) (nl u) (nl v).
  Proof.
    intros Γ u v H. induction H.
    - constructor 1. admit.
    - econstructor 2; tea. admit.
  Admitted.

  Derive Signature for Acc.

  Lemma wf_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A),
      well_founded R ->
      well_founded (fun x y => R (f x) (f y)).
  Proof.
    intros A R B f h x.
    specialize (h (f x)).
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  Lemma Acc_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A) x,
      Acc R (f x) ->
      Acc (fun x y => R (f x) (f y)) x.
  Proof.
    intros A R B f x h.
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  (* TODO Put more general lemma in Inversion *)
  Lemma welltyped_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ Δ t h.
    induction Δ as [| [na [b|] A] Δ ih ] in Γ, t, h |- *.
    - assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      apply inversion_LetIn in h as hh ; auto.
      destruct hh as [s1 [A' [? [? [? ?]]]]].
      exists A'. assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      apply inversion_Lambda in h as hh ; auto.
      pose proof hh as [s1 [B [? [? ?]]]].
      exists B. assumption.
  Qed.

  Lemma it_mkLambda_or_LetIn_welltyped :
    forall Γ Δ t,
      welltyped Σ (Γ ,,, Δ) t ->
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t).
  Proof.
    intros Γ Δ t [T h].
    eexists. eapply PCUICGeneration.type_it_mkLambda_or_LetIn.
    eassumption.
  Qed.

  Lemma welltyped_it_mkLambda_or_LetIn_iff :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) <->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    intros. split.
    - apply welltyped_it_mkLambda_or_LetIn.
    - apply it_mkLambda_or_LetIn_welltyped.
  Qed.

  Lemma isWfArity_it_mkLambda_or_LetIn :
    forall Γ Δ T,
      isWfArity typing Σ Γ (it_mkLambda_or_LetIn Δ T) ->
      isWfArity typing Σ (Γ ,,, Δ) T.
  Proof.
    intro Γ; induction Δ in Γ |- *; intro T; [easy|].
    destruct a as [na [bd|] ty].
    - simpl. cbn. intro HH. apply IHΔ in HH.
      destruct HH as [Δ' [s [HH HH']]].
      cbn in HH; apply destArity_app_Some in HH.
      destruct HH as [Δ'' [HH1 HH2]].
      exists Δ'', s. split; tas.
      refine (eq_rect _ (fun Γ => wf_local Σ Γ) HH' _ _).
      rewrite HH2. rewrite app_context_assoc. reflexivity.
    - simpl. cbn. intro HH. apply IHΔ in HH.
      destruct HH as [Δ' [s [HH HH']]]. discriminate.
  Qed.

  Lemma wellformed_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      wellformed Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      wellformed Σ (Γ ,,, Δ) t.
  Proof.
    intros Γ Δ t [Hwf|Hwf];
      [left; now apply welltyped_it_mkLambda_or_LetIn |
       right; destruct Hwf; constructor].
    now apply isWfArity_it_mkLambda_or_LetIn.
  Qed.


  Lemma wellformed_zipp :
    forall Γ t ρ,
      wellformed Σ Γ (zipp t ρ) ->
      wellformed Σ Γ t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ t ρ h.
    unfold zipp in h.
    case_eq (decompose_stack ρ). intros l π e.
    rewrite e in h. clear - h wΣ.
    destruct h as [[A h]|[h]].
    - left.
      induction l in t, A, h |- *.
      + eexists. eassumption.
      + apply IHl in h.
        destruct h as [T h].
        apply inversion_App in h as hh ; auto.
        rdestruct hh. econstructor. eassumption.
    - right. constructor. destruct l.
      + assumption.
      + destruct h as [ctx [s [h1 _]]].
        rewrite destArity_tApp in h1. discriminate.
  Qed.

  (* WRONG *)
  Lemma it_mkLambda_or_LetIn_wellformed :
    forall Γ Δ t,
      wellformed Σ (Γ ,,, Δ) t ->
      wellformed Σ Γ (it_mkLambda_or_LetIn Δ t).
  Abort.

  (* Wrong for t = alg univ, π = ε, Γ = vass A *)
  Lemma zipx_wellformed :
    forall {Γ t π},
      wellformed Σ Γ (zipc t π) ->
      wellformed Σ [] (zipx Γ t π).
  (* Proof. *)
  (*   intros Γ t π h. *)
  (*   eapply it_mkLambda_or_LetIn_wellformed. *)
  (*   rewrite app_context_nil_l. *)
  (*   assumption. *)
  (* Qed. *)
  Abort.

  Lemma wellformed_zipx :
    forall {Γ t π},
      wellformed Σ [] (zipx Γ t π) ->
      wellformed Σ Γ (zipc t π).
  Proof.
    intros Γ t π h.
    apply wellformed_it_mkLambda_or_LetIn in h.
    rewrite app_context_nil_l in h.
    assumption.
  Qed.

  Lemma wellformed_zipc_stack_context Γ t π ρ args
    : decompose_stack π = (args, ρ)
      -> wellformed Σ Γ (zipc t π)
      -> wellformed Σ (Γ ,,, stack_context π) (zipc t (appstack args ε)).
  Proof.
    intros h h1.
    apply decompose_stack_eq in h. subst.
    rewrite stack_context_appstack.
    induction args in Γ, t, ρ, h1 |- *.
    - cbn in *.
      now apply (wellformed_context Γ (t, ρ)).
    - simpl. eauto.
  Qed.

  (* Wrong  *)
  Lemma wellformed_zipc_zippx :
    forall Γ t π,
      wellformed Σ Γ (zipc t π) ->
      wellformed Σ Γ (zippx t π).
  (* Proof. *)
  (*   intros Γ t π h. *)
  (*   unfold zippx. *)
  (*   case_eq (decompose_stack π). intros l ρ e. *)
  (*   pose proof (decompose_stack_eq _ _ _ e). subst. clear e. *)
  (*   rewrite zipc_appstack in h. *)
  (*   zip fold in h. *)
  (*   apply wellformed_context in h ; simpl in h. *)
  (*   eapply it_mkLambda_or_LetIn_wellformed. *)
  (*   assumption. *)
  (* Qed. *)
  Abort.

  Lemma red_const :
    forall {Γ c u cty cb cu},
      Some (ConstantDecl {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      red (fst Σ) Γ (tConst c u) (subst_instance_constr u cb).
  Proof.
    intros Γ c u cty cb cu e.
    econstructor.
    - econstructor.
    - econstructor.
      + symmetry in e.  exact e.
      + reflexivity.
  Qed.

  Lemma cored_const :
    forall {Γ c u cty cb cu},
      Some (ConstantDecl {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      cored (fst Σ) Γ (subst_instance_constr u cb) (tConst c u).
  Proof.
    intros Γ c u cty cb cu e.
    symmetry in e.
    econstructor.
    econstructor.
    - exact e.
    - reflexivity.
  Qed.

  Derive Signature for cumul.
  Derive Signature for red1.

  Lemma app_cored_r :
    forall Γ u v1 v2,
      cored Σ Γ v1 v2 ->
      cored Σ Γ (tApp u v1) (tApp u v2).
  Proof.
    intros Γ u v1 v2 h.
    induction h.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + constructor. assumption.
  Qed.

  Fixpoint isAppProd (t : term) : bool :=
    match t with
    | tApp t l => isAppProd t
    | tProd na A B => true
    | _ => false
    end.

  Fixpoint isProd t :=
    match t with
    | tProd na A B => true
    | _ => false
    end.

  Lemma isAppProd_mkApps :
    forall t l, isAppProd (mkApps t l) = isAppProd t.
  Proof.
    intros t l. revert t.
    induction l ; intros t.
    - reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Lemma isProdmkApps :
    forall t l,
      isProd (mkApps t l) ->
      l = [].
  Proof.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. discriminate h.
  Qed.

  Lemma isSortmkApps :
    forall t l,
      isSort (mkApps t l) ->
      l = [].
  Proof.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. exfalso. assumption.
  Qed.

  Lemma isAppProd_isProd :
    forall Γ t,
      isAppProd t ->
      welltyped Σ Γ t ->
      isProd t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ t hp hw.
    induction t in Γ, hp, hw |- *.
    all: try discriminate hp.
    - reflexivity.
    - simpl in hp.
      specialize IHt1 with (1 := hp).
      assert (welltyped Σ Γ t1) as h.
      { destruct hw as [T h].
        apply inversion_App in h as hh ; auto.
        destruct hh as [na [A' [B' [? [? ?]]]]].
        eexists. eassumption.
      }
      specialize IHt1 with (1 := h).
      destruct t1.
      all: try discriminate IHt1.
      destruct hw as [T hw'].
      apply inversion_App in hw' as ihw' ; auto.
      destruct ihw' as [na' [A' [B' [hP [? ?]]]]].
      apply inversion_Prod in hP as [s1 [s2 [? [? bot]]]] ; auto.
      apply PCUICPrincipality.invert_cumul_prod_r in bot ; auto.
      destruct bot as [? [? [? [[r ?] ?]]]].
      exfalso. clear - r wΣ.
      revert r. generalize (Universe.sort_of_product s1 s2). intro s. clear.
      intro r.
      dependent induction r.
      assert (h : P = tSort s).
      { clear - r. induction r ; auto. subst.
        dependent destruction r0.
        assert (h : isSort (mkApps (tFix mfix idx) args)).
        { rewrite <- H. constructor. }
        apply isSortmkApps in h. subst. cbn in H.
        discriminate.
      }
      subst.
      dependent destruction r0.
      assert (h : isSort (mkApps (tFix mfix idx) args)).
      { rewrite <- H. constructor. }
      apply isSortmkApps in h. subst. cbn in H.
      discriminate.
  Qed.

  Lemma mkApps_Prod_nil :
    forall Γ na A B l,
      welltyped Σ Γ (mkApps (tProd na A B) l) ->
      l = [].
  Proof.
    intros Γ na A B l h.
    pose proof (isAppProd_isProd) as hh.
    specialize hh with (2 := h).
    rewrite isAppProd_mkApps in hh.
    specialize hh with (1 := eq_refl).
    apply isProdmkApps in hh. assumption.
  Qed.

  Lemma mkApps_Prod_nil' :
    forall Γ na A B l,
      wellformed Σ Γ (mkApps (tProd na A B) l) ->
      l = [].
  Proof.
    intros Γ na A B l [h | [[ctx [s [hd hw]]]]].
    - eapply mkApps_Prod_nil. eassumption.
    - destruct l ; auto.
      cbn in hd. rewrite destArity_tApp in hd. discriminate.
  Qed.

  (* TODO MOVE or even replace old lemma *)
  Lemma decompose_stack_noStackApp :
    forall π l ρ,
      decompose_stack π = (l,ρ) ->
      isStackApp ρ = false.
  Proof.
    intros π l ρ e.
    destruct ρ. all: auto.
    exfalso. eapply decompose_stack_not_app. eassumption.
  Qed.

  (* TODO MOVE *)
  Lemma stack_context_decompose :
    forall π,
      stack_context (snd (decompose_stack π)) = stack_context π.
  Proof.
    intros π.
    case_eq (decompose_stack π). intros l ρ e.
    cbn. pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite stack_context_appstack. reflexivity.
  Qed.

  Lemma it_mkLambda_or_LetIn_inj :
    forall Γ u v,
      it_mkLambda_or_LetIn Γ u =
      it_mkLambda_or_LetIn Γ v ->
      u = v.
  Proof.
    intros Γ u v e.
    revert u v e.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros u v e.
    - assumption.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
  Qed.

  Lemma nleq_term_zipc :
    forall u v π,
      nleq_term u v ->
      nleq_term (zipc u π) (zipc v π).
  Proof.
    intros u v π h.
    eapply ssrbool.introT.
    - eapply reflect_nleq_term.
    - cbn. rewrite 2!nl_zipc. f_equal.
      eapply ssrbool.elimT.
      + eapply reflect_nleq_term.
      + assumption.
  Qed.

  Lemma nleq_term_zipx :
    forall Γ u v π,
      nleq_term u v ->
      nleq_term (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    unfold zipx.
    eapply nleq_term_it_mkLambda_or_LetIn.
    eapply nleq_term_zipc.
    assumption.
  Qed.

  Hint Resolve conv_alt_refl conv_alt_red : core.
  Hint Resolve conv_ctx_refl: core.


  (* Let bindings are not injective, so it_mkLambda_or_LetIn is not either.
     However, when they are all lambdas they become injective for conversion.
     stack_contexts only produce lambdas so we can use this property on them.
     It only applies to stacks manipulated by conversion/reduction which are
     indeed let-free.
   *)
  Fixpoint let_free_context (Γ : context) :=
    match Γ with
    | [] => true
    | {| decl_name := na ; decl_body := Some b ; decl_type := B |} :: Γ => false
    | {| decl_name := na ; decl_body := None ; decl_type := B |} :: Γ =>
      let_free_context Γ
    end.

  Lemma let_free_context_app :
    forall Γ Δ,
      let_free_context (Γ ,,, Δ) = let_free_context Δ && let_free_context Γ.
  Proof.
    intros Γ Δ.
    induction Δ as [| [na [b|] B] Δ ih ] in Γ |- *.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. apply ih.
  Qed.

  Lemma let_free_context_rev :
    forall Γ,
      let_free_context (List.rev Γ) = let_free_context Γ.
  Proof.
    intros Γ.
    induction Γ as [| [na [b|] B] Γ ih ].
    - reflexivity.
    - simpl. rewrite let_free_context_app. simpl.
      apply andb_false_r.
    - simpl. rewrite let_free_context_app. simpl.
      rewrite ih. rewrite andb_true_r. reflexivity.
  Qed.

  Fixpoint let_free_stack (π : stack) :=
    match π with
    | ε => true
    | App u ρ => let_free_stack ρ
    | Fix f n args ρ => let_free_stack ρ
    | Fix_mfix_ty na bo ra mfix1 mfix2 idx ρ => let_free_stack ρ
    | Fix_mfix_bd na ty ra mfix1 mfix2 idx ρ => let_free_stack ρ
    | CoFix f n args ρ => let_free_stack ρ
    | Case_p indn c brs ρ => let_free_stack ρ
    | Case indn p brs ρ => let_free_stack ρ
    | Case_brs indn p c m brs1 brs2 ρ => let_free_stack ρ
    | Proj p ρ => let_free_stack ρ
    | Prod_l na B ρ => let_free_stack ρ
    | Prod_r na A ρ => let_free_stack ρ
    | Lambda_ty na u ρ => let_free_stack ρ
    | Lambda_tm na A ρ => let_free_stack ρ
    | LetIn_bd na B u ρ => let_free_stack ρ
    | LetIn_ty na b u ρ => let_free_stack ρ
    | LetIn_in na b B ρ => false
    | coApp u ρ => let_free_stack ρ
    end.

  Lemma let_free_stack_context :
    forall π,
      let_free_stack π ->
      let_free_context (stack_context π).
  Proof.
    intros π h.
    induction π.
    all: try solve [ simpl ; rewrite ?IHπ by auto ; reflexivity ].
    2: discriminate.
    simpl. rewrite let_free_context_app.
    rewrite IHπ by auto. rewrite andb_true_r. rewrite let_free_context_rev.
    match goal with
    | |- context [ mapi ?f ?l ] =>
      generalize l
    end.
    intro l. unfold mapi.
    generalize 0 at 2. intro n.
    induction l in n |- *.
    - simpl. reflexivity.
    - simpl. apply IHl.
  Qed.

  Lemma cored_red_cored :
    forall Γ u v w,
      cored Σ Γ w v ->
      red Σ Γ u v ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 ; intros t h2.
    - eapply cored_red_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Lemma red_neq_cored :
    forall Γ u v,
      red Σ Γ u v ->
      u <> v ->
      cored Σ Γ v u.
  Proof.
    intros Γ u v r n.
    destruct r.
    - exfalso. apply n. reflexivity.
    - eapply cored_red_cored ; try eassumption.
      constructor. assumption.
  Qed.

  Lemma red_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      ∥ red (fst Σ) Γ u v ∥ ->
      welltyped Σ Γ v.
  Proof.
    destruct hΣ as [wΣ]; clear hΣ.
    intros Γ u v h [r].
    revert h. induction r ; intros h.
    - assumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply sr_red1 ; eauto with wf.
  Qed.

  Lemma red_cored_cored :
    forall Γ u v w,
      red Σ Γ v w ->
      cored Σ Γ v u ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 ; intros t h2.
    - assumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  (* TODO MOVE It needs wf Σ entirely *)
  Lemma subject_conversion :
    forall Γ u v A B,
      Σ ;;; Γ |- u : A ->
      Σ ;;; Γ |- v : B ->
      Σ ;;; Γ |- u == v ->
      ∑ C,
        Σ ;;; Γ |- u : C ×
        Σ ;;; Γ |- v : C.
  Proof.
    intros Γ u v A B hu hv h.
    (* apply conv_conv_alt in h. *)
    (* apply conv_alt_red in h as [u' [v' [? [? ?]]]]. *)
    (* pose proof (subject_reduction _ Γ _ _ _ hΣ hu r) as hu'. *)
    (* pose proof (subject_reduction _ Γ _ _ _ hΣ hv r0) as hv'. *)
    (* pose proof (typing_alpha _ _ _ _ hu' e) as hv''. *)
    (* pose proof (principal_typing _ hv' hv'') as [C [? [? hvC]]]. *)
    (* apply eq_term_sym in e as e'. *)
    (* pose proof (typing_alpha _ _ _ _ hvC e') as huC. *)
    (* Not clear.*)
  Abort.

  Lemma welltyped_zipc_replace :
    forall Γ u v π,
      welltyped Σ Γ (zipc v π) ->
      welltyped Σ (Γ ,,, stack_context π) u ->
      Σ ;;; Γ ,,, stack_context π |- u == v ->
      welltyped Σ Γ (zipc u π).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ u v π hv hu heq.
    induction π in u, v, hu, hv, heq |- *.
    - simpl in *. assumption.
    - simpl in *. eapply IHπ.
      + eassumption.
      + zip fold in hv. apply welltyped_context in hv.
        simpl in hv.
        destruct hv as [Tv hv].
        destruct hu as [Tu hu].
        apply inversion_App in hv as ihv ; auto.
        destruct ihv as [na [A' [B' [hv' [ht ?]]]]].
        (* Seems to be derivable (tediously) from some principal type lemma. *)
        admit.
      + (* Congruence *)
        admit.
  Admitted.

  Lemma wellformed_zipc_replace :
    forall Γ u v π,
      wellformed Σ Γ (zipc v π) ->
      wellformed Σ (Γ ,,, stack_context π) u ->
      Σ ;;; Γ ,,, stack_context π |- u == v ->
      wellformed Σ Γ (zipc u π).
  Admitted.

  Derive Signature for typing.

  (* Follows from principality, inversion of cumul/confluence *)
  Lemma Construct_Ind_ind_eq :
    forall {Γ n i args u i' args' u'},
      Σ ;;; Γ |- mkApps (tConstruct i n u) args : mkApps (tInd i' u') args' ->
      i = i'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ n i args u i' args' u' h.
    eapply inversion_mkApps in h ; auto.
    destruct h as [T [U [hC [hs hc]]]].
    apply inversion_Construct in hC
      as [mdecl [idecl [cdecl [hΓ [isdecl [const htc]]]]]]. 2: assumption.
    unfold type_of_constructor in htc. simpl in htc.
    destruct i as [mind nind]. simpl in *.
    destruct cdecl as [[cna ct] cn]. cbn in htc.
    destruct mdecl as [mnpars mpars mbod muni]. simpl in *.
    destruct idecl as [ina ity ike ict iprj]. simpl in *.
    unfold declared_constructor in isdecl. cbn in isdecl.
    destruct isdecl as [[dm hin] hn]. simpl in *.
    unfold declared_minductive in dm.
    (* Do we need to exploit wellformedness of the context?? *)
    (* We should also use invert_cumul_ind_l at some point. *)
  Admitted.

  Lemma Proj_red_cond :
    forall Γ i pars narg i' c u l,
      wellformed Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
      nth_error l (pars + narg) <> None.
  Proof.
    intros Γ i pars narg i' c u l [[T h]|[[ctx [s [e _]]]]];
      [|discriminate].
    destruct hΣ as [wΣ].
    apply inversion_Proj in h. 2: assumption.
    destruct h as [uni [mdecl [idecl [pdecl [args' [d [hc [? ?]]]]]]]].
    eapply on_declared_projection in d. 2: assumption.
    destruct d as [? [? ?]].
    simpl in *.
    destruct p.
    destruct o0.
  Admitted.

  Lemma Case_Construct_ind_eq :
    forall {Γ ind ind' npar pred i u brs args},
      wellformed Σ Γ (tCase (ind, npar) pred (mkApps (tConstruct ind' i u) args) brs) ->
      ind = ind'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ ind ind' npar pred i u brs args [[A h]|[[ctx [s [e _]]]]];
      [|discriminate].
    apply inversion_Case in h as ih ; auto.
    destruct ih as [uni [args' [mdecl [idecl [ps [pty [btys
                                 [? [? [? [? [? [X [ht0 [? ?]]]]]]]]]]]]]]].
    apply Construct_Ind_ind_eq in X. eauto.
  Qed.

  Lemma Proj_Constuct_ind_eq :
    forall Γ i i' pars narg c u l,
      wellformed Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
      i = i'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ i i' pars narg c u l [[T h]|[[ctx [s [e _]]]]];
      [|discriminate].
    apply inversion_Proj in h ; auto.
    destruct h as [uni [mdecl [idecl [pdecl [args' [? [hc [? ?]]]]]]]].
    apply Construct_Ind_ind_eq in hc. eauto.
  Qed.

  Lemma cored_zipc :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zipc t π) (zipc u π).
  Proof.
    intros Γ t u π h.
    do 2 zip fold. eapply cored_context. assumption.
  Qed.

  Lemma red_zipc :
    forall Γ t u π,
      red Σ (Γ ,,, stack_context π) t u ->
      red Σ Γ (zipc t π) (zipc u π).
  Proof.
    intros Γ t u π h.
    do 2 zip fold. eapply red_context. assumption.
  Qed.

  Lemma wellformed_zipc_zipp :
    forall Γ t π,
      wellformed Σ Γ (zipc t π) ->
      wellformed Σ (Γ ,,, stack_context π) (zipp t π).
  Proof.
    intros Γ t π h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst. clear e.
    rewrite zipc_appstack in h.
    zip fold in h.
    apply wellformed_context in h. simpl in h.
    rewrite stack_context_appstack.
    assumption.
  Qed.

  Lemma conv_context_convp :
    forall Γ Γ' leq u v,
      conv leq Σ Γ u v ->
      conv_context Σ Γ Γ' ->
      conv leq Σ Γ' u v.
  Proof.
    intros Γ Γ' leq u v h hx.
    destruct hΣ.
    destruct leq.
    - simpl. destruct h. constructor.
      eapply conv_alt_conv_ctx. all: eauto.
    - simpl in *. destruct h. constructor.
      eapply cumul_conv_ctx. all: eauto.
  Qed.

End Lemmata.

From MetaCoq.Checker Require Import uGraph.

(* todo: move *)
Lemma map_option_out_mapi :
  forall {A B} (l : list A) (l' : list B) f P,
    map_option_out (mapi f l) = Some l' ->
    Alli (fun i x => on_Some_or_None P (f i x)) 0 l ->
    All P l'.
Proof.
  intros A B l l' f P.
  unfold mapi. generalize 0.
  induction l in l' |- *; simpl; intro n.
  - inversion 1; constructor.
  - case_eq (f n a); [|discriminate].
    intros b Hb.
    case_eq (map_option_out (mapi_rec f l (S n))); [|discriminate].
    intros l0 Hl0 HH0 HH1.
    inversion HH0; subst; clear HH0.
    inversion HH1; subst.
    constructor.
    + now rewrite Hb in H0.
    + now eapply IHl.
Qed.

(* todo: move *)
Lemma Alli_id :
  forall {A} {P : nat -> A -> Type} (l : list A) (n : nat),
    (forall n x, P n x) -> Alli P n l.
Proof.
  intros A P l n h.
  induction l in n |- * ; constructor ; eauto.
Qed.

Definition on_some_or_none {A} (P : A -> Type) (o : option A) :=
  match o with
  | Some t => P t
  | None => True
  end.

(* todo: move *)
Lemma map_option_out_All {A} P (l : list (option A)) l' :
  (All (on_some_or_none P) l) ->
  map_option_out l = Some l' ->
  All P l'.
Proof.
  induction 1 in l' |- *; cbn; inversion 1; subst; try constructor.
  destruct x; [|discriminate].
  case_eq (map_option_out l); [|intro e; rewrite e in H1; discriminate].
  intros l0 e; rewrite e in H1; inversion H1; subst.
  constructor; auto.
Qed.

(* todo: move *)
Lemma All_mapi {A B} P f l k :
  Alli (fun i x => P (f i x)) k l -> All P (@mapi_rec A B f l k).
Proof.
  induction 1; simpl; constructor; tas.
Qed.

(* todo: move *)
Lemma All_Alli {A} {P : A -> Type} {Q : nat -> A -> Type} {l n} :
  All P l ->
  (forall n x, P x -> Q n x) ->
  Alli Q n l.
Proof.
  intro H. revert n. induction H; constructor; eauto.
Qed.

Lemma All2_All_left_pack {A B} {P : A -> B -> Type} {l l'} :
  All2 P l l' -> All (fun x => ∑ y, P x y) l.
Proof.
  intros HF. induction HF; constructor; eauto.
Qed.
Require Import ssreflect.

Lemma type_mkProd_or_LetIn {cf:checker_flags} Σ Γ d u t s : 
  wf Σ.1 ->
  Σ ;;; Γ |- decl_type d : tSort u ->
  match decl_body d return Type with 
  | Some b => 
   Σ ;;; Γ ,, d |- t : tSort s ->
   Σ ;;; Γ |- mkProd_or_LetIn d t : tSort s
  | None =>
    Σ ;;; Γ ,, d |- t : tSort s ->
    Σ ;;; Γ |- mkProd_or_LetIn d t : tSort (Universe.sort_of_product u s)
  end.
Proof.
  intros wfΣ. destruct d as [na [b|] dty] => [Hd Ht|Hd Ht]; rewrite /mkProd_or_LetIn /=.
  - have wf := typing_wf_local Ht.
    depelim wf; simpl in H; noconf H. clear l.
    eapply type_Cumul. econstructor; eauto.
    left. red. exists [], s; intuition auto.
    transitivity (tSort s).
    eapply red_cumul. eapply red1_red. constructor. reflexivity.
  - have wf := typing_wf_local Ht.
    depelim wf; simpl in H; noconf H.
    clear l.
    eapply type_Cumul. eapply type_Prod; eauto.
    left. red. exists [], (Universe.sort_of_product u s); intuition auto.
    reflexivity.
Qed.

Inductive decl_typing {cf : checker_flags} Σ Γ : context -> list universe -> Type :=
| decl_typing_empty : decl_typing Σ Γ [] []
| decl_typing_cons Γ' us d u : decl_typing Σ Γ Γ' us -> 
  Σ ;;; (Γ ,,, Γ') |- decl_type d : tSort u ->
  decl_typing Σ Γ (d :: Γ') (u :: us).

Definition max_list (u : list universe) v : universe :=
  List.fold_left (fun u v => Universe.sort_of_product v u) u v.

Lemma type_it_mkProd_or_LetIn {cf:checker_flags} Σ Γ Γ' u t s : 
  wf Σ.1 ->
  type_local_ctx (lift_typing typing) Σ Γ Γ' u ->
  Σ ;;; Γ ,,, Γ' |- t : tSort s ->
  Σ ;;; Γ |- it_mkProd_or_LetIn Γ' t : tSort (Universe.sort_of_product u s).
Proof.
  revert Γ u s t.
  induction Γ'; simpl; auto; move=> Γ u s t wfΣ equ Ht.
  - eapply type_Cumul; eauto.
    left. eexists [], _; intuition eauto.
    eapply typing_wf_local; eauto.
    constructor. constructor.
    eapply leq_universe_product.
  - specialize (IHΓ' Γ  u (Universe.sort_of_product u s)); auto.
    unfold app_context in Ht.
    eapply type_Cumul.
    eapply IHΓ'; auto.
    destruct a as [na [b|] ty]; intuition auto.
    destruct a as [na [b|] ty]; intuition auto.
    eapply (type_mkProd_or_LetIn _ _ {| decl_body := Some b |}); auto. simpl.
    (* We must sure in wf that types of let-ins are not algebraic!*)
    todo "wf let"%string.
    cbn. eapply type_Cumul; eauto.
    left. eexists [], _; intuition eauto using typing_wf_local.
    constructor. constructor. eapply leq_universe_product.
    eapply (type_mkProd_or_LetIn _ _ {| decl_body := None |}) => /=; eauto.
    left. eexists [], _; intuition eauto using typing_wf_local.
    eapply typing_wf_local in Ht.
    depelim Ht; eapply All_local_env_app in Ht; intuition auto.
    constructor. constructor.
    (* Universe property: @Simon *)
    admit.
Admitted.

Lemma weakening_gen : forall (cf : checker_flags) (Σ : global_env × universes_decl)
  (Γ Γ' : context) (t T : term) n, n = #|Γ'| ->
wf Σ.1 ->
wf_local Σ (Γ ,,, Γ') ->
Σ;;; Γ |- t : T -> Σ;;; Γ ,,, Γ' |- (lift0 n) t : (lift0 n) T.
Proof.
  intros ; subst n; now apply weakening.
Qed.

Lemma reln_length Γ Γ' n : #|reln Γ n Γ'| = #|Γ| + context_assumptions Γ'.
Proof.
  induction Γ' in n, Γ |- *; simpl; auto.
  destruct a as [? [b|] ?]; simpl; auto.
  rewrite Nat.add_1_r. simpl. rewrite IHΓ' => /= //.
Qed.

Lemma to_extended_list_k_length Γ n : #|to_extended_list_k Γ n| = context_assumptions Γ.
Proof.
  now rewrite /to_extended_list_k reln_length.
Qed.

Local Open Scope string_scope.

Definition same_shape (d d' : context_decl) := 
  match decl_body d, decl_body d' with
  | None, None => True
  | Some _, Some _ => True
  | _, _ => False
  end.
  
Definition same_ctx_shape (Γ Γ' : context) :=
  context_relation (fun _ _ => same_shape) Γ Γ'.
  
Hint Unfold same_ctx_shape : core.

Lemma same_ctx_shape_app Γ Γ' Δ Δ' : same_ctx_shape Γ Γ' -> 
  same_ctx_shape Δ Δ' ->
  same_ctx_shape (Γ ++ Δ)%list (Γ' ++ Δ')%list.
Proof.
  induction 1; simpl; try constructor; auto. 
  apply IHcontext_relation. auto.
  apply IHcontext_relation. auto.
Qed.

Lemma same_ctx_shape_rev Γ Γ' : same_ctx_shape Γ Γ' -> 
  same_ctx_shape (List.rev Γ) (List.rev Γ').
Proof.
  induction 1; simpl; try constructor.
  apply same_ctx_shape_app; auto. repeat constructor.
  apply same_ctx_shape_app; auto. repeat constructor.
Qed.

Lemma context_assumptions_app Γ Γ' : context_assumptions (Γ ++ Γ')%list = 
  context_assumptions Γ + context_assumptions Γ'.
Proof.
  induction Γ; simpl; auto.
  destruct a as [? [?|] ?]; simpl; auto.
Qed.

Lemma instantiate_params_ok ctx ctx' pars t : 
  same_ctx_shape ctx ctx' -> #|pars| = context_assumptions ctx ->
  ∑ h, instantiate_params ctx pars (it_mkProd_or_LetIn ctx' t) = Some h.
Proof.
  intros Hctx Hpars. rewrite instantiate_params_.
  apply same_ctx_shape_rev in Hctx.
  rewrite -(List.rev_involutive ctx').
  rewrite -(List.rev_involutive ctx) in Hpars.
  generalize (@nil term).
  induction Hctx in t, pars, Hpars |- *.
  - simpl. destruct pars; try discriminate. simpl in Hpars. intros l.
    now eexists (subst0 l _).
  - destruct pars; try discriminate.
    simpl in Hpars. rewrite context_assumptions_app in Hpars.
    simpl in Hpars. elimtype False. omega.
    simpl in Hpars. rewrite context_assumptions_app in Hpars.
    rewrite Nat.add_1_r in Hpars. noconf Hpars.
    simpl in H.
    intros l.
    destruct (IHHctx _ t H (t0 :: l)).
    simpl. exists x.
    now rewrite it_mkProd_or_LetIn_app.
  - intros l.
    simpl in Hpars. rewrite context_assumptions_app in Hpars.
    simpl in Hpars. rewrite Nat.add_0_r in Hpars. simpl.
    rewrite it_mkProd_or_LetIn_app.
    simpl. apply IHHctx. auto.
Qed.

Lemma isArity_it_mkProd_or_LetIn Γ t : isArity t -> isArity (it_mkProd_or_LetIn Γ t).
Proof.
  intros isA. induction Γ using rev_ind; simpl; auto.
  rewrite it_mkProd_or_LetIn_app. simpl; auto.
  destruct x as [? [?|] ?]; simpl; auto.
Qed.

Lemma smash_context_app Δ Γ Γ' : smash_context Δ (Γ ++ Γ')%list = smash_context (smash_context Δ Γ) Γ'.
Proof.
  revert Δ; induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
Qed.

Lemma smash_context_subst Δ s n Γ : smash_context (subst_context s (n + #|Γ|) Δ) (subst_context s n Γ) =
  subst_context s n (smash_context Δ Γ).
Proof.
  revert Δ. induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
  - now rewrite Nat.add_0_r.
  - rewrite -IHΓ.
    rewrite subst_context_snoc /=. f_equal.
    rewrite !subst_context_alt !mapi_compose.
    apply mapi_ext=> n' x.
    destruct x as [na' [b'|] ty']; simpl.
    * rewrite !mapi_length /subst_decl /= /map_decl /=; f_equal.
      f_equal. rewrite Nat.add_0_r distr_subst_rec. simpl. 
      f_equal; try lia. do 2 f_equal; lia. f_equal; lia.
      rewrite Nat.add_0_r distr_subst_rec; simpl.
      f_equal; try lia. do 2 f_equal; lia. f_equal; lia.
    * rewrite !mapi_length /subst_decl /= /map_decl /=; f_equal.
      rewrite Nat.add_0_r distr_subst_rec /=.
      f_equal. f_equal; f_equal; lia. f_equal; lia. 
  - rewrite -IHΓ.
    rewrite subst_context_snoc /= // /subst_decl /map_decl /=.
    f_equal.
    rewrite subst_context_app. simpl.
    rewrite /app_context. f_equal.
    f_equal; lia.
    rewrite /subst_context // /fold_context /= /map_decl /=.
    f_equal. f_equal. f_equal; lia.
Qed.

Lemma smash_context_subst_empty s n Γ : 
  smash_context [] (subst_context s n Γ) =
  subst_context s n (smash_context [] Γ).
Proof. apply: (smash_context_subst []). Qed.

Lemma invert_cumul_arity_l {cf:checker_flags} Σ (Γ : context) (C : term) T :
  wf Σ.1 ->
  Σ;;; Γ |- C <= T ->
  match destArity [] C with
  | Some (ctx, s) =>
    ∑ T' ctx' s', red Σ.1 Γ T T' * (destArity [] T' = Some (ctx', s')) * 
       conv_context Σ (Γ ,,, smash_context [] ctx) (Γ ,,, ctx') * leq_universe
       (global_ext_constraints Σ) s s'
  | None => unit
  end.
Proof.
intros wfΣ CT.
generalize (destArity_spec [] C). destruct destArity as [[ctx p]|].
simpl. intros ->. 2:intros _; exact tt.
revert Γ T CT.
generalize (@le_n #|ctx|).
generalize (#|ctx|) at 2. intros n; revert ctx.
induction n; intros ctx Hlen Γ T HT.
- destruct ctx; simpl in Hlen; try omega.
  eapply invert_cumul_sort_l in HT as [u' [redT leqT]].
  exists (tSort u'), [], u'; intuition auto.
  reflexivity.
- destruct ctx using rev_ind.
  * eapply invert_cumul_sort_l in HT as [u' [redT leqT]].
    exists (tSort u'), [], u'; intuition auto.  
    reflexivity.
  * rewrite it_mkProd_or_LetIn_app in HT; simpl in HT.
    destruct x as [na [b|] ty]; unfold mkProd_or_LetIn in HT; simpl in *.
    + eapply invert_cumul_letin_l in HT; auto.
      unfold subst1 in HT; rewrite subst_it_mkProd_or_LetIn in HT.
      rewrite app_length /= Nat.add_1_r in Hlen.
      simpl in HT. specialize (IHn (subst_context [b] 0 ctx) ltac:(rewrite
      subst_context_length; lia) Γ T HT).
      destruct IHn as [T' [ctx' [s' [[[redT destT] convctx] leq]]]].
      clear IHctx.
      exists T', ctx', s'. intuition auto.
      rewrite smash_context_app. simpl.
      now rewrite -smash_context_subst_empty.
    + eapply invert_cumul_prod_l in HT; auto. 
      rewrite -> app_length in Hlen.
      rewrite Nat.add_1_r in Hlen.
      destruct HT as [na' [A' [B' [[redT convT] HT]]]].
      specialize (IHn ctx ltac:(lia) (Γ ,, vass na ty) B' HT). clear IHctx.
      destruct IHn as [T' [ctx' [s' [[[redT' destT] convctx] leq]]]].
      exists (tProd na' A' T'), (ctx' ++ [vass na' A'])%list, s'. intuition auto. 2:simpl.
      -- transitivity (tProd na' A' B'); auto.
        eapply red_prod. reflexivity.
        todo"red context conv"%string.
      -- now rewrite destArity_app destT.
      -- rewrite smash_context_app /= .
         rewrite !app_context_assoc. simpl.
         eapply conv_context_trans with (Γ ,, vass na ty ,,, ctx'); auto.
         todo "conv context"%string.
Qed.

Lemma subst_context_comm s s' Γ : 
  subst_context s 0 (subst_context s' 0 Γ) =
  subst_context (map (subst s 0) s' ++ s) 0 Γ.
Proof.
  intros.
  rewrite !subst_context_alt !mapi_compose.
  apply mapi_ext => i x.
  destruct x as [na [b|] ty] => //.
  - rewrite /subst_decl /map_decl /=; f_equal.
    rewrite !mapi_length. f_equal. rewrite {2}Nat.add_0_r.
    rewrite subst_app_simpl.
    rewrite distr_subst_rec. rewrite Nat.add_0_r; f_equal. lia.
    rewrite map_length. f_equal. lia.
    rewrite mapi_length.
    rewrite subst_app_simpl.
    rewrite {2}Nat.add_0_r.
    rewrite distr_subst_rec. rewrite Nat.add_0_r; f_equal. lia.
    rewrite map_length. f_equal; lia.
  - rewrite /subst_decl /map_decl /=; f_equal.
    rewrite !mapi_length. rewrite {2}Nat.add_0_r.
    rewrite subst_app_simpl.
    rewrite distr_subst_rec. rewrite Nat.add_0_r; f_equal. lia.
    rewrite map_length. f_equal. lia.
Qed.

Lemma substitution_wf_local `{cf : checker_flags} (Σ : global_env_ext) Γ Γ' s Δ :
  wf Σ -> subslet Σ Γ s Γ' ->
  wf_local Σ (Γ ,,, Γ' ,,, Δ) ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ).
Proof.
  intros wfΣ subs wfl.
  induction Δ.
  simpl. apply All_local_env_app in wfl as [wfl _].
  now apply All_local_env_app in wfl as [wfl _].
  destruct a as [na [b|] ty]; depelim wfl; rewrite subst_context_snoc; simpl in *.
  constructor. now apply IHΔ.
  simpl in H; noconf H.
  simpl in H; noconf H.
  simpl in H; noconf H.
  simpl in *. constructor; auto. red. simpl. rewrite Nat.add_0_r.
  destruct l as [s' Hs].
  eapply substitution in Hs; eauto.
  simpl. rewrite Nat.add_0_r.
  eapply substitution in l0; eauto.
  simpl.
  rewrite /subst_decl. rewrite Nat.add_0_r /map_decl /=.
  constructor. noconf H. auto.
  red. noconf H.
  destruct l as [s' Hs].
  exists s'. eapply substitution in Hs; eauto.
  constructor. noconf H. red.
  noconf H.
Qed.

Lemma destArity_spec_Some ctx T ctx' s :
  destArity ctx T = Some (ctx', s)
  -> it_mkProd_or_LetIn ctx T = it_mkProd_or_LetIn ctx' (tSort s).
Proof.
  pose proof (PCUICClosed.destArity_spec ctx T) as H.
  intro e; now rewrite e in H.
Qed.

Lemma isWAT_tProd {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ} (HΓ : wf_local Σ Γ) {na A B}
  : isWfArity_or_Type Σ Γ (tProd na A B)
    <~> (isType Σ Γ A × isWfArity_or_Type Σ (Γ,, vass na A) B).
Proof.
  split; intro HH.
  - destruct HH as [[ctx [s [H1 H2]]]|[s H]].
    + cbn in H1. apply destArity_app_Some in H1.
      destruct H1 as [ctx' [H1 HH]]; subst ctx.
      rewrite app_context_assoc in H2. split.
      * apply wf_local_app in H2. inversion H2; subst. assumption.
      * left. exists ctx', s. split; tas.
    + apply inversion_Prod in H; tas. destruct H as [s1 [s2 [HA [HB Hs]]]].
      split.
      * eexists; tea.
      * right. eexists; tea.
  - destruct HH as [HA [[ctx [s [H1 H2]]]|HB]].
    + left. exists ([vass na A] ,,, ctx), s. split.
      cbn. now rewrite destArity_app H1.
      now rewrite app_context_assoc.
    + right. destruct HA as [sA HA], HB as [sB HB].
      eexists. econstructor; eassumption.
Defined.

Lemma isWAT_subst {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ Δ} (HΓ : wf_local Σ (Γ ,,, Δ)) {A} s :
    subslet Σ Γ s Δ ->
    isWfArity_or_Type Σ (Γ ,,, Δ) A -> 
    isWfArity_or_Type Σ Γ (subst0 s A).
Proof.
  intros sub WAT.
  destruct WAT.
  - left.
    destruct i as [ctx [s' [wfa wfl]]].
    exists (subst_context s 0 ctx), s'.
    generalize (subst_destArity [] A s 0).
    rewrite wfa. simpl. intros ->.
    split; auto.
    now eapply substitution_wf_local.
  - right.
    destruct i as [s' Hs].
    exists s'. eapply (substitution _ _ Δ s [] _ _ HΣ' sub Hs).
    now apply wf_local_app in HΓ.
Qed.

Lemma isWAT_tLetIn {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ} (HΓ : wf_local Σ Γ) {na t A B}
  : isWfArity_or_Type Σ Γ (tLetIn na t A B)
    <~> (isType Σ Γ A × (Σ ;;; Γ |- t : A)
                      × isWfArity_or_Type Σ (Γ,, vdef na t A) B).
Proof.
  split; intro HH.
  - destruct HH as [[ctx [s [H1 H2]]]|[s H]].
    + cbn in H1. apply destArity_app_Some in H1.
      destruct H1 as [ctx' [H1 HH]]; subst ctx.
      rewrite app_context_assoc in H2. repeat split.
      * apply wf_local_app in H2. inversion H2; subst. assumption.
      * apply wf_local_app in H2. inversion H2; subst. assumption.
      * left. exists ctx', s. split; tas.
    + apply inversion_LetIn in H; tas. destruct H as [s1 [A' [HA [Ht [HB H]]]]].
      repeat split; tas. 1: eexists; eassumption.
      apply cumul_Sort_r_inv in H.
      destruct H as [s' [H H']].
      right. exists s'. eapply type_reduction; tea.
      1:{ constructor; tas. eexists; tea. }
      apply invert_red_letin in H; tas.
      destruct H as [[? [? [? [? [[[H ?] ?] ?]]]]]|H].
      * apply invert_red_sort in H; inv H.
      * etransitivity.
        2: apply weakening_red_0 with (Γ' := [_]) (N := tSort _);
          tea; reflexivity.
        exact (red_rel_all _ (Γ ,, vdef na t A) 0 t A' eq_refl).
  - destruct HH as [HA [Ht [[ctx [s [H1 H2]]]|HB]]].
    + left. exists ([vdef na t A] ,,, ctx), s. split.
      cbn. now rewrite destArity_app H1.
      now rewrite app_context_assoc.
    + right. destruct HB as [sB HB].
      eexists. eapply type_reduction; tas.
      * econstructor; tea.
        apply HA.π2.
      * apply red1_red.
        apply red_zeta with (b':=tSort sB).
Defined.

Lemma typing_spine_strengthen {cf:checker_flags} Σ Γ T T' args U : 
  wf Σ.1 ->
  typing_spine Σ Γ T args U ->
  isWfArity_or_Type Σ Γ T' ->
  Σ ;;; Γ |- T' <= T ->
  ∑ U', (typing_spine Σ Γ T' args U') * (Σ ;;; Γ |- U' <= U).
Proof.
  induction 2 in T' |- *; intros WAT redT.
  - exists T'.
    split. constructor. auto. reflexivity. transitivity ty; auto.
  - eapply invert_cumul_prod_r in c as [na' [A' [B'' HT]]]; auto.
    destruct HT as [[redT' convA] cumulB].
    assert (Σ ;;; Γ |- T' <= tProd na' A' B'').
    transitivity T; auto. now eapply red_cumul.
    eapply invert_cumul_prod_r in X1 as [na'' [A'' [B''' [[redt' convA'] cumulB''']]]]; auto.
    specialize (IHX0 (B''' {0 := hd})).
    have WAT' : isWfArity_or_Type Σ Γ (tProd na'' A'' B'''). {
      eapply (isWfArity_or_Type_red (A:=T')); auto.
    }
    have WAT'': isWfArity_or_Type Σ Γ (B''' {0 := hd}). 
    { eapply isWAT_tProd in WAT' as [AWAT BWAT].
      eapply (isWAT_subst(Δ := [vass na'' A'']) X); eauto.
      constructor; eauto using typing_wf_local.
      constructor. constructor. rewrite subst_empty.
      eapply type_Cumul; eauto. transitivity A'; auto using conv_alt_cumul.
      auto. eauto using typing_wf_local. }
    forward IHX0 by auto.
    forward IHX0. {
      transitivity (B'' {0 := hd}); auto.
      eapply substitution_cumul0; eauto.
      eapply substitution_cumul0; eauto.            
    }
    destruct IHX0 as [U' [spineU' leU']].
    exists U'; split.
    eapply type_spine_cons with na'' A'' B'''; auto.
    now eapply red_cumul. 
    eapply type_Cumul with A; eauto.
    eapply isWAT_tProd in WAT'; intuition eauto using typing_wf_local.
    transitivity A'; auto using conv_alt_cumul.
    assumption.
Qed.

Lemma context_relation_app {P} Γ Γ' Δ Δ' : 
  #|Δ| = #|Δ'| ->
  context_relation P (Γ ,,, Δ) (Γ' ,,, Δ') ->
  context_relation P Γ Γ' * context_relation (fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ')) Δ Δ'.
Proof.
  intros H.
  induction Δ in H, Δ', Γ, Γ' |- *;
  destruct Δ'; try discriminate.
  intuition auto. constructor.
  intros H'. simpl in H.
  specialize (IHΔ Γ Γ' Δ' ltac:(lia)).
  depelim H'; specialize (IHΔ H'); intuition auto;
  constructor; auto.
Qed.

Lemma typing_spine_weaken_concl {cf:checker_flags} Σ Γ T args S S' : 
  wf Σ.1 ->
  typing_spine Σ Γ T args S ->
  Σ ;;; Γ |- S <= S' ->
  isWfArity_or_Type Σ Γ S' ->
  typing_spine Σ Γ T args S'.
Proof.
  intros wfΣ.  
  induction 1 in S' => cum.
  constructor; auto. now transitivity ty'.
  intros isWAT.
  econstructor; eauto.
Qed.

Lemma typing_spine_letin {cf:checker_flags} Σ Γ na b B T args S : 
  wf Σ.1 ->
  typing_spine Σ Γ (tLetIn na b B T) args S ->
  typing_spine Σ Γ (T {0 := b}) args S.
Proof.
  intros wfΣ Hsp.
  depelim Hsp.
  constructor. auto.
  now eapply invert_cumul_letin_l in c.
  econstructor; eauto.
  now eapply invert_cumul_letin_l in c.
Qed.
(* 
Lemma typing_spine_prod {cf:checker_flags} Σ Γ na b B T args S : 
  wf Σ.1 ->
  typing_spine Σ Γ (tProd na b B T) args S ->
  typing_spine Σ Γ (T {0 := b}) args S.
Proof.
  intros wfΣ Hsp.
  depelim Hsp.
  constructor. auto.
  now eapply invert_cumul_letin_l in c.
  econstructor; eauto.
  now eapply invert_cumul_letin_l in c.
Qed. *)
   
Lemma context_assumptions_subst s n Γ : 
  context_assumptions (subst_context s n Γ) = context_assumptions Γ.
Proof. apply context_assumptions_fold. Qed.
Hint Rewrite context_assumptions_subst : pcuic.

Lemma arity_typing_spine {cf:checker_flags} Σ Γ Γ' s inst s' : 
  wf Σ.1 ->
  wf_local Σ Γ ->
  wf_local Σ (Γ ,,, Γ') ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Γ' (tSort s)) inst (tSort s') ->
  #|inst| = context_assumptions Γ' /\ leq_universe (global_ext_constraints Σ) s s'.
Proof.
  intros wfΣ wfΓ wfΓ'; revert s inst s'.
  generalize (le_n #|Γ'|).
  generalize (#|Γ'|) at 2.
  induction n in Γ', wfΓ' |- *. 
  destruct Γ' using rev_ind; try clear IHΓ'; simpl; intros len s inst s' Hsp.
  - depelim Hsp. intuition auto.
    now eapply cumul_Sort_inv.
    now eapply cumul_Sort_Prod_inv in c.
  - rewrite app_length /= in len; elimtype False; lia.
  - intros len s inst s' Hsp.
    destruct Γ' using rev_ind; try clear IHΓ'.
    -- depelim Hsp. intuition auto.
      now eapply cumul_Sort_inv.
      now eapply cumul_Sort_Prod_inv in c.
    -- rewrite app_length /= in len.
      rewrite it_mkProd_or_LetIn_app in Hsp.
      destruct x as [na [b|] ty]; simpl in *; rewrite /mkProd_or_LetIn /= in Hsp.
      + rewrite context_assumptions_app /= Nat.add_0_r.
        eapply typing_spine_letin in Hsp; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn /= in Hsp.
        specialize (IHn (subst_context [b] 0 l)).
        forward IHn. {
          rewrite app_context_assoc in wfΓ'.
          apply All_local_env_app in wfΓ' as [wfb wfa].
          depelim wfb. simpl in H; noconf H. simpl in H. noconf H.
          eapply substitution_wf_local. eauto. 
          epose proof (cons_let_def Σ Γ [] [] na b ty ltac:(constructor)).
          rewrite !subst_empty in X. eapply X. auto.
          eapply All_local_env_app_inv; split.
          constructor; auto. apply wfa. }
        forward IHn by rewrite subst_context_length; lia.
        specialize (IHn s inst s'). 
        now rewrite context_assumptions_subst in IHn.
      + rewrite context_assumptions_app /=.
        depelim Hsp. 
        now eapply cumul_Prod_Sort_inv in c.
        eapply cumul_Prod_inv in c as [conva cumulB].
        eapply (substitution_cumul0 _ _ _ _ _ _ hd) in cumulB; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn /= in cumulB.
        specialize (IHn (subst_context [hd] 0 l)).
        forward IHn. {
          rewrite app_context_assoc in wfΓ'.
          apply All_local_env_app in wfΓ' as [wfb wfa]; eauto.
          depelim wfb. simpl in H; noconf H.
          eapply substitution_wf_local. auto. 
          constructor. constructor. rewrite subst_empty.
          eapply type_Cumul. eapply t.
          right; eapply l0.
          eapply conv_alt_cumul; auto. now symmetry. 
          eapply All_local_env_app_inv; eauto; split.
          constructor; eauto. eapply isWAT_tProd in i; intuition eauto.
          simpl in H; noconf H.
        }
        forward IHn by rewrite subst_context_length; lia.
        specialize (IHn s tl s'). 
        rewrite context_assumptions_subst in IHn.
        eapply typing_spine_strengthen in Hsp.
        4:eapply cumulB. all:eauto.
        simpl. destruct Hsp as [U' [sp' cum]].
        eapply typing_spine_weaken_concl in sp'; eauto using cum.
        intuition auto. now rewrite H0; lia.
        left; eexists _, _; intuition auto.
        left; eexists (subst_context [hd] 0 l), s; intuition auto.
        now rewrite destArity_it_mkProd_or_LetIn /= app_context_nil_l.
        eapply substitution_wf_local; eauto. constructor. constructor.
        rewrite subst_empty. eapply type_Cumul. eapply t.
        2:{ eapply conv_alt_cumul. auto. symmetry. eassumption. } 
        eapply All_local_env_app in wfΓ' as [wfb wfa].
        eapply All_local_env_app in wfa as [wfa' wfa''].
        depelim wfa'. simpl in H; noconf H. right; auto.
        simpl in H; noconf H. 
        unfold snoc. rewrite app_context_assoc in wfΓ'. eapply wfΓ'.
Qed.
  
Lemma context_assumptions_length_bound Γ : context_assumptions Γ <= #|Γ|.
Proof.
  induction Γ; simpl; auto. destruct a as [? [?|] ?]; simpl; auto.
  lia.
Qed.

Lemma conv_context_smash {cf:checker_flags} Σ Γ Δ Δ' : 
  assumption_context Δ ->
  context_relation (fun Δ Δ' => conv_decls Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ' ->
  assumption_context Δ'.
Proof.
  intros Hass Hconv.
  induction Hass in Δ', Hconv |- *. depelim Hconv. constructor.
  depelim Hconv;
  simpl in H; noconf H.
  constructor; auto.
Qed.

Lemma smash_context_assumption_context {Γ Δ} : 
  assumption_context Γ ->
  assumption_context (smash_context Γ Δ).
Proof.
  induction Δ in Γ |- *; simpl; auto.
  destruct a as [? [b|] ty]; auto.
  intros.
  eapply IHΔ. clear -H.
  induction H; simpl; auto. constructor.
  rewrite subst_context_snoc. constructor; auto.
  intros.
  eapply IHΔ.
  clear -H. induction H; simpl; auto. constructor. constructor.
  constructor. auto.
Qed.

Lemma assumption_context_length ctx : assumption_context ctx ->
  context_assumptions ctx = #|ctx|.
Proof.
  induction ctx; simpl; auto.
  destruct a as [na [b|] ty]; simpl.
  intros. depelim H; simpl in H0; noconf H0.
  depelim H; simpl in H0; noconf H0.
  rewrite IHctx; auto.
Qed.
 
(** We can easily invert in case there are only assumptions: not so 
    easy to formulate with LetIn's which have non-local effects.
    Luckily, most kernel functions just expand lets when needed. *)
Lemma inversion_it_mkProd_or_LetIn {cf:checker_flags} Σ {wfΣ : wf Σ.1}:
 forall {Γ Δ t s},
  assumption_context Δ ->
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ t : tSort s ->
  Σ ;;; Γ ,,, Δ |- t : tSort s.
Proof.
intros Γ Δ t s HΔ h. revert HΔ Γ t s h.
induction Δ; intros.
- apply h.
- destruct a as [na [b|] ty]; simpl in *;
  rewrite /mkProd_or_LetIn /= in h.
  elimtype False. depelim HΔ. simpl in H; noconf H.
  forward IHΔ. depelim HΔ. now simpl in H; noconf H.
  clear HΔ.
  specialize (IHΔ _ _ _ h).
  (* eapply inversion_LetIn in IHΔ as [s' [? [? [? [? ?]]]]].
  eapply type_Cumul. eapply t2.
  left. eexists _, _; intuition eauto using typing_wf_local.
  eapply invert_cumul_letin_l in c; auto.
  eapply invert_cumul_sort_r in c as [u' [redu' cumu']].
  transitivity (tSort u'). 2:do 2 constructor; auto. all:auto.
  eapply red_cumul. admit.
  specialize (IHΔ _ _ _ h).
   *)eapply inversion_Prod in IHΔ as [? [? [? [? ]]]].
  eapply type_Cumul; eauto.
  left. eexists _, _; intuition eauto using typing_wf_local.
  do 2 constructor.
  eapply cumul_Sort_inv in c.
  transitivity (Universe.sort_of_product x x0); auto using leq_universe_product.
  auto.
Qed.

(** This lemmma is complicated by the fact that `args` might be an instance
    of arguments for a convertible arity of `ind`.
    Actually #|args| must be exactly of the length of the number of parameters
    + indices (lets excluded). *)
Lemma inversion_Ind_app {cf:checker_flags} Σ Γ ind u c args :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    wf Σ.1 ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    mdecl.(ind_npars) <= #|args| /\ inductive_ind ind < #|ind_bodies mdecl|.
Proof.
  intros mdecl idecl decli wfΣ cty.
  pose proof (typing_wf_local cty).
  apply validity in cty as [_ cty]; auto with wf.
  destruct cty.
  - red in i. destruct i as [ctx [s [da wfext]]].
    now rewrite destArity_tInd in da.
  - destruct i as [s Hs].
    eapply type_mkApps_inv in Hs as [T' [U' [[H Hspine] H']]]; auto.
    have validT' := (validity _ _ _ _ _ _ H).
    specialize (validT' wfΣ (typing_wf_local H)).
    destruct validT' as [_ validT'].
    eapply inversion_Ind in H as [mdecl' [idecl' [wfl [decli' [univs ?]]]]]; auto.
    destruct decli, decli'.
    red in H, H1. rewrite H in H1. noconf H1.
    rewrite H0 in H2. noconf H2.
    assert (declared_inductive Σ.1 mdecl ind idecl).
    split; auto.
    apply on_declared_inductive in H1 as [onmind onind]; auto.
    rewrite (ind_arity_eq onind) in c0; auto.
    rewrite !subst_instance_constr_it_mkProd_or_LetIn in c0.
    simpl in c0.
    eapply invert_cumul_arity_l in c0; auto.
    rewrite !destArity_it_mkProd_or_LetIn in c0.
    destruct c0 as [T'0 [ctx' [s' [[[redT' destT'] convctx]leq]]]].
    eapply isWfArity_or_Type_red in validT'. 3:eapply redT'. 2:auto.
    eapply typing_spine_strengthen in Hspine; last first.
    eapply red_cumul_inv, redT'. all:eauto.
    generalize (destArity_spec [] T'0). rewrite destT'.
    simpl; intros ->.
    pose proof (context_relation_length _ _ _ convctx).
    assert(assumption_context ctx').
    { eapply context_relation_app in convctx as [convΓ convctx'].
      eapply conv_context_smash in convctx'.
      auto. eapply smash_context_assumption_context. constructor.
      rewrite smash_context_length. simpl.
      rewrite !app_context_length smash_context_length /= in H1.
      lia.
    }
    assert(wf_local Σ (Γ ,,, ctx')).
    { destruct validT'.
      destruct i as [ctx'' [s'' [i j]]].
      rewrite destArity_it_mkProd_or_LetIn /= in i. noconf i. 
      rewrite app_context_nil_l in j. apply j.
      destruct i as [i Hs].
      eapply inversion_it_mkProd_or_LetIn in Hs.
      eauto using typing_wf_local. auto. auto. }
    destruct Hspine as [U'concl [sp' cum']].
    rewrite app_context_length smash_context_length /= app_context_nil_l context_assumptions_app in H1.
    rewrite !subst_instance_context_assumptions onmind.(onNpars _ _ _ _) app_context_length in H1.
    clear destT' redT'.
    eapply typing_spine_weaken_concl in sp'.
    3:{ transitivity U'. eapply cum'. eapply H'. }
    eapply arity_typing_spine in sp'; eauto.
    destruct sp'.
    rewrite H3 (assumption_context_length ctx') //.
    split. lia. now eapply nth_error_Some_length in H0.
    auto.
    left. eexists _, _; intuition auto.
Qed.

Lemma subst_inds_concl_head ind u mdecl (arity : context) :
  let head := tRel (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| + #|arity|) in
  let s := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  inductive_ind ind < #|ind_bodies mdecl| ->
  subst s (#|arity| + #|ind_params mdecl|)
        (subst_instance_constr u head)
  = tInd ind u.
Proof.
  intros.
  subst head. simpl subst_instance_constr.
  rewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| - S (inductive_ind ind)) (tInd ind u)) //; try lia.
  subst s. rewrite inds_spec rev_mapi nth_error_mapi /=.
  elim nth_error_spec. intros. simpl.
  f_equal. destruct ind; simpl. f_equal. f_equal. simpl in H. lia.
  rewrite List.rev_length. lia.
Qed.

Lemma type_Case_valid_btys {cf:checker_flags} Σ Γ ind u npar p c args :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    wf Σ.1 ->
    mdecl.(ind_npars) = npar ->
    let pars := List.firstn npar args in
    forall pty, Σ ;;; Γ |- p : pty ->
    forall indctx pctx ps btys, types_of_case ind mdecl idecl pars u p pty
                           = Some (indctx, pctx, ps, btys) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    All (fun x => Σ ;;; Γ |- snd x : tSort ps) btys.
Proof.
  intros mdecl idecl isdecl wfΣ H0 pars pty X indctx pctx ps btys toc cty.
  apply types_of_case_spec in toc.
  destruct toc as [s' [instpar [H1 H2]]].
  pose proof (PCUICClosed.destArity_spec [] pty) as Hpty; rewrite H1 in Hpty;
    cbn in Hpty; subst; clear H1.
  unfold build_branches_type in H2.
  eapply map_option_out_All; tea. clear H2.
  apply All_mapi.
  pose proof isdecl as isdecl'.
  apply PCUICWeakeningEnv.on_declared_inductive in isdecl' as [oind oc]; auto.
  pose proof oc.(onConstructors) as oc'.
  eapply All_Alli. eapply All2_All_left_pack; tea. cbn.
  intros n [[id ct] k] [cs [Hct1 Hct2]]; cbn in *.
  case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) pars
             ((subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)))
                (subst_instance_constr u ct))); [|simpl; trivial].
  intros ct' Hct'.
  case_eq (decompose_prod_assum [] ct'); intros sign ccl e1.
  case_eq (chop (ind_npars mdecl) (decompose_app ccl).2);
  intros paramrels args0 e2; cbn.
  destruct Hct1 as [s Hs].
  destruct Hct2 as [cs' Hcs'].
  destruct cs'. simpl in *. subst ct.
  eapply instantiate_params_make_context_subst in Hct'.
  destruct Hct' as [ctx' [ty'' [parinst Hct']]].
  rewrite !subst_instance_constr_it_mkProd_or_LetIn in Hct'.
  rewrite !subst_it_mkProd_or_LetIn in Hct'.
  rewrite -(subst_context_length  (inds (inductive_mind ind) u
     (ind_bodies mdecl)) 0) in Hct'.
  rewrite decompose_prod_n_assum_it_mkProd app_nil_r in Hct'.
  destruct Hct' as [[= eqs eqs'] [eqpars ->]].
  subst ctx' ty''.
  rewrite !subst_it_mkProd_or_LetIn in e1.
  eapply inversion_Ind_app in cty as [argapp indannot]; eauto.
  rewrite decompose_prod_assum_it_mkProd in e1.
  rewrite !subst_context_length !subst_instance_context_length !Nat.add_0_r.
  rewrite subst_cstr_concl_head.
   intuition auto. 
  rewrite subst_mkApps. simpl. apply is_ind_app_head_mkApps.
  noconf e1. simpl in e2. 
  rewrite !subst_context_length app_nil_r !subst_instance_context_length.
  rewrite !subst_context_length.
  rewrite Nat.add_0_r !subst_context_length !subst_instance_context_length in e2.
  rewrite subst_instance_constr_mkApps !subst_mkApps /cshape_concl_head in e2.
  rewrite decompose_app_mkApps in e2.
  rewrite !Nat.add_0_r.
  rewrite subst_inds_concl_head. auto. simpl. trivial.
  simpl in e2. 
  rewrite !map_map_compose in e2.
  apply make_context_subst_spec in eqpars.
  rewrite List.rev_involutive in eqpars.
  eapply type_Cumul with (tSort (Universe.sort_of_product ps ps)).
  eapply type_it_mkProd_or_LetIn; eauto.
  3:{ left. exists [], ps; intuition eauto using typing_wf_local. }
  3:{ todo "universes: @Simon". }
  red in oc'.
  destruct oc.
  todo "the context of arguments should be typeable with ps (from Simon's PR)"%string.
  rewrite !subst_instance_context_length Nat.add_0_r.
  rewrite map_app in e2.
  rewrite chop_n_app in e2.
  { rewrite !map_length to_extended_list_k_length.
    destruct oind. auto. }
  noconf e2.
  eapply type_mkApps. all:eauto.
  eapply weakening_gen; eauto.
  - now rewrite !subst_context_length !subst_instance_context_length.
  - eapply typing_wf_local in X.
  todo "wf_local of the substituted arguments context, by sustitution lemma,
  knowing that params forms a well-typed instantiation of the inductive type.
  Needs more properties from inversion_Ind_app"%string.
  - todo "typing_spine proof: the params + rels for the arguments are a well
  typed rgument list for the inductive"%string.
Qed.

Lemma type_Case' {cf:checker_flags} Σ Γ ind u npar p c brs args :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    mdecl.(ind_npars) = npar ->
    wf Σ.1 ->
    let pars := List.firstn npar args in
    forall pty, Σ ;;; Γ |- p : pty ->
    forall indctx pctx ps btys, types_of_case ind mdecl idecl pars u p pty
                           = Some (indctx, pctx, ps, btys) ->
    check_correct_arity (global_ext_constraints Σ) idecl ind u indctx pars pctx ->
    existsb (leb_sort_family (universe_family ps)) idecl.(ind_kelim) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    All2 (fun x y => (fst x = fst y) × (Σ ;;; Γ |- snd x : snd y)) brs btys ->
    Σ ;;; Γ |- tCase (ind, npar) p c brs : mkApps p (List.skipn npar args ++ [c]).
Proof.
  intros mdecl idecl isdecl wfΣ H pars pty X indctx pctx ps btys H0 X0 H1 X1 X2.
  econstructor; tea.
  eapply type_Case_valid_btys in H0; tea.
  eapply All2_All_mix_right; tas.
Qed.
