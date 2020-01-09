(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.CRelationClasses ProofIrrelevance ssreflect.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICCumulativity PCUICSR PCUICPosition PCUICEquality PCUICNameless
     PCUICAlpha PCUICNormal PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion PCUICValidity
     PCUICParallelReductionConfluence PCUICWeakeningEnv
     PCUICClosed PCUICPrincipality PCUICSubstitution
     PCUICWeakening PCUICGeneration PCUICUtils PCUICCtxShape PCUICContexts
     PCUICUniverses.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.

Derive Signature for typing_spine.

Lemma isArity_it_mkProd_or_LetIn Γ t : isArity t -> isArity (it_mkProd_or_LetIn Γ t).
Proof.
  intros isA. induction Γ using rev_ind; simpl; auto.
  rewrite it_mkProd_or_LetIn_app. simpl; auto.
  destruct x as [? [?|] ?]; simpl; auto.
Qed.

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
- destruct ctx; simpl in Hlen; try lia.
  eapply invert_cumul_sort_l in HT as [u' [redT leqT]].
  exists (tSort u'), [], u'; intuition auto.
  reflexivity. elimtype False; lia.
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
    rewrite wfa /= => ->.
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



Lemma typing_spine_letin_inv {cf:checker_flags} {Σ Γ na b B T args S} : 
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

Lemma typing_spine_letin {cf:checker_flags} {Σ Γ na b B T args S} : 
  wf Σ.1 ->
  typing_spine Σ Γ (T {0 := b}) args S ->
  typing_spine Σ Γ (tLetIn na b B T) args S.
Proof.
  intros wfΣ Hsp.
  depelim Hsp.
  constructor. auto.
  etransitivity. eapply red_cumul. eapply red1_red, red_zeta. auto.
  econstructor; eauto.
  etransitivity. eapply red_cumul. eapply red1_red, red_zeta. auto.
Qed.

Lemma typing_spine_weaken_concl {cf:checker_flags} {Σ Γ T args S S'} : 
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

Lemma typing_spine_prod {cf:checker_flags} {Σ Γ na b B T args S} : 
  wf Σ.1 ->
  typing_spine Σ Γ (T {0 := b}) args S ->
  isWfArity_or_Type Σ Γ (tProd na B T) ->
  Σ ;;; Γ |- b : B ->
  typing_spine Σ Γ (tProd na B T) (b :: args) S.
Proof.
  intros wfΣ Hsp.
  depelim Hsp.
  econstructor; eauto. constructor; auto.
  intros Har. eapply isWAT_tProd in Har as [? ?]; eauto using typing_wf_local.
  intros Hb.
  econstructor. 3:eauto. 2:eauto. 
  destruct i1 as [[ctx [s [Hs ?]]]|?].
  - left. exists ([vass na B] ,,, ctx), s; simpl; intuition auto.
    rewrite destArity_app Hs /= ?app_context_nil_l //.
    now rewrite app_context_assoc.
  - right. destruct i1 as [s Hs], i0 as [s' Hs'].
    eexists. eapply type_Prod; eauto.
  - econstructor; eauto.
Qed.

Lemma typing_spine_WAT_concl {cf:checker_flags} {Σ Γ T args S} : 
  typing_spine Σ Γ T args S ->
  isWfArity_or_Type Σ Γ S.
Proof.
  induction 1; auto.
Qed.

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
        eapply typing_spine_letin_inv in Hsp; auto.
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


Lemma mkApps_ind_typing_spine {cf:checker_flags} Σ Γ Γ' ind i
  inst ind' i' args args' : 
  wf Σ.1 ->
  wf_local Σ Γ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) inst 
    (mkApps (tInd ind' i') args') ->
  #|inst| = context_assumptions Γ' /\ ind = ind'.
Proof.
  intros wfΣ wfΓ; revert args args' ind i ind' i' inst.
  generalize (le_n #|Γ'|).
  generalize (#|Γ'|) at 2.
  induction n in Γ' |- *. 
  destruct Γ' using rev_ind; try clear IHΓ'; simpl; intros len args args' ind i ind' i' inst wat Hsp.
  - depelim Hsp. intuition auto.
    eapply invert_cumul_ind_l in c as [? [? [? ?]]]; auto.
    eapply invert_red_ind in r as [? [eq ?]]. now solve_discr.
    eapply invert_cumul_prod_r in c as [? [? [? [[? ?] ?]]]]; auto.
    eapply invert_red_ind in r as [? [eq ?]]. now solve_discr.
  - rewrite app_length /= in len; elimtype False; lia.
  - intros len args args' ind i ind' i' inst wat Hsp.
    destruct Γ' using rev_ind; try clear IHΓ'.
    -- depelim Hsp. intuition auto.
      eapply invert_cumul_ind_l in c as [? [? [? ?]]]; auto.
      eapply invert_red_ind in r as [? [eq ?]]. now solve_discr.
      eapply invert_cumul_prod_r in c as [? [? [? [[? ?] ?]]]]; auto.
      eapply invert_red_ind in r as [? [eq ?]]. now solve_discr.
    -- rewrite app_length /= in len.
      rewrite it_mkProd_or_LetIn_app in Hsp.
      destruct x as [na [b|] ty]; simpl in *; rewrite /mkProd_or_LetIn /= in Hsp.
      + rewrite context_assumptions_app /= Nat.add_0_r.
        eapply typing_spine_letin_inv in Hsp; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn /= in Hsp.
        specialize (IHn (subst_context [b] 0 l)).
        forward IHn by rewrite subst_context_length; lia.
        rewrite subst_mkApps Nat.add_0_r in Hsp.
        specialize (IHn (map (subst [b] #|l|) args) args' ind i ind' i' inst).
        forward IHn. {
          move: wat; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => wat.
          eapply isWfArity_or_Type_red in wat; last first. eapply red1_red.
          constructor. auto.
          now rewrite /subst1 subst_it_mkProd_or_LetIn subst_mkApps Nat.add_0_r
          in wat. }
        now rewrite context_assumptions_subst in IHn.
      + rewrite context_assumptions_app /=.
        pose proof (typing_spine_WAT_concl Hsp).
        depelim Hsp.
        eapply invert_cumul_prod_l in c as [? [? [? [[? ?] ?]]]]; auto.
        eapply invert_red_ind in r as [? [eq ?]]. now solve_discr.
        eapply cumul_Prod_inv in c as [conva cumulB].
        eapply (substitution_cumul0 _ _ _ _ _ _ hd) in cumulB; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn /= in cumulB.
        specialize (IHn (subst_context [hd] 0 l)).
        forward IHn by rewrite subst_context_length; lia.
        specialize (IHn (map (subst [hd] #|l|) args) args' ind i ind' i' tl). all:auto.
        have isWATs: isWfArity_or_Type Σ Γ
        (it_mkProd_or_LetIn (subst_context [hd] 0 l)
           (mkApps (tInd ind i) (map (subst [hd] #|l|) args))). {
          move: wat; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => wat.
          eapply isWAT_tProd in wat; auto. destruct wat as [isty wat].
          epose proof (isWAT_subst wfΣ (Γ:=Γ) (Δ:=[vass na ty])).
          forward X0. constructor; auto.
          specialize (X0 (it_mkProd_or_LetIn l (mkApps (tInd ind i) args)) [hd]).
          forward X0. constructor. constructor. rewrite subst_empty; auto.
          eapply isWAT_tProd in i0; auto. destruct i0. 
          eapply type_Cumul with A; auto. now eapply conv_alt_cumul.
          now rewrite /subst1 subst_it_mkProd_or_LetIn subst_mkApps Nat.add_0_r
          in X0. }
        rewrite subst_mkApps Nat.add_0_r in cumulB. simpl in *. 
        rewrite context_assumptions_subst in IHn.
        eapply typing_spine_strengthen in Hsp.
        4:eapply cumulB. all:eauto.
        simpl. destruct Hsp as [U' [sp' cum]].
        eapply typing_spine_weaken_concl in sp'; eauto using cum.
        intuition auto. now rewrite H; lia.
Qed.

Lemma type_mkProd_or_LetIn {cf:checker_flags} Σ Γ d u t s : 
  wf Σ.1 ->
  Σ ;;; Γ |- decl_type d : tSort u ->
  Σ ;;; Γ ,, d |- t : tSort s ->
  match decl_body d return Type with 
  | Some b => Σ ;;; Γ |- mkProd_or_LetIn d t : tSort s
  | None => Σ ;;; Γ |- mkProd_or_LetIn d t : tSort (Universe.sort_of_product u s)
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
    { apply typing_wf_local in Ht as XX. inversion XX; subst.
      eapply (type_mkProd_or_LetIn _ _ {| decl_body := Some b |}); auto.
      + simpl. exact X0.π2.
      + eapply type_Cumul; eauto.
        left. eexists [], _. intuition eauto.
        constructor. constructor. eapply leq_universe_product. }
    eapply (type_mkProd_or_LetIn _ _ {| decl_body := None |}) => /=; eauto.
    left. eexists [], _; intuition eauto using typing_wf_local.
    eapply typing_wf_local in Ht.
    depelim Ht; eapply All_local_env_app in Ht; intuition auto.
    constructor. constructor.
    apply eq_universe_leq_universe.
    apply sort_of_product_twice.
Qed.

Local Open Scope string_scope.



Lemma isWAT_wf_local {cf:checker_flags} {Σ Γ T} : isWfArity_or_Type Σ Γ T -> wf_local Σ Γ.
Proof.
  move=> [[ctx [s [_ Hs]]]|[s Hs]]. 
  - eapply All_local_env_app in Hs.
    intuition eauto with pcuic.
  - now eapply typing_wf_local.
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

 
(** We can easily invert in case there are only assumptions: not so 
    easy to formulate with LetIn's which have non-local effects.
    Luckily, most kernel functions just expand lets when needed. *)
(*
  Lemma inversion_it_mkProd_or_LetIn {cf:checker_flags} Σ {wfΣ : wf Σ.1}:
 forall {Γ Δ t s},
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ t : tSort s ->
  Σ ;;; Γ ,,, Δ |- t : tSort s.
Proof.
intros Γ Δ t s h. revert Γ t s h.
induction Δ; intros.
- apply h.
- destruct a as [na [b|] ty]; simpl in *;
  rewrite /mkProd_or_LetIn /= in h.
  specialize (IHΔ _ _ _ h).
  eapply inversion_LetIn in IHΔ as [s' [? [? [? [? ?]]]]]; auto.
  eapply type_Cumul. eapply t2.
  left. eexists _, _; intuition eauto using typing_wf_local.
  eapply invert_cumul_letin_l in c; auto.
  eapply invert_cumul_sort_r in c as [u' [redu' cumu']].
  transitivity (tSort u'). 2:do 2 constructor; auto. all:auto.
  eapply red_cumul.
  transitivity (x {0 := b}).
  eapply red1_red. 

  specialize (IHΔ _ _ _ h).
   
  eapply inversion_Prod in IHΔ as [? [? [? [? ]]]].
  eapply type_Cumul; eauto.
  left. eexists _, _; intuition eauto using typing_wf_local.
  do 2 constructor.
  eapply cumul_Sort_inv in c.
  transitivity (Universe.sort_of_product x x0); auto using leq_universe_product.
  auto.
Qed.*)

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
   *)
  eapply inversion_Prod in IHΔ as [? [? [? [? ]]]].
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
Lemma inversion_WAT_indapp {cf:checker_flags} Σ Γ ind u args :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    wf Σ.1 ->
    isType Σ Γ (mkApps (tInd ind u) args) ->
    mdecl.(ind_npars) <= #|args| /\ inductive_ind ind < #|ind_bodies mdecl| /\
    consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  intros mdecl idecl decli wfΣ cty.
  destruct cty as [s Hs].
  pose proof (typing_wf_local Hs).
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
  rewrite (ind_arity_eq onind) in c; auto.
  rewrite !subst_instance_constr_it_mkProd_or_LetIn in c.
  simpl in c.
  eapply invert_cumul_arity_l in c; auto.
  rewrite !destArity_it_mkProd_or_LetIn in c.
  destruct c as [T'0 [ctx' [s' [[[redT' destT'] convctx]leq]]]].
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
  rewrite !subst_instance_context_assumptions app_context_length in H1.
  rewrite onmind.(onNpars _ _ _ _) in H1.
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
