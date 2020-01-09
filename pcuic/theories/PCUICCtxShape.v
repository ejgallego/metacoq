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