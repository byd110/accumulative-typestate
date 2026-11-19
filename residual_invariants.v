(* Reachable regex environments describe the runtime histories themselves.
   The canonical conversion preserves finite-map shadowing and yields an exact
   empty output environment, including when the remaining statement is Skip. *)
From Coq Require Import List Arith Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import regexp.
From Accumulation Require Import syntax trace_languages protocols semantics typestate
  invariants soundness regular_protocols residual_typestate.
Import ListNotations.
Set Implicit Arguments.

Section CanonicalResiduals.
Variable A : finType.
Variable initial : class -> regexp A.
Fixpoint residual_after (r : regexp A) (w : list A) : regexp A :=
  match w with [] => r | a::u => residual_after (regex_derivative a r) u end.
Definition canonical_regex c w := residual_after (initial c) w.
Definition canonical_qualifier (q : qualifier A) := (fst q,canonical_regex (fst q) (snd q)).
Definition canonical_env (g : environment A) : regex_environment A :=
  map (fun p => (fst p,option_map canonical_qualifier (snd p))) g.
Lemma residual_after_app r u v :
  residual_after r (u ++ v) = residual_after (residual_after r u) v.
Proof. revert r; induction u; intros r; simpl; auto. Qed.
Lemma residual_after_correct r w v :
  denote (residual_after r w) v <-> denote r (w ++ v).
Proof.
  revert r; induction w as [|a w IH]; intros r; simpl; [reflexivity|].
  rewrite IH regex_derivative_correct. reflexivity.
Qed.
Lemma canonical_regex_empty c : canonical_regex c [] = initial c.
Proof. reflexivity. Qed.
Lemma canonical_regex_snoc c w a :
  canonical_regex c (w ++ [a]) = regex_derivative a (canonical_regex c w).
Proof. unfold canonical_regex. rewrite residual_after_app. reflexivity. Qed.
Lemma canonical_get g x : get (canonical_env g) x = option_map canonical_qualifier (get g x).
Proof.
  induction g as [|[y ov] g IH]; simpl; [reflexivity|].
  destruct (Nat.eqb x y); [reflexivity|exact IH].
Qed.
Lemma canonical_put g x c w : canonical_env (put g x (Some (c,w))) =
  put (canonical_env g) x (Some (c,canonical_regex c w)).
Proof. reflexivity. Qed.
End CanonicalResiduals.

Section RuntimeResiduals.
Variable A : finType.
Variable P : protocol_family A.
Variable FT : class -> field -> class.
Variable initial : class -> regexp A.
Hypothesis initial_correct : forall c w, denote (initial c) w <-> protocol P c w.

Lemma canonical_represents c w :
  residual_typestate.represents P c w (canonical_regex initial c w).
Proof.
  intros v; unfold canonical_regex; rewrite residual_after_correct.
  apply initial_correct.
Qed.
Lemma canonical_related g : environments_related P g (canonical_env initial g).
Proof.
  intros x; rewrite canonical_get. destruct (get g x) as [[c w]|]; simpl.
  - split; [reflexivity|apply canonical_represents].
  - exact I.
Qed.
Lemma canonical_primitive_typing g i g' : type_step P FT g i g' ->
  regex_type_step FT initial (canonical_env initial g) i (canonical_env initial g').
Proof.
  intros H; destruct H; rewrite ?canonical_put ?canonical_regex_empty ?canonical_regex_snoc.
  - constructor.
    + apply (proj1 (retirable_correspondence x (canonical_related g))); exact H.
    + apply (proj2 (represents_nonempty (canonical_represents c []))); exact H0.
  - eapply regex_type_copy.
    + rewrite canonical_get H; reflexivity.
    + apply (proj1 (retirable_correspondence x (canonical_related g))); exact H0.
    + apply (proj2 (represents_nonempty (canonical_represents c []))); exact H1.
  - eapply regex_type_load.
    + rewrite canonical_get H; reflexivity.
    + apply (proj1 (retirable_correspondence x (canonical_related g))); exact H0.
    + apply (proj2 (represents_nonempty (canonical_represents (FT c f) []))); exact H1.
  - eapply regex_type_store.
    + rewrite canonical_get H; reflexivity.
    + rewrite canonical_get H0; reflexivity.
    + exact H1.
  - eapply regex_type_call.
    + rewrite canonical_get H; reflexivity.
    + apply (proj2 (represents_nonempty (derivative_represents a (canonical_represents c w)))); exact H0.
  - apply regex_type_finish.
    apply (proj1 (completion_correspondence (canonical_related g))); exact H.
Qed.
Theorem canonical_statement_typing g s g' : typed_stmt P FT g s g' ->
  regex_typed_stmt FT initial (canonical_env initial g) s (canonical_env initial g').
Proof.
  intros H; induction H.
  - apply regex_typed_primitive; now apply canonical_primitive_typing.
  - apply regex_typed_skip.
  - eapply regex_typed_seq; eauto.
Qed.

Record residual_runtime_invariant (m : machine A) (G : regex_environment A) : Prop := {
  residual_binding_agreement : forall x,
    match get (refs m) x, get G x with
    | None,None => True
    | Some e,Some (c,r) => c=classes m (owners m e) /\
        residual_typestate.represents P c (local_history m e) r /\ regex_nonempty r=true
    | _,_ => False
    end;
  residual_retired_complete : forall e, Nat.lt e (next_epoch m) ->
    (forall x, get (refs m) x <> Some e) ->
    protocol P (classes m (owners m e)) (local_history m e)
}.

Lemma invariant_residual_representation m g G : invariant P FT m g ->
  environments_related P g G -> residual_runtime_invariant m G.
Proof.
  intros HI HR; constructor.
  - intros x; specialize (HR x). rewrite <- (inv_agree HI x) in HR.
    destruct (get (refs m) x) as [e|] eqn:E;
      destruct (get G x) as [[c r]|] eqn:EG; simpl in HR; try contradiction; [|exact I].
    destruct HR as [HC Hr]; subst c. split; [reflexivity|]. split; [exact Hr|].
    apply (proj2 (represents_nonempty Hr)).
    eapply inv_viable; [exact HI|apply (agree_ref x HI E)].
  - intros e He Hd; unfold protocol, local_history; eapply inv_retired; eauto.
Qed.

Theorem reachable_residual_configuration s m t :
  check_program P FT s=true -> execution (initial_machine,instrument s) (m,t) ->
  exists G, regex_typed_stmt FT initial G t [] /\ residual_runtime_invariant m G.
Proof.
  intros HC HE. apply check_program_spec in HC; destruct HC as [_ HT].
  destruct (execution_preservation HE (invariant_initial P FT) HT) as [g [HI Ht]].
  exists (canonical_env initial g); split.
  - exact (canonical_statement_typing Ht).
  - eapply invariant_residual_representation; [exact HI|apply canonical_related].
Qed.
End RuntimeResiduals.

From Accumulation Require Import copying_typestate copying_languages copying_soundness
  copying_residual_typestate.

Section CopyingRuntimeResiduals.
Variable A : finType.
Variable P : protocol_family A.
Variable FT : class -> field -> class.
Variable initial : class -> regexp A.
Variable mode : class -> bool.
Hypothesis initial_correct : forall c w, denote (initial c) w <-> protocol P c w.

Lemma canonical_copying_primitive_typing g i g' : type_step_with_copy P FT mode g i g' ->
  regex_copy_type_step FT initial mode (canonical_env initial g) i (canonical_env initial g').
Proof.
  intros H; destruct H.
  - apply regex_copy_ordinary; [apply (canonical_primitive_typing initial initial_correct); constructor; eauto|discriminate].
  - rewrite canonical_put.
    have Ec : canonical_regex initial c (if mode c then w else []) =
      (if mode c then canonical_regex initial c w else initial c).
    { destruct (mode c); reflexivity. }
    rewrite Ec. eapply regex_copy_assignment.
    + rewrite canonical_get H; reflexivity.
    + apply (proj1 (retirable_correspondence x (canonical_related initial initial_correct g))); exact H0.
    + destruct (mode c); [exact I|].
      apply (proj2 (represents_nonempty (canonical_represents initial initial_correct c []))); exact H1.
  - apply regex_copy_ordinary; [apply (canonical_primitive_typing initial initial_correct); econstructor; eauto|discriminate].
  - apply regex_copy_ordinary; [apply (canonical_primitive_typing initial initial_correct); econstructor; eauto|discriminate].
  - apply regex_copy_ordinary; [apply (canonical_primitive_typing initial initial_correct); econstructor; eauto|discriminate].
  - apply regex_copy_ordinary; [apply (canonical_primitive_typing initial initial_correct); constructor; eauto|discriminate].
Qed.
Theorem canonical_copying_statement_typing g s g' : typed_stmt_with_copy P FT mode g s g' ->
  regex_copy_typed_stmt FT initial mode (canonical_env initial g) s (canonical_env initial g').
Proof.
  intros H; induction H.
  - apply regex_copy_typed_primitive; now apply canonical_copying_primitive_typing.
  - apply regex_copy_skip.
  - eapply regex_copy_seq; eauto.
Qed.

(* Inherited views overlap. The V map and the continuation invariant retain
   that distinction; they are never identified with disjoint event histories. *)
Record copying_residual_runtime_invariant (m : machine A) (G : regex_environment A)
    (V : nat -> list A) : Prop := {
  copying_residual_shape : shape FT m;
  copying_residual_binding : forall x,
    match get (refs m) x, get G x with
    | None,None => True
    | Some e,Some (c,r) => c=classes m (owners m e) /\
        residual_typestate.represents P c (V e) r /\ regex_nonempty r=true
    | _,_ => False
    end;
  copying_residual_retired : forall e, Nat.lt e (next_epoch m) ->
    (forall x, get (refs m) x <> Some e) -> protocol P (classes m (owners m e)) (V e);
  copying_residual_future : forall l, Nat.lt l (next_loc m) ->
    future_safe (protocol P (classes m l)) (epoch_set m l) V (object_history m l)
}.

Lemma copying_invariant_residual_representation m g G V : copying_invariant P FT m g V ->
  environments_related P g G -> copying_residual_runtime_invariant m G V.
Proof.
  intros HI HR; constructor.
  - exact (ci_shape HI).
  - intros x; specialize (HR x); rewrite <- (ci_agree HI x) in HR.
    destruct (get (refs m) x) as [e|] eqn:E;
      destruct (get G x) as [[c r]|] eqn:EG; simpl in HR; try contradiction; [|exact I].
    destruct HR as [HC Hr]; subst c. split; [reflexivity|]. split; [exact Hr|].
    apply (proj2 (represents_nonempty Hr)); apply (ci_viable HI).
    destruct (ci_shape HI) as [h Hshape]; eapply inv_refs; eauto.
  - intros e He Hd; unfold protocol; eapply ci_retired; eauto.
  - exact (ci_future HI).
Qed.

Theorem copying_reachable_residual_configuration s m t : copying_certified P mode ->
  check_program_with_copy P FT mode s=true -> execution (initial_machine,instrument s) (m,t) ->
  exists G V, regex_copy_typed_stmt FT initial mode G t [] /\
    copying_residual_runtime_invariant m G V.
Proof.
  intros HM HC HE; apply check_program_with_copy_spec in HC; destruct HC as [_ HT].
  destruct (copying_execution_preservation HM HE (ci_initial P FT) HT) as [g [V [HI Ht]]].
  exists (canonical_env initial g), V; split.
  - exact (canonical_copying_statement_typing Ht).
  - eapply copying_invariant_residual_representation; [exact HI|].
    apply canonical_related; exact initial_correct.
Qed.
End CopyingRuntimeResiduals.

Section RegularReachability.
Variable A : finType.
Variable FT : class -> field -> class.
Variable spec : class -> regexp A.
Theorem regular_reachable_residual_configuration s m t :
  check_program (regular_family spec) FT s=true ->
  execution (initial_machine,instrument s) (m,t) ->
  exists G, regex_typed_stmt FT (fun c => closure_regex (spec c)) G t [] /\
    residual_runtime_invariant (regular_family spec) m G.
Proof.
  apply reachable_residual_configuration.
  apply regular_initial_correct.
Qed.
Theorem copying_regular_reachable_residual_configuration mode s m t :
  copying_certified (regular_family spec) mode ->
  check_program_with_copy (regular_family spec) FT mode s=true ->
  execution (initial_machine,instrument s) (m,t) ->
  exists G V, regex_copy_typed_stmt FT (fun c => closure_regex (spec c)) mode G t [] /\
    copying_residual_runtime_invariant (regular_family spec) FT m G V.
Proof.
  apply copying_reachable_residual_configuration.
  apply regular_initial_correct.
Qed.
End RegularReachability.
