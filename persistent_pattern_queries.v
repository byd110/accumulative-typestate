(* Executable queries for a finite persistent machine.  A fixed suffix that
   completes every state establishes exact viability, including the sink case. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa.
From Accumulation Require Import trace_languages protocols syntax semantics
  typestate copying_typestate copying_soundness monotone_protocols
  monotone_pumping monotone_regular accumulation_bridge.
Set Implicit Arguments.

Section Queries.
Variables A S : finType.
Variable M : monotone_machine A S.
Variable enabledb : S -> A -> bool.
Variable completeb : S -> bool.
Hypothesis enabledb_spec : forall s a, enabledb s a = true <-> mm_enabled M s a.
Hypothesis completeb_spec : forall s, completeb s = true <-> mm_accept M s.
Variable initial : S.

Fixpoint persistent_run (s : S) (w : seq A) : option S :=
  if w is a :: rest then
    if enabledb s a then persistent_run (mm_step M s a) rest else None
  else Some s.
Definition persistent_accept (w : seq A) : bool :=
  if persistent_run initial w is Some s then completeb s else false.
Definition persistent_viable (w : seq A) : bool :=
  if persistent_run initial w is Some _ then true else false.

Lemma persistent_run_spec s w t :
  persistent_run s w = Some t <-> machine_run M s w t.
Proof.
  split.
  - revert s. induction w as [|a w IH]; intros s H; simpl in H.
    + inversion H; subst. constructor.
    + destruct (enabledb s a) eqn:E; try discriminate.
      constructor; [apply enabledb_spec; exact E|]. apply IH. exact H.
  - intros H. induction H; simpl; auto.
    have E := proj2 (enabledb_spec s a) H. by rewrite E.
Qed.
Lemma persistent_run_app s u v :
  persistent_run s (u ++ v) =
  if persistent_run s u is Some t then persistent_run t v else None.
Proof.
  revert s. induction u as [|a u IH]; intros s; simpl; auto.
  destruct (enabledb s a); auto.
Qed.
Lemma persistent_accept_spec w :
  persistent_accept w = true <-> machine_language M initial w.
Proof.
  unfold persistent_accept, machine_language. split.
  - destruct (persistent_run initial w) as [s|] eqn:E; try discriminate.
    intros H. exists s. split; [now apply persistent_run_spec|].
    apply completeb_spec. exact H.
  - intros [s [Hr Ha]]. apply persistent_run_spec in Hr. rewrite Hr.
    apply completeb_spec. exact Ha.
Qed.

Variable suffix : seq A.
Hypothesis suffix_completes : forall s,
  exists t, persistent_run s suffix = Some t /\ completeb t = true.

Lemma persistent_viable_spec w :
  persistent_viable w = true <-> exists v, persistent_accept (w ++ v) = true.
Proof.
  unfold persistent_viable, persistent_accept.
  setoid_rewrite persistent_run_app.
  destruct (persistent_run initial w) as [s|] eqn:E.
  - split; [|auto]. intros _.
    exists suffix. destruct (suffix_completes s) as [t [Hr Ha]].
    rewrite Hr. exact Ha.
  - split; [discriminate|]. intros [v H]. discriminate.
Qed.
Definition persistent_family : protocol_family A :=
  {| accepts := fun _ => persistent_accept;
     viable := fun _ => persistent_viable;
     viable_spec := fun _ => persistent_viable_spec |}.

Theorem persistent_language_regular c : regular (protocol persistent_family c).
Proof.
  exists (@machine_dfa A S M enabledb completeb initial). intros w.
  change (persistent_accept w = true <-> w \in dfa_lang (@machine_dfa A S M enabledb completeb initial)).
  rewrite persistent_accept_spec. symmetry. apply machine_dfa_language;
    [exact enabledb_spec|exact completeb_spec].
Qed.
Theorem persistent_certified : certified persistent_family.
Proof.
  intros c u v w Hu Hv Hsh. apply persistent_accept_spec.
  eapply machine_language_shuffle_closed;
    [apply persistent_accept_spec; exact Hu|
     apply persistent_accept_spec; exact Hv|exact Hsh].
Qed.
Theorem persistent_residuals c :
  residual_shuffle_closed (protocol persistent_family c).
Proof.
  intros p u v w Hu Hv Hsh. apply persistent_accept_spec.
  eapply machine_language_residual_shuffle_closed;
    [apply persistent_accept_spec; exact Hu|
     apply persistent_accept_spec; exact Hv|exact Hsh].
Qed.
Theorem persistent_copying_certified mode : copying_certified persistent_family mode.
Proof. split; [apply persistent_certified|]. intros c _. apply persistent_residuals. Qed.
Theorem persistent_pumping default c u v :
  protocol persistent_family c u -> @pumping.pumping A default u v ->
  protocol persistent_family c v.
Proof.
  intros Hu Hp. apply persistent_accept_spec.
  eapply machine_language_pumping; [apply persistent_accept_spec; exact Hu|exact Hp].
Qed.
Lemma persistent_run_subsequence u v : trace_subsequence u v ->
  forall s t su tv, mm_le M s t ->
  machine_run M s u su -> machine_run M t v tv -> mm_le M su tv.
Proof.
  intros Hsub. induction Hsub; intros s t su tv Hle Hu Hv.
  - inversion Hu; inversion Hv; subst. exact Hle.
  - inversion Hu as [|? ? ? ? Henu Hru]; subst.
    inversion Hv as [|? ? ? ? Henv Hrv]; subst.
    eapply IHHsub; [eapply mm_step_mono; eauto|exact Hru|exact Hrv].
  - inversion Hv as [|? ? ? ? Henv Hrv]; subst.
    eapply IHHsub; [|exact Hu|exact Hrv].
    eapply mm_trans; [exact Hle|eapply mm_step_inflationary; exact Henv].
Qed.
Theorem persistent_completion_stable c :
  completion_stable (protocol persistent_family c).
Proof.
  intros u v Hsub Hu [rest Hv].
  apply persistent_accept_spec in Hu. apply persistent_accept_spec in Hv.
  destruct Hu as [su [Hru Hau]]. destruct Hv as [z [Hrv Haz]].
  destruct (@machine_run_app_inv A S M initial v rest z Hrv) as [tv [Hprefix Htail]].
  apply persistent_accept_spec. exists tv. split; [exact Hprefix|].
  eapply mm_accept_up; [|exact Hau].
  eapply persistent_run_subsequence; [exact Hsub|apply mm_refl|exact Hru|exact Hprefix].
Qed.
Theorem persistent_accumulation_contract c :
  accumulation_contract (protocol persistent_family c).
Proof.
  split; [|apply persistent_completion_stable].
  apply residual_prefix_shuffle_closed_subsequence_safe_extension.
  apply residual_shuffle_closed_prefix. apply persistent_residuals.
Qed.
Theorem persistent_kellogg c :
  kellogg_error_closed (prefix_language (protocol persistent_family c)).
Proof. apply residual_shuffle_closed_kellogg_error_closed. apply persistent_residuals. Qed.
Theorem persistent_checked_prefix FT mode s m :
  check_program_with_copy persistent_family FT mode s = true ->
  program_prefix s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
    prefix_language (protocol persistent_family (classes m l)) (object_history m l).
Proof. eapply copying_program_prefix_sound. apply persistent_copying_certified. Qed.
Theorem persistent_checked_completion FT mode s m :
  check_program_with_copy persistent_family FT mode s = true ->
  program_execution s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
    protocol persistent_family (classes m l) (object_history m l).
Proof. eapply copying_program_completion_sound. apply persistent_copying_certified. Qed.
End Queries.
