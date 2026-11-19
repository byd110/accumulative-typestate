(* A sufficient construction for protocols with persistent information.
   This module does not require the event alphabet or state space to be finite. *)
From Coq Require Import List.
From Accumulation Require Import trace_languages copying_typestate.
Import ListNotations.
Set Implicit Arguments.

Record monotone_machine (A S : Type) := {
  mm_le : S -> S -> Prop;
  mm_refl : forall s, mm_le s s;
  mm_trans : forall s t u, mm_le s t -> mm_le t u -> mm_le s u;
  mm_enabled : S -> A -> Prop;
  mm_step : S -> A -> S;
  mm_accept : S -> Prop;
  mm_enabled_up : forall s t a,
    mm_le s t -> mm_enabled s a -> mm_enabled t a;
  mm_step_mono : forall s t a,
    mm_le s t -> mm_enabled s a -> mm_le (mm_step s a) (mm_step t a);
  mm_step_inflationary : forall s a,
    mm_enabled s a -> mm_le s (mm_step s a);
  mm_accept_up : forall s t, mm_le s t -> mm_accept s -> mm_accept t
}.

Inductive machine_run {A S} (M : monotone_machine A S) : S -> list A -> S -> Prop :=
| machine_run_nil s : machine_run M s [] s
| machine_run_cons s a w t :
    mm_enabled M s a -> machine_run M (mm_step M s a) w t ->
    machine_run M s (a :: w) t.

Definition machine_language {A S} (M : monotone_machine A S) (s : S) : language A :=
  fun w => exists t, machine_run M s w t /\ mm_accept M t.

Section MachineLemmas.
Context {A S : Type} (M : monotone_machine A S).

Lemma machine_run_deterministic s w t : machine_run M s w t ->
  forall t', machine_run M s w t' -> t = t'.
Proof.
  intros H; induction H; intros t' H'; inversion H'; subst; eauto.
Qed.

Lemma machine_run_inflationary s w t : machine_run M s w t -> mm_le M s t.
Proof.
  intros H; induction H.
  - apply mm_refl.
  - eapply mm_trans; [eapply mm_step_inflationary; eassumption|exact IHmachine_run].
Qed.

Lemma machine_run_app s u t v z :
  machine_run M s u t -> machine_run M t v z -> machine_run M s (u ++ v) z.
Proof.
  intros H; induction H; simpl; intros Hv; eauto using machine_run.
Qed.

Lemma machine_run_app_inv s u v z : machine_run M s (u ++ v) z ->
  exists t, machine_run M s u t /\ machine_run M t v z.
Proof.
  revert s; induction u as [|a u IH]; intros s H.
  - exists s; split; [constructor|exact H].
  - simpl in H; inversion H as [|? ? ? ? Hen Htail]; subst.
    destruct (IH _ Htail) as [t [Hu Hv]].
    exists t; split; [econstructor; eauto|exact Hv].
Qed.

Lemma machine_run_monotone s w t : machine_run M s w t ->
  forall s', mm_le M s s' ->
  exists t', machine_run M s' w t' /\ mm_le M t t'.
Proof.
  intros H; induction H; intros s' Hle.
  - exists s'; split; [constructor|exact Hle].
  - assert (Hen : mm_enabled M s' a) by (eapply mm_enabled_up; eauto).
    assert (Hstep : mm_le M (mm_step M s a) (mm_step M s' a))
      by (eapply mm_step_mono; eauto).
    destruct (IHmachine_run _ Hstep) as [t' [Hrun Hout]].
    exists t'; split; [econstructor; eauto|exact Hout].
Qed.

Lemma machine_language_monotone s t w :
  mm_le M s t -> machine_language M s w -> machine_language M t w.
Proof.
  intros Hle [z [Hr Ha]].
  destruct (machine_run_monotone Hr t Hle) as [z' [Hr' Hle']].
  exists z'; split; [exact Hr'|eapply mm_accept_up; eauto].
Qed.

(* The combined state dominates both component states throughout a shuffle. *)
Lemma machine_run_shuffle u v w : shuffle u v w ->
  forall s su sv tu tv,
  mm_le M su s -> mm_le M sv s ->
  machine_run M su u tu -> machine_run M sv v tv ->
  exists t, machine_run M s w t /\ mm_le M tu t /\ mm_le M tv t.
Proof.
  intros Hsh; induction Hsh; intros s su sv tu tv Hlu Hlv Hu Hv.
  - inversion Hu; inversion Hv; subst.
    exists s; repeat split; try constructor; assumption.
  - inversion Hu as [|? ? ? ? Henu Hrunu]; subst.
    assert (Hen : mm_enabled M s a) by
      (eapply (@mm_enabled_up A S M su s a); eauto).
    assert (Hlu' : mm_le M (mm_step M su a) (mm_step M s a))
      by (eapply mm_step_mono; eauto).
    assert (Hlv' : mm_le M sv (mm_step M s a)).
    { eapply mm_trans; [exact Hlv|eapply mm_step_inflationary; exact Hen]. }
    destruct (IHHsh _ _ _ _ _ Hlu' Hlv' Hrunu Hv) as [t [Hr [Htu Htv]]].
    exists t; repeat split; eauto using machine_run.
  - inversion Hv as [|? ? ? ? Henv Hrunv]; subst.
    assert (Hen : mm_enabled M s a) by
      (eapply (@mm_enabled_up A S M sv s a); eauto).
    assert (Hlv' : mm_le M (mm_step M sv a) (mm_step M s a))
      by (eapply mm_step_mono; eauto).
    assert (Hlu' : mm_le M su (mm_step M s a)).
    { eapply mm_trans; [exact Hlu|eapply mm_step_inflationary; exact Hen]. }
    destruct (IHHsh _ _ _ _ _ Hlu' Hlv' Hu Hrunv) as [t [Hr [Htu Htv]]].
    exists t; repeat split; eauto using machine_run.
Qed.

Theorem machine_language_shuffle_closed s : shuffle_closed (machine_language M s).
Proof.
  intros u v w [tu [Hu Hau]] [tv [Hv Hav]] Hsh.
  destruct (@machine_run_shuffle u v w Hsh s s s tu tv
    (mm_refl M s) (mm_refl M s) Hu Hv) as [t [Hr [Htu Htv]]].
  exists t; split; [exact Hr|eapply mm_accept_up; eauto].
Qed.

Theorem machine_language_residual_shuffle_closed s :
  residual_shuffle_closed (machine_language M s).
Proof.
  intros p u v w [tu [Hu Hau]] [tv [Hv Hav]] Hsh.
  destruct (@machine_run_app_inv s p u tu Hu) as [q [Hp Hqu]].
  destruct (@machine_run_app_inv s p v tv Hv) as [q' [Hp' Hqv]].
  assert (q = q') by (eapply machine_run_deterministic; eauto).
  subst q'.
  assert (Huw : machine_language M q u) by (exists tu; auto).
  assert (Hvw : machine_language M q v) by (exists tv; auto).
  destruct (@machine_language_shuffle_closed q u v w Huw Hvw Hsh) as [t [Hr Ha]].
  exists t; split; [eapply machine_run_app; eauto|exact Ha].
Qed.

Lemma machine_run_seen_enabled s p t : machine_run M s p t ->
  forall a, In a p -> mm_enabled M t a.
Proof.
  intros Hr; induction Hr; intros b Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst b. eapply mm_enabled_up; [|exact H].
      eapply mm_trans; [eapply mm_step_inflationary; exact H|].
      eapply machine_run_inflationary; exact Hr.
    + exact (IHHr _ Hin).
Qed.

Theorem machine_language_repeat s p a q :
  In a p -> machine_language M s (p ++ q) ->
  machine_language M s (p ++ a :: q).
Proof.
  intros Hin [t [Hr Ha]].
  destruct (@machine_run_app_inv s p q t Hr) as [m [Hp Hq]].
  assert (Hen : mm_enabled M m a) by (eapply machine_run_seen_enabled; eauto).
  assert (Hle : mm_le M m (mm_step M m a)) by (apply mm_step_inflationary; exact Hen).
  destruct (machine_run_monotone Hq (mm_step M m a) Hle) as [t' [Hq' Hout]].
  exists t'; split.
  - eapply machine_run_app; [exact Hp|econstructor; eauto].
  - eapply mm_accept_up; eauto.
Qed.
End MachineLemmas.
