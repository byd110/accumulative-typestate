(* From local binding histories to global object protocols. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import trace_languages protocols syntax semantics typestate invariants.
Import ListNotations.
Set Implicit Arguments.

Section Soundness.
Context {A : Type} (P : protocol_family A) (FT : class -> field -> class).

Definition object_epochs (m : machine A) l :=
  filter (fun e => Nat.eqb (owners m e) l) (seq 0 (next_epoch m)).
Lemma object_epochs_spec m l e : In e (object_epochs m l) <->
  e < next_epoch m /\ owners m e = l.
Proof. unfold object_epochs; rewrite filter_In, in_seq, Nat.eqb_eq; lia. Qed.

Lemma epoch_viable m g e : invariant P FT m g -> e < next_epoch m ->
  prefix_language (protocol P (classes m (owners m e))) (project e (events m)).
Proof.
  intros HI He; apply viable_prefix.
  destruct (liveb (refs m) e) eqn:E.
  - apply liveb_spec in E; destruct E as [x Ex].
    eapply inv_viable; [exact HI|eapply agree_ref; eauto].
  - apply complete_viable. eapply inv_retired; eauto.
    intros x Ex; assert (liveb (refs m) e = true) by (apply liveb_spec; eauto); congruence.
Qed.

Lemma invariant_object_language m g l (K : language A) :
  invariant P FT m g -> l < next_loc m -> shuffle_closed K ->
  (forall e, e < next_epoch m -> owners m e = l -> K (project e (events m))) ->
  K (object_history m l).
Proof.
  intros HI Hl HK HE. unfold object_history.
  eapply (@tagged_shuffle_closed A K (object_epochs m l) (object_events m l)); eauto.
  - apply NoDup_filter, seq_NoDup.
  - destruct (inv_objects HI Hl) as [e [He Ho]].
    assert (In e (object_epochs m l)) by (apply object_epochs_spec; auto).
    intros E; rewrite E in H; contradiction.
  - intros e a Hin. unfold object_events in Hin; apply filter_In in Hin.
    destruct Hin as [Hin Ho]; simpl in Ho; apply Nat.eqb_eq in Ho.
    apply object_epochs_spec; split; auto; eapply inv_events; eauto.
  - intros e Hin; apply object_epochs_spec in Hin; destruct Hin as [He Ho].
    unfold object_events, epoch. rewrite (@project_filter A (fun e => Nat.eqb (owners m e) l) e (events m)).
    + apply HE; auto.
    + rewrite Ho, Nat.eqb_refl; reflexivity.
Qed.

Theorem invariant_prefix_safe m g : certified P -> invariant P FT m g ->
  forall l, l < next_loc m -> prefix_language (protocol P (classes m l)) (object_history m l).
Proof.
  intros HC HI l Hl; eapply invariant_object_language; eauto.
  - apply prefix_shuffle_closed, HC.
  - intros e He Ho; rewrite <- Ho; eapply epoch_viable; eauto.
Qed.

Theorem invariant_complete m g : certified P -> invariant P FT m g ->
  (forall x, get g x = None) ->
  forall l, l < next_loc m -> protocol P (classes m l) (object_history m l).
Proof.
  intros HC HI HG l Hl; eapply invariant_object_language; eauto.
  intros e He Ho; unfold protocol; rewrite <- Ho.
  eapply inv_retired; eauto. intros x Ex.
  pose proof (agree_ref x HI Ex) as E. rewrite HG in E; discriminate.
Qed.

(* Prefixes range over every branch path. The raw semantics has no protocol
   premises; field-initialization safety is deliberately a separate issue. *)
Theorem typestate_prefix_sound s m : certified P -> check_program P FT s = true ->
  program_prefix s initial_machine m ->
  forall l, l < next_loc m -> prefix_language (protocol P (classes m l)) (object_history m l).
Proof.
  intros HC HT [p [q [HP HE]]].
  destruct (check_program_path P FT HT HP) as [g [HG Hempty]].
  destruct (@typed_trace_split A P FT [] p q g HG) as [gm [Hp Hq]].
  eapply invariant_prefix_safe; eauto. eapply trace_preservation; eauto.
  apply invariant_initial.
Qed.

Theorem typestate_completion_sound s m : certified P -> check_program P FT s = true ->
  program_execution s initial_machine m ->
  forall l, l < next_loc m -> protocol P (classes m l) (object_history m l).
Proof.
  intros HC HT [p [HP HE]].
  destruct (check_program_path P FT HT HP) as [g [HG Hempty]].
  eapply invariant_complete; eauto. eapply trace_preservation; eauto.
  apply invariant_initial.
Qed.
End Soundness.
