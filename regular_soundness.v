(* End-to-end theorem: certified regular seeds and accepted clients. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import regexp.
From Accumulation Require Import pumping certification regular_protocols protocols
  trace_languages syntax semantics typestate soundness.
Set Implicit Arguments.

Section RegularSoundness.
Variable A : finType.
Variable default : A.
Variable specifications : list (regexp A).
Variable FT : class -> field -> class.
Definition class_seed c := List.nth c specifications (@Void A).
Definition table_certified := List.forallb (@certify_regex A) specifications.
Definition compiled_family := regular_family class_seed.

Lemma table_certified_spec : table_certified = true ->
  forall c, certify_regex (class_seed c) = true.
Proof.
  unfold table_certified, class_seed.
  induction specifications as [|r rs IH]; intros H c; destruct c; simpl in *; auto.
  - apply andb_true_iff in H; tauto.
  - apply andb_true_iff in H; destruct H; now apply IH.
Qed.
Lemma compiled_family_certified : table_certified = true -> certified compiled_family.
Proof. intros H; apply (regular_family_certified default); now apply table_certified_spec. Qed.
Definition check_regular_program s := table_certified && check_program compiled_family FT s.

Theorem regular_program_prefix_sound s m : check_regular_program s = true ->
  program_prefix s initial_machine m -> forall l, (l < next_loc m)%coq_nat ->
  exists suffix, @pumping_closure A default (regex_lang A (class_seed (classes m l)))
    (object_history m l ++ suffix).
Proof.
  unfold check_regular_program; rewrite Bool.andb_true_iff.
  intros [HC HS] HE l Hl.
  pose proof (typestate_prefix_sound FT (compiled_family_certified HC) HS HE Hl) as H.
  destruct H as [v Hv]; exists v; now apply (regular_family_language default) in Hv.
Qed.

Theorem regular_program_completion_sound s m : check_regular_program s = true ->
  program_execution s initial_machine m -> forall l, (l < next_loc m)%coq_nat ->
  @pumping_closure A default (regex_lang A (class_seed (classes m l))) (object_history m l).
Proof.
  unfold check_regular_program; rewrite Bool.andb_true_iff.
  intros [HC HS] HE l Hl.
  apply (regular_family_language default).
  eapply typestate_completion_sound; eauto using compiled_family_certified.
Qed.
End RegularSoundness.
