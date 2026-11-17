From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import regexp.
From Accumulation Require Import pumping certification regular_protocols regular_soundness
  trace_languages protocols syntax typestate examples coverage_simulation.

Local Notation B := (Finite.clone bool _).

(* false and true are two distinct events, conventionally a and b. *)
Example empty_seed_language_certified : @certify_regex B Void = true.
Proof. vm_compute; reflexivity. Qed.
Example epsilon_seed_certified : @certify_regex B Eps = true.
Proof. vm_compute; reflexivity. Qed.
Example ordered_seed_certified : @certify_seeds B [:: [:: false;true]] = true.
Proof. vm_compute; reflexivity. Qed.
Example repeated_seed_certified : @certify_seeds B [:: [:: false;false]] = true.
Proof. vm_compute; reflexivity. Qed.
Example repeated_seed_needs_two_occurrences : @coverb B [:: false;false] [:: false] = false.
Proof. vm_compute; reflexivity. Qed.
Example canonical_shortcut_counterexample :
  @certify_seeds B [:: [:: false;true]; [:: true;true;false]] = false.
Proof. vm_compute; reflexivity. Qed.
Example stated_uncovered_shuffle :
  @coveredb B [:: [:: false;true]; [:: true;true;false]] [::true;false;true;false;true] = false.
Proof. vm_compute; reflexivity. Qed.
Example actual_rejection_has_witness :
  match @counterexample B [:: [:: false;true]; [:: true;true;false]] with
  | Some _ => true | None => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example regular_star_seed_certified : @certify_regex B (Star (Atom false)) = true.
Proof.
  rewrite /certify_regex /normalized_seeds /= /bounded_star_basis card_bool.
  rewrite !big_ord_recl big_ord0 /=.
  vm_compute; reflexivity.
Qed.

Definition singleton_spec : nat -> regexp B := fun _ => Atom true.
Example regular_residual_complete : accepts (@regular_family B singleton_spec) 0 [::true;true] = true.
Proof. vm_compute; reflexivity. Qed.
Example regular_residual_incomplete : accepts (@regular_family B singleton_spec) 0 [::] = false.
Proof. vm_compute; reflexivity. Qed.
Example regular_residual_initial_viable : viable (@regular_family B singleton_spec) 0 [::] = true.
Proof. apply viable_spec; exists [:: true]; vm_compute; reflexivity. Qed.
Example regular_residual_dead : viable (@regular_family B singleton_spec) 0 [::false] = false.
Proof.
  apply Bool.not_true_is_false; rewrite viable_spec.
  intros [v H].
  change (coveredb B [::[::true]] (false::v) = true) in H.
  unfold coveredb in H.
  change (coverb B [::true] (false::v) || false = true) in H.
  rewrite /coverb covers_simulation_correct in H; vm_compute in H; discriminate.
Qed.

Definition one_class := @compiled_family B [:: Atom true].
Lemma one_class_viable0 : viable one_class 0 [::] = true.
Proof. apply viable_spec; exists [:: true]; vm_compute; reflexivity. Qed.
Lemma one_class_viable1 : viable one_class 0 [::true] = true.
Proof. apply complete_viable; vm_compute; reflexivity. Qed.
Lemma one_class_viable2 : viable one_class 0 [::true;true] = true.
Proof. apply complete_viable; vm_compute; reflexivity. Qed.
Lemma one_class_complete2 : accepts one_class 0 [::true;true] = true.
Proof. vm_compute; reflexivity. Qed.
Example complete_pipeline : @check_regular_program B [:: Atom true] fields aliases = true.
Proof.
  change (table_certified [:: Atom true] && check_program one_class fields aliases = true).
  change (true && check_program one_class fields aliases = true).
  rewrite andTb.
  unfold check_program, aliases.
  cbn [paths block List.flat_map List.map List.app List.forallb check_trace check_step
       check_bind retirable get put andb Nat.eqb List.app].
  unfold check_bind, retirable; cbn [get andb Nat.eqb List.app].
  rewrite one_class_viable0.
  cbn [check_trace check_step check_bind retirable get put andb Nat.eqb List.app].
  rewrite one_class_viable0.
  cbn [check_trace check_step get put andb Nat.eqb List.app].
  rewrite one_class_viable1.
  cbn [check_trace check_step get put andb Nat.eqb List.app].
  rewrite one_class_viable1.
  cbn [check_trace check_step get put andb Nat.eqb List.app].
  rewrite one_class_viable2.
  cbn [check_trace check_step get put andb Nat.eqb List.app].
  rewrite one_class_complete2.
  cbn [check_trace check_step get put andb Nat.eqb List.app].
  rewrite one_class_viable2.
  cbn [check_trace check_step get put andb Nat.eqb List.app].
  rewrite one_class_complete2.
  reflexivity.
Qed.
