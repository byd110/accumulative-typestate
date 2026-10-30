(* Optional residual certification composed with the regular-seed compiler. *)
From Coq Require Import List Bool Lia.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import regexp.
From Accumulation Require Import pumping certification regular_protocols regular_soundness
  protocols trace_languages syntax semantics copying_typestate copying_soundness residual_certification.
Set Implicit Arguments.

Section CopyingRegularSoundness.
Variable A : finType.
Variable default : A.
Variable specifications : list (regexp A).
Variable copying_flags : list bool.
Variable FT : class -> field -> class.
Definition requested_copying c := List.nth c copying_flags false.
Definition copying_table_certified :=
  table_certified specifications &&
  List.forallb (fun c => if requested_copying c
    then certify_copying_regex (class_seed specifications c) else true)
    (List.seq 0 (List.length copying_flags)).
Definition check_regular_program_with_copy s := copying_table_certified &&
  check_program_with_copy (compiled_family specifications) FT requested_copying s.

Lemma copying_table_sound : copying_table_certified = true ->
  copying_certified (compiled_family specifications) requested_copying.
Proof.
  unfold copying_table_certified. rewrite Bool.andb_true_iff. intros [HB HC]. split.
  - exact (compiled_family_certified default HB).
  - intros c HM. apply certify_copying_regex_spec.
    apply List.forallb_forall with (x := c) in HC.
    + by rewrite HM in HC.
    + apply List.in_seq. split. lia.
      destruct (Compare_dec.lt_dec c (List.length copying_flags)) as [Hlt|Hge]. exact Hlt.
      unfold requested_copying in HM.
      rewrite List.nth_overflow in HM. discriminate. lia.
Qed.
Theorem copying_regular_program_prefix_sound s m : check_regular_program_with_copy s = true ->
  program_prefix s initial_machine m -> forall l, (l < next_loc m)%coq_nat ->
  exists suffix, @pumping_closure A default (regex_lang A (class_seed specifications (classes m l)))
    (object_history m l ++ suffix).
Proof.
  unfold check_regular_program_with_copy. rewrite Bool.andb_true_iff.
  intros [HC HS] HE l Hl.
  pose proof (copying_program_prefix_sound FT (copying_table_sound HC) HS HE Hl) as H.
  destruct H as [v Hv]. exists v. now apply (regular_family_language default) in Hv.
Qed.
Theorem copying_regular_program_completion_sound s m : check_regular_program_with_copy s = true ->
  program_execution s initial_machine m -> forall l, (l < next_loc m)%coq_nat ->
  @pumping_closure A default (regex_lang A (class_seed specifications (classes m l))) (object_history m l).
Proof.
  unfold check_regular_program_with_copy. rewrite Bool.andb_true_iff.
  intros [HC HS] HE l Hl. apply (regular_family_language default).
  eapply copying_program_completion_sound. exact (copying_table_sound HC). exact HS. exact HE. exact Hl.
Qed.
End CopyingRegularSoundness.
