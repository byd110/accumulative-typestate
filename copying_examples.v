(* Copying regressions include sharing, retirement, heap loads and path checks. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import trace_languages protocols syntax semantics typestate examples
  copying_typestate copying_soundness.
Import ListNotations.

Lemma two_calls_residuals c : residual_shuffle_closed (protocol two_calls c).
Proof.
  intros p u v w Hu Hv Hs.
  change (two_calls_accept c (p ++ u) = true) in Hu.
  change (two_calls_accept c (p ++ v) = true) in Hv.
  change (two_calls_accept c (p ++ w) = true).
  unfold two_calls_accept in Hu, Hv |- *.
  apply andb_true_iff in Hu. destruct Hu as [Hpu Hlen].
  apply andb_true_iff in Hv. destruct Hv as [Hpv _].
  rewrite forallb_app in Hpu, Hpv. apply andb_true_iff in Hpu. apply andb_true_iff in Hpv.
  destruct Hpu as [Hp Hu]. destruct Hpv as [_ Hv].
  apply andb_true_iff. split.
  - rewrite forallb_app, Hp. simpl. eapply shuffle_all_true. exact Hs. exact Hu. exact Hv.
  - apply Nat.leb_le. apply Nat.leb_le in Hlen.
    rewrite length_app in *. pose proof (shuffle_length Hs). lia.
Qed.
Lemma two_calls_copying_certified mode : copying_certified two_calls mode.
Proof. split. exact two_calls_certified. intros c _. apply two_calls_residuals. Qed.
Definition copy_all (_ : class) := true.
Definition inherited_progress := block
  [New 0 0; Call 0 true; Copy 1 0; Call 0 true; Call 1 true; Finish 0; Finish 1].
Example inherited_progress_accepted :
  check_program_with_copy two_calls fields copy_all inherited_progress = true.
Proof. vm_compute. reflexivity. Qed.
Example inherited_progress_needs_copying : check_program two_calls fields inherited_progress = false.
Proof. vm_compute. reflexivity. Qed.
Example inherited_progress_sound m : program_execution inherited_progress initial_machine m ->
  forall l, l < next_loc m -> protocol two_calls (classes m l) (object_history m l).
Proof.
  eapply copying_program_completion_sound.
  apply two_calls_copying_certified. exact inherited_progress_accepted.
Qed.
Example nested_copies_accepted : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Copy 1 0; Copy 2 1;
          Call 0 true; Call 1 true; Call 2 true; Finish 0; Finish 1; Finish 2]) = true.
Proof. vm_compute. reflexivity. Qed.
Example completed_history_can_be_shared : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Call 0 true; Copy 1 0; Finish 0; Finish 1]) = true.
Proof. vm_compute. reflexivity. Qed.
Example incomplete_source_obligation_remains : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Copy 1 0; Call 1 true; Finish 0; Finish 1]) = false.
Proof. vm_compute. reflexivity. Qed.
Example overwriting_incomplete_target_rejected : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Call 0 true; New 1 0; Copy 1 0; Finish 0; Finish 1]) = false.
Proof. vm_compute. reflexivity. Qed.
Example same_object_overwrite_accepted : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Copy 1 0; Call 1 true; Copy 1 0;
          Call 0 true; Call 1 true; Finish 0; Finish 1]) = true.
Proof. vm_compute. reflexivity. Qed.
Example retirement_does_not_invalidate_other_alias : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Copy 1 0; Call 0 true; Finish 0; Call 1 true; Finish 1]) = true.
Proof. vm_compute. reflexivity. Qed.
Example field_load_still_starts_fresh : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Call 0 true; Store 0 0 0; Load 1 0 0; Finish 0; Finish 1]) = false.
Proof. vm_compute. reflexivity. Qed.
Example both_modes_in_one_program : check_program_with_copy two_calls fields (Nat.eqb 0)
  (block [New 0 0; Call 0 true; Call 0 true; Copy 1 0; Finish 0; Finish 1;
          New 2 1; Call 2 true; Copy 3 2; Call 2 true; Call 3 true; Call 3 true; Finish 2; Finish 3]) = true.
Proof. vm_compute. reflexivity. Qed.
Example unselected_class_does_not_inherit : check_program_with_copy two_calls fields (Nat.eqb 0)
  (block [New 0 1; Call 0 true; Copy 1 0; Call 0 true; Call 1 true; Finish 0; Finish 1]) = false.
Proof. vm_compute. reflexivity. Qed.
Example incomplete_copy_branch_rejected : check_program_with_copy two_calls fields copy_all
  (Seq (Do (New 0 0)) (Seq (Do (Call 0 true)) (Seq (Do (Copy 1 0))
    (Branch (block [Call 0 true; Call 1 true; Finish 0; Finish 1])
            (block [Call 1 true; Finish 0; Finish 1]))))) = false.
Proof. vm_compute. reflexivity. Qed.
