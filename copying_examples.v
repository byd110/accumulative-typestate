(* Copying regressions include sharing, bulk completion, and fresh heap loads. *)
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
  [New 0 0; Call 0 true; Copy 1 0; Call 0 true; Call 1 true].
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

(* Both views finish at [true; true], whereas the actual shared history has
   three events.  Inherited evidence is not a second operational event. *)
Definition inherited_progress_final : machine bool :=
  let m := allocate initial_machine 0 0 in
  let m := emit m 0 true in
  let m := bind m 1 0 in
  let m := emit m 0 true in
  let m := emit m 1 true in
  clear_refs m.
Example inherited_progress_terminates :
  program_execution inherited_progress initial_machine inherited_progress_final.
Proof.
  unfold inherited_progress_final. apply source_execution_instrument.
  - reflexivity.
  - unfold inherited_progress, block. simpl.
    repeat (eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.
Example inherited_progress_object_history :
  next_loc inherited_progress_final = 1 /\
  object_history inherited_progress_final 0 = [true; true; true].
Proof. vm_compute; auto. Qed.
Example nested_copies_accepted : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Copy 1 0; Copy 2 1;
          Call 0 true; Call 1 true; Call 2 true]) = true.
Proof. vm_compute. reflexivity. Qed.
Example completed_history_can_be_shared : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Call 0 true; Copy 1 0]) = true.
Proof. vm_compute. reflexivity. Qed.
Example incomplete_source_obligation_remains : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Copy 1 0; Call 1 true]) = false.
Proof. vm_compute. reflexivity. Qed.
Example overwriting_incomplete_target_rejected : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Call 0 true; New 1 0; Copy 1 0]) = false.
Proof. vm_compute. reflexivity. Qed.
Example same_object_overwrite_accepted : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Copy 1 0; Call 1 true; Copy 1 0;
          Call 0 true; Call 1 true]) = true.
Proof. vm_compute. reflexivity. Qed.
Example completed_binding_does_not_invalidate_other_alias : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Copy 1 0; Call 0 true; Call 1 true]) = true.
Proof. vm_compute. reflexivity. Qed.
Example field_load_still_starts_fresh : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Call 0 true; Store 0 0 0; Load 1 0 0]) = false.
Proof. vm_compute. reflexivity. Qed.
Example both_modes_in_one_program : check_program_with_copy two_calls fields (Nat.eqb 0)
  (block [New 0 0; Call 0 true; Call 0 true; Copy 1 0;
          New 2 1; Call 2 true; Copy 3 2; Call 2 true; Call 3 true; Call 3 true]) = true.
Proof. vm_compute. reflexivity. Qed.
Example unselected_class_does_not_inherit : check_program_with_copy two_calls fields (Nat.eqb 0)
  (block [New 0 1; Call 0 true; Copy 1 0; Call 0 true; Call 1 true]) = false.
Proof. vm_compute. reflexivity. Qed.
Example incomplete_self_assignment_rejected : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Copy 0 0; Call 0 true]) = false.
Proof. vm_compute. reflexivity. Qed.
Example completed_self_assignment_accepted : check_program_with_copy two_calls fields copy_all
  (block [New 0 0; Call 0 true; Call 0 true; Copy 0 0]) = true.
Proof. vm_compute. reflexivity. Qed.
Example copying_empty_source_accepted :
  check_program_with_copy two_calls fields copy_all Skip = true.
Proof. vm_compute. reflexivity. Qed.
Example copying_source_finish_rejected :
  check_program_with_copy two_calls fields copy_all Finish = false.
Proof. vm_compute. reflexivity. Qed.

(* Constructive runs for nested/mixed inheritance, rebinding, and self-copy. *)
Definition nested_copies_source := block
  [New 0 0; Call 0 true; Copy 1 0; Copy 2 1;
   Call 0 true; Call 1 true; Call 2 true].
Definition nested_copies_final : machine bool :=
  let m := allocate initial_machine 0 0 in
  let m := emit m 0 true in
  let m := bind m 1 0 in let m := bind m 2 0 in
  clear_refs (emit (emit (emit m 0 true) 1 true) 2 true).
Example nested_copies_constructive :
  check_program_with_copy two_calls fields copy_all nested_copies_source=true /\
  program_execution nested_copies_source initial_machine nested_copies_final /\
  object_history nested_copies_final 0=[true;true;true;true].
Proof.
  split; [exact nested_copies_accepted|]. split; [|reflexivity].
  unfold nested_copies_final. apply source_execution_instrument; [reflexivity|].
  unfold nested_copies_source, block; cbn [sequence].
  repeat (eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.
Definition mixed_modes_source := block
  [New 0 0; Call 0 true; Call 0 true; Copy 1 0;
   New 2 1; Call 2 true; Copy 3 2; Call 2 true; Call 3 true; Call 3 true].
Definition mixed_modes_final : machine bool :=
  let m := allocate initial_machine 0 0 in
  let m := emit (emit m 0 true) 0 true in let m := bind m 1 0 in
  let m := allocate m 2 1 in let m := emit m 2 true in let m := bind m 3 1 in
  clear_refs (emit (emit (emit m 2 true) 3 true) 3 true).
Example mixed_modes_constructive :
  check_program_with_copy two_calls fields (Nat.eqb 0) mixed_modes_source=true /\
  program_execution mixed_modes_source initial_machine mixed_modes_final /\
  object_history mixed_modes_final 0=[true;true] /\
  object_history mixed_modes_final 1=[true;true;true;true].
Proof.
  split; [exact both_modes_in_one_program|]. split; [|split; reflexivity].
  unfold mixed_modes_final. apply source_execution_instrument; [reflexivity|].
  unfold mixed_modes_source, block; cbn [sequence].
  repeat (eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.
Definition overwrite_copy_source := block
  [New 0 0; Call 0 true; Copy 1 0; Call 1 true; Copy 1 0;
   Call 0 true; Call 1 true].
Definition overwrite_copy_final : machine bool :=
  let m := allocate initial_machine 0 0 in let m := emit m 0 true in
  let m := bind m 1 0 in let m := emit m 1 true in let m := bind m 1 0 in
  clear_refs (emit (emit m 0 true) 2 true).
Example overwrite_copy_constructive :
  check_program_with_copy two_calls fields copy_all overwrite_copy_source=true /\
  program_execution overwrite_copy_source initial_machine overwrite_copy_final /\
  object_history overwrite_copy_final 0=[true;true;true;true].
Proof.
  split; [exact same_object_overwrite_accepted|]. split; [|reflexivity].
  unfold overwrite_copy_final. apply source_execution_instrument; [reflexivity|].
  unfold overwrite_copy_source, block; cbn [sequence].
  repeat (eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.
Definition self_copy_source := block [New 0 0; Call 0 true; Call 0 true; Copy 0 0].
Definition self_copy_final : machine bool :=
  clear_refs (bind (emit (emit (allocate initial_machine 0 0) 0 true) 0 true) 0 0).
Example self_copy_constructive :
  check_program_with_copy two_calls fields copy_all self_copy_source=true /\
  program_execution self_copy_source initial_machine self_copy_final /\
  object_history self_copy_final 0=[true;true].
Proof.
  split; [exact completed_self_assignment_accepted|]. split; [|reflexivity].
  unfold self_copy_final. apply source_execution_instrument; [reflexivity|].
  unfold self_copy_source, block; cbn [sequence].
  repeat (eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.
