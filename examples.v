(* Regression examples exercise obligations, aliasing, heap aliases and structural sequencing. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import trace_languages protocols syntax semantics typestate invariants soundness.
Import ListNotations.
Set Implicit Arguments.

Definition two_calls_accept (_ : nat) (w : list bool) :=
  forallb (fun b => b) w && (2 <=? length w).
Definition two_calls_viable (_ : nat) (w : list bool) := forallb (fun b => b) w.
Lemma two_calls_queries c w : two_calls_viable c w = true <->
  exists v, two_calls_accept c (w ++ v) = true.
Proof.
  unfold two_calls_viable, two_calls_accept; split.
  - intros H; exists [true;true]. rewrite forallb_app, H. change ((2 <=? length (w ++ [true;true])) = true).
    apply Nat.leb_le; rewrite length_app; simpl; lia.
  - intros [v H]; apply andb_true_iff in H; destruct H as [H _].
    rewrite forallb_app in H; apply andb_true_iff in H; tauto.
Qed.
Definition two_calls : protocol_family bool :=
  {| accepts := two_calls_accept; viable := two_calls_viable; viable_spec := two_calls_queries |}.

Lemma shuffle_length {A} (u v w : list A) : shuffle u v w -> length w = length u + length v.
Proof. intros H; induction H; simpl; lia. Qed.
Lemma shuffle_all_true u v w : shuffle u v w ->
  forallb (fun b => b) u = true -> forallb (fun b => b) v = true -> forallb (fun b => b) w = true.
Proof.
  intros H; induction H; simpl; intros Hu Hv; auto.
  - apply andb_true_iff in Hu; destruct Hu; apply andb_true_iff; split; auto.
  - apply andb_true_iff in Hv; destruct Hv; apply andb_true_iff; split; auto.
Qed.
Lemma two_calls_certified : certified two_calls.
Proof.
  intros c u v w Hu Hv Hs; change (two_calls_accept c u = true) in Hu; change (two_calls_accept c v = true) in Hv; change (two_calls_accept c w = true); unfold two_calls_accept in *.
  apply andb_true_iff in Hu; apply andb_true_iff in Hv.
  destruct Hu as [Hu Hlu]; destruct Hv as [Hv Hlv]; apply andb_true_iff; split.
  - eapply shuffle_all_true; eauto.
  - apply Nat.leb_le; apply Nat.leb_le in Hlu; pose proof (shuffle_length Hs); lia.
Qed.

Definition fields (c : class) (_ : field) := c.
Definition block := @sequence bool.
Definition aliases := block [New 0 0; Copy 1 0; Call 0 true; Call 1 true;
                            Call 0 true; Call 1 true].
Example aliases_accepted : check_program two_calls fields aliases = true.
Proof. vm_compute; reflexivity. Qed.
Example aliases_safe m : program_execution aliases initial_machine m ->
  forall l, l < next_loc m -> protocol two_calls (classes m l) (object_history m l).
Proof. apply typestate_completion_sound with fields; [apply two_calls_certified|apply aliases_accepted]. Qed.

Example incomplete_alias_rejected : check_program two_calls fields
  (block [New 0 0; Copy 1 0; Call 0 true; Call 0 true]) = false.
Proof. vm_compute; reflexivity. Qed.
Example overwrite_incomplete_rejected : check_program two_calls fields
  (block [New 0 0; New 0 0; Call 0 true; Call 0 true]) = false.
Proof. vm_compute; reflexivity. Qed.
Example invalid_event_rejected : check_program two_calls fields
  (block [New 0 0; Call 0 false; Call 0 true]) = false.
Proof. vm_compute; reflexivity. Qed.
Example live_at_exit_accepted : check_program two_calls fields
  (block [New 0 0; Call 0 true; Call 0 true]) = true.
Proof. vm_compute; reflexivity. Qed.
Example retired_rebind_accepted : check_program two_calls fields
  (block [New 0 0; Call 0 true; Call 0 true; Copy 0 0;
          Call 0 true; Call 0 true]) = true.
Proof. vm_compute; reflexivity. Qed.
Example heap_alias_accepted : check_program two_calls fields
  (block [New 0 0; New 1 0; Store 0 0 1; Load 2 0 0;
          Call 0 true; Call 0 true;
          Call 1 true; Call 1 true;
          Call 2 true; Call 2 true]) = true.
Proof. vm_compute; reflexivity. Qed.
Example wrong_field_class_rejected : check_program two_calls fields
  (block [New 0 0; New 1 1; Store 0 0 1]) = false.
Proof. vm_compute; reflexivity. Qed.
(* Explicit executions rule out vacuity of the soundness examples.  The
   protocol excludes false and requires two calls, so neither acceptance nor
   completion is trivial.  These machines are built only by the raw steps. *)
Definition aliases_final : machine bool :=
  let m := allocate initial_machine 0 0 in
  let m := bind m 1 0 in
  let m := emit m 0 true in
  let m := emit m 1 true in
  let m := emit m 0 true in
  let m := emit m 1 true in
  clear_refs m.
Example aliases_terminates : program_execution aliases initial_machine aliases_final.
Proof.
  unfold aliases, block, aliases_final. apply source_execution_instrument; [reflexivity|].
  cbn [sequence]. repeat (eapply execution_seq;
    [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.
Example aliases_object_history : next_loc aliases_final = 1 /\
  object_history aliases_final 0 = [true; true; true; true].
Proof. vm_compute; auto. Qed.

(* Overwriting drops the last reference to location 0, but its completed
   history remains in the theorem's domain after location 1 is allocated. *)
Definition abandoned_object := block
  [New 0 0; Call 0 true; Call 0 true; New 0 0;
   Call 0 true; Call 0 true].
Definition abandoned_object_final : machine bool :=
  let m := allocate initial_machine 0 0 in
  let m := emit m 0 true in
  let m := emit m 0 true in
  let m := allocate m 0 0 in
  let m := emit m 1 true in
  let m := emit m 1 true in
  clear_refs m.
Example abandoned_object_accepted :
  check_program two_calls fields abandoned_object = true.
Proof. vm_compute; reflexivity. Qed.
Example abandoned_object_terminates :
  program_execution abandoned_object initial_machine abandoned_object_final.
Proof.
  unfold abandoned_object, block, abandoned_object_final.
  apply source_execution_instrument; [reflexivity|]. cbn [sequence].
  repeat (eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.
Example abandoned_object_unreachable :
  next_loc abandoned_object_final = 2 /\
  object_history abandoned_object_final 0 = [true; true] /\
  (forall x, reference abandoned_object_final x = None) /\
  (forall l f, heap abandoned_object_final l f = None).
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split.
  - intros [|x]; reflexivity.
  - reflexivity.
Qed.
Example abandoned_object_complete :
  protocol two_calls (classes abandoned_object_final 0)
    (object_history abandoned_object_final 0).
Proof.
  eapply typestate_completion_sound with (FT := fields).
  - apply two_calls_certified.
  - apply abandoned_object_accepted.
  - apply abandoned_object_terminates.
  - simpl; lia.
Qed.

(* The operational semantics permits the very error excluded by checking;
   it does not hide invalid calls behind a protocol-monitor premise. *)
Example raw_invalid_call_executes :
  exists m, program_execution (block [New 0 0; Call 0 false]) initial_machine m /\
    next_loc m = 1 /\
    ~ prefix_language (protocol two_calls (classes m 0)) (object_history m 0).
Proof.
  exists (clear_refs (emit (allocate initial_machine 0 0) 0 false)). split.
  - apply source_execution_instrument; [reflexivity|]. unfold block; cbn [sequence].
    repeat (eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|]); constructor.
  - split; [reflexivity|]. intros H.
    apply viable_prefix in H. discriminate.
Qed.

(* Empty/nested syntax and current-binding completion regressions. *)
Example empty_source_accepted : check_program two_calls fields Skip = true.
Proof. reflexivity. Qed.
Example empty_source_terminates : program_execution (@Skip bool) initial_machine initial_machine.
Proof. change (program_execution (@Skip bool) initial_machine (clear_refs initial_machine)).
  apply source_execution_instrument; [reflexivity|constructor]. Qed.
Example explicit_exit_is_not_source : check_program two_calls fields Finish = false.
Proof. reflexivity. Qed.
Example nested_sequences_accepted : check_program two_calls fields
  (Seq (Seq Skip (New 0 0)) (Seq (Call 0 true) (Seq Skip (Call 0 true)))) = true.
Proof. vm_compute; reflexivity. Qed.
Example nested_sequences_terminate :
  program_execution (Seq (Seq Skip (New 0 0)) (Seq (Call 0 true) (Seq Skip (Call 0 true))))
    initial_machine (clear_refs (emit (emit (allocate initial_machine 0 0) 0 true) 0 true)).
Proof.
  apply source_execution_instrument; [reflexivity|].
  eapply execution_seq.
  - eapply execution_seq; [constructor|apply execution_primitive; constructor].
  - eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|].
    eapply execution_seq; [constructor|apply execution_primitive; econstructor; reflexivity].
Qed.
Example shadowed_incomplete_ignored :
  all_complete two_calls [(0,Some (0,[true;true])); (0,Some (0,[]))] = true.
Proof. reflexivity. Qed.
Example stale_complete_does_not_discharge_live :
  all_complete two_calls [(0,Some (0,[])); (0,Some (0,[true;true]))] = false.
Proof. reflexivity. Qed.

Definition heap_alias_source := block
  [New 0 0; New 1 0; Store 0 0 1; Load 2 0 0;
   Call 0 true; Call 0 true; Call 1 true; Call 1 true; Call 2 true; Call 2 true].
Definition heap_alias_final : machine bool :=
  let m := allocate initial_machine 0 0 in
  let m := allocate m 1 0 in
  let m := store m 0 0 1 in
  let m := bind m 2 1 in
  let m := emit (emit m 0 true) 0 true in
  let m := emit (emit m 1 true) 1 true in
  let m := emit (emit m 2 true) 2 true in clear_refs m.
Example heap_alias_source_accepted : check_program two_calls fields heap_alias_source = true.
Proof. reflexivity. Qed.
Example heap_alias_terminates : program_execution heap_alias_source initial_machine heap_alias_final.
Proof.
  unfold heap_alias_source, heap_alias_final, block.
  apply source_execution_instrument; [reflexivity|]. cbn [sequence].
  repeat (eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.
Example heap_alias_histories : object_history heap_alias_final 0=[true;true] /\
  object_history heap_alias_final 1=[true;true;true;true] /\ heap heap_alias_final 0 0=Some 1.
Proof. reflexivity || (repeat split; reflexivity). Qed.
Example left_sequence_exposes_remainder :
  raw_step (initial_machine, Seq (New 0 0) (Call 0 true))
    (allocate initial_machine 0 0, Seq Skip (Call 0 true)).
Proof. apply step_seq, step_primitive, run_new. Qed.
Example left_sequence_skip_eliminates :
  raw_step (allocate initial_machine 0 0, Seq Skip (Call 0 true))
    (allocate initial_machine 0 0, Call 0 true).
Proof. apply step_skip. Qed.
