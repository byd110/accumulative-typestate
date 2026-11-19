(* Explicit checked reductions: allocation/call/exit failures, unreachable
   incomplete objects, stopped continuations, and successful bulk completion. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import trace_languages protocols syntax semantics
  typestate copying_typestate examples copying_examples runtime_monitor.
Import ListNotations.
Set Implicit Arguments.

Definition empty_runtime_protocol : protocol_family bool.
Proof.
  refine {| accepts := fun _ _ => false; viable := fun _ _ => false |}.
  intros c u; split; [discriminate|]. intros [v H]; discriminate.
Defined.

Lemma source_monitor_error {A} (P : protocol_family A) s m :
  finish_free s -> monitored_execution P (RuntimeState (m,s)) ProtocolError ->
  monitored_program P s m ProtocolError.
Proof.
  intros HF HE; split; [split; [exact HF|]|exact I].
  exact (monitored_execution_context (SeqLeft Hole Finish) HE).
Qed.
Lemma source_monitor_incomplete_exit {A} (P : protocol_family A) s m m' :
  finish_free s -> monitored_execution P (RuntimeState (m,s)) (RuntimeState (m',Skip)) ->
  runtime_exit_check P m'=false -> monitored_program P s m ProtocolError.
Proof.
  intros HF HE HG; split; [split; [exact HF|]|exact I].
  eapply monitored_execution_trans.
  - exact (monitored_execution_context (SeqLeft Hole Finish) HE).
  - eapply monitor_exec_step; [apply monitor_step_skip|].
    apply monitor_exec_error. eapply monitor_step_error; [constructor|exact HG].
Qed.

Example empty_protocol_allocation_errors :
  monitored_program empty_runtime_protocol (New 0 0) initial_machine ProtocolError.
Proof.
  apply source_monitor_error; [reflexivity|].
  apply monitor_exec_error; eapply monitor_step_error; [constructor|reflexivity].
Qed.
Example invalid_call_monitor_errors :
  monitored_program two_calls (block [New 0 0; Call 0 false]) initial_machine ProtocolError.
Proof.
  apply source_monitor_error; [reflexivity|]. unfold block; cbn [sequence].
  eapply monitor_exec_step.
  - apply monitor_step_seq; eapply monitor_step_ok; [constructor|reflexivity].
  - eapply monitor_exec_step; [apply monitor_step_skip|].
    apply monitor_exec_error, monitor_step_seq_error.
    eapply monitor_step_error; [econstructor; reflexivity|reflexivity].
Qed.
Example incomplete_bulk_exit_errors :
  monitored_program two_calls (New 0 0) initial_machine ProtocolError.
Proof.
  apply source_monitor_incomplete_exit with (m' := allocate initial_machine 0 0).
  - reflexivity.
  - apply monitored_execution_primitive; [constructor|reflexivity].
  - reflexivity.
Qed.
Example empty_protocol_empty_source_succeeds :
  monitored_program empty_runtime_protocol Skip initial_machine
    (RuntimeState (initial_machine,Skip)).
Proof.
  split; [split; [reflexivity|]|reflexivity]. unfold instrument.
  eapply monitor_exec_step; [apply monitor_step_skip|].
  change (monitored_execution empty_runtime_protocol (RuntimeState (initial_machine,Finish))
    (RuntimeState (clear_refs initial_machine,Skip))).
  apply monitored_execution_primitive; [constructor|reflexivity].
Qed.

(* The first object loses its last reference at overwrite. Its history remains
   in the domain of the sole bulk guard, even when the replacement is complete. *)
Definition unreachable_incomplete_source := block
  [New 0 0; New 0 0; Call 0 true; Call 0 true].
Definition unreachable_incomplete_machine : machine bool :=
  let m := allocate (allocate initial_machine 0 0) 0 0 in
  emit (emit m 1 true) 1 true.
Example unreachable_incomplete_static_rejection :
  check_program two_calls fields unreachable_incomplete_source = false.
Proof. reflexivity. Qed.
Example unreachable_incomplete_source_runs :
  monitored_execution two_calls (RuntimeState (initial_machine,unreachable_incomplete_source))
    (RuntimeState (unreachable_incomplete_machine,Skip)).
Proof.
  unfold unreachable_incomplete_source, unreachable_incomplete_machine, block.
  cbn [sequence]. repeat (eapply monitored_execution_seq;
    [apply monitored_execution_primitive; [econstructor; reflexivity|reflexivity]|]); constructor.
Qed.
Example unreachable_incomplete_object :
  next_loc unreachable_incomplete_machine=2 /\
  object_history unreachable_incomplete_machine 0=[] /\
  object_history unreachable_incomplete_machine 1=[true;true] /\
  (forall x, reference unreachable_incomplete_machine x <> Some 0) /\
  (forall l f, heap unreachable_incomplete_machine l f=None).
Proof.
  repeat split; try reflexivity.
  intros [|x]; discriminate.
Qed.
Example unreachable_incomplete_bulk_exit_rejected :
  runtime_exit_check two_calls unreachable_incomplete_machine=false.
Proof. reflexivity. Qed.
Example unreachable_incomplete_program_errors :
  monitored_program two_calls unreachable_incomplete_source initial_machine ProtocolError.
Proof.
  eapply source_monitor_incomplete_exit; [reflexivity|apply unreachable_incomplete_source_runs|reflexivity].
Qed.

Example left_context_propagates_error :
  monitored_step empty_runtime_protocol
    (initial_machine,Seq (Seq (New 0 0) (New 1 0)) (New 2 0)) ProtocolError.
Proof.
  repeat apply monitor_step_seq_error.
  eapply monitor_step_error; [constructor|reflexivity].
Qed.
Example error_cannot_execute_continuation m s :
  ~ monitored_execution empty_runtime_protocol ProtocolError (RuntimeState (m,s)).
Proof. intros H; apply monitored_error_terminal in H; discriminate. Qed.
Example missing_reference_is_not_protocol_error :
  ~ monitored_step two_calls (initial_machine,Call 0 true) ProtocolError.
Proof.
  intros H; inversion H; subst.
  match goal with HP : primitive_step _ _ _ |- _ => inversion HP; subst end.
  discriminate.
Qed.

(* One binding may complete while another continues. No exit operation occurs
   between those calls; the final bulk exit discharges both together. *)
Definition staggered_completion := block
  [New 0 0; New 1 0; Call 0 true; Call 0 true; Call 1 true; Call 1 true].
Definition staggered_midpoint : machine bool :=
  let m := allocate (allocate initial_machine 0 0) 1 0 in
  emit (emit m 0 true) 0 true.
Definition staggered_final : machine bool :=
  clear_refs (emit (emit staggered_midpoint 1 true) 1 true).
Example staggered_completion_accepted : check_program two_calls fields staggered_completion=true.
Proof. reflexivity. Qed.
Example completed_binding_allows_other_to_continue :
  object_history staggered_midpoint 0=[true;true] /\
  object_history staggered_midpoint 1=[] /\
  runtime_exit_check two_calls staggered_midpoint=false /\
  monitored_step two_calls (staggered_midpoint,Call 1 true)
    (RuntimeState (emit staggered_midpoint 1 true,Skip)).
Proof.
  repeat split; try reflexivity.
  eapply monitor_step_ok; [econstructor; reflexivity|reflexivity].
Qed.
Example staggered_completion_terminates :
  program_execution staggered_completion initial_machine staggered_final.
Proof.
  unfold staggered_completion, block, staggered_final, staggered_midpoint.
  apply source_execution_instrument; [reflexivity|]. cbn [sequence].
  repeat (eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.
Example staggered_completion_monitor_succeeds :
  monitored_program two_calls staggered_completion initial_machine (RuntimeState (staggered_final,Skip)).
Proof.
  apply (proj2 (baseline_runtime_equivalence fields staggered_completion
    two_calls_certified staggered_completion_accepted staggered_final)).
  apply staggered_completion_terminates.
Qed.
Example aliases_monitor_succeeds :
  monitored_program two_calls aliases initial_machine (RuntimeState (aliases_final,Skip)).
Proof.
  apply (proj2 (baseline_runtime_equivalence fields aliases
    two_calls_certified aliases_accepted aliases_final)).
  apply aliases_terminates.
Qed.
Example abandoned_object_monitor_succeeds :
  monitored_program two_calls abandoned_object initial_machine
    (RuntimeState (abandoned_object_final,Skip)).
Proof.
  apply (proj2 (baseline_runtime_equivalence fields abandoned_object
    two_calls_certified abandoned_object_accepted abandoned_object_final)).
  apply abandoned_object_terminates.
Qed.
Example inherited_progress_monitor_succeeds :
  monitored_program two_calls inherited_progress initial_machine
    (RuntimeState (inherited_progress_final,Skip)).
Proof.
  apply (proj2 (copying_runtime_equivalence fields inherited_progress
    (two_calls_copying_certified copy_all) inherited_progress_accepted inherited_progress_final)).
  apply inherited_progress_terminates.
Qed.
Example heap_alias_monitor_succeeds :
  monitored_program two_calls heap_alias_source initial_machine (RuntimeState (heap_alias_final,Skip)).
Proof.
  apply (proj2 (baseline_runtime_equivalence fields heap_alias_source
    two_calls_certified heap_alias_source_accepted heap_alias_final)).
  apply heap_alias_terminates.
Qed.
