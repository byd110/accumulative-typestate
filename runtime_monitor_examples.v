(* Nonvacuous monitor regressions: explicit failures, unreachable objects,
   individual retirement, and successful baseline/copying executions. *)
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

Example empty_protocol_allocation_errors :
  monitored_program empty_runtime_protocol (Do (New 0 0))
    initial_machine ProtocolError.
Proof.
  eapply monitor_program_step_error with (p := [New 0 0]).
  - constructor.
  - apply monitor_trace_error.
    eapply monitor_step_error; [constructor|reflexivity].
Qed.

Example invalid_call_monitor_errors :
  monitored_program two_calls (block [New 0 0; Call 0 false])
    initial_machine ProtocolError.
Proof.
  eapply monitor_program_step_error with (p := [New 0 0; Call 0 false]).
  - apply block_path.
  - eapply monitor_trace_cons.
    + eapply monitor_step_ok; [constructor|reflexivity].
    + apply monitor_trace_error.
      eapply monitor_step_error; [econstructor; reflexivity|reflexivity].
Qed.

Definition incomplete_retired_machine : machine bool :=
  retire (allocate initial_machine 0 0) 0.

Example incomplete_retirement_trace_succeeds :
  monitored_trace two_calls [New 0 0; Finish 0] initial_machine
    (RuntimeState incomplete_retired_machine).
Proof.
  unfold incomplete_retired_machine.
  repeat (eapply monitor_trace_cons;
    [eapply monitor_step_ok; [econstructor; reflexivity|reflexivity]|]); constructor.
Qed.

Example incomplete_retired_object_unreachable :
  next_loc incomplete_retired_machine = 1 /\
  object_history incomplete_retired_machine 0 = [] /\
  (forall x, reference incomplete_retired_machine x = None) /\
  (forall l f, heap incomplete_retired_machine l f = None).
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split.
  - intros [|x]; reflexivity.
  - reflexivity.
Qed.

Example incomplete_retired_object_exit_rejected :
  runtime_exit_check two_calls incomplete_retired_machine = false.
Proof. reflexivity. Qed.

Example incomplete_retired_object_program_errors :
  monitored_program two_calls (block [New 0 0; Finish 0])
    initial_machine ProtocolError.
Proof.
  eapply monitor_program_exit_error with
    (p := [New 0 0; Finish 0]) (m' := incomplete_retired_machine).
  - apply block_path.
  - apply incomplete_retirement_trace_succeeds.
  - apply incomplete_retired_object_exit_rejected.
Qed.

(* Finishing object 0 does not demand completion of object 1. The remaining
   calls complete object 1 before the sole aggregate program-exit check. *)
Definition staggered_retirement := block
  [New 0 0; New 1 0; Call 0 true; Call 0 true; Finish 0;
   Call 1 true; Call 1 true; Finish 1].
Definition staggered_before_finish : machine bool :=
  let m := allocate initial_machine 0 0 in
  let m := allocate m 1 0 in
  let m := emit m 0 true in
  emit m 0 true.
Definition staggered_after_finish : machine bool :=
  retire staggered_before_finish 0.
Definition staggered_final : machine bool :=
  let m := emit staggered_after_finish 1 true in
  let m := emit m 1 true in
  retire m 1.

Example staggered_retirement_accepted :
  check_program two_calls fields staggered_retirement = true.
Proof. vm_compute; reflexivity. Qed.

Example individual_finish_allows_other_incomplete_object :
  monitored_step two_calls (Finish 0) staggered_before_finish
    (RuntimeState staggered_after_finish) /\
  object_history staggered_after_finish 1 = [] /\
  runtime_exit_check two_calls staggered_after_finish = false.
Proof.
  split.
  - eapply monitor_step_ok; [econstructor; reflexivity|reflexivity].
  - split; reflexivity.
Qed.

Example staggered_retirement_terminates :
  program_execution staggered_retirement initial_machine staggered_final.
Proof.
  apply block_execution.
  unfold staggered_final, staggered_after_finish, staggered_before_finish.
  repeat (eapply execution_cons; [econstructor; reflexivity|]); constructor.
Qed.

Example staggered_retirement_monitor_succeeds :
  monitored_program two_calls staggered_retirement initial_machine
    (RuntimeState staggered_final).
Proof.
  apply (proj2 (baseline_runtime_equivalence fields staggered_retirement
    two_calls_certified staggered_retirement_accepted staggered_final)).
  apply staggered_retirement_terminates.
Qed.

Example aliases_monitor_succeeds :
  monitored_program two_calls aliases initial_machine (RuntimeState aliases_final).
Proof.
  apply (proj2 (baseline_runtime_equivalence fields aliases
    two_calls_certified aliases_accepted aliases_final)).
  apply aliases_terminates.
Qed.

Example abandoned_object_monitor_succeeds :
  monitored_program two_calls abandoned_object initial_machine
    (RuntimeState abandoned_object_final).
Proof.
  apply (proj2 (baseline_runtime_equivalence fields abandoned_object
    two_calls_certified abandoned_object_accepted abandoned_object_final)).
  apply abandoned_object_terminates.
Qed.

Example inherited_progress_monitor_succeeds :
  monitored_program two_calls inherited_progress initial_machine
    (RuntimeState inherited_progress_final).
Proof.
  apply (proj2 (copying_runtime_equivalence fields inherited_progress
    (two_calls_copying_certified copy_all) inherited_progress_accepted
    inherited_progress_final)).
  apply inherited_progress_terminates.
Qed.
