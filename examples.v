(* Regression examples exercise obligations, aliasing, heap aliases and branches. *)
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
Fixpoint block (is : list (instruction bool)) : statement bool :=
  match is with [] => Skip | i::rest => Seq (Do i) (block rest) end.
Lemma block_path is : path (block is) is.
Proof.
  induction is as [|i is IH]; simpl; [constructor|].
  change (path (Seq (Do i) (block is)) ([i] ++ is)).
  constructor; [constructor|exact IH].
Qed.
Lemma block_execution is m m' : execution is m m' ->
  program_execution (block is) m m'.
Proof. intros H; exists is; split; [apply block_path|exact H]. Qed.
Definition aliases := block [New 0 0; Copy 1 0; Call 0 true; Call 1 true;
                            Call 0 true; Finish 0; Call 1 true; Finish 1].
Example aliases_accepted : check_program two_calls fields aliases = true.
Proof. vm_compute; reflexivity. Qed.
Example aliases_safe m : program_execution aliases initial_machine m ->
  forall l, l < next_loc m -> protocol two_calls (classes m l) (object_history m l).
Proof. apply typestate_completion_sound with fields; [apply two_calls_certified|apply aliases_accepted]. Qed.

Example incomplete_alias_rejected : check_program two_calls fields
  (block [New 0 0; Copy 1 0; Call 0 true; Call 0 true; Finish 0; Finish 1]) = false.
Proof. vm_compute; reflexivity. Qed.
Example overwrite_incomplete_rejected : check_program two_calls fields
  (block [New 0 0; New 0 0; Call 0 true; Call 0 true; Finish 0]) = false.
Proof. vm_compute; reflexivity. Qed.
Example invalid_event_rejected : check_program two_calls fields
  (block [New 0 0; Call 0 false; Call 0 true; Finish 0]) = false.
Proof. vm_compute; reflexivity. Qed.
Example live_at_exit_rejected : check_program two_calls fields
  (block [New 0 0; Call 0 true; Call 0 true]) = false.
Proof. vm_compute; reflexivity. Qed.
Example retired_rebind_accepted : check_program two_calls fields
  (block [New 0 0; Call 0 true; Call 0 true; Copy 0 0;
          Call 0 true; Call 0 true; Finish 0]) = true.
Proof. vm_compute; reflexivity. Qed.
Example heap_alias_accepted : check_program two_calls fields
  (block [New 0 0; New 1 0; Store 0 0 1; Load 2 0 0;
          Call 0 true; Call 0 true; Finish 0;
          Call 1 true; Call 1 true; Finish 1;
          Call 2 true; Call 2 true; Finish 2]) = true.
Proof. vm_compute; reflexivity. Qed.
Example wrong_field_class_rejected : check_program two_calls fields
  (block [New 0 0; New 1 1; Store 0 0 1]) = false.
Proof. vm_compute; reflexivity. Qed.
Example incomplete_branch_rejected : check_program two_calls fields
  (Seq (Do (New 0 0)) (Branch
    (block [Call 0 true; Call 0 true; Finish 0])
    (block [Call 0 true; Finish 0]))) = false.
Proof. vm_compute; reflexivity. Qed.
Example completed_branches_accepted : check_program two_calls fields
  (Seq (Do (New 0 0)) (Branch
    (block [Call 0 true; Call 0 true; Finish 0])
    (block [Call 0 true; Call 0 true; Call 0 true; Finish 0]))) = true.
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
  let m := retire m 0 in
  let m := emit m 1 true in
  retire m 1.
Example aliases_terminates : program_execution aliases initial_machine aliases_final.
Proof.
  apply block_execution. unfold aliases_final.
  repeat (eapply execution_cons; [econstructor; reflexivity|]); constructor.
Qed.
Example aliases_object_history : next_loc aliases_final = 1 /\
  object_history aliases_final 0 = [true; true; true; true].
Proof. vm_compute; auto. Qed.

(* Overwriting drops the last reference to location 0, but its completed
   history remains in the theorem's domain after location 1 is allocated. *)
Definition abandoned_object := block
  [New 0 0; Call 0 true; Call 0 true; New 0 0;
   Call 0 true; Call 0 true; Finish 0].
Definition abandoned_object_final : machine bool :=
  let m := allocate initial_machine 0 0 in
  let m := emit m 0 true in
  let m := emit m 0 true in
  let m := allocate m 0 0 in
  let m := emit m 1 true in
  let m := emit m 1 true in
  retire m 0.
Example abandoned_object_accepted :
  check_program two_calls fields abandoned_object = true.
Proof. vm_compute; reflexivity. Qed.
Example abandoned_object_terminates :
  program_execution abandoned_object initial_machine abandoned_object_final.
Proof.
  apply block_execution. unfold abandoned_object_final.
  repeat (eapply execution_cons; [econstructor; reflexivity|]); constructor.
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
  exists (emit (allocate initial_machine 0 0) 0 false). split.
  - apply block_execution.
    eapply execution_cons; [constructor|].
    eapply execution_cons; [econstructor; reflexivity|constructor].
  - split; [reflexivity|]. intros H.
    apply viable_prefix in H. discriminate.
Qed.
