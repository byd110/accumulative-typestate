(* Checked clients and rejection controls for the new manuscript examples. *)
From mathcomp Require Import all_ssreflect.
From Accumulation Require Import trace_languages protocols syntax semantics
  typestate copying_typestate copying_soundness milestone_service_patterns.
Set Implicit Arguments.

Definition persistent_example_fields (_ _ : nat) := 0.
Definition persistent_example_copy (_ : nat) := true.
Local Notation t := (@None bool).
Local Notation i := (Some false).
Local Notation r := (Some true).
Definition milestone_client : statement milestone_alphabet :=
  sequence [::New 0 0; Call 0 t; Call 0 i; Call 0 r].
Example milestone_client_accepted :
  check_program milestone_family persistent_example_fields milestone_client = true.
Proof. vm_compute. reflexivity. Qed.
Example milestone_out_of_order_rejected :
  check_program milestone_family persistent_example_fields
    (sequence [::New 0 0; Call 0 t; Call 0 r]) = false.
Proof. vm_compute. reflexivity. Qed.

Local Notation st := (false,false).
Local Notation sw := (false,true).
Local Notation sc := (true,false).
Local Notation sq := (true,true).
Definition service_alias_client : statement service_alphabet := sequence
  [::New 0 0; Call 0 st; Copy 1 0; Call 0 sw; Call 1 sw;
     Call 0 sc; Call 1 sc; Call 0 sq; Call 1 sq].
Example service_alias_client_accepted :
  check_program_with_copy service_family persistent_example_fields
    persistent_example_copy service_alias_client = true.
Proof. vm_compute. reflexivity. Qed.
Example service_alias_client_needs_inheritance :
  check_program service_family persistent_example_fields service_alias_client = false.
Proof. vm_compute. reflexivity. Qed.
Example service_both_queries_required :
  check_program_with_copy service_family persistent_example_fields
    persistent_example_copy (sequence [::New 0 0; Call 0 st; Call 0 sw]) = false.
Proof. vm_compute. reflexivity. Qed.

Definition service_alias_final : machine service_alphabet :=
  let m := allocate initial_machine 0 0 in
  let m := emit m 0 st in
  let m := bind m 1 0 in
  let m := emit m 0 sw in
  let m := emit m 1 sw in
  let m := emit m 0 sc in
  let m := emit m 1 sc in
  clear_refs (emit (emit m 0 sq) 1 sq).
Example service_alias_terminates :
  program_execution service_alias_client initial_machine service_alias_final.
Proof.
  unfold service_alias_final. apply source_execution_instrument; [reflexivity|].
  unfold service_alias_client; cbn [sequence].
  repeat (eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|]);
    constructor.
Qed.
Example service_alias_object_history :
  next_loc service_alias_final = 1 /\
  object_history service_alias_final 0 = [::st;sw;sw;sc;sc;sq;sq].
Proof. vm_compute; auto. Qed.
Theorem service_alias_completion m :
  program_execution service_alias_client initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
    protocol service_family (classes m l) (object_history m l).
Proof.
  eapply copying_program_completion_sound;
    [apply service_copying_certified|exact service_alias_client_accepted].
Qed.
