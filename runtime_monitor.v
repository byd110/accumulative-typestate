(* A protocol monitor with executable guards over the unchanged raw calculus.
   Finish x retires one binding. The aggregate completion check occurs once,
   at program exit, after all instructions on the selected path. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import syntax trace_languages protocols semantics
  typestate soundness copying_typestate copying_soundness monitor_shape.
Import ListNotations.
Set Implicit Arguments.

Inductive runtime_outcome (A : Type) :=
| RuntimeState (m : machine A)
| ProtocolError.
Arguments RuntimeState {A} _.
Arguments ProtocolError {A}.

Section Monitor.
Context {A : Type} (P : protocol_family A).

(* Calls inspect the updated aggregate object history, not the local view.
   A raw candidate update is pure data: a failed guard commits no update. *)
Definition runtime_guard (i : instruction A) (m m' : machine A) : bool :=
  match i with
  | New _ c => viable P c []
  | Call x _ => match reference m x with
      | Some l => viable P (classes m l) (object_history m' l)
      | None => false
      end
  | _ => true
  end.

Definition runtime_exit_check (m : machine A) : bool :=
  forallb (fun l => accepts P (classes m l) (object_history m l))
    (seq 0 (next_loc m)).

Lemma runtime_call_guard x a m m' l :
  raw_step (Call x a) m m' -> reference m x = Some l ->
  runtime_guard (Call x a) m m' =
    viable P (classes m l) (object_history m l ++ [a]).
Proof.
  intros HR Href; inversion HR; subst.
  match goal with Hget : get (refs _) _ = Some _ |- _ =>
    unfold reference in Href; rewrite Hget in Href; inversion Href; subst;
    cbn [runtime_guard]; unfold reference; rewrite Hget; simpl
  end.
  rewrite emit_history, Nat.eqb_refl. reflexivity.
Qed.

(* Individual retirement neither checks nor changes aggregate completion.
   Thus moving a final whole-object check across the exit retirements is exact. *)
Lemma runtime_finish_guard x m m' : runtime_guard (Finish x) m m' = true.
Proof. reflexivity. Qed.
Lemma runtime_exit_check_retire m x : runtime_exit_check (retire m x) = runtime_exit_check m.
Proof. reflexivity. Qed.

Lemma runtime_exit_check_spec m : runtime_exit_check m = true <->
  forall l, l < next_loc m -> protocol P (classes m l) (object_history m l).
Proof.
  unfold runtime_exit_check, protocol. rewrite forallb_forall.
  split; intros H l Hl; apply H; [apply in_seq|apply in_seq in Hl]; lia.
Qed.

Inductive monitored_step (i : instruction A) (m : machine A) : runtime_outcome A -> Prop :=
| monitor_step_ok m' : raw_step i m m' -> runtime_guard i m m' = true ->
    monitored_step i m (RuntimeState m')
| monitor_step_error m' : raw_step i m m' -> runtime_guard i m m' = false ->
    monitored_step i m ProtocolError.

Inductive monitored_trace : list (instruction A) -> machine A -> runtime_outcome A -> Prop :=
| monitor_trace_nil m : monitored_trace [] m (RuntimeState m)
| monitor_trace_cons i is m m' out : monitored_step i m (RuntimeState m') ->
    monitored_trace is m' out -> monitored_trace (i :: is) m out
| monitor_trace_error i is m : monitored_step i m ProtocolError ->
    monitored_trace (i :: is) m ProtocolError.

(* Ordinary missing-reference / uninitialized-load failures are still outside
   this monitor: both outcome rules require an enabled raw step. *)
Inductive monitored_program (s : statement A) (m : machine A) : runtime_outcome A -> Prop :=
| monitor_program_ok p m' : path s p -> monitored_trace p m (RuntimeState m') ->
    runtime_exit_check m' = true -> monitored_program s m (RuntimeState m')
| monitor_program_step_error p : path s p -> monitored_trace p m ProtocolError ->
    monitored_program s m ProtocolError
| monitor_program_exit_error p m' : path s p -> monitored_trace p m (RuntimeState m') ->
    runtime_exit_check m' = false -> monitored_program s m ProtocolError.

Lemma monitored_trace_erases is m m' :
  monitored_trace is m (RuntimeState m') -> execution is m m'.
Proof.
  intros H; remember (RuntimeState m') as out eqn:E.
  induction H; inversion E; subst.
  - constructor.
  - inversion H; subst. econstructor; eauto.
Qed.

Lemma monitored_program_erases s m m' :
  monitored_program s m (RuntimeState m') -> program_execution s m m'.
Proof.
  intros H; inversion H; subst. exists p; split; auto.
  now apply monitored_trace_erases.
Qed.

Lemma monitor_execution_app (p q : list (instruction A)) (m m' m'' : machine A) :
  execution p m m' -> execution q m' m'' -> execution (p ++ q) m m''.
Proof. intros H; induction H; simpl; intros; eauto using execution. Qed.

Definition raw_protocol_contract (s : statement A) :=
  (forall m, program_prefix s initial_machine m ->
    forall l, l < next_loc m ->
      prefix_language (protocol P (classes m l)) (object_history m l)) /\
  (forall m, program_execution s initial_machine m ->
    forall l, l < next_loc m -> protocol P (classes m l) (object_history m l)).

Definition path_guards (s : statement A) :=
  forall p i q m m', path s (p ++ i :: q) ->
    execution p initial_machine m -> raw_step i m m' -> runtime_guard i m m' = true.

Lemma raw_contract_guards s : raw_protocol_contract s -> path_guards s.
Proof.
  intros [HS HC] p i q m m' HP HE HR.
  assert (Hpre : program_prefix s initial_machine m).
  { exists p, (i :: q); auto. }
  assert (Hpost : program_prefix s initial_machine m').
  { exists (p ++ [i]), q. split.
    - rewrite <- app_assoc; exact HP.
    - eapply monitor_execution_app; [exact HE|].
      econstructor; [exact HR|constructor]. }
  pose proof (HS m' Hpost) as HV.
  destruct HR; cbn [runtime_guard]; auto.
  - specialize (HV (next_loc m)).
    cbn [allocate install next_loc classes] in HV.
    rewrite update_same in HV.
    apply viable_initial with (u := object_history (allocate m x c) (next_loc m)).
    apply viable_prefix. apply HV. lia.
  - unfold reference. rewrite H. simpl.
    apply viable_prefix. apply HV.
    change (owners m e < next_loc m).
    eapply monitor_program_prefix_target; eauto.
Qed.

Lemma raw_trace_monitored s : path_guards s ->
  forall is m m', execution is m m' -> forall p,
  path s (p ++ is) -> execution p initial_machine m ->
  monitored_trace is m (RuntimeState m').
Proof.
  intros HG is m m' HE; induction HE; intros p HP Hpre.
  - constructor.
  - econstructor.
    + econstructor; [exact H|eapply HG; eauto].
    + apply IHHE with (p := p ++ [i]).
      * rewrite <- app_assoc; exact HP.
      * eapply monitor_execution_app; [exact Hpre|].
        econstructor; [exact H|constructor].
Qed.

Lemma monitored_trace_no_error s : path_guards s ->
  forall is m out, monitored_trace is m out -> forall p,
  path s (p ++ is) -> execution p initial_machine m -> out <> ProtocolError.
Proof.
  intros HG is m out HM; induction HM; intros p HP Hpre.
  - discriminate.
  - inversion H; subst. apply IHHM with (p := p ++ [i]).
    + rewrite <- app_assoc; exact HP.
    + eapply monitor_execution_app; [exact Hpre|].
      econstructor; eauto using execution.
  - inversion H; subst.
    assert (runtime_guard i m m' = true) by (eapply HG; eauto).
    congruence.
Qed.

Theorem raw_contract_monitor_no_error s : raw_protocol_contract s ->
  ~ monitored_program s initial_machine ProtocolError.
Proof.
  intros HC HM. pose proof (raw_contract_guards HC) as HG.
  inversion HM; subst.
  - eapply (@monitored_trace_no_error s HG p initial_machine ProtocolError H0 []).
    + exact H.
    + constructor.
    + reflexivity.
  - assert (program_execution s initial_machine m') as HE.
    { exists p; split; auto. now apply monitored_trace_erases. }
    assert (runtime_exit_check m' = true).
    { apply runtime_exit_check_spec. now apply (proj2 HC). }
    congruence.
Qed.

Theorem raw_contract_monitor_equivalence s : raw_protocol_contract s -> forall m,
  monitored_program s initial_machine (RuntimeState m) <->
  program_execution s initial_machine m.
Proof.
  intros HC m; split; [apply monitored_program_erases|].
  intros [p [HP HE]]. eapply monitor_program_ok with (p := p).
  - exact HP.
  - eapply raw_trace_monitored with (p := []); eauto using raw_contract_guards, execution.
  - apply runtime_exit_check_spec. apply (proj2 HC).
    exists p; auto.
Qed.

Theorem baseline_raw_protocol_contract FT s : certified P ->
  check_program P FT s = true -> raw_protocol_contract s.
Proof.
  intros HC HT; split; intros m HE.
  - eapply typestate_prefix_sound; eauto.
  - eapply typestate_completion_sound; eauto.
Qed.

Theorem baseline_runtime_no_error FT s : certified P ->
  check_program P FT s = true -> ~ monitored_program s initial_machine ProtocolError.
Proof. intros; apply raw_contract_monitor_no_error; eauto using baseline_raw_protocol_contract. Qed.

Theorem baseline_runtime_equivalence FT s : certified P -> check_program P FT s = true ->
  forall m, monitored_program s initial_machine (RuntimeState m) <->
    program_execution s initial_machine m.
Proof. intros; apply raw_contract_monitor_equivalence; eauto using baseline_raw_protocol_contract. Qed.

Theorem copying_raw_protocol_contract FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true -> raw_protocol_contract s.
Proof.
  intros HC HT; split; intros m HE.
  - eapply copying_program_prefix_sound; eauto.
  - eapply copying_program_completion_sound; eauto.
Qed.

Theorem copying_runtime_no_error FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true ->
  ~ monitored_program s initial_machine ProtocolError.
Proof. intros; apply raw_contract_monitor_no_error; eauto using copying_raw_protocol_contract. Qed.

Theorem copying_runtime_equivalence FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true -> forall m,
  monitored_program s initial_machine (RuntimeState m) <->
    program_execution s initial_machine m.
Proof. intros; apply raw_contract_monitor_equivalence; eauto using copying_raw_protocol_contract. Qed.
End Monitor.
