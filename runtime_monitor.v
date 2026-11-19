(* Checked configuration reduction.  The only aggregate completion check is
   the explicit, automatically inserted bulk Finish step.  ProtocolError is
   terminal, including under evaluation contexts. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import syntax trace_languages protocols semantics
  typestate soundness copying_typestate copying_soundness monitor_shape.
Import ListNotations.
Set Implicit Arguments.

Inductive runtime_outcome (A : Type) :=
| RuntimeState (c : configuration A)
| ProtocolError.
Arguments RuntimeState {A} _.
Arguments ProtocolError {A}.

Section Monitor.
Context {A : Type} (P : protocol_family A).

Definition runtime_exit_check (m : machine A) : bool :=
  forallb (fun l => accepts P (classes m l) (object_history m l))
    (seq 0 (next_loc m)).
Definition runtime_guard (i : statement A) (m m' : machine A) : bool :=
  match i with
  | New _ c => viable P c []
  | Call x _ => match reference m x with
      | Some l => viable P (classes m l) (object_history m' l)
      | None => false
      end
  | Finish => runtime_exit_check m
  | _ => true
  end.

Lemma runtime_call_guard x a m m' l :
  primitive_step (Call x a) m m' -> reference m x = Some l ->
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
Lemma runtime_finish_guard m m' : runtime_guard Finish m m' = runtime_exit_check m.
Proof. reflexivity. Qed.
Lemma runtime_exit_check_clear m : runtime_exit_check (clear_refs m) = runtime_exit_check m.
Proof. reflexivity. Qed.
Lemma runtime_exit_check_spec m : runtime_exit_check m = true <->
  forall l, l < next_loc m -> protocol P (classes m l) (object_history m l).
Proof.
  unfold runtime_exit_check, protocol. rewrite forallb_forall.
  split; intros H l Hl; apply H; [apply in_seq|apply in_seq in Hl]; lia.
Qed.

(* Missing references and undefined field loads have no primitive transition;
   they are distinct from a failed protocol guard. *)
Inductive monitored_step : configuration A -> runtime_outcome A -> Prop :=
| monitor_step_ok i m m' : primitive_step i m m' -> runtime_guard i m m' = true ->
    monitored_step (m,i) (RuntimeState (m',Skip))
| monitor_step_error i m m' : primitive_step i m m' -> runtime_guard i m m' = false ->
    monitored_step (m,i) ProtocolError
| monitor_step_seq m s m' s' t : monitored_step (m,s) (RuntimeState (m',s')) ->
    monitored_step (m,Seq s t) (RuntimeState (m',Seq s' t))
| monitor_step_seq_error m s t : monitored_step (m,s) ProtocolError ->
    monitored_step (m,Seq s t) ProtocolError
| monitor_step_skip m t : monitored_step (m,Seq Skip t) (RuntimeState (m,t)).

Inductive monitored_execution : runtime_outcome A -> runtime_outcome A -> Prop :=
| monitor_exec_refl out : monitored_execution out out
| monitor_exec_step c d out : monitored_step c (RuntimeState d) ->
    monitored_execution (RuntimeState d) out -> monitored_execution (RuntimeState c) out
| monitor_exec_error c : monitored_step c ProtocolError ->
    monitored_execution (RuntimeState c) ProtocolError.
Definition runtime_terminal (out : runtime_outcome A) := match out with
  | RuntimeState (_,s) => s = Skip | ProtocolError => True end.
Definition monitored_prefix (s : statement A) m out :=
  finish_free s /\ monitored_execution (RuntimeState (m,instrument s)) out.
Definition monitored_program (s : statement A) m out :=
  monitored_prefix s m out /\ runtime_terminal out.

Lemma monitored_error_terminal out : monitored_execution ProtocolError out -> out = ProtocolError.
Proof. intros H; inversion H; reflexivity. Qed.
Lemma monitored_step_context E m s m' s' :
  monitored_step (m,s) (RuntimeState (m',s')) ->
  monitored_step (m,plug E s) (RuntimeState (m',plug E s')).
Proof. intros H; induction E; simpl; [exact H|apply monitor_step_seq; exact IHE]. Qed.
Lemma monitored_error_context E m s : monitored_step (m,s) ProtocolError ->
  monitored_step (m,plug E s) ProtocolError.
Proof. intros H; induction E; simpl; [exact H|apply monitor_step_seq_error; exact IHE]. Qed.
Lemma monitored_step_erases c d : monitored_step c (RuntimeState d) -> raw_step c d.
Proof.
  intros H; remember (RuntimeState d) as out eqn:E.
  revert d E; induction H; intros d E; inversion E; subst; eauto using raw_step.
Qed.
Lemma monitored_execution_erases c d :
  monitored_execution (RuntimeState c) (RuntimeState d) -> execution c d.
Proof.
  intros H; remember (RuntimeState c) as src eqn:Es; remember (RuntimeState d) as dst eqn:Ed.
  revert c d Es Ed; induction H; intros q r Es Ed; inversion Es; inversion Ed; subst.
  - inversion Ed; subst; constructor.
  - eapply exec_step; [eapply monitored_step_erases; exact H|eapply IHmonitored_execution; reflexivity].
Qed.
Lemma monitored_execution_trans x y z :
  monitored_execution x y -> monitored_execution y z -> monitored_execution x z.
Proof.
  intros H; induction H; intros Hz; auto.
  - eapply monitor_exec_step; eauto.
  - apply monitored_error_terminal in Hz; subst; now apply monitor_exec_error.
Qed.
Definition plug_outcome E (out : runtime_outcome A) :=
  match out with RuntimeState (m,s) => RuntimeState (m,plug E s) | ProtocolError => ProtocolError end.
Lemma monitored_step_context_outcome E c out : monitored_step c out ->
  monitored_step (fst c,plug E (snd c)) (plug_outcome E out).
Proof.
  destruct c as [m s], out as [[m' s']|]; simpl.
  - apply monitored_step_context.
  - apply monitored_error_context.
Qed.
Lemma monitored_execution_context E src out : monitored_execution src out ->
  monitored_execution (plug_outcome E src) (plug_outcome E out).
Proof.
  intros H; induction H; [constructor| |].
  - destruct c as [m s], d as [m' s']; simpl in *.
    eapply monitor_exec_step; [eapply monitored_step_context; exact H|exact IHmonitored_execution].
  - destruct c as [m s]; simpl. apply monitor_exec_error; now apply monitored_error_context.
Qed.
Lemma monitored_execution_primitive i m m' : primitive_step i m m' -> runtime_guard i m m'=true ->
  monitored_execution (RuntimeState (m,i)) (RuntimeState (m',Skip)).
Proof. intros H G; eapply monitor_exec_step; [eapply monitor_step_ok; eauto|constructor]. Qed.
Lemma monitored_execution_seq s t m m' m'' :
  monitored_execution (RuntimeState (m,s)) (RuntimeState (m',Skip)) ->
  monitored_execution (RuntimeState (m',t)) (RuntimeState (m'',Skip)) ->
  monitored_execution (RuntimeState (m,Seq s t)) (RuntimeState (m'',Skip)).
Proof.
  intros Hs Ht; eapply monitored_execution_trans.
  - exact (monitored_execution_context (SeqLeft Hole t) Hs).
  - eapply monitor_exec_step; [apply monitor_step_skip|exact Ht].
Qed.

Lemma monitored_prefix_erases s m m' t :
  monitored_prefix s m (RuntimeState (m',t)) -> program_prefix s m m'.
Proof. intros [HF HE]; split; [exact HF|exists t; now apply monitored_execution_erases]. Qed.
Lemma monitored_program_erases s m m' :
  monitored_program s m (RuntimeState (m',Skip)) -> program_execution s m m'.
Proof. intros [[HF HE] _]; split; [exact HF|now apply monitored_execution_erases]. Qed.

(* The final exit remains outside every source continuation.  This invariant
   connects the guard at Finish to guard-erased completion, independently of
   typing or the checked semantics. *)
Lemma finish_free_raw_step (c d : configuration A) : raw_step c d -> finish_free (snd c) -> finish_free (snd d).
Proof.
  intros H; induction H; unfold finish_free in *; simpl in *; auto.
  - rewrite andb_true_iff; intros [Hs Ht]; rewrite andb_true_iff; auto.
Qed.
Definition exit_position (s : statement A) :=
  finish_free s \/ s=Finish \/ exists t, finish_free t /\ s=Seq t Finish.
Lemma exit_position_step c d : raw_step c d -> exit_position (snd c) -> exit_position (snd d).
Proof.
  intros H [HF|[HF|[t [Ht HE]]]].
  - left; eapply finish_free_raw_step; eauto.
  - destruct c as [m s], d as [m' s']; simpl in *; subst s.
    inversion H; subst. match goal with Hp : primitive_step _ _ _ |- _ => inversion Hp; subst end. left; reflexivity.
  - destruct c as [m s], d as [m' s']; simpl in *; subst s.
    inversion H; subst.
    + match goal with Hp : primitive_step _ _ _ |- _ => inversion Hp end.
    + right; right; eexists; split; [eapply finish_free_raw_step; eauto|reflexivity].
    + right; left; reflexivity.
Qed.
Lemma exit_position_execution c d : execution c d -> exit_position (snd c) -> exit_position (snd d).
Proof. intros H; induction H; auto. intros HE; apply IHexecution; eapply exit_position_step; eauto. Qed.
Lemma finish_free_plug (E : context A) s : finish_free (plug E s) -> finish_free s.
Proof.
  induction E; simpl; auto. unfold finish_free; simpl.
  rewrite andb_true_iff; intros [H _]; apply IHE; exact H.
Qed.
Lemma final_finish_context s E : exit_position s -> s=plug E Finish -> E=Hole.
Proof.
  intros [HF|[HF|[t [Ht HE]]]] Hs.
  - subst s; apply finish_free_plug in HF; discriminate.
  - subst s; destruct E; [reflexivity|discriminate].
  - subst s; destruct E; simpl in Hs; [discriminate|].
    inversion Hs; subst. apply finish_free_plug in Ht; discriminate.
Qed.

Definition raw_protocol_contract (s : statement A) :=
  (forall m, program_prefix s initial_machine m ->
    forall l, l < next_loc m ->
      prefix_language (protocol P (classes m l)) (object_history m l)) /\
  (forall m, program_execution s initial_machine m ->
    forall l, l < next_loc m -> protocol P (classes m l) (object_history m l)).
Definition active_guards (m : machine A) (s : statement A) :=
  forall E i m', s=plug E i -> primitive_step i m m' -> runtime_guard i m m'=true.

Lemma raw_contract_guards s m t : raw_protocol_contract s -> finish_free s ->
  execution (initial_machine,instrument s) (m,t) -> active_guards m t.
Proof.
  intros [HS HC] HF HE E i m' Ht HP.
  assert (Hstep : raw_step (m,t) (m',plug E Skip)).
  { rewrite Ht; apply raw_step_context; now apply step_primitive. }
  assert (Hpost : execution (initial_machine,instrument s) (m',plug E Skip)).
  { eapply execution_trans; [exact HE|eapply exec_step; [exact Hstep|constructor]]. }
  assert (Hprefix : program_prefix s initial_machine m) by (split; [exact HF|eauto]).
  assert (Hprefix' : program_prefix s initial_machine m') by (split; [exact HF|eauto]).
  pose proof (HS m' Hprefix') as HV.
  destruct HP; cbn [runtime_guard]; auto.
  - specialize (HV (next_loc m)). cbn [allocate install next_loc classes] in HV.
    rewrite update_same in HV.
    apply viable_initial with (u := object_history (allocate m x c) (next_loc m)).
    apply viable_prefix. apply HV; lia.
  - unfold reference; rewrite H; simpl. apply viable_prefix; apply HV.
    change (owners m e < next_loc m). eapply monitor_program_prefix_target; eauto.
  - assert (HEpos : exit_position t).
    { eapply (@exit_position_execution (initial_machine,instrument s) (m,t)); [exact HE|]. right; right; exists s; auto. }
    assert (E=Hole) by (eapply final_finish_context; eauto). subst E; simpl in Hpost.
    rewrite <- runtime_exit_check_clear. apply runtime_exit_check_spec.
    apply HC; split; assumption.
Qed.

Lemma raw_step_monitored c d : raw_step c d -> active_guards (fst c) (snd c) ->
  monitored_step c (RuntimeState d).
Proof.
  intros H; induction H; simpl; intros HG.
  - eapply monitor_step_ok; [exact H|eapply (HG Hole); eauto].
  - apply monitor_step_seq; apply IHraw_step.
    intros E i u Hs HP; simpl in Hs, HP. eapply (HG (SeqLeft E t)); [simpl; now rewrite Hs|exact HP].
  - constructor.
Qed.
Lemma monitored_step_no_error c : active_guards (fst c) (snd c) ->
  ~ monitored_step c ProtocolError.
Proof.
  intros HG HM; remember ProtocolError as out eqn:EO; induction HM; inversion EO; subst; simpl in HG.
  - assert (runtime_guard i m m'=true) by (eapply (HG Hole); eauto); congruence.
  - apply IHHM; [|reflexivity]. intros E i u Hs HP.
    simpl in Hs, HP. eapply (HG (SeqLeft E t)); [simpl; now rewrite Hs|exact HP].
Qed.

Lemma raw_execution_monitored s c d : raw_protocol_contract s -> finish_free s ->
  execution c d -> execution (initial_machine,instrument s) c ->
  monitored_execution (RuntimeState c) (RuntimeState d).
Proof.
  intros HC HF HE; induction HE; intros Hpre; [constructor|].
  eapply monitor_exec_step.
  - apply raw_step_monitored; [exact H|]. destruct c as [m t]; simpl.
    eapply raw_contract_guards; eauto.
  - apply IHHE. eapply execution_trans; [exact Hpre|eapply exec_step; [exact H|constructor]].
Qed.
Lemma monitored_execution_no_error s c out : raw_protocol_contract s -> finish_free s ->
  monitored_execution (RuntimeState c) out ->
  execution (initial_machine,instrument s) c -> out<>ProtocolError.
Proof.
  intros HC HF HM; remember (RuntimeState c) as src eqn:ES.
  revert c ES; induction HM; intros q ES Hpre; inversion ES; subst.
  - discriminate.
  - apply IHHM with d; [reflexivity|].
    eapply execution_trans; [exact Hpre|].
    eapply exec_step; [eapply monitored_step_erases; exact H|constructor].
  - intros _. eapply monitored_step_no_error; [|exact H]. destruct q as [m t]; simpl.
    eapply raw_contract_guards; eauto.
Qed.

Theorem raw_contract_monitor_no_error s : raw_protocol_contract s ->
  ~ monitored_program s initial_machine ProtocolError.
Proof.
  intros HC [[HF HM] _].
  eapply (@monitored_execution_no_error s (initial_machine,instrument s) ProtocolError HC HF HM);
    [constructor|reflexivity].
Qed.
Theorem raw_contract_monitor_prefix_equivalence s : raw_protocol_contract s ->
  forall m t, monitored_prefix s initial_machine (RuntimeState (m,t)) <->
  finish_free s /\ execution (initial_machine,instrument s) (m,t).
Proof.
  intros HC m t; split.
  - intros [HF HM]; split; [exact HF|now apply monitored_execution_erases].
  - intros [HF HE]; split; [exact HF|]. eapply raw_execution_monitored; eauto; constructor.
Qed.
Theorem raw_contract_monitor_equivalence s : raw_protocol_contract s -> forall m,
  monitored_program s initial_machine (RuntimeState (m,Skip)) <->
  program_execution s initial_machine m.
Proof.
  intros HC m; split; [apply monitored_program_erases|].
  intros [HF HE]; split; [split; [exact HF|]|reflexivity].
  eapply raw_execution_monitored; eauto; constructor.
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
Theorem baseline_runtime_prefix_equivalence FT s : certified P -> check_program P FT s = true ->
  forall m t, monitored_prefix s initial_machine (RuntimeState (m,t)) <->
  finish_free s /\ execution (initial_machine,instrument s) (m,t).
Proof. intros; apply raw_contract_monitor_prefix_equivalence; eauto using baseline_raw_protocol_contract. Qed.
Theorem baseline_runtime_equivalence FT s : certified P -> check_program P FT s = true ->
  forall m, monitored_program s initial_machine (RuntimeState (m,Skip)) <->
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
Theorem copying_runtime_prefix_equivalence FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true ->
  forall m t, monitored_prefix s initial_machine (RuntimeState (m,t)) <->
  finish_free s /\ execution (initial_machine,instrument s) (m,t).
Proof. intros; apply raw_contract_monitor_prefix_equivalence; eauto using copying_raw_protocol_contract. Qed.
Theorem copying_runtime_equivalence FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true -> forall m,
  monitored_program s initial_machine (RuntimeState (m,Skip)) <->
    program_execution s initial_machine m.
Proof. intros; apply raw_contract_monitor_equivalence; eauto using copying_raw_protocol_contract. Qed.
End Monitor.
