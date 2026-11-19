(* Protocol guards are specified on the four observable maps.  Only the
   correspondence proof imports the ghost runtime monitor; raw semantics and
   its simulation above are independent of static soundness. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import syntax trace_languages protocols semantics surface_semantics
  typestate soundness necessity copying_typestate copying_soundness runtime_monitor.
Import ListNotations.
Set Implicit Arguments.

Definition surface_guard {A} (P : protocol_family A) (s : statement A) (M : surface A) : Prop :=
  match s with
  | New _ c => viable P c [] = true
  | Call x a => match surface_refs M x with
      | Some l => match surface_classes M l with
          | Some c => viable P c (surface_history M l ++ [a]) = true
          | None => False end
      | None => False end
  | Finish => surface_all_objects (protocol P) M
  | _ => True
  end.

Lemma runtime_surface_guard {A} (P : protocol_family A) r s (m m' : machine A) M :
  ghost_well_formed m -> represents r m M -> primitive_step s m m' ->
  (runtime_guard P s m m' = true <-> surface_guard P s M).
Proof.
  intros H R S; destruct S; cbn [surface_guard]; try (cbn [runtime_guard]; tauto).
  - assert (He : e < next_epoch m) by (eapply ghost_refs; eauto).
    pose proof (ghost_owners H He) as Hl.
    rewrite (represents_get x R H0), (represents_classes R Hl),
      (represents_histories R Hl).
    unfold runtime_guard, reference; rewrite H0; simpl.
    rewrite ghost_history_emit, Nat.eqb_refl; tauto.
  - rewrite runtime_finish_guard, runtime_exit_check_spec.
    exact (@represents_all_objects A r m M (protocol P) R).
Qed.

Inductive surface_runtime_outcome (A : Type) :=
| SurfaceState (c : surface_configuration A)
| SurfaceProtocolError.
Arguments SurfaceState {A} _.
Arguments SurfaceProtocolError {A}.

Section SurfaceMonitor.
Context {A : Type} (P : protocol_family A).

Inductive surface_monitored_step : surface_configuration A -> surface_runtime_outcome A -> Prop :=
| surface_monitor_ok i M M' : surface_primitive i M M' -> surface_guard P i M ->
    surface_monitored_step (M,i) (SurfaceState (M',Skip))
| surface_monitor_error i M M' : surface_primitive i M M' -> ~ surface_guard P i M ->
    surface_monitored_step (M,i) SurfaceProtocolError
| surface_monitor_seq M s M' s' t :
    surface_monitored_step (M,s) (SurfaceState (M',s')) ->
    surface_monitored_step (M,Seq s t) (SurfaceState (M',Seq s' t))
| surface_monitor_seq_error M s t : surface_monitored_step (M,s) SurfaceProtocolError ->
    surface_monitored_step (M,Seq s t) SurfaceProtocolError
| surface_monitor_skip M t :
    surface_monitored_step (M,Seq Skip t) (SurfaceState (M,t)).

Inductive surface_monitored_execution : surface_runtime_outcome A -> surface_runtime_outcome A -> Prop :=
| surface_monitor_refl out : surface_monitored_execution out out
| surface_monitor_step c d out : surface_monitored_step c (SurfaceState d) ->
    surface_monitored_execution (SurfaceState d) out ->
    surface_monitored_execution (SurfaceState c) out
| surface_monitor_failure c : surface_monitored_step c SurfaceProtocolError ->
    surface_monitored_execution (SurfaceState c) SurfaceProtocolError.

Definition surface_monitored_prefix (s : statement A) M out :=
  finish_free s /\ surface_monitored_execution (SurfaceState (M,instrument s)) out.
Definition surface_monitored_program (s : statement A) M out :=
  surface_monitored_prefix s M out /\
    match out with SurfaceState (_,t) => t=Skip | SurfaceProtocolError => True end.

Lemma surface_monitored_step_context E M s M' s' :
  surface_monitored_step (M,s) (SurfaceState (M',s')) ->
  surface_monitored_step (M,plug E s) (SurfaceState (M',plug E s')).
Proof. intros H; induction E; simpl; [exact H|].
  apply surface_monitor_seq; exact IHE. Qed.
Lemma surface_monitored_error_context E M s :
  surface_monitored_step (M,s) SurfaceProtocolError ->
  surface_monitored_step (M,plug E s) SurfaceProtocolError.
Proof. intros H; induction E; simpl; [exact H|].
  apply surface_monitor_seq_error; exact IHE. Qed.

Theorem ghost_surface_monitored_step r m m' M s s' :
  ghost_well_formed m -> represents r m M ->
  monitored_step P (m,s) (RuntimeState (m',s')) ->
  exists r' M', extends_on (next_loc m) r r' /\
    surface_monitored_step (M,s) (SurfaceState (M',s')) /\ represents r' m' M'.
Proof.
  intros H R S; remember (m,s) as c eqn:Ec;
    remember (RuntimeState (m',s')) as out eqn:Eo.
  revert m s m' s' r M H R Ec Eo.
  induction S; intros u v u' v' r N WF R Ec Eo; inversion Ec; inversion Eo; subst.
  - destruct (ghost_surface_primitive WF R H) as [r' [N' [Ext [Sp Rp]]]].
    exists r',N'; split; auto; split; auto.
    eapply surface_monitor_ok; eauto. apply (proj1 (runtime_surface_guard P WF R H)); exact H0.
  - destruct (IHS _ _ _ _ r N WF R eq_refl eq_refl) as [r' [N' [Ext [Sp Rp]]]].
    exists r',N'; split; auto; split; auto. now apply surface_monitor_seq.
  - exists r,N; split; [intros l Hl; reflexivity|]; split; auto; constructor.
Qed.

Theorem surface_ghost_monitored_step r m M M' s s' :
  ghost_well_formed m -> represents r m M ->
  surface_monitored_step (M,s) (SurfaceState (M',s')) ->
  exists r' m', extends_on (next_loc m) r r' /\
    monitored_step P (m,s) (RuntimeState (m',s')) /\ represents r' m' M'.
Proof.
  intros H R S; remember (M,s) as c eqn:Ec;
    remember (SurfaceState (M',s')) as out eqn:Eo.
  revert M s M' s' r m H R Ec Eo.
  induction S; intros N v N' v' r u WF R Ec Eo; inversion Ec; inversion Eo; subst.
  - destruct (surface_ghost_primitive WF R H) as [r' [u' [Ext [Sp Rp]]]].
    exists r',u'; split; auto; split; auto.
    eapply monitor_step_ok; eauto. apply (proj2 (runtime_surface_guard P WF R Sp)); exact H0.
  - destruct (IHS _ _ _ _ r u WF R eq_refl eq_refl) as [r' [u' [Ext [Sp Rp]]]].
    exists r',u'; split; auto; split; auto. now apply monitor_step_seq.
  - exists r,u; split; [intros l Hl; reflexivity|]; split; auto; constructor.
Qed.

Theorem ghost_surface_monitored_error r m M s :
  ghost_well_formed m -> represents r m M -> monitored_step P (m,s) ProtocolError ->
  surface_monitored_step (M,s) SurfaceProtocolError.
Proof.
  intros H R S; remember (m,s) as c eqn:Ec; remember ProtocolError as out eqn:Eo.
  revert m s r M H R Ec Eo.
  induction S; intros u v r N WF R Ec Eo; inversion Ec; inversion Eo; subst.
  - destruct (ghost_surface_primitive WF R H) as [r' [N' [Ext [Sp Rp]]]].
    eapply surface_monitor_error; [exact Sp|]. intros G.
    apply (proj2 (runtime_surface_guard P WF R H)) in G; congruence.
  - apply surface_monitor_seq_error; eapply IHS; eauto.
Qed.

Theorem surface_ghost_monitored_error r m M s :
  ghost_well_formed m -> represents r m M ->
  surface_monitored_step (M,s) SurfaceProtocolError -> monitored_step P (m,s) ProtocolError.
Proof.
  intros H R S; remember (M,s) as c eqn:Ec; remember SurfaceProtocolError as out eqn:Eo.
  revert M s r m H R Ec Eo.
  induction S; intros N v r u WF R Ec Eo; inversion Ec; inversion Eo; subst.
  - destruct (surface_ghost_primitive WF R H) as [r' [u' [Ext [Sp Rp]]]].
    eapply monitor_step_error; [exact Sp|].
    destruct (runtime_guard P v u u') eqn:E; auto.
    exfalso; apply H0; apply (proj1 (runtime_surface_guard P WF R Sp)); exact E.
  - apply monitor_step_seq_error; eapply IHS; eauto.
Qed.

Theorem ghost_surface_monitored_execution r m m' M s t :
  ghost_well_formed m -> represents r m M ->
  monitored_execution P (RuntimeState (m,s)) (RuntimeState (m',t)) ->
  exists r' M', extends_on (next_loc m) r r' /\
    surface_monitored_execution (SurfaceState (M,s)) (SurfaceState (M',t)) /\
    represents r' m' M'.
Proof.
  intros H R E; remember (RuntimeState (m,s)) as c eqn:Ec;
    remember (RuntimeState (m',t)) as d eqn:Ed.
  revert m s m' t r M H R Ec Ed.
  induction E; intros u v u' v' r N WF R Ec Ed; inversion Ec; inversion Ed; subst; try discriminate.
  - inversion H0; subst. exists r,N; split; [intros l Hl; reflexivity|]; split; auto; constructor.
  - destruct d as [md sd].
    destruct (ghost_surface_monitored_step WF R H) as [rd [Nd [Ext [Sp Rp]]]].
    pose proof (monitored_step_erases H) as Raw.
    destruct (IHE _ _ _ _ rd Nd (ghost_raw_step Raw WF) Rp eq_refl eq_refl)
      as [re [Ne [Exte [Se Re]]]].
    exists re,Ne; split.
    + intros l Hl; rewrite Exte; [apply Ext; exact Hl|].
      pose proof (step_locations_monotone Raw); simpl in *; lia.
    + split; auto; eapply surface_monitor_step; eauto.
Qed.

Theorem surface_ghost_monitored_execution r m M M' s t :
  ghost_well_formed m -> represents r m M ->
  surface_monitored_execution (SurfaceState (M,s)) (SurfaceState (M',t)) ->
  exists r' m', extends_on (next_loc m) r r' /\
    monitored_execution P (RuntimeState (m,s)) (RuntimeState (m',t)) /\
    represents r' m' M'.
Proof.
  intros H R E; remember (SurfaceState (M,s)) as c eqn:Ec;
    remember (SurfaceState (M',t)) as d eqn:Ed.
  revert M s M' t r m H R Ec Ed.
  induction E; intros N v N' v' r u WF R Ec Ed; inversion Ec; inversion Ed; subst; try discriminate.
  - inversion H0; subst. exists r,u; split; [intros l Hl; reflexivity|]; split; auto; constructor.
  - destruct d as [Md sd].
    destruct (surface_ghost_monitored_step WF R H) as [rd [ud [Ext [Sp Rp]]]].
    pose proof (monitored_step_erases Sp) as Raw.
    destruct (IHE _ _ _ _ rd ud (ghost_raw_step Raw WF) Rp eq_refl eq_refl)
      as [re [ue [Exte [Se Re]]]].
    exists re,ue; split.
    + intros l Hl; rewrite Exte; [apply Ext; exact Hl|].
      pose proof (step_locations_monotone Raw); simpl in *; lia.
    + split; auto; eapply monitor_exec_step; eauto.
Qed.

Theorem ghost_surface_monitored_execution_error r m M s :
  ghost_well_formed m -> represents r m M ->
  monitored_execution P (RuntimeState (m,s)) ProtocolError ->
  surface_monitored_execution (SurfaceState (M,s)) SurfaceProtocolError.
Proof.
  intros H R E; remember (RuntimeState (m,s)) as c eqn:Ec;
    remember ProtocolError as d eqn:Ed.
  revert m s r M H R Ec Ed.
  induction E; intros u v r N WF R Ec Ed; inversion Ec; inversion Ed; subst; try discriminate.
  - destruct d as [md sd].
    destruct (ghost_surface_monitored_step WF R H) as [rd [Nd [Ext [Sp Rp]]]].
    pose proof (monitored_step_erases H) as Raw.
    eapply surface_monitor_step; [exact Sp|].
    exact (IHE md sd rd Nd (ghost_raw_step Raw WF) Rp eq_refl eq_refl).
  - apply surface_monitor_failure; eapply ghost_surface_monitored_error; eauto.
Qed.

Theorem surface_ghost_monitored_execution_error r m M s :
  ghost_well_formed m -> represents r m M ->
  surface_monitored_execution (SurfaceState (M,s)) SurfaceProtocolError ->
  monitored_execution P (RuntimeState (m,s)) ProtocolError.
Proof.
  intros H R E; remember (SurfaceState (M,s)) as c eqn:Ec;
    remember SurfaceProtocolError as d eqn:Ed.
  revert M s r m H R Ec Ed.
  induction E; intros N v r u WF R Ec Ed; inversion Ec; inversion Ed; subst; try discriminate.
  - destruct d as [Md sd].
    destruct (surface_ghost_monitored_step WF R H) as [rd [ud [Ext [Sp Rp]]]].
    pose proof (monitored_step_erases Sp) as Raw.
    eapply monitor_exec_step; [exact Sp|].
    exact (IHE Md sd rd ud (ghost_raw_step Raw WF) Rp eq_refl eq_refl).
  - apply monitor_exec_error; eapply surface_ghost_monitored_error; eauto.
Qed.

Theorem ghost_surface_error_equivalence s :
  monitored_program P s initial_machine ProtocolError <->
  surface_monitored_program s initial_surface SurfaceProtocolError.
Proof.
  split; intros [[F E] T]; split; [split|exact I|split|exact I].
  - exact F.
  - eapply ghost_surface_monitored_execution_error; [apply ghost_initial|
      apply (represents_initial (fun l => l))|exact E].
  - exact F.
  - eapply surface_ghost_monitored_execution_error; [apply ghost_initial|
      apply (represents_initial (fun l => l))|exact E].
Qed.

Lemma surface_monitored_step_erases c d :
  surface_monitored_step c (SurfaceState d) -> surface_step c d.
Proof.
  intros H; remember (SurfaceState d) as out eqn:E.
  revert d E; induction H; intros d E; inversion E; subst; eauto using surface_step.
Qed.
Lemma surface_monitored_execution_erases c d :
  surface_monitored_execution (SurfaceState c) (SurfaceState d) -> surface_execution c d.
Proof.
  intros H; remember (SurfaceState c) as src eqn:Es;
    remember (SurfaceState d) as dst eqn:Ed.
  revert c d Es Ed; induction H; intros q r Es Ed; inversion Es; inversion Ed; subst.
  - inversion H0; subst; constructor.
  - eapply surface_exec_step; [eapply surface_monitored_step_erases; exact H|
      eapply IHsurface_monitored_execution; reflexivity].
Qed.

Lemma surface_raw_step_checked s M t M' t' :
  raw_protocol_contract P s -> finish_free s ->
  surface_execution (initial_surface,instrument s) (M,t) ->
  surface_step (M,t) (M',t') ->
  surface_monitored_step (M,t) (SurfaceState (M',t')).
Proof.
  intros HC HF HE HS.
  destruct (@surface_ghost_execution A (initial_surface,instrument s) (M,t)
    (fun l => l) initial_machine ghost_initial (represents_initial _) HE)
    as [r [m [Ext [E R]]]].
  assert (WF : ghost_well_formed m).
  { exact (ghost_execution E ghost_initial). }
  pose proof (raw_contract_guards HC HF E) as G.
  destruct (surface_step_decompose HS)
    as [[C [i [Ht [Ht' Hp]]]]|[C [v [Ht [Ht' Eq]]]]].
  - destruct (surface_ghost_primitive WF R Hp) as [r' [m' [Ext' [Sp Rp]]]].
    specialize (G C i m' Ht Sp).
    subst t t'; apply surface_monitored_step_context.
    eapply surface_monitor_ok; [exact Hp|].
    apply (proj1 (runtime_surface_guard P WF R Sp)); exact G.
  - subst t t' M'; apply surface_monitored_step_context; constructor.
Qed.

Lemma surface_raw_execution_checked s c d :
  raw_protocol_contract P s -> finish_free s ->
  surface_execution (initial_surface,instrument s) c -> surface_execution c d ->
  surface_monitored_execution (SurfaceState c) (SurfaceState d).
Proof.
  intros HC HF Pre E; revert Pre; induction E; intros Pre; [constructor|].
  destruct c as [M t], d as [M' t']; eapply surface_monitor_step.
  - eapply surface_raw_step_checked; eauto.
  - apply IHE; eapply surface_execution_trans; [exact Pre|].
    eapply surface_exec_step; [exact H|constructor].
Qed.

Theorem surface_contract_prefix_equivalence s : raw_protocol_contract P s ->
  forall M t, surface_monitored_prefix s initial_surface (SurfaceState (M,t)) <->
    finish_free s /\ surface_execution (initial_surface,instrument s) (M,t).
Proof.
  intros HC M t; split; intros [HF HE]; split; auto.
  - now apply surface_monitored_execution_erases.
  - eapply surface_raw_execution_checked; eauto; constructor.
Qed.

Theorem surface_contract_completion_equivalence s : raw_protocol_contract P s ->
  forall M, surface_monitored_program s initial_surface (SurfaceState (M,Skip)) <->
    surface_program_execution s initial_surface M.
Proof.
  intros HC M; split.
  - intros [[HF HE] _]; split; auto; now apply surface_monitored_execution_erases.
  - intros [HF HE]; split; [split; auto|reflexivity].
    eapply surface_raw_execution_checked; eauto; constructor.
Qed.

Theorem surface_typestate_prefix_sound FT s M : certified P -> check_program P FT s = true ->
  surface_program_prefix s initial_surface M ->
  forall l c, surface_classes M l = Some c -> prefix_language (protocol P c) (surface_history M l).
Proof.
  intros HC HT; apply (proj1 (ghost_surface_prefix_safety (protocol P) s)).
  intros m HE; eapply typestate_prefix_sound; eauto.
Qed.

Theorem surface_typestate_completion_sound FT s M : certified P -> check_program P FT s = true ->
  surface_program_execution s initial_surface M ->
  forall l c, surface_classes M l = Some c -> protocol P c (surface_history M l).
Proof.
  intros HC HT; apply (proj1 (ghost_surface_completion_safety (protocol P) s)).
  intros m HE; eapply typestate_completion_sound; eauto.
Qed.

Theorem surface_runtime_prefix_equivalence FT s : certified P -> check_program P FT s = true ->
  forall M t, surface_monitored_prefix s initial_surface (SurfaceState (M,t)) <->
    finish_free s /\ surface_execution (initial_surface,instrument s) (M,t).
Proof. intros; apply surface_contract_prefix_equivalence; eauto using baseline_raw_protocol_contract. Qed.

Theorem surface_runtime_equivalence FT s : certified P -> check_program P FT s = true ->
  forall M, surface_monitored_program s initial_surface (SurfaceState (M,Skip)) <->
    surface_program_execution s initial_surface M.
Proof. intros; apply surface_contract_completion_equivalence; eauto using baseline_raw_protocol_contract. Qed.

Theorem surface_runtime_no_error FT s : certified P -> check_program P FT s = true ->
  ~ surface_monitored_program s initial_surface SurfaceProtocolError.
Proof.
  intros HC HT E; apply (proj2 (ghost_surface_error_equivalence s)) in E.
  eapply baseline_runtime_no_error; eauto.
Qed.

Theorem surface_copying_prefix_sound FT mode s M :
  copying_certified P mode -> check_program_with_copy P FT mode s = true ->
  surface_program_prefix s initial_surface M ->
  forall l c, surface_classes M l = Some c -> prefix_language (protocol P c) (surface_history M l).
Proof.
  intros HC HT; apply (proj1 (ghost_surface_prefix_safety (protocol P) s)).
  intros m HE; eapply copying_program_prefix_sound; eauto.
Qed.

Theorem surface_copying_completion_sound FT mode s M :
  copying_certified P mode -> check_program_with_copy P FT mode s = true ->
  surface_program_execution s initial_surface M ->
  forall l c, surface_classes M l = Some c -> protocol P c (surface_history M l).
Proof.
  intros HC HT; apply (proj1 (ghost_surface_completion_safety (protocol P) s)).
  intros m HE; eapply copying_program_completion_sound; eauto.
Qed.

Theorem surface_copying_runtime_prefix_equivalence FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true ->
  forall M t, surface_monitored_prefix s initial_surface (SurfaceState (M,t)) <->
    finish_free s /\ surface_execution (initial_surface,instrument s) (M,t).
Proof. intros; apply surface_contract_prefix_equivalence; eauto using copying_raw_protocol_contract. Qed.

Theorem surface_copying_runtime_equivalence FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true ->
  forall M, surface_monitored_program s initial_surface (SurfaceState (M,Skip)) <->
    surface_program_execution s initial_surface M.
Proof. intros; apply surface_contract_completion_equivalence; eauto using copying_raw_protocol_contract. Qed.

Theorem surface_copying_runtime_no_error FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true ->
  ~ surface_monitored_program s initial_surface SurfaceProtocolError.
Proof.
  intros HC HT E; apply (proj2 (ghost_surface_error_equivalence s)) in E.
  eapply copying_runtime_no_error; eauto.
Qed.

(* Necessity is transported from unguarded completion soundness.  Successful
   checked completion alone would make this statement vacuous by its guard. *)
Theorem surface_completion_sound_requires_certified FT :
  (forall s M, check_program P FT s = true ->
    surface_program_execution s initial_surface M ->
    forall l c, surface_classes M l = Some c -> protocol P c (surface_history M l)) ->
  certified P.
Proof.
  intros H; apply (@completion_sound_requires_certified A P FT).
  intros s m HT HE. apply (proj2 (ghost_surface_completion_safety (protocol P) s)).
  - intros M HM; eapply H; eauto.
  - exact HE.
Qed.

Theorem surface_completion_sound_iff_certified FT :
  (forall s M, check_program P FT s = true ->
    surface_program_execution s initial_surface M ->
    forall l c, surface_classes M l = Some c -> protocol P c (surface_history M l)) <->
  certified P.
Proof.
  split; [apply surface_completion_sound_requires_certified|].
  intros HC s M HT HE; eapply surface_typestate_completion_sound; eauto.
Qed.

End SurfaceMonitor.

(* A constructive allocation regression chooses 37 and then 5.  Both objects
   remain observable after the common exit has removed all references. *)
Definition noncanonical_source {A} c d : statement A := Seq (New 0 c) (New 1 d).
Definition noncanonical_final {A} c d : surface A :=
  surface_clear (surface_allocate (surface_allocate initial_surface 0 c 37) 1 d 5).

Example noncanonical_surface_execution {A} c d :
  surface_program_execution (@noncanonical_source A c d) initial_surface (noncanonical_final c d).
Proof.
  split; [reflexivity|]. unfold instrument, noncanonical_source, noncanonical_final.
  eapply surface_exec_step.
  - apply surface_step_seq, surface_step_seq, surface_step_primitive.
    apply surface_new with (l:=37); reflexivity.
  - eapply surface_exec_step; [apply surface_step_seq, surface_step_skip|].
    eapply surface_exec_step.
    + apply surface_step_seq, surface_step_primitive.
      apply surface_new with (l:=5); reflexivity.
    + eapply surface_exec_step; [apply surface_step_skip|].
      eapply surface_exec_step; [apply surface_step_primitive; constructor|constructor].
Qed.

Example noncanonical_surface_observations {A} c d :
  surface_classes (@noncanonical_final A c d) 37 = Some c /\
  surface_classes (@noncanonical_final A c d) 5 = Some d /\
  (forall x, surface_refs (@noncanonical_final A c d) x = None).
Proof. repeat split; reflexivity. Qed.

Example noncanonical_surface_equipped {A} c d :
  exists r m, program_execution (@noncanonical_source A c d) initial_machine m /\
    represents r m (noncanonical_final c d).
Proof.
  destruct (@surface_ghost_program A (fun l => l) (noncanonical_source c d)
    initial_machine initial_surface (noncanonical_final c d)
    ghost_initial (represents_initial _) (noncanonical_surface_execution c d))
    as [r [m [Ext [E R]]]]. exists r,m; auto.
Qed.
