(* Finite persistent prerequisites. Setters accumulate established features;
   a designated use requires a monotone guard and records completion. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From Accumulation Require Import trace_languages protocols syntax semantics typestate
  copying_typestate copying_soundness.
Set Implicit Arguments.

Definition prerequisite_alphabet (F : finType) := Finite.clone (option F) _.
Definition prerequisite_states (F : finType) := Finite.clone ({set F} * bool)%type _.

Record prerequisite_spec (F : finType) := {
  prerequisite_guard : {set F} -> bool;
  prerequisite_guard_up : forall xs ys : {set F}, xs \subset ys ->
    prerequisite_guard xs = true -> prerequisite_guard ys = true;
  prerequisite_witness : {set F};
  prerequisite_witness_valid : prerequisite_guard prerequisite_witness = true
}.

Section Prerequisites.
Variable F : finType.
Variable G : prerequisite_spec F.
Local Notation A := (prerequisite_alphabet F).
Local Notation S := (prerequisite_states F).

Definition prerequisite_initial : S := (set0, false).
Definition prerequisite_le (s t : S) :=
  (s.1 \subset t.1) /\ (s.2 = true -> t.2 = true).
Definition prerequisite_enabled (s : S) (a : A) : bool :=
  match a with Some _ => true | None => prerequisite_guard G s.1 end.
Definition prerequisite_step (s : S) (a : A) : S :=
  match a with Some f => ([set f] :|: s.1, s.2) | None => (s.1, true) end.

Fixpoint prerequisite_run (s : S) (w : list A) : option S :=
  match w with
  | nil => Some s
  | a :: w' => if prerequisite_enabled s a
      then prerequisite_run (prerequisite_step s a) w' else None
  end.

Lemma prerequisite_run_app s u v :
  prerequisite_run s (u ++ v) =
  match prerequisite_run s u with
  | Some t => prerequisite_run t v
  | None => None
  end.
Proof.
  revert s. induction u as [|a u IH]; intros s; simpl; auto.
  destruct (prerequisite_enabled s a); auto.
Qed.

Fixpoint prerequisite_set_list (s : S) (xs : seq F) : S :=
  match xs with
  | nil => s
  | f :: rest => prerequisite_set_list (prerequisite_step s (Some f)) rest
  end.

Lemma prerequisite_set_list_extends (s : S) (xs : seq F) :
  s.1 \subset (prerequisite_set_list s xs).1.
Proof.
  revert s. induction xs as [|f xs IH]; intros s; simpl.
  - apply subxx.
  - eapply subset_trans; [|apply IH]. apply subsetUr.
Qed.

Lemma prerequisite_set_list_contains (s : S) (xs : seq F) (f : F) :
  f \in xs -> f \in (prerequisite_set_list s xs).1.
Proof.
  revert s. induction xs as [|g xs IH]; intros s H; first by rewrite in_nil in H.
  rewrite in_cons in H. move/orP: H => [/eqP E|H].
  - subst g. apply (subsetP (prerequisite_set_list_extends
      (prerequisite_step s (Some f)) xs)).
    by rewrite /prerequisite_step /= in_setU in_set1 eqxx.
  - exact (IH _ H).
Qed.

Lemma prerequisite_run_sets s xs :
  prerequisite_run s (map (@Some F) xs) = Some (prerequisite_set_list s xs).
Proof. revert s. induction xs; intros s; simpl; auto. Qed.

Definition prerequisite_accept (w : list A) : bool :=
  match prerequisite_run prerequisite_initial w with
  | Some s => s.2 | None => false
  end.
Definition prerequisite_viable (w : list A) : bool :=
  match prerequisite_run prerequisite_initial w with
  | Some _ => true | None => false
  end.

Lemma prerequisite_viable_spec w :
  prerequisite_viable w = true <->
  exists v, prerequisite_accept (w ++ v) = true.
Proof.
  unfold prerequisite_viable, prerequisite_accept.
  setoid_rewrite prerequisite_run_app.
  destruct (prerequisite_run prerequisite_initial w) as [s|] eqn:E.
  - split; [|auto]. intros _.
    exists (map (@Some F) (enum F) ++ [::None]).
    rewrite prerequisite_run_app prerequisite_run_sets. simpl.
    assert (Hguard : prerequisite_guard G
      (prerequisite_set_list s (enum F)).1 = true).
    { eapply prerequisite_guard_up; [|apply prerequisite_witness_valid].
      apply/subsetP. intros f Hf. apply prerequisite_set_list_contains.
      apply mem_enum. }
    now rewrite Hguard.
  - split; [discriminate|]. intros [v H]. discriminate.
Qed.

Definition prerequisite_protocol : protocol_family A :=
  {| accepts := fun _ => prerequisite_accept;
     viable := fun _ => prerequisite_viable;
     viable_spec := fun _ => prerequisite_viable_spec |}.

End Prerequisites.

Definition all_prerequisites (F : finType) (required : {set F}) : prerequisite_spec F.
Proof.
  refine {| prerequisite_guard := fun acquired => required \subset acquired;
            prerequisite_witness := required |}.
  - intros xs ys Hxy H. exact (subset_trans H Hxy).
  - apply subxx.
Defined.

Definition any_prerequisites (F : finType) (required : {set F})
    (nonempty : required != set0) : prerequisite_spec F.
Proof.
  refine {| prerequisite_guard := fun acquired =>
              [exists f : F, (f \in required) && (f \in acquired)];
            prerequisite_witness := required |}.
  - intros xs ys Hxy H. move/existsP: H => [f /andP [Hf Hx]].
    apply/existsP. exists f. apply/andP; split; [exact Hf|].
    exact (subsetP Hxy f Hx).
  - move/set0Pn: nonempty => [f Hf]. apply/existsP.
    exists f. by rewrite Hf.
Defined.

(* The shared theorem is imported separately so the executable layer above
   remains independent of its proof strategy. *)
From Accumulation Require Import monotone_protocols.

Section MonotonePrerequisites.
Variable F : finType.
Variable G : prerequisite_spec F.
Local Notation A := (prerequisite_alphabet F).
Local Notation S := (prerequisite_states F).

Definition prerequisite_machine : monotone_machine A S.
Proof.
  refine {| mm_le := @prerequisite_le F;
            mm_enabled := fun s a => prerequisite_enabled G s a = true;
            mm_step := @prerequisite_step F;
            mm_accept := fun s => s.2 = true |}.
  - intros s. split; [apply subxx|auto].
  - intros s t u [Hst Hbst] [Htu Hbtu].
    split; [exact (subset_trans Hst Htu)|auto].
  - intros s t a [Hst Hb] H. destruct a; simpl in *; auto.
    eapply prerequisite_guard_up; eauto.
  - intros s t a [Hst Hb] H. destruct a as [f|]; split; simpl in *; auto.
    apply/subsetP; intros g. rewrite !in_setU; move/orP => [Hg|Hg].
    + by apply/orP; left.
    + apply/orP; right. exact (subsetP Hst g Hg).
  - intros s a H. destruct a as [f|]; split; simpl; auto using subxx.
    apply subsetUr.
  - intros s t [Hst Hb] H. exact (Hb H).
Defined.

Lemma prerequisite_run_spec s w t :
  prerequisite_run G s w = Some t <-> machine_run prerequisite_machine s w t.
Proof.
  split.
  - revert s. induction w as [|a w IH]; intros s H; simpl in H.
    + inversion H; subst. constructor.
    + destruct (prerequisite_enabled G s a) eqn:E; try discriminate.
      constructor; [exact E|]. apply IH. exact H.
  - intros H. induction H; simpl; auto.
    change (prerequisite_enabled G s a = true) in H. now rewrite H.
Qed.

Lemma prerequisite_accept_spec w :
  prerequisite_accept G w = true <->
  machine_language prerequisite_machine (prerequisite_initial F) w.
Proof.
  unfold prerequisite_accept, machine_language.
  split.
  - destruct (prerequisite_run G (prerequisite_initial F) w) as [s|] eqn:E;
      try discriminate.
    intros H. exists s. split; [now apply prerequisite_run_spec|exact H].
  - intros [s [Hrun Haccept]]. apply prerequisite_run_spec in Hrun.
    rewrite Hrun. exact Haccept.
Qed.

Lemma prerequisite_protocol_certified : certified (prerequisite_protocol G).
Proof.
  intros c u v w Hu Hv Hshuffle.
  apply prerequisite_accept_spec.
  eapply machine_language_shuffle_closed.
  - apply prerequisite_accept_spec. exact Hu.
  - apply prerequisite_accept_spec. exact Hv.
  - exact Hshuffle.
Qed.

Lemma prerequisite_protocol_residuals c :
  residual_shuffle_closed (protocol (prerequisite_protocol G) c).
Proof.
  intros p u v w Hu Hv Hshuffle.
  apply prerequisite_accept_spec.
  eapply (@machine_language_residual_shuffle_closed A S prerequisite_machine
    (prerequisite_initial F) p u v w).
  - apply prerequisite_accept_spec. exact Hu.
  - apply prerequisite_accept_spec. exact Hv.
  - exact Hshuffle.
Qed.

Lemma prerequisite_protocol_copying_certified mode :
  copying_certified (prerequisite_protocol G) mode.
Proof.
  split; [apply prerequisite_protocol_certified|].
  intros c _. apply prerequisite_protocol_residuals.
Qed.

Theorem prerequisite_checked_prefix FT mode s m :
  check_program_with_copy (prerequisite_protocol G) FT mode s = true ->
  program_prefix s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
    prefix_language (protocol (prerequisite_protocol G) (classes m l))
      (object_history m l).
Proof.
  eapply copying_program_prefix_sound.
  apply prerequisite_protocol_copying_certified.
Qed.

Theorem prerequisite_checked_completion FT mode s m :
  check_program_with_copy (prerequisite_protocol G) FT mode s = true ->
  program_execution s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
    protocol (prerequisite_protocol G) (classes m l) (object_history m l).
Proof.
  eapply copying_program_completion_sound.
  apply prerequisite_protocol_copying_certified.
Qed.
End MonotonePrerequisites.

(* Finite states give a regular expression whose pumping closure is exactly
   the executable protocol, with both seed and residual certificates. *)
From RegLang Require Import dfa regexp.
From Accumulation Require Import monotone_regular regular_protocols certification
  residual_certification.

Section RegularPrerequisites.
Variable F : finType.
Variable G : prerequisite_spec F.
Local Notation A := (prerequisite_alphabet F).
Local Notation S := (prerequisite_states F).

Definition prerequisite_completeb (s : S) := s.2.
Lemma prerequisite_enabled_spec s a :
  prerequisite_enabled G s a = true <-> mm_enabled (prerequisite_machine G) s a.
Proof. reflexivity. Qed.
Lemma prerequisite_completeb_spec s :
  prerequisite_completeb s = true <-> mm_accept (prerequisite_machine G) s.
Proof. reflexivity. Qed.

Definition prerequisite_regex : regexp A :=
  @machine_regex A S (prerequisite_machine G) (prerequisite_enabled G)
    prerequisite_completeb (prerequisite_initial F).

Theorem prerequisite_language_regular c :
  regular (protocol (prerequisite_protocol G) c).
Proof.
  destruct (@finite_machine_language_regular A S (prerequisite_machine G)
    (prerequisite_enabled G) prerequisite_completeb prerequisite_enabled_spec
    prerequisite_completeb_spec (prerequisite_initial F)) as [D HD].
  exists D. intros w.
  change (prerequisite_accept G w = true <-> w \in dfa_lang D).
  rewrite prerequisite_accept_spec. apply HD.
Qed.

Theorem prerequisite_regex_certificate : @certify_regex A prerequisite_regex = true.
Proof.
  exact (@finite_machine_seed_certificate A S None (prerequisite_machine G)
    (prerequisite_enabled G) prerequisite_completeb prerequisite_enabled_spec
    prerequisite_completeb_spec (prerequisite_initial F)).
Qed.

Theorem prerequisite_regex_copying_certificate :
  @certify_copying_regex A prerequisite_regex = true.
Proof.
  exact (@finite_machine_copying_certificate A S None (prerequisite_machine G)
    (prerequisite_enabled G) prerequisite_completeb prerequisite_enabled_spec
    prerequisite_completeb_spec (prerequisite_initial F)).
Qed.

Theorem prerequisite_regular_family_exact c w :
  protocol (@regular_family A (fun _ => prerequisite_regex)) c w <->
  protocol (prerequisite_protocol G) c w.
Proof.
  rewrite (@finite_machine_regular_family_language A S None (prerequisite_machine G)
    (prerequisite_enabled G) prerequisite_completeb prerequisite_enabled_spec
    prerequisite_completeb_spec (prerequisite_initial F) c w).
  symmetry. apply prerequisite_accept_spec.
Qed.
End RegularPrerequisites.
