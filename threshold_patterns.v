(* Reusable count thresholds.  false increments a saturated counter;
   true uses the established threshold.  Completion requires at least
   one use, and every use must occur after the threshold was established. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import trace_languages protocols syntax semantics
  typestate copying_typestate soundness copying_soundness monotone_protocols.
Import ListNotations.
Set Implicit Arguments.

Definition threshold_state := (nat * bool)%type.
Definition threshold_next (N n : nat) := if n <? N then S n else n.

Lemma threshold_next_inflationary N n : n <= threshold_next N n.
Proof. unfold threshold_next; destruct (n <? N); lia. Qed.

Lemma threshold_next_monotone N n m :
  n <= m -> threshold_next N n <= threshold_next N m.
Proof.
  intros H; unfold threshold_next; destruct (n <? N) eqn:E;
    destruct (m <? N) eqn:F; try lia.
  apply Nat.ltb_lt in E. apply Nat.ltb_ge in F. lia.
Qed.

Lemma threshold_next_bounded N n : n <= N -> threshold_next N n <= N.
Proof.
  unfold threshold_next; destruct (n <? N) eqn:E;
    try apply Nat.ltb_lt in E; lia.
Qed.

Lemma threshold_next_saturated N : threshold_next N N = N.
Proof. unfold threshold_next; now rewrite Nat.ltb_irrefl. Qed.

Lemma threshold_next_min N n :
  n <= N -> threshold_next N n = Nat.min N (S n).
Proof.
  intros H; unfold threshold_next; destruct (n <? N) eqn:E.
  - apply Nat.ltb_lt in E. rewrite Nat.min_r; lia.
  - apply Nat.ltb_ge in E. rewrite Nat.min_l; lia.
Qed.

Fixpoint threshold_scan (N : nat) (s : threshold_state)
    (w : list bool) : option threshold_state :=
  match w with
  | [] => Some s
  | false :: v => threshold_scan N (threshold_next N (fst s), snd s) v
  | true :: v =>
      if N <=? fst s then threshold_scan N (fst s,true) v else None
  end.

Lemma threshold_scan_app N u v s :
  threshold_scan N s (u ++ v) =
  match threshold_scan N s u with
  | Some t => threshold_scan N t v
  | None => None
  end.
Proof.
  revert s; induction u as [|a u IH]; intros [n b]; simpl; auto.
  destruct a; simpl; [destruct (N <=? n); simpl; auto|apply IH].
Qed.

Lemma threshold_scan_bounded N w n b m d :
  n <= N -> threshold_scan N (n,b) w = Some (m,d) -> m <= N.
Proof.
  revert n b; induction w as [|a w IH]; intros n b Hn; simpl.
  - intros E; inversion E; subst; assumption.
  - destruct a; simpl.
    + destruct (N <=? n); [eapply IH; exact Hn|discriminate].
    + eapply IH. now apply threshold_next_bounded.
Qed.

Lemma threshold_scan_increments N k n b : n <= N ->
  threshold_scan N (n,b) (repeat false k) =
    Some (Nat.min N (n+k),b).
Proof.
  revert n; induction k as [|k IH]; intros n Hn; simpl.
  - rewrite Nat.add_0_r, Nat.min_r; auto.
  - rewrite IH by (now apply threshold_next_bounded).
    rewrite threshold_next_min by assumption.
    destruct (le_dec N (S n)) as [H|H].
    + rewrite (Nat.min_l N (S n)) by lia.
      rewrite !Nat.min_l; reflexivity || lia.
    + rewrite (Nat.min_r N (S n)) by lia.
      replace (n + S k) with (S n + k) by lia. reflexivity.
Qed.

Lemma threshold_scan_completion N n b : n <= N ->
  threshold_scan N (n,b) (repeat false N ++ [true]) = Some (N,true).
Proof.
  intros Hn. rewrite threshold_scan_app, threshold_scan_increments by assumption.
  rewrite Nat.min_l by lia. simpl. now rewrite Nat.leb_refl.
Qed.

Definition threshold_accept N (_ : nat) (w : list bool) :=
  match threshold_scan N (0,false) w with
  | Some (_,b) => b
  | None => false
  end.
Definition threshold_viable N (_ : nat) (w : list bool) :=
  match threshold_scan N (0,false) w with
  | Some _ => true
  | None => false
  end.

Lemma threshold_queries N c w : threshold_viable N c w = true <->
  exists v, threshold_accept N c (w ++ v) = true.
Proof.
  unfold threshold_viable, threshold_accept.
  destruct (threshold_scan N (0,false) w) as [[n b]|] eqn:E.
  - split; intros _.
    + exists (repeat false N ++ [true]).
      rewrite threshold_scan_app, E, threshold_scan_completion; [reflexivity|].
      eapply threshold_scan_bounded; [|exact E]. lia.
    + reflexivity.
  - split; [discriminate|]. intros [v H].
    rewrite threshold_scan_app, E in H. discriminate.
Qed.

Definition threshold_family N : protocol_family bool :=
  {| accepts := threshold_accept N;
     viable := threshold_viable N;
     viable_spec := threshold_queries N |}.

Definition threshold_machine (N : nat) : monotone_machine bool threshold_state.
Proof.
  refine {| mm_le := fun s t : threshold_state => fst s <= fst t /\
                                (snd s = true -> snd t = true);
            mm_enabled := fun (s : threshold_state) (a : bool) => if a then N <= fst s else True;
            mm_step := fun (s : threshold_state) (a : bool) =>
              if a then (fst s,true) else (threshold_next N (fst s),snd s);
            mm_accept := fun s => snd s = true |}.
  - intros [n b]; simpl; auto.
  - intros [n b] [m c] [k d]; simpl; intuition lia.
  - intros [n b] [m c] [|]; simpl; intuition lia.
  - intros [n b] [m c] [|]; simpl; intros [Hnm Hbc] _; split; auto.
    now apply threshold_next_monotone.
  - intros [n b] [|]; simpl; intros _; split; auto using threshold_next_inflationary.
  - intros [n b] [m c]; simpl; tauto.
Defined.

Lemma threshold_run_scan N s w t :
  machine_run (threshold_machine N) s w t -> threshold_scan N s w = Some t.
Proof.
  intros H; induction H; [reflexivity|].
  destruct a; cbn [threshold_scan threshold_machine] in *.
  - apply Nat.leb_le in H. now rewrite H.
  - exact IHmachine_run.
Qed.

Lemma threshold_scan_run N w s t :
  threshold_scan N s w = Some t -> machine_run (threshold_machine N) s w t.
Proof.
  revert s t; induction w as [|a w IH]; intros [n b] t; simpl.
  - intros H; inversion H; constructor.
  - destruct a; simpl.
    + destruct (N <=? n) eqn:E; [|discriminate].
      intros H; constructor.
      * apply Nat.leb_le; exact E.
      * now apply IH.
    + intros H; constructor; [exact I|]. now apply IH.
Qed.

Lemma threshold_machine_language N c w :
  protocol (threshold_family N) c w <->
  machine_language (threshold_machine N) (0,false) w.
Proof.
  unfold protocol, threshold_family, threshold_accept, machine_language; simpl.
  split.
  - destruct (threshold_scan N (0,false) w) as [[n b]|] eqn:E; [|discriminate].
    intros H; exists (n,b); split; [now apply threshold_scan_run|exact H].
  - intros [[n b] [Hr Ha]]. rewrite (threshold_run_scan Hr). exact Ha.
Qed.

Theorem threshold_certified N : certified (threshold_family N).
Proof.
  intros c u v w Hu Hv Hsh. apply threshold_machine_language.
  eapply machine_language_shuffle_closed; [| |exact Hsh].
  - exact (proj1 (threshold_machine_language N c u) Hu).
  - exact (proj1 (threshold_machine_language N c v) Hv).
Qed.

Theorem threshold_residual_shuffle_closed N c :
  residual_shuffle_closed (protocol (threshold_family N) c).
Proof.
  intros p u v w Hu Hv Hsh.
  unfold residual in *. apply threshold_machine_language.
  eapply (@machine_language_residual_shuffle_closed bool threshold_state
    (threshold_machine N) (0,false) p u v w); [| |exact Hsh].
  - exact (proj1 (threshold_machine_language N c (p ++ u)) Hu).
  - exact (proj1 (threshold_machine_language N c (p ++ v)) Hv).
Qed.

Theorem threshold_copying_certified N mode : copying_certified (threshold_family N) mode.
Proof.
  split; [apply threshold_certified|]. intros c _. apply threshold_residual_shuffle_closed.
Qed.

Theorem threshold_repeat_insertion N c p a q :
  In a p -> protocol (threshold_family N) c (p ++ q) ->
  protocol (threshold_family N) c (p ++ a :: q).
Proof.
  intros Hin H. apply threshold_machine_language.
  apply machine_language_repeat; [exact Hin|].
  exact (proj1 (threshold_machine_language N c (p ++ q)) H).
Qed.

Theorem threshold_complete_word N c :
  protocol (threshold_family N) c (repeat false N ++ [true]).
Proof.
  unfold protocol, threshold_family, threshold_accept; simpl.
  rewrite threshold_scan_completion; reflexivity || lia.
Qed.

Theorem threshold_early_use_rejected N c w : 0 < N ->
  viable (threshold_family N) c (true :: w) = false.
Proof.
  intros H. unfold threshold_family, threshold_viable; simpl.
  destruct N; [lia|reflexivity].
Qed.

Theorem threshold_repeated_increments_accepted N k c :
  protocol (threshold_family N) c
    ((repeat false N ++ [true]) ++ repeat false k).
Proof.
  unfold protocol, threshold_family, threshold_accept; simpl.
  rewrite threshold_scan_app, threshold_scan_completion by lia.
  rewrite threshold_scan_increments by lia. reflexivity.
Qed.

Lemma threshold_scan_ready N w : threshold_scan N (N,true) w = Some (N,true).
Proof.
  induction w as [|a w IH]; simpl; [reflexivity|].
  destruct a; simpl; rewrite ?Nat.leb_refl, ?threshold_next_saturated; exact IH.
Qed.

Theorem threshold_post_use_operations_accepted N c w :
  protocol (threshold_family N) c ((repeat false N ++ [true]) ++ w).
Proof.
  unfold protocol, threshold_family, threshold_accept; simpl.
  rewrite threshold_scan_app, threshold_scan_completion by lia.
  now rewrite threshold_scan_ready.
Qed.

Theorem threshold_zero_initial_viable c : viable (threshold_family 0) c [] = true.
Proof. reflexivity. Qed.

Theorem threshold_zero_use_complete c : accepts (threshold_family 0) c [true] = true.
Proof. reflexivity. Qed.

Theorem threshold_no_use_incomplete N c k :
  accepts (threshold_family N) c (repeat false k) = false.
Proof.
  unfold threshold_family, threshold_accept; simpl.
  rewrite threshold_scan_increments; reflexivity || lia.
Qed.

Lemma threshold_scan_done N w n b m d :
  threshold_scan N (n,b) w = Some (m,d) -> d = true ->
  b = true \/ In true w.
Proof.
  revert n b; induction w as [|a w IH]; intros n b; simpl.
  - intros E Hd; inversion E; subst; now left.
  - destruct a; simpl.
    + intros _ _; right; now left.
    + intros E Hd. destruct (IH _ _ E Hd) as [Hb|Hin].
      * now left.
      * right; now right.
Qed.

Lemma threshold_first_use w : In true w ->
  exists k v, w = repeat false k ++ true :: v.
Proof.
  induction w as [|a w IH]; simpl; [tauto|].
  destruct a.
  - intros _; exists 0,w; reflexivity.
  - intros [H|Hin]; [discriminate|].
    destruct (IH Hin) as [k [v ->]]. exists (S k),v; reflexivity.
Qed.

Theorem threshold_language_shape N c w :
  protocol (threshold_family N) c w <->
  exists k v, w = repeat false k ++ true :: v /\ N <= k.
Proof.
  split.
  - intros H.
    assert (Hin : In true w).
    { unfold protocol, threshold_family, threshold_accept in H; simpl in H.
      destruct (threshold_scan N (0,false) w) as [[m d]|] eqn:E; [|discriminate].
      destruct (@threshold_scan_done N w 0 false m d E H) as [Hbad|Hin];
        [discriminate|exact Hin]. }
    destruct (threshold_first_use w Hin) as [k [v Hw]]. exists k,v; split; [exact Hw|].
    unfold protocol, threshold_family, threshold_accept in H; simpl in H.
    rewrite Hw, threshold_scan_app, threshold_scan_increments in H by lia.
    simpl in H. destruct (N <=? Nat.min N k) eqn:E; [|discriminate].
    apply Nat.leb_le in E. pose proof (Nat.le_min_r N k). lia.
  - intros [k [v [-> Hk]]].
    unfold protocol, threshold_family, threshold_accept; simpl.
    rewrite threshold_scan_app, threshold_scan_increments by lia.
    simpl. rewrite Nat.min_l by assumption. rewrite Nat.leb_refl, threshold_scan_ready.
    reflexivity.
Qed.

(* Same event sets, different readiness: multiplicity matters. *)
Theorem threshold_counts_not_sets :
  (forall a : bool, In a [false] <-> In a [false;false]) /\
  viable (threshold_family 2) 0 [false;true] = false /\
  accepts (threshold_family 2) 0 [false;false;true] = true.
Proof. split; [intros a; simpl; tauto|]. split; reflexivity. Qed.

Definition threshold_fields (c : class) (_ : field) := c.
Definition threshold_aliases := sequence
  [New 0 0; Copy 1 0; Call 0 false; Call 1 false;
   Call 0 false; Call 1 false; Call 0 true; Call 1 true].

Example threshold_aliases_accepted :
  check_program (threshold_family 2) threshold_fields threshold_aliases = true.
Proof. vm_compute; reflexivity. Qed.

Definition threshold_inherited_aliases := sequence
  [New 0 0; Call 0 false; Call 0 false; Copy 1 0; Call 0 true; Call 1 true].

Example threshold_inherited_aliases_accepted :
  check_program_with_copy (threshold_family 2) threshold_fields
    (fun _ => true) threshold_inherited_aliases = true.
Proof. vm_compute; reflexivity. Qed.

Example threshold_inherited_aliases_need_inheritance :
  check_program (threshold_family 2) threshold_fields threshold_inherited_aliases = false.
Proof. vm_compute; reflexivity. Qed.

Definition threshold_inherited_final : machine bool :=
  let m := allocate initial_machine 0 0 in
  let m := emit m 0 false in
  let m := emit m 0 false in
  let m := bind m 1 0 in
  let m := emit m 0 true in
  let m := emit m 1 true in
  clear_refs m.

Example threshold_inherited_aliases_terminate :
  program_execution threshold_inherited_aliases initial_machine threshold_inherited_final.
Proof.
  unfold threshold_inherited_aliases, threshold_inherited_final.
  apply source_execution_instrument; [reflexivity|]. cbn [sequence].
  repeat (eapply execution_seq;
    [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.

Example threshold_inherited_object_history :
  next_loc threshold_inherited_final = 1 /\
  object_history threshold_inherited_final 0 = [false;false;true;true].
Proof. vm_compute; auto. Qed.

Theorem threshold_aliases_sound m :
  program_execution threshold_aliases initial_machine m ->
  forall l, l < next_loc m ->
  protocol (threshold_family 2) (classes m l) (object_history m l).
Proof.
  apply typestate_completion_sound with threshold_fields;
    [apply threshold_certified|apply threshold_aliases_accepted].
Qed.

Theorem threshold_inherited_aliases_sound m :
  program_execution threshold_inherited_aliases initial_machine m ->
  forall l, l < next_loc m ->
  protocol (threshold_family 2) (classes m l) (object_history m l).
Proof.
  eapply copying_program_completion_sound;
    [apply threshold_copying_certified|apply threshold_inherited_aliases_accepted].
Qed.
