(* Finite-state presentation of the threshold family.  The counter has
   exactly N+1 possible values; the additional bit records completion. *)
From Coq Require Import List Arith Bool Lia.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa regexp.
From Accumulation Require Import trace_languages protocols threshold_patterns
  monotone_protocols monotone_regular monotone_pumping pumping
  certification regular_protocols residual_certification.
Set Implicit Arguments.
Local Notation B := (Finite.clone bool _).

Definition threshold_finite_state N := Finite.clone ('I_(S N) * bool)%type _.

Definition threshold_ordinal_next N (n : 'I_(S N)) : 'I_(S N).
Proof.
  refine (@Ordinal (S N) (threshold_next N n) _).
  apply/ltP. apply Nat.lt_succ_r. apply threshold_next_bounded.
  have H := elimT ltP (ltn_ord n). simpl in H. lia.
Defined.

Definition threshold_embed N (s : threshold_finite_state N) : threshold_state :=
  (nat_of_ord s.1,s.2).

Definition threshold_finite_step N (s : threshold_finite_state N) (a : bool) :
    threshold_finite_state N :=
  if a then (s.1,true) else (threshold_ordinal_next s.1,s.2).

Lemma threshold_embed_step N (s : threshold_finite_state N) a :
  threshold_embed (threshold_finite_step s a) =
  mm_step (threshold_machine N) (threshold_embed s) a.
Proof. by case: a; case: s. Qed.

Definition threshold_finite_machine N :
    monotone_machine B (threshold_finite_state N).
Proof.
  refine {| mm_le := fun s t =>
              mm_le (threshold_machine N) (threshold_embed s) (threshold_embed t);
            mm_enabled := fun s a =>
              mm_enabled (threshold_machine N) (threshold_embed s) a;
            mm_step := @threshold_finite_step N;
            mm_accept := fun s => mm_accept (threshold_machine N) (threshold_embed s) |}.
  - intros s; apply mm_refl.
  - intros s t u Hst Htu; eapply mm_trans; eassumption.
  - intros s t a Hst Ha; eapply mm_enabled_up; eassumption.
  - intros s t a Hst Ha. rewrite !threshold_embed_step.
    eapply mm_step_mono; eassumption.
  - intros s a Ha. rewrite threshold_embed_step. eapply mm_step_inflationary; eassumption.
  - intros s t Hst Ha; eapply mm_accept_up; eassumption.
Defined.

Lemma threshold_finite_run_embed N s w t :
  machine_run (threshold_finite_machine N) s w t ->
  machine_run (threshold_machine N) (threshold_embed s) w (threshold_embed t).
Proof.
  intros H; induction H.
  - constructor.
  - econstructor; [exact H|].
    rewrite <- threshold_embed_step. exact IHmachine_run.
Qed.

Lemma threshold_run_lift N w s t :
  machine_run (threshold_machine N) (threshold_embed s) w t ->
  exists u, machine_run (threshold_finite_machine N) s w u /\ threshold_embed u = t.
Proof.
  revert s t; induction w as [|a w IH]; intros s t H.
  - inversion H; subst. exists s; split; [constructor|reflexivity].
  - inversion H as [|s0 a0 w0 t0 Hen Htail]; subst.
    rewrite <- threshold_embed_step in Htail.
    destruct (IH _ _ Htail) as [u [Hu Heq]].
    exists u; split; [econstructor; eassumption|exact Heq].
Qed.

Definition threshold_finite_initial N : threshold_finite_state N := (ord0,false).

Theorem threshold_finite_language N c w :
  protocol (threshold_family N) c w <->
  machine_language (threshold_finite_machine N) (threshold_finite_initial N) w.
Proof.
  rewrite threshold_machine_language. split.
  - intros [t [Hr Ha]].
    change (machine_run (threshold_machine N)
      (threshold_embed (threshold_finite_initial N)) w t) in Hr.
    destruct (threshold_run_lift Hr) as [u [Hu Heq]].
    exists u; split; [exact Hu|].
    change (mm_accept (threshold_machine N) (threshold_embed u)). now rewrite Heq.
  - intros [u [Hu Ha]]. exists (threshold_embed u); split.
    + exact (threshold_finite_run_embed Hu).
    + exact Ha.
Qed.

Definition threshold_enabledb N (s : threshold_finite_state N) (a : bool) :=
  if a then Nat.leb N (nat_of_ord s.1) else true.
Definition threshold_completeb N (s : threshold_finite_state N) := s.2.

Lemma threshold_enabledb_spec N s a :
  threshold_enabledb s a = true <-> mm_enabled (threshold_finite_machine N) s a.
Proof. case: a; simpl; [apply Nat.leb_le|tauto]. Qed.

Lemma threshold_completeb_spec N s :
  threshold_completeb s = true <-> mm_accept (threshold_finite_machine N) s.
Proof. reflexivity. Qed.

Theorem threshold_regular N c : @regular B (protocol (threshold_family N) c).
Proof.
  destruct (@finite_machine_language_regular B (threshold_finite_state N)
    (threshold_finite_machine N) (@threshold_enabledb N) (@threshold_completeb N)
    (@threshold_enabledb_spec N) (@threshold_completeb_spec N)
    (threshold_finite_initial N)) as [D HD].
  exists D; intros w. rewrite threshold_finite_language. exact (HD w).
Qed.

Definition threshold_regex N :=
  @machine_regex B (threshold_finite_state N) (threshold_finite_machine N)
    (@threshold_enabledb N) (@threshold_completeb N) (threshold_finite_initial N).

Theorem threshold_regex_language N c w :
  (w \in threshold_regex N) <-> protocol (threshold_family N) c w.
Proof.
  rewrite threshold_finite_language. apply machine_regex_language;
    [apply threshold_enabledb_spec|apply threshold_completeb_spec].
Qed.

Theorem threshold_seed_certificate N : @certify_regex B (threshold_regex N) = true.
Proof.
  exact (@finite_machine_seed_certificate B (threshold_finite_state N) false
    (threshold_finite_machine N) (@threshold_enabledb N) (@threshold_completeb N)
    (@threshold_enabledb_spec N) (@threshold_completeb_spec N)
    (threshold_finite_initial N)).
Qed.

Theorem threshold_copying_certificate N :
  @certify_copying_regex B (threshold_regex N) = true.
Proof.
  exact (@finite_machine_copying_certificate B (threshold_finite_state N) false
    (threshold_finite_machine N) (@threshold_enabledb N) (@threshold_completeb N)
    (@threshold_enabledb_spec N) (@threshold_completeb_spec N)
    (threshold_finite_initial N)).
Qed.

Theorem threshold_regular_family_exact N c w :
  protocol (@regular_family B (fun _ => threshold_regex N)) c w <->
  protocol (threshold_family N) c w.
Proof.
  rewrite threshold_finite_language.
  exact (@finite_machine_regular_family_language B (threshold_finite_state N) false
    (threshold_finite_machine N) (@threshold_enabledb N) (@threshold_completeb N)
    (@threshold_enabledb_spec N) (@threshold_completeb_spec N)
    (threshold_finite_initial N) c w).
Qed.

Definition threshold_seed N := repeat false N ++ [:: true].

Theorem threshold_singleton_seed_exact N c w : Nat.lt 0 N ->
  @pumping_closure B false (pred1 (threshold_seed N)) w <->
  protocol (threshold_family N) c w.
Proof.
  intros HN; split.
  - intros H. apply threshold_machine_language.
    eapply (@machine_language_pumping_closure B false threshold_state
      (threshold_machine N) (0,false) (pred1 (threshold_seed N))); [|exact H].
    intros u Hu. move/eqP: Hu => Hu; subst u.
    exact (proj1 (threshold_machine_language N c (threshold_seed N))
      (threshold_complete_word N c)).
  - intros H. apply threshold_language_shape in H.
    destruct H as [k [v [-> Hk]]].
    assert (Hfalse : false \in repeat false N).
    { destruct N as [|n]; [lia|reflexivity]. }
    assert (Hall : all (fun a => a \in repeat false N) (repeat false (Nat.sub k N))).
    { apply/allP; intros a Ha. apply mem_list_in in Ha.
      apply repeat_spec in Ha; subst a; exact Hfalse. }
    pose proof (@pumping_insert_block_after_prefix B false (repeat false N)
      (repeat false (Nat.sub k N)) [::true] Hall) as Hcount.
    assert (Ecount : repeat false N ++ repeat false (Nat.sub k N) = repeat false k).
    { rewrite <- repeat_app. f_equal. lia. }
    rewrite catA Ecount in Hcount.
    assert (Hsymbols : all (fun a => a \in repeat false k ++ [::true]) v).
    { apply/allP; intros a _. destruct a.
      - rewrite mem_cat inE eq_refl orbT. reflexivity.
      - rewrite mem_cat. apply/orP; left.
        destruct k as [|k]; [lia|reflexivity]. }
    pose proof (@pumping_insert_block_after_prefix B false
      (repeat false k ++ [::true]) v [::] Hsymbols) as Htail.
    rewrite !cats0 in Htail. rewrite <- catA in Htail.
    exact (@pumping_closure_lift_closure B false (pred1 (threshold_seed N))
      (repeat false k ++ [::true]) (repeat false k ++ true :: v) Hcount Htail).
Qed.

Lemma threshold_two_event_seed_pumps (a b : bool) k v : a <> b -> Nat.lt 0 k ->
  @pumping_closure B false (pred1 [::a;b]) (repeat a k ++ b :: v).
Proof.
  intros Hab Hk; destruct k as [|k]; [lia|].
  assert (Hall : all (fun x => x \in [::a]) (repeat a k)).
  { apply/allP; intros x Hx. apply mem_list_in in Hx.
    apply repeat_spec in Hx; subst x. now rewrite inE eq_refl. }
  pose proof (@pumping_insert_block_after_prefix B false [::a]
    (repeat a k) [::b] Hall) as Hprefix.
  assert (Hsymbols : all (fun x => x \in repeat a (S k) ++ [::b]) v).
  { apply/allP; intros x _. rewrite mem_cat. apply/orP.
    destruct (Bool.bool_dec x a) as [->|Hxa].
    - left. apply mem_list_in. simpl; now left.
    - right. assert (x = b) by (destruct x,a,b; congruence).
      subst x. now rewrite inE eq_refl. }
  pose proof (@pumping_insert_block_after_prefix B false
    (repeat a (S k) ++ [::b]) v [::] Hsymbols) as Htail.
  rewrite !cats0 in Htail. rewrite <- catA in Htail.
  exact (@pumping_closure_lift_closure B false (pred1 [::a;b])
    (repeat a (S k) ++ [::b]) (repeat a (S k) ++ b :: v) Hprefix Htail).
Qed.

Lemma threshold_first_increment w : List.In false w ->
  exists k v, w = repeat true k ++ false :: v.
Proof.
  induction w as [|a w IH]; simpl; [tauto|]. destruct a.
  - intros [H|Hin]; [discriminate|].
    destruct (IH Hin) as [k [v ->]]. exists (S k),v; reflexivity.
  - intros _; exists 0,w; reflexivity.
Qed.

Definition threshold_zero_seeds := [:: [::true]; [::false;true]; [::true;false]].

Theorem threshold_zero_seeds_exact c w :
  @pumping_closure B false (@seed_language B threshold_zero_seeds) w <->
  protocol (threshold_family 0) c w.
Proof.
  split.
  - intros H. apply threshold_machine_language.
    eapply (@machine_language_pumping_closure B false threshold_state
      (threshold_machine 0) (0,false) (@seed_language B threshold_zero_seeds)); [|exact H].
    intros u Hu. change (is_true (u \in threshold_zero_seeds)) in Hu.
    apply mem_list_in in Hu. unfold threshold_zero_seeds in Hu; simpl in Hu.
    destruct Hu as [<-|[<-|[<-|Hbad]]]; try contradiction;
      apply (proj1 (threshold_machine_language 0 c _)); reflexivity.
  - intros H. apply threshold_language_shape in H.
    destruct H as [k [v [-> Hk]]]. destruct k as [|k].
    + simpl. destruct (List.in_dec Bool.bool_dec false v) as [Hin|Hnone].
      * destruct (threshold_first_increment v Hin) as [j [z ->]].
        eapply (@pumping_closure_lift_singleton B false
          (@seed_language B threshold_zero_seeds) [::true;false]); [reflexivity|].
        change (@pumping_closure B false (pred1 [::true;false])
          (repeat true (S j) ++ false :: z)).
        apply threshold_two_event_seed_pumps; [discriminate|lia].
      * assert (Hall : all (fun a => a \in [::true]) v).
        { apply/allP; intros a Ha. destruct a; [reflexivity|].
          exfalso; apply Hnone. now apply mem_list_in. }
        pose proof (@pumping_insert_block_after_prefix B false [::true] v [::] Hall) as Hp.
        rewrite !cats0 in Hp. simpl in Hp.
        eapply (@pumping_closure_lift_singleton B false
          (@seed_language B threshold_zero_seeds) [::true]); [reflexivity|exact Hp].
    + eapply (@pumping_closure_lift_singleton B false
        (@seed_language B threshold_zero_seeds) [::false;true]); [reflexivity|].
      apply threshold_two_event_seed_pumps; [discriminate|lia].
Qed.
