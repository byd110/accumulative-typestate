(* Semantic invariant and preservation helpers for the programming language. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import syntax trace_languages protocols semantics typestate.
Import ListNotations.
Set Implicit Arguments.

Section Invariants.
Context {A : Type} (P : protocol_family A) (FT : class -> field -> class).

Record invariant (m : machine A) (g : environment A) : Prop := {
  inv_refs : forall x e, get (refs m) x = Some e -> e < next_epoch m;
  inv_unique : forall x y e, get (refs m) x = Some e -> get (refs m) y = Some e -> x = y;
  inv_owners : forall e, e < next_epoch m -> owners m e < next_loc m;
  inv_objects : forall l, l < next_loc m -> exists e, e < next_epoch m /\ owners m e = l;
  inv_events : forall e a, In (e,a) (events m) -> e < next_epoch m;
  inv_heap : forall l f t, heap m l f = Some t ->
    l < next_loc m /\ t < next_loc m /\ classes m t = FT (classes m l) f;
  inv_agree : forall x,
    option_map (fun e => (classes m (owners m e), project e (events m)))
      (get (refs m) x) = get g x;
  inv_viable : forall x c w, get g x = Some (c,w) -> viable P c w = true;
  inv_retired : forall e, e < next_epoch m ->
    (forall x, get (refs m) x <> Some e) ->
    accepts P (classes m (owners m e)) (project e (events m)) = true
}.

Lemma invariant_initial : invariant initial_machine [].
Proof.
  constructor; simpl; intros; try discriminate; try contradiction; try lia; reflexivity.
Qed.

Lemma agree_ref m g x e : invariant m g -> get (refs m) x = Some e ->
  get g x = Some (classes m (owners m e), project e (events m)).
Proof. intros H E. rewrite <- (inv_agree H x), E. reflexivity. Qed.

Lemma retirement_evidence m g x e : invariant m g -> retirable P g x = true ->
  get (refs m) x = Some e ->
  accepts P (classes m (owners m e)) (project e (events m)) = true.
Proof.
  intros H Hr He. unfold retirable in Hr.
  rewrite <- (inv_agree H x), He in Hr. exact Hr.
Qed.

Lemma invariant_install m g x l n cs c :
  invariant m g -> retirable P g x = true -> viable P c [] = true ->
  next_loc m <= n ->
  (forall q, q < next_loc m -> cs q = classes m q) ->
  l < n -> cs l = c ->
  (forall q, q < n -> q < next_loc m \/ q = l) ->
  invariant (install m x l n cs) (put g x (Some (c,[]))).
Proof.
  intros HI HR HV Hle Hcs Hl Hlc Hworld.
  assert (Hold : forall e, e < next_epoch m ->
    cs (update (owners m) (next_epoch m) l e) = classes m (owners m e)).
  { intros e He; rewrite update_other by lia. apply Hcs. now apply (inv_owners HI). }
  assert (Hfresh : project (next_epoch m) (events m) = []).
  { apply project_absent; intros i a Hin. pose proof (inv_events HI i a Hin); lia. }
  constructor; cbn [install refs next_epoch next_loc owners classes heap events].
  - intros y e He; destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite get_put_same in He; inversion He; lia.
    + rewrite get_put_other in He by exact Hne. pose proof (inv_refs HI _ He); lia.
  - intros y z e Hy Hz.
    destruct (Nat.eq_dec y x) as [->|Hyx]; destruct (Nat.eq_dec z x) as [->|Hzx]; auto.
    + rewrite get_put_same in Hy; inversion Hy; subst e.
      rewrite get_put_other in Hz by exact Hzx. pose proof (inv_refs HI _ Hz); lia.
    + rewrite get_put_same in Hz; inversion Hz; subst e.
      rewrite get_put_other in Hy by exact Hyx. pose proof (inv_refs HI _ Hy); lia.
    + rewrite get_put_other in Hy by exact Hyx; rewrite get_put_other in Hz by exact Hzx.
      eapply inv_unique; eauto.
  - intros e He; destruct (Nat.eq_dec e (next_epoch m)) as [->|Hne].
    + now rewrite update_same.
    + rewrite update_other by exact Hne. pose proof (inv_owners HI (e:=e) ltac:(lia)); lia.
  - intros q Hq; destruct (Hworld q Hq) as [Hqold | ->].
    + destruct (inv_objects HI Hqold) as [e [He Ho]].
      exists e; split; [lia|rewrite update_other by lia; exact Ho].
    + exists (next_epoch m); split; [lia|apply update_same].
  - intros e a Hin; pose proof (inv_events HI e a Hin); lia.
  - intros q f t Ht; destruct (inv_heap HI q f Ht) as [Hq [Ht' HC]].
    repeat split; try lia. rewrite (Hcs t Ht'), (Hcs q Hq); exact HC.
  - intros y; destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite !get_put_same; simpl. rewrite update_same, Hlc, Hfresh; reflexivity.
    + rewrite !get_put_other by exact Hne. rewrite <- (inv_agree HI y).
      destruct (get (refs m) y) as [e|] eqn:E; simpl; auto.
      rewrite Hold; [reflexivity|eapply inv_refs; eauto].
  - intros y d w E; destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite get_put_same in E; inversion E; subst; exact HV.
    + rewrite get_put_other in E by exact Hne; eapply inv_viable; eauto.
  - intros e He Hdead. assert (Hene : e <> next_epoch m).
    { intros ->; specialize (Hdead x); rewrite get_put_same in Hdead; contradiction. }
    assert (Heold : e < next_epoch m) by lia. rewrite (Hold e Heold).
    destruct (get (refs m) x) as [d|] eqn:Ex.
    + destruct (Nat.eq_dec d e) as [->|Hde].
      * eapply retirement_evidence; eauto.
      * apply (inv_retired HI Heold); intros y Ey.
        destruct (Nat.eq_dec y x) as [->|Hne]; [congruence|].
        apply (Hdead y). rewrite get_put_other by exact Hne; exact Ey.
    + apply (inv_retired HI Heold); intros y Ey.
      destruct (Nat.eq_dec y x) as [->|Hne]; [congruence|].
      apply (Hdead y). rewrite get_put_other by exact Hne; exact Ey.
Qed.

Lemma invariant_allocate m g x c : invariant m g ->
  retirable P g x = true -> viable P c [] = true ->
  invariant (allocate m x c) (put g x (Some (c,[]))).
Proof.
  intros HI HR HV; unfold allocate; eapply invariant_install; eauto; try lia.
  - intros q Hq; apply update_other; lia.
  - apply update_same.
Qed.

Lemma invariant_bind m g x l : invariant m g -> retirable P g x = true ->
  l < next_loc m -> viable P (classes m l) [] = true ->
  invariant (bind m x l) (put g x (Some (classes m l,[]))).
Proof. intros; unfold bind; eapply invariant_install; eauto. Qed.

Lemma invariant_emit m g x e a : invariant m g -> get (refs m) x = Some e ->
  viable P (classes m (owners m e)) (project e (events m) ++ [a]) = true ->
  invariant (emit m e a)
    (put g x (Some (classes m (owners m e), project e (events m) ++ [a]))).
Proof.
  intros HI Ex HV. constructor; cbn [emit refs next_epoch next_loc owners classes heap events].
  - exact (inv_refs HI).
  - exact (inv_unique HI).
  - exact (inv_owners HI).
  - exact (inv_objects HI).
  - intros d b Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    + eapply inv_events; eauto.
    + simpl in Hin; destruct Hin as [E|[]]; inversion E; subst; eapply inv_refs; eauto.
  - exact (inv_heap HI).
  - intros y; destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite get_put_same, Ex; simpl. rewrite project_snoc, Nat.eqb_refl; reflexivity.
    + rewrite get_put_other by exact Hne. rewrite <- (inv_agree HI y).
      destruct (get (refs m) y) as [d|] eqn:Ey; simpl; auto.
      assert (Hde : d <> e).
      { intros ->; apply Hne; eapply inv_unique; eauto. }
      rewrite project_snoc. rewrite (proj2 (Nat.eqb_neq e d) ltac:(congruence)); reflexivity.
  - intros y c w E; destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite get_put_same in E; inversion E; subst; exact HV.
    + rewrite get_put_other in E by exact Hne; eapply inv_viable; eauto.
  - intros d Hd Hdead. assert (Hde : e <> d) by (intros ->; exact (Hdead x Ex)).
    rewrite project_snoc, (proj2 (Nat.eqb_neq e d) Hde).
    eapply inv_retired; eauto.
Qed.

Lemma invariant_retire m g x e : invariant m g -> get (refs m) x = Some e ->
  accepts P (classes m (owners m e)) (project e (events m)) = true ->
  invariant (retire m x) (put g x None).
Proof.
  intros HI Ex HA. constructor; cbn [retire refs next_epoch next_loc owners classes heap events].
  - intros y d Ey; destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite get_put_same in Ey; discriminate.
    + rewrite get_put_other in Ey by exact Hne; eapply inv_refs; eauto.
  - intros y z d Ey Ez.
    destruct (Nat.eq_dec y x) as [->|Hy]; [rewrite get_put_same in Ey; discriminate|].
    destruct (Nat.eq_dec z x) as [->|Hz]; [rewrite get_put_same in Ez; discriminate|].
    rewrite get_put_other in Ey by exact Hy; rewrite get_put_other in Ez by exact Hz.
    eapply inv_unique; eauto.
  - exact (inv_owners HI).
  - exact (inv_objects HI).
  - exact (inv_events HI).
  - exact (inv_heap HI).
  - intros y; destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite !get_put_same; reflexivity.
    + rewrite !get_put_other by exact Hne; apply inv_agree; exact HI.
  - intros y c w E; destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite get_put_same in E; discriminate.
    + rewrite get_put_other in E by exact Hne; eapply inv_viable; eauto.
  - intros d Hd Hdead; destruct (Nat.eq_dec d e) as [->|Hne]; auto.
    apply (inv_retired HI Hd); intros y Ey.
    destruct (Nat.eq_dec y x) as [->|Hy]; [congruence|].
    apply (Hdead y); rewrite get_put_other by exact Hy; exact Ey.
Qed.

Lemma invariant_store m g l f t : invariant m g ->
  l < next_loc m -> t < next_loc m -> classes m t = FT (classes m l) f ->
  invariant (store m l f t) g.
Proof.
  intros HI Hl Ht HC. constructor; cbn [store refs next_epoch next_loc owners classes heap events];
    try solve [eapply inv_refs; eauto | eapply inv_unique; eauto |
    eapply inv_owners; eauto | eapply inv_objects; eauto | eapply inv_events; eauto |
    eapply inv_agree; eauto | eapply inv_viable; eauto | eapply inv_retired; eauto].
  intros q h v E. destruct (q =? l) eqn:Eq.
  - apply Nat.eqb_eq in Eq; subst q.
    destruct (Nat.eq_dec h f) as [->|Hne].
    + rewrite update_same in E; inversion E; subst; auto.
    + rewrite update_other in E by exact Hne; eapply inv_heap; eauto.
  - eapply inv_heap; eauto.
Qed.

Lemma preservation m g i m' g' : invariant m g ->
  raw_step i m m' -> type_step P FT g i g' -> invariant m' g'.
Proof.
  intros HI HR HT. destruct HR; inversion HT; subst; unfold qualifier, class in *.
  - eapply invariant_allocate; eauto.
  - match goal with E : get ?env y = Some (_,_) |- _ =>
      let Eq := fresh "Eagree" in pose proof (agree_ref _ HI H) as Eq; unfold qualifier, class in Eq; rewrite E in Eq; inversion Eq; subst end.
    eapply invariant_bind; eauto. apply (inv_owners HI); eapply inv_refs; eauto.
  - match goal with E : get ?env y = Some (_,_) |- _ =>
      let Eq := fresh "Eagree" in pose proof (agree_ref _ HI H) as Eq; unfold qualifier, class in Eq; rewrite E in Eq; inversion Eq; subst end.
    destruct (inv_heap HI (owners m e) f H0) as [Hl [Ht HC]].
    rewrite <- HC. eapply invariant_bind; eauto. rewrite HC; assumption.
  - match goal with E : get ?env x = Some (_,_) |- _ =>
      let Eq := fresh "Eagree" in pose proof (agree_ref _ HI H) as Eq; unfold qualifier, class in Eq; rewrite E in Eq; inversion Eq; subst end.
    match goal with E : get ?env y = Some (_,_) |- _ =>
      let Eq := fresh "Eagree" in pose proof (agree_ref _ HI H0) as Eq; unfold qualifier, class in Eq; rewrite E in Eq; inversion Eq; subst end.
    eapply invariant_store; eauto; try (apply (inv_owners HI); eapply inv_refs; eauto).
  - match goal with E : get ?env x = Some (_,_) |- _ =>
      let Eq := fresh "Eagree" in pose proof (agree_ref _ HI H) as Eq; unfold qualifier, class in Eq; rewrite E in Eq; inversion Eq; subst end.
    eapply invariant_emit; eauto.
  - match goal with E : get ?env x = Some (_,_) |- _ =>
      let Eq := fresh "Eagree" in pose proof (agree_ref _ HI H) as Eq; unfold qualifier, class in Eq; rewrite E in Eq; inversion Eq; subst end.
    eapply invariant_retire; eauto.
Qed.

Lemma trace_preservation m g is m' g' : invariant m g ->
  execution is m m' -> typed_trace P FT g is g' -> invariant m' g'.
Proof.
  intros HI HE; revert g HI g'; induction HE; intros g HI g' HT; inversion HT; subst; auto.
  eapply IHHE; eauto. eapply preservation; eauto.
Qed.

End Invariants.
