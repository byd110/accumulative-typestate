(* Soundness of optional history copying for the existing raw semantics. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import syntax trace_languages protocols semantics typestate
  invariants copying_typestate copying_languages.
Import ListNotations.
Set Implicit Arguments.

Section CopyingSoundness.
Context {A : Type} (P : protocol_family A) (FT : class -> field -> class).
Variable copy_history : class -> bool.
Hypothesis certified_modes : copying_certified P copy_history.

Definition total_protocol : protocol_family A.
Proof.
  refine {| accepts := fun _ _ => true; viable := fun _ _ => true |}.
  intros c u. split. intros _. exists []. reflexivity. intros _. reflexivity.
Defined.
Lemma total_retirable g x : retirable total_protocol g x = true.
Proof. unfold retirable. destruct (get g x) as [[c w]|]. all: reflexivity. Qed.
Definition shape (m : machine A) := exists h, invariant total_protocol FT m h.
Definition epoch_set (m : machine A) l e := e < next_epoch m /\ owners m e = l.
Record copying_invariant (m : machine A) (g : environment A) (V : nat -> list A) := {
  ci_shape : shape m;
  ci_agree : forall x,
    option_map (fun e => (classes m (owners m e), V e)) (get (refs m) x) = get g x;
  ci_viable : forall e, e < next_epoch m -> viable P (classes m (owners m e)) (V e) = true;
  ci_retired : forall e, e < next_epoch m ->
    (forall x, get (refs m) x <> Some e) -> accepts P (classes m (owners m e)) (V e) = true;
  ci_future : forall l, l < next_loc m ->
    future_safe (protocol P (classes m l)) (epoch_set m l) V (object_history m l)
}.
Lemma ci_ref m g V x e : copying_invariant m g V -> get (refs m) x = Some e ->
  get g x = Some (classes m (owners m e), V e).
Proof. intros H E. rewrite <- (ci_agree H x), E. reflexivity. Qed.
Lemma ci_initial : copying_invariant initial_machine [] (fun _ => []).
Proof.
  constructor.
  - exists []. apply invariant_initial.
  - reflexivity.
  - simpl. intros. lia.
  - simpl. intros. lia.
  - simpl. intros. lia.
Qed.
Lemma install_history m x l n cs q : shape m ->
  object_history (install m x l n cs) q = object_history m q.
Proof.
  intros [h H]. unfold object_history, object_events. simpl.
  f_equal. apply filter_ext_in. intros [e a] Hin. simpl.
  rewrite update_other. reflexivity.
  pose proof (inv_events H e a Hin). lia.
Qed.
Lemma emit_history (m : machine A) e a l :
  object_history (emit m e a) l =
  object_history m l ++ (if owners m e =? l then [a] else []).
Proof.
  unfold object_history, object_events, erase_tags. simpl.
  rewrite filter_app, map_app. simpl. now destruct (owners m e =? l).
Qed.
Lemma absent_object_history m l : shape m -> next_loc m <= l -> object_history m l = [].
Proof.
  intros [h H] Hl. unfold object_history, object_events.
  assert (E : filter (fun p : epoch * A => owners m (fst p) =? l) (events m) = []).
  { destruct (filter (fun p : epoch * A => owners m (fst p) =? l) (events m)) as [|[e a] t] eqn:E.
    reflexivity. exfalso.
    assert (Hin : In (e,a) (filter (fun p : epoch * A => owners m (fst p) =? l) (events m))).
    { rewrite E. now left. }
    apply filter_In in Hin. destruct Hin as [Hin Ho]. simpl in Ho. apply Nat.eqb_eq in Ho.
    pose proof (inv_events H e a Hin) as He.
    pose proof (inv_owners H He). lia. }
  now rewrite E.
Qed.

Lemma ci_install m g V x l n cs c v : copying_invariant m g V ->
  retirable P g x = true -> next_loc m <= n ->
  (forall q, q < next_loc m -> cs q = classes m q) ->
  l < n -> cs l = c ->
  (forall q, q < n -> q < next_loc m \/ q = l) -> viable P c v = true ->
  (forall q, q < n ->
    future_safe (protocol P (cs q)) (epoch_set (install m x l n cs) q)
      (update V (next_epoch m) v) (object_history m q)) ->
  copying_invariant (install m x l n cs) (put g x (Some (c,v))) (update V (next_epoch m) v).
Proof.
  intros HI HR Hle Hcs Hl Hlc Hworld HV HF.
  destruct (ci_shape HI) as [h HS].
  assert (Hold : forall e, e < next_epoch m ->
    cs (update (owners m) (next_epoch m) l e) = classes m (owners m e)).
  { intros e He. rewrite update_other by lia. apply Hcs. now apply (inv_owners HS). }
  constructor.
  - exists (put h x (Some (c,[]))). eapply invariant_install.
    exact HS. apply total_retirable. reflexivity. exact Hle. exact Hcs.
    exact Hl. exact Hlc. exact Hworld.
  - intros y. cbn [install refs classes owners]. destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite !get_put_same. simpl. rewrite !update_same, Hlc. reflexivity.
    + rewrite !get_put_other by exact Hne. rewrite <- (ci_agree HI y).
      destruct (get (refs m) y) as [e|] eqn:E. 2: reflexivity.
      pose proof (inv_refs HS y E) as He. simpl.
      rewrite Hold by exact He. rewrite update_other by lia. reflexivity.
  - intros e He. cbn [install next_epoch classes owners] in *. destruct (Nat.eq_dec e (next_epoch m)) as [->|Hne].
    + now rewrite !update_same, Hlc.
    + rewrite Hold by lia. rewrite update_other by exact Hne. apply (ci_viable HI). lia.
  - intros e He Hdead. cbn [install next_epoch refs classes owners] in *.
    assert (Hne : e <> next_epoch m).
    { intros ->. specialize (Hdead x). rewrite get_put_same in Hdead. contradiction. }
    rewrite Hold by lia. rewrite update_other by exact Hne.
    destruct (get (refs m) x) as [d|] eqn:E.
    + destruct (Nat.eq_dec d e) as [->|Hde].
      * unfold retirable in HR. rewrite (ci_ref x HI E) in HR. exact HR.
      * apply (ci_retired HI). lia. intros y Ey.
        destruct (Nat.eq_dec y x) as [->|Hy]. congruence.
        apply (Hdead y). rewrite get_put_other by exact Hy. exact Ey.
    + apply (ci_retired HI). lia. intros y Ey.
      destruct (Nat.eq_dec y x) as [->|Hy]. congruence.
      apply (Hdead y). rewrite get_put_other by exact Hy. exact Ey.
  - intros q Hq. rewrite install_history by (exists h; exact HS). apply HF. exact Hq.
Qed.

Lemma ci_bind m g V x l v : copying_invariant m g V ->
  retirable P g x = true -> l < next_loc m -> viable P (classes m l) v = true ->
  (forall q, q < next_loc m ->
    future_safe (protocol P (classes m q)) (epoch_set (bind m x l) q)
      (update V (next_epoch m) v) (object_history m q)) ->
  copying_invariant (bind m x l) (put g x (Some (classes m l,v))) (update V (next_epoch m) v).
Proof.
  intros HI HR Hl HV HF. unfold bind in *. eapply ci_install.
  exact HI. exact HR. lia. reflexivity. exact Hl. reflexivity.
  intros q Hq. now left. exact HV. exact HF.
Qed.

Lemma bind_epoch_set (m : machine A) x l q e :
  epoch_set (bind m x l) q e <->
  (e = next_epoch m /\ l = q) \/ epoch_set m q e.
Proof.
  unfold epoch_set, bind, install. simpl.
  destruct (Nat.eq_dec e (next_epoch m)) as [->|Hne].
  - rewrite update_same. intuition lia.
  - rewrite update_other by exact Hne. intuition lia.
Qed.
Lemma ci_fresh_bind m g V x l : copying_invariant m g V ->
  retirable P g x = true -> l < next_loc m -> viable P (classes m l) [] = true ->
  copying_invariant (bind m x l) (put g x (Some (classes m l,[]))) (update V (next_epoch m) []).
Proof.
  intros HI HR Hl HV. apply ci_bind. exact HI. exact HR. exact Hl. exact HV.
  intros q Hq. destruct (Nat.eq_dec l q) as [->|Hne].
  - eapply future_safe_ext with (I := fun e => e = next_epoch m \/ epoch_set m q e).
    + intros e. rewrite bind_epoch_set. tauto.
    + reflexivity.
    + apply future_safe_fresh.
      * exact (proj1 certified_modes (classes m q)).
      * unfold epoch_set. intros [H _]. lia.
      * apply (ci_future HI). exact Hq.
  - eapply future_safe_ext with (I := epoch_set m q) (V := V).
    + intros e. rewrite bind_epoch_set. tauto.
    + intros e [He Ho]. unfold update. rewrite (proj2 (Nat.eqb_neq e (next_epoch m)) ltac:(lia)). reflexivity.
    + apply (ci_future HI). exact Hq.
Qed.

Lemma ci_copy_bind m g V x l s : copying_invariant m g V ->
  retirable P g x = true -> epoch_set m l s -> copy_history (classes m l) = true ->
  copying_invariant (bind m x l) (put g x (Some (classes m l,V s)))
    (update V (next_epoch m) (V s)).
Proof.
  intros HI HR [Hs Ho] HM. destruct (ci_shape HI) as [h HS].
  apply ci_bind. exact HI. exact HR.
  - rewrite <- Ho. now apply (inv_owners HS).
  - rewrite <- Ho. now apply (ci_viable HI).
  - intros q Hq. destruct (Nat.eq_dec l q) as [->|Hne].
    + eapply future_safe_ext with (I := fun e => e = next_epoch m \/ epoch_set m q e).
      * intros e. rewrite bind_epoch_set. tauto.
      * reflexivity.
      * apply (future_safe_copy s).
        -- unfold epoch_set. intros [H _]. lia.
        -- split. exact Hs. exact Ho.
        -- apply (proj2 certified_modes (classes m q) HM).
        -- apply (ci_future HI). exact Hq.
    + eapply future_safe_ext with (I := epoch_set m q) (V := V).
      * intros e. rewrite bind_epoch_set. tauto.
      * intros e [He _]. rewrite update_other by lia. reflexivity.
      * apply (ci_future HI). exact Hq.
Qed.

Lemma ci_allocate m g V x c : copying_invariant m g V ->
  retirable P g x = true -> viable P c [] = true ->
  copying_invariant (allocate m x c) (put g x (Some (c,[]))) (update V (next_epoch m) []).
Proof.
  intros HI HR HV. destruct (ci_shape HI) as [h HS].
  unfold allocate. eapply ci_install.
  exact HI. exact HR. lia.
  - intros q Hq. rewrite update_other by lia. reflexivity.
  - lia.
  - apply update_same.
  - intros q Hq. destruct (Nat.eq_dec q (next_loc m)). now right. left. lia.
  - exact HV.
  - intros q Hq. destruct (Nat.eq_dec q (next_loc m)) as [->|Hne].
    + rewrite update_same, absent_object_history by (try (exists h; exact HS); lia).
      eapply future_safe_ext with (I := fun e => e = next_epoch m).
      * intros e. change (e = next_epoch m <-> epoch_set (bind m x (next_loc m)) (next_loc m) e).
        rewrite bind_epoch_set. unfold epoch_set. split. tauto.
        intros [[He _]|[He Ho]]. exact He.
        pose proof (inv_owners HS He). lia.
      * reflexivity.
      * apply future_safe_single. apply update_same.
    + rewrite update_other by exact Hne.
      eapply future_safe_ext with (I := epoch_set m q) (V := V).
      * intros e. change (epoch_set m q e <-> epoch_set (bind m x (next_loc m)) q e).
        rewrite bind_epoch_set. intuition congruence.
      * intros e [He _]. rewrite update_other by lia. reflexivity.
      * apply (ci_future HI). lia.
Qed.

Lemma ci_emit m g V x e a : copying_invariant m g V -> get (refs m) x = Some e ->
  viable P (classes m (owners m e)) (V e ++ [a]) = true ->
  copying_invariant (emit m e a)
    (put g x (Some (classes m (owners m e),V e ++ [a]))) (update V e (V e ++ [a])).
Proof.
  intros HI Ex HV. destruct (ci_shape HI) as [h HS].
  constructor.
  - exists (put h x (Some (classes m (owners m e), project e (events m) ++ [a]))).
    eapply invariant_emit. exact HS. exact Ex. reflexivity.
  - intros y. cbn [emit refs classes owners]. destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite Ex, get_put_same. simpl. rewrite update_same. reflexivity.
    + rewrite get_put_other by exact Hne. rewrite <- (ci_agree HI y).
      destruct (get (refs m) y) as [d|] eqn:Ey. 2: reflexivity.
      simpl. rewrite update_other. reflexivity.
      intros ->. apply Hne. eapply inv_unique. exact HS. exact Ey. exact Ex.
  - intros d Hd. cbn [emit classes owners next_epoch] in *.
    destruct (Nat.eq_dec d e) as [->|Hne]. now rewrite update_same.
    rewrite update_other by exact Hne. now apply (ci_viable HI).
  - intros d Hd Hdead. cbn [emit refs classes owners next_epoch] in *.
    rewrite update_other. now apply (ci_retired HI).
    intros ->. exact (Hdead x Ex).
  - intros l Hl. cbn [emit next_loc classes] in *. rewrite emit_history.
    change (future_safe (protocol P (classes m l)) (epoch_set m l)
      (update V e (V e ++ [a])) (object_history m l ++ (if owners m e =? l then [a] else []))).
    destruct (owners m e =? l) eqn:Ho.
    + apply Nat.eqb_eq in Ho. apply future_safe_call.
      * split. eapply inv_refs. exact HS. exact Ex. exact Ho.
      * now apply (ci_future HI).
    + rewrite app_nil_r. eapply future_safe_ext with (I := epoch_set m l) (V := V).
      * tauto.
      * intros d [Hd Hdo]. rewrite update_other. reflexivity.
        intros ->. rewrite Hdo, Nat.eqb_refl in Ho. discriminate.
      * now apply (ci_future HI).
Qed.

Lemma ci_retire m g V x e : copying_invariant m g V -> get (refs m) x = Some e ->
  accepts P (classes m (owners m e)) (V e) = true ->
  copying_invariant (retire m x) (put g x None) V.
Proof.
  intros HI Ex HA. destruct (ci_shape HI) as [h HS]. constructor.
  - exists (put h x None). eapply invariant_retire. exact HS. exact Ex. reflexivity.
  - intros y. cbn [retire refs classes owners]. destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite !get_put_same. reflexivity.
    + rewrite !get_put_other by exact Hne. apply (ci_agree HI).
  - exact (ci_viable HI).
  - intros d Hd Hdead. cbn [retire refs classes owners next_epoch] in *.
    destruct (Nat.eq_dec d e) as [->|Hne]. exact HA.
    apply (ci_retired HI). exact Hd. intros y Ey.
    destruct (Nat.eq_dec y x) as [->|Hy]. congruence.
    apply (Hdead y). rewrite get_put_other by exact Hy. exact Ey.
  - exact (ci_future HI).
Qed.
Lemma ci_store m g V l f t : copying_invariant m g V ->
  l < next_loc m -> t < next_loc m -> classes m t = FT (classes m l) f ->
  copying_invariant (store m l f t) g V.
Proof.
  intros HI Hl Ht HC. constructor.
  - destruct (ci_shape HI) as [h HS]. exists h. now apply invariant_store.
  - exact (ci_agree HI).
  - exact (ci_viable HI).
  - exact (ci_retired HI).
  - exact (ci_future HI).
Qed.

Theorem copying_preservation m g V i m' g' : copying_invariant m g V ->
  raw_step i m m' -> check_step_with_copy P FT copy_history i g = Some g' ->
  exists V', copying_invariant m' g' V'.
Proof.
  intros HI HR HC. destruct (ci_shape HI) as [h HS]. destruct HR.
  - apply (check_bind_spec P FT) in HC. destruct HC as [HT [HV ->]].
    eexists. eapply ci_allocate. exact HI. exact HT. exact HV.
  - apply copy_step_spec in HC. destruct HC as [c [w [Ey [HT HC]]]].
    pose proof (ci_ref y HI H) as E. rewrite Ey in E. inversion E. subst c w.
    destruct (copy_history (classes m (owners m e))) eqn:HM.
    + subst g'. eexists. eapply ci_copy_bind. exact HI. exact HT.
      split. eapply inv_refs. exact HS. exact H. reflexivity. exact HM.
    + destruct HC as [HV ->]. eexists. eapply ci_fresh_bind. exact HI. exact HT.
      apply (inv_owners HS). eapply inv_refs. exact HS. exact H. exact HV.
  - cbn [check_step_with_copy check_step] in HC.
    rewrite (ci_ref y HI H) in HC. apply (check_bind_spec P FT) in HC.
    destruct HC as [HT [HV ->]]. destruct (inv_heap HS (owners m e) f H0) as [Hl [Ht Hclass]].
    rewrite <- Hclass in *. eexists. eapply ci_fresh_bind. exact HI. exact HT. exact Ht. exact HV.
  - cbn [check_step_with_copy check_step] in HC.
    rewrite (ci_ref x HI H), (ci_ref y HI H0) in HC.
    destruct (FT (classes m (owners m e)) f =? classes m (owners m d)) eqn:EF. 2: discriminate.
    inversion HC. subst g'. apply Nat.eqb_eq in EF.
    exists V. apply ci_store. exact HI.
    + apply (inv_owners HS). eapply inv_refs. exact HS. exact H.
    + apply (inv_owners HS). eapply inv_refs. exact HS. exact H0.
    + symmetry. exact EF.
  - cbn [check_step_with_copy check_step] in HC. rewrite (ci_ref x HI H) in HC.
    destruct (viable P (classes m (owners m e)) (V e ++ [a])) eqn:HV. 2: discriminate.
    inversion HC. subst g'. eexists. eapply ci_emit. exact HI. exact H. exact HV.
  - cbn [check_step_with_copy check_step] in HC. rewrite (ci_ref x HI H) in HC.
    destruct (accepts P (classes m (owners m e)) (V e)) eqn:HA. 2: discriminate.
    inversion HC. subst g'. exists V. eapply ci_retire. exact HI. exact H. exact HA.
Qed.

Lemma copying_trace_preservation m g V is m' g' : copying_invariant m g V ->
  execution is m m' -> check_trace_with_copy P FT copy_history is g = Some g' ->
  exists V', copying_invariant m' g' V'.
Proof.
  intros HI HE. revert g V HI g'. induction HE.
  - intros g V HI g' HC. simpl in HC. inversion HC. subst. now exists V.
  - intros g V HI g' HC. simpl in HC.
    destruct (check_step_with_copy P FT copy_history i g) as [gm|] eqn:HT. 2: discriminate.
    destruct (copying_preservation HI H HT) as [W HW]. eapply IHHE. exact HW. exact HC.
Qed.

Lemma copying_invariant_prefix m g V : copying_invariant m g V ->
  forall l, l < next_loc m -> prefix_language (protocol P (classes m l)) (object_history m l).
Proof.
  intros HI l Hl.
  set (ids := filter (fun e => owners m e =? l) (seq 0 (next_epoch m))).
  assert (Eids : forall e, In e ids <-> epoch_set m l e).
  { intros e. unfold ids, epoch_set. rewrite filter_In, in_seq. rewrite Nat.eqb_eq. lia. }
  assert (Hnd : NoDup ids) by (apply NoDup_filter; apply seq_NoDup).
  destruct (finite_completions (protocol P (classes m l)) V Hnd) as [t [Ht HC]].
  - intros e He. apply Eids in He. destruct He as [He Ho].
    pose proof (ci_viable HI He) as HV. apply viable_spec in HV. rewrite Ho in HV. exact HV.
  - exists (erase_tags t). apply (ci_future HI Hl).
    + intros e a He. apply Eids. eapply Ht. exact He.
    + intros e He. apply HC. now apply Eids.
Qed.
Lemma copying_invariant_complete m g V : copying_invariant m g V ->
  (forall x, get g x = None) ->
  forall l, l < next_loc m -> protocol P (classes m l) (object_history m l).
Proof.
  intros HI HG l Hl. rewrite <- (app_nil_r (object_history m l)).
  apply (ci_future HI Hl) with (t := []).
  - intros e a H. contradiction.
  - intros e [He Ho]. simpl. rewrite app_nil_r. unfold protocol. rewrite <- Ho.
    apply (ci_retired HI). exact He. intros x Ex.
    pose proof (ci_ref x HI Ex) as E. rewrite HG in E. discriminate.
Qed.
Theorem copying_program_prefix_sound s m :
  check_program_with_copy P FT copy_history s = true -> program_prefix s initial_machine m ->
  forall l, l < next_loc m -> prefix_language (protocol P (classes m l)) (object_history m l).
Proof.
  intros HC [p [q [HP HE]]] l Hl.
  destruct (check_program_with_copy_path P FT copy_history HC HP) as [g [HG Hempty]].
  rewrite check_trace_with_copy_app in HG.
  destruct (check_trace_with_copy P FT copy_history p []) as [gm|] eqn:HT. 2: discriminate.
  destruct (copying_trace_preservation ci_initial HE HT) as [V HV].
  eapply copying_invariant_prefix. exact HV. exact Hl.
Qed.
Theorem copying_program_completion_sound s m :
  check_program_with_copy P FT copy_history s = true -> program_execution s initial_machine m ->
  forall l, l < next_loc m -> protocol P (classes m l) (object_history m l).
Proof.
  intros HC [p [HP HE]] l Hl.
  destruct (check_program_with_copy_path P FT copy_history HC HP) as [g [HG Hempty]].
  destruct (copying_trace_preservation ci_initial HE HG) as [V HV].
  eapply copying_invariant_complete. exact HV. exact Hempty. exact Hl.
Qed.
End CopyingSoundness.
