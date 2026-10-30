(* Completion continuations share inherited evidence without duplicating events. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import syntax trace_languages.
Import ListNotations.
Set Implicit Arguments.

Section FutureLanguages.
Context {A : Type}.
Definition supported (I : nat -> Prop) (t : list (nat * A)) :=
  forall e a, In (e,a) t -> I e.
Definition future_safe (K : language A) (I : nat -> Prop)
    (V : nat -> list A) (w : list A) :=
  forall t, supported I t ->
    (forall e, I e -> K (V e ++ project e t)) -> K (w ++ erase_tags t).

Lemma shuffle_swap (u v w : list A) : shuffle u v w -> shuffle v u w.
Proof. intros H. induction H. constructor. now constructor 3. now constructor 2. Qed.
Lemma shuffle_prefix (p u v w : list A) : shuffle u v w -> shuffle (p ++ u) v (p ++ w).
Proof. intros H. induction p. exact H. simpl. now constructor. Qed.
Definition retag (n s : nat) (t : list (nat * A)) :=
  map (fun p => (if fst p =? n then s else fst p, snd p)) t.
Lemma erase_retag n s t : erase_tags (retag n s t) = erase_tags t.
Proof.
  induction t as [|[e a] t IH]. reflexivity.
  simpl in *. now rewrite IH.
Qed.
Lemma project_retag_other n s e t : e <> n -> e <> s ->
  project e (retag n s t) = project e t.
Proof.
  intros Hn Hs. induction t as [|[d a] t IH]. reflexivity.
  simpl. destruct (d =? n) eqn:N.
  - apply Nat.eqb_eq in N. subst d.
    rewrite (proj2 (Nat.eqb_neq s e) ltac:(congruence)).
    rewrite (proj2 (Nat.eqb_neq n e) ltac:(congruence)). exact IH.
  - simpl. rewrite IH. reflexivity.
Qed.
Lemma project_retag_shuffle n s t : n <> s ->
  shuffle (project n t) (project s t) (project s (retag n s t)).
Proof.
  intros Hne. induction t as [|[e a] t IH]. constructor.
  simpl. destruct (e =? n) eqn:N.
  - apply Nat.eqb_eq in N. subst e.
    rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq n s) Hne). now constructor.
  - simpl. destruct (e =? s). now constructor 3. exact IH.
Qed.

Lemma future_safe_ext K I J V W w :
  (forall e, I e <-> J e) -> (forall e, I e -> V e = W e) ->
  future_safe K I V w -> future_safe K J W w.
Proof.
  intros HI HV H t Ht HC. apply H.
  - intros e a He. apply HI. eapply Ht. exact He.
  - intros e He. rewrite HV by exact He. apply HC. now apply HI.
Qed.

Lemma future_safe_call K I V w e a : I e -> future_safe K I V w ->
  future_safe K I (update V e (V e ++ [a])) (w ++ [a]).
Proof.
  intros He H t Ht HC.
  specialize (H ((e,a)::t)). simpl in H.
  rewrite <- app_assoc. simpl. apply H.
  - intros d b [E|E]. inversion E. subst. exact He. eapply Ht. exact E.
  - intros d Hd. destruct (Nat.eq_dec d e) as [->|Hde].
    + specialize (HC e He). rewrite update_same in HC.
      rewrite Nat.eqb_refl. now rewrite <- app_assoc in HC.
    + specialize (HC d Hd). rewrite update_other in HC by exact Hde.
      rewrite (proj2 (Nat.eqb_neq e d) ltac:(congruence)). exact HC.
Qed.

Lemma future_safe_fresh K I V w n : shuffle_closed K -> ~ I n ->
  future_safe K I V w ->
  future_safe K (fun e => e = n \/ I e) (update V n []) w.
Proof.
  intros HK Hn H t Ht HC.
  assert (Hrest : K (w ++ erase_tags (without_tag n t))).
  { apply H.
    - intros e a E. apply filter_In in E. destruct E as [E Hne].
      unfold supported in Ht. specialize (Ht e a E). simpl in Hne.
      destruct Ht as [->|HI]. rewrite Nat.eqb_refl in Hne. discriminate. exact HI.
    - intros e He. assert (Hne : e <> n) by (intros ->; contradiction).
      specialize (HC e (or_intror He)). rewrite update_other in HC by exact Hne.
      rewrite project_without by exact Hne. exact HC. }
  assert (Hnew : K (project n t)).
  { specialize (HC n (or_introl eq_refl)). now rewrite update_same in HC. }
  eapply HK. exact Hrest. exact Hnew.
  apply shuffle_prefix. apply shuffle_swap. apply project_partition.
Qed.

Lemma future_safe_copy K I V w n s : ~ I n -> I s ->
  shuffle_closed (residual K (V s)) -> future_safe K I V w ->
  future_safe K (fun e => e = n \/ I e) (update V n (V s)) w.
Proof.
  intros Hn Hs HK H t Ht HC. rewrite <- (erase_retag n s t).
  apply H.
  - intros e a E. apply in_map_iff in E. destruct E as [[d b] [E Hin]]. simpl in E.
    destruct (d =? n) eqn:N. inversion E. subst. exact Hs.
    inversion E. subst. specialize (Ht e a Hin). destruct Ht as [->|Ht].
    rewrite Nat.eqb_refl in N. discriminate. exact Ht.
  - intros e He. assert (Hne : e <> n) by (intros ->; contradiction).
    destruct (Nat.eq_dec e s) as [->|Hes].
    + apply HK with (project n t) (project s t).
      * specialize (HC n (or_introl eq_refl)). now rewrite update_same in HC.
      * specialize (HC s (or_intror He)). now rewrite update_other in HC by exact Hne.
      * apply project_retag_shuffle. congruence.
    + rewrite project_retag_other by assumption.
      specialize (HC e (or_intror He)). now rewrite update_other in HC by exact Hne.
Qed.

Lemma future_safe_single K n V : V n = [] ->
  future_safe K (fun e => e = n) V [].
Proof.
  intros HV t Ht HC. simpl. rewrite <- (@project_only A n t).
  - specialize (HC n eq_refl). now rewrite HV in HC.
  - exact Ht.
Qed.

Lemma project_tag_block e d (w : list A) :
  project e (map (fun a => (d,a)) w) = if d =? e then w else [].
Proof.
  induction w as [|a w IH]. simpl. now destruct (d =? e).
  simpl. rewrite IH. now destruct (d =? e).
Qed.
Lemma finite_completions K V ids : NoDup ids ->
  (forall e, In e ids -> exists u, K (V e ++ u)) ->
  exists t, supported (fun e => In e ids) t /\
    forall e, In e ids -> K (V e ++ project e t).
Proof.
  intros Hnd. induction Hnd as [|e ids Hnot Hnd IH].
  - intros H. exists []. split. intros d a E. contradiction. intros d E. contradiction.
  - intros H. destruct (H e (or_introl eq_refl)) as [u Hu].
    destruct IH as [t [Ht HC]]. intros d Hd. apply H. now right.
    exists (map (fun a => (e,a)) u ++ t). split.
    + intros d a E. apply in_app_or in E. destruct E as [E|E].
      * apply in_map_iff in E. destruct E as [b [E Hb]]. inversion E. now left.
      * right. eapply Ht. exact E.
    + intros d [<-|Hd].
      * rewrite project_app, project_tag_block, Nat.eqb_refl.
        rewrite project_absent. now rewrite app_nil_r.
        intros i a Hi E. subst i. apply Hnot. eapply Ht. exact Hi.
      * rewrite project_app, project_tag_block.
        rewrite (proj2 (Nat.eqb_neq e d) ltac:(intros ->; contradiction)).
        simpl. apply HC. exact Hd.
Qed.
End FutureLanguages.
