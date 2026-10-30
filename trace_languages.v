(* Formal-language lemmas used by the typestate development.  No syntax,
   heap, reference, or typing definitions belong in this module. *)
From Coq Require Import List Arith Bool Lia.
Import ListNotations.
Set Implicit Arguments.

Definition language (A : Type) := list A -> Prop.
Definition prefix_language {A} (K : language A) (u : list A) :=
  exists v, K (u ++ v).
Definition residual {A} (K : language A) (u : list A) : language A :=
  fun v => K (u ++ v).

Inductive shuffle {A : Type} : list A -> list A -> list A -> Prop :=
| shuffle_nil : shuffle [] [] []
| shuffle_left a u v w : shuffle u v w -> shuffle (a :: u) v (a :: w)
| shuffle_right a u v w : shuffle u v w -> shuffle u (a :: v) (a :: w).

Definition shuffle_closed {A} (K : language A) :=
  forall u v w, K u -> K v -> shuffle u v w -> K w.

Lemma shuffle_nil_left {A} (w : list A) : shuffle [] w w.
Proof. induction w; constructor; assumption. Qed.
Lemma shuffle_nil_right {A} (w : list A) : shuffle w [] w.
Proof. induction w; constructor; assumption. Qed.
Lemma shuffle_app {A} (u v w u' v' w' : list A) :
  shuffle u v w -> shuffle u' v' w' ->
  shuffle (u ++ u') (v ++ v') (w ++ w').
Proof. intros H; induction H; simpl; intros; eauto using shuffle. Qed.
Lemma shuffle_concat {A} (u v : list A) : shuffle u v (u ++ v).
Proof. induction u; simpl; auto using shuffle_nil_left, shuffle_left. Qed.
Lemma prefix_includes {A} (K : language A) w : K w -> prefix_language K w.
Proof. intros H; exists []; now rewrite app_nil_r. Qed.
Lemma prefix_shuffle_closed {A} (K : language A) :
  shuffle_closed K -> shuffle_closed (prefix_language K).
Proof.
  intros H u v w [u' Hu] [v' Hv] Hs.
  exists (u' ++ v'). eapply H; [exact Hu|exact Hv|].
  apply shuffle_app; [exact Hs|apply shuffle_concat].
Qed.
Lemma residual_snoc {A} (K : language A) u a v :
  residual K (u ++ [a]) v <-> residual K u (a :: v).
Proof. unfold residual. now rewrite <- app_assoc. Qed.
Lemma residual_nullable {A} (K : language A) u :
  residual K u [] <-> K u.
Proof. unfold residual. now rewrite app_nil_r. Qed.

(* Tagged words give the exact event partition used by binding epochs. *)
Fixpoint project {A} (e : nat) (t : list (nat * A)) : list A :=
  match t with
  | [] => []
  | (i,a) :: t' => if Nat.eqb i e then a :: project e t' else project e t'
  end.
Definition erase_tags {A} (t : list (nat * A)) := map (@snd nat A) t.
Definition without_tag {A} e (t : list (nat * A)) :=
  filter (fun p => negb (Nat.eqb (fst p) e)) t.

Lemma project_app {A} e (t u : list (nat * A)) :
  project e (t ++ u) = project e t ++ project e u.
Proof. induction t as [|[i a] t IH]; simpl; auto.
  destruct (i =? e); simpl; now rewrite IH. Qed.
Lemma project_snoc {A} e i (a : A) t :
  project e (t ++ [(i,a)]) =
  if i =? e then project e t ++ [a] else project e t.
Proof. rewrite project_app. simpl. destruct (i =? e); now rewrite ?app_nil_r. Qed.
Lemma project_absent {A} e (t : list (nat * A)) :
  (forall i a, In (i,a) t -> i <> e) -> project e t = [].
Proof.
  induction t as [|[i a] t IH]; simpl; auto.
  intros H. assert (i <> e) by (apply (H i a); now left).
  apply Nat.eqb_neq in H0. rewrite H0. apply IH.
  intros j b Hin. apply (H j b). now right.
Qed.
Lemma project_without {A} i e (t : list (nat * A)) :
  i <> e -> project i (without_tag e t) = project i t.
Proof.
  intros Hne; induction t as [|[j a] t IH]; simpl; auto.
  unfold without_tag in *; simpl in *.
  destruct (j =? e) eqn:He; simpl.
  - apply Nat.eqb_eq in He; subst j. assert (Hne' : (e =? i) = false) by (apply Nat.eqb_neq; congruence).
    rewrite Hne'. exact IH.
  - destruct (j =? i); simpl; now rewrite IH.
Qed.
Lemma project_partition {A} e (t : list (nat * A)) :
  shuffle (project e t) (erase_tags (without_tag e t)) (erase_tags t).
Proof.
  induction t as [|[i a] t IH]; simpl; [constructor|].
  unfold without_tag, erase_tags in *; simpl in *.
  destruct (i =? e); simpl; auto using shuffle_left, shuffle_right.
Qed.

(* Empty projections are retained.  Nonempty index sets, rather than an
   assumption K [], handle protocols with mandatory completion events. *)
Lemma project_only {A} e (t : list (nat * A)) :
  (forall i a, In (i,a) t -> i = e) -> project e t = erase_tags t.
Proof.
  induction t as [|[i a] t IH]; simpl; auto.
  intros H. assert (i=e) by (apply (H i a); now left).
  subst i; rewrite Nat.eqb_refl. f_equal. apply IH.
  intros j b Hin. apply (H j b). now right.
Qed.

Theorem tagged_shuffle_closed {A} (K : language A) ids t :
  shuffle_closed K -> NoDup ids -> ids <> [] ->
  (forall i a, In (i,a) t -> In i ids) ->
  (forall i, In i ids -> K (project i t)) -> K (erase_tags t).
Proof.
  intros HC. revert t.
  induction ids as [|e ids IH]; intros t Hnd Hne Htags Hall; [contradiction|].
  inversion Hnd as [|? ? Hnot Htail]; subst.
  destruct ids as [|j ids].
  - rewrite <- (@project_only A e t).
    + apply Hall; now left.
    + intros i a Hin. specialize (Htags i a Hin). simpl in Htags; destruct Htags as [He|HF]; [congruence|contradiction].
  - apply (HC (project e t) (erase_tags (without_tag e t))).
    + apply Hall; now left.
    + apply IH; [exact Htail|discriminate| |].
      * intros i a Hin. apply filter_In in Hin. destruct Hin as [Hin Hkeep].
        specialize (Htags i a Hin). simpl in Htags.
        destruct Htags as [He|Hin']; [|exact Hin'].
        subst i. simpl in Hkeep. now rewrite Nat.eqb_refl in Hkeep.
      * intros i Hin. assert (Hneq : i <> e) by (intros ->; contradiction).
        rewrite project_without by exact Hneq. apply Hall. now right.
    + apply project_partition.
Qed.

Lemma project_filter {A} (test : nat -> bool) e (t : list (nat * A)) :
  test e = true -> project e (filter (fun p => test (fst p)) t) = project e t.
Proof.
  intros He; induction t as [|[i a] t IH]; simpl; auto.
  destruct (Nat.eq_dec i e) as [->|Hne].
  - rewrite He; simpl; rewrite Nat.eqb_refl, IH; reflexivity.
  - assert (E : (i =? e) = false) by (apply Nat.eqb_neq; exact Hne).
    destruct (test i); simpl; rewrite E; exact IH.
Qed.
