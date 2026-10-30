(* Programming-language syntax and finite maps. *)
From Coq Require Import List Arith Bool Lia.
Import ListNotations.
Set Implicit Arguments.
Definition var := nat.
Definition loc := nat.
Definition class := nat.
Definition field := nat.
Definition epoch := nat.

(* Shadowing association lists; deletion is an explicit None entry. *)
Definition fmap (V : Type) := list (nat * option V).
Fixpoint get {V} (m : fmap V) (x : nat) : option V :=
  match m with
  | [] => None
  | (y,v) :: rest => if Nat.eqb x y then v else get rest x
  end.
Definition put {V} (m : fmap V) (x : nat) (v : option V) := (x,v) :: m.
Definition update {V} (f : nat -> V) x v :=
  fun y => if Nat.eqb y x then v else f y.
Lemma get_put_same {V} (m : fmap V) x v : get (put m x v) x = v.
Proof. simpl; now rewrite Nat.eqb_refl. Qed.
Lemma get_put_other {V} (m : fmap V) x y v :
  y <> x -> get (put m x v) y = get m y.
Proof. intros H; simpl. apply Nat.eqb_neq in H; now rewrite H. Qed.
Lemma update_same {V} (f : nat -> V) x v : update f x v x = v.
Proof. unfold update; now rewrite Nat.eqb_refl. Qed.
Lemma update_other {V} (f : nat -> V) x y v :
  y <> x -> update f x v y = f y.
Proof. intros H; unfold update. apply Nat.eqb_neq in H; now rewrite H. Qed.
Definition emptyb {V} (m : fmap V) :=
  forallb (fun p => match get m (fst p) with None => true | Some _ => false end) m.
Lemma get_some_key {V} (m : fmap V) x v :
  get m x = Some v -> exists ov, In (x,ov) m.
Proof.
  induction m as [|[y ov] m IH]; simpl; [discriminate|].
  destruct (x =? y) eqn:E.
  - apply Nat.eqb_eq in E; subst; intros; exists ov; now left.
  - intros H; destruct (IH H) as [ov' Hin]; exists ov'; now right.
Qed.
Lemma emptyb_spec {V} (m : fmap V) :
  emptyb m = true <-> forall x, get m x = None.
Proof.
  unfold emptyb; rewrite forallb_forall; split.
  - intros H x; destruct (get m x) as [v|] eqn:E; auto.
    destruct (@get_some_key V m x v E) as [ov Hin].
    specialize (H (x,ov) Hin); simpl in H; rewrite E in H; discriminate.
  - intros H [x ov] Hin; simpl; now rewrite H.
Qed.

Inductive instruction (A : Type) :=
| New (x : var) (c : class)
| Copy (x y : var)
| Load (x y : var) (f : field)
| Store (x : var) (f : field) (y : var)
| Call (x : var) (a : A)
| Finish (x : var)
Arguments New {A} _ _.
Arguments Copy {A} _ _.
Arguments Load {A} _ _ _.
Arguments Store {A} _ _ _.
Arguments Call {A} _ _.
Arguments Finish {A} _.
Inductive statement (A : Type) :=
| Skip
| Do (i : instruction A)
| Seq (s t : statement A)
| Branch (s t : statement A).
Arguments Skip {A}.
Arguments Do {A} _.
Arguments Seq {A} _ _.
Arguments Branch {A} _ _.

(* Both outcomes of a protocol-pure condition are checked. *)
Fixpoint paths {A} (s : statement A) : list (list (instruction A)) :=
  match s with
  | Skip => [[]]
  | Do i => [[i]]
  | Seq s t => flat_map (fun p => map (fun q => p ++ q) (paths t)) (paths s)
  | Branch s t => paths s ++ paths t
  end.
Inductive path {A} : statement A -> list (instruction A) -> Prop :=
| path_skip : path Skip []
| path_do i : path (Do i) [i]
| path_seq s t p q : path s p -> path t q -> path (Seq s t) (p ++ q)
| path_left s t p : path s p -> path (Branch s t) p
| path_right s t q : path t q -> path (Branch s t) q.
Lemma paths_spec {A} (s : statement A) p : In p (paths s) <-> path s p.
Proof.
  split.
  - revert p; induction s; simpl; intros p H.
    + destruct H as [<-|H]; [constructor|contradiction].
    + destruct H as [<-|H]; [constructor|contradiction].
    + apply in_flat_map in H; destruct H as [q [Hq H]].
      apply in_map_iff in H; destruct H as [r [<- Hr]]. constructor; auto.
    + apply in_app_or in H; destruct H; [apply path_left|apply path_right]; auto.
  - intros H; induction H; simpl; auto.
    + apply in_flat_map; exists p; split; auto. apply in_map; assumption.
    + apply in_or_app; auto.
    + apply in_or_app; auto.
Qed.

(* Lookup current bindings, ignoring shadowed entries in the finite map. *)
Definition liveb (r : fmap epoch) e :=
  existsb (fun p => match get r (fst p) with
     | Some d => Nat.eqb d e | None => false end) r.
Lemma liveb_spec r e : liveb r e = true <-> exists x, get r x = Some e.
Proof.
  unfold liveb; rewrite existsb_exists; split.
  - intros [[x v] [Hin E]]; simpl in E.
    destruct (get r x) as [d|] eqn:Ex; try discriminate.
    apply Nat.eqb_eq in E; subst; eauto.
  - intros [x Ex]. destruct (@get_some_key epoch r x e Ex) as [v Hin].
    exists (x,v); split; auto; simpl; rewrite Ex, Nat.eqb_refl; reflexivity.
Qed.
