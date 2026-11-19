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

(* Public statements: source syntax is the finish-free fragment. *)
Inductive statement (A : Type) :=
| Skip
| New (x : var) (c : class)
| Copy (x y : var)
| Load (x y : var) (f : field)
| Store (x : var) (f : field) (y : var)
| Call (x : var) (a : A)
| Finish
| Seq (s t : statement A).
Arguments Skip {A}.
Arguments New {A} _ _.
Arguments Copy {A} _ _.
Arguments Load {A} _ _ _.
Arguments Store {A} _ _ _.
Arguments Call {A} _ _.
Arguments Finish {A}.
Arguments Seq {A} _ _.

Inductive context (A : Type) :=
| Hole
| SeqLeft (E : context A) (t : statement A).
Arguments Hole {A}.
Arguments SeqLeft {A} _ _.
Fixpoint plug {A} (E : context A) (s : statement A) :=
  match E with Hole => s | SeqLeft F t => Seq (plug F s) t end.
Fixpoint compose {A} (E F : context A) :=
  match E with Hole => F | SeqLeft E t => SeqLeft (compose E F) t end.
Lemma plug_compose {A} (E F : context A) s :
  plug (compose E F) s = plug E (plug F s).
Proof. induction E; simpl; congruence. Qed.

Fixpoint finish_freeb {A} (s : statement A) : bool :=
  match s with Finish => false | Seq s t => finish_freeb s && finish_freeb t | _ => true end.
Definition finish_free {A} (s : statement A) := finish_freeb s = true.
Definition instrument {A} (s : statement A) := Seq s Finish.
Fixpoint finish_count {A} (s : statement A) : nat :=
  match s with Finish => 1 | Seq s t => finish_count s + finish_count t | _ => 0 end.
Lemma finish_free_count {A} (s : statement A) :
  finish_free s <-> finish_count s = 0.
Proof.
  unfold finish_free; induction s; simpl; try tauto; try (split; discriminate).
  rewrite andb_true_iff, IHs1, IHs2. lia.
Qed.
Theorem instrument_single_exit {A} (s : statement A) :
  finish_free s -> finish_count (instrument s) = 1.
Proof. intros H; apply finish_free_count in H. simpl. lia. Qed.
Theorem instrument_not_source {A} (s : statement A) : ~ finish_free (instrument s).
Proof. unfold finish_free, instrument; simpl. rewrite andb_false_r. discriminate. Qed.

(* A notation-building helper, not an execution semantics. *)
Fixpoint sequence {A} (ss : list (statement A)) : statement A :=
  match ss with [] => Skip | s :: ss => Seq s (sequence ss) end.

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
