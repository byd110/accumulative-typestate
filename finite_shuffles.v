(* Complete enumeration of binary shuffles, independent of the event alphabet. *)
From Coq Require Import List.
From Accumulation Require Import trace_languages.
Import ListNotations.
Set Implicit Arguments.

Fixpoint shuffles {A} (u : list A) (v : list A) : list (list A) :=
  match u with
  | [] => [v]
  | a :: us =>
      (fix right (v : list A) :=
       match v with
       | [] => [a :: us]
       | b :: vs => map (cons a) (shuffles us v) ++ map (cons b) (right vs)
       end) v
  end.
Lemma shuffles_left_nil {A} (v : list A) : shuffles [] v = [v].
Proof. reflexivity. Qed.
Lemma shuffles_right_nil {A} (u : list A) : shuffles u [] = [u].
Proof. destruct u; reflexivity. Qed.
Lemma shuffles_cons {A} (a b : A) u v :
  shuffles (a::u) (b::v) =
  map (cons a) (shuffles u (b::v)) ++ map (cons b) (shuffles (a::u) v).
Proof. reflexivity. Qed.
Lemma shuffle_nil_left_inv {A} (u v : list A) : shuffle [] u v -> u = v.
Proof.
  intros H; remember [] as z eqn:E; induction H; inversion E; subst; f_equal; auto.
Qed.
Lemma shuffle_nil_right_inv {A} (u v : list A) : shuffle u [] v -> u = v.
Proof.
  intros H; remember [] as z eqn:E; induction H; inversion E; subst; f_equal; auto.
Qed.

Theorem shuffles_spec {A} (u v w : list A) : In w (shuffles u v) <-> shuffle u v w.
Proof.
  revert v w; induction u as [|a u IHu]; intros v w.
  - simpl; split.
    + intros [<-|[]]; apply shuffle_nil_left.
    + intros H; apply shuffle_nil_left_inv in H; auto.
  - revert w; induction v as [|b v IHv]; intros w.
    + rewrite shuffles_right_nil; simpl; split.
      * intros [<-|[]]; apply shuffle_nil_right.
      * intros H; apply shuffle_nil_right_inv in H; auto.
    + rewrite shuffles_cons, in_app_iff, !in_map_iff; split.
      * intros [[z [<- Hz]]|[z [<- Hz]]].
        -- apply shuffle_left; now apply IHu.
        -- apply shuffle_right; now apply IHv.
      * intros H; inversion H; subst.
        -- left; eexists; split; [reflexivity|now apply IHu].
        -- right; eexists; split; [reflexivity|now apply IHv].
Qed.
