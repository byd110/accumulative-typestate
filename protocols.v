(* Decidable language interface. Implementations prove their queries. *)
From Coq Require Import List Bool.
From Accumulation Require Import trace_languages.
Import ListNotations.
Set Implicit Arguments.

Record protocol_family (A : Type) := {
  accepts : nat -> list A -> bool;
  viable : nat -> list A -> bool;
  viable_spec : forall c u, viable c u = true <->
    exists v, accepts c (u ++ v) = true
}.
Arguments accepts {A} _ _ _.
Arguments viable {A} _ _ _.
Definition protocol {A} (P : protocol_family A) c : language A :=
  fun w => accepts P c w = true.
Definition certified {A} (P : protocol_family A) :=
  forall c, shuffle_closed (protocol P c).

Lemma viable_prefix {A} (P : protocol_family A) c u :
  viable P c u = true <-> prefix_language (protocol P c) u.
Proof. apply viable_spec. Qed.
Lemma complete_viable {A} (P : protocol_family A) c u :
  accepts P c u = true -> viable P c u = true.
Proof. intros H; apply viable_spec. exists []; now rewrite app_nil_r. Qed.
Lemma viable_initial {A} (P : protocol_family A) c u :
  viable P c u = true -> viable P c [] = true.
Proof. rewrite !viable_spec. intros [v H]; exists (u ++ v); exact H. Qed.
