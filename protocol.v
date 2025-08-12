(* definition for protocol and its compliance at language level *)

Require Import RegLang.languages.

Require Import String List.
Import ListNotations.
Open Scope string_scope.

From mathcomp Require Import all_ssreflect.

Require Import ssreflect ssrfun ssrbool.
Require Import Coq.Strings.String.

Inductive ab_letter := a | b.

Definition ab_letter_eq (x y : ab_letter) : bool :=
  match x, y with
  | a, a => true
  | b, b => true
  | _, _ => false
  end.

Lemma ab_letter_eqP : Equality.axiom ab_letter_eq.
Proof.
  move=> x y; case: x; case: y; constructor; congruence.
Qed.

Definition ab_letter_eqMixin := Equality.Mixin ab_letter_eqP.
Canonical ab_letter_eqType := eqType ab_letter ab_letter_eqMixin.

(* Now define your language type *)
Definition Sigma := ab_letter_eqType.

(* Example word type: list Sigma *)
Definition word := seq Sigma.

(* Example: pumping closure language *)
Definition pumping_closure_lang (s : word) : word -> bool :=
  fun w =>
    exists a n, a \in s /\ 1 <= n /\ w = (let fix pump_after_first s a n :=
      match s with
      | [::] => [::]
      | x :: xs =>
          if x == a then
            x :: (nseq n a) ++ xs
          else
            x :: pump_after_first xs a n
      end in pump_after_first s a n).