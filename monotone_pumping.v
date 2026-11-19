(* Connect persistent-information machines to the existing pumping operation. *)
From Coq Require Import List.
From mathcomp Require Import all_ssreflect.
From Accumulation Require Import pumping certification monotone_protocols.
Set Implicit Arguments.

Section MonotonePumping.
Variable A : finType.
Variable default : A.
Variable S : Type.
Variable M : monotone_machine A S.

Theorem machine_language_pumping s u v :
  machine_language M s u -> @pumping A default u v ->
  machine_language M s v.
Proof.
  move=> Hu Hp.
  case: (@pumping_decompose A default u v Hp) => p [q [a [Eu Ev Ha]]].
  subst u v. apply machine_language_repeat; first by apply mem_list_in.
  exact Hu.
Qed.

Theorem machine_language_pumping_closure s (L : dlang_base A) :
  (forall w, L w -> machine_language M s w) ->
  forall w, @pumping_closure A default L w -> machine_language M s w.
Proof.
  move=> Hseeds w Hclosure.
  elim: Hclosure => [u Hu | u v _ IH Hp].
  - exact: Hseeds Hu.
  - exact: machine_language_pumping IH Hp.
Qed.

Theorem machine_language_pumping_fixed_point s (L : dlang_base A) :
  (forall w, L w <-> machine_language M s w) ->
  forall w, @pumping_closure A default L w <-> machine_language M s w.
Proof.
  move=> HL w; split.
  - apply machine_language_pumping_closure. move=> u Hu. exact: (proj1 (HL u) Hu).
  - move=> Hw. apply pumping_closure_base. exact: (proj2 (HL w) Hw).
Qed.
End MonotonePumping.
