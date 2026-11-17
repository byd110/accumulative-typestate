(* Direct singleton coverage, with no enumeration of the event alphabet.
   A cut chooses the block of repeatable events following each milestone. *)
From Coq Require Import List.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import regexp.
From Accumulation Require Import pumping.
Set Implicit Arguments.

Section Coverage.
Variable A : finType.
Fixpoint covers_from (seen seed out : seq A) : bool :=
  match seed, out with
  | [::], _ => out == [::]
  | a::s, b::v => (a == b) &&
      has (fun k => all (fun c => c \in a::seen) (take k v) &&
                    covers_from (a::seen) s (drop k v)) (iota 0 (size v).+1)
  | _, _ => false
  end.

Lemma covers_from_sound seed seen out (X : {set A}) :
  (forall c, (c \in X) = (c \in seen)) -> covers_from seen seed out ->
  @pump_semantic A X seed out.
Proof.
  elim: seed seen out X => [|a s IH] seen out X HX /=.
  - move/eqP=> ->; constructor.
  - case: out => [|b v] //= /andP [Hab Hmore].
    move/eqP: Hab => <-.
    change (is_true (has (fun k => all (fun c => c \in a::seen) (take k v) &&
      covers_from (a::seen) s (drop k v)) (iota 0 (size v).+1))) in Hmore.
    move/hasP: Hmore => [k Hk /andP [Hb Hrest]].
    rewrite -(cat_take_drop k v).
    apply: pump_semantic_cons.
    + apply/allP=> c Hc; have H := (allP Hb) c Hc.
      rewrite !inE HX. move: H; by rewrite seq.in_cons orbC.
    + apply: (IH (a::seen) (drop k v) (X :|: [set a]) _ Hrest).
      move=> c; by rewrite !inE HX orbC.
Qed.

Lemma covers_from_complete X seed out : @pump_semantic A X seed out ->
  forall seen, (forall c, (c \in X) = (c \in seen)) -> covers_from seen seed out.
Proof.
  move=> H; elim: H => [X0|X0 a s0 block out0 Hb Hrest IH] seen HX /=.
  - by rewrite eq_refl.
  - change (is_true ((a == a) && has (fun k =>
      all (fun c => c \in a::seen) (take k (block ++ out0)) &&
      covers_from (a::seen) s0 (drop k (block ++ out0)))
      (iota 0 (size (block ++ out0)).+1))).
    rewrite eq_refl andTb; apply/hasP; exists (size block).
    + rewrite mem_iota add0n leq0n size_cat ltnS; exact: leq_addr.
    + rewrite take_size_cat // drop_size_cat //; apply/andP; split.
      * apply/allP=> c Hc; have H := (allP Hb) c Hc.
        move: H; by rewrite !inE HX orbC.
      * apply IH => c; by rewrite !inE HX orbC.
Qed.

Definition covers (seed out : seq A) := covers_from [::] seed out.
Theorem covers_regex seed out : covers seed out = (out \in pumping_singleton_re A seed).
Proof.
  apply/idP/idP.
  - move=> H; apply/(pump_semanticP A set0 seed out).
    apply: (@covers_from_sound seed [::] out set0 _ H). by move=> c; rewrite inE.
  - move/(pump_semanticP A set0 seed out)=> H.
    apply: (covers_from_complete H). by move=> c; rewrite inE.
Qed.
Theorem covers_spec (default : A) seed out :
  covers seed out = true <-> @seed_covers A default seed out.
Proof. rewrite covers_regex; symmetry; apply pumping_closure_singleton_correct. Qed.
End Coverage.
