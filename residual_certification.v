(* Exact finite certification of shuffle closure at every reachable residual. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa regexp.
From Accumulation Require Import trace_languages copying_typestate regular_protocols.
Set Implicit Arguments.

Section ResidualCertification.
Variable A : finType.
Variable D : dfa A.
Local Notation tagged := (Finite.clone (bool * A)%type _).
Local Notation triple := (Finite.clone ((D * D) * D)%type _).

Fixpoint left_word (t : seq tagged) : seq A :=
  if t is (b,a)::rest then if b then a::left_word rest else left_word rest else [::].
Fixpoint right_word (t : seq tagged) : seq A :=
  if t is (b,a)::rest then if b then right_word rest else a::right_word rest else [::].
Definition merged_word (t : seq tagged) : seq A := map snd t.

Lemma tagged_shuffle t : trace_languages.shuffle (left_word t) (right_word t) (merged_word t).
Proof.
  elim: t => [|[b a] t IH]. constructor.
  case: b => /=. now constructor. now constructor 3.
Qed.
Lemma shuffle_tagged u v w : trace_languages.shuffle u v w ->
  exists t, left_word t = u /\ right_word t = v /\ merged_word t = w.
Proof.
  intros H. induction H.
  - exists [::]. auto.
  - destruct IHshuffle as [t [Hu [Hv Hw]]]. exists ((true,a)::t). simpl. now rewrite Hu Hv Hw.
  - destruct IHshuffle as [t [Hu [Hv Hw]]]. exists ((false,a)::t). simpl. now rewrite Hu Hv Hw.
Qed.
Definition shuffle_witness_dfa (q : D) : dfa tagged :=
  {| dfa_state := triple;
     dfa_s := ((q,q),q);
     dfa_fin := [set t : triple | (t.1.1 \in dfa_fin D) && (t.1.2 \in dfa_fin D) && (t.2 \notin dfa_fin D)];
     dfa_trans := fun t ba =>
       if ba.1 then ((dfa_trans t.1.1 ba.2, t.1.2), dfa_trans t.2 ba.2)
       else ((t.1.1, dfa_trans t.1.2 ba.2), dfa_trans t.2 ba.2) |}.
Lemma witness_delta q t p r s :
  @delta tagged (shuffle_witness_dfa q) ((p,r),s) t =
  ((@delta A D p (left_word t), @delta A D r (right_word t)), @delta A D s (merged_word t)).
Proof.
  elim: t p r s => [|[b a] t IH] p r s //=.
  case: b => /=; apply IH.
Qed.
Lemma witness_accept q t :
  (t \in dfa_lang (shuffle_witness_dfa q)) =
  (dfa_accept q (left_word t) && dfa_accept q (right_word t) && ~~ dfa_accept q (merged_word t)).
Proof. by rewrite inE /dfa_accept witness_delta inE. Qed.
Definition state_shuffle_certified (q : D) := ~~ dfa_inhab (shuffle_witness_dfa q).
Lemma state_shuffle_certified_spec q : state_shuffle_certified q = true <->
  shuffle_closed (fun w => dfa_accept q w = true).
Proof.
  split.
  - move/negP=> H u v w Hu Hv Hs.
    destruct (shuffle_tagged Hs) as [t [Ht1 [Ht2 Ht3]]].
    apply/negPn/negP=> Hw. apply H. apply/dfa_inhabP. exists t.
    rewrite witness_accept Ht1 Ht2 Ht3 Hu Hv. exact Hw.
  - intros H. apply/negP=> /dfa_inhabP [t Ht].
    rewrite witness_accept in Ht. move/andP: Ht=> [/andP [Hl Hr] Hn].
    have Ha := H _ _ _ Hl Hr (tagged_shuffle t). by rewrite Ha in Hn.
Qed.
Definition reachable_state (q : D) := exseqb (delta (dfa_s D)) (pred1 q).
Lemma reachable_state_spec q : reachable_state q = true <-> exists p, delta (dfa_s D) p = q.
Proof.
  split.
  - move/(exseqP (@delta_rc A D))=> [p /eqP Hp]. now exists p.
  - move=> [p Hp]. apply/(exseqP (@delta_rc A D)). exists p. by apply/eqP.
Qed.
Definition certify_residuals := [forall q : D, reachable_state q ==> state_shuffle_certified q].
Theorem certify_residuals_spec : certify_residuals = true <->
  residual_shuffle_closed (fun w => w \in dfa_lang D).
Proof.
  split.
  - move/forallP=> H p u v w Hu Hv Hs.
    have Hreach : reachable_state (delta (dfa_s D) p) = true.
    { apply reachable_state_spec. now exists p. }
    have HC : state_shuffle_certified (delta (dfa_s D) p) = true.
    { move/implyP: (H (delta (dfa_s D) p))=> HC. exact (HC Hreach). }
    apply state_shuffle_certified_spec in HC.
    unfold trace_languages.residual in *. rewrite !inE /dfa_accept !delta_cat in Hu Hv *.
    exact (HC u v w Hu Hv Hs).
  - intros H. apply/forallP=> q. apply/implyP=> Hq.
    apply reachable_state_spec in Hq. destruct Hq as [p <-].
    apply state_shuffle_certified_spec. intros u v w Hu Hv Hs.
    unfold dfa_accept. rewrite -delta_cat.
    apply (H p u v w).
    + unfold trace_languages.residual. by rewrite inE /dfa_accept delta_cat.
    + unfold trace_languages.residual. by rewrite inE /dfa_accept delta_cat.
    + exact Hs.
Qed.
End ResidualCertification.

Section RegularResiduals.
Variable A : finType.
Definition certify_copying_regex (r : regexp A) := certify_residuals (re_to_dfa (closure_regex r)).
Theorem certify_copying_regex_spec (spec : nat -> regexp A) c :
  certify_copying_regex (spec c) = true <->
  residual_shuffle_closed (protocols.protocol (regular_family spec) c).
Proof.
  rewrite /certify_copying_regex certify_residuals_spec.
  have E : forall w, (w \in dfa_lang (re_to_dfa (closure_regex (spec c)))) =
    protocols.accepts (regular_family spec) c w.
  { intros w. rewrite re_to_dfa_correct closure_regex_covered. reflexivity. }
  unfold residual_shuffle_closed, shuffle_closed, trace_languages.residual, protocols.protocol.
  split => H p u v w Hu Hv Hs.
  - rewrite <- E. apply (H p u v w). now rewrite E. now rewrite E. exact Hs.
  - rewrite E. apply (H p u v w). now rewrite <- E. now rewrite <- E. exact Hs.
Qed.
End RegularResiduals.
