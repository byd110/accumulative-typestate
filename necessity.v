(* Exactness of shuffle closure for the baseline checker's completion
   guarantee.  Any two complete local words and their chosen interleaving
   are realized by an accepted, terminating two-alias program. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import trace_languages protocols syntax semantics
  typestate soundness.
Import ListNotations.
Set Implicit Arguments.

Section Necessity.
Context {A : Type} (P : protocol_family A) (FT : class -> field -> class).

(* The machine obtained by allocating location 0 and copying its reference
   to variable 1.  Both epoch owners remain 0 throughout the scheduled calls. *)
Local Definition pair_machine c (t : list (epoch * A)) : machine A :=
  {| next_loc := 1; classes := update (fun _ => 0) 0 c;
     next_epoch := 2; owners := update (update (fun _ => 0) 0 0) 1 0;
     refs := put (put [] 0 (Some 0)) 1 (Some 1);
     heap := fun _ _ => None; events := t |}.

Local Lemma pair_machine_history c t :
  object_history (pair_machine c t) 0 = erase_tags t.
Proof.
  unfold object_history, object_events; simpl.
  assert (Howners : forall e, update (update (fun _ => 0) 0 0) 1 0 e = 0).
  { intros e; unfold update; now destruct (e =? 1), (e =? 0). }
  assert (Hfilter : filter
    (fun p : epoch * A => update (update (fun _ => 0) 0 0) 1 0 (fst p) =? 0) t = t).
  { induction t as [|[e a] t IH]; simpl; [reflexivity|].
    now rewrite Howners, IH. }
  now rewrite Hfilter.
Qed.

(* Start with arbitrary completed extensions of the two local prefixes.
   Induction on the chosen shuffle schedules each next event on its own
   binding.  Retirement succeeds even when either completed word is empty. *)
Local Lemma realize_shuffle c u v w : shuffle u v w ->
  forall hx hy g t,
    accepts P c (hx ++ u) = true -> accepts P c (hy ++ v) = true ->
    get g 0 = Some (c,hx) -> get g 1 = Some (c,hy) ->
    (forall x, x <> 0 -> x <> 1 -> get g x = None) ->
    exists s t' g', finish_free s /\
      check_stmt P FT s g = Some g' /\ all_complete P g' = true /\
      execution (pair_machine c t,s) (pair_machine c t',Skip) /\
      erase_tags t' = erase_tags t ++ w.
Proof.
  intros Hsh; induction Hsh; intros hx hy g t Hu Hv Hx Hy Hother;
    unfold qualifier, class in *.
  - rewrite app_nil_r in Hu, Hv.
    exists Skip,t,g; split; [reflexivity|]. split; [reflexivity|]. split.
    + apply all_complete_spec; intros x d z E; unfold qualifier, class in *.
      destruct (Nat.eq_dec x 0) as [->|H0].
      * rewrite Hx in E; inversion E; subst; exact Hu.
      * destruct (Nat.eq_dec x 1) as [->|H1].
        -- rewrite Hy in E; inversion E; subst; exact Hv.
        -- rewrite Hother in E by assumption; discriminate.
    + split; [constructor|now rewrite app_nil_r].
  - assert (Hcall : viable P c (hx ++ [a]) = true).
    { apply viable_spec. exists u. now rewrite <- app_assoc. }
    destruct (IHHsh (hx ++ [a]) hy (put g 0 (Some (c,hx ++ [a])))
      (t ++ [(0,a)])) as [s [t' [g' [HF [HC [HE [HR HW]]]]]]].
    + now rewrite <- app_assoc.
    + exact Hv.
    + apply get_put_same.
    + rewrite get_put_other by discriminate. exact Hy.
    + intros x H0 H1. rewrite get_put_other by exact H0. now apply Hother.
    + exists (Seq (Call 0 a) s),t',g'; split; [exact HF|]. split.
      * cbn [check_stmt check_step]. unfold qualifier, class in *. now rewrite Hx,Hcall.
      * split; [exact HE|]. split.
        -- eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|exact HR].
        -- rewrite HW. unfold erase_tags. rewrite map_app. simpl. now rewrite <- app_assoc.
  - assert (Hcall : viable P c (hy ++ [a]) = true).
    { apply viable_spec. exists v. now rewrite <- app_assoc. }
    destruct (IHHsh hx (hy ++ [a]) (put g 1 (Some (c,hy ++ [a])))
      (t ++ [(1,a)])) as [s [t' [g' [HF [HC [HE [HR HW]]]]]]].
    + exact Hu.
    + now rewrite <- app_assoc.
    + rewrite get_put_other by discriminate. exact Hx.
    + apply get_put_same.
    + intros x H0 H1. rewrite get_put_other by exact H1. now apply Hother.
    + exists (Seq (Call 1 a) s),t',g'; split; [exact HF|]. split.
      * cbn [check_stmt check_step]. unfold qualifier, class in *. now rewrite Hy,Hcall.
      * split; [exact HE|]. split.
        -- eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|exact HR].
        -- rewrite HW. unfold erase_tags. rewrite map_app. simpl. now rewrite <- app_assoc.
Qed.

Theorem completion_sound_requires_certified :
  (forall s m, check_program P FT s = true ->
    program_execution s initial_machine m ->
    forall l, l < next_loc m ->
      protocol P (classes m l) (object_history m l)) -> certified P.
Proof.
  intros Hsound c u v w Hu Hv Hsh.
  change (accepts P c u = true) in Hu. change (accepts P c v = true) in Hv.
  assert (Hinitial : viable P c [] = true) by (apply viable_spec; now exists u).
  destruct (@realize_shuffle c u v w Hsh [] []
    (put (put [] 0 (Some (c,[]))) 1 (Some (c,[]))) [] Hu Hv)
    as [body [t [g [HF [HC [HE [HR HW]]]]]]]; try reflexivity.
  - intros x H0 H1. rewrite !get_put_other by assumption. reflexivity.
  - set (s := Seq (New 0 c) (Seq (Copy 1 0) body)).
    set (m := clear_refs (pair_machine c t)).
    assert (Hsource : finish_free s) by (exact HF).
    assert (Hchecked : check_program P FT s = true).
    { apply source_checker_instrument; split; auto. exists g; split; auto.
      unfold s. cbn [check_stmt check_step]. unfold check_bind,retirable.
      simpl. rewrite Hinitial. simpl. rewrite Hinitial. exact HC. }
    assert (Hrun : program_execution s initial_machine m).
    { apply source_execution_instrument; auto. unfold s.
      eapply execution_seq; [apply execution_primitive; constructor|].
      eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|exact HR]. }
    pose proof (Hsound s m Hchecked Hrun 0 ltac:(unfold m; simpl; lia)) as Hdone.
    change (protocol P c (object_history (pair_machine c t) 0)) in Hdone.
    rewrite pair_machine_history, HW in Hdone. exact Hdone.
Qed.

Theorem completion_sound_iff_certified :
  (forall s m, check_program P FT s = true ->
    program_execution s initial_machine m ->
    forall l, l < next_loc m ->
      protocol P (classes m l) (object_history m l)) <->
  certified P.
Proof.
  split; [apply completion_sound_requires_certified|].
  intros HC s m HT HR. eapply typestate_completion_sound; eauto.
Qed.
End Necessity.
