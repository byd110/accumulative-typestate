(* Optional inheritance of source histories in the structural checker. *)
From Coq Require Import List Bool Arith.
From Accumulation Require Import syntax trace_languages protocols typestate.
Import ListNotations.
Set Implicit Arguments.

Definition residual_shuffle_closed {A} (K : language A) :=
  forall p, shuffle_closed (residual K p).
Definition copying_certified {A} (P : protocol_family A) (copy_history : class -> bool) :=
  certified P /\ forall c, copy_history c = true -> residual_shuffle_closed (protocol P c).

Section CopyingChecker.
Context {A : Type} (P : protocol_family A) (FT : class -> field -> class).
Variable copy_history : class -> bool.
Definition check_step_with_copy (i : statement A) (g : environment A) :=
  match i with
  | Copy x y =>
      match get g y with
      | Some (c,w) =>
          if copy_history c then
            if retirable P g x then Some (put g x (Some (c,w))) else None
          else check_bind P g x c
      | None => None
      end
  | _ => check_step P FT i g
  end.

Inductive type_step_with_copy : environment A -> statement A -> environment A -> Prop :=
| copy_type_new g x c : retirable P g x = true -> viable P c [] = true ->
    type_step_with_copy g (New x c) (put g x (Some (c,[])))
| copy_type_copy g x y c w : get g y = Some (c,w) -> retirable P g x = true ->
    (if copy_history c then True else viable P c [] = true) ->
    type_step_with_copy g (Copy x y)
      (put g x (Some (c,if copy_history c then w else [])))
| copy_type_load g x y f c w : get g y = Some (c,w) -> retirable P g x = true ->
    viable P (FT c f) [] = true ->
    type_step_with_copy g (Load x y f) (put g x (Some (FT c f,[])))
| copy_type_store g x f y c w d v : get g x = Some (c,w) -> get g y = Some (d,v) ->
    FT c f = d -> type_step_with_copy g (Store x f y) g
| copy_type_call g x a c w : get g x = Some (c,w) -> viable P c (w ++ [a]) = true ->
    type_step_with_copy g (Call x a) (put g x (Some (c,w ++ [a])))
| copy_type_finish g : all_complete P g = true -> type_step_with_copy g Finish [].

Lemma copy_step_spec g x y g' :
  check_step_with_copy (Copy x y) g = Some g' <->
  exists c w, get g y = Some (c,w) /\ retirable P g x = true /\
    (if copy_history c then g' = put g x (Some (c,w))
     else viable P c [] = true /\ g' = put g x (Some (c,[]))).
Proof.
  split.
  - unfold check_step_with_copy.
    destruct (get g y) as [[c w]|] eqn:E. 2: discriminate.
    intros H. exists c, w. split. reflexivity.
    destruct (copy_history c) eqn:M.
    + destruct (retirable P g x) eqn:R. 2: discriminate.
      inversion H. auto.
    + apply (check_bind_spec P FT) in H. tauto.
  - intros [c [w [E [R H]]]]. unfold check_step_with_copy. rewrite E.
    destruct (copy_history c) eqn:M.
    + rewrite R, H. reflexivity.
    + destruct H as [V H]. unfold check_bind. rewrite R, V, H. reflexivity.
Qed.

Lemma check_step_with_copy_sound i g g' :
  check_step_with_copy i g = Some g' -> type_step_with_copy g i g'.
Proof.
  destruct i as [|x c|x y|x y f|x f y|x a| |s t];
    cbn [check_step_with_copy check_step]; try discriminate.
  - intros H. apply (check_bind_spec P FT) in H.
    destruct H as [HR [HV ->]]. constructor; assumption.
  - destruct (get g y) as [[c w]|] eqn:E; try discriminate.
    destruct (copy_history c) eqn:M.
    + destruct (retirable P g x) eqn:R; try discriminate.
      intros H. inversion H; subst.
      replace w with (if copy_history c then w else []) by now rewrite M.
      apply copy_type_copy with (w := w); auto. now rewrite M.
    + intros H. apply (check_bind_spec P FT) in H. destruct H as [R [V ->]].
      replace (@nil A) with (if copy_history c then w else []) by now rewrite M.
      apply copy_type_copy with (w := w); auto. now rewrite M.
  - destruct (get g y) as [[c w]|] eqn:E; try discriminate.
    intros H. apply (check_bind_spec P FT) in H. destruct H as [R [V ->]].
    econstructor; eauto.
  - destruct (get g x) as [[c w]|] eqn:Ex; try discriminate.
    destruct (get g y) as [[d v]|] eqn:Ey; try discriminate.
    destruct (FT c f =? d) eqn:E; try discriminate.
    intros H. inversion H; subst. apply Nat.eqb_eq in E. econstructor; eauto.
  - destruct (get g x) as [[c w]|] eqn:E; try discriminate.
    destruct (viable P c (w ++ [a])) eqn:V; try discriminate.
    intros H. inversion H; subst. econstructor; eauto.
  - destruct (all_complete P g) eqn:E; try discriminate.
    intros H. inversion H; subst. constructor. exact E.
Qed.
Lemma check_step_with_copy_complete g i g' :
  type_step_with_copy g i g' -> check_step_with_copy i g = Some g'.
Proof.
  intros H. destruct H; cbn [check_step_with_copy check_step]; unfold qualifier, class in *.
  - unfold check_bind. rewrite H, H0. reflexivity.
  - rewrite H. destruct (copy_history c) eqn:M.
    + now rewrite H0.
    + unfold check_bind. now rewrite H0, H1.
  - rewrite H. unfold check_bind. now rewrite H0, H1.
  - now rewrite H, H0, H1, Nat.eqb_refl.
  - now rewrite H, H0.
  - now rewrite H.
Qed.

Fixpoint check_stmt_with_copy (s : statement A) (g : environment A) : option (environment A) :=
  match s with
  | Skip => Some g
  | Seq s t => match check_stmt_with_copy s g with
      | Some gm => check_stmt_with_copy t gm | None => None end
  | _ => check_step_with_copy s g
  end.
Inductive typed_stmt_with_copy : environment A -> statement A -> environment A -> Prop :=
| copy_typed_primitive g i g' : type_step_with_copy g i g' -> typed_stmt_with_copy g i g'
| copy_type_skip g : typed_stmt_with_copy g Skip g
| copy_type_seq g s gm t g' : typed_stmt_with_copy g s gm -> typed_stmt_with_copy gm t g' ->
    typed_stmt_with_copy g (Seq s t) g'.

Lemma check_stmt_with_copy_spec s g g' :
  check_stmt_with_copy s g = Some g' <-> typed_stmt_with_copy g s g'.
Proof.
  split.
  - revert g g'. induction s; intros g g' H; cbn [check_stmt_with_copy] in H.
    + inversion H; subst. apply copy_type_skip.
    + apply copy_typed_primitive. now apply check_step_with_copy_sound.
    + apply copy_typed_primitive. now apply check_step_with_copy_sound.
    + apply copy_typed_primitive. now apply check_step_with_copy_sound.
    + apply copy_typed_primitive. now apply check_step_with_copy_sound.
    + apply copy_typed_primitive. now apply check_step_with_copy_sound.
    + apply copy_typed_primitive. now apply check_step_with_copy_sound.
    + destruct (check_stmt_with_copy s1 g) as [gm|] eqn:E; try discriminate.
      eapply copy_type_seq. apply IHs1. exact E. apply IHs2. exact H.
  - intros H. induction H.
    + pose proof (check_step_with_copy_complete H) as E.
      destruct H; exact E.
    + reflexivity.
    + simpl. now rewrite IHtyped_stmt_with_copy1.
Qed.

Definition check_program_with_copy (s : statement A) :=
  finish_freeb s && match check_stmt_with_copy (instrument s) [] with
                   | Some _ => true | None => false end.
Lemma check_stmt_with_copy_instrument s g g' :
  check_stmt_with_copy (instrument s) g = Some g' -> g' = [].
Proof.
  unfold instrument. simpl.
  destruct (check_stmt_with_copy s g) as [gm|]; try discriminate.
  cbn [check_step_with_copy check_step].
  destruct (all_complete P gm); intros H; inversion H. reflexivity.
Qed.
Lemma check_program_with_copy_spec s :
  check_program_with_copy s = true <->
  finish_free s /\ typed_stmt_with_copy [] (instrument s) [].
Proof.
  unfold check_program_with_copy. rewrite andb_true_iff. split.
  - intros [HF HC]. split. exact HF.
    destruct (check_stmt_with_copy (instrument s) []) as [g|] eqn:E; try discriminate.
    pose proof (check_stmt_with_copy_instrument s [] E) as ->.
    now apply check_stmt_with_copy_spec.
  - intros [HF HT]. split. exact HF.
    apply check_stmt_with_copy_spec in HT. now rewrite HT.
Qed.
End CopyingChecker.

Lemma fresh_step_unchanged {A} (P : protocol_family A) FT i g :
  check_step_with_copy P FT (fun _ => false) i g = check_step P FT i g.
Proof. destruct i; reflexivity. Qed.
Lemma fresh_stmt_unchanged {A} (P : protocol_family A) FT s g :
  check_stmt_with_copy P FT (fun _ => false) s g = check_stmt P FT s g.
Proof.
  revert g. induction s; intros g; try reflexivity.
  simpl. rewrite IHs1. destruct (check_stmt P FT s1 g). apply IHs2. reflexivity.
Qed.
Theorem fresh_program_unchanged {A} (P : protocol_family A) FT s :
  check_program_with_copy P FT (fun _ => false) s = check_program P FT s.
Proof.
  unfold check_program_with_copy, check_program. now rewrite fresh_stmt_unchanged.
Qed.
