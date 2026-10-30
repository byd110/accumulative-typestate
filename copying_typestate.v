(* Optional inheritance of source histories. The original checker is unchanged. *)
From Coq Require Import List Bool.
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
Definition check_step_with_copy (i : instruction A) (g : environment A) :=
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
Fixpoint check_trace_with_copy (is : list (instruction A)) (g : environment A) :=
  match is with
  | [] => Some g
  | i :: rest =>
      match check_step_with_copy i g with
      | Some g' => check_trace_with_copy rest g'
      | None => None
      end
  end.
Definition check_program_with_copy (s : statement A) :=
  forallb (fun is => match check_trace_with_copy is [] with
                    | Some g => emptyb g | None => false end) (paths s).
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
Lemma check_trace_with_copy_app p q g :
  check_trace_with_copy (p ++ q) g =
  match check_trace_with_copy p g with
  | Some gm => check_trace_with_copy q gm | None => None end.
Proof.
  revert g. induction p as [|i p IH]. reflexivity.
  intros g. simpl. destruct (check_step_with_copy i g). apply IH. reflexivity.
Qed.
Lemma check_program_with_copy_path s p : check_program_with_copy s = true -> path s p ->
  exists g, check_trace_with_copy p [] = Some g /\ forall x, get g x = None.
Proof.
  unfold check_program_with_copy. rewrite forallb_forall. intros H Hp.
  apply paths_spec in Hp. specialize (H p Hp).
  destruct (check_trace_with_copy p []) as [g|] eqn:E. 2: discriminate.
  exists g. split. reflexivity. now apply emptyb_spec.
Qed.
End CopyingChecker.
Lemma fresh_step_unchanged {A} (P : protocol_family A) FT i g :
  check_step_with_copy P FT (fun _ => false) i g = check_step P FT i g.
Proof.
  destruct i. all: try reflexivity.
Qed.
Lemma fresh_trace_unchanged {A} (P : protocol_family A) FT is g :
  check_trace_with_copy P FT (fun _ => false) is g = check_trace P FT is g.
Proof.
  revert g. induction is as [|i is IH]. reflexivity.
  intros g. simpl. rewrite fresh_step_unchanged.
  destruct (check_step P FT i g). apply IH. reflexivity.
Qed.
Theorem fresh_program_unchanged {A} (P : protocol_family A) FT s :
  check_program_with_copy P FT (fun _ => false) s = check_program P FT s.
Proof.
  unfold check_program_with_copy, check_program.
  generalize (paths s). intros ps. induction ps as [|p ps IH]. reflexivity.
  simpl. rewrite fresh_trace_unchanged, IH. reflexivity.
Qed.
