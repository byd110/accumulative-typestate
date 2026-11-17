(* Alias-oblivious typing and a total executable path-sensitive checker. *)
From Coq Require Import List Arith Bool.
From Accumulation Require Import syntax trace_languages protocols.
Import ListNotations.
Set Implicit Arguments.

Definition qualifier (A : Type) := (class * list A)%type.
Definition environment (A : Type) := fmap (qualifier A).
Definition qualifier_language {A} (P : protocol_family A) (q : qualifier A) :=
  residual (protocol P (fst q)) (snd q).

Section Typestate.
Context {A : Type} (P : protocol_family A) (field_type : class -> field -> class).
Definition retirable (g : environment A) x :=
  match get g x with None => true | Some (c,w) => accepts P c w end.
Definition check_bind (g : environment A) x c :=
  if retirable g x && viable P c [] then Some (put g x (Some (c,[]))) else None.

Definition check_step (i : instruction A) (g : environment A) : option (environment A) :=
  match i with
  | New x c => check_bind g x c
  | Copy x y => match get g y with
      | Some (c,_) => check_bind g x c | None => None end
  | Load x y f => match get g y with
      | Some (c,_) => check_bind g x (field_type c f) | None => None end
  | Store x f y => match get g x, get g y with
      | Some (c,_), Some (d,_) => if Nat.eqb (field_type c f) d then Some g else None
      | _,_ => None end
  | Call x a => match get g x with
      | Some (c,w) => if viable P c (w ++ [a])
          then Some (put g x (Some (c,w ++ [a]))) else None
      | None => None end
  | Finish x => match get g x with
      | Some (c,w) => if accepts P c w then Some (put g x None) else None
      | None => None end
  end.

Inductive type_step : environment A -> instruction A -> environment A -> Prop :=
| type_new g x c : retirable g x = true -> viable P c [] = true ->
    type_step g (New x c) (put g x (Some (c,[])))
| type_copy g x y c w : get g y = Some (c,w) -> retirable g x = true ->
    viable P c [] = true -> type_step g (Copy x y) (put g x (Some (c,[])))
| type_load g x y f c w : get g y = Some (c,w) -> retirable g x = true ->
    viable P (field_type c f) [] = true ->
    type_step g (Load x y f) (put g x (Some (field_type c f,[])))
| type_store g x f y c w d v : get g x = Some (c,w) -> get g y = Some (d,v) ->
    field_type c f = d -> type_step g (Store x f y) g
| type_call g x a c w : get g x = Some (c,w) -> viable P c (w ++ [a]) = true ->
    type_step g (Call x a) (put g x (Some (c,w ++ [a])))
| type_finish g x c w : get g x = Some (c,w) -> accepts P c w = true ->
    type_step g (Finish x) (put g x None).

Lemma check_bind_spec g x c g' : check_bind g x c = Some g' ->
  retirable g x = true /\ viable P c [] = true /\ g' = put g x (Some (c,[])).
Proof.
  unfold check_bind; destruct (retirable g x && viable P c []) eqn:E; try discriminate.
  intros H; inversion H; subst. apply andb_true_iff in E; tauto.
Qed.
Lemma check_step_sound i g g' : check_step i g = Some g' -> type_step g i g'.
Proof.
  destruct i as [x c|x y|x y f|x f y|x a|x]; simpl.
  - intros H; apply check_bind_spec in H; destruct H as [H1 [H2 ->]]; constructor; auto.
  - destruct (get g y) as [[c w]|] eqn:E; try discriminate.
    intros H; apply check_bind_spec in H; destruct H as [H1 [H2 ->]]; econstructor; eauto.
  - destruct (get g y) as [[c w]|] eqn:E; try discriminate.
    intros H; apply check_bind_spec in H; destruct H as [H1 [H2 ->]]; econstructor; eauto.
  - destruct (get g x) as [[c w]|] eqn:Ex; try discriminate.
    destruct (get g y) as [[d v]|] eqn:Ey; try discriminate.
    destruct (field_type c f =? d) eqn:E; try discriminate.
    intros H; inversion H; subst. apply Nat.eqb_eq in E; econstructor; eauto.
  - destruct (get g x) as [[c w]|] eqn:E; try discriminate.
    destruct (viable P c (w ++ [a])) eqn:Hv; try discriminate.
    intros H; inversion H; subst; econstructor; eauto.
  - destruct (get g x) as [[c w]|] eqn:E; try discriminate.
    destruct (accepts P c w) eqn:Ha; try discriminate.
    intros H; inversion H; subst; econstructor; eauto.
Qed.
Lemma check_step_complete g i g' : type_step g i g' -> check_step i g = Some g'.
Proof.
  intros H; destruct H; unfold qualifier, class in *.
  - cbn [check_step]. unfold check_bind. rewrite H, H0. reflexivity.
  - cbn [check_step]; unfold qualifier, class in *. rewrite H. unfold check_bind. rewrite H0, H1. reflexivity.
  - cbn [check_step]; unfold qualifier, class in *. rewrite H. unfold check_bind. rewrite H0, H1. reflexivity.
  - cbn [check_step]; unfold qualifier, class in *. rewrite H, H0, H1, Nat.eqb_refl. reflexivity.
  - cbn [check_step]; unfold qualifier, class in *. rewrite H, H0. reflexivity.
  - cbn [check_step]; unfold qualifier, class in *. rewrite H, H0. reflexivity.
Qed.

Fixpoint check_trace (is : list (instruction A)) (g : environment A) :=
  match is with
  | [] => Some g
  | i :: rest => match check_step i g with
      | Some g' => check_trace rest g' | None => None end
  end.
Inductive typed_trace : environment A -> list (instruction A) -> environment A -> Prop :=
| typed_nil g : typed_trace g [] g
| typed_cons g i g' is g'' : type_step g i g' -> typed_trace g' is g'' ->
    typed_trace g (i::is) g''.

Lemma check_trace_spec is g g' : check_trace is g = Some g' <-> typed_trace g is g'.
Proof.
  split.
  - revert g g'; induction is as [|i is IH]; intros g g'; simpl.
    + intros H; inversion H; subst; constructor.
    + destruct (check_step i g) as [gm|] eqn:E; try discriminate.
      intros H; econstructor; [apply check_step_sound; exact E|now apply IH].
  - intros H; induction H; simpl; auto. rewrite (check_step_complete H). exact IHtyped_trace.
Qed.
Definition check_program (s : statement A) :=
  forallb (fun is => match check_trace is [] with
                     | Some g => emptyb g | None => false end) (paths s).

Lemma check_program_path s is : check_program s = true -> path s is ->
  exists g, typed_trace [] is g /\ forall x, get g x = None.
Proof.
  unfold check_program; rewrite forallb_forall; intros H Hp.
  apply paths_spec in Hp. specialize (H is Hp).
  destruct (check_trace is []) as [g|] eqn:E; try discriminate.
  exists g; split; [now apply check_trace_spec|now apply emptyb_spec].
Qed.
Lemma typed_trace_split g p q g' : typed_trace g (p ++ q) g' ->
  exists gm, typed_trace g p gm /\ typed_trace gm q g'.
Proof.
  revert g; induction p as [|i p IH]; intros g H; simpl in H.
  - exists g; split; [constructor|exact H].
  - inversion H; subst. match goal with
      Ht : typed_trace _ (p ++ q) _ |- _ => destruct (IH _ Ht) as [gm [Hp Hq]] end.
    exists gm; split; [econstructor; eauto|exact Hq].
Qed.
End Typestate.
