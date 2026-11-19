(* Alias-oblivious typing and a total executable structural checker. *)
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

Definition all_complete (g : environment A) :=
  forallb (fun p => retirable g (fst p)) g.
Lemma all_complete_spec g : all_complete g = true <->
  forall x c w, get g x = Some (c,w) -> accepts P c w = true.
Proof.
  unfold all_complete; rewrite forallb_forall; split.
  - intros H x c w E. destruct (get_some_key g x E) as [ov Hin].
    specialize (H (x,ov) Hin). unfold retirable in H; simpl in H. now rewrite E in H.
  - intros H [x ov] Hin. unfold retirable; simpl.
    destruct (get g x) as [[c w]|] eqn:E; auto. eapply H; eauto.
Qed.

Definition check_step (i : statement A) (g : environment A) : option (environment A) :=
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
  | Finish => if all_complete g then Some [] else None
  | Skip | Seq _ _ => None
  end.

Inductive type_step : environment A -> statement A -> environment A -> Prop :=
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
| type_finish g : all_complete g = true -> type_step g Finish [].

Lemma check_bind_spec g x c g' : check_bind g x c = Some g' ->
  retirable g x = true /\ viable P c [] = true /\ g' = put g x (Some (c,[])).
Proof.
  unfold check_bind; destruct (retirable g x && viable P c []) eqn:E; try discriminate.
  intros H; inversion H; subst. apply andb_true_iff in E; tauto.
Qed.
Lemma check_step_sound i g g' : check_step i g = Some g' -> type_step g i g'.
Proof.
  destruct i as [ | x c | x y | x y f | x f y | x a | | s t ]; simpl; try discriminate.
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
  - destruct (all_complete g) eqn:E; try discriminate.
    intros H; inversion H; subst; constructor; auto.
Qed.
Lemma check_step_complete g i g' : type_step g i g' -> check_step i g = Some g'.
Proof.
  intros H; destruct H; unfold qualifier, class in *.
  - cbn [check_step]. unfold check_bind. rewrite H, H0. reflexivity.
  - cbn [check_step]; unfold qualifier, class in *. rewrite H. unfold check_bind. rewrite H0, H1. reflexivity.
  - cbn [check_step]; unfold qualifier, class in *. rewrite H. unfold check_bind. rewrite H0, H1. reflexivity.
  - cbn [check_step]; unfold qualifier, class in *. rewrite H, H0, H1, Nat.eqb_refl. reflexivity.
  - cbn [check_step]; unfold qualifier, class in *. rewrite H, H0. reflexivity.
  - cbn [check_step]; rewrite H. reflexivity.
Qed.

Inductive typed_stmt : environment A -> statement A -> environment A -> Prop :=
| typed_primitive g i g' : type_step g i g' -> typed_stmt g i g'
| type_skip g : typed_stmt g Skip g
| type_seq g s gm t g' : typed_stmt g s gm -> typed_stmt gm t g' ->
    typed_stmt g (Seq s t) g'.
Fixpoint check_stmt (s : statement A) (g : environment A) : option (environment A) :=
  match s with
  | Skip => Some g
  | Seq s t => match check_stmt s g with Some gm => check_stmt t gm | None => None end
  | _ => check_step s g
  end.
Lemma check_stmt_primitive i g g' : type_step g i g' -> check_stmt i g = Some g'.
Proof. intros H; destruct H; cbn [check_stmt]; apply check_step_complete; econstructor; eauto. Qed.
Theorem check_stmt_spec s g g' : check_stmt s g = Some g' <-> typed_stmt g s g'.
Proof.
  split.
  - revert g g'; induction s; intros g g' H;
      try solve [apply typed_primitive; now apply check_step_sound].
    + simpl in H; inversion H; subst; apply type_skip.
    + simpl in H. destruct (check_stmt s1 g) as [gm|] eqn:E; try discriminate.
      eapply type_seq; [eapply IHs1; exact E|now apply IHs2].
  - intros H; induction H; simpl; auto using check_stmt_primitive.
    now rewrite IHtyped_stmt1.
Qed.
Lemma typed_stmt_skip g g' : typed_stmt g Skip g' -> g'=g.
Proof. intros H; inversion H; subst; auto. inversion H0. Qed.
Lemma typed_stmt_primitive g i g' :
  (forall s t, i <> Seq s t) -> i <> Skip -> typed_stmt g i g' -> type_step g i g'.
Proof. intros HS HK H; inversion H; subst; auto.
  - exfalso; apply HK; reflexivity.
  - exfalso; eapply HS; reflexivity.
Qed.
Lemma typed_stmt_seq g s t g' : typed_stmt g (Seq s t) g' ->
  exists gm, typed_stmt g s gm /\ typed_stmt gm t g'.
Proof. intros H; inversion H; subst; eauto. inversion H0. Qed.
Lemma typed_stmt_finish g g' : typed_stmt g Finish g' -> all_complete g=true /\ g'=[].
Proof. intros H; inversion H; subst. inversion H0; auto. Qed.

Definition check_program (s : statement A) :=
  finish_freeb s && match check_stmt (instrument s) [] with Some _ => true | None => false end.
Theorem check_program_spec s : check_program s = true <->
  finish_free s /\ typed_stmt [] (instrument s) [].
Proof.
  unfold check_program, finish_free; rewrite andb_true_iff; split.
  - intros [HF HC]; split; auto.
    destruct (check_stmt (instrument s) []) as [g|] eqn:E; try discriminate.
    apply check_stmt_spec in E.
    destruct (typed_stmt_seq E) as [gm [Hs Hf]].
    destruct (typed_stmt_finish Hf) as [_ ->]. exact E.
  - intros [HF HT]; split; auto. apply check_stmt_spec in HT. now rewrite HT.
Qed.
Theorem source_typing_instrument s g : typed_stmt [] s g -> all_complete g=true ->
  typed_stmt [] (instrument s) [].
Proof. intros Hs Hf. eapply type_seq; [exact Hs|apply typed_primitive; now constructor]. Qed.
Theorem source_checker_instrument s : check_program s = true <->
  finish_free s /\ exists g, check_stmt s []=Some g /\ all_complete g=true.
Proof.
  rewrite check_program_spec; split.
  - intros [HF HT]; split; auto. destruct (typed_stmt_seq HT) as [g [Hs Hf]].
    exists g; split; [now apply check_stmt_spec|exact (proj1 (typed_stmt_finish Hf))].
  - intros [HF [g [Hs Hf]]]; split; auto. apply source_typing_instrument with g; auto.
    now apply check_stmt_spec.
Qed.
End Typestate.
