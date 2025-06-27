(* the basic syntax for checkol *)

Require Import String.
Require Import List.
Import ListNotations.
Require Import RegLang.

(* Identifiers *)

Definition var := nat.
Definition class_name := nat.
Definition field_name := nat.
Definition method_name := nat.
Definition address := nat.

(* Types *)
Inductive ty : Type :=
| TyObject
| TyClass (cname : nat)().

(* Expressions *)
Inductive expr : Type :=
| EVar (x : )

(* Expressions *)
Inductive expr : Type :=
| EVar (x : var)
| EInt (n : nat)
| EBool (b : bool)
| EField (e : expr) (f : field_name)
| ECall (e : expr) (m : method_name) (args : list expr)
| ENew (c : class_name) (args : list expr)
| EBinOp (op : binop) (e1 e2 : expr)
| EUnOp (op : unop) (e : expr)

with binop : Type :=
| OpAdd | OpSub | OpMul | OpDiv
| OpEq | OpNeq | OpLt | OpLe | OpGt | OpGe
| OpAnd | OpOr

with unop : Type :=
| OpNeg | OpNot.

(* Statements *)
Inductive stmt : Type :=
| SSkip
| SAssign (x : var) (e : expr)
| SFieldAssign (e : expr) (f : field_name) (rhs : expr)
| SSeq (s1 s2 : stmt)
| SIf (cond : expr) (s_then s_else : stmt)
| SWhile (cond : expr) (body : stmt)
| SReturn (e : option expr).

(* Method and class definitions *)
Record param := {
    param_name : var;
    param_type : ty
}.

Record field := {
    field_name_ : field_name;
    field_type : ty
}.

Record method := {
    method_name_ : method_name;
    method_params : list param;
    method_ret_type : option ty;
    method_body : stmt
}.

Record class := {
    class_name_ : class_name;
    class_fields : list field;
    class_methods : list method
}.

Definition program := list class.

Local Open Scope string_scope.

Example testname := "TestClass".


(* Example 1: A simple Counter class *)
Definition counter_class : class := {|
    class_name_ := "Counter";
    class_fields := [{| field_name_ := "value"; field_type := TyInt |}];
    class_methods := [
        {| method_name_ := "inc";
             method_params := [];
             method_ret_type := None;
             method_body := SFieldAssign (EVar "this") "value"
                 (EBinOp OpAdd (EField (EVar "this") "value") (EInt 1))
        |};
        {| method_name_ := "get";
             method_params := [];
             method_ret_type := Some TyInt;
             method_body := SReturn (Some (EField (EVar "this") "value"))
        |}
    ]
|}.

Definition counter_program : program := [counter_class].

(* Example 2: A Pair class with swap method *)
Definition pair_class : class := {|
    class_name_ := "Pair";
    class_fields := [
        {| field_name_ := "fst"; field_type := TyInt |};
        {| field_name_ := "snd"; field_type := TyInt |}
    ];
    class_methods := [
        {| method_name_ := "swap";
             method_params := [];
             method_ret_type := None;
             method_body :=
                 SSeq
                     (SAssign "tmp" (EField (EVar "this") "fst"))
                     (SSeq
                         (SFieldAssign (EVar "this") "fst" (EField (EVar "this") "snd"))
                         (SFieldAssign (EVar "this") "snd" (EVar "tmp")))
        |}
    ]
|}.

Definition pair_program : program := [pair_class].