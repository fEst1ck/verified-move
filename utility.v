Require Export Coq.Unicode.Utf8_core.
Require Import Coq.Lists.List.
Open Scope list_scope.
Import ListNotations.
(** Utility *)
Notation "A ⇀ B" := (A → option B) (at level 75, right associativity).

Inductive maps_to : ∀ {A B : Set} (f : A ⇀ B) (x : A) (y : B), Prop :=
  maps_to_ : ∀ {A B : Set} (f : A ⇀ B) (x : A) (y : B),
    f x = Some(y) →
    maps_to f x y.

Axiom UIP : ∀ {A : Type} {x y : A} (p1 p2 : x = y), p1 = p2.

Lemma maps_to_up : ∀ {A B : Set} {f : A ⇀ B} {x : A} {y : B} (p1 p2 : maps_to f x y), p1 = p2.
Proof.
  intros.
  destruct p1.
  destruct p2.
  assert (e = e0) by apply UIP.
  rewrite H.
  reflexivity.
Qed.

Class EqDec (A : Type) := {
  eq_dec : ∀ (x y : A), {x = y} + {x <> y}
}.

Definition remove {X : Set} {Y : Set} `{eq : EqDec X} (f : X ⇀ Y) (a : X) : X ⇀ Y :=
  fun x => match eq_dec x a with
    | left _ => None
    | right _ => f x
    end.

Definition update {X : Set} {Y : Set} `{eq : EqDec X} (f : X ⇀ Y) (a : X) (b : Y) : X ⇀ Y :=
  fun x => match eq_dec x a with
    | left _ => Some(b)
    | right _ => f x
    end.

Inductive list_contains {A : Type} : list A → A → Prop :=
  | list_contains_car : ∀ (x : A), list_contains [ x ] x
  | list_contains_cdr : ∀ (x y : A) (l : list A),
    list_contains l y → list_contains (x :: l) y
.