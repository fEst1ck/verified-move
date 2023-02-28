Require Export Coq.Unicode.Utf8_core.
(** Utility *)
Notation "A ⇀ B" := (A → option B) (at level 75, right associativity).

Inductive maps_to : ∀ {A B : Set} (f : A ⇀ B) (x : A) (y : B), Prop :=
  maps_to_ : ∀ {A B : Set} (f : A ⇀ B) (x : A) (y : B),
    f x = Some(y) →
    maps_to f x y.

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