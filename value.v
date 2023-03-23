Require Import Coq.Lists.List.
Open Scope list_scope.
Import ListNotations.
Require Import Resources.utility.
Require Import Resources.name.
Require Import Resources.type.
(** Values *)
Parameter Signer : Set.
Parameter UnsignedInt64 : Set.
Parameter Bytes : Set.

Parameter Tag : Set.

Parameter tag_dec_eq :  ∀ (x y : Tag), {x = y} + {x <> y}.
Instance tag_eq_dec : EqDec Tag := {
  eq_dec := tag_dec_eq
}.

Inductive Resource : Set :=
  | resource : Tag → StructType → list Value -> Resource

with Struct : Set :=
  | struct : StructType → list UnrestrictedValue -> Struct

with PrimitiveValue : Set :=
  | accountAddressValue : AccountAddress -> PrimitiveValue
  | signerValue : Signer -> PrimitiveValue
  | boolValue : bool -> PrimitiveValue
  | unsignedInt64Value : UnsignedInt64 -> PrimitiveValue
  | bytesValue : Bytes -> PrimitiveValue

with UnrestrictedValue : Set :=
  | structValue : Struct -> UnrestrictedValue
  | primitiveValue : PrimitiveValue -> UnrestrictedValue

with Value : Set :=
  | resourceValue : Resource -> Value
  | unrestrictiveValue : UnrestrictedValue -> Value.

Definition tag_of (r : Resource) : Tag :=
  match r with
  | resource t _ _ => t
  end.

Coercion structValue : Struct >-> UnrestrictedValue.
Coercion resourceValue : Resource >-> Value.
Coercion unrestrictiveValue : UnrestrictedValue >-> Value.
Coercion primitiveValue : PrimitiveValue >-> UnrestrictedValue.
Coercion boolValue : bool >-> PrimitiveValue.
Coercion unsignedInt64Value : UnsignedInt64 >-> PrimitiveValue.
Coercion accountAddressValue : AccountAddress >-> PrimitiveValue.
Coercion bytesValue : Bytes >-> PrimitiveValue.

Inductive resource_contains_t : Resource → Tag → Set :=
  | rct_root : ∀ {r}, resource_contains_t r (tag_of r)
  | rct_field : ∀ {t1 t2} {τ} {field_vals : list Value} {r : Resource},
    list_contains field_vals r →
    resource_contains_t r t2 →
    resource_contains_t (resource t1 τ field_vals) t2
.

Definition RuntimeValue := Value.