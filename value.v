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
  | struct : StructType → list Value -> Struct

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

Inductive resource_contains_r : Resource → Resource → Set :=
  | rc_id : ∀ {r}, resource_contains_r r r
  | rc_field : ∀ {t} {τ} {field_vals : list Value} {r1 r2 : Resource},
    list_contains field_vals r1 →
    resource_contains_r r1 r2 →
    resource_contains_r (resource t τ field_vals) r2
.

Inductive resource_contains_t : Resource → Tag → Set :=
  | rct_root : ∀ {r}, resource_contains_t r (tag_of r)
  | rct_field : ∀ {t1 t2} {τ} {field_vals : list Value} {r : Resource},
    list_contains field_vals r →
    resource_contains_t r t2 →
    resource_contains_t (resource t1 τ field_vals) t2
.

(** References  *)
Inductive Qualifier : Set :=
  | mut : Qualifier
  | immut : Qualifier.

Inductive Root : Set :=
  | local_root : LocalVariable -> Root
  | global_root : GlobalResourceID -> Root.

Coercion local_root : LocalVariable >-> Root.
Coercion global_root : GlobalResourceID >-> Root.

Definition Path := list FieldName.

Parameter read_val : Value → Path → Value → Prop.

Axiom read_unrestricted : ∀ (u : UnrestrictedValue) (p : Path) (v : Value),
  read_val u p v →
  ∃ (u' : UnrestrictedValue), v = u'.

Axiom read_resource : ∀ (s : Value) (p : Path) (a : Resource),
read_val s p a →
∃ (b : Resource), s = b.

Record Reference : Set := {
  root : Root;
  access_path : Path;
  mutability : Qualifier;
}.

Inductive is_mut : Reference → Prop :=
  | is_mut_ref : ∀ (r : Root) (p : Path), is_mut {|
    root := r; access_path := p; mutability := mut;
  |}.

Inductive is_immut : Reference → Prop :=
  | is_immut_ref : ∀ (r : Root) (p : Path), is_immut {|
  root := r; access_path := p; mutability := immut;
  |}.

Definition extend_ref (r : Reference) (e : FieldName) : Reference :=
  match r with
  | {| root := root ; access_path := access_path; mutability := mutability |} => {|
    root := root;
    access_path := access_path ++ [ e ];
    mutability := mutability;
  |}
  end.

Definition freeze_ref (r : Reference) : Reference :=
  match r with
  | {| root := root; access_path := access_path; mutability := _ |} => {|
      root := root;
      access_path := access_path;
      mutability := immut;
  |}
  end.

Inductive RuntimeValue : Set :=
  | val : Value → RuntimeValue
  | ref_val : Reference → RuntimeValue.

Coercion val : Value >-> RuntimeValue.
Coercion ref_val : Reference >-> RuntimeValue.
Coercion foo (v : UnrestrictedValue) := val (unrestrictiveValue v).