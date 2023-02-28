Require Import Coq.Unicode.Utf8_core.
Open Scope list_scope.

(** Partial Maps  *)
Notation "A ⇀ B" := (A → option B) (at level 75, right associativity).

Inductive maps_to : ∀ {A B : Set} (f : A ⇀ B) (x : A) (y : B), Prop :=
  maps_to_ : ∀ {A B : Set} (f : A ⇀ B) (x : A) (y : B),
    f x = Some(y) →
    maps_to f x y.

Notation "f x ↦ y" := (maps_to f x y) (at level 75, right associativity).

Class EqDec (A : Type) := {
  eq_dec : ∀ (x y : A), {x = y} + {x <> y}
}.

(** Parameters  *)
Variable LocalVariable : Set.
Variable var_dec_eq :  ∀ (x y : LocalVariable), {x = y} + {x <> y}.
Instance var_eq_dec : EqDec LocalVariable := {
  eq_dec := var_dec_eq
}.

Variable FieldName : Set.
Variable StructName : Set.
Variable ModuleName : Set.
Variable AccountAddress : Set.

(** Values *)
Variable Signer : Set.
Variable UnsignedInt64 : Set.
Variable Bytes : Set.

Inductive Resource : Set :=
  | resource : (FieldName ⇀ Value) -> Resource

with Struct : Set :=
  | struct : (FieldName ⇀ UnrestrictedValue) -> Struct

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

Coercion resourceValue : Resource >-> Value.
Coercion unrestrictiveValue : UnrestrictedValue >-> Value.

(** * Paths and Trees *)
Definition Path := list FieldName.

(** * States  *)
(** The set of memory locations  *)
Variable Location : Set.
Variable loc_dec_eq : ∀ (x y : Location), {x = y} + {x <> y}.
Instance location_eq_dec : EqDec Location := {
  eq_dec := loc_dec_eq
}.

Definition remove {X : Set} {Y : Set} `{eq : EqDec X} (f : X ⇀ Y) (a : X) : X ⇀ Y :=
  fun x => match eq_dec x a with
    | left _ => None
    | right _ => f x
    end.

Inductive Qualifier : Set :=
  | mut : Qualifier
  | immut : Qualifier.

Record Reference : Set := {
  root : Location;
  access_path : Path;
  mutability : Qualifier;
}.

Definition Memory : Set := Location ⇀ Value.

Inductive LocalValues : Set :=
  | location : Location → LocalValues
  | reference : Reference → LocalValues.

Coercion location : Location >-> LocalValues.
Coercion reference : Reference >-> LocalValues.

Definition LocalMemory : Set := LocalVariable ⇀ LocalValues.

Inductive RuntimeValue : Set :=
  | tagged_val : Value → RuntimeValue
  | ref_val : Reference → RuntimeValue.

Coercion tagged_val : Value >-> RuntimeValue.
Coercion ref_val : Reference >-> RuntimeValue.

Definition LocalStack : Set := list RuntimeValue.

Record ModuleID : Set := {
  account_addr : AccountAddress;
  module_name : ModuleName;
}.

Record StructID : Set := {
  mod_id : ModuleID;
  name : StructName;
}.

Record GlobalResourceID : Set := {
  addr : AccountAddress;
  struct_id : StructID;
}.

Definition GlobalStore : Set := GlobalResourceID ⇀ Location.

Record GlobalState : Set := {
  memory : Memory;
  global_store : GlobalStore;
  local_mem : LocalMemory;
  stack : LocalStack;
}.

(** Move Instructions *)
Inductive Instr : Set :=
  | MvLoc : LocalVariable → Instr
  | CpLoc : LocalVariable → Instr
.

(** Local State Rules *)
Inductive step_local : ∀
(M : Memory) (L : LocalMemory) (S : LocalStack) (i : Instr)
(M' : Memory) (L' : LocalMemory) (S' : LocalStack), Prop :=
  | step_mvloc : ∀ {x : LocalVariable} {c : Location} {v : Value}
    {M : Memory} {L : LocalMemory} {S : LocalStack},
    maps_to L x c →
    maps_to M c v →
    step_local M L S (MvLoc x) (remove M c) (remove L x) (tagged_val v :: S)
  | step_mvloc_ref : ∀ {x : LocalVariable} {r : Reference}
    {M : Memory} {L : LocalMemory} {S : LocalStack},
    maps_to L x r →
    step_local M L S (MvLoc x) M (remove L x) (ref_val r :: S)
  | step_cploc : ∀ {x : LocalVariable} {c : Location} {u : UnrestrictedValue}
    {M : Memory} {L : LocalMemory} {S : LocalStack},
    maps_to L x c →
    maps_to M c u →
    step_local M L S (CpLoc x) M L ((tagged_val (unrestrictiveValue u)) :: S)
  | step_cploc_ref : ∀ {x : LocalVariable} {r : Reference}
    {M : Memory} {L : LocalMemory} {S : LocalStack},
    maps_to L x r →
    step_local M L S (MvLoc x) M L (ref_val r :: S)
  | 
.