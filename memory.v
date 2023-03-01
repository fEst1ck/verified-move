Require Import Resources.utility.
Require Import Resources.name.
Require Import Resources.type.
Require Import Resources.value.

(** Memory model  *)
Definition LocalMemory : Set := LocalVariable ⇀ RuntimeValue.

Inductive local_mem_contains_r : LocalMemory → Resource → Prop :=
  | local_mem_contains_r_c : ∀ {L : LocalMemory} {x : LocalVariable } {r1 r2 : Resource},
    maps_to L x r1 →
    resource_contains_r r1 r2 →
    local_mem_contains_r L r2
.

Module StructSig.
Record StructSig := {
  kind : Kind;
  field: list (FieldName * NonReferenceType)
}.
End StructSig.
Import StructSig(StructSig).

Record Module : Set := {
  struct_decls : StructName ⇀ StructSig;
}.

Record Account : Set := {
  resources : StructName ⇀ Resource;
  modules : ModuleName ⇀ Module
}.

Definition GlobalMemory : Set := AccountAddress ⇀ Account.

Inductive global_mem_contains_r : GlobalMemory → Resource → Prop :=
  | global_mem_contains_r_c : ∀ {G : GlobalMemory} {x : GlobalResourceID} {a} {r1 r2 : Resource},
    maps_to G x.(mod_id).(account_addr) a →
    maps_to a.(resources) x.(name) r1 →
    resource_contains_r r1 r2 →
    global_mem_contains_r G r2
.

Record Memory := {
  local: LocalMemory;
  global: GlobalMemory;
}.

Inductive mem_contains_r : Memory → Resource → Prop :=
  | local_mem_cr : ∀ L G r, local_mem_contains_r L r → mem_contains_r {|
    local := L; global := G;
  |} r
  | global_mem_cr : ∀ L G r, global_mem_contains_r G r → mem_contains_r {|
    local := L; global := G;
  |} r
.

Definition mem_remove (M : Memory) (x : LocalVariable) : Memory.
Admitted.

Definition mem_update_local (M : Memory) (x : LocalVariable) (v : RuntimeValue) : Memory.
Admitted.

Definition mem_update_ref (M : Memory) (r : Reference) (v : RuntimeValue) : Memory.
Admitted.

Inductive maps_var_to : Memory → LocalVariable → RuntimeValue → Prop :=.

Inductive maps_ref_to : Memory → Reference → RuntimeValue → Prop :=.

Inductive maps_struct_kind : Memory → StructType → Kind → Prop :=.

Inductive maps_struct_arity : Memory → StructType → nat → Prop :=.

Definition LocalStack : Set := list RuntimeValue.

Inductive lstack_contains_r : LocalStack → Resource → Prop :=
  | lstack_car : ∀ (r1 r2 : Resource) S,
    resource_contains_r r1 r2 →
    lstack_contains_r (val r1 :: S) r2
  | lstack_cdr : ∀ v r S,
    lstack_contains_r S r →
    lstack_contains_r (v :: S) r
.

Inductive fresh_tag : Memory → LocalStack → Tag → Prop :=
  | fresh_tag_c : ∀ M S t,
    (∀r, mem_contains_r M r → tag_of r ≠ t) →
    (∀r, lstack_contains_r S r → tag_of r ≠ t) →
    fresh_tag M S t.