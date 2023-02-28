Require Import Resources.utility.
Require Import Resources.name.
Require Import Resources.type.
Require Import Resources.value.


(** Memory model  *)
Definition LocalMemory : Set := LocalVariable ⇀ RuntimeValue.

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
  resources : StructID ⇀ Resource;
  modules : ModuleName ⇀ Module
}.

Definition GlobalMemory : Set := AccountAddress ⇀ Account.

Record Memory := {
  local: LocalMemory;
  global: GlobalMemory;
}.

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

Inductive fresh_tag (M : Memory) (S : LocalStack) : Tag → Prop :=.