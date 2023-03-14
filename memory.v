Require Import Resources.utility.
Require Import Resources.name.
Require Import Resources.type.
Require Import Resources.value.
Require Import Coq.Program.Equality.

(** Memory model  *)
Definition LocalMemory : Set := LocalVariable ⇀ RuntimeValue.

Inductive local_mem_contains_r : LocalMemory → Resource → Set :=
  | local_mem_contains_r_c : ∀ {L : LocalMemory} {x : LocalVariable } {r1 r2 : Resource},
    maps_to L x r1 →
    resource_contains_r r1 r2 →
    local_mem_contains_r L r2
.

Inductive local_mem_contains_t : LocalMemory → Tag → Set :=
  | local_mem_contains_tc : ∀ (L : LocalMemory) (x : LocalVariable) (r : Resource),
    maps_to L x r → ∀ t,
    resource_contains_t r t →
    local_mem_contains_t L t
.

Lemma local_mem_contains_tc_inj : ∀ L x r t H p1 p2, local_mem_contains_tc L x r t H p1 = local_mem_contains_tc L x r t H p2 → p1 = p2.
Proof.
  intros.
  dependent destruction H0.
  reflexivity.
Qed.

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

Inductive global_mem_contains_r : GlobalMemory → Resource → Set :=
  | global_mem_contains_r_c : ∀ {G : GlobalMemory} {x : GlobalResourceID} {a} {r1 r2 : Resource},
    maps_to G x.(mod_id).(account_addr) a →
    maps_to a.(resources) x.(name) r1 →
    resource_contains_r r1 r2 →
    global_mem_contains_r G r2
.

Inductive global_mem_contains_t : GlobalMemory → Tag → Set :=
  | global_mem_contains_rt : ∀ {G : GlobalMemory} {x : GlobalResourceID} {a} {r} {t},
    maps_to G x.(mod_id).(account_addr) a →
    maps_to a.(resources) x.(name) r →
    resource_contains_t r t →
    global_mem_contains_t G t
.

Record Memory := {
  local: LocalMemory;
  global: GlobalMemory;
}.

Inductive mem_contains_r : Memory → Resource → Set :=
  | local_mem_cr : ∀ {L} {G} {r}, local_mem_contains_r L r → mem_contains_r {|
    local := L; global := G;
  |} r
  | global_mem_cr : ∀ {L} {G} {r}, global_mem_contains_r G r → mem_contains_r {|
    local := L; global := G;
  |} r
.

Inductive mem_contains_t : Memory → Tag → Set :=
  | local_mem_ct : ∀ m t, local_mem_contains_t m.(local) t → mem_contains_t m t
  | global_mem_ct : ∀ m t, global_mem_contains_t m.(global) t → mem_contains_t m t
.

Definition mem_remove (M : Memory) (x : LocalVariable) : Memory.
Admitted.

Definition mem_update_local (M : Memory) (x : LocalVariable) (v : RuntimeValue) : Memory.
Admitted.

Lemma mem_update_local_global_const1 {M} {x} {v} :
∀ t, global_mem_contains_t M.(global) t → global_mem_contains_t (mem_update_local M x v).(global) t.
Admitted.

Lemma mem_update_local_global_const2 {M} {x} {v} :
∀ t, global_mem_contains_t (mem_update_local M x v).(global) t →
global_mem_contains_t M.(global) t.
Admitted.

Lemma mem_update_local_u1 {M} {x} {u : UnrestrictedValue} :
∀ t, local_mem_contains_t M.(local) t → local_mem_contains_t (mem_update_local M x u).(local) t.
Admitted.

Lemma mem_update_local_u2 {M} {x} {u : UnrestrictedValue} :
∀ t, local_mem_contains_t (mem_update_local M x u).(local) t → local_mem_contains_t M.(local) t.
Admitted.

Definition mem_update_ref (M : Memory) (r : Reference) (v : RuntimeValue) : Memory.
Admitted.

Definition maps_var_to (M : Memory) x v : Set := maps_to M.(local) x v.

Inductive maps_ref_to : Memory → Reference → RuntimeValue → Prop :=.

Inductive maps_struct_kind : Memory → StructType → Kind → Prop :=.

Inductive maps_struct_arity : Memory → StructType → nat → Prop :=.

Definition LocalStack : Set := list RuntimeValue.

Inductive lstack_contains_r : LocalStack → Resource → Set :=
  | lstack_car : ∀ (r1 r2 : Resource) S,
    resource_contains_r r1 r2 →
    lstack_contains_r (val r1 :: S) r2
  | lstack_cdr : ∀ v r S,
    lstack_contains_r S r →
    lstack_contains_r (v :: S) r
.

Inductive lstack_contains_t : LocalStack → Tag → Set :=
  | lstackt_car : ∀ S r t,
    resource_contains_t r t →
    lstack_contains_t (val r :: S) t
  | lstackt_cdr : ∀ S t,
    lstack_contains_t S t →
    ∀ v, lstack_contains_t (v :: S) t
.

Inductive fresh_tag : Memory → LocalStack → Tag → Set :=
  | fresh_tag_c : ∀ M S t,
    (∀t', mem_contains_t M t' → t ≠ t') →
    (∀t', lstack_contains_t S t' → t ≠ t') →
    fresh_tag M S t.