Require Import Resources.utility.
Require Import Resources.name.
Require Import Resources.type.
Require Import Resources.value.
Require Import Coq.Program.Equality.

(** Memory model  *)
Definition LocalMemory : Set := LocalVariable ⇀ RuntimeValue.

Inductive local_mem_contains_t : LocalMemory → Tag → Set :=
  | local_mem_contains_tc : ∀ {L : LocalMemory} {x : LocalVariable} {r : Resource},
    maps_to L x r → ∀ {t},
    resource_contains_t r t →
    local_mem_contains_t L t
.

Definition local_mem_remove (L : LocalMemory) x := remove L x.

Definition GlobalMemory : Set := GlobalResourceID ⇀ Resource.

Inductive global_mem_contains_t : GlobalMemory → Tag → Set :=
  | global_mem_contains_rt : ∀ {G : GlobalMemory} {x : GlobalResourceID} {r},
    maps_to G x r → ∀ {t},
    resource_contains_t r t →
    global_mem_contains_t G t
.

Module StructSig.
Record StructSig := {
  kind : Kind;
  field: list (FieldName * NonReferenceType)
}.
End StructSig.
Import StructSig(StructSig).

Record ModuleDefinition : Set := {
  struct_decls : StructName ⇀ StructSig;
}.

Definition ModuleDefinitions := (AccountAddress * ModuleName) ⇀ ModuleDefinition.

Record Memory := {
  local: LocalMemory;
  global: GlobalMemory;
}.

Inductive mem_contains_t : Memory → Tag → Set :=
  | local_mem_ct : ∀ {m} {t}, local_mem_contains_t m.(local) t → mem_contains_t m t
  | global_mem_ct : ∀ {m} {t}, global_mem_contains_t m.(global) t → mem_contains_t m t
.

Definition mem_remove (M : Memory) (x : LocalVariable) : Memory.
Proof.
  destruct M as [local global].
  constructor.
  + refine (remove local x).
  + refine global.
Defined.

Definition maps_var_to (M : Memory) x v : Set := maps_to M.(local) x v.

Lemma remove_p1 : ∀ {Y : Set} (M : LocalVariable ⇀ Y) x v, notT (maps_to (remove M x) x v).
Proof.
  intros Y M x v Hc.
  unfold remove in Hc.
  unfold maps_to in Hc.
  simpl in Hc.
  destruct (var_dec_eq x x).
  + inversion Hc.
  + apply n. reflexivity.
Qed.

Lemma mem_remove_p1 : ∀ M x v, notT (maps_var_to (mem_remove M x) x v).
Proof.
  intros M x v Hc.
  destruct M as [local global].
  inversion Hc.
  unfold remove in H0.
  simpl in H0.
  destruct (var_dec_eq x x).
  + inversion H0.
  + apply n. reflexivity.
Qed.

Lemma remove_p2 : ∀ {Y : Set} (M : LocalVariable ⇀ Y) x y v, ¬ x = y →  (maps_to (remove M x) y v) = (maps_to M y v).
Proof.
  intros Y M x y v H.
  unfold remove.
  unfold maps_to.
  destruct (eq_dec y x); auto.
  rewrite e in H.
  contradiction.
Qed.

Lemma mem_remove_p2 : ∀ M x y v, ¬ x = y →  (maps_var_to (mem_remove M x) y v) = (maps_var_to M y v).
Proof.
  intros M x y v H.
  destruct M as [local global].
  unfold mem_remove.
  unfold maps_var_to.
  simpl.
  unfold maps_to.
  unfold remove.
  destruct (eq_dec y x); auto.
  rewrite e in H.
  contradiction.
Qed.

Lemma remove_p3 : ∀ {Y : Set}  (M : LocalVariable ⇀ Y) x y v, (maps_to (remove M x) y v) → maps_to M y v.
Proof.
  intros Y M x y v H.
  erewrite <- remove_p2.
  + exact H.
  + intro Hc.
    rewrite Hc in H.
    eapply remove_p1.
    exact H.
Qed.

Lemma mem_remove_p3 : ∀ M x y v, (maps_var_to (mem_remove M x) y v) → maps_var_to M y v.
Proof.
  intros M x y v H.
  erewrite <- mem_remove_p2.
  + exact H.
  + intro Hc.
    rewrite Hc in H.
    eapply mem_remove_p1.
    exact H.
Qed.

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

Inductive maps_struct_kind : ModuleDefinitions → StructType → Kind → Prop :=.

Inductive maps_struct_arity : ModuleDefinitions → StructType → nat → Prop :=.

Definition LocalStack : Set := list RuntimeValue.

Inductive lstack_contains_t : LocalStack → Tag → Set :=
  | lstackt_car : ∀ S r t,
    resource_contains_t r t →
    lstack_contains_t (resourceValue r :: S) t
  | lstackt_cdr : ∀ S t,
    lstack_contains_t S t →
    ∀ v, lstack_contains_t (v :: S) t
.

Inductive fresh_tag : Memory → LocalStack → Tag → Set :=
  | fresh_tag_c : ∀ M S t,
    (∀t', mem_contains_t M t' → t ≠ t') →
    (∀t', lstack_contains_t S t' → t ≠ t') →
    fresh_tag M S t.