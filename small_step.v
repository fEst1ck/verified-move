Require Import Coq.Lists.List.
Open Scope list_scope.
Import ListNotations.
Require Import Resources.utility.
Require Import Resources.name.
Require Import Resources.type.
Require Import Resources.value.
Require Import Resources.memory.
Require Import Resources.instr.
(** Local State Rules *)

Record state := {
  mem : Memory;
  stack : LocalStack;
}.

Definition state_contains_t s t : Type := 
   mem_contains_t s.(mem) t + lstack_contains_t s.(stack) t.

Inductive step_local : ∀
(M : Memory) (S : LocalStack) (i : Instr)
(M' : Memory) (S' : LocalStack), Prop :=
  | step_mvloc : ∀ {x : LocalVariable} {v : RuntimeValue}
    {M : Memory} {S : LocalStack},
    maps_var_to M x v →
    step_local M S (MvLoc x) (mem_remove M x) (v :: S)
  | step_cploc : ∀ {x : LocalVariable} {u : UnrestrictedValue}
    {M : Memory} {S : LocalStack},
    maps_var_to M x u →
    step_local M S (CpLoc x) M (val u :: S)
  | step_stloc_u : ∀ {x : LocalVariable} {u : UnrestrictedValue}
    {M : Memory} {S : LocalStack},
    maps_var_to M x u →
    step_local M (val u :: S) (StLoc x) (mem_update_local M x u) S
  | step_stloc_ref : ∀ {x : LocalVariable} {r : Reference}
    {M : Memory} {S : LocalStack},
    maps_var_to M x r →
    step_local M (ref_val r :: S) (StLoc x) (mem_update_local M x r) S
  | step_borrow_loc : ∀ {x : LocalVariable} {v : Value}
    {M : Memory} {S : LocalStack},
    maps_var_to M x v →
    step_local M S (BorrowLoc x) M (ref_val {|
      root := x;
      access_path := [ ];
      mutability := mut
    |} :: S)
  | step_borrow_field : ∀ {x : LocalVariable} {f : FieldName} {r : Reference}
    {M : Memory} {S : LocalStack},
    step_local M (ref_val r :: S) (BorrowField f) M (ref_val (extend_ref r f) :: S)
  | step_freeze_ref : ∀ {r : Reference}
    {M : Memory} {S : LocalStack},
    step_local M (ref_val r :: S) FreezeRef M ((ref_val (freeze_ref r)) :: S)
  | step_read_ref : ∀ {r : Reference} {u : UnrestrictedValue}
    {M : Memory} {S : LocalStack},
    maps_ref_to M r u →
    step_local M (ref_val r :: S) ReadRef M (val u :: S)
  | step_write_ref : ∀ {r : Reference} {u : UnrestrictedValue}
    {M : Memory} {S : LocalStack},
    maps_ref_to M r u →
    step_local M (val u :: ref_val r :: S) WriteRef (mem_update_ref M r u) S
  | step_pop_u : ∀ {u : UnrestrictedValue}
    {M : Memory} {S : LocalStack},
    step_local M (val u :: S) Pop M S
  | step_pop_ref : ∀ {r : Reference}
    {M : Memory} {S : LocalStack},
    step_local M (ref_val r :: S) Pop M S
  | step_pack_r : ∀ {τ : StructType} {n : nat} {lov : list Value} {t : Tag}
    {M : Memory} {S : LocalStack},
    maps_struct_kind M τ resourceKind →
    maps_struct_arity M τ n →
    length lov = n →
    fresh_tag M S t →
    step_local M ((map val lov) ++ S) (Pack τ) M (val (resource t τ lov) :: S)
  | step_pack_u : ∀ {τ : StructType} {n : nat} {lou : list UnrestrictedValue}
    {M : Memory} {S : LocalStack},
    maps_struct_kind M τ unrestrictedKind →
    maps_struct_arity M τ n →
    length lou = n →
    step_local M ((map (fun x => (val (unrestrictiveValue x)))) lou) (Pack τ) M ((val (struct τ lou)) :: S)
  | step_unpack : ∀ {τ : StructType} {t} {lov : list Value}
    {M : Memory} {S : LocalStack},
    step_local M (val (resource t τ lov) :: S) Unpack M (map val lov ++ S)
  | step_load_true : ∀ {M : Memory} {S : LocalStack},
    step_local M S LoadTrue M (val true :: S)
  | step_load_false : ∀ {M : Memory} {S : LocalStack},
    step_local M S LoadFalse M (val false :: S)
  | step_load_u64 : ∀ {M : Memory} {S : LocalStack} {n : UnsignedInt64},
    step_local M S (LoadU64 n) M (val n :: S)
  | step_load_address : ∀ {M : Memory} {S : LocalStack} {a : AccountAddress},
    step_local M S (LoadAddress a) M (val a :: S)
  | step_load_bytes : ∀ {M : Memory} {S : LocalStack} {b : Bytes},
    step_local M S (LoadBytes b) M (val b :: S)
  | step_op : ∀ {op : OpCode} {n : nat} {lou : list UnrestrictedValue}
    {M : Memory} {S : LocalStack},
    op_arity op n →
    length lou = n →
    step_local M (map (fun x => (val (unrestrictiveValue x))) lou ++ S) op M (val (opcode_to_op op lou) :: S)
  .

Definition step_i s0 i s1 : Prop := step_local s0.(mem) s0.(stack) i s1.(mem) s1.(stack).

Definition step s0 s1 : Type := { i & step_i s0 i s1 }.

Definition instr_of_step {s0 s1} (Hs : step s0 s1) : Instr.
Proof.
  unfold step in Hs.
  destruct Hs as [i Hs].
  refine i.
Defined.
  
Inductive steps_local : state → state → Prop :=
  | refl : ∀ {s : state}, steps_local s s
  | trans : ∀ {s0 s1 s2 : state} {i : Instr},
    step s0 s1 →
    steps_local s1 s2 →
    steps_local s0 s2
.