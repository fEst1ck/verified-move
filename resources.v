Require Import Coq.Unicode.Utf8_core.
Open Scope list_scope.

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

Fixpoint map {A B} (f : A -> B) (l:list A) : list B :=
  match l with
    | nil => nil
    | a :: t => (f a) :: (map f t)
  end.

(** Names  *)
Variable LocalVariable : Set.
Variable var_dec_eq :  ∀ (x y : LocalVariable), {x = y} + {x <> y}.
Instance var_eq_dec : EqDec LocalVariable := {
  eq_dec := var_dec_eq
}.

Variable FieldName : Set.
Variable StructName : Set.
Variable ModuleName : Set.
Variable AccountAddress : Set.

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

(** Types *)
Inductive Kind : Set := resourceKind | unrestrictedKind.

Module StructType.
Record StructType : Set := {
  struct_id : StructID;
}.
End StructType.
Import StructType(StructType).

Inductive PrimitiveType : Set :=
  | accountAddressType : PrimitiveType
  | signerType : PrimitiveType
  | boolType : PrimitiveType
  | unsignedInt64Type : PrimitiveType
  | bytesType : PrimitiveType.

Inductive NonReferenceType : Set :=
  | structNonReferenceType : StructType -> NonReferenceType
  | primitiveNonReferenceType : PrimitiveType -> NonReferenceType.

Inductive MoveType : Set :=
  | nonReferenceMoveType : NonReferenceType -> MoveType
  | mutRefMoveType : NonReferenceType -> MoveType
  | refMoveType : NonReferenceType -> MoveType.

(** Values *)
Variable Signer : Set.
Variable UnsignedInt64 : Set.
Variable Bytes : Set.

Inductive Resource : Set :=
  | resource : (FieldName ⇀ Value) -> Resource

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

Coercion structValue : Struct >-> UnrestrictedValue.
Coercion resourceValue : Resource >-> Value.
Coercion unrestrictiveValue : UnrestrictedValue >-> Value.
Coercion primitiveValue : PrimitiveValue >-> UnrestrictedValue.
Coercion boolValue : bool >-> PrimitiveValue.
Coercion unsignedInt64Value : UnsignedInt64 >-> PrimitiveValue.
Coercion accountAddressValue : AccountAddress >-> PrimitiveValue.
Coercion bytesValue : Bytes >-> PrimitiveValue.

Inductive Qualifier : Set :=
  | mut : Qualifier
  | immut : Qualifier.

Inductive Root : Set :=
  | local_root : LocalVariable -> Root
  | global_root : GlobalResourceID -> Root.

Coercion local_root : LocalVariable >-> Root.
Coercion global_root : GlobalResourceID >-> Root.

Definition Path := list FieldName.

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
    access_path := access_path ++ (cons e nil);
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

(** * States  *)
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

(** Move Instructions *)
Inductive OpCode : Set.

Inductive op_arity : OpCode → nat → Prop :=.

Inductive legal : OpCode → list UnrestrictedValue → Prop :=.

Definition opcode_to_op (op : OpCode) (args : list UnrestrictedValue) : UnrestrictedValue. Admitted.

Inductive Instr : Set :=
  | MvLoc : LocalVariable → Instr
  | CpLoc : LocalVariable → Instr
  | StLoc : LocalVariable → Instr
  | BorrowLoc : LocalVariable → Instr
  | BorrowField : FieldName → Instr
  | FreezeRef : Instr
  | ReadRef : Instr
  | WriteRef : Instr
  | Pop : Instr
  | Pack : StructType → Instr
  | Unpack : Instr
  | LoadTrue : Instr
  | LoadFalse : Instr
  | LoadU64 : UnsignedInt64 → Instr
  | LoadAddress : AccountAddress → Instr
  | LoadBytes : Bytes → Instr
  | Op : OpCode → Instr
.

Coercion Op : OpCode >-> Instr.

(** Local State Rules *)
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
      access_path := nil;
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
  | step_pack_r : ∀ {τ : StructType} {n : nat} {lov : list Value}
    {M : Memory} {S : LocalStack},
    maps_struct_kind M τ resourceKind →
    maps_struct_arity M τ n →
    length lov = n →
    step_local M ((map val lov) ++ S) (Pack τ) M (val (struct τ lov) :: S)
  | step_pack_u : ∀ {τ : StructType} {n : nat} {lou : list UnrestrictedValue}
    {M : Memory} {S : LocalStack},
    maps_struct_kind M τ unrestrictedKind →
    maps_struct_arity M τ n →
    length lou = n →
    step_local M ((map (fun x => (val (unrestrictiveValue x)))) lou) (Pack τ) M ((val (struct τ (map unrestrictiveValue lou))) :: S)
  | step_unpack : ∀ {τ : StructType} {lov : list Value}
    {M : Memory} {S : LocalStack},
    step_local M (val (struct τ lov) :: S) Unpack M (map val lov ++ S)
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