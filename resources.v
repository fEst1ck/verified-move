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
  kind : Kind;
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

Definition GlobalMemory : Set := GlobalResourceID ⇀ Value.

Inductive LocalMemTo : LocalMemory → Reference → RuntimeValue → Prop :=.

Inductive mem_to : GlobalMemory → LocalMemory → Reference → RuntimeValue → Prop :=.

Definition write_mem (G : GlobalMemory) (L : LocalMemory) (ref : Reference) (u : UnrestrictedValue) : GlobalMemory * LocalMemory.
Admitted.

Definition LocalStack : Set := list RuntimeValue.

Record GlobalState : Set := {
  global_mem : GlobalMemory;
  local_mem : LocalMemory;
  stack : LocalStack;
}.

(** Move Instructions *)
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
.

(** Local State Rules *)
Inductive step_local : ∀
(G : GlobalMemory) (L : LocalMemory) (S : LocalStack) (i : Instr)
(G : GlobalMemory) (L' : LocalMemory) (S' : LocalStack), Prop :=
  | step_mvloc : ∀ {x : LocalVariable} {v : RuntimeValue}
    {G : GlobalMemory} {L : LocalMemory} {S : LocalStack},
    maps_to L x v →
    step_local G L S (MvLoc x) G (remove L x) (v :: S)
  | step_cploc : ∀ {x : LocalVariable} {u : UnrestrictedValue}
    {G : GlobalMemory} {L : LocalMemory} {S : LocalStack},
    maps_to L x u →
    step_local G L S (CpLoc x) G L (val (unrestrictiveValue u) :: S)
  | step_stloc_val : ∀ {x : LocalVariable} {u : UnrestrictedValue}
    {G : GlobalMemory} {L : LocalMemory} {S : LocalStack},
    maps_to L x u →
    step_local G L (val (unrestrictiveValue u) :: S) (StLoc x) G (update L x u) S
  | step_stloc_ref : ∀ {x : LocalVariable} {r : Reference}
    {G : GlobalMemory} {L : LocalMemory} {S : LocalStack},
    maps_to L x r →
    step_local G L (ref_val r :: S) (StLoc x) G (update L x r) S
  | step_borrow_loc : ∀ {x : LocalVariable} {v : RuntimeValue}
    {G : GlobalMemory} {L : LocalMemory} {S : LocalStack},
    maps_to L x v →
    step_local G L S (BorrowLoc x) G L (ref_val {|
      root := x;
      access_path := nil;
      mutability := mut
    |} :: S)
  | step_borrow_field : ∀ {x : LocalVariable} {f : FieldName} {r : Reference}
    {G : GlobalMemory} {L : LocalMemory} {S : LocalStack},
    step_local G L (ref_val r :: S) (BorrowField f) G L (ref_val (extend_ref r f) :: S) (* todo *)
  | step_freeze_ref : ∀ {r : Reference}
    {G : GlobalMemory} {L : LocalMemory} {S : LocalStack},
    step_local G L (ref_val r :: S) FreezeRef G L ((ref_val (freeze_ref r)) :: S) 
  | step_read_ref : ∀ {r : Reference} {u : UnrestrictedValue}
    {G : GlobalMemory} {L : LocalMemory} {S : LocalStack},
    mem_to G L r u →
    step_local G L (ref_val r :: S) ReadRef G L (val (unrestrictiveValue u) :: S)
  | step_write_ref : ∀ {root} {path} {u : UnrestrictedValue}
    {G : GlobalMemory} {L : LocalMemory} {S : LocalStack} {G' : GlobalMemory} {L' : LocalMemory},
    write_mem G L {|
      root := root; access_path := path; mutability := mut
    |} u = (G', L') →
    step_local G L (val (unrestrictiveValue u) :: ref_val {|
       root := root; access_path := path; mutability := mut
    |} :: S) WriteRef G' L' S
  | step_pop_u : ∀ {u : UnrestrictedValue}
    {G : GlobalMemory} {L : LocalMemory} {S : LocalStack},
    step_local G L (val (unrestrictiveValue u) :: S) Pop G L S
  | step_pop_ref : ∀ {r : Reference}
    {G : GlobalMemory} {L : LocalMemory} {S : LocalStack},
    step_local G L (ref_val r :: S) Pop G L S
  .