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

Definition GlobalResourceID := StructID.

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

Variable Tag : Set.

Variable tag_dec_eq :  ∀ (x y : Tag), {x = y} + {x <> y}.
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

Inductive fresh_tag (M : Memory) (S : LocalStack) : Tag → Prop :=.

(** Move Instructions *)
Inductive OpCode : Set.

Parameter op_arity : OpCode → nat → Prop.

Parameter legal : OpCode → list UnrestrictedValue → Prop.

Parameter opcode_to_op: OpCode → list UnrestrictedValue → UnrestrictedValue.

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

(** Execution sequence  *)
Record state := {
  mem : Memory;
  stack : LocalStack;
}.

Record StackRef := {
  stack_root : nat;
  stack_path : Path;
}.

Parameter stack_maps_to : LocalStack → StackRef → Value → Prop.

Axiom stack_maps_to_car : ∀ (s : LocalStack) (a : Value)
  (root : nat) (p : Path) (v : Value),
  read_val a p v →
  stack_maps_to (val a :: s) {|
    stack_root := 0; stack_path := p;
  |} v.

Axiom stack_maps_to_car1 : ∀ (s : LocalStack) (p : Path) (v : Value),
stack_maps_to s {|
  stack_root := 0; stack_path := p;
|} v →
∃ (a : Value) (s' : LocalStack), (val a :: s') = s ∧ read_val a p v.

Axiom stack_maps_to_cdr : ∀ (s : LocalStack)
  (root : nat) (p : Path) (v : Value),
  stack_maps_to s {|
    stack_root := S root;
    stack_path := p;
  |} v →
  ∃ a s', s = a :: s' ∧ stack_maps_to s' {|
    stack_root := root; stack_path := p;
  |} v.

Lemma stack_maps_empty : ∀ (r : StackRef) (v : Value), ¬ stack_maps_to nil r v.
Proof.
  intros.
  destruct r.
  destruct stack_root0; unfold not; intros.
  + apply stack_maps_to_car1 in H.
    destruct H. destruct H. destruct H.
    inversion H.
  + apply stack_maps_to_cdr in H.
    destruct H. destruct H. destruct H.
    inversion H.
Qed.

Axiom stack_maps_to_cons : ∀ (s : LocalStack) (a : Value)
(root : nat) (p : Path) (v : Value),
stack_maps_to s {|
  stack_root := root; stack_path := p;
|} v →
stack_maps_to (val a :: s) {|
  stack_root := S root;
  stack_path := p;
|} v.

Lemma stack_maps_to_u_cons :
∀ (u : UnrestrictedValue) (s : LocalStack) (root : nat) (p : Path) (c : Resource),
stack_maps_to (val u :: s) {|
  stack_root := root; stack_path := p;
|} c →
∃ n', S n' = root ∧ stack_maps_to s {|
  stack_root := n'; stack_path := p;
|} c.
Proof.
  intros.
  destruct root0.
  {
    apply stack_maps_to_car1 in H.
    destruct H. destruct H. destruct H.
    apply read_resource in H0.
    destruct H0.
    inversion H.
    rewrite H0 in H2.
    inversion H2.
  }
  {
    apply stack_maps_to_cdr in H.
    destruct H. destruct H. destruct H.
    exists root0.
    split.
    + reflexivity.
    + inversion H.
      assumption. 
  }
Qed.

Definition state_loc : Set := Reference + StackRef.

Parameter state_maps_to : state → state_loc → Value → Prop.

Axiom state_maps_unique : ∀ (s : state) (l : state_loc) (v1 v2 : Value),
  state_maps_to s l v1 →
  state_maps_to s l v2 →
  v1 = v2.

Axiom state_maps_to_mem_compat0 : ∀ (s : state) (r : Reference) (v : Value),
  maps_ref_to s.(mem) r v -> state_maps_to s (inl r) v.

Axiom state_maps_to_mem_compat1 : ∀ (s : state) (r : Reference) (v : Value),
  state_maps_to s (inl r) v -> maps_ref_to s.(mem) r v.

Axiom state_maps_to_stack_compat0 : ∀ (s : state) (r : StackRef) (v : Value),
stack_maps_to s.(stack) r v -> state_maps_to s (inr r) v.

Axiom state_maps_to_stack_compat1 : ∀ (s : state) (r : StackRef) (v : Value),
state_maps_to s (inr r) v -> stack_maps_to s.(stack) r v.

Definition tag_consistent (s : state) : Prop :=
  ∀ (l1 l2 : state_loc) (c1 c2 : Resource),
    state_maps_to s l1 c1 →
    state_maps_to s l2 c2 →
    tag_of c1 = tag_of c2 →
    l1 = l2.

Inductive step : state → state → Prop :=
  | step_c : ∀ {s0 s1 : state} {i : Instr},
    step_local s0.(mem) s0.(stack) i s1.(mem) s1.(stack) →
    step s0 s1.

Theorem step_preserve_tag_consistent :
∀ (s0 s1 : state),
  tag_consistent s0 →
  step s0 s1 →
  tag_consistent s1.
Proof.
  intros s0 s1 Hc Hs.
  destruct s0. destruct s1.
  destruct Hs.
  inversion H.
  + admit.
  (* cploc *)
  + unfold tag_consistent. intros.
    destruct l1; destruct l2.
      ++ assert (state_maps_to s0 (inl r) c1). {
        apply state_maps_to_mem_compat1 in H6.
        apply state_maps_to_mem_compat0.
        rewrite H0.
        assumption.
      } assert (state_maps_to s0 (inl r0) c2). {
        apply state_maps_to_mem_compat1 in H7.
        apply state_maps_to_mem_compat0.
        rewrite H0.
        assumption.
      }
      unfold tag_consistent in Hc.
      apply Hc with (l1:=inl r) (l2:=inl r0) (c1:=c1) (c2:=c2); assumption.
      ++ unfold tag_consistent in Hc.
        apply state_maps_to_mem_compat1 in H6.
        rewrite <- H0 in H6.
        apply state_maps_to_mem_compat0 in H6.
        apply state_maps_to_stack_compat1 in H7.
        rewrite <- H4 in H7.
        destruct s.
        destruct stack_root0.
        {
          apply stack_maps_to_car1 in H7.
          destruct H7. destruct H7. destruct H7.
          inversion H7.
          contradiction.
        }
        {
          apply stack_maps_to_cdr in H7.
          destruct H7. destruct H7. destruct H7.
          inversion H7.
          rewrite <- H12 in H9.
          apply state_maps_to_stack_compat0 in H9.
          specialize Hc with (l1 := inl r) (l2 := inr {| stack_root := stack_root0; stack_path := stack_path0 |}) (c1:=c1) (c2:=c2).
          apply Hc in H6; auto.
          inversion H6.
        }
      ++ unfold tag_consistent in Hc.
        apply state_maps_to_mem_compat1 in H7.
        rewrite <- H0 in H7.
        apply state_maps_to_mem_compat0 in H7.
        apply state_maps_to_stack_compat1 in H6.
        rewrite <- H4 in H6.
        destruct s.
        destruct stack_root0.
        {
          apply stack_maps_to_car1 in H6.
          destruct H6. destruct H6. destruct H6.
          inversion H6.
          contradiction.
        }
        {
          apply stack_maps_to_cdr in H6.
          destruct H6. destruct H6. destruct H6.
          inversion H6.
          rewrite <- H12 in H9.
          apply state_maps_to_stack_compat0 in H9.
          specialize Hc with (l2 := inl r) (l1 := inr {| stack_root := stack_root0; stack_path := stack_path0 |}) (c1:=c1) (c2:=c2).
          apply Hc in H7; auto.
          inversion H7.
        }
      ++ unfold tag_consistent in Hc.
        apply state_maps_to_stack_compat1 in H6.
        apply state_maps_to_stack_compat1 in H7.
        rewrite <- H4 in H6, H7.
        destruct s.
        apply stack_maps_to_u_cons in H6.
        destruct H6. destruct H6.
        apply state_maps_to_stack_compat0 in H9.
        destruct s2.
        apply stack_maps_to_u_cons in H7.
        destruct H7. destruct H7.
        apply state_maps_to_stack_compat0 in H10.
        specialize Hc with (l1 := (inr {| stack_root := x0; stack_path := stack_path0 |})) (l2 := (inr {| stack_root := x1; stack_path := stack_path1 |}))
        (c1 := c1) (c2 := c2).
        apply Hc in H9; auto.
        rewrite <- H6.
        rewrite <- H7.
        inversion H9.
        reflexivity.
Admitted.

Inductive steps_local : state → state → Prop :=
  | refl : ∀ {s : state}, steps_local s s
  | trans : ∀ {s0 s1 s2 : state} {i : Instr},
    step s0 s1 →
    steps_local s1 s2 →
    steps_local s0 s2.