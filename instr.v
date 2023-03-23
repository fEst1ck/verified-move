Require Import Resources.utility.
Require Import Resources.name.
Require Import Resources.type.
Require Import Resources.value.

(** Move Instructions *)
Inductive OpCode : Set.

Parameter op_arity : OpCode → nat → Prop.

Parameter legal : OpCode → list UnrestrictedValue → Prop.

Parameter opcode_to_op: OpCode → list UnrestrictedValue → UnrestrictedValue.

Inductive Instr : Set :=
  | MvLoc : LocalVariable → Instr
  | CpLoc : LocalVariable → Instr
  | StLoc : LocalVariable → Instr
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