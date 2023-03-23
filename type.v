Require Import Resources.name.
(** Types *)
Inductive Kind : Set := resourceKind | unrestrictedKind.

Module StructType.
Record StructType : Set := {
  struct_id : StructID;
}.
End StructType.
Export StructType(StructType).

Inductive PrimitiveType : Set :=
  | accountAddressType : PrimitiveType
  | signerType : PrimitiveType
  | boolType : PrimitiveType
  | unsignedInt64Type : PrimitiveType
  | bytesType : PrimitiveType.

Inductive NonReferenceType : Set :=
  | structNonReferenceType : StructType -> NonReferenceType
  | primitiveNonReferenceType : PrimitiveType -> NonReferenceType.

Definition MoveType : Set := NonReferenceType.