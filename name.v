Require Import Coq.Unicode.Utf8_core.
Require Import Resources.utility.

(** Names  *)
Parameter LocalVariable : Set.
Parameter var_dec_eq :  ∀ (x y : LocalVariable), {x = y} + {x <> y}.
Instance var_eq_dec : EqDec LocalVariable := {
  eq_dec := var_dec_eq
}.

Parameter FieldName : Set.
Parameter StructName : Set.
Parameter ModuleName : Set.
Parameter AccountAddress : Set.

Record ModuleID : Set := {
  account_addr : AccountAddress;
  module_name : ModuleName;
}.

Record StructID : Set := {
  mod_id : ModuleID;
  name : StructName;
}.

Definition GlobalResourceID := StructID.