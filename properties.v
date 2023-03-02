
Require Import Coq.Lists.List.
Open Scope list_scope.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Resources.utility.
Require Import Resources.name.
Require Import Resources.type.
Require Import Resources.value.
Require Import Resources.memory.
Require Import Resources.instr.
Require Import Resources.small_step.

Definition stack_tag_u (s : LocalStack) : Prop := ∀ t (p1 p2 : lstack_contains_t s t), p1 = p2.

Definition mem_tag_u (m : Memory) : Prop := ∀ t (p1 p2 : mem_contains_t m t), p1 = p2.

Definition notc (s : Set) : Prop := s → False.

Definition stack_mem_disjoint_tag m s : Prop :=
  (∀ t, mem_contains_t m t → notc (lstack_contains_t s t)) ∧
  (∀ t, lstack_contains_t s t → notc (mem_contains_t m t)).

Definition tag_uniq s : Set :=
  mem_tag_u s.(mem) ∧
  stack_tag_u s.(stack) ∧
  stack_mem_disjoint_tag s.(mem) s.(stack).

Lemma stack_contains_t_cons_u : ∀ (u : UnrestrictedValue) s t,
  lstack_contains_t (val u :: s) t →
  lstack_contains_t s t.
Proof.
  intros.
  inversion H.
  assumption.
Defined.

Proposition step_preserve_stack_tag_u :
∀ (s0 s1 : state),
tag_uniq s0 →
step s0 s1 →
stack_tag_u s1.(stack).
Proof.
  intros s0 s1 [Hm [Hu Hd]] Hs.
  destruct Hs as [s0 s1 i].
  unfold stack_tag_u in Hu.
  unfold stack_tag_u.
  inversion H.
  + destruct v.
    ++
      destruct v.
      {
        intros.
        dependent destruction p1; dependent destruction p2.
        + enough (r1 = r2).
          rewrite H6.
          reflexivity.
          unfold mem_tag_u in Hm.
          destruct s0.
          simpl in *.
          destruct mem.
          unfold maps_var_to in H5.
          simpl in *.
          subst.
          remember local as L. remember global as G.
          remember (local_mem_ct L G t (local_mem_contains_tc L x r H5 t r1)) as p1.
          remember (local_mem_ct L G t (local_mem_contains_tc L x r H5 t r2)) as p2.
          specialize Hm with t p1 p2.
          subst.
          dependent destruction Heqp2.
          reflexivity.
        + admit.
        + admit.
        + specialize Hu with t p1 p2.
          rewrite Hu.
          reflexivity.
      }
      {
        intros.
        dependent destruction p1.
        dependent destruction p2.
        specialize Hu with t p1 p2.
        rewrite Hu.
        reflexivity.
      }
    (* x -> ref *)
    ++ intros.
      dependent destruction p1.
      dependent destruction p2.
      specialize Hu with t p1 p2.
      rewrite Hu.
      reflexivity.
  + intros.
    dependent destruction p1.
    dependent destruction p2.
    specialize Hu with t p1 p2.
    rewrite Hu.
    reflexivity.
Admitted.