
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
  (∀ t, mem_contains_t m t → notT (lstack_contains_t s t)) ∧
  (∀ t, lstack_contains_t s t → notT (mem_contains_t m t)).

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

Proposition step_preserve_mem_tag_u :
∀ (s0 s1 : state),
tag_uniq s0 →
step s0 s1 →
mem_tag_u s1.(mem).
Proof.
  intros s0 s1 [H1 [H2 H3]] Hs.
  destruct Hs.
  inversion H; subst.
  + admit.
  + unfold mem_tag_u in *.
    destruct H3.
    assumption.
Admitted.


Proposition step_preserve_stack_mem_disjoint :
∀ (s0 s1 : state),
tag_uniq s0 →
step s0 s1 →
stack_mem_disjoint_tag s1.(mem) s1.(stack).
Proof.
  intros s0 s1 [H1 [H2 H3]] Hs.
  destruct Hs.
  inversion H; subst.
  + admit.
  + unfold stack_mem_disjoint_tag in *.
    destruct H3 as [H3 H4].
    split.
    ++ intros.
      apply H3 in H5.
      unfold notT.
      intros.
      apply stack_contains_t_cons_u in H6.
      apply H5 in H6.
      destruct H6.
    ++ intros.
      apply stack_contains_t_cons_u in H5.
      apply H4 in H5.
      assumption.
Admitted.

Proposition step_preserve_tag_u :
∀ (s0 s1 : state),
tag_uniq s0 →
step s0 s1 →
tag_uniq s1.
Proof.
  intros.
  split.
  + apply step_preserve_mem_tag_u with (s0:=s0); assumption.
  + split.
    ++ apply step_preserve_stack_tag_u with (s0:=s0); assumption.
    ++ apply step_preserve_stack_mem_disjoint with (s0:=s0); assumption.
Qed.

Definition resource_conservation s0 s1 : Type :=
  step s0 s1 *
  (∀ t, state_contains_t s0 t → state_contains_t s1 t) *
  (∀ t, state_contains_t s1 t → state_contains_t s0 t).

Definition introduce_r s0 s1 t : Type :=
  step s0 s1 *
  (∀ t, state_contains_t s0 t → state_contains_t s1 t) *
  notT (state_contains_t s0 t) *
  state_contains_t s1 t *
  (∀ t', state_contains_t s1 t' * notT (state_contains_t s0 t') → t' = t).

Definition elim_r s0 s1 t : Type := introduce_r s1 s0 t.

Lemma resource_conservation_not_intro : ∀ {s0 s1},
  resource_conservation s0 s1 → ∀ t, notT (introduce_r s0 s1 t).
Proof.
  intros s0 s1 Hc t contra.
  destruct Hc as [[Hstep Hc1] Hc2].
  destruct contra as [[[[_ c0] c1] c2] c3].
  apply Hc2 in c2.
  apply c1 in c2.
  contradiction.
Qed.

Lemma resource_conservation_not_elim : ∀ {s0 s1},
  resource_conservation s0 s1 → ∀ t, notT (elim_r s0 s1 t).
Proof.
  intros s0 s1 Hc t contra.
  destruct Hc as [[Hstep Hc1] Hc2].
  destruct contra as [[[[_ c0] c1] c2] c3].
  apply Hc1 in c2.
  apply c1 in c2.
  contradiction.
Qed.

Lemma introduce_r_not_conserved : ∀ {s0 s1 t},
introduce_r s0 s1 t → notT (resource_conservation s0 s1).
Proof.
  intros s0 s1 t Hi Hc.
  destruct Hi as [[[[Hi1 Hi2] Hi3] Hi4] Hi5].
  destruct Hc as [[Hc1 Hc2] Hc3].
  apply Hc3 in Hi4.
  apply Hi3 in Hi4.
  contradiction.
Qed.

Lemma introduce_r_not_elim_r : ∀ {s0 s1 t},
introduce_r s0 s1 t → ∀ t, notT (elim_r s0 s1 t).
Proof.
  intros s0 s1 t1 Hi t2 Hc.
  destruct Hi as [[[[Hi1 Hi2] Hi3] Hi4] Hi5].
  destruct Hc as [[[[Hc Hc0] Hc1] Hc2] Hc3].
  apply Hc0 in Hi4.
  contradiction.
Qed.

Lemma elim_r_not_conserved : ∀ {s0 s1 t},
elim_r s0 s1 t → notT (resource_conservation s0 s1).
Proof.
  intros s0 s1 t Hi Hc.
  destruct Hi as [[[[Hi1 Hi2] Hi3] Hi4] Hi5].
  destruct Hc as [[Hc1 Hc2] Hc3].
  apply Hc2 in Hi4.
  contradiction.
Qed.

Lemma elim_r_not_elim_r : ∀ {s0 s1 t},
elim_r s0 s1 t → ∀ t, notT (introduce_r s0 s1 t).
Proof.
  intros s0 s1 t1 Hi t2 Hc.
  destruct Hi as [[[[Hi1 Hi2] Hi3] Hi4] Hi5].
  destruct Hc as [[[[Hc Hc0] Hc1] Hc2] Hc3].
  apply Hc0 in Hi4.
  contradiction.
Qed.