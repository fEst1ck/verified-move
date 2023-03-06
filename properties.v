
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
  destruct Hs as [i Hs].
  unfold stack_tag_u in *.
  inversion Hs.
  + destruct v.
    ++ destruct v.
      {
        intros.
        dependent destruction p1; dependent destruction p2.
        + enough (r1 = r2) as He.
          rewrite He.
          reflexivity.
          unfold mem_tag_u in Hm.
          destruct s0.
          simpl in *.
          destruct mem.
          unfold maps_var_to in H4.
          simpl in *.
          subst.
          remember local as L. remember global as G.
          remember (local_mem_ct L G t (local_mem_contains_tc L x r H4 t r1)) as p1.
          remember (local_mem_ct L G t (local_mem_contains_tc L x r H4 t r2)) as p2.
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
  destruct Hs as [i Hs].
  inversion Hs; subst.
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
  destruct Hs as [i Hs].
  inversion Hs; subst.
  + admit.
  + unfold stack_mem_disjoint_tag in *.
    destruct H3 as [H3 H4].
    split.
    ++ intros.
      apply H3 in H0.
      intro contra.
      apply stack_contains_t_cons_u in contra.
      contradiction.
    ++ intros.
      apply stack_contains_t_cons_u in H0.
      auto.
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

Definition resource_conservation {s0} {s1} (_ : step s0 s1) : Type :=
  (∀ t, state_contains_t s0 t → state_contains_t s1 t) *
  (∀ t, state_contains_t s1 t → state_contains_t s0 t).

Definition introduce_t {s0} {s1} (_ : step s0 s1) t : Type :=
  (∀ t, state_contains_t s0 t → state_contains_t s1 t) *
  notT (state_contains_t s0 t) *
  state_contains_t s1 t *
  (∀ t', state_contains_t s1 t' * notT (state_contains_t s0 t') → t' = t).

Definition elim_t {s0} {s1} (_ : step s0 s1) t : Type :=
  (∀ t, state_contains_t s1 t → state_contains_t s0 t) *
  notT (state_contains_t s1 t) *
  state_contains_t s0 t *
  (∀ t', state_contains_t s0 t' * notT (state_contains_t s1 t') → t' = t).

Lemma resource_conservation_not_intro : ∀ {s0 s1} (Hs : step s0 s1),
  resource_conservation Hs → ∀ t, notT (introduce_t Hs t).
Proof.
  intros s0 s1 Hs Hc t contra.
  destruct Hc as [Hc1 Hc2].
  destruct contra as [[[c1 c2] c3] c4].
  apply Hc2 in c3.
  apply c2 in c3.
  contradiction.
Qed.

Lemma resource_conservation_not_elim : ∀ {s0 s1} (Hs : step s0 s1),
  resource_conservation Hs → ∀ t, notT (elim_t Hs t).
Proof.
  intros s0 s1 Hs Hc t contra.
  destruct Hc as [Hc1 Hc2].
  destruct contra as [[[c1 c2] c3] c4].
  apply Hc1 in c3.
  apply c2 in c3.
  contradiction.
Qed.

Lemma introduce_t_not_conserved : ∀ {s0 s1} (Hs : step s0 s1) {t},
introduce_t Hs t → notT (resource_conservation Hs).
Proof.
  intros s0 s1 Hs t Hi Hc.
  destruct Hi as [[[Hi1 Hi2] Hi3] Hi4].
  destruct Hc as [Hc1 Hc2].
  apply Hc2 in Hi3.
  apply Hi2 in Hi3.
  contradiction.
Qed.

Lemma introduce_t_not_elim_t : ∀ {s0 s1} (Hs : step s0 s1) {t},
introduce_t Hs t → ∀ t, notT (elim_t Hs t).
Proof.
  intros s0 s1 Hs t1 Hi t2 He.
  destruct Hi as [[[Hi1 Hi2] Hi3] Hi4].
  destruct He as [[[He1 He2] He3] He4].
  apply Hi1 in He3.
  contradiction.
Qed.

Lemma elim_t_not_conserved : ∀ {s0 s1} (Hs : step s0 s1) {t},
elim_t Hs t → notT (resource_conservation Hs).
Proof.
  intros s0 s1 Hs t He Hc.
  destruct He as [[[He1 He2] He3] He4].
  destruct Hc as [Hc1 Hc2].
  apply Hc1 in He3.
  contradiction.
Qed.

Lemma elim_t_not_elim_t : ∀ {s0 s1} (Hs : step s0 s1) {t},
elim_t Hs t → ∀ t, notT (introduce_t Hs t).
Proof.
  intros s0 s1 Hs t1 He t2 Hi.
  destruct Hi as [[[Hi1 Hi2] Hi3] Hi4].
  destruct He as [[[He1 He2] He3] He4].
  apply He1 in Hi3.
  contradiction.
Qed.

Theorem local_resource_safety : ∀ {s0 s1} (Hs : step s0 s1),
resource_conservation Hs +
{ t & introduce_t Hs t} +
{ t & elim_t Hs t}.
Proof.
Admitted.

Open Scope type_scope.
Theorem only_pack_intro_r : ∀ {s0 s1} (Hs : step s0 s1) {t}
(Hi : introduce_t Hs t),
{ τ & instr_of_step Hs = (Pack τ) } +
{r & { S & (val (resourceValue r) :: S = s1.(stack)) * (tag_of r = t) }}.
Proof.
Admitted.

Theorem only_unpack_elim_t : ∀ {s0 s1} (Hs : step s0 s1) {t}
(Hi : elim_t Hs t),
(instr_of_step Hs = Unpack) +
{ r & { S & (val (resourceValue r) :: S = s0.(stack)) * (tag_of r = t) }}.
Proof.
Admitted.