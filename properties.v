
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

(** Two versions of tag-consistent  *)
Definition tag_uniq s : Set :=
  mem_tag_u s.(mem) ∧
  stack_tag_u s.(stack) ∧
  stack_mem_disjoint_tag s.(mem) s.(stack).

Definition state_tag_u (s : state) : Prop := ∀ t (p1 p2: state_contains_t s t), p1 = p2.

Lemma mem_tag_u_p1 {M} : ∀ {x y} {r1 r2 : Resource} {t}, mem_tag_u M →
maps_var_to M x r1 →
resource_contains_t r1 t →
maps_var_to M y r2 →
resource_contains_t r2 t →
x = y /\ r1 = r2.
Proof.
  intros x y r1 r2 t Hm Hx Hr1 Hy Hr2.
  remember (local_mem_ct (local_mem_contains_tc Hx Hr1)) as p1 eqn:Hp1.
  remember (local_mem_ct (local_mem_contains_tc Hy Hr2)) as p2 eqn:Hp2.
  pose (Hm _ p1 p2).
  rewrite Hp1, Hp2 in e.
  dependent destruction e.
  easy.
Qed.

Definition inject {A B} (f : A -> B) := (∀ x y, f x = f y -> x = y).

Ltac prove_inj := let h := fresh "Heq" in let x := fresh "x" in let y := fresh "y" in
  intros x y h; dependent destruction h; auto.

Ltac inject f := let hn := fresh "f_inj" in
  enough (∀ x y, f x = f y → x = y) as f_inj; try (eapply f_inj) || prove_inj.

Ltac inject1 f h := 
  enough (∀ x y, f x = f y → x = y) as h; try (eapply h) || prove_inj.

(** Equivalence of two versions of tag-consistent  *)
Lemma mem_tag_u_implies_mem_disjoint1 : ∀ {m},
mem_tag_u m → (∀ {t},
global_mem_contains_t m.(global) t →
notT (local_mem_contains_t m.(local) t)).
Proof.
  intros m Hm t Ht Hc.
  remember (local_mem_ct Hc) as p1.
  remember (global_mem_ct Ht) as p2.
  pose (Hm _ p1 p2).
  subst.
  inversion e.
Qed.

Lemma mem_tag_u_implies_mem_disjoint2 : ∀ {m},
mem_tag_u m → (∀ {t},
local_mem_contains_t m.(local) t →
notT (global_mem_contains_t m.(global) t)).
Proof.
  intros m Hm t Hc Ht.
  remember (local_mem_ct Hc) as p1.
  remember (global_mem_ct Ht) as p2.
  pose (Hm _ p1 p2).
  subst.
  inversion e.
Qed.

Lemma state_tag_u_implies_mem_tag_u : ∀ s, state_tag_u s → mem_tag_u s.(mem).
Proof.
  intros s Hs t p1 p2.
  inject (@ inl (mem_contains_t s.(mem) t) (lstack_contains_t s.(stack) t)).
  apply Hs.
Qed.

Lemma state_tag_u_implies_stack_tag_u : ∀ s, state_tag_u s → stack_tag_u s.(stack).
Proof.
  intros s Hs t p1 p2.
  inject (@ inr (mem_contains_t s.(mem) t) (lstack_contains_t s.(stack) t)).
  apply Hs.
Qed.

Lemma state_tag_u_implies_disjoint : ∀ s, state_tag_u s → stack_mem_disjoint_tag s.(mem) s.(stack).
Proof.
  intros s Hs.
  split.
  + intros t Hm contra.
    remember (inl Hm : state_contains_t s t) as q1 eqn:Hq1.
    remember (inr contra : state_contains_t s t) as q2 eqn:Hq2.
    unfold state_tag_u in Hs.
    specialize Hs with t q1 q2.
    subst.
    inversion Hq2.
  + intros t Hm contra.
    remember (inr Hm : state_contains_t s t) as q1 eqn:Hq1.
    remember (inl contra : state_contains_t s t) as q2 eqn:Hq2.
    unfold state_tag_u in Hs.
    specialize Hs with t q1 q2.
    subst.
    inversion Hq2.
Qed.

Lemma state_tag_u_implies_tag_uniq : ∀ s, state_tag_u s → tag_uniq s.
Proof.
  intros s Hs.
  split.
  + apply state_tag_u_implies_mem_tag_u; assumption.
  + split.
    ++ apply state_tag_u_implies_stack_tag_u; assumption.
    ++ apply state_tag_u_implies_disjoint; assumption.
Qed.

Lemma tag_uniq_implies_state_tag_u : ∀ s, tag_uniq s → state_tag_u s.
Proof.
  intros s Hs t p1 p2.
  destruct Hs as [Hm [Hs Hd]].
  dependent destruction p1; dependent destruction p2.
  + apply f_equal.
    apply Hm. 
  + exfalso.
    eapply Hd; eauto.
  + exfalso.
    eapply Hd; eauto.
  + apply f_equal.
    apply Hs.
Qed.

Lemma stack_contains_t_cons_u : ∀ (u : UnrestrictedValue) s t,
  lstack_contains_t (unrestrictiveValue u :: s) t →
  lstack_contains_t s t.
Proof.
  intros.
  inversion H.
  assumption.
Defined.

Proposition step_preserve_stack_tag_u {defs} :
∀ (s0 s1 : state),
tag_uniq s0 →
@step defs s0 s1 →
stack_tag_u s1.(stack).
Proof.
  intros s0 s1 [Hm [Hu Hd]] Hs.
  destruct Hs as [i Hs].
  unfold stack_tag_u in *.
  inversion Hs.
  (* MvLoc *)
  + destruct v.
    {
      intros.
      dependent destruction p1; dependent destruction p2.
      + apply f_equal.
        inject (@local_mem_contains_tc s0.(mem).(local) x r H4 t).
        inject1 (@local_mem_ct (mem s0) t) f_inj1.
        apply Hm.
      + exfalso.
        (* p1 is in local mem of s0 *)
        (* but p2 is in stack of s0 *)
        remember (local_mem_ct (local_mem_contains_tc H4 r1)) as pr1.
        unfold stack_mem_disjoint_tag in Hd.
        destruct Hd as [Hd1 _].
        eapply Hd1; eauto.
      (* symmetric case *)
      + exfalso.
        remember (local_mem_ct (local_mem_contains_tc H4 r1)) as pr1.
        unfold stack_mem_disjoint_tag in Hd.
        destruct Hd as [Hd1 _].
        eapply Hd1; eauto.
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
  (* CpLoc *)
  + intros.
    dependent destruction p1.
    dependent destruction p2.
    specialize Hu with t p1 p2.
    rewrite Hu.
    reflexivity.
Admitted.

Proposition step_preserve_mem_tag_u {defs} :
∀ (s0 s1 : state),
tag_uniq s0 →
@step defs s0 s1 →
mem_tag_u s1.(mem).
Proof.
  intros s0 s1 [H1 [H2 H3]] Hs.
  destruct Hs as [i Hs].
  inversion Hs; subst.
  + unfold mem_tag_u.
    intros t p1 p2.
    dependent destruction p1; dependent destruction p2.
    ++ 
      (* p1 p2 both points to local mem of s1 which is M/x *)
      (* so p1 p2 both points to some y in M *)
      (* so p1 = p2 by tag consistency of s0 *)
      dependent destruction l; dependent destruction l0.
      destruct s0 as [mem0 stack0] eqn:Hs0.
      destruct mem0 as [l g] eqn:Hmem0.
      simpl in m, m0.
      pose (remove_p3 _ _ _ _ m) as m'.
      pose (remove_p3 _ _ _ _ m0) as m0'.
      replace l with (local mem0) in m', m0'.
      remember (@local_mem_ct mem0 _ (local_mem_contains_tc m' r0)) as pm'.
      remember (@local_mem_ct mem0 _ (local_mem_contains_tc m0' r2)) as pm0'.
      assert (pm' = pm0').
      {
        simpl in H1.
        rewrite <- Hmem0 in H1.
        apply H1.
      }
      subst.
      dependent destruction H0.
      assert (m = m0) by (apply maps_to_up).
      rewrite H0.
      reflexivity.
      rewrite Hmem0.
      reflexivity.
    (* p1 points to local mem p2 points to global mem *)
    ++ exfalso.
      destruct s0 as [mem0 stack0] eqn:Hs0.
      subst.
      unfold mem_remove in l, g.
      destruct mem0 as [loc glob] eqn:Hmem0.
      simpl in l, g.
      dependent destruction l.
      pose (remove_p3 _ _ _ _ m) as m'.
      simpl in H1.
      rewrite <- Hmem0 in H1.
      replace loc with (mem0.(local)) in m'.
      remember (local_mem_ct (local_mem_contains_tc m' r0)) as pm.
      replace glob with (mem0.(global)) in g.
      remember (global_mem_ct g) as pg.
      assert (pm = pg) by (apply H1).
      subst.
      inversion H0.
      rewrite Hmem0. reflexivity.
      rewrite Hmem0. reflexivity.
    (* p1 points to global mem p2 points to local mem *)
    ++ exfalso.
      destruct s0 as [mem0 stack0] eqn:Hs0.
      destruct mem0 as [loc glob] eqn:Hmem0.
      simpl in l, g.
      dependent destruction l.
      pose (remove_p3 _ _ _ _ m) as m'.
      simpl in H1.
      rewrite <- Hmem0 in H1.
      replace loc with (mem0.(local)) in m'.
      remember (local_mem_ct (local_mem_contains_tc m' r0)) as pm.
      replace glob with (mem0.(global)) in g.
      remember (global_mem_ct g) as pg.
      assert (pm = pg) by (apply H1).
      subst.
      inversion H0.
      rewrite Hmem0. reflexivity.
      rewrite Hmem0. reflexivity.
    (* p1 p2 both points to global mem *)
    ++ destruct s0 as [mem0 stack0] eqn:Hs0.
      destruct mem0 as [loc glob] eqn:Hmem0.
      simpl in *.
      remember (@global_mem_ct {| local := loc; global := glob |} _ g) as pg.
      remember (@global_mem_ct {| local := loc; global := glob |} _ g0) as pg0.
      assert (pg = pg0) by (apply H1).
      apply f_equal.
      inject (@global_mem_ct {| local := loc; global := glob |} t).
      auto.
  (* CpLoc *)
  + unfold mem_tag_u in *.
    destruct H3.
    assumption.
Admitted.


Proposition step_preserve_stack_mem_disjoint {defs} :
∀ (s0 s1 : state),
tag_uniq s0 →
@step defs s0 s1 →
stack_mem_disjoint_tag s1.(mem) s1.(stack).
Proof.
  intros s0 s1 [Hm [Hs Hd]] Hs1.
  destruct Hs1 as [i Hs1].
  inversion Hs1; subst.
  (* MvLoc *)
  + unfold stack_mem_disjoint_tag.
    split.
    (* in mem implies not in stack *)
    ++ intros t Ht Hc.
      pose proof (mem_contains_t_remove_p3 _ _ _ Ht) as Ht'.
      destruct Hd as [Hd1 Hd2].
      destruct v.
      (* moved val is resource *)
      {
        dependent destruction Hc.
        {
          remember (mem s0) as M.
          inversion Ht.
          {
            (* t in M(x) *)
            (* Ht : t in M/x *)
            (* so t in M(y) where y <> x  *)
            (* we thus have two different path to t in M,
              which contradicts the memory uniqueness of M
            *)
            assert ({y & { r & (y <> x) * maps_var_to M y (resourceValue r) * (resource_contains_t r t) }}).
            {
              rewrite local_mem_remove_ in H0.
              inversion H0. subst.
              apply remove_p2_' in H5.
              destruct H5.
              exists x0. exists r0.
              split; auto.
            }
            destruct H5 as [y [r0 [[foo bar] baz]]].
            apply foo.
            eapply mem_tag_u_p1; eauto.
          }
          {
            (* t in M(x) *)
            (* so t is in local memory of M *)
            apply mem_contains_t_remove_p3 in Ht.
            assert (local_mem_contains_t (local M) t).
            {
              econstructor; eauto.
            }
            apply global_mem_contains_t_remove_p3 in H0.
            eapply mem_tag_u_implies_mem_disjoint1; eauto.
          }
        }
        {
          apply mem_contains_t_remove_p3 in Ht.
          apply Hd1 in Ht.
          contradiction.
        }
      }
      (* moved val is unrestricted *)
      {
        apply stack_contains_t_cons_u in Hc.
        eapply Hd1; eauto.
      }
    (* in stack implies not in mem *)
    ++ intros t Ht Hc.
      dependent destruction Ht.
      (* t on top of stack *)
      {
        dependent destruction Hc.
        {
            admit.
        }
        (* Hc points to global memory, not possible since t is moved from local memory *)
        {
          apply global_mem_contains_t_remove_p3 in g.
          eapply mem_tag_u_implies_mem_disjoint1; eauto.
          econstructor; eauto.
        }
      }
      (* t on cdr of stack *)
      {
       apply mem_contains_t_remove_p3 in Hc.
       destruct Hd as [Hd _].
       eapply Hd; eauto. 
      }
  + unfold stack_mem_disjoint_tag in *.
    destruct Hd as [Hd H5].
    split.
    ++ intros t t_in_s0_mem.
      apply Hd in t_in_s0_mem.
      intro contra.
      apply stack_contains_t_cons_u in contra.
      contradiction.
    ++ intros t t_in_s1_stack.
      apply stack_contains_t_cons_u in t_in_s1_stack.
      auto.
Admitted.

Proposition step_preserve_tag_u {defs}:
∀ (s0 s1 : state),
tag_uniq s0 →
@step defs s0 s1 →
tag_uniq s1.
Proof.
  intros.
  split.
  + apply (@step_preserve_mem_tag_u defs) with (s0:=s0); assumption.
  + split.
    ++ apply (@step_preserve_stack_tag_u defs) with (s0:=s0); assumption.
    ++ apply (@step_preserve_stack_mem_disjoint defs) with (s0:=s0); assumption.
Qed.

Definition conserve_t {defs} {s0} {s1} (_ : @step defs s0 s1) : Type :=
  (∀ t, state_contains_t s0 t → state_contains_t s1 t) *
  (∀ t, state_contains_t s1 t → state_contains_t s0 t).

Definition introduce_t {defs} {s0} {s1} (_ : @step defs s0 s1) t : Type :=
  (∀ t, state_contains_t s0 t → state_contains_t s1 t) *
  notT (state_contains_t s0 t) *
  state_contains_t s1 t *
  (∀ t', state_contains_t s1 t' * notT (state_contains_t s0 t') → t' = t).

Definition elim_t {defs} {s0} {s1} (_ : @step defs s0 s1) t : Type :=
  (∀ t, state_contains_t s1 t → state_contains_t s0 t) *
  notT (state_contains_t s1 t) *
  state_contains_t s0 t *
  (∀ t', state_contains_t s0 t' * notT (state_contains_t s1 t') → t' = t).

Lemma conserve_t_not_intro {defs} : ∀ {s0 s1} (Hs : @step defs s0 s1),
  conserve_t Hs → ∀ t, notT (introduce_t Hs t).
Proof.
  intros s0 s1 Hs Hc t contra.
  destruct Hc as [Hc1 Hc2].
  destruct contra as [[[c1 c2] c3] c4].
  apply Hc2 in c3.
  apply c2 in c3.
  contradiction.
Qed.

Lemma conserve_t_not_elim {defs} : ∀ {s0 s1} (Hs : @step defs s0 s1),
  conserve_t Hs → ∀ t, notT (elim_t Hs t).
Proof.
  intros s0 s1 Hs Hc t contra.
  destruct Hc as [Hc1 Hc2].
  destruct contra as [[[c1 c2] c3] c4].
  apply Hc1 in c3.
  apply c2 in c3.
  contradiction.
Qed.

Lemma introduce_t_not_conserved {defs} : ∀ {s0 s1} (Hs : @step defs s0 s1) {t},
introduce_t Hs t → notT (conserve_t Hs).
Proof.
  intros s0 s1 Hs t Hi Hc.
  destruct Hi as [[[Hi1 Hi2] Hi3] Hi4].
  destruct Hc as [Hc1 Hc2].
  apply Hc2 in Hi3.
  apply Hi2 in Hi3.
  contradiction.
Qed.

Lemma introduce_t_not_elim_t {defs} : ∀ {s0 s1} (Hs : @step defs s0 s1) {t},
introduce_t Hs t → ∀ t, notT (elim_t Hs t).
Proof.
  intros s0 s1 Hs t1 Hi t2 He.
  destruct Hi as [[[Hi1 Hi2] Hi3] Hi4].
  destruct He as [[[He1 He2] He3] He4].
  apply Hi1 in He3.
  contradiction.
Qed.

Lemma elim_t_not_conserved {defs} : ∀ {s0 s1} (Hs : @step defs s0 s1) {t},
elim_t Hs t → notT (conserve_t Hs).
Proof.
  intros s0 s1 Hs t He Hc.
  destruct He as [[[He1 He2] He3] He4].
  destruct Hc as [Hc1 Hc2].
  apply Hc1 in He3.
  contradiction.
Qed.

Lemma elim_t_not_elim_t {defs} : ∀ {s0 s1} (Hs : @step defs s0 s1) {t},
elim_t Hs t → ∀ t, notT (introduce_t Hs t).
Proof.
  intros s0 s1 Hs t1 He t2 Hi.
  destruct Hi as [[[Hi1 Hi2] Hi3] Hi4].
  destruct He as [[[He1 He2] He3] He4].
  apply He1 in Hi3.
  contradiction.
Qed.

Theorem local_resource_safety {defs} : ∀ {s0 s1} (Hs : @step defs s0 s1),
conserve_t Hs +
{ t & introduce_t Hs t} +
{ t & elim_t Hs t}.
Proof.
  intros s0 s1 Hs.
  destruct Hs as [i Hs].
  inversion Hs; subst.
  + admit.
  + left. left.
    split.
    ++ intros t t_in_s0.
      destruct t_in_s0.
      {
        left.
        rewrite H in m.
        assumption.
      }
      {
        right.
        rewrite <- H3.
        apply lstackt_cdr.
        assumption.
      }
    ++ intros t t_in_s1.
      destruct t_in_s1.
      {
        left.
        rewrite H.
        assumption.
      }
      {
        rewrite <- H3 in l.
        apply stack_contains_t_cons_u in l.
        right.
        assumption.
      }
  (* StLoc *)
  + left. left. (* prove resource conservation *)
    split.
    (* tag s0 ⊆ tag s1 *)
    ++ intros t t_in_s0.
      destruct t_in_s0.
      (* t in memory of s0 *)
      {
        destruct m.
        (* t in local memory *)
        + left.
          apply local_mem_ct.
          rewrite <- H1.
          apply mem_update_local_u1.
          assumption.
        (* t in global memory *)
        + left.
          apply global_mem_ct.
          rewrite <- H1.
          apply mem_update_local_global_const1.
          assumption.
      }
      (* t in stack of s0 *)
      {
        right.
        rewrite <- H in l.
        apply stack_contains_t_cons_u in l.
        assumption.
      }
    (* tag s1 ⊆ tag s0 *)
    ++ intros t t_in_s1.
      destruct t_in_s1.
      {
        destruct m.
        + left.
          apply local_mem_ct.
          rewrite <- H1 in l.
          apply mem_update_local_u2 in l.
          assumption.
        + left.
          apply global_mem_ct.
          rewrite <- H1 in g.
          apply mem_update_local_global_const2 in g.
          assumption.
      }
      {
        right.
        rewrite <- H.
        apply lstackt_cdr.
        assumption.
      }
  + 
Admitted.

Open Scope type_scope.
(* Theorem only_pack_intro_r : ∀ {defs} {s0 s1} (Hs : @step defs s0 s1) {t}
(Hi : introduce_t Hs t),
{ τ & instr_of_step Hs = (Pack τ) } +
{r & { S & (val (resourceValue r) :: S = s1.(stack)) * (tag_of r = t) }}.
Proof.
Admitted.

Theorem only_unpack_elim_t : ∀ {defs} {s0 s1} (Hs : @step defs s0 s1) {t}
(Hi : elim_t Hs t),
(instr_of_step Hs = Unpack) +
{ r & { S & (val (resourceValue r) :: S = s0.(stack)) * (tag_of r = t) }}.
Proof.
Admitted. *)