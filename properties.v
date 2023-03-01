
Require Import Coq.Lists.List.
Open Scope list_scope.
Import ListNotations.
Require Import Resources.utility.
Require Import Resources.name.
Require Import Resources.type.
Require Import Resources.value.
Require Import Resources.memory.
Require Import Resources.instr.
Require Import Resources.small_step.

Definition pre_tag_consistent (s : state) : Prop :=
  ∀ (r1 r2 : Resource),
    state_contains_r s r1 →
    state_contains_r s r2 →
    tag_of r1 = tag_of r2 →
    r1 = r2.

Theorem step_preserve_tag_consistent :
∀ (s0 s1 : state),
  pre_tag_consistent s0 →
  step s0 s1 →
  pre_tag_consistent s1.
Proof.
intros s0 s1 Hc Hs.
destruct Hs as [s0 s1 i].
unfold pre_tag_consistent.
inversion H.
+ admit.
+ intros.
  unfold pre_tag_consistent in Hc. 
    (* r1, r2 on stack or in mem? *)
    inversion H6; inversion H7.
    {
      (* both in mem  *)
      apply Hc.
      {
        apply state_mem_contains.
        rewrite H0.
        assumption.
      }
      {
        apply state_mem_contains.
        rewrite H0.
        assumption.
      }
      {
        assumption.
      }
    }
    {
      (* r1 on mem, r2 on stack *)
      subst.
      apply Hc.
      {
        apply state_mem_contains.
        rewrite H0.
        assumption.
      }
      {
        apply state_stack_contains.
        rewrite <- H4 in H12.
        apply stack_contains_cons_u in H12.
        assumption.
      }
      {
        assumption.
      }
    }
    {
      (* r1 on mem, r2 on stack *)
      subst.
      apply Hc.
      {
        apply state_stack_contains.
        rewrite <- H4 in H9.
        apply stack_contains_cons_u in H9.
        assumption.
      }
      {
        apply state_mem_contains.
        rewrite H0.
        assumption.
      }
      {
        assumption.
      }
    }
    {
      subst.
      apply Hc.
      {
        apply state_stack_contains.
        rewrite <- H4 in H9.
        apply stack_contains_cons_u in H9.
        assumption.
      }
      {
        apply state_stack_contains.
        rewrite <- H4 in H12.
        apply stack_contains_cons_u in H12.
        assumption.
      }
      {
        assumption.
      }
    }
  ++ intros.
    unfold tag_consistent in Hc. destruct Hc as [_ Hc].
    (* destruct s0.
    destruct s1.
    simpl in *.
    subst.
    destruct p1. *)
    destruct p1; destruct p2.
    {
      subst.
      destruct s.
      simpl in *.
      subst.
      assert (m = m0). {
      remember (state_mem_contains s0 r m0) as m0'.
      remember (state_mem_contains s0 r m) as m'.
      pose proof (Hc r m0' m').
      rewrite Heqm0' in H0.
      rewrite Heqm' in H0.
      apply foo in H0.
      symmetry.
      assump


Definition tag_consistent (s : state) : Prop :=
  (∀ (r1 r2 : Resource),
    state_contains_r s r1 →
    state_contains_r s r2 →
    tag_of r1 = tag_of r2 →
    r1 = r2) ∧
  (∀ (r : Resource) (p1 p2 : state_contains_r s r), p1 = p2).

Lemma stack_contains_cons_u : ∀ (u : UnrestrictedValue) s r,
  lstack_contains_r (val u :: s) r →
  lstack_contains_r s r.
Proof.
  intros.
  inversion H.
  assumption.
Qed.

Lemma foo s :
(∀ (r : Resource) (p1 p2 : state_contains_r s r), p1 = p2) →
(∀ r (p1 p2 : mem_contains_r s.(mem) r), p1 = p2).
Proof.
  intros.
  remember (s.(mem)) as mem.
  remember (s.(stack)) as stack.
  remember (state_mem_contains mem r p1 stack) as x.
  remember (state_mem_contains mem r p2 stack) as y.
  assert (s = {| mem := mem; stack := stack |}). {
    rewrite Heqmem. rewrite Heqstack.
    destruct s.
    simpl.
    reflexivity.
  }
  rewrite <- H0 in x.
  specialize H with r x y.
  rewrite Heqx in H.
  rewrite Heqy in H.
  inversion H.
  inversion H1.
  inversion (existT (λ s : state, {r : Resource & mem_contains_r (mem s) r}) s
  (existT (λ r : Resource, mem_contains_r (mem s) r) r p1) ).
  simpl in H1.
  intuition.
  auto.
  destruct x.

(* Inductive state_contains_r' : state → Resource → Set :=
  | state_mem_contains : ∀ m s r, mem_contains_r m r → state_contains_r' {|
    mem := m;
    stack := s;
  |} r
  | state_stack_contains : ∀ s r, lstack_contains_r s.(stack) r → state_contains_r' s r
. *)

Lemma foo : ∀ s r x y, state_mem_contains s r x = state_mem_contains s r y → x = y.
Proof.
  intros.
  destruct (state_mem_contains s r x) eqn:E1.
  inversion H.
  + 
  destruct (state_mem_contains s r x) eqn:E1; destruct (state_mem_contains s r y) eqn:E2.
  +  
  - destruct (state_mem_contains s r y) eqn:E2.
    + assert (x0 = x) as Hx. { apply (mem_contains_r_proof_uniq s.(mem) r); auto. }
      assert (x0 = y) as Hy. { apply (mem_contains_r_proof_uniq s.(mem) r); auto. }
      rewrite Hx, Hy. reflexivity.
    + discriminate H.
  - destruct (state_mem_contains s r y) eqn:E2.
    + discriminate H.
    + reflexivity.
Qed.

Lemma foo : ∀ s r x y, state_mem_contains s r x = state_mem_contains s r y → x = y.
Proof.
  intros.
  inversion H.
Admitted.

Theorem step_preserve_tag_consistent :
∀ (s0 s1 : state),
  tag_consistent s0 →
  step s0 s1 →
  tag_consistent s1.
Proof.
  intros s0 s1 Hc Hs.
  destruct Hs as [s0 s1 i].
  unfold tag_consistent.
  inversion H.
  + admit.
  + split.
    ++ intros.
      unfold tag_consistent in Hc. destruct Hc as [Hc _].
      (* r1, r2 on stack or in mem? *)
      inversion H6; inversion H7.
      {
        (* both in mem  *)
        apply Hc.
        {
          apply state_mem_contains.
          rewrite H0.
          assumption.
        }
        {
          apply state_mem_contains.
          rewrite H0.
          assumption.
        }
        {
          assumption.
        }
      }
      {
        (* r1 on mem, r2 on stack *)
        subst.
        apply Hc.
        {
          apply state_mem_contains.
          rewrite H0.
          assumption.
        }
        {
          apply state_stack_contains.
          rewrite <- H4 in H12.
          apply stack_contains_cons_u in H12.
          assumption.
        }
        {
          assumption.
        }
      }
      {
        (* r1 on mem, r2 on stack *)
        subst.
        apply Hc.
        {
          apply state_stack_contains.
          rewrite <- H4 in H9.
          apply stack_contains_cons_u in H9.
          assumption.
        }
        {
          apply state_mem_contains.
          rewrite H0.
          assumption.
        }
        {
          assumption.
        }
      }
      {
        subst.
        apply Hc.
        {
          apply state_stack_contains.
          rewrite <- H4 in H9.
          apply stack_contains_cons_u in H9.
          assumption.
        }
        {
          apply state_stack_contains.
          rewrite <- H4 in H12.
          apply stack_contains_cons_u in H12.
          assumption.
        }
        {
          assumption.
        }
      }
    ++ intros.
      unfold tag_consistent in Hc. destruct Hc as [_ Hc].
      (* destruct s0.
      destruct s1.
      simpl in *.
      subst.
      destruct p1. *)
      destruct p1; destruct p2.
      {
       subst.
       destruct s.
       simpl in *.
       subst.
       assert (m = m0). {
        remember (state_mem_contains s0 r m0) as m0'.
        remember (state_mem_contains s0 r m) as m'.
        pose proof (Hc r m0' m').
        rewrite Heqm0' in H0.
        rewrite Heqm' in H0.
        apply foo in H0.
        symmetry.
        assumption.
       }
       rewrite H0.
       reflexivity.
      }
      {

      }
      }
      apply Hc.

Theorem step_preserve_tag_consistent' :
∀ (s0 s1 : state),
  tag_consistent' s0 →
  step s0 s1 →
  tag_consistent' s1.
Proof.
  intros s0 s1 Hc Hs.
  destruct s0. destruct s1.
  destruct Hs.
  inversion H.
  + admit.
  (* cploc *)
  + unfold tag_consistent'. intros.
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
      unfold tag_consistent' in Hc.
      apply Hc with (l1:=inl r) (l2:=inl r0) (c1:=c1) (c2:=c2); assumption.
      ++ unfold tag_consistent' in Hc.
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
      ++ unfold tag_consistent' in Hc.
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
      ++ unfold tag_consistent' in Hc.
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