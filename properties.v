
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

Lemma stack_maps_empty : ∀ (r : StackRef) (v : Value), ¬ stack_maps_to [ ] r v.
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
  destruct root.
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
    exists root.
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

Definition tag_consistent' (s : state) : Prop :=
  ∀ (l1 l2 : state_loc) (c1 c2 : Resource),
    state_maps_to s l1 c1 →
    state_maps_to s l2 c2 →
    tag_of c1 = tag_of c2 →
    l1 = l2.

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

Inductive steps_local : state → state → Prop :=
  | refl : ∀ {s : state}, steps_local s s
  | trans : ∀ {s0 s1 s2 : state} {i : Instr},
    step s0 s1 →
    steps_local s1 s2 →
    steps_local s0 s2.