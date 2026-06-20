From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Export ListDef.

Inductive type : Type :=
| Natural : type
| Function : type -> type -> type
.

Notation "'ℕ'" := (Natural) (at level 50). 
Notation "tau → tau'" := (Function tau tau') (at level 60).

Definition var : Type := nat.

Inductive term : Type :=
| Nat : nat -> term
| Sum : term -> term -> term
| Var : var -> term
| Lam : var -> type -> term -> term
| App : term -> term -> term
.
Notation "t '+' t'" := (Sum t t').
Notation "'λ' x ':' tau '.' t" := (Lam x tau t) (at level 60).

Inductive value : term -> Prop :=
| VNat (n : nat) : value (Nat n)
| VLam (x : var) (tau : type) (t : term) : value (Lam x tau t)
.

Fixpoint subst (t t' : term) (var : nat) : term :=
  match t with
  | Nat n => Nat n
  | Sum t1 t2 => Sum (subst t1 t' var) (subst t2 t' var)
  | Var v => if v =? var then t' else Var v
  | Lam x tau body => if x =? var then Lam x tau body else Lam x tau (subst body t' var)
  | App t1 t2 => App (subst t1 t' var) (subst t2 t' var)
  end
.
Notation "a [ b / c ]" := (subst a b c).

Definition Gamma : Type := var -> option type.
Definition gamma_nil : Gamma := fun x => None.
Definition gamma_cons (g : Gamma) (x : var) (tau : type) :=
  fun x' => if x' =? x then Some tau else g x
.
Notation " ∅ " := (gamma_nil).
Notation "g , x : tau" := (gamma_cons g x tau) (at level 60).

Inductive synty (g : Gamma) : term -> type -> Prop :=
| TNat (n : nat) : synty g (Nat n) Natural
| TSum (t t' : term) : synty g t Natural -> synty g t' Natural -> synty g (Sum t t') Natural
| TVar (v : var) (tau : type) : (g v) = Some tau -> synty g (Var v) tau
| TLam (v : var) (tau tau' : type) (t : term) : synty (gamma_cons g v tau) t tau' -> synty g (Lam v tau t) (Function tau tau')
| TApp (t t' : term) (tau tau' : type) : synty g t (Function tau tau') -> synty g t' tau -> synty g (App t t') tau'
.
Notation "g ⊢ t : tau" := (synty g t tau) (at level 60).

Definition identity : term := Lam 0 Natural (Var 0).
Example identity_typing : synty gamma_nil identity (Function Natural Natural).
Proof.
  unfold identity.
  apply TLam. apply TVar. now cbn.
Qed.

Inductive red : term -> term -> Prop :=
| RSumLeft (t1 t1' t2 : term) : red t1 t1' -> red (Sum t1 t2) (Sum t1' t2)
| RSumRight (n : nat) (t2 t2' : term) : red t2 t2' -> red (Sum (Nat n) t2) (Sum (Nat n) t2')
| RSum (n n' : nat) : red (Sum (Nat n) (Nat n')) (Nat (n + n'))
| RAppLeft (t1 t1' t2 : term) : red t1 t1' -> red (App t1 t2) (App t1' t2)
| RAppRight (x : var) (tau : type) (t : term) (t2 t2' : term) : red t2 t2' -> red (App (Lam x tau t) t2) (App (Lam x tau t) t2')
| RApp (x : var) (tau : type) (t : term) (v : term) : value v -> red (App (Lam x tau t) v) (subst t v x)
.
Notation "t ↪ t'" := (red t t') (at level 60).

Lemma canonicity_nat : forall t, synty gamma_nil t Natural -> value t -> exists n, t = Nat n.
Proof.
    intros t H1 H2.
    inversion H1.
    - exists n. reflexivity.
    - rewrite <- H3 in H2. inversion H2.
    - rewrite <- H0 in H2. inversion H2.
    - rewrite <- H3 in H2. inversion H2.
Qed.

Lemma canonicity_lam : forall t tau tau', synty gamma_nil t (Function tau tau') -> value t -> exists x t', t = Lam x tau t'.
Proof.
    intros t tau tau' H1 H2.
    inversion H1.
    - unfold gamma_nil in H. discriminate.
    - subst. exists v. exists t0. reflexivity.
    - subst. inversion H2.
Qed.

Theorem progress : forall t tau, synty gamma_nil t tau -> (value t \/ exists t', red t t').
Proof.
  intros t tau H.
  remember gamma_nil as g eqn:Gnil.
  induction H as [g n|g t t' H1 IH1 H2 IH2|g v tau H|g v tau tau' t H1 IH|g t t' tau tau' H1 IH1 H2 IH2]; subst.
  - left. apply VNat.
  - right. specialize (IH1 eq_refl). specialize (IH2 eq_refl).
    destruct IH1 as [H3|H3'], IH2 as [H4|H4'].
    + pose proof (canonicity_nat t H1 H3) as H5. destruct H5 as [n H5].
      pose proof (canonicity_nat t' H2 H4) as H6. destruct H6 as [n' H6].
      subst. exists (Nat (n + n')). apply RSum.
    + destruct H4' as [t'' H4'].
      exists (Sum t t'').
      pose proof (canonicity_nat t H1 H3) as H. destruct H as [n H]. subst.
      now apply RSumRight.
    + destruct H3' as [t'' H3'].
      exists (Sum t'' t').
      now apply RSumLeft.
    + destruct H3' as [t'' H3'].
      exists (Sum t'' t').
      now apply RSumLeft.
  - now subst.
  - left. apply VLam.
  - right. specialize (IH1 eq_refl). specialize (IH2 eq_refl).
    destruct IH1 as [H3|H3'], IH2 as [H4|H4'].
    + pose proof (canonicity_lam t tau tau' H1 H3) as H5.
      destruct H5 as [x [t'' H5]].
      exists (subst t'' t' x).
      rewrite H5.
      now apply RApp.
    + pose proof (canonicity_lam t tau tau' H1 H3) as H5.
      destruct H5 as [x [t'' H5]].
      destruct H4' as [t''' H4'].
      exists (App t t''').
      subst. now apply RAppRight.
    + destruct H3' as [t'' H3'].
      exists (App t'' t').
      now apply RAppLeft.
    + destruct H3' as [t'' H3'].
      exists (App t'' t').
      now apply RAppLeft.
Qed.

Lemma preservation_subst : forall t t' x tau tau',
  synty (gamma_cons gamma_nil x tau) t tau' ->
  synty gamma_nil t' tau ->
  synty gamma_nil (subst t t' x) tau'.
Proof.
  intros t t' x tau tau' H1 H2.
  generalize dependent tau'.
  induction t.
  - intros tau' H1. inversion H1. subst. cbn. apply TNat.
  - intros tau' H1. inversion H1. cbn.
    specialize (IHt1 Natural H3). specialize (IHt2 Natural H5).
    now apply TSum.
  - intros tau' H1. cbn. destruct (v =? x) eqn:Evx.
    + apply Nat.eqb_eq in Evx. subst.
      inversion H1. subst. unfold gamma_cons in H0.
      rewrite Nat.eqb_refl in H0. injection H0 as H0'. now subst.
    + inversion H1. subst. unfold gamma_cons in H0.
      rewrite Evx in H0. discriminate.
  - intros tau' H1. cbn. destruct (v =? x) eqn:Exv.
    + specialize (IHt tau').
Admitted.

Theorem preservation : forall t tau t', synty gamma_nil t tau -> red t t' -> synty gamma_nil t' tau.
Proof.
  intros t tau t' H1 H2.
  generalize dependent tau.
  induction H2 as [
    t1 t1' t2 H2 IH|
    n t2 t2' H2 IH|
    n1 n2|
    t1 t1' t2 H2 IH|
    x tau t t2 t2' H2 IH|
    x tau t t2 H2].
  - intros tau H1. specialize (IH tau).
    inversion H1. subst. specialize (IH H3). now apply TSum.
  - intros tau H1. specialize (IH tau).
    inversion H1. subst. specialize (IH H5). now apply TSum.
  - intros tau H1. inversion H1. subst. apply TNat.
  - intros tau H1. inversion H1. subst.
    specialize (IH (Function tau0 tau) H3).
    now apply TApp with (tau := tau0).
  - intros tau' H1. inversion H1. subst. specialize (IH tau0 H5).
    now apply TApp with (tau := tau0).
  - intros tau' H1. inversion H1. subst. inversion H3. subst.
    now apply preservation_subst with (tau := tau0).
Qed.

Inductive red_star : term -> term -> Prop :=
| RSRefl (t : term) : red_star t t
| RSTrans (t t' t'' : term) : red t t' -> red_star t' t'' -> red_star t t''
.
Notation "t ↪⋆ t'" := (red_star t t') (at level 60).
Definition refl := red_star (Nat 0) (Nat 0).
Print refl.

Theorem type_safety : forall t t' tau,
  synty gamma_nil t tau ->
  red_star t t' ->
  (value t' \/ exists t'', red t' t'').
Proof.
  intros t t' tau H1 H2.
  induction H2 as [|t t0 t' H2 H3 IH].
  - now apply progress in H1.
  - pose proof (preservation t tau t0 H1 H2) as HP.
    now specialize (IH HP).
Qed.