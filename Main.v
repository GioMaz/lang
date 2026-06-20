From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Export ListDef.

Inductive type : Type :=
| Natural : type
| Function : type -> type -> type
.

Notation "'ℕ'" := Natural (at level 60). 
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

Definition Gamma : Type := list (var * type).

Fixpoint subst (t t' : term) (var : nat) : term :=
  match t with
  | Nat n => Nat n
  | Sum t1 t2 => Sum (subst t1 t' var) (subst t2 t' var)
  | Var v => if v =? var then t' else Var v
  | Lam x _ body => if x =? var then body else subst body t' var
  | App t1 t2 => App (subst t1 t' var) (subst t2 t' var)
  end
.

Inductive synty (g : Gamma) : term -> type -> Prop :=
| TNat (n : nat) : synty g (Nat n) Natural
| TSum (t t' : term) : synty g t Natural -> synty g t' Natural -> synty g (Sum t t') Natural
| TVar (v : var) (tau : type) : In (v, tau) g -> synty g (Var v) tau
| TLam (v : var) (tau tau' : type) (t : term) : synty ((v, tau) :: g) t tau' -> synty g (Lam v tau t) (Function tau tau')
| TApp (t t' : term) (tau tau' : type) : synty g t (Function tau tau') -> synty g t' tau -> synty g (App t t') tau'
.

Notation "g ⊢ t : tau" := (synty g t tau) (at level 60).

Definition identity : term := Lam 0 Natural (Var 0).
Example identity_typing : synty nil identity (Function Natural Natural).
Proof.
  unfold identity.
  apply TLam, TVar. unfold In. left. reflexivity.
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

Lemma canonicity_nat : forall t, synty nil t Natural -> value t -> exists n, t = Nat n.
Proof.
    intros t H1 H2.
    inversion H1.
    - exists n. reflexivity.
    - rewrite <- H3 in H2. inversion H2.
    - rewrite <- H0 in H2. inversion H2.
    - rewrite <- H3 in H2. inversion H2.
Qed.

Lemma canonicity_lam : forall t tau tau', synty nil t (Function tau tau') -> value t -> exists x t', t = Lam x tau t'.
Proof.
    intros t tau tau' H1 H2.
    inversion H1.
    - contradiction.
    - subst. exists v. exists t0. reflexivity.
    - subst. inversion H2.
Qed.

Theorem progress : forall t tau, synty nil t tau -> (value t \/ exists t', red t t').
Proof.
  intros t tau H.
  remember nil as g eqn:Gnil.
  induction H as [g n|g t t' H1 IH1 H2 IH2|g v tau H|g v tau tau' t H IH|g t t' tau tau' H1 IH1 H2 IH2]; subst.
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