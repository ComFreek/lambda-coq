From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Relations.Relation_Operators.
Require Import Relations.Operators_Properties.

Require Import utlc.
Import LCNotations.

Open Scope lc_scope.

(* We use a uniform approach to terms and types: they both are lambda terms. *)

(* For types we posit a fundamental term representing types. *)
Axiom typeTp: LC.
Axiom typeTpClosed: LC.

Hint Resolve typeTpClosed : lc_step_db.

(* and a fundamental term representing function types, i.e. funTp A B represents the function type A => B. *)
Axiom funTp : LC.
Axiom funTpClosed : closed funTp.

Hint Resolve funTpClosed : lc_step_db.

Notation "A '=>' B" := (funTp A B) (at level 60, right associativity).

(* with de Bruijn indices our context just needs to be a list of types *)
Definition TpCtx := list LC.

(* colon instead of 'of' didn't work *)
Reserved Notation "Gamma '|-' s 'of' t" (at level 65).

Inductive TpJudgement : TpCtx -> LC -> LC -> Prop :=
  | tpOfType: forall ctx tp, ctx |- tp of typeTp

  | tpOfVar: forall ctx n tp,

       nth_error ctx n = Some tp
    -> ctx |- (#n) of tp

  | tpOfApp: forall ctx s t A B,

       ctx |- s of (A => B)
    -> ctx |- t of A
    -> ctx |- (s t) of B

  | tpOfLam: forall ctx t A B B',
       variablesUpticked B B'
    -> (cons A ctx) |- t of B'
    -> ctx |- (\ t) of (A => B)

  | eqTp: forall ctx t A B,
       A <-->* B
    -> ctx |- t of A
    -> ctx |- t of B

  | depTp: forall ctx t depTp,
       (forall tpInstance, closed tpInstance -> ctx |- t of ((\ depTp) tpInstance))
    -> ctx |- t of (\ depTp)


where "Gamma '|-' s 'of' t" := (TpJudgement Gamma s t).

Notation "'|-' s 'of' t" := (nil |- s of t) (at level 65).

Example identityTypeExtensional: forall A, closed A -> |- (\ #0) of (A => A).
Proof.
  move => ? ?.
  by apply: tpOfLam; [apply: ClosedTermsStableUnderUpticking|constructor].
Qed.

Example identityTypeIntensional: |- (\ #0) of (\ #0 => #0).
Proof.
  apply: depTp.
  move => ? ?.
  apply: eqTp.
  - by apply: rst_sym; do ! constructor; auto with lc_step_db.
  - by apply: identityTypeExtensional.
Qed.

Definition lc_product_type := \ \ \ (#2) => (#1) => (#0).


Example lc_pair_type: |- lc_pair of (\ \ #1 => #0 => lc_product_type (#1) (#0)).
Proof.
  have abc: (closed lc_product_type). admit.
  apply: depTp => ? ?.
  apply: eqTp.
  - by apply: rst_sym; do ! constructor; auto with lc_step_db.
  - apply: eqTp. 
    + apply: rst_sym. do ! constructor; auto with lc_step_db.
      econstructor.
      * by apply: ClosedTermsStableUnderUpticking.
      * do ! constructor.
        ** by apply: NClosedTermsStableUnderNSubstitution; auto with lc_step_db.
        ** by apply: NClosedTermsStableUnderNSubstitution; auto with lc_step_db.
        ** apply: NClosedTermsStableUnderNSubstitution; auto with lc_step_db.
    + do ! constructor => ? ?.
      apply: eqTp.
      * apply: rst_sym. do ! constructor; auto with lc_step_db.
      * do ! constructor.

Definition lc_list_type := \ #0 => (#0 => #0) => #0.
Definition lc_list_type_for (A: LC) := A => (A => A) => A.

Example lc_nil_type: |- lc_nil of lc_list_type.
Proof.
  apply: depTp => ? ?.
  apply: eqTp.
  - by apply: rst_sym; do ! constructor; auto with lc_step_db.
  - do ! constructor.
Qed.

Example lc_cons_type: |- lc_cons of (\ #0 => lc_list_type_for (#0) => lc_list_type_for (#0)).
Proof.
  apply: depTp => A ?.
  apply: eqTp.
  - by apply: rst_sym; do ! constructor; auto with lc_step_db.
  - do ! constructor.
Qed.