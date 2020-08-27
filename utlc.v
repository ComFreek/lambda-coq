From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Nat.
Require Import Arith.PeanoNat.
Require Import Relations.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Coq.micromega.Lia.

Inductive LC :=
  | var: nat -> LC
  | app: LC -> LC -> LC
  | lam: LC -> LC
.

Module LCNotations.
  Declare Scope lc_scope.
  Delimit Scope lc_scope with lc.

  Notation "'#' n"  := (var n) (at level 55) : lc_scope.
  Coercion app : LC >-> Funclass.
  Notation "s '@' t"  := (app s t) (at level 60, no associativity) : lc_scope.
  Notation "'\' t" := (lam t) (at level 65).
End LCNotations.

Import LCNotations.
Local Open Scope lc_scope.

Check (\ \ #0 @ #1). (* \x. \y. x y *)

(* A more general notion of closedness: a term is n-closed iff. it accesses at most variables with de Bruijn indices < n.


   The special case for closed terms emerges with n = 0.
*)
Inductive NClosed (n: nat) : LC -> Prop :=
  | varClosed: forall m, Nat.ltb m n -> NClosed n (#m)
  | appClosed: forall s t, NClosed n s -> NClosed n t -> NClosed n (s t)
  | lamClosed: forall s, NClosed (S n) s -> NClosed n (\ s)
.

Definition closed : LC -> Prop := NClosed 0.

Lemma BiggerVariablesNotClosed: forall n m, n <=? m -> ~(NClosed n (#m)).
Proof.
  move => n m Hgt H.
Admitted.

Corollary VariablesNeverClosed: forall n, ~closed (#n).
Proof.
  by move => n; apply: (BiggerVariablesNotClosed).
Qed.

Hint Resolve VariablesNeverClosed : lc_step_db.

Lemma closedHierarchy: forall n m t, NClosed n t -> m >= n -> NClosed m t.
Admitted.
Corollary closedEverywhere: forall n t, closed t -> NClosed n t.
Proof.
  move => n t Hclosed.
  apply: closedHierarchy.
  - apply: Hclosed.
  - by apply Nat.leb_le.
Qed.

Hint Resolve closedEverywhere : lc_step_db.

Fixpoint isNClosed (n: nat) (term: LC): bool := match term with
| #m    => Nat.ltb m n
| s @ t => (isNClosed n s) && (isNClosed n t)
| \ t   => isNClosed (S n) t
end.

Lemma closedP: forall n t, reflect (NClosed n t) (isNClosed n t).
Proof.
  elim => [t|t].
  - elim: t => [n|l IH_l k IH_k|].
    + simpl.
      have U: (n <? 0 = false). admit.
      rewrite U; clear U.
      constructor.
      auto with lc_step_db.
    + simpl.
      case Hl_closed: (isNClosed 0 l); case Hk_closed: (isNClosed 0 k); simpl.
      * apply: ReflectT; constructor.
        Admitted.

Hint Resolve closedP : lc_step_db.

Inductive variablesUpdated (n delta: nat): LC -> LC -> Prop :=
  | deltaOnVarUntouched: forall m, Nat.ltb m n -> variablesUpdated n delta (#m) (#m)

  | deltaOnVar: forall m, Nat.leb n m -> variablesUpdated n delta (#m) (#(delta+m))

  | deltaOnApp: forall s s' t t',
        variablesUpdated n delta s s'
     -> variablesUpdated n delta t t'
     -> variablesUpdated n delta (s t) (s' t')

  | deltaOnLam: forall s s',
        variablesUpdated (S n) delta s s'
     -> variablesUpdated n delta (\ s) (\ s')
.

(* represents the levelling up of exactly 1 to variables *)
Definition variablesUpticked: LC -> LC -> Prop := variablesUpdated 0 0.

Fixpoint updateVariables (n delta: nat) (t: LC) : LC := match t with
| #m => if (Nat.ltb m n) then (#m) else (#(delta+m))
| s @ t => (updateVariables n delta s) @ (updateVariables n delta t)
| (\ s) => \ (updateVariables (S n) delta s)
end.

Definition uptickVariables := updateVariables 0 1.

Lemma UpdateVariablesReflection: forall n delta s t, variablesUpdated n delta s t <-> updateVariables n delta s = t.
Admitted.

Lemma UptickVariablesReflection: forall t, variablesUpticked t (uptickVariables t).
Proof.
Admitted.

Hint Resolve UptickVariablesReflection : lc_step_db.

Lemma ClosedTermsStableUnderDeltaOfVariables: forall t delta, closed t -> variablesUpdated 0 delta t t.
Proof.
  by move => ? ?; elim => //; do ! constructor.
Qed.

Corollary ClosedTermsStableUnderUpticking: forall t, closed t -> variablesUpticked t t.
Proof.
  by move => t; apply: ClosedTermsStableUnderDeltaOfVariables.
Qed.

Hint Resolve ClosedTermsStableUnderUpticking : lc_step_db.

Lemma CanonicalUpticking: forall s t, variablesUpticked s t -> t = uptickVariables s.
Proof. Admitted. (* we should prove this via a yet-to-be-created reflection view. *)

Hint Resolve CanonicalUpticking : lc_step_db.

(*

  `levelledSubstitution n s t s'` is supposed to state that `s` goes over to `s'` upon eliminating n-th variable occurrences (i.e. #n) by substitution with `t`.

  This substitution is performed non-naively, see examples below.

  Later, when stating the operational semantics of our lambda calculus, the beta redex `(\ s) t` will go over to `s'` where `s'` is precisely such that `levelledSubstitution 0 s t s'`.
  That is, it represents (as a special case) elimination of #0 occurrences.
*)
Inductive levelledSubstitution (n: nat): LC -> LC -> LC -> Prop :=
  (* when the current level matches precisely, substitute *)
  | matchingVarIdx: forall t, levelledSubstitution n (#n) t t

  (* variable indices < n are left untouched: they refer to more inner lambda abstractions *)

  | untouchedVarIdx: forall t m, Nat.ltb m n -> levelledSubstitution n (#m) t (#m)

  (* variable indices > n are decremented since the n-th level is eliminated *)
  | decrementedVarIdx: forall t m, Nat.ltb n (S m) -> levelledSubstitution n (#(S m)) t (#m)

  | appRepl: forall s1 s2 s1' s2' t,
       levelledSubstitution n s1 t s1'
    -> levelledSubstitution n s2 t s2'
    -> levelledSubstitution n (s1 s2) t (s1' s2')

  | lamRepl: forall s s' t t',
       variablesUpticked t t'
    -> levelledSubstitution (S n) s t' s'
    -> levelledSubstitution n (\ s) t (\ s')
.

Notation "s '//' t '-->' s'" := (levelledSubstitution 0 s t s') (at level 60, no associativity).

Lemma ltbIrreflexive: forall n, ~(n <? n).
Proof.
  by elim => [|n IHn]; cbn.
Qed.

(* Main motivation: (0)-closed terms are stable under (0)substitution.
   However, we need the following stronger statement for induction to go through.
*)
Lemma NClosedTermsStableUnderNSubstitution: forall s t n, NClosed n s -> levelledSubstitution n s t s.
Proof.
  elim => // [m t n' Hs_closed | l IH_l k IH_k t Hcompound_closed | l IH t n  Hclosed_abstraction].
  - case Hcmp: (m ?= n').
    + have Heq: (m = n') by apply (Nat.compare_eq_iff _ _).
      contradict Hs_closed.
      rewrite Heq.
      move => H.
      inversion H.
      by contradict H1; apply: ltbIrreflexive.
    + have Hlt: (m < n') by apply (Nat.compare_lt_iff _ _).
      apply: untouchedVarIdx.
      by apply Nat.ltb_lt.
    + have Hgt: (m > n') by apply (Nat.compare_gt_iff _ _).
      contradict Hs_closed.
      apply: BiggerVariablesNotClosed.
      apply Nat.leb_le.
      lia.

  - constructor.
    + by apply: IH_l; inversion H.
    + by apply: IH_k; inversion H.

  - have Hclosed_body: (NClosed (S n) l) by inversion Hclosed_abstraction.
    apply: lamRepl.
    + apply: UptickVariablesReflection.
    + by apply: IH.
Qed.

Corollary ClosedTermsStableUnderSubstitution: forall s t, closed s -> s // t --> s.
Proof.
  by move => ? ? ?; apply: NClosedTermsStableUnderNSubstitution.
Qed.

Hint Resolve ClosedTermsStableUnderSubstitution : lc_step_db.

Lemma UptickingLevelsUpClosedness: forall n t t', variablesUpticked t t' -> NClosed n t -> NClosed (S n) t'.
Proof.
Admitted.

Hint Resolve UptickingLevelsUpClosedness : lc_step_db.

Lemma NUpdatedVariablesStableUnderSubstitution: forall n s t, levelledSubstitution n (updateVariables n 1 s) t s.
Proof.
  move => n s.
  generalize dependent n.
  elim: s => [m n t|l IH_l k IH_k n t|l IH_l n t].
  - case Hcmp: (n ?= m).
    + have Heq: (n = m) by apply (Nat.compare_eq_iff _ _).
      rewrite Heq.
      have U: (updateVariables m 1 (#m) = #(S m)). admit.
      rewrite U.
      constructor.
      by apply Nat.ltb_lt.
    + have Hlt: (n < m) by apply (Nat.compare_lt_iff _ _).
      have notHgt: ((m <? n) = false). admit.
      simpl; rewrite notHgt.
      
      constructor.
      by apply Nat.ltb_lt; lia.
    + have Hgt: (n > m) by apply (Nat.compare_gt_iff _ _).
      have notHgt: (m <? n = true). admit.
      simpl. rewrite notHgt.
      
      constructor.
      by apply Nat.ltb_lt; lia.

  - simpl; constructor.
    + by apply: IH_l.
    + by apply: IH_k.
  - econstructor.
    + apply: UptickVariablesReflection.
    + fold updateVariables.
      apply: IH_l.
Admitted.

Corollary UptickedVariablesStableUnderSubstitution: forall s t, uptickVariables s // t --> s.
Proof. by apply: NUpdatedVariablesStableUnderSubstitution. Qed.

Hint Resolve UptickedVariablesStableUnderSubstitution : lc_step_db.

Module VarReplExamples.
Example ex0: forall term, (#0) // term --> term.
Proof. by do ! constructor. Qed.

Example ex1: forall term, closed term -> (\ (#0) (#1)) // term --> (\ (#0) term).
Proof.
  move => term Hclosed.
  by do ! econstructor; apply: ClosedTermsStableUnderUpticking.
Qed.

Example ex2: forall term, closed term -> (\ (#0) (#1) (#2)) // term --> (\ (#0) term (#1)).
Proof.
  move => term Hclosed.
  by do ! econstructor; apply: ClosedTermsStableUnderUpticking.
Qed.

Example ex3: forall term, closed term -> (\ #1) // term --> (\ term).
Proof.
  move => term Hclosed.
  by do ! econstructor; apply: ClosedTermsStableUnderUpticking.
Qed.
End VarReplExamples.



Reserved Notation "s '-->' t" (at level 65).

(* One-step operational semantics for our lambda calculus *)
Inductive lcOpSem : LC -> LC -> Prop :=
  | betaRed: forall s s' t,
         levelledSubstitution 0 s t s'
      -> (\ s) t --> s'

  | appStepL: forall s s' t,
         s --> s'
      -> (s t) --> (s' t)

  | appStepR: forall s t t',
         t --> t'
      -> (s t) --> (s t')

  where "s '-->' t" := (lcOpSem s t).



Notation "s '-->*' t" := (clos_refl_trans LC lcOpSem s t) (at level 65).
Notation "s '<-->*' t" := (clos_refl_sym_trans LC lcOpSem s t) (at level 65).

Example identity: forall t, (\ #0) t --> t.
Proof. by do ! constructor. Qed.

Example first_projection: forall s t, (\ \ #1) s t -->* s.
Proof. 
  move => s t.
  apply: rt_trans.
  - constructor.
    apply: appStepL.
    apply: betaRed.

    by do ! econstructor; apply: UptickVariablesReflection.
  - constructor.
    apply: betaRed.
    apply: UptickedVariablesStableUnderSubstitution.
Qed.

(* Church encoding of nat

   0 = \z \s. z
   1 = \z \s. s z
   2 = \z \s. s (s z)
   ...
   
   (n + 1) = \z \s. (n (s z) s)

 *)

Fixpoint internalizeNatInner (n: nat): LC := match n with
| 0 => #1
| S m => #0 @ (internalizeNatInner m)
end.

Definition internalizeNat (n: nat) := \ \ internalizeNatInner n.

Example ex0 : internalizeNat 0 = \ \ #1.
Proof. by simpl. Qed.
Example ex1 : internalizeNat 1 = \ \  #0 @ #1.
Proof. by simpl. Qed.
Example ex2 : internalizeNat 2 = \ \  #0 @ (#0 @ #1).
Proof. by simpl. Qed.

(* Church Encoding of LC: \var \app \lam. ---*)

Fixpoint internalizeLCInner (term: LC): LC := match term with
| # idx => #2 @ internalizeNat idx
| s @ t => (#1 @ internalizeLCInner s) @ (internalizeLCInner t)
| \ t   => #0 @ internalizeLCInner t
end.
Definition internalizeLC (term: LC): LC := \ \ \ internalizeLCInner term.

(* \x. x *)
Example exInt0 : internalizeLC (\ #0) = \ \ \ #0 @ (#2 @ internalizeNat 0).
Proof. by simpl. Qed.
Compute (internalizeLC (\ #0 @ #0)).

(* Church Encodings of tuples *)
Definition lc_pair: LC := \ \ \ (#0) (#2) (#1).
Definition lc_fst: LC := \ (#0) (\ \ (#1)).
Definition lc_snd: LC := \ (#0) (\ \ (#0)).

(* Church Encodings of lists *)
Definition lc_nil: LC := \ (*1:nilInterp*) \ (*0:consInterp*) #1.
Definition lc_cons: LC := \ (*3:x*) \ (*2:xs*) \ (*1:nilInterp*) \ (*0:consInterp*) (#0) (#3) ((#2) (#1) (#0)).

(* some default value required for def. of lc_head *)
Definition lc_dummy: LC := \ #0.
Definition lc_head: LC := \ (*list*) (#0) lc_dummy (\ (*x*) \ (*xs*) (#1)).
Definition lc_tail: LC := \ (*list*) lc_fst (
  (#0) (lc_pair lc_nil lc_nil) (\(*x*) \(*xs*) lc_pair (lc_snd (#0)) (lc_cons (#1) (lc_snd (#0))))
).

(* Define evaluation on internalized LC terms by folding on them.
   Concretely, we transform every internalized LC term to a function receiving
   a context and returning the evaluated thing.
   
   Construction by int-e from ##math on Freenode. Formalization in Coq by me.
*)

(* The variable interpretation returns a function receiving a context
   and returning the respective variable from that, i.e., the n-th entry. *)
Definition evalVarInterp: LC := \ \            (* \n. \ctx. *)
  lc_head ((#1) (#0) lc_tail).                       (* head ((n ctx) tail) *)

(* T *)
Definition evalAppInterp: LC := \ \ \          (* \s. \t. \ctx. *)
  (#2) (#0) ((#1) (#0)).                       (* s ctx (t ctx) *)

(* The lambda abstraction interpretation returns a function receiving a context --
   as before -- and receiving a term for application and returning the applied
   (i.e. beta reduced) lambda's function body.
 *)
Definition evalLamInterp: LC := \ \ \          (* \t. \ctx. \v. *)
  (#2) (lc_cons (#0) (#1)).                          (* t (cons v ctx) *)

(* Finally, the evaluator just folds on internalized LC terms by the above interpretations and starts with an empty (nil) context. *)
Definition evaluator: LC := \ (#0) evalVarInterp evalAppInterp evalLamInterp lc_nil.

(*Lemma lem: closed evalVarInterp.
Proof.
  rewrite /closed.
  move /closedP.
Lemma lem1: closed evalAppInterp. Admitted.

Hint Resolve lem lem1 : lc_step_db.

Example ex: forall t, evaluator (internalizeLC ((\ #0) t)) -->* t.
Proof.
  move => t.
  rewrite /evaluator.

  apply: rt_trans.
  - constructor.
    apply: betaRed.
    constructor.
    + constructor.
      * constructor. constructor. constructor.
        assert (K: closed evalVarInterp). admit. auto 10 with lc_step_db.
        apply: ClosedTermsStableUnderSubstitution. auto with lc_step_db.
  apply betaRed.
  apply appRedL.

  do ! constructor.
  apply: betaRed.

*)