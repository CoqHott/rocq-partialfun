From Stdlib Require Import Utf8 RelationClasses.
From Partial Require Import Util.
From Equations Require Import Equations.

Set Default Goal Selector "!".
(* Set Universe Polymorphism. *)
(* Set Polymorphic Inductive Cumulativity. *)
Set Primitive Projections.
Set Equations Transparent.
Unset Equations With Funext.

(**
  We define partial values as a record with
  - a proposition telling us whether it has a value or not;
  - the value when the proposition holds;
  - a proof that the value is unique.

  We could also require the proposition to be a mere proposition, or put it in
  SProp, but that would lead to complications we decided against.
*)

Record partial A := guarded {
  defined : Prop ;
  value : defined → A ;
  unique_value : ∀ p q, value p = value q
}.

Arguments guarded {A}.
Arguments defined {A}.
Arguments value {A}.
Arguments unique_value {A}.

(** Equality and ordering of partial values *)

Definition partial_eq {A} (u v : partial A) :=
  (defined u ↔ defined v) ∧
  (∀ p q, value u p = value v q).

Notation "u ≈ v" := (partial_eq u v) (at level 70, no associativity).

Definition partial_le {A} (u v : partial A) :=
  (defined u → defined v) ∧
  (∀ p q, value u p = value v q).

Notation "u ≲ v" := (partial_le u v) (at level 70, no associativity).

#[export]
Instance Reflexive_partial_eq A : Reflexive (@partial_eq A).
Proof.
  intros [P v h]. split. all: cbn.
  all: firstorder.
Qed.

#[export]
Instance Symmetric_partial_eq A : Symmetric (@partial_eq A).
Proof.
  intros [P v p] [Q w q] [hPQ e]. cbn in *. split. all: cbn.
  all: firstorder.
Qed.

#[export]
Instance Transitive_partial_eq A : Transitive (@partial_eq A).
Proof.
  intros [P v p] [Q w q] [R z r] [hPQ evw] [hQR ewz].
  cbn in *. split. all: cbn. 1: firstorder.
  intros x y. unshelve erewrite evw. 1: firstorder.
  eapply ewz.
Qed.

#[export]
Instance Reflexive_partial_le A : Reflexive (@partial_le A).
Proof.
  intros [P v h]. split. all: cbn.
  all: firstorder.
Qed.

#[export]
Instance Transitive_partial_le A : Transitive (@partial_le A).
Proof.
  intros [P v p] [Q w q] [R z r] [hPQ evw] [hQR ewz].
  cbn in *. split. all: cbn. 1: firstorder.
  intros x y. unshelve erewrite evw. 1: firstorder.
  eapply ewz.
Qed.

Lemma partial_eq_value A (u v : partial A) p q :
  u ≈ v →
  value u p = value v q.
Proof.
  intros [h e].
  apply e.
Qed.

Lemma value_cong A (u v : partial A) p q :
  u = v →
  value u p = value v q.
Proof.
  intros e.
  apply partial_eq_value, reflexive_eq. 1: exact _.
  assumption.
Qed.

(** Partial equality coincides with equality with sufficient assumptions *)

Definition PropExt := ∀ (P Q : Prop), P ↔ Q → P = Q.
Definition FunExt := ∀ A B (f g : ∀ (x : A), B x), (∀ x, f x = g x) → f = g.
Definition ProofIrr := ∀ (P : Prop) (p q : P), p = q.

Lemma PropExt_ProofIrr : PropExt → ProofIrr.
Proof.
  intros hpe P p q.
  assert (e : P = True).
  { apply hpe. firstorder. }
  subst. destruct p, q. reflexivity.
Qed.

Lemma partial_eq_eq A (u v : partial A) :
  PropExt →
  FunExt →
  u ≈ v →
  u = v.
Proof.
  intros hpe hfe [h%hpe e].
  destruct u as [du vu uu], v as [dv vv uv].
  cbn in *. subst.
  assert (vu = vv) as ->.
  { apply hfe. intros. apply e. }
  f_equal. apply PropExt_ProofIrr. assumption.
Qed.

(** Definition relation *)

Definition hasdef {A} (e : partial A) (v : A) :=
  defined e ∧ (∀ p, value e p = v).

Notation "e ↦ v" := (hasdef e v) (at level 70, no associativity).

Lemma hasdef_equiv {A} (e : partial A) v h :
  e ↦ v ↔ value e h = v.
Proof.
  split.
  - intros [_ hev]. apply hev.
  - intros hev. split. 1: auto.
    intros p. rewrite <- hev. eapply unique_value.
Qed.

(** Partiality is a monad *)

Definition ret {A} (a : A) : partial A :=
  guarded True (λ _, a) (λ _ _, eq_refl).

#[refine]
Definition bind {A B} (pa : partial A) (pb : A → partial B) : partial B :=
  let (da,va,ua) := pa in
  guarded
    (∃ p : da, defined (pb (va p)))
    (λ p, value (pb (value pa (ex_proj1 p))) (ex_proj2 p))
    _.
Proof.
  intros [p1 p2] [q1 q2]. cbn.
  apply partial_eq_value.
  erewrite ua. reflexivity.
Defined.

(** Monad laws, relative to partial equality *)

Lemma ret_bind {A B} (a : A) (pb : A → partial B) :
  bind (ret a) pb ≈ pb a.
Proof.
  split.
  - cbn. firstorder. constructor.
  - cbn. intros [i pu] pv. cbn.
    apply unique_value.
Qed.

Lemma bind_ret {A} (pa : partial A) :
  bind pa ret ≈ pa.
Proof.
  split.
  - cbn. firstorder.
  - cbn. intros [h i] h'. cbn.
    apply unique_value.
Qed.

Lemma bind_assoc {A B C} (pa : partial A) (pb : A → partial B) (pc : B → partial C) :
  bind (bind pa pb) pc ≈ bind pa (λ a, bind (pb a) pc).
Proof.
  split.
  - cbn. split.
    + intros [[ha hb] hc]. cbn in *.
      exists ha, hb. assumption.
    + intros [ha [hb hc]].
      unshelve eexists.
      * exists ha. assumption.
      * assumption.
  - cbn. intros [[ha hb] hc] [ha' [hb' hc']]. cbn in *.
    apply value_cong. f_equal.
    apply value_cong. f_equal.
    apply unique_value.
Qed.

(** Monad and hasdef *)

Lemma hasdef_ret A (a : A) :
  ret a ↦ a.
Proof.
  unshelve rewrite hasdef_equiv. 1: constructor.
  cbn. reflexivity.
Qed.

Lemma hasdef_bind A B a f v w :
  a ↦ w →
  f w ↦ v →
  @bind A B a f ↦ v.
Proof.
  intros ha hf.
  unshelve rewrite hasdef_equiv.
  - cbn. destruct ha as [ha ea].
    exists ha. rewrite ea. apply hf.
  - cbn. destruct ha as [ha ea]. cbn.
    destruct hf as [hf ef].
    rewrite ea. apply ef.
Qed.

(** Partiality is easily witnessed by the undefined constant *)

#[refine]
Definition undefined {A} : partial A :=
  guarded False (λ h, False_rect _ h) _.
Proof.
  contradiction.
Defined.
