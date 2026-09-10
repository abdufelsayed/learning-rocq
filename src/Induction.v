From LF Require Export Basics.

(* Proof by Induction *)

Theorem add_0_r_firsttry:
  forall n:nat, n + 0 = n.
Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

Theorem add_0_r_secondtry:
  forall n:nat, n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

Theorem add_0_r:
  forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n:
  forall n, minus n n = 0.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Exercise: 2 stars, standard, especially useful (basic_induction) *)
Theorem mul_0_r:
  forall (n : nat), n * 0 = 0.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_Sm:
  forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_comm:
  forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n.
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc:
  forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Exercise: 2 stars, standard (double_plus) *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus:
  forall n, double n = n + n.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

(* Exercise: 2 stars, standard (eqb_refl) *)

Theorem eqb_refl:
  forall n : nat, (n =? n) = true.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Exercise: 2 stars, standard, optional (even_S) *)

Theorem even_S:
  forall n : nat, even (S n) = negb (even n).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - rewrite IHn. simpl. rewrite negb_involutive. reflexivity.
Qed.
