(** * Data and Functions *)

(** ** Enumerated Types *)

(** *** Days of the Week *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_weekday friday).

Example test_next_weekday:
  (next_weekday (next_weekday saturday) = tuesday).

Proof. simpl. reflexivity. Qed.

(** ** Booleans *)
From Stdlib Require Export String.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) :=
  match b1 with
  | true  => b2
  | false => false
  end.

Definition orb (b1 b2 : bool) :=
  match b1 with
  | true  => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b : bool) : bool :=
  if b then false
  else true.

Definition andb' (b1 : bool) (b2 : bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1 : bool) (b2 : bool) : bool :=
  if b1 then true
  else b2.

(** Exercise: nandb (1 star, standard)

    Define boolean NAND: return false only when both inputs are true.
    Verify the four tests below. *)

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true  => negb b2
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(** Exercise: andb3 (1 star, standard)

    Define conjunction of three booleans and verify the four tests below. *)

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  match b1 with
  | true => b2 && b3
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(** ** Types *)

Check true : bool.
Check (negb true).
Check negb.

(** ** New Types from Old *)

Inductive rgb : Type :=
  | red
  | blue
  | green.

Inductive color : Type :=
  | white
  | black
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | primary p => false
  | _         => true
  end.

Definition is_red (c : color) : bool :=
  match c with
  | primary red => true
  | _           => false
  end.

(** ** Numbers *)

Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).

  Definition pred (n : nat) : nat :=
    match n with
    | O    => O
    | S n' => n'
    end.
End NatPlayground.

Check S (S (S (S O))).

Definition minus_two (n : nat) : nat :=
  match n with
  | O        => O
  | S O      => O
  | S (S n') => n'
  end.

Compute (minus_two 4).

Fixpoint even (n : nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
  negb (even n).

Example test_odd2: odd 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_odd4: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O    => m
  | S n' => S (plus n' m)
  end.

Compute (plus 4 3).

Fixpoint mult (n : nat) (m : nat) : nat :=
  match n with
  | O    => O
  | S n' => plus m (mult n' m)
  end.

Compute (mult 3 4).

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

(** Exercise: factorial (1 star, standard)

    Define factorial recursively: factorial 0 is 1, and factorial (S n)
    is (S n) * factorial n. Replace the admitted definition with := followed
    by your implementation, then prove the two tests below. *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult (S n') (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n : nat) (m : nat) : nat :=
  match n, m with
  | O, _       => O
  | S _, O     => n
  | S n', S m' => minus n' m'
  end.

Example test_minus1: (minus 3 2) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n : nat) (m : nat) : bool :=
  match n, m with
  | O, O       => true
  | S _, O     => false
  | O, S _     => false
  | S n', S m' => eqb n' m'
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Example test_eqb1: 1 =? 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_eqb2: 2 =? 1 = false.
Proof. simpl. reflexivity. Qed.

Example test_eqb3: 1 =? 3 = false.
Proof. simpl. reflexivity. Qed.

Fixpoint leb (n : nat) (m : nat) : bool :=
  match n, m with
  | O, O       => true
  | S _, O     => false
  | O, S _     => true
  | S n', S m' => leb n' m'
  end.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb1: 1 <=? 2 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: 1 <=? 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3: 4 <=? 2 = false.
Proof. simpl. reflexivity. Qed.

(** Exercise: ltb (1 star, standard)

    Define a boolean test for strict less-than and verify the three tests
    below. Try expressing it using an existing function. *)

Fixpoint ltb (n m : nat) : bool :=
  match n, m with
  | O, O       => false
  | S _, O     => false
  | O, S _     => true
  | S n', S m' => ltb n' m'
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(** * Proof by Simplification *)

Theorem plus_0_n:
  forall (n : nat), 0 + n = n.
Proof.
  intros k. simpl. reflexivity.
Qed.

(** * Proof by Rewriting *)

Theorem plus_id_example:
  forall n m : nat, n = m -> n + n = m + m.
Proof.
  (* move both quantifiers into the context *)
  intros n m.
  (* move the hypothesis into the context *)
  intros H.
  (* rewrite the goal using the hypothesis *)
  rewrite <- H.
  reflexivity.
Qed.

(** Exercise: plus_id_exercise (1 star, standard)

    Use the two equality hypotheses to prove the equality of the sums. *)

Theorem plus_id_exercise:
  forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Check mult_n_O.

Check mult_n_Sm.

Theorem mult_n_0_m_0:
  forall n m : nat, (n * 0) + (m * 0) = 0.
Proof.
  intros n m.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

(** Exercise: mult_n_1 (1 star, standard)

    Prove multiplication by one on the right using mult_n_Sm and mult_n_O. *)

Theorem mult_n_1:
  forall p : nat, p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

(** * Proof by Case Analysis *)

Theorem plus_1_neq_0:
  forall n : nat, ((n + 1) =? 0) = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive:
  forall b : bool, negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_commutative:
  forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb3_exchange:
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + destruct d eqn:Ed.
      * reflexivity.
      * reflexivity.
    + destruct d eqn:Ed.
      * reflexivity.
      * reflexivity.
  - destruct c eqn:Ec.
    + destruct d eqn:Ed.
      * reflexivity.
      * reflexivity.
    + destruct d eqn:Ed.
      * reflexivity.
      * reflexivity.
Qed.

(* Exercise: 2 stars, standard (andb_true_elim2)

Prove the following claim, marking cases (and subcases) with bullets when you use destruct. *)

Theorem andb_true_elim2:
  forall b c : bool, andb b c = true -> c = true.
Proof.
  intros b c.
  intros H.
  destruct b eqn:Eb.
  simpl in H.
  - destruct c eqn:Ec.
    + reflexivity.
    + rewrite -> H. reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + simpl in H. rewrite -> H. reflexivity.
Qed.

Theorem plus_1_neq_0':
  forall n : nat, ((n + 1) =? 0) = false.
Proof.
  intros [| n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative':
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb3_exchange':
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros [] [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_nbeq_plus_1:
  forall n : nat, 0 =? (n + 1) = false.
Proof.
  intros [| n'].
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise: 2 stars, standard, optional (decreasing)

To get a concrete sense of this, find a way to write a sensible Fixpoint definition
(of a simple function on numbers, say) that does terminate on all inputs,
but that Rocq will reject because of this restriction. *)

(* Fixpoint fib (n : nat) : nat :=
  match n with
  | O    => O
  | S O  => S O
  | n'   =>  plus (fib (pred n)) (fib (pred (pred n)))
  end. *)

(* Exercise: 1 star, standard (identity_fn_applied_twice)

Use the tactics you have learned so far to prove the following theorem about boolean functions. *)

Theorem identity_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros IdH.
  intros IdAppH.
  intros b.
  rewrite -> IdAppH.
  rewrite -> IdAppH.
  reflexivity.
Qed.

(* Exercise: 1 star, standard (negation_fn_applied_twice)

Now state and prove a theorem negation_fn_applied_twice similar to the previous one
but where the hypothesis says that the function f has the property that f x = negb x. *)

Theorem negation_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros NegbH.
  intros NegbAppH.
  intros b.
  rewrite -> NegbAppH.
  rewrite -> NegbAppH.
  destruct b eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_negation_fn_applied_twice : option (nat * string) := None.

(* Exercise: 3 stars, standard, optional (andb_eq_orb) *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  intros H.
  destruct b eqn:Eb.
  simpl in H.
  - destruct c eqn:Ec.
    + reflexivity.
    + rewrite -> H. reflexivity.
  - destruct c eqn:Ec.
    + simpl in H. rewrite -> H. reflexivity.
    + reflexivity.
Qed.

(* Course Late Policies, Formalized *)

Module LateDays.
  Inductive letter : Type := A | B | C | D | F.
  Inductive modifier : Type := Plus | Natural | Minus.

  Inductive grade : Type := Grade (l:letter) (m:modifier).

  Inductive comparison : Type := Eq | Lt | Gt.

  Definition letter_comparison (l1 l2 : letter) : comparison :=
    match l1, l2 with
    | A, A               => Eq
    | A, _               => Gt
    | B, A               => Lt
    | B, B               => Eq
    | B, _               => Gt
    | C, (A | B)         => Lt
    | C, C               => Eq
    | C, _               => Gt
    | D, (A | B | C)     => Lt
    | D, D               => Eq
    | D, _               => Gt
    | F, (A | B | C | D) => Lt
    | F, F               => Eq
    end.

  (* Exercise: 1 star, standard (letter_comparison) *)
  Theorem letter_comparison_Eq :
    forall l, letter_comparison l l = Eq.
  Proof.
    intros l.
    destruct l eqn:E.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Definition modifier_comparison (m1 m2 : modifier) : comparison :=
    match m1, m2 with
    | Plus, Plus              => Eq
    | Plus, _                 => Gt
    | Natural, Plus           => Lt
    | Natural, Natural        => Eq
    | Natural, _              => Gt
    | Minus, (Plus | Natural) => Lt
    | Minus, Minus            => Eq
    end.

  (* Exercise: 2 stars, standard (grade_comparison) *)
  Definition grade_comparison (g1 g2 : grade) : comparison :=
    let '(Grade g1_letter g1_modifier) := g1  in
    let '(Grade g2_letter g2_modifier) := g2 in
    let letter_comparison_result := letter_comparison g1_letter g2_letter in
    let modifier_comparison_result := modifier_comparison g1_modifier g2_modifier in

    match letter_comparison_result, modifier_comparison_result with
    | Eq, Eq => Eq
    | Eq, Lt => Lt
    | Eq, Gt => Gt
    | Lt, _  => Lt
    | Gt, _  => Gt
    end.

  Example test_grade_comparison1 :
    (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
  Proof. simpl. reflexivity. Qed.

  Example test_grade_comparison2 :
    (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
  Proof. simpl. reflexivity. Qed.

  Example test_grade_comparison3 :
    (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
  Proof. simpl. reflexivity. Qed.

  Example test_grade_comparison4 :
    (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
  Proof. simpl. reflexivity. Qed.

  Definition lower_letter (l : letter) : letter :=
    match l with
    | A => B
    | B => C
    | C => D
    | D => F
    | F => F
    end.

  Theorem lower_letter_lowers:
    forall (l : letter), letter_comparison (lower_letter l) l = Lt.
  Proof.
    intros l.
    destruct l.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. (* We get stuck here. *)
  Abort.

  Theorem lower_letter_F_is_F:
    lower_letter F = F.
  Proof.
    simpl. reflexivity.
  Qed.

  (* Exercise: 2 stars, standard (lower_letter_lowers) *)
  Theorem lower_letter_lowers:
    forall (l : letter),
      letter_comparison F l = Lt ->
      letter_comparison (lower_letter l) l = Lt.
  Proof.
    intros l.
    intros H.
    destruct l.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - rewrite <- H. simpl. reflexivity.
  Qed.

  (* Exercise: 2 stars, standard (lower_grade) *)
  Definition lower_grade (g : grade) : grade :=
    match g with
    | Grade F Plus         => Grade F Natural
    | Grade F _      => Grade F Minus
    | Grade letter Plus    => Grade letter Natural
    | Grade letter Natural => Grade letter Minus
    | Grade letter Minus   => Grade (lower_letter letter) Plus
    end.

  Example lower_grade_A_Plus:
    lower_grade (Grade A Plus) = (Grade A Natural).
  Proof. simpl. reflexivity. Qed.

  Example lower_grade_A_Natural:
    lower_grade (Grade A Natural) = (Grade A Minus).
  Proof. simpl. reflexivity. Qed.

  Example lower_grade_A_Minus:
    lower_grade (Grade A Minus) = (Grade B Plus).
  Proof. simpl. reflexivity. Qed.

  Example lower_grade_B_Plus :
    lower_grade (Grade B Plus) = (Grade B Natural).
  Proof. simpl. reflexivity. Qed.

  Example lower_grade_F_Natural :
    lower_grade (Grade F Natural) = (Grade F Minus).
  Proof. simpl. reflexivity. Qed.

  Example lower_grade_twice :
    lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
  Proof. simpl. reflexivity. Qed.

  Example lower_grade_thrice :
    lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
  Proof. simpl. reflexivity. Qed.

  Theorem lower_grade_F_Minus:
    lower_grade (Grade F Minus) = (Grade F Minus).
  Proof. simpl. reflexivity. Qed.

  (* Exercise: 3 stars, standard (lower_grade_lowers) *)
  Theorem lower_grade_lowers :
    forall (g : grade),
      grade_comparison (Grade F Minus) g = Lt ->
      grade_comparison (lower_grade g) g = Lt.
  Proof.
    intros g.
    intros H.
    destruct g eqn:Eg.
    destruct l eqn:El.
    - destruct m eqn:Em.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct m eqn:Em.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct m eqn:Em.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct m eqn:Em.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct m eqn:Em.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + rewrite <- H. simpl. reflexivity.
    Qed.

  Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
    if late_days <? 9 then g
    else if late_days <? 17 then lower_grade g
    else if late_days <? 21 then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g)).

  Theorem apply_late_policy_unfold:
    forall (late_days : nat) (g : grade),
      (apply_late_policy late_days g)
      =
      if late_days <? 9 then g
      else if late_days <? 17 then lower_grade g
      else if late_days <? 21 then lower_grade (lower_grade g)
      else lower_grade (lower_grade (lower_grade g)).
  Proof.
    intros. reflexivity.
  Qed.

  (* Exercise: 2 stars, standard (no_penalty_for_mostly_on_time) *)
  Theorem no_penalty_for_mostly_on_time :
    forall (late_days : nat) (g : grade),
      (late_days <? 9 = true) ->
      apply_late_policy late_days g = g.
  Proof.
    intros.
    rewrite -> apply_late_policy_unfold.
    rewrite -> H.
    reflexivity.
  Qed.

  (* Exercise: 2 stars, standard (graded_lowered_once) *)
  Theorem grade_lowered_once :
    forall (late_days : nat) (g : grade),
      (late_days <? 9 = false) ->
      (late_days <? 17 = true) ->
      (apply_late_policy late_days g) = (lower_grade g).
  Proof.
    intros late_days g H1 H2.
    rewrite -> apply_late_policy_unfold.
    rewrite -> H1.
    rewrite -> H2.
    reflexivity.
  Qed.
End LateDays.

(* Binary Numerals *)

(* Exercise: 3 stars, standard (binary) *)
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z     => B1 Z
  | B0 b  => B1 b
  | B1 b  => B0 (incr b)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z    => O
  | B0 b => 2 * (bin_to_nat b)
  | B1 b => (2 * (bin_to_nat b)) + 1
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 :
  bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr6 :
  bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr7 : bin_to_nat (B0 (B0 (B0 (B1 Z)))) = 8.
Proof. simpl. reflexivity. Qed.
