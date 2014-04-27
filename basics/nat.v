(*
   nat defines theorems about natural numbers; these are the integers >= 0.
 *)
Module playground1.

(*
   Natural numbers are represented as either O, which is equivalent to 0,
   or S n. For example, 1 is represented as S O; 2 is represented as S (S O).
 *)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(* pred returns the predecessor of n; that is, n-1. *)
Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Check (S (S (S (S O)))).

End playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
Example test_mult: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
Example test_minus: (minus 5 3) = 2.
Proof. reflexivity. Qed.
End Playground2.

(*
Exercise: 1 star (factorial)
Recall the standard factorial function:

    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)

Translate this into Coq.
 *)
Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => O
    | S O => S O
    | S n' => mult n (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y)
                               (at level 50, left associativity)
                               : nat_scope.

Notation "x - y" := (minus x y)
                               (at level 50, left associativity)
                               : nat_scope.

(*
Notation "x * y" := (mult x y)
                               (at level 30, left associativity)
                               : nat_scope.
 *)
Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
    | O => match m with
                 | O => true
                 | S m' => false
               end
    | S n' => match m with
                    | O => false
                    | S m' => beq_nat n' m'
                  end
    end.
Example test_beq_nat1: (beq_nat 0 0) = true.
Proof. reflexivity. Qed.
Example test_beq_nat2: (beq_nat 0 1) = false.
Proof. reflexivity. Qed.
Example test_beq_nat3: (beq_nat 1 0) = false.
Proof. reflexivity. Qed.
Example test_beq_nat4: (beq_nat 1 1) = true.
Proof. reflexivity. Qed.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

(*
Exercise: 2 stars (blt_nat)
The blt_nat function tests natural numbers for less-than, yielding a
boolean. Instead of making up a new Fixpoint for this one, define it in
terms of a previously defined function.

Note: If you have trouble with the simpl tactic, try using compute, which
is like simpl on steroids. However, there is a simple, elegant solution for
which simpl suffices. 

Given n and m, two natural numbers, return true if n < m and false otherwise.

Theorem:
  If m is zero, which is the lowest value that a natural number can be, n
  cannot possibly be less than m. Return false.

  Otherwise, subtract n from m. If n is equal to m, the result will be zero;
  if n is greater than m, the result would be negative but results in zero
  (the lowest possible value). Therefore, if (m - n) == O, n must be greater
  than or equal to n, and therefore is not less than m. Otherwise, n is
  less than m.
 *)
Definition blt_nat (n m : nat) : bool :=
  match m with
    | O => false
    | S m' => match (m - n) with
                     | O => false
                     | _ => true
                    end
    end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Proof by simplification. *)
Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.
Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

(* Proof by rewriting. *)
Theorem plus_id_example: forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.     (* Move both quantifiers into the context. *)
  intros H.        (* Move hypothesis into context. *)
  rewrite -> H. (* Rewrite the goal using the hypothesis. *)
  reflexivity. Qed.

Theorem two_plus_two_is_five: 2 + 2 = 5.
Proof. Admitted.

(*
Exercise: 1 star (plus_id_exercise)
Remove "Admitted." and fill in the proof.
 *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity. Qed.

(*
Exercise: 2 stars (mult_S_1)
 *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros m n.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

(* Proof by case analysis. *)
Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity. Qed.

(* proving the involution of the boolean negation *)
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  reflexivity. reflexivity.
Qed.

(*
Exercise: 1 star (zero_nbeq_plus_1)
 *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* (* FILL IN HERE *) Admitted. *)
  intros n. destruct n as [|n'].
  reflexivity. reflexivity.
Qed.

