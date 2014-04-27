(* boolean implementation and theorems.*)

(* A value of type bool is one of a finite set of elements: either true or false.*)
Inductive bool : Type :=
  | true : bool
  | false : bool.

(* NOTE: functions here are named as <function>b; the b is used to indicate
    that it is a boolean function.*)

(* negb defines the negation of a boolean value.*)
Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Example test_negb_true: (negb true) = false.
Proof. simpl. reflexivity. Qed.
Example test_negb_false: (negb false) = true.
Proof. simpl. reflexivity. Qed.

(*
Boolean "and".

Given two boolean values, a and b, andb returns true if both are true
or false otherwise.

Theorem:
  If a is true, the result of andb depends on the value of a; returning the
  value of b means that if b is true, andb returns true.

  Otherwise, if a is false, there is no way for andb to return true.
*)  
Definition andb (a:bool) (b:bool) : bool :=
  match a with
    | true => b
    | false => false
  end.

Example test_andb_ff: (andb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb_ft: (andb false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb_tf: (andb true false) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb_tt: (andb true true) = true.
Proof. simpl. reflexivity. Qed.

(*
Boolean "or".

Given two boolean values, a and b, orb returns true if either value is true
or false otherwise.

Theorem:
  If a is true, then orb is true and no further evaluation needs to be done.

  Otherwise, if a is false, the value of the or is dependent on b: if b is
  false, the outcome is false as this implies both a and b are false. Otherwise,
  the outcome is true.
*)  

Definition orb (a:bool) (b:bool) : bool :=
  match a with
    | false => b
    | true => true
  end.

Example test_orb_ff: (orb false false) = false.
Proof. reflexivity. Qed.
Example test_orb_ft: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb_tf: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb_tt: (orb true true) = true.
Proof. reflexivity. Qed.

(*
Exercise: 1 star (nandb)
Complete the definition of the following function, then make sure that the
Example assertions below can each be verified by Coq.
 *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | false => true
    | true => negb b2
  end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

(*
Do the same for the andb3 function below. This function should return true
when all of its inputs are true, and false otherwise. 
 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (andb (andb b1 b2) b3).

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

(* proving the involution of the boolean negation *)
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  reflexivity. reflexivity.
Qed.

(*
Exercise: 2 stars (boolean functions)
Use the tactics you have learned so far to prove the following theorem about boolean
functions.
 *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite -> x.
  rewrite -> x.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

(*
Now state and prove a theorem negation_fn_applied_twice similar to the previous one
but where the second hypothesis says that the function f has the property that
f x = negb x.
 *)

Theorem identity_fn_applied_twice_neg :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite -> x.
  rewrite -> x.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

(*
Exercise: 2 stars (andb_eq_orb)
Prove the following theorem. (You may want to first prove a subsidiary lemma or two.)
 *)

Theorem andb_eq_orb :
  forall(b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b. destruct c.
  reflexivity. simpl.
  intros H1. rewrite H1.
  reflexivity. simpl.
  destruct c. intros H2. rewrite H2. reflexivity. reflexivity.
Qed.
