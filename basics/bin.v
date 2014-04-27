(*
Exercise: 3 stars (binary)
Consider a different, more efficient representation of natural numbers using a binary rather
than unary system. That is, instead of saying that each natural number is either zero or the
successor of a natural number, we can say that each binary number is either

    zero,
    twice a binary number, or
    one more than twice a binary number.

(a) First, write an inductive definition of the type bin corresponding to this description of
binary numbers.

(Hint: Recall that the definition of nat from class,
    Inductive nat : Type :=
      | O : nat
      | S : nat → nat.

says nothing about what O and S "mean." It just says "O is in the set called nat, and if n is
in the set then so is S n." The interpretation of O as zero and S as successor/plus one comes
from the way that we use nat values, by writing functions to do things with them, proving 
things about them, and so on. Your definition of bin should be correspondingly simple; it is
the functions you will write next that will give it mathematical meaning.)

(b) Next, write an increment function for binary numbers, and a function to convert binary
numbers to unary numbers.
(c) Write some unit tests for your increment and binary-to-unary functions. Notice that
incrementing a binary number and then converting it to unary should yield the same result as
first converting it to unary and then incrementing.

 *)
