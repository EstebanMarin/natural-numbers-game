/-
# Multiplication World

In this world, we'll prove fundamental properties of multiplication
on natural numbers.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import NaturalNumbers.Addition

namespace NaturalNumbersGame

/-
## Level 1: Multiplication by zero

Prove that multiplying by zero gives zero.
-/
lemma one_eq_succ_zero: 1 = Nat.succ 0 := by
  rfl
lemma mul_one (m : ℕ) : m * 1 = m := by 
  exact Nat.mul_one m

theorem fmul_zero (n : ℕ) : n * 1 = n := by
  rw [one_eq_succ_zero];
  rw [Nat.mul_one];
  

/-
## Level 2: Zero multiplication

Prove that zero times anything is zero.
-/

theorem zero_mulf (n : ℕ) : 0 * n = 0 := by
  sorry

/-
## Level 3: Multiplication by one

Prove that multiplying by one gives the same number.
-/

theorem mul_one (n : ℕ) : n * 1 = n := by
  sorry

/-
## Level 4: One multiplication

Prove that one times anything gives that number.
-/

theorem one_mul (n : ℕ) : 1 * n = n := by
  sorry

/-
## Level 5: Multiplication with successor

Prove that `n * succ m = n * m + n`.
-/

theorem mul_succ (n m : ℕ) : n * Nat.succ m = n * m + n := by
  sorry

/-
## Level 6: Commutativity of multiplication

Prove that multiplication is commutative.
-/

theorem mul_comm (n m : ℕ) : n * m = m * n := by
  sorry

/-
## Level 7: Distributivity

Prove that multiplication distributes over addition.
-/

theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  sorry

/-
## Level 8: Associativity of multiplication

Prove that multiplication is associative.
-/

theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  sorry

/-
## Challenge: Prove from scratch using induction
-/

theorem mul_comm_induction (n m : ℕ) : n * m = m * n := by
  induction m with
  | zero =>
    sorry
  | succ m ih =>
    sorry

end NaturalNumbersGame
