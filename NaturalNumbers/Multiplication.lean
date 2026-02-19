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

lemma mul_succ (a b : ℕ) : a * Nat.succ b = a * b + a  := by 
  exact Nat.mul_succ a b

#check Nat.zero_add

theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  induction m with
  | zero => rw [mul_zero]
  | succ a h₁ => rw [mul_succ]; rw[h₁]

theorem succ_mul (a b : ℕ) : Nat.succ a * b = a * b + b := by
  induction b with
  | zero => rw [mul_zero]; rw[mul_zero]; rfl
  | succ a h₁ => rw [mul_succ]; rw[h₁]
--rw [succ_mul a]  
--rw [Nat.add_one_mul]

end NaturalNumbersGame
