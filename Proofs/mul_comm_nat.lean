import Mathlib

open Nat

/-- Multiplication of natural numbers is commutative. -/
theorem mul_comm_nat (a b : ℕ) : a * b = b * a := by
  exact Nat.mul_comm a b

/-- A simple test that 2*3 = 3*2 using the theorem. -/
 example : 2 * 3 = 3 * 2 := by
  exact mul_comm_nat 2 3