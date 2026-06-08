import Mathlib

open Nat

/-- Addition of natural numbers is commutative. -/
theorem add_comm_nat (a b : ℕ) : a + b = b + a := by
  exact Nat.add_comm a b

/-- A simple test that 2+3 = 3+2 using the theorem. -/
 example : 2 + 3 = 3 + 2 := by
  exact add_comm_nat 2 3