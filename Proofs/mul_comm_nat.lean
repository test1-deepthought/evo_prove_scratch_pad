import Mathlib

open Nat

theorem mul_comm_nat (a b : ℕ) : a * b = b * a := by
  exact Nat.mul_comm a b
