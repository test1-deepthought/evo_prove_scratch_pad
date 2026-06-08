import Mathlib

open Nat

theorem add_comm_test (a b : ℕ) : a + b = b + a := by
  omega

theorem add_zero_test (a : ℕ) : a + 0 = a := by
  omega

theorem zero_add_test (a : ℕ) : 0 + a = a := by
  omega
