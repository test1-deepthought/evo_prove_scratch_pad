import Mathlib

/-- Simple test: 1 + 1 = 2 -/
theorem one_plus_one_eq_two : (1 : ℕ) + 1 = 2 := by
  norm_num

/-- Another test: equality is symmetric -/
theorem eq_symm_test {α : Type} {a b : α} (h : a = b) : b = a := by
  exact h.symm

/-- Test: 0 < 1 -/
theorem zero_lt_one : (0 : ℕ) < 1 := by
  norm_num

/-- Extra theorem: 2 + 2 = 4 -/
theorem two_plus_two_eq_four : (2 : ℕ) + 2 = 4 := by
  norm_num