import Mathlib

/-- A simple test theorem: for any natural number n, n + 0 = n. -/
theorem add_zero_test (n : ℕ) : n + 0 = n := by
  omega
