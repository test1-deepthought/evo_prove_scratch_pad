import Mathlib

/-- A trivial test theorem: 1 + 1 = 2 -/
theorem one_plus_one_eq_two : 1 + 1 = 2 := by
  norm_num

/-- Another trivial test: 0 = 0 -/
theorem zero_eq_zero : (0 : ℕ) = 0 := by
  rfl