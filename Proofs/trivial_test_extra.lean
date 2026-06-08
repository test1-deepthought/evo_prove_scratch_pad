import Mathlib

/-- A theorem about 2 = 2 -/
theorem two_eq_two : (2 : ℕ) = 2 := by
  rfl

/-- Symmetry of equality on naturals -/
theorem eq_symm_nat (a b : ℕ) (h : a = b) : b = a := by
  exact h.symm