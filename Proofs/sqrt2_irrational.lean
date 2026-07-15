import Mathlib

open Real

set_option autoImplicit false

/-- The square root of 2 is irrational. -/
theorem sqrt2_irrational : Irrational (Real.sqrt 2) := by
  rw [irrational_sqrt_natCast_iff]
  norm_num
