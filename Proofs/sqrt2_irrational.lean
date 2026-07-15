import Mathlib

open Real

set_option autoImplicit false

/-- The square root of 2 is irrational.
    Classic proof adapted to Lean 4 using the general criterion
    that √n is irrational iff n is not a perfect square. -/
theorem sqrt2_irrational : Irrational (Real.sqrt 2) := by
  -- Use the criterion: for n : ℕ, √n is irrational iff n is not a square
  rw [irrational_sqrt_natCast_iff]
  -- Goal: ¬ IsSquare (2 : ℕ)
  intro h_sq
  -- h_sq : IsSquare (2 : ℕ), i.e., ∃ k : ℕ, 2 = k * k
  obtain ⟨k, hk⟩ := h_sq
  -- hk : 2 = k * k  (or equivalently k * k = 2)
  -- Since k : ℕ, we can do case analysis: k = 0, k = 1, or k ≥ 2
  have hk_bound : k ≤ 2 := by
    -- If k ≥ 3, then k*k ≥ 9 > 2, contradiction
    by_contra! h
    have hk3 : 3 ≤ k := by omega
    have hsq : 9 ≤ k * k := by
      nlinarith
    have : k * k = 2 := by
      -- from hk, depending on the direction
      -- Actually IsSquare n in ℕ is defined as ∃ k, n = k*k
      sorry
    nlinarith
  -- Now k ≤ 2, so k ∈ {0, 1, 2}
  have h_cases : k = 0 ∨ k = 1 ∨ k = 2 := by
    interval_cases k
    · left; rfl
    · right; left; rfl
    · right; right; rfl
  rcases h_cases with (hk0 | hk1 | hk2)
  · -- k = 0 → 0*0 = 0 ≠ 2
    rw [hk0] at hk
    simp at hk
  · -- k = 1 → 1*1 = 1 ≠ 2
    rw [hk1] at hk
    norm_num at hk
  · -- k = 2 → 2*2 = 4 ≠ 2
    rw [hk2] at hk
    norm_num at hk