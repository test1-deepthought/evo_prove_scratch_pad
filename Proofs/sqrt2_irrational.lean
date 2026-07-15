import Mathlib

open Real

set_option autoImplicit false

namespace Sqrt2Irrational

/-- If an integer squared is even, then the integer is even. -/
lemma even_of_sq_even {n : ℤ} (h : 2 ∣ n ^ 2) : 2 ∣ n := by
  by_contra! h_not
  -- n is odd, so n = 2k + 1
  have h_odd : n % 2 = 1 := by
    have := Int.emod_add_ediv n 2
    have h_mod_lt : n % 2 < 2 := Int.emod_lt n (by norm_num : 0 < 2)
    have h_mod_ne_zero : n % 2 ≠ 0 := by
      intro hzero
      apply h_not
      exact (Int.dvd_mod_iff (by norm_num : (2 : ℤ) ∣ 2)).mp ?_
      -- Actually, n % 2 = 0 means 2 ∣ n
      sorry
    sorry
  sorry

/-- The square root of 2 is irrational. -/
theorem sqrt2_irrational : Irrational (Real.sqrt 2) := by
  -- Irrational x is defined as x ∉ Set.range (algebraMap ℚ ℝ)
  intro h
  obtain ⟨q, hq⟩ := h
  -- q : ℚ, hq : (q : ℝ) = Real.sqrt 2
  have h_sq_eq_two : (q : ℝ) ^ 2 = (2 : ℝ) := by
    rw [hq]
    exact Real.pow_sqrt_eq_abs 2
    -- Actually Real.sq_sqrt (show 0 ≤ 2 from by norm_num)
  have h_sq_eq_two' : (q : ℝ) ^ 2 = (2 : ℝ) := by
    rw [hq]
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  -- Since q is rational, q = a / b for some a, b : ℤ, b > 0, coprime
  let a := q.num
  let b := q.den
  have hq_eq : (q : ℝ) = (a : ℝ) / (b : ℝ) := by
    exact mod_cast Rat.num_div_den q
  have hb_pos : 0 < b := by
    exact mod_cast q.pos
  have h_coprime : Nat.Coprime (Int.natAbs a) b := by
    -- Rat.num_den_coprime
    have := q.reduced
    -- q.reduced : Nat.Coprime (Int.natAbs q.num) q.den
    -- Actually q.reduced gives coprime of |num| and den
    sorry
  sorry

end Sqrt2Irrational