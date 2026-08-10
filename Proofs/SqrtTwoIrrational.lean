import Mathlib

open Real

namespace SqrtTwoProof

theorem irrational_sqrt_two : Irrational (Real.sqrt 2) := by
  rintro ⟨⟨p, q, hq, hcop⟩, h⟩
  have hq_ne_zero : (q : ℚ) ≠ 0 := by
    intro hzero
    apply hq
    exact_mod_cast hzero
  have h_sq_eq : ((p : ℚ) / (q : ℚ)) ^ 2 = (2 : ℚ) := by
    have h_real_sq : (((p : ℚ) / (q : ℚ) : ℚ) : ℝ) ^ 2 = ((Real.sqrt 2) ^ 2 : ℝ) := by
      simpa [h] using rfl
    have h_sqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show 0 ≤ 2 by norm_num)
    have h_two_real : (((p : ℚ) / (q : ℚ)) ^ 2 : ℝ) = (2 : ℝ) := by
      simpa [h_sqrt_sq] using h_real_sq
    exact_mod_cast h_two_real
  have h_p_sq : (p : ℚ) ^ 2 = 2 * (q : ℚ) ^ 2 := by
    field_simp [hq_ne_zero] at h_sq_eq
    exact h_sq_eq
  have h_p_sq_int : (p : ℤ) ^ 2 = 2 * (q : ℤ) ^ 2 := by
    exact_mod_cast h_p_sq
  have hp_even : 2 ∣ (p : ℤ) := by
    have h_two_dvd_p_sq : 2 ∣ (p : ℤ) ^ 2 := by
      rw [h_p_sq_int]
      exact ⟨(q : ℤ) ^ 2, by ring⟩
    have h_prime : Nat.Prime 2 := by norm_num [Nat.prime_def_sqrt]
    exact Prime.dvd_of_dvd_pow (Nat.prime_iff_prime_int.mp h_prime) h_two_dvd_p_sq
  obtain ⟨k, hk⟩ := hp_even
  have hq_even : 2 ∣ (q : ℤ) := by
    have h_q_sq_even : 2 ∣ (q : ℤ) ^ 2 := by
      rw [h_p_sq_int, hk] at h_p_sq_int
      have htemp : (2 * k) ^ 2 = 2 * (q : ℤ) ^ 2 := h_p_sq_int
      rw [mul_pow] at htemp
      ring_nf at htemp
      have : 2 * (k ^ 2) = (q : ℤ) ^ 2 := by
        nlinarith
      rw [this]
      exact ⟨k ^ 2, by ring⟩
    have h_prime : Nat.Prime 2 := by norm_num [Nat.prime_def_sqrt]
    exact Prime.dvd_of_dvd_pow (Nat.prime_iff_prime_int.mp h_prime) h_q_sq_even
  have h_common : 2 ∣ (Nat.gcd (Int.natAbs p) (Int.natAbs q)) := by
    apply Nat.dvd_gcd
    · rw [← Int.coe_nat_dvd]
      simpa using hp_even
    · rw [← Int.coe_nat_dvd]
      simpa using hq_even
  have h_cop : Nat.Coprime (Int.natAbs p) (Int.natAbs q) := hcop
  have h_gcd_one : Nat.gcd (Int.natAbs p) (Int.natAbs q) = 1 :=
    Nat.Coprime.gcd_eq_one h_cop
  rw [h_gcd_one] at h_common
  have : ¬ 2 ∣ (1 : ℕ) := by norm_num
  exact this h_common

end SqrtTwoProof