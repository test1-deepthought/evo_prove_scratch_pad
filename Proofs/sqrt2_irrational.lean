import Mathlib

open Real

set_option autoImplicit false

/-- Classic proof that √2 is irrational using a parity argument.
    Assume √2 = a/b in lowest terms. Then a² = 2b², so a is even.
    But then b is also even, contradicting coprimality. -/
theorem sqrt2_irrational : Irrational (Real.sqrt 2) := by
  -- Irrational x is defined as x ∉ Set.range (algebraMap ℚ ℝ)
  intro h_mem
  -- Get a rational q such that (q : ℝ) = Real.sqrt 2
  obtain ⟨q, hq⟩ := h_mem
  -- Square both sides
  have h_sq : (q : ℝ) ^ 2 = (2 : ℝ) := by
    rw [hq]
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  -- Write q = a / b where a, b are integers, b > 0, coprime
  have hq_eq_rat : (q : ℚ) = q := rfl
  -- Express q in lowest terms using Rat.num and Rat.den
  set a := q.num with ha
  set b := q.den with hb
  have hb_pos : 0 < b := q.pos
  have h_coprime : Nat.Coprime (Int.natAbs a) b := q.reduced
  have hq_val : (q : ℝ) = (a : ℝ) / (b : ℝ) := by
    exact mod_cast q.num_div_den
  -- From h_sq, we get (a/b)^2 = 2, so a^2 = 2 * b^2
  rw [hq_val] at h_sq
  field_simp at h_sq
  -- h_sq : (a : ℝ)^2 = 2 * (b : ℝ)^2
  -- Convert to ℤ: a^2 = 2 * b^2
  have h_sq_int : a ^ 2 = (2 : ℤ) * (b : ℤ) ^ 2 := by
    have := mod_cast h_sq
    -- This gives a^2 = 2 * b^2 in ℤ
    -- But we need to be careful about the types
    sorry
  -- Since 2 is prime in ℤ, and 2 ∣ a^2, we have 2 ∣ a
  have h2_prime : Nat.Prime 2 := by norm_num [Nat.prime_def_sqrt]
  have ha_even : (2 : ℤ) ∣ a := by
    -- Using the lemma that if prime p divides n^2, then p divides n
    have h_dvd_sq : (2 : ℤ) ∣ a ^ 2 := by
      rw [h_sq_int]
      exact ⟨(b : ℤ) ^ 2, by ring⟩
    exact Prime.dvd_of_dvd_pow (Nat.prime_iff_prime_int.mp h2_prime) h_dvd_sq
  -- Write a = 2k
  obtain ⟨k, hk⟩ := ha_even
  -- Substitute into a^2 = 2*b^2
  rw [hk] at h_sq_int
  -- (2k)^2 = 2*b^2 → 4k^2 = 2*b^2 → 2k^2 = b^2 → b^2 = 2k^2
  have hb_sq_eq : (b : ℤ) ^ 2 = (2 : ℤ) * k ^ 2 := by
    nlinarith
  -- So 2 ∣ b^2, hence 2 ∣ b
  have hb_even : (2 : ℤ) ∣ b := by
    have h_dvd_sq : (2 : ℤ) ∣ (b : ℤ) ^ 2 := by
      rw [hb_sq_eq]
      exact ⟨k ^ 2, by ring⟩
    exact Prime.dvd_of_dvd_pow (Nat.prime_iff_prime_int.mp h2_prime) h_dvd_sq
  -- Now both a and b are divisible by 2 in ℤ
  -- This means their absolute values share factor 2, contradicting coprimality
  have ha_nat : (2 : ℕ) ∣ Int.natAbs a := by
    -- Convert the ℤ divisibility to ℕ
    sorry
  have hb_nat : (2 : ℕ) ∣ b := by
    exact mod_cast hb_even
  -- This contradicts Nat.Coprime (Int.natAbs a) b
  have h_not_coprime : ¬ Nat.Coprime (Int.natAbs a) b := by
    refine Nat.not_coprime_of_dvd_of_dvd ?_ ha_nat hb_nat
    -- Need 1 < 2
    norm_num
  exact h_not_coprime h_coprime
