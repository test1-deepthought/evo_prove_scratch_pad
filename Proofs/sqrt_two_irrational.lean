import Mathlib

theorem sqrt_two_irrational : ¬ ∃ (a b : ℕ), b ≠ 0 ∧ a ^ 2 = 2 * b ^ 2 := by
  intro h
  rcases h with ⟨a, b, hb, h⟩
  have ha_pos : a > 0 := by
    by_contra! ha0
    have : a = 0 := Nat.eq_zero_of_not_pos ha0
    subst this
    have hzero : 0 = 2 * b ^ 2 := by simpa using h
    have hb0 : b = 0 := by
      nlinarith
    exact hb hb0
  have h2prime : Nat.Prime 2 := Nat.prime_two
  refine Nat.strong_induction_on a ?_ h hb ha_pos
  intro a ih h hb ha_pos
  have h2_dvd_a_sq : 2 ∣ a ^ 2 := by
    rw [h]
    exact ⟨b ^ 2, by ring⟩
  have h2_dvd_a : 2 ∣ a := h2prime.dvd_of_dvd_pow h2_dvd_a_sq
  rcases h2_dvd_a with ⟨k, hk⟩
  have hb_sq_eq : b ^ 2 = 2 * k ^ 2 := by
    nlinarith
  have h2_dvd_b_sq : 2 ∣ b ^ 2 := by
    rw [hb_sq_eq]
    exact ⟨k ^ 2, by ring⟩
  have h2_dvd_b : 2 ∣ b := h2prime.dvd_of_dvd_pow h2_dvd_b_sq
  rcases h2_dvd_b with ⟨m, hm⟩
  have hk_sq_eq : k ^ 2 = 2 * m ^ 2 := by
    nlinarith
  have hm_pos : m ≠ 0 := by
    intro hmz
    have : b = 0 := by
      calc
        b = 2 * m := hm
        _ = 2 * 0 := by rw [hmz]
        _ = 0 := by ring
    exact hb this
  have hk_lt_a : k < a := by
    have ha_eq_2k : a = 2 * k := hk
    omega
  exact ih k hk_lt_a hk_sq_eq hm_pos