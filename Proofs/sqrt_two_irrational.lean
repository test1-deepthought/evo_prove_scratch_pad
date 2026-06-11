import Mathlib

theorem sqrt_two_irrational : ¬∃ (r : ℚ), r ^ 2 = 2 := by
  intro h
  rcases h with ⟨r, hr⟩
  have hred := r.reduced
  have hden_ne_zero : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_pos.ne.symm
  
  -- Step 1: From r^2 = 2 and Rat.num_div_den, derive (r.num : ℚ)^2 = 2 * (r.den : ℚ)^2
  have hq_eq : (r.num : ℚ) ^ 2 = 2 * ((r.den : ℚ) ^ 2) := by
    calc
      (r.num : ℚ) ^ 2 = (((r.num : ℚ) / (r.den : ℚ)) * (r.den : ℚ)) ^ 2 := by
        field_simp [hden_ne_zero]
      _ = (r * (r.den : ℚ)) ^ 2 := by rw [Rat.num_div_den r]
      _ = r ^ 2 * ((r.den : ℚ) ^ 2) := by ring
      _ = 2 * ((r.den : ℚ) ^ 2) := by rw [hr]
  
  -- Step 2: Convert from ℚ to ℤ
  have hz_eq : (r.num : ℤ) ^ 2 = 2 * ((r.den : ℕ) : ℤ) ^ 2 := by
    apply (Int.cast_inj (α := ℚ)).mp
    push_cast
    simpa using hq_eq
  
  -- Step 3: Since a^2 = 2*b^2, we have 2 ∣ a (in ℤ)
  have ha_dvd : (2 : ℤ) ∣ (r.num : ℤ) := by
    have ha_sq_even : Even ((r.num : ℤ) ^ 2) := by
      rw [hz_eq]
      refine ⟨((r.den : ℕ) : ℤ) ^ 2, ?_⟩
      ring
    have ha_even : Even (r.num : ℤ) :=
      ((Int.even_pow (m := r.num) (n := 2)).mp ha_sq_even).left
    rw [← even_iff_two_dvd]
    exact ha_even
  
  -- Step 4: From a = 2*k, deduce 2 ∣ b (in ℤ)
  have hb_dvd : (2 : ℤ) ∣ ((r.den : ℕ) : ℤ) := by
    rcases ha_dvd with ⟨k, hk⟩
    have hb_sq_eq : ((r.den : ℕ) : ℤ) ^ 2 = 2 * k ^ 2 := by
      rw [hk] at hz_eq
      nlinarith
    have hb_sq_even : Even (((r.den : ℕ) : ℤ) ^ 2) := by
      rw [hb_sq_eq]
      refine ⟨k ^ 2, ?_⟩
      ring
    have hb_even : Even ((r.den : ℕ) : ℤ) :=
      ((Int.even_pow (m := ((r.den : ℕ) : ℤ)) (n := 2)).mp hb_sq_even).left
    rw [← even_iff_two_dvd]
    exact hb_even
  
  -- Step 5: Transfer to ℕ and contradict coprimality
  have ha_nat_dvd : (2 : ℕ) ∣ r.num.natAbs := by
    have h : (2 : ℤ) ∣ (r.num.natAbs : ℤ) :=
      (Int.dvd_natAbs (a := (2 : ℤ)) (b := r.num)).mpr ha_dvd
    exact (Int.ofNat_dvd.mp h)
  
  have hb_nat_dvd : (2 : ℕ) ∣ r.den := by
    have h : (2 : ℤ) ∣ (r.den : ℤ) := hb_dvd
    exact (Int.ofNat_dvd.mp h)
  
  have hgcd_eq_one : (r.num.natAbs).gcd r.den = 1 := by
    rw [← Nat.coprime_iff_gcd_eq_one]
    exact hred
  
  have h2_dvd_gcd : (2 : ℕ) ∣ (r.num.natAbs).gcd r.den :=
    Nat.dvd_gcd ha_nat_dvd hb_nat_dvd
  
  rw [hgcd_eq_one] at h2_dvd_gcd
  have h2_not_dvd_one : ¬ (2 : ℕ) ∣ 1 := by
    norm_num
  exact h2_not_dvd_one h2_dvd_gcd
