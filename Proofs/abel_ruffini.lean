import Mathlib
open Polynomial
open IntermediateField
open Ideal

set_option maxHeartbeats 800000

/-!
# Abel-Ruffini Theorem

For each positive n, every complex root of every degree-n rational polynomial lies in
solvableByRad ℚ ℂ iff n ≤ 4.
-/

namespace AbelRuffini

-- ======================================================================
-- PART 1: The fundamental lemma about solvableByRad
-- ======================================================================

/-- If a ∈ solvableByRad ℚ ℂ and n ≠ 0, then any nth root of a is also in solvableByRad ℚ ℂ. -/
lemma rad_mem_sq (a : ℂ) (ha : a ∈ solvableByRad ℚ ℂ) (r : ℂ) (hr : r ^ 2 = a) : r ∈ solvableByRad ℚ ℂ := by
  have h_sq_mem : r ^ 2 ∈ solvableByRad ℚ ℂ := by rw [hr]; exact ha
  have h2_ne_zero : (2 : ℕ) ≠ 0 := by norm_num
  exact solvableByRad.rad_mem h2_ne_zero h_sq_mem

/-- If a ∈ solvableByRad ℚ ℂ and n ≠ 0, then any nth root of a is also in solvableByRad ℚ ℂ. -/
lemma rad_mem_cu (a : ℂ) (ha : a ∈ solvableByRad ℚ ℂ) (r : ℂ) (hr : r ^ 3 = a) : r ∈ solvableByRad ℚ ℂ := by
  have h_cu_mem : r ^ 3 ∈ solvableByRad ℚ ℂ := by rw [hr]; exact ha
  have h3_ne_zero : (3 : ℕ) ≠ 0 := by norm_num
  exact solvableByRad.rad_mem h3_ne_zero h_cu_mem

-- ======================================================================
-- PART 2: The forward direction (n > 4)
-- ======================================================================

noncomputable def fZ : ℤ[X] := X ^ 5 - C (4 : ℤ) * X + C (2 : ℤ)
noncomputable def fQ : ℚ[X] := fZ.map (Int.castRingHom ℚ)

lemma nd_fZ : fZ.natDegree = 5 := by
  unfold fZ
  have h_sub : (C (4 : ℤ) * X).natDegree < (X ^ 5 : ℤ[X]).natDegree := by
    have h1 : (C (4 : ℤ) * X).natDegree = 1 := by
      apply natDegree_C_mul_X (4 : ℤ); norm_num
    have h5 : (X ^ 5 : ℤ[X]).natDegree = 5 := by simp
    omega
  have h_sub_res : (X ^ 5 - C (4 : ℤ) * X).natDegree = (X ^ 5 : ℤ[X]).natDegree :=
    natDegree_sub_eq_left_of_natDegree_lt h_sub
  have h_add : (C (2 : ℤ) : ℤ[X]).natDegree < (X ^ 5 - C (4 : ℤ) * X).natDegree := by
    rw [h_sub_res]
    simp
  calc
    (X ^ 5 - C (4 : ℤ) * X + C (2 : ℤ)).natDegree = (X ^ 5 - C (4 : ℤ) * X).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt h_add
    _ = (X ^ 5 : ℤ[X]).natDegree := h_sub_res
    _ = 5 := by simp

lemma lc_fZ : fZ.leadingCoeff = (1 : ℤ) := by
  unfold fZ
  rw [Polynomial.leadingCoeff, nd_fZ]
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X]

lemma monic_fZ : fZ.Monic := by
  rw [Polynomial.Monic, lc_fZ]

lemma fZ_ne_zero : fZ ≠ 0 := monic_fZ.ne_zero

lemma deg_fZ : degree (fZ : ℤ[X]) = (5 : ℕ) := by
  rw [degree_eq_natDegree fZ_ne_zero, nd_fZ]

lemma primitive_fZ : fZ.IsPrimitive := Monic.isPrimitive monic_fZ

lemma irreducible_fZ : Irreducible fZ := by
  apply irreducible_of_eisenstein_criterion (P := Ideal.span {(2 : ℤ)}) (hu := primitive_fZ)
  · have h2_ne_zero : (2 : ℤ) ≠ 0 := by norm_num
    rw [Ideal.span_singleton_prime h2_ne_zero]
    exact Nat.prime_iff_prime_int.mp Nat.prime_two
  · rw [lc_fZ, Ideal.mem_span_singleton]
    norm_num
  · intro n hn
    rw [Ideal.mem_span_singleton]
    rw [deg_fZ] at hn
    have hn' : (n : ℕ) < 5 := WithBot.coe_lt_coe.mp hn
    unfold fZ
    interval_cases n
    · simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X]
    · simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X]
    · simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X]
    · simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X]
    · simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X]
  · rw [deg_fZ]
    norm_num
  · have hcoeff0 : coeff fZ 0 = (2 : ℤ) := by
      unfold fZ; simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X]
    rw [hcoeff0, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num

theorem irreducible_fQ : Irreducible fQ :=
  (IsPrimitive.Int.irreducible_iff_irreducible_map_cast primitive_fZ).mp irreducible_fZ

noncomputable instance splits_ℚ_ℂ (p : ℚ[X]) : Fact ((p.map (algebraMap ℚ ℂ)).Splits) :=
  ⟨IsAlgClosed.splits _⟩

lemma natDegree_fQ : fQ.natDegree = 5 := by
  rw [← nd_fZ, Polynomial.natDegree_map]

lemma prime_natDegree_fQ : Nat.Prime fQ.natDegree := by
  rw [natDegree_fQ]
  exact Nat.prime_five

-- Placeholder: we need to prove the real root count
-- This requires analysis (derivative test, IVT)
lemma card_real_roots_fQ : Fintype.card (fQ.rootSet ℝ : Set ℝ) = 3 := by
  sorry

lemma root_condition : Fintype.card (fQ.rootSet ℂ : Set ℂ) = Fintype.card (fQ.rootSet ℝ : Set ℝ) + 2 := by
  sorry

lemma gal_bijective : Function.Bijective (Gal.galActionHom fQ ℂ) :=
  Gal.galActionHom_bijective_of_prime_degree irreducible_fQ prime_natDegree_fQ root_condition

theorem not_solvable_by_rad (x : ℂ) (hx : aeval x fQ = 0) : x ∉ solvableByRad ℚ ℂ := by
  intro hx_sol
  have h_sol_gal : IsSolvable fQ.Gal :=
    isSolvable_gal_of_irreducible hx_sol irreducible_fQ hx
  have h_non_sol_gal : ¬IsSolvable fQ.Gal := by
    -- fQ.Gal ≃ S5 via gal_bijective, and S5 is not solvable
    have h_card : Fintype.card (fQ.rootSet ℂ) = 5 := sorry
    have h_perm : ¬IsSolvable (Equiv.Perm (fQ.rootSet ℂ)) :=
      Equiv.Perm.not_solvable _ (by
        have : Fintype.card (fQ.rootSet ℂ) = 5 := h_card
        have h_card' : 5 ≤ Cardinal.mk (fQ.rootSet ℂ) := by
          simpa [this] using show (5 : Cardinal) ≤ (5 : Cardinal) from le_rfl
        exact h_card')
    sorry
  exact h_non_sol_gal h_sol_gal

theorem exists_not_solvable_of_deg_ge_5 (n : ℕ) (hn : 5 ≤ n) :
    ∃ p : ℚ[X], p.natDegree = n ∧ ∃ x : ℂ, aeval x p = 0 ∧ x ∉ solvableByRad ℚ ℂ := by
  sorry

-- ======================================================================
-- PART 3: The reverse direction (n ≤ 4)
-- ======================================================================

theorem deg1_all_roots_solvable (p : ℚ[X]) (hp : p.natDegree = 1) (x : ℂ) (hx : aeval x p = 0) :
    x ∈ solvableByRad ℚ ℂ := by
  sorry

theorem deg2_all_roots_solvable (p : ℚ[X]) (hp : p.natDegree = 2) (x : ℂ) (hx : aeval x p = 0) :
    x ∈ solvableByRad ℚ ℂ := by
  sorry

theorem deg3_all_roots_solvable (p : ℚ[X]) (hp : p.natDegree = 3) (x : ℂ) (hx : aeval x p = 0) :
    x ∈ solvableByRad ℚ ℂ := by
  sorry

theorem deg4_all_roots_solvable (p : ℚ[X]) (hp : p.natDegree = 4) (x : ℂ) (hx : aeval x p = 0) :
    x ∈ solvableByRad ℚ ℂ := by
  sorry

-- ======================================================================
-- PART 4: The main theorem
-- ======================================================================

theorem abel_ruffini (n : ℕ) (_hn : 1 ≤ n) :
    (∀ p : ℚ[X], p.natDegree = n → ∀ x : ℂ, aeval x p = 0 → x ∈ solvableByRad ℚ ℂ) ↔ n ≤ 4 := by
  constructor
  · intro h
    by_contra! h_not
    have hn5 : 5 ≤ n := by omega
    rcases exists_not_solvable_of_deg_ge_5 n hn5 with ⟨p, hp, x, hx, hx_not⟩
    apply hx_not
    exact h p hp x hx
  · intro h
    rcases n with (rfl|rfl|rfl|rfl|m)
    · intro p hp x hx; exact deg1_all_roots_solvable p hp x hx
    · intro p hp x hx; exact deg2_all_roots_solvable p hp x hx
    · intro p hp x hx; exact deg3_all_roots_solvable p hp x hx
    · intro p hp x hx; exact deg4_all_roots_solvable p hp x hx
    · exfalso; omega

end AbelRuffini