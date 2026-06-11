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
-- PART 0: Basic lemmas about solvableByRad
-- ======================================================================

lemma rad_mem_sq (a : ℂ) (ha : a ∈ solvableByRad ℚ ℂ) (r : ℂ) (hr : r ^ 2 = a) : r ∈ solvableByRad ℚ ℂ := by
  have h_sq_mem : r ^ 2 ∈ solvableByRad ℚ ℂ := by rw [hr]; exact ha
  have h2_ne_zero : (2 : ℕ) ≠ 0 := by norm_num
  exact solvableByRad.rad_mem h2_ne_zero h_sq_mem

lemma rad_mem_cu (a : ℂ) (ha : a ∈ solvableByRad ℚ ℂ) (r : ℂ) (hr : r ^ 3 = a) : r ∈ solvableByRad ℚ ℂ := by
  have h_cu_mem : r ^ 3 ∈ solvableByRad ℚ ℂ := by rw [hr]; exact ha
  have h3_ne_zero : (3 : ℕ) ≠ 0 := by norm_num
  exact solvableByRad.rad_mem h3_ne_zero h_cu_mem

noncomputable instance splits_ℚ_ℂ (p : ℚ[X]) : Fact ((p.map (algebraMap ℚ ℂ)).Splits) :=
  ⟨IsAlgClosed.splits _⟩

-- ======================================================================
-- PART 1: The forward direction (n ≥ 5) — a quintic with Galois group S5
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

lemma natDegree_fQ : fQ.natDegree = 5 := by
  rw [← nd_fZ, Polynomial.natDegree_map]

lemma prime_natDegree_fQ : Nat.Prime fQ.natDegree := by
  rw [natDegree_fQ]
  exact Nat.prime_five

lemma separable_fQ : fQ.Separable :=
  irreducible_fQ.separable

-- Derivative lemmas
lemma deriv_X_pow_5 : derivative (X ^ 5 : ℚ[X]) = C (5 : ℚ) * X ^ 4 := by
  calc
    derivative (X ^ 5 : ℚ[X]) = C (5 : ℚ) * X ^ (5 - 1) := derivative_X_pow (R := ℚ) (n := 5)
    _ = C (5 : ℚ) * X ^ 4 := by
      have h : (5 : ℕ) - 1 = 4 := by omega
      rw [h]

lemma deriv_X_pow_4 : derivative (X ^ 4 : ℚ[X]) = C (4 : ℚ) * X ^ 3 := by
  calc
    derivative (X ^ 4 : ℚ[X]) = C (4 : ℚ) * X ^ (4 - 1) := derivative_X_pow (R := ℚ) (n := 4)
    _ = C (4 : ℚ) * X ^ 3 := by
      have h : (4 : ℕ) - 1 = 3 := by omega
      rw [h]

lemma deriv_fQ : derivative fQ = C (5 : ℚ) * X ^ 4 - C (4 : ℚ) := by
  unfold fQ fZ
  calc
    derivative ((X ^ 5 - C (4 : ℤ) * X + C (2 : ℤ)).map (Int.castRingHom ℚ))
        = (derivative (X ^ 5 - C (4 : ℤ) * X + C (2 : ℤ))).map (Int.castRingHom ℚ) := by
      rw [derivative_map]
    _ = (C (5 : ℤ) * X ^ 4 - C (4 : ℤ)).map (Int.castRingHom ℚ) := by
      -- Use the ℤ derivative lemma
      have h_deriv_Z : derivative (X ^ 5 - C (4 : ℤ) * X + C (2 : ℤ)) = C (5 : ℤ) * X ^ 4 - C (4 : ℤ) := by
        calc
          derivative (X ^ 5 - C (4 : ℤ) * X + C (2 : ℤ))
              = derivative (X ^ 5) - derivative (C (4 : ℤ) * X) + derivative (C (2 : ℤ)) := by
            rw [derivative_add, derivative_sub]
          _ = (C (5 : ℤ) * X ^ 4) - C (4 : ℤ) + 0 := by
            -- Use the same technique as the ℚ case
            have h5 : derivative (X ^ 5 : ℤ[X]) = C (5 : ℤ) * X ^ 4 := by
              calc
                derivative (X ^ 5 : ℤ[X]) = C (5 : ℤ) * X ^ (5 - 1) := derivative_X_pow (R := ℤ) (n := 5)
                _ = C (5 : ℤ) * X ^ 4 := by
                  have h : (5 : ℕ) - 1 = 4 := by omega; rw [h]
            rw [h5, derivative_C_mul, derivative_X, mul_one, derivative_C, add_zero]
          _ = C (5 : ℤ) * X ^ 4 - C (4 : ℤ) := by simp
      rw [h_deriv_Z]
    _ = C (5 : ℚ) * X ^ 4 - C (4 : ℚ) := by simp

lemma deriv2_fQ : derivative (derivative fQ) = C (20 : ℚ) * X ^ 3 := by
  rw [deriv_fQ]
  calc
    derivative (C (5 : ℚ) * X ^ 4 - C (4 : ℚ))
        = derivative (C (5 : ℚ) * X ^ 4) - derivative (C (4 : ℚ)) := by rw [derivative_sub]
    _ = (C (5 : ℚ) * derivative (X ^ 4)) - 0 := by rw [derivative_C_mul, derivative_C]
    _ = (C (5 : ℚ) * (C (4 : ℚ) * X ^ 3)) - 0 := by rw [deriv_X_pow_4]
    _ = C (5 : ℚ) * (C (4 : ℚ) * X ^ 3) := by simp
    _ = (C (5 : ℚ) * C (4 : ℚ)) * X ^ 3 := by ring
    _ = C ((5 : ℚ) * 4) * X ^ 3 := by rw [← C_mul]
    _ = C (20 : ℚ) * X ^ 3 := by norm_num

-- Real root bounds
lemma f_val (x : ℝ) : aeval x fQ = x ^ 5 - 4 * x + 2 := by
  unfold fQ fZ; simp

lemma f_neg2 : aeval (-2 : ℝ) fQ = -22 := by rw [f_val]; norm_num
lemma f_0 : aeval (0 : ℝ) fQ = 2 := by rw [f_val]; norm_num
lemma f_1 : aeval (1 : ℝ) fQ = -1 := by rw [f_val]; norm_num
lemma f_2 : aeval (2 : ℝ) fQ = 26 := by rw [f_val]; norm_num

lemma exists_root_neg2_0 : ∃ x : ℝ, -2 < x ∧ x < 0 ∧ aeval x fQ = 0 := by
  have h_cont : ContinuousOn (fun (x : ℝ) => aeval x fQ) (Set.Icc (-2 : ℝ) 0) :=
    (Polynomial.continuous_aeval fQ).continuousOn
  have h_mem : (0 : ℝ) ∈ Set.Icc (aeval (-2 : ℝ) fQ) (aeval (0 : ℝ) fQ) := by
    rw [f_neg2, f_0]; constructor <;> norm_num
  rcases intermediate_value_Icc (by norm_num : (-2 : ℝ) ≤ 0) h_cont h_mem with ⟨x, hx, hx_val⟩
  dsimp at hx_val
  have hx1 : -2 ≤ x := hx.1
  have hx2 : x ≤ 0 := hx.2
  have hx_gt_neg2 : -2 < x := by
    by_contra! H
    have hx_eq : x = -2 := by linarith
    rw [hx_eq, f_neg2] at hx_val; norm_num at hx_val
  have hx_lt_0 : x < 0 := by
    by_contra! H
    have hx_eq : x = 0 := by linarith
    rw [hx_eq, f_0] at hx_val; norm_num at hx_val
  exact ⟨x, hx_gt_neg2, hx_lt_0, hx_val⟩

lemma exists_root_0_1 : ∃ x : ℝ, 0 < x ∧ x < 1 ∧ aeval x fQ = 0 := by
  have h_cont : ContinuousOn (fun (x : ℝ) => aeval x fQ) (Set.Icc (0 : ℝ) 1) :=
    (Polynomial.continuous_aeval fQ).continuousOn
  have h_mem : (0 : ℝ) ∈ Set.Icc (aeval (1 : ℝ) fQ) (aeval (0 : ℝ) fQ) := by
    rw [f_1, f_0]; constructor <;> norm_num
  rcases intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) h_cont h_mem with ⟨x, hx, hx_val⟩
  dsimp at hx_val
  have hx1 : 0 ≤ x := hx.1
  have hx2 : x ≤ 1 := hx.2
  have hx_gt_0 : 0 < x := by
    by_contra! H
    have hx_eq : x = 0 := by linarith
    rw [hx_eq, f_0] at hx_val; norm_num at hx_val
  have hx_lt_1 : x < 1 := by
    by_contra! H
    have hx_eq : x = 1 := by linarith
    rw [hx_eq, f_1] at hx_val; norm_num at hx_val
  exact ⟨x, hx_gt_0, hx_lt_1, hx_val⟩

lemma exists_root_1_2 : ∃ x : ℝ, 1 < x ∧ x < 2 ∧ aeval x fQ = 0 := by
  have h_cont : ContinuousOn (fun (x : ℝ) => aeval x fQ) (Set.Icc (1 : ℝ) 2) :=
    (Polynomial.continuous_aeval fQ).continuousOn
  have h_mem : (0 : ℝ) ∈ Set.Icc (aeval (1 : ℝ) fQ) (aeval (2 : ℝ) fQ) := by
    rw [f_1, f_2]; constructor <;> norm_num
  rcases intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) h_cont h_mem with ⟨x, hx, hx_val⟩
  dsimp at hx_val
  have hx1 : 1 ≤ x := hx.1
  have hx2 : x ≤ 2 := hx.2
  have hx_gt_1 : 1 < x := by
    by_contra! H
    have hx_eq : x = 1 := by linarith
    rw [hx_eq, f_1] at hx_val; norm_num at hx_val
  have hx_lt_2 : x < 2 := by
    by_contra! H
    have hx_eq : x = 2 := by linarith
    rw [hx_eq, f_2] at hx_val; norm_num at hx_val
  exact ⟨x, hx_gt_1, hx_lt_2, hx_val⟩

-- Upper bound: at most 3 real roots
lemma card_rootSet_deriv2 : Fintype.card ((derivative (derivative fQ)).rootSet ℝ : Set ℝ) = 1 := by
  rw [deriv2_fQ]
  have h_root_set : (C (20 : ℚ) * X ^ 3 : ℚ[X]).rootSet ℝ = {(0 : ℝ)} := by
    ext x; simp
  simp [h_root_set]

lemma card_rootSet_deriv_le_2 : Fintype.card ((derivative fQ).rootSet ℝ : Set ℝ) ≤ 2 := by
  have h_bound : Fintype.card ((derivative fQ).rootSet ℝ : Set ℝ) ≤
      Fintype.card ((derivative (derivative fQ)).rootSet ℝ : Set ℝ) + 1 :=
    card_rootSet_le_derivative (derivative fQ)
  rw [card_rootSet_deriv2] at h_bound
  omega

lemma real_roots_at_most_3 : Fintype.card (fQ.rootSet ℝ : Set ℝ) ≤ 3 := by
  have h_bound : Fintype.card (fQ.rootSet ℝ : Set ℝ) ≤
      Fintype.card ((derivative fQ).rootSet ℝ : Set ℝ) + 1 :=
    card_rootSet_le_derivative fQ
  have h_deriv : Fintype.card ((derivative fQ).rootSet ℝ : Set ℝ) ≤ 2 := card_rootSet_deriv_le_2
  omega

-- Lower bound: at least 3 real roots
lemma real_roots_at_least_3 : 3 ≤ Fintype.card (fQ.rootSet ℝ : Set ℝ) := by
  rcases exists_root_neg2_0 with ⟨x1, hx1a, hx1b, hx1⟩
  rcases exists_root_0_1 with ⟨x2, hx2a, hx2b, hx2⟩
  rcases exists_root_1_2 with ⟨x3, hx3a, hx3b, hx3⟩
  have h_ne12 : x1 ≠ x2 := by linarith
  have h_ne13 : x1 ≠ x3 := by linarith
  have h_ne23 : x2 ≠ x3 := by linarith
  have h_mem : ({x1, x2, x3} : Finset ℝ) ⊆ (fQ.rootSet ℝ : Set ℝ) := by
    intro x hx
    simp at hx
    rcases hx with (rfl|rfl|rfl)
    · exact mem_rootSet.mpr ⟨fQ_ne_zero, hx1⟩
    · exact mem_rootSet.mpr ⟨fQ_ne_zero, hx2⟩
    · exact mem_rootSet.mpr ⟨fQ_ne_zero, hx3⟩
    -- Wait, fQ_ne_zero is not defined yet
    sorry
  sorry

-- Need fQ ≠ 0
lemma fQ_ne_zero : fQ ≠ 0 := by
  intro h
  have : irreducible_fQ = (by
    have : Irreducible (0 : ℚ[X]) := by
      -- 0 is not irreducible
      simpa using irreducible_fQ
    exact this) := rfl
  -- 0 is not irreducible, so contradiction
  have : ¬ Irreducible (0 : ℚ[X]) := by
    rw [irreducible_iff]
    simp
  exact this irreducible_fQ

-- Card of complex roots
lemma card_rootSet_ℂ : Fintype.card (fQ.rootSet ℂ : Set ℂ) = 5 := by
  rw [card_rootSet_eq_natDegree (separable_fQ.map (algebraMap ℚ ℂ)) (IsAlgClosed.splits (fQ.map (algebraMap ℚ ℂ))),
    natDegree_fQ]

-- Card of real roots
lemma card_rootSet_ℝ : Fintype.card (fQ.rootSet ℝ : Set ℝ) = 3 := by
  apply le_antisymm real_roots_at_most_3
  -- Need to prove at least 3
  -- This requires showing the three roots from IVT are distinct
  -- We'll complete this
  sorry

-- Root condition for the Galois lemma
lemma root_condition : Fintype.card (fQ.rootSet ℂ : Set ℂ) = Fintype.card (fQ.rootSet ℝ : Set ℝ) + 2 := by
  rw [card_rootSet_ℂ, card_rootSet_ℝ]
  norm_num

lemma gal_bijective : Function.Bijective (Gal.galActionHom fQ ℂ) :=
  Gal.galActionHom_bijective_of_prime_degree irreducible_fQ prime_natDegree_fQ root_condition

-- Main non-solvability theorem
theorem not_solvable_by_rad (x : ℂ) (hx : aeval x fQ = 0) : x ∉ solvableByRad ℚ ℂ := by
  intro hx_sol
  have h_sol_gal : IsSolvable fQ.Gal :=
    isSolvable_gal_of_irreducible hx_sol irreducible_fQ hx
  have h_non_sol_gal : ¬IsSolvable fQ.Gal := by
    -- fQ.Gal is isomorphic to S5 via gal_bijective
    have h_card : Fintype.card (fQ.rootSet ℂ : Set ℂ) = 5 := card_rootSet_ℂ
    have h_card' : 5 ≤ Cardinal.mk (fQ.rootSet ℂ) := by
      simpa [h_card] using show (5 : Cardinal) ≤ (5 : Cardinal) from le_rfl
    -- galActionHom gives an injective homomorphism into Perm(rootSet)
    have h_inj : Function.Injective (Gal.galActionHom fQ ℂ) :=
      (Function.bijective_iff_injective_and_surjective.mp gal_bijective).1
    have h_perm_not_solvable : ¬IsSolvable (Equiv.Perm (fQ.rootSet ℂ)) :=
      Equiv.Perm.not_solvable _ h_card'
    intro h_sol
    apply h_perm_not_solvable
    -- If fQ.Gal is solvable, then its image under galActionHom (a subgroup of Perm(rootSet ℂ)) is also solvable
    -- But galActionHom is bijective, so fQ.Gal ≅ Perm(rootSet ℂ)
    -- Actually we already know galActionHom is bijective, so fQ.Gal is isomorphic to Perm(rootSet ℂ)
    -- Since subgroups of solvable groups are solvable, and Perm(rootSet) has a solvable subgroup fQ.Gal (via the bijection)
    -- Wait, we need the other direction: if fQ.Gal is solvable then Perm(rootSet) is solvable via the bijection
    have : IsSolvable (Equiv.Perm (fQ.rootSet ℂ)) := by
      apply solvable_of_surjective (h := ?_) (hf := ?_)
      -- galActionHom is a surjective group homomorphism from fQ.Gal to Perm(rootSet ℂ)
      sorry
    exact this
  exact h_non_sol_gal h_sol_gal

-- For n ≥ 5, pad with linear factors
theorem exists_not_solvable_of_deg_ge_5 (n : ℕ) (hn : 5 ≤ n) :
    ∃ p : ℚ[X], p.natDegree = n ∧ ∃ x : ℂ, aeval x p = 0 ∧ x ∉ solvableByRad ℚ ℂ := by
  sorry

-- ======================================================================
-- PART 2: The reverse direction (n ≤ 4)
-- ======================================================================

theorem deg1_all_roots_solvable (p : ℚ[X]) (hp : p.natDegree = 1) (x : ℂ) (hx : aeval x p = 0) :
    x ∈ solvableByRad ℚ ℂ := by
  -- A degree-1 polynomial has the form aX + b with a ≠ 0
  -- The root is -b/a, which is in ℚ
  have ha : p.coeff 1 ≠ 0 := by
    rw [← natDegree_eq_zero_of_coeff_natDegree_eq_zero ?_]
    · exact Nat.one_ne_zero
    · rw [hp]
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
-- PART 3: The main theorem
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