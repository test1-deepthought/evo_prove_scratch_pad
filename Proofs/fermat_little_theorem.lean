import Mathlib
open Finset
open Nat

/--
Lemma: If each term of a sum is ≡ 0 [MOD p], then the sum is ≡ 0 [MOD p].
-/
lemma sum_modEq_zero (s : Finset ℕ) (f : ℕ → ℕ) (p : ℕ) (h : ∀ i ∈ s, f i ≡ 0 [MOD p]) : 
    (∑ i ∈ s, f i) ≡ 0 [MOD p] := by
  induction' s using Finset.induction_on with a s has ih
  · exact Nat.ModEq.refl 0
  · have ha : f a ≡ 0 [MOD p] := h a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, f i ≡ 0 [MOD p] := by
      intro i hi
      exact h i (Finset.mem_insert_of_mem hi)
    have hsum : (∑ i ∈ s, f i) ≡ 0 [MOD p] := ih hs
    simp [Finset.sum_insert has, ha.add hsum]

/--
Fermat's Little Theorem for natural numbers.
For any prime p and natural number n, n^p ≡ n (mod p).

Proof: By induction on n using the binomial theorem.
The inductive step expands (k+1)^p using add_pow (binomial theorem).
For 0 < i < p, the prime p divides the binomial coefficient C(p,i)
by Nat.Prime.dvd_choose_self, making those terms ≡ 0 (mod p).
Only the i=0 term (1) and i=p term (k^p) survive modulo p.
-/
theorem fermat_nat (p : ℕ) (hp : p.Prime) (n : ℕ) : n ^ p ≡ n [MOD p] := by
  induction' n with k ih
  · have hp_pos : 0 < p := Nat.Prime.pos hp
    simp [hp_pos, Nat.ModEq]
  · have hbinom : (k + 1) ^ p = ∑ i ∈ range (p + 1), (Nat.choose p i : ℕ) * (k ^ i) := by
      calc
        (k + 1) ^ p = ∑ m ∈ range (p + 1), k ^ m * (1 : ℕ) ^ (p - m) * (Nat.choose p m : ℕ) := by
          simpa using add_pow (k : ℕ) (1 : ℕ) p
        _ = ∑ m ∈ range (p + 1), (Nat.choose p m : ℕ) * (k ^ m) := by simp [mul_comm]
    rw [hbinom]
    have hmem0 : (0 : ℕ) ∈ range (p + 1) := by simp
    have hp_pos : 0 < p := Nat.Prime.pos hp
    have hmemP : (p : ℕ) ∈ (range (p + 1)).erase 0 := by
      refine Finset.mem_erase.mpr ⟨by omega, by simp⟩
    have h_sum_decomp : (∑ i ∈ range (p + 1), (Nat.choose p i : ℕ) * (k ^ i)) =
        (Nat.choose p 0 : ℕ) * (k ^ 0) + (Nat.choose p p : ℕ) * (k ^ p) +
        (∑ i ∈ ((range (p + 1)).erase 0).erase p, (Nat.choose p i : ℕ) * (k ^ i)) := by
      calc
        (∑ i ∈ range (p + 1), (Nat.choose p i : ℕ) * (k ^ i))
            = ((∑ i ∈ (range (p + 1)).erase 0, (Nat.choose p i : ℕ) * (k ^ i)) + 
               (Nat.choose p 0 : ℕ) * (k ^ 0)) := by
          rw [← Finset.sum_erase_add (range (p + 1)) (λ i => (Nat.choose p i : ℕ) * (k ^ i)) hmem0]
        _ = (Nat.choose p 0 : ℕ) * (k ^ 0) + (∑ i ∈ (range (p + 1)).erase 0, (Nat.choose p i : ℕ) * (k ^ i)) := by
          omega
        _ = (Nat.choose p 0 : ℕ) * (k ^ 0) + ((∑ i ∈ ((range (p + 1)).erase 0).erase p, (Nat.choose p i : ℕ) * (k ^ i)) +
            (Nat.choose p p : ℕ) * (k ^ p)) := by
          rw [← Finset.sum_erase_add ((range (p + 1)).erase 0) (λ i => (Nat.choose p i : ℕ) * (k ^ i)) hmemP]
        _ = (Nat.choose p 0 : ℕ) * (k ^ 0) + (Nat.choose p p : ℕ) * (k ^ p) +
            (∑ i ∈ ((range (p + 1)).erase 0).erase p, (Nat.choose p i : ℕ) * (k ^ i)) := by
          omega
    rw [h_sum_decomp]
    let interior := ((range (p + 1)).erase 0).erase p
    have h_interior : ∀ i ∈ interior, (Nat.choose p i : ℕ) * (k ^ i) ≡ 0 [MOD p] := by
      intro i hi
      rcases Finset.mem_erase.mp hi with ⟨hi_ne_p, hi_mem⟩
      rcases Finset.mem_erase.mp hi_mem with ⟨hi_ne_0, hi_mem_range⟩
      have hi_lt_p : i < p := by
        have hi_le_p : i ≤ p := Finset.mem_range_succ_iff.mp hi_mem_range
        exact Nat.lt_of_le_of_ne hi_le_p hi_ne_p
      have hdiv : p ∣ Nat.choose p i := hp.dvd_choose_self hi_ne_0 hi_lt_p
      have hprod : p ∣ (Nat.choose p i : ℕ) * (k ^ i) := hdiv.mul_right (k ^ i)
      rcases hprod with ⟨t, ht⟩
      rw [ht]
      simp [Nat.ModEq]
    have h_interior_sum : (∑ i ∈ interior, (Nat.choose p i : ℕ) * (k ^ i)) ≡ 0 [MOD p] :=
      sum_modEq_zero interior (λ i => (Nat.choose p i : ℕ) * (k ^ i)) p h_interior
    calc
      (Nat.choose p 0 : ℕ) * (k ^ 0) + (Nat.choose p p : ℕ) * (k ^ p) + 
          (∑ i ∈ interior, (Nat.choose p i : ℕ) * (k ^ i))
        ≡ (Nat.choose p 0 : ℕ) * (k ^ 0) + (Nat.choose p p : ℕ) * (k ^ p) + 0 [MOD p] := by
          exact ((Nat.ModEq.refl _).add (Nat.ModEq.refl _)).add h_interior_sum
      _ = (Nat.choose p 0 : ℕ) * (k ^ 0) + (Nat.choose p p : ℕ) * (k ^ p) := by simp
      _ = 1 + k ^ p := by simp
      _ ≡ 1 + k [MOD p] := by
        simpa using (Nat.ModEq.refl (1 : ℕ)).add ih
      _ = k + 1 := by omega

/--
Fermat's Little Theorem for integers.
For any prime p and integer a, a^p ≡ a (mod p).

Proof: Use the fact that ZMod p has characteristic p, so by Freshman's Dream
(ZMod.pow_card) we have (a : ZMod p)^p = (a : ZMod p). Translating this equality
back to ℤ using ZMod.intCast_eq_intCast_iff_dvd_sub gives the result.
-/
theorem fermat_int (p : ℕ) (hp : p.Prime) (a : ℤ) : a ^ p ≡ a [ZMOD p] := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h : (a : ZMod p) ^ p = (a : ZMod p) := ZMod.pow_card (a : ZMod p)
  have h_cast : ((a ^ p : ℤ) : ZMod p) = (a : ZMod p) := by
    calc
      ((a ^ p : ℤ) : ZMod p) = ((a : ZMod p) ^ p) := by
        simp
      _ = (a : ZMod p) := h
  have hdvd : (p : ℤ) ∣ a - (a ^ p : ℤ) :=
    ((ZMod.intCast_eq_intCast_iff_dvd_sub (a ^ p) a p).mp h_cast)
  rw [Int.modEq_iff_dvd]
  exact hdvd