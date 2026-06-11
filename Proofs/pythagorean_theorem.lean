import Mathlib
open EuclideanGeometry
open Real

/-!
# The Pythagorean Theorem

For any right triangle with right angle at B,
the square of the hypotenuse equals the sum of the squares of the legs:
|A-C|² = |A-B|² + |B-C|²

## Proof

Two proofs are provided:

1. **Direct lemma**: Uses `EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two`
   which is exactly the Pythagorean theorem as an "if and only if" statement.

2. **Law of cosines**: Applies the law of cosines and the fact that cos(π/2) = 0.
-/

/-!
### Theorem (Pythagoras)
If ∠ABC = π/2, then |A-C|² = |A-B|² + |B-C|².
-/

theorem pythagorean_theorem {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C : P)
    (h : ∠ A B C = π / 2) : dist A C * dist A C = dist A B * dist A B + dist C B * dist C B := by
  -- Proof 1: Using the direct Mathlib lemma
  have h_iff := (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A B C).mpr h
  exact h_iff

/-!
### Proof via Law of Cosines

The law of cosines states:
|A-C|² = |A-B|² + |B-C|² - 2·|A-B|·|B-C|·cos(∠ABC)

When ∠ABC = π/2, we have cos(π/2) = 0, so the Pythagorean theorem follows.
-/

theorem pythagorean_via_law_of_cosines {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C : P)
    (h : ∠ A B C = π / 2) : dist A C * dist A C = dist A B * dist A B + dist C B * dist C B := by
  have law_cos_eq : dist A C * dist A C = dist A B * dist A B + dist C B * dist C B
      - 2 * dist A B * dist C B * Real.cos (∠ A B C) := EuclideanGeometry.law_cos A B C
  have cos_right_angle : Real.cos (∠ A B C) = 0 := by
    rw [h]
    exact Real.cos_pi_div_two
  rw [cos_right_angle] at law_cos_eq
  ring_nf at law_cos_eq
  exact law_cos_eq

/-!
### Converse
If |A-C|² = |A-B|² + |B-C|², then ∠ABC = π/2.
-/

theorem pythagorean_converse {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C : P)
    (h : dist A C * dist A C = dist A B * dist A B + dist C B * dist C B) : ∠ A B C = π / 2 := by
  exact (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A B C).mp h

/-!
### Full Equivalence
-/

theorem pythagorean_iff {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C : P) :
    dist A C * dist A C = dist A B * dist A B + dist C B * dist C B ↔ ∠ A B C = π / 2 :=
  EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A B C
