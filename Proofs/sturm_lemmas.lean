import Mathlib
open List
open Polynomial
open scoped Classical

/-!
# Sturm's Theorem — Verified Helper Lemmas

This file contains verified lemmas for formalizing Sturm's theorem:
For a squarefree real polynomial p and interval (a,b) with p(a)≠0, p(b)≠0,
the number of distinct real roots of p in (a,b) equals σ(a) - σ(b),
where σ is the sign-variation function of the Sturm chain.
-/

namespace LeanEval.Algebra

noncomputable def sturmAux : ℝ[X] → ℝ[X] → ℕ → List ℝ[X]
  | a, _, 0       => [a]
  | a, b, (n + 1) =>
    if b = 0 then [a] else a :: sturmAux b (-(a % b)) n

noncomputable def sturmChain (p : ℝ[X]) : List ℝ[X] :=
  sturmAux p (derivative p) (p.natDegree + 2)

noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0)
  ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length

noncomputable def sigma (p : ℝ[X]) (x : ℝ) : ℕ :=
  signChanges ((sturmChain p).map fun q => q.eval x)

/-- The empty list has 0 sign changes. -/
lemma signChanges_empty : signChanges ([] : List ℝ) = 0 := by
  unfold signChanges; simp

/-- A singleton list with a nonzero element has 0 sign changes. -/
lemma signChanges_singleton (x : ℝ) (hx : x ≠ 0) : signChanges [x] = 0 := by
  unfold signChanges; simp [hx]

/-- Two elements of opposite sign have exactly 1 sign change. -/
lemma signChanges_two_opposite (x y : ℝ) (h : x * y < 0) : signChanges [x, y] = 1 := by
  have hx : x ≠ 0 := by
    intro hzero; have hzero_prod : x * y = 0 := mul_eq_zero.mpr (Or.inl hzero); linarith
  have hy : y ≠ 0 := by
    intro hzero; have hzero_prod : x * y = 0 := mul_eq_zero.mpr (Or.inr hzero); linarith
  unfold signChanges; simp [hx, hy, h]

/-- Prepending zero does not change the sign-change count. -/
lemma signChanges_cons_zero (xs : List ℝ) : signChanges (0 :: xs) = signChanges xs := by
  unfold signChanges; simp

/-- The Sturm auxiliary function never returns an empty list. -/
lemma sturmAux_ne_nil (a b : ℝ[X]) (n : ℕ) : sturmAux a b n ≠ [] := by
  induction' n with k ih generalizing a b
  · simp [sturmAux]
  · simp [sturmAux]
    split
    · simp
    · intro h; apply ih b (-(a % b)); simpa using h

/-- The Sturm chain is never empty. -/
lemma sturmChain_ne_nil (p : ℝ[X]) : sturmChain p ≠ [] := by
  simp [sturmChain, sturmAux_ne_nil]

/-- Over ℝ (a perfect field of characteristic 0), Squarefree ↔ Separable.
This lemma gives the forward direction: Squarefree → Separable. -/
lemma squarefree_imp_separable (p : ℝ[X]) (hp : Squarefree p) : Separable p :=
  ((PerfectField.separable_iff_squarefree (K := ℝ) (g := p)).mpr hp)

end LeanEval.Algebra
