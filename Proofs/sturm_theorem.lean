import Mathlib

open Polynomial

set_option autoImplicit false

namespace SturmTheorem

/-!
# Sturm's Theorem — Partial Formalization

This file contains the verified infrastructure for Sturm's theorem.
The full main theorem (`sturm_theorem`) is not yet formally verified;
see the remaining goals listed below.

## Verified Components

- `sturmSeqAux` / `sturmSeq`: Recursive Sturm sequence with termination proof
- `div_add_mod_eq`: Euclidean division identity for ℝ[x]
- `opposite_at_root`: a(x) = -c(x) when b(x)=0 and c = -(a % b)
- `signChangesAux` / `signChanges`: Sign change counting with zero-skipping
- `signChanges_cons_zero`: Removing leading zero preserves count
- `signChanges_triple`: [A,0,-A] → 1 for A ≠ 0
- `Vf`: The V_f(x) function
- `realRootsIn`: Real root extraction from complex roots

## Remaining Goals

1. `sturmSeq_no_consecutive_zero`: No two consecutive Sturm terms vanish together
2. `sign_change_at_f_root`: V_f decreases by 1 at a simple root of f (real analysis)
3. `no_change_at_intermediate`: V_f is locally constant at roots of intermediate p_i
4. `sturm_theorem`: Assembly of the full theorem via interval partitioning
-/

/-- Recursive Sturm sequence tail. -/
noncomputable def sturmSeqAux (p q : Polynomial ℝ) : List (Polynomial ℝ) :=
  if h : q = 0 then [] else q :: sturmSeqAux q (-(p % q))
termination_by degree q
decreasing_by simpa [degree_neg] using Polynomial.degree_mod_lt p h

/-- The full Sturm sequence: [f, f', p_2, ..., p_k]. -/
noncomputable def sturmSeq (f : Polynomial ℝ) : List (Polynomial ℝ) :=
  f :: sturmSeqAux f (derivative f)

/-- Euclidean division identity. -/
lemma div_add_mod_eq (a b : Polynomial ℝ) : a = (a / b) * b + a % b := by
  have h := EuclideanDomain.div_add_mod (a := a) (b := b); rw [mul_comm] at h; exact h.symm

/-- At root of b, neighbor values: a(x) = -r(x) where r = -(a % b). -/
lemma opposite_at_root (a b : Polynomial ℝ) (x : ℝ) (hbx : b.eval x = 0) :
    a.eval x = -((-(a % b)).eval x) := by
  have h := div_add_mod_eq a b
  have h' := congrArg (fun p : Polynomial ℝ => p.eval x) h; simp [h', hbx]

/-- Sign change counting (zeros filtered first). -/
noncomputable def signChangesAux : List ℝ → ℕ
  | [] => 0 | [_] => 0
  | x :: y :: zs => (if x * y < 0 then 1 else 0) + signChangesAux (y :: zs)

noncomputable def signChanges (xs : List ℝ) : ℕ :=
  signChangesAux (xs.filter (fun x => x ≠ 0))

/-- V_f(x) = sign change count of Sturm sequence at x. -/
noncomputable def Vf (f : Polynomial ℝ) (x : ℝ) : ℕ :=
  signChanges ((sturmSeq f).map (fun p => p.eval x))

lemma signChanges_cons_zero (xs : List ℝ) : signChanges (0 :: xs) = signChanges xs := by
  unfold signChanges; simp

lemma signChanges_triple (A : ℝ) (hA : A ≠ 0) : signChanges [A, 0, -A] = 1 := by
  unfold signChanges
  have hneg : -A ≠ 0 := by intro h; apply hA; linarith
  have hfilter : ([A, 0, -A] : List ℝ).filter (fun x => x ≠ 0) = [A, -A] := by simp [hA, hneg]
  rw [hfilter]; simp [signChangesAux, hA]

noncomputable def realRootsIn (f : Polynomial ℝ) (a b : ℝ) : Finset ℝ :=
  let f_ℂ := f.map (algebraMap ℝ ℂ)
  ((f_ℂ.roots.toFinset).filter (fun r : ℂ => r.im = 0 ∧ a < r.re ∧ r.re < b)).image Complex.re

/-- Sturm's Theorem (main statement — proof incomplete).
    For square-free f with f(a),f(b) ≠ 0 and a < b,
    #{real roots in (a,b)} = V_f(a) - V_f(b). -/
theorem sturm_theorem : ∀ (f : Polynomial ℝ) (a b : ℝ), Squarefree f → a < b →
    f.eval a ≠ 0 → f.eval b ≠ 0 → (realRootsIn f a b).card = Vf f a - Vf f b := by
  -- The full Lean proof requires 4 remaining subgoals (see file header).
  -- All algebraic foundations are verified above.
  sorry

end SturmTheorem