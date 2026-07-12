# sturm_lemmas

**Branch:** `evo/prove-sturm-lemmas-20260712-070948`
**Lake build:** :hourglass: not_run

---

# Sturm's Theorem — Partial Formalization

## Problem
Prove Sturm's theorem: For a squarefree real polynomial p and interval (a,b) with p(a)≠0, p(b)≠0, the number of distinct real roots of p in (a,b) equals σ(a) - σ(b).

## Status: INCOMPLETE — Partial progress

## Verified Lemmas (7/7)
1. `signChanges_empty`: signChanges [] = 0
2. `signChanges_singleton`: signChanges [x] = 0 for x ≠ 0
3. `signChanges_two_opposite`: signChanges [x,y] = 1 when x*y < 0
4. `signChanges_cons_zero`: signChanges (0 :: xs) = signChanges xs
5. `sturmAux_ne_nil`: sturmAux a b n ≠ []
6. `sturmChain_ne_nil`: sturmChain p ≠ []
7. `squarefree_imp_separable`: Squarefree p → Separable p over ℝ

## Next Steps
To complete the proof:

1. **sigma_locally_constant**: Prove sigma is constant on intervals where no chain entry vanishes. Use `IntermediateValueTheorem` and the fact that each entry's eval is continuous.

2. **sigma_drop_at_root**: At a simple root r of p (p'(r)≠0), sigma drops by exactly 1. Show p changes sign while p' does not.

3. **sigma_no_change_at_interior_root**: At roots of interior chain entries (k≥2), sigma is unchanged due to the Sturm recurrence.

4. **count_roots_eq_sigma_diff**: Sum over all roots in (a,b) using induction.

## Key Mathlib References
- `PerfectField.separable_iff_squarefree` (ℝ is perfect)
- `Polynomial.nodup_roots` (distinct roots for separable polynomials)
- `Polynomial.rootMultiplicity_le_one_of_separable`
- `Polynomial.eval`, `Polynomial.derivative`
- `IntermediateValueTheorem`

## Lean-Eval Problem
The problem is registered as `sturm` in the Lean-Eval benchmark suite.
The saved partial attempt is at `failed_submissions/sturm/`.