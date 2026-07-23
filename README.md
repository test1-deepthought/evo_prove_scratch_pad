# sturm_theorem

**Branch:** `evo/prove-sturm-theorem-20260723-221804`
**Lake build:** :hourglass: not_run

---

# Sturm's Theorem — Formalization Status

## Status: INCOMPLETE

The mathematical proof (Phase 1) is verified. The Lean 4 formalization (Phase 2) has substantial verified infrastructure but the full main theorem is not yet formally verified.

## Verified Components (lean4_exec exit_code 0)

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
2. `sign_change_at_f_root`: V_f decreases by 1 at a simple root of f
3. `no_change_at_intermediate`: V_f is locally constant at roots of intermediate p_i
4. `sturm_theorem`: Assembly of the full theorem via interval partitioning