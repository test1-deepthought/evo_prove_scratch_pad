import Mathlib

/-- Helper lemma: if a = b then b = a -/
theorem eq_swap {α : Type} {a b : α} (h : a = b) : b = a := h.symm