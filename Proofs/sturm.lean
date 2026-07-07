import Mathlib
open Polynomial
open Set

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

lemma signChanges_nil : signChanges ([] : List ℝ) = 0 := by
  unfold signChanges; simp

lemma signChanges_singleton (x : ℝ) : signChanges [x] = 0 := by
  unfold signChanges
  by_cases h : x = 0
  · subst x; simp
  · simp [h]

lemma div_lemma (a b : ℝ[X]) : a = (a /ₘ b) * b + a %ₘ b := by
  have h := (Polynomial.modByMonic_add_div a b).symm
  calc
    a = a %ₘ b + b * (a /ₘ b) := h
    _ = (a /ₘ b) * b + a %ₘ b := by ring

lemma sturm_recurrence (a b c : ℝ[X]) (hc : c = -(a %ₘ b)) : a = (a /ₘ b) * b - c := by
  have h := div_lemma a b
  calc
    a = (a /ₘ b) * b + a %ₘ b := h
    _ = (a /ₘ b) * b - (-(a %ₘ b)) := by ring
    _ = (a /ₘ b) * b - c := by rw [hc]

lemma opposite_at_root (a b c : ℝ[X]) (hc_def : c = -(a %ₘ b)) (r : ℝ) (hb_root : b.eval r = 0) : 
    a.eval r = -(c.eval r) := by
  have h := sturm_recurrence a b c hc_def
  apply_fun (fun q => q.eval r) at h
  simp [hb_root] at h
  linarith

lemma opposite_signs_at_root (a b c : ℝ[X]) (hc_def : c = -(a %ₘ b))
    (r : ℝ) (hb_root : b.eval r = 0) (hc_nonzero : c.eval r ≠ 0) : a.eval r * c.eval r < 0 := by
  have ha_eq : a.eval r = -(c.eval r) := opposite_at_root a b c hc_def r hb_root
  rw [ha_eq]
  have hsq : 0 < c.eval r * c.eval r := mul_self_pos.mpr hc_nonzero
  nlinarith

/- Main theorem: Sturm's theorem -/
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  sorry