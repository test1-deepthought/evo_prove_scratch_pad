import Mathlib
open Polynomial
open Set
open Filter

set_option autoImplicit false

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

lemma div_lemma (a b : ℝ[X]) : a % b + b * (a / b) = a :=
  EuclideanDomain.mod_add_div a b

lemma opposite_signs_at_root (a b c : ℝ[X]) (hc_def : c = -(a % b)) (r : ℝ) (hb_root : b.eval r = 0) 
    (hc_nonzero : c.eval r ≠ 0) : a.eval r * c.eval r < 0 := by
  have hdiv := div_lemma a b
  have ha_mod_eq_neg_c : a % b = -c := by
    rw [hc_def, neg_neg]
  rw [ha_mod_eq_neg_c] at hdiv
  have ha_expr : a = b * (a / b) - c := by
    calc
      a = (-c) + b * (a / b) := hdiv.symm
      _ = b * (a / b) - c := by ring
  have ha_val : a.eval r = -(c.eval r) := by
    have := congrArg (fun q => q.eval r) ha_expr
    simp [hb_root, Polynomial.eval_sub, Polynomial.eval_mul] at this
    exact this
  rw [ha_val]
  have hsq : 0 < c.eval r * c.eval r := mul_self_pos.mpr hc_nonzero
  nlinarith

lemma poly_continuous (q : ℝ[X]) : Continuous (q.eval : ℝ → ℝ) :=
  Polynomial.continuous q

-- Sign of a polynomial is locally constant where it's nonzero
lemma sign_locally_constant (q : ℝ[X]) (x : ℝ) (hx : q.eval x ≠ 0) :
    ∃ ε > 0, ∀ y, |y - x| < ε → q.eval y * q.eval x > 0 := by
  have hc : Continuous (q.eval : ℝ → ℝ) := poly_continuous q
  have hpos : 0 < |q.eval x| := abs_pos.mpr hx
  rcases Metric.tendsto_nhds_nhds.mp (hc.tendsto x) (|q.eval x|) hpos with ⟨ε, hε, h⟩
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hqy : |q.eval y - q.eval x| < |q.eval x| := h y hy
  have h_nonzero : q.eval y ≠ 0 := by
    intro hzero
    have : |0 - q.eval x| = |q.eval x| := by simp
    have : |q.eval y - q.eval x| = |q.eval x| := by simp [hzero]
    linarith
  have h_same_sign : q.eval y * q.eval x > 0 := by
    by_contra! hle
    have : q.eval y * q.eval x ≤ 0 := hle
    have h_abs_ge : |q.eval y - q.eval x| ≥ |q.eval x| := by
      have h_opp : q.eval y * q.eval x ≤ 0 := hle
      nlinarith [abs_add (q.eval y) (-q.eval x), abs_sub_abs_le_abs_sub (q.eval y) (q.eval x)]
    linarith
  exact h_same_sign

-- sigma is locally constant where all chain entries are nonzero
lemma sigma_locally_constant (p : ℝ[X]) (x : ℝ) (h : ∀ q ∈ sturmChain p, q.eval x ≠ 0) :
    ∃ ε > 0, ∀ y, |y - x| < ε → sigma p y = sigma p x := by
  sorry

-- Main theorem
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  sorry