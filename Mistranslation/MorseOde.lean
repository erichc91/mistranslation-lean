import Mathlib
import Mistranslation.BratuOde
import Mistranslation.PinneyInv

/-! # The Morse bridge Bratu -> Bratu from the ODE (2026-10-23)

Seat `x'' + mu (e^x + lam e^(2x)) = 0`, `x(0) = x(1) = 0`, `lam >= 0` (no seat in the table: an empty-seat family).
`u = e^(-x)` straightens it to `u'' = E u - mu`, so `u - mu/E` is a cosh-spring. Every solution then satisfies
`u_m = mu/c^2 + (1 - mu/c^2)/cosh(c/2)` and `c^2 u_m^2 = mu (2 u_m + lam)` (c = sqrt E, u_m = e^(-x(1/2))). -/

namespace MorseOde

def Sol (lam μ : ℝ) (x x' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt x (x' t) t ∧
      HasDerivAt x' (-(μ * (Real.exp (x t) + lam * Real.exp (2 * x t)))) t) ∧ x 0 = 0 ∧ x 1 = 0

lemma energy {lam μ : ℝ} {x x' : ℝ → ℝ} (h : Sol lam μ x x') :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, x' t * x' t + 2 * μ * Real.exp (x t) + μ * lam * Real.exp (2 * x t)
      = x' 0 * x' 0 + 2 * μ * Real.exp (x 0) + μ * lam * Real.exp (2 * x 0) := by
  refine BratuOde.const_on (f := fun t => x' t * x' t + 2 * μ * Real.exp (x t) + μ * lam * Real.exp (2 * x t)) ?_
  intro s hs
  obtain ⟨hd, hdd⟩ := h.1 s hs
  have := ((hdd.mul hdd).add (hd.exp.const_mul (2 * μ))).add ((hd.const_mul 2).exp.const_mul (μ * lam))
  refine this.congr_deriv ?_
  ring

/-- **Every Morse solution (mu > 0) satisfies the two-equation formula.** -/
theorem mu_formula {lam μ : ℝ} {x x' : ℝ → ℝ} (h : Sol lam μ x x') (hμ : 0 < μ) (hl : 0 ≤ lam) :
    ∃ c um : ℝ, 0 < c ∧ 0 < um ∧ um = μ / c ^ 2 + (1 - μ / c ^ 2) / Real.cosh (c / 2) ∧
      c ^ 2 * um ^ 2 = μ * (2 * um + lam) := by
  set E := x' 0 * x' 0 + 2 * μ * Real.exp (x 0) + μ * lam * Real.exp (2 * x 0) with hE
  have hEpos : 0 < E := by
    have h1 := Real.exp_pos (x 0)
    have h2 := Real.exp_pos (2 * x 0)
    have : 0 ≤ μ * lam * Real.exp (2 * x 0) := by positivity
    nlinarith [mul_self_nonneg (x' 0)]
  clear_value E
  set c := Real.sqrt E with hc
  have hcpos : 0 < c := Real.sqrt_pos.mpr hEpos
  have hc2 : c ^ 2 = E := Real.sq_sqrt hEpos.le
  have memh : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  -- z = e^(-x) - mu/E is a cosh-spring with k = c
  have sol := PinneyInv.cosh_solve (z := fun t => Real.exp (-(x t)) - μ / E)
    (z' := fun t => -(x' t) * Real.exp (-(x t))) (k := c) (z0 := 1 - μ / E) hcpos
    (fun t ht => by
      obtain ⟨hd, hdd⟩ := h.1 t ht
      refine ⟨((hd.neg.exp).sub_const _).congr_deriv (by simp only [Pi.neg_apply]; ring), ?_⟩
      have hEt := energy h t ht
      rw [← hE] at hEt
      refine ((hdd.neg).mul (hd.neg.exp)).congr_deriv ?_
      rw [hc2, mul_sub, mul_div_cancel₀ _ hEpos.ne']
      have e2 : Real.exp (2 * x t) = Real.exp (x t) * Real.exp (x t) := by rw [← Real.exp_add]; ring_nf
      have e1 : Real.exp (x t) * Real.exp (-(x t)) = 1 := by rw [← Real.exp_add]; simp
      simp only [Pi.neg_apply]
      rw [e2] at hEt ⊢
      linear_combination (Real.exp (-(x t))) * hEt - μ * e1)
    (by simp [h.2.1]) (by simp [h.2.2])
  obtain ⟨hz, hz'⟩ := sol
  beta_reduce at hz hz'
  have hx'0 : x' (1 / 2) = 0 := by
    have hp := Real.exp_pos (-(x (1 / 2)))
    have : x' (1 / 2) * Real.exp (-(x (1 / 2))) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · linarith
  refine ⟨c, Real.exp (-(x (1 / 2))), hcpos, Real.exp_pos _, ?_, ?_⟩
  · rw [hc2]; linarith
  · have hEm := energy h (1 / 2) memh
    rw [← hE, hx'0] at hEm
    rw [hc2]
    have e2 : Real.exp (2 * x (1 / 2)) = Real.exp (x (1 / 2)) * Real.exp (x (1 / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have e1 : Real.exp (x (1 / 2)) * Real.exp (-(x (1 / 2))) = 1 := by rw [← Real.exp_add]; simp
    rw [e2] at hEm
    set U := Real.exp (-(x (1 / 2)))
    set X := Real.exp (x (1 / 2))
    linear_combination (-(U ^ 2)) * hEm + (2 * μ * U + μ * lam * (X * U + 1)) * e1
end MorseOde
