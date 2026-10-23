import Mathlib

/-! # The genus-0 band: forced spring, break = pi^2 (2026-10-23)

Seat `x'' + mu (1 + x) = 0`, `x(0) = x(1) = 0`, `x >= 0`. Positive solutions exist exactly for `0 < mu < pi^2`,
so the break is `pi^2` (a supremum, not reached: the solution blows up at resonance).
Upper bound with no integrals: `W = x' sin(pi t) - x pi cos(pi t)` vanishes at both ends, and
`W' = (pi^2 - mu) x sin(pi t) - mu sin(pi t) < 0` on (0,1) when `mu >= pi^2` -- contradiction. -/

namespace LinearOde

def Sol (μ : ℝ) (x x' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x t ∧ HasDerivAt x (x' t) t ∧ HasDerivAt x' (-(μ * (1 + x t))) t) ∧
    x 0 = 0 ∧ x 1 = 0

/-- No nonnegative solution at or beyond resonance. -/
theorem lt_pi_sq {μ : ℝ} {x x' : ℝ → ℝ} (h : Sol μ x x') (hμ : 0 < μ) : μ < Real.pi ^ 2 := by
  by_contra hge
  push_neg at hge
  set W : ℝ → ℝ := fun t => x' t * Real.sin (Real.pi * t) - x t * (Real.pi * Real.cos (Real.pi * t))
  have hW : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt W
      ((Real.pi ^ 2 - μ) * x t * Real.sin (Real.pi * t) - μ * Real.sin (Real.pi * t)) t := by
    intro t ht
    obtain ⟨_, hd, hdd⟩ := h.1 t ht
    have hs : HasDerivAt (fun t => Real.sin (Real.pi * t)) (Real.cos (Real.pi * t) * Real.pi) t := by
      have h := (Real.hasDerivAt_sin (Real.pi * t)).comp t ((hasDerivAt_id' t).const_mul Real.pi)
      exact h.congr_deriv (by ring)
    have hc : HasDerivAt (fun t => Real.pi * Real.cos (Real.pi * t)) (Real.pi * (-Real.sin (Real.pi * t) * Real.pi)) t := by
      have h := ((Real.hasDerivAt_cos (Real.pi * t)).comp t ((hasDerivAt_id' t).const_mul Real.pi)).const_mul Real.pi
      exact h.congr_deriv (by ring)
    exact ((hdd.mul hs).sub (hd.mul hc)).congr_deriv (by ring)
  have hanti : StrictAntiOn W (Set.Icc 0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    · exact fun t ht => (hW t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hW t (Set.Ioo_subset_Icc_self ht)).deriv]
      have hsin : 0 < Real.sin (Real.pi * t) :=
        Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, ht.1]) (by nlinarith [Real.pi_pos, ht.2])
      have hx := (h.1 t (Set.Ioo_subset_Icc_self ht)).1
      have : (Real.pi ^ 2 - μ) * x t * Real.sin (Real.pi * t) ≤ 0 := by
        have : Real.pi ^ 2 - μ ≤ 0 := by linarith
        have := mul_nonneg hx hsin.le
        nlinarith
      nlinarith [mul_pos hμ hsin]
  have h01 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
  simp only [W, h.2.1, h.2.2, mul_zero, Real.sin_zero, Real.sin_pi, mul_one, zero_mul, sub_zero] at h01
  linarith

/-- Below resonance there is an explicit nonnegative solution. -/
theorem exists_below {μ : ℝ} (hμ : 0 < μ) (hlt : μ < Real.pi ^ 2) :
    Sol μ (fun t => Real.cos (Real.sqrt μ * (t - 1 / 2)) / Real.cos (Real.sqrt μ / 2) - 1)
      (fun t => -(Real.sqrt μ * Real.sin (Real.sqrt μ * (t - 1 / 2))) / Real.cos (Real.sqrt μ / 2)) := by
  set s := Real.sqrt μ with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hμ
  have hs2 : s ^ 2 = μ := Real.sq_sqrt hμ.le
  have hspi : s < Real.pi := by
    have := Real.sqrt_lt_sqrt hμ.le hlt
    rwa [Real.sqrt_sq Real.pi_pos.le] at this
  have hC : 0 < Real.cos (s / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  refine ⟨fun t ht => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- nonnegativity: |s (t - 1/2)| <= s/2 < pi/2, so cos(s (t - 1/2)) >= cos(s/2)
    rw [sub_nonneg, le_div_iff₀ hC, one_mul]
    rw [← Real.cos_abs (s * (t - 1 / 2))]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
    rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2]
  · have := ((Real.hasDerivAt_cos (s * (t - 1 / 2))).comp t (((hasDerivAt_id t).sub_const (1 / 2)).const_mul s))
    exact ((this.div_const (Real.cos (s / 2))).sub_const 1).congr_deriv (by simp; ring)
  · have := ((Real.hasDerivAt_sin (s * (t - 1 / 2))).comp t (((hasDerivAt_id t).sub_const (1 / 2)).const_mul s))
    refine (((this.const_mul s).neg).div_const (Real.cos (s / 2))).congr_deriv ?_
    field_simp
    rw [← hs2]; ring
  · beta_reduce; rw [show s * (0 - 1 / 2) = -(s / 2) by ring, Real.cos_neg, div_self hC.ne']; ring
  · beta_reduce; rw [show s * (1 - 1 / 2) = s / 2 by ring, div_self hC.ne']; ring

/-- **Genus-0 band, end to end: the break is pi^2** (least upper bound of pushes with a nonnegative solution). -/
theorem linear_break_exact : IsLUB {μ : ℝ | 0 < μ ∧ ∃ x x' : ℝ → ℝ, Sol μ x x'} (Real.pi ^ 2) := by
  constructor
  · rintro μ ⟨hμ, x, x', h⟩; exact (lt_pi_sq h hμ).le
  · intro b hb
    by_contra hlt
    push_neg at hlt
    have hp := pow_pos Real.pi_pos 2
    set μ := max (b + (Real.pi ^ 2 - b) / 2) (Real.pi ^ 2 / 2)
    have hμ0 : 0 < μ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hμlt : μ < Real.pi ^ 2 := max_lt (by linarith) (by linarith)
    have := hb ⟨hμ0, _, _, exists_below hμ0 hμlt⟩
    have : b + (Real.pi ^ 2 - b) / 2 ≤ μ := le_max_left _ _
    linarith

end LinearOde
