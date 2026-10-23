import Mathlib
import Mistranslation.MorseOde

/-! # The Morse bridge: existence and the break (2026-10-23)

Seat `x'' + mu (e^x + lam e^(2x)) = 0`, `x(0) = x(1) = 0`, `lam >= 0`. Straightened coordinate `u = e^(-x)` is the
shifted spring `u = p + b cosh(c(t - 1/2))`, `p = mu/c^2`, `b = (1-p)/C`, `C = cosh(c/2)`, with the energy tie
`b^2 = p^2 + p lam`. That tie is the quadratic `(C^2-1) p^2 + Q p - 1 = 0`, `Q = C^2 lam + 2`, whose positive root is
`p = 2/(Q + sqrt(Q^2 + 4(C^2-1)))`. So the push curve is `fm(c) = c^2 p(c)`: every c gives a solution, every
solution comes from a c, and the break is the top of fm (attained). -/

namespace MorseOde

noncomputable def Cm (c : ℝ) : ℝ := Real.cosh (c / 2)
noncomputable def Qm (lam c : ℝ) : ℝ := Cm c ^ 2 * lam + 2
noncomputable def Sm (lam c : ℝ) : ℝ := Real.sqrt (Qm lam c ^ 2 + 4 * (Cm c ^ 2 - 1))
noncomputable def pm (lam c : ℝ) : ℝ := 2 / (Qm lam c + Sm lam c)
noncomputable def fm (lam c : ℝ) : ℝ := c ^ 2 * pm lam c

lemma Cm_ge (c : ℝ) : 1 ≤ Cm c := Real.one_le_cosh _
lemma Qm_ge {lam : ℝ} (hl : 0 ≤ lam) (c : ℝ) : 2 ≤ Qm lam c := by
  unfold Qm; have := sq_nonneg (Cm c); nlinarith
lemma Sm_sq {lam : ℝ} (hl : 0 ≤ lam) (c : ℝ) : Sm lam c ^ 2 = Qm lam c ^ 2 + 4 * (Cm c ^ 2 - 1) := by
  unfold Sm; rw [Real.sq_sqrt]; nlinarith [Cm_ge c, Qm_ge hl c]
lemma Sm_ge {lam : ℝ} (hl : 0 ≤ lam) (c : ℝ) : 2 * Cm c ≤ Sm lam c := by
  have h := Sm_sq hl c; have hq := Qm_ge hl c; have hs : 0 ≤ Sm lam c := Real.sqrt_nonneg _
  nlinarith [Cm_ge c]
lemma den_pos {lam : ℝ} (hl : 0 ≤ lam) (c : ℝ) : 0 < Qm lam c + Sm lam c := by
  have := Qm_ge hl c; have := Sm_ge hl c; have := Cm_ge c; linarith
lemma pm_pos {lam : ℝ} (hl : 0 ≤ lam) (c : ℝ) : 0 < pm lam c := by
  unfold pm; have := den_pos hl c; positivity
lemma pm_lt_one {lam : ℝ} (hl : 0 ≤ lam) (c : ℝ) : pm lam c < 1 := by
  unfold pm; rw [div_lt_one (den_pos hl c)]
  have := Qm_ge hl c; have := Sm_ge hl c; have := Cm_ge c; linarith
lemma pm_le {lam : ℝ} (hl : 0 ≤ lam) (c : ℝ) : pm lam c ≤ 1 / Cm c := by
  unfold pm; have hC : 0 < Cm c := by linarith [Cm_ge c]
  rw [div_le_div_iff₀ (den_pos hl c) hC]; have := Qm_ge hl c; have := Sm_ge hl c; linarith

/-- the energy tie as a quadratic: pm is a root -/
lemma pm_root {lam : ℝ} (hl : 0 ≤ lam) (c : ℝ) :
    (Cm c ^ 2 - 1) * pm lam c ^ 2 + Qm lam c * pm lam c - 1 = 0 := by
  have hd := (den_pos hl c).ne'
  have hS := Sm_sq hl c
  unfold pm; field_simp; linear_combination (-1 : ℝ) * hS

/-- and the only positive root -/
lemma root_unique {lam c p : ℝ} (hl : 0 ≤ lam) (hp : 0 < p)
    (h : (Cm c ^ 2 - 1) * p ^ 2 + Qm lam c * p - 1 = 0) : p = pm lam c := by
  have h2 := pm_root hl c
  have hq := Qm_ge hl c; have hC := Cm_ge c; have hpm := pm_pos hl c
  have hfac : (p - pm lam c) * ((Cm c ^ 2 - 1) * (p + pm lam c) + Qm lam c) = 0 := by
    linear_combination h - h2
  have hC1 : 0 ≤ Cm c ^ 2 - 1 := by nlinarith
  have := mul_nonneg hC1 (by linarith : 0 ≤ p + pm lam c)
  have : 0 < (Cm c ^ 2 - 1) * (p + pm lam c) + Qm lam c := by linarith
  rcases mul_eq_zero.mp hfac with h0 | h0
  · linarith
  · linarith

/-- **Every clock c gives a solution with push fm(c).** -/
theorem exists_sol {lam c : ℝ} (hl : 0 ≤ lam) :
    Sol lam (fm lam c)
      (fun t => -Real.log (pm lam c + (1 - pm lam c) / Cm c * Real.cosh (c * (t - 1 / 2))))
      (fun t => -(((1 - pm lam c) / Cm c * (Real.sinh (c * (t - 1 / 2)) * c)) /
        (pm lam c + (1 - pm lam c) / Cm c * Real.cosh (c * (t - 1 / 2))))) := by
  have hp := pm_pos hl c
  have hp1 := pm_lt_one hl c
  have hC : 0 < Cm c := by linarith [Cm_ge c]
  have hroot := pm_root hl c
  have hfm : fm lam c = c ^ 2 * pm lam c := rfl
  unfold Qm at hroot
  set p := pm lam c with hpdef
  set C := Cm c with hCdef
  set b := (1 - p) / C with hbdef
  have hb : 0 < b := by rw [hbdef]; apply div_pos <;> linarith
  -- energy tie b^2 = p^2 + p lam
  have htie : b ^ 2 = p ^ 2 + p * lam := by
    rw [hbdef, div_pow]; field_simp
    linear_combination (-1 : ℝ) * hroot
  clear_value b C p
  have hu : ∀ t, 0 < p + b * Real.cosh (c * (t - 1 / 2)) := fun t => by
    have := Real.cosh_pos (c * (t - 1 / 2)); positivity
  have hs : ∀ t, HasDerivAt (fun t => c * (t - 1 / 2)) c t := fun t => by
    have h := ((hasDerivAt_id' t).sub_const (1 / 2)).const_mul c
    rwa [mul_one] at h
  refine ⟨fun t _ => ⟨?_, ?_⟩, ?_, ?_⟩
  · have hU := (((Real.hasDerivAt_cosh _).comp t (hs t)).const_mul b).const_add p
    have := (hU.log (hu t).ne').neg
    refine this.congr_deriv ?_
    simp only [Function.comp]
    try ring
  · have hU := (((Real.hasDerivAt_cosh _).comp t (hs t)).const_mul b).const_add p
    have hV := (((Real.hasDerivAt_sinh _).comp t (hs t)).mul_const c).const_mul b
    have := (hV.div hU (hu t).ne').neg
    refine this.congr_deriv ?_
    have hut := (hu t).ne'
    have e1 : Real.exp (-Real.log (p + b * Real.cosh (c * (t - 1 / 2)))) =
        (p + b * Real.cosh (c * (t - 1 / 2)))⁻¹ := by rw [Real.exp_neg, Real.exp_log (hu t)]
    have e2 : Real.exp (2 * -Real.log (p + b * Real.cosh (c * (t - 1 / 2)))) =
        ((p + b * Real.cosh (c * (t - 1 / 2)))⁻¹) ^ 2 := by
      rw [show 2 * -Real.log (p + b * Real.cosh (c * (t - 1 / 2))) =
        -Real.log (p + b * Real.cosh (c * (t - 1 / 2))) + -Real.log (p + b * Real.cosh (c * (t - 1 / 2))) by ring,
        Real.exp_add, e1]; ring
    have hcs := Real.cosh_sq_sub_sinh_sq (c * (t - 1 / 2))
    simp only [Function.comp, e1, e2, hfm]
    generalize Real.cosh (c * (t - 1 / 2)) = X at hut hcs ⊢
    generalize Real.sinh (c * (t - 1 / 2)) = Y at hcs ⊢
    rw [neg_inj, div_eq_iff (pow_ne_zero 2 hut)]
    have hr : c ^ 2 * p * ((p + b * X)⁻¹ + lam * ((p + b * X)⁻¹) ^ 2) * (p + b * X) ^ 2 =
        c ^ 2 * p * (p + b * X) + c ^ 2 * p * lam := by field_simp
    linear_combination (b ^ 2 * c ^ 2) * hcs + c ^ 2 * htie - hr
  · show -Real.log (p + b * Real.cosh (c * (0 - 1 / 2))) = 0
    rw [show c * (0 - 1 / 2) = -(c / 2) by ring, Real.cosh_neg]
    have : p + b * Real.cosh (c / 2) = 1 := by
      rw [hbdef, show Real.cosh (c / 2) = C by rw [hCdef, Cm], div_mul_cancel₀ _ hC.ne']
      try ring
    rw [this]; simp
  · show -Real.log (p + b * Real.cosh (c * (1 - 1 / 2))) = 0
    rw [show c * (1 - 1 / 2) = c / 2 by ring]
    have : p + b * Real.cosh (c / 2) = 1 := by
      rw [hbdef, show Real.cosh (c / 2) = C by rw [hCdef, Cm], div_mul_cancel₀ _ hC.ne']
      try ring
    rw [this]; simp

/-- **Every solution with mu > 0 sits on the curve: mu = fm(c) for some c > 0.** -/
theorem on_curve {lam μ : ℝ} {x x' : ℝ → ℝ} (h : Sol lam μ x x') (hμ : 0 < μ) (hl : 0 ≤ lam) :
    ∃ c : ℝ, 0 < c ∧ μ = fm lam c := by
  obtain ⟨c, um, hc, hum, h1, h2⟩ := mu_formula h hμ hl
  refine ⟨c, hc, ?_⟩
  have hc2 : 0 < c ^ 2 := by positivity
  set p := μ / c ^ 2 with hpdef
  have hp : 0 < p := by positivity
  have hμp : μ = c ^ 2 * p := by rw [hpdef]; field_simp
  clear_value p
  have hC : 0 < Cm c := by linarith [Cm_ge c]
  have h1' : (um - p) * Cm c = 1 - p := by rw [h1, Cm]; field_simp; ring
  have h2' : um ^ 2 = p * (2 * um + lam) := by
    rw [hμp] at h2
    have : c ^ 2 * (um ^ 2 - p * (2 * um + lam)) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · linarith
  have hq : (Cm c ^ 2 - 1) * p ^ 2 + Qm lam c * p - 1 = 0 := by
    unfold Qm; linear_combination (-(Cm c ^ 2)) * h2' + ((um - p) * Cm c + 1 - p) * h1'
  rw [hμp, fm, root_unique hl hp hq]

/-! The top of the curve. -/

lemma fm_cont {lam : ℝ} (hl : 0 ≤ lam) : Continuous (fm lam) := by
  have hd : Continuous (fun c => Qm lam c + Sm lam c) := by simp only [Sm, Qm, Cm]; fun_prop
  exact (continuous_pow 2).mul (continuous_const.div hd (fun c => (den_pos hl c).ne'))

lemma fm_zero (lam : ℝ) : fm lam 0 = 0 := by simp [fm]

lemma fm_pos {lam c : ℝ} (hl : 0 ≤ lam) (hc : 0 < c) : 0 < fm lam c := by
  unfold fm; have := pm_pos hl c; positivity

lemma fm_tail {lam c : ℝ} (hl : 0 ≤ lam) (hc : 0 < c) : fm lam c ≤ 768 / c ^ 2 := by
  have hC : 0 < Cm c := by linarith [Cm_ge c]
  have h4 : (c / 2) ^ 4 / 24 ≤ Real.exp (c / 2) := by
    have := Real.pow_div_factorial_le_exp (c / 2) (by positivity) 4
    simpa [Nat.factorial] using this
  have hcosh : Real.exp (c / 2) / 2 ≤ Cm c := by
    unfold Cm; rw [Real.cosh_eq]; have := Real.exp_pos (-(c / 2)); linarith
  have hCc : c ^ 4 / 768 ≤ Cm c := by nlinarith
  have hc4 : 0 < c ^ 4 / 768 := by positivity
  have hpm := pm_le hl c
  unfold fm
  calc c ^ 2 * pm lam c ≤ c ^ 2 * (1 / Cm c) := by gcongr
    _ ≤ c ^ 2 * (1 / (c ^ 4 / 768)) := by gcongr
    _ = 768 / c ^ 2 := by field_simp

/-- **The Morse bridge's break exists and is attained**, for every lam >= 0: the top of fm on (0, infinity). -/
theorem break_exists {lam : ℝ} (hl : 0 ≤ lam) :
    ∃ cs : ℝ, 0 < cs ∧ IsGreatest {μ : ℝ | ∃ x x' : ℝ → ℝ, Sol lam μ x x'} (fm lam cs) := by
  set f1 := fm lam 1
  have hf1 : 0 < f1 := fm_pos hl one_pos
  set R := 1 + 768 / f1
  have hR0 : 0 ≤ 768 / f1 := by positivity
  have hR : 1 ≤ R := by linarith
  obtain ⟨cs, hcs, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc 0 R)).exists_isMaxOn
    ⟨0, le_rfl, by linarith⟩ (fm_cont hl).continuousOn
  have hfcs : f1 ≤ fm lam cs := hmax ⟨zero_le_one, hR⟩
  have hcs0 : 0 < cs := by
    rcases eq_or_lt_of_le hcs.1 with h0 | h0
    · rw [← h0, fm_zero] at hfcs; linarith
    · exact h0
  refine ⟨cs, hcs0, ⟨_, _, exists_sol hl⟩, ?_⟩
  rintro μ ⟨x, x', h⟩
  rcases le_or_gt μ 0 with hμ | hμ
  · linarith
  obtain ⟨c, hc, rfl⟩ := on_curve h hμ hl
  rcases le_or_gt c R with hcR | hcR
  · exact hmax ⟨hc.le, hcR⟩
  · have ht := fm_tail hl hc
    have hc1 : 1 < c := by linarith
    have h7 : 768 / f1 < c := by linarith
    have h8 : 768 < c * f1 := by rwa [div_lt_iff₀ hf1] at h7
    have h9 : 768 < f1 * c ^ 2 := by nlinarith
    have : 768 / c ^ 2 < f1 := by rw [div_lt_iff₀ (by positivity)]; linarith
    linarith

end MorseOde
