import Mathlib
import Mistranslation.Pinch

open Set Real intervalIntegral Filter Topology MeasureTheory
open scoped Interval

/-! # The pinch fold: dT/dA, and existence of lam* (2026-10-23)

Companion to `Mistranslation/Pinch.lean`.

* `hasDerivAt_T` -- for every `lam > 0`, `A > 0`: `HasDerivAt (fun A => T (P lam) A) (D lam A) A`
  (differentiation under the integral sign; `Q >= 1` on `[0,1]` gives a uniform bound).
* `fold_transcendental` -- at a pinch point with `dT/dA = 0`, `4 T(A)^2` is transcendental.
* `chi`, `chi_root` -- in `s = sqrt(A/B)` the fold is `chi(s) = 0`,
  `chi(s) = 2s(8 - 25s^2 + 15s^4) - 15 s^2 (1-s^2)^2 log((1+s)/(1-s))`; IVT on `[0.51728, 0.51738]` with
  rigorous exp bounds (`L_upper`, `L_lower`).
* `lam_star_exists` -- a pinch point with `lam* in (0.0755, 0.0756)`, `dT/dA = 0`, transcendental push.

Prior art: time-map method (Laetsch 1970, Schaaf 1990); Hermite-Lindemann (1882).
NOT PROVED here: that the fold value is the break (global max of `4T^2` over all admissible `A`).
-/

namespace PinchBreak

open Pinch

lemma Qd_ge_one {lam A t : ℝ} (hlam : 0 < lam) (hA : 0 < A) (ht : t ∈ Icc (-1:ℝ) 1) :
    1 ≤ Qd lam A t := by
  unfold Qd P
  have h1 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hy : 0 ≤ A - A * t ^ 2 := by nlinarith
  generalize A - A * t ^ 2 = y at *
  have : 0 ≤ lam * (A ^ 2 + A * y + y ^ 2) / 3 := by positivity
  linarith

lemma QA_le {lam A t : ℝ} (hlam : 0 < lam) (hA : 0 < A) (ht : t ∈ Icc (-1:ℝ) 1) :
    0 ≤ QA lam A t ∧ QA lam A t ≤ 1 + 2 * lam * A := by
  unfold QA
  have h1 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hu : 0 ≤ 1 - t ^ 2 := by linarith
  have hu1 : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  generalize 1 - t ^ 2 = u at *
  have hla : 0 < lam * A := mul_pos hlam hA
  constructor
  · positivity
  · nlinarith [mul_nonneg hla.le hu, mul_nonneg hla.le (mul_nonneg hu hu), mul_nonneg hu (sub_nonneg.2 hu1),
      mul_nonneg hla.le (mul_nonneg hu (sub_nonneg.2 hu1))]

/-- Pointwise: `Dint` is the `A`-derivative of the time-map integrand. -/
lemma hasDerivAt_integrand {lam A t : ℝ} (hlam : 0 < lam) (hA : 0 < A) (ht : t ∈ Icc (-1:ℝ) 1) :
    HasDerivAt (fun A => TimeMap.integrand (P lam) A t) (Dint lam A t) A := by
  have hQ := Qd_ge_one hlam hA ht
  have hg : HasDerivAt (fun A => 2 * A * Qd lam A t) (2 * Qd lam A t + 2 * A * QA lam A t) A := by
    have := ((hasDerivAt_id A).const_mul 2).mul (hasDerivAt_Qd lam A t)
    convert this using 1
    · funext y; simp [Pi.mul_apply]; try ring
    · try simp
  have hg0 : 2 * A * Qd lam A t ≠ 0 := by positivity
  have hs := hg.sqrt hg0
  have := ((hasDerivAt_id A).const_mul 2).div hs (sqrt_pos.2 (by positivity)).ne'
  convert this using 1
  · funext y; simp [TimeMap.integrand, Qd]
  unfold Dint
  rw [sqrt_mul (by positivity)]
  have ha := sq_sqrt (show 0 ≤ 2 * A by positivity)
  have hq := sq_sqrt (show 0 ≤ Qd lam A t by positivity)
  have ha0 : 0 < sqrt (2 * A) := sqrt_pos.2 (by positivity)
  have hq0 : 0 < sqrt (Qd lam A t) := sqrt_pos.2 (by positivity)
  generalize sqrt (2 * A) = a at *
  generalize sqrt (Qd lam A t) = q at *
  generalize Qd lam A t = Q at *
  generalize QA lam A t = B at *
  have hA' : A = a ^ 2 / 2 := by linarith
  subst hA' hq
  simp only [id]
  field_simp
  ring

/-- **`D` is the derivative.** `dT/dA = D(lam, A)` for every `A > 0` (differentiation under the integral). -/
theorem hasDerivAt_T {lam A : ℝ} (hlam : 0 < lam) (hA : 0 < A) :
    HasDerivAt (fun A => TimeMap.T (P lam) A) (D lam A) A := by
  have hIoc : ∀ t ∈ Ι (0:ℝ) 1, t ∈ Icc (-1:ℝ) 1 := by
    intro t ht; rw [uIoc_of_le zero_le_one] at ht; exact ⟨by linarith [ht.1], ht.2⟩
  set C : ℝ := 1 / sqrt (A) + sqrt (2 * (2 * A)) * (1 + 2 * lam * (2 * A)) / 2
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun x t => TimeMap.integrand (P lam) x t) (F' := fun x t => Dint lam x t)
    (x₀ := A) (s := Ioo (A / 2) (2 * A)) (bound := fun _ => C) (a := 0) (b := 1)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun x => by
      apply Measurable.aestronglyMeasurable
      unfold TimeMap.integrand P; fun_prop)
    (by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hQ := Qd_ge_one hlam hA ⟨by linarith [ht.1], ht.2⟩
      apply ContinuousAt.continuousWithinAt
      unfold TimeMap.integrand
      refine ContinuousAt.div continuousAt_const ?_ ?_
      · unfold P; fun_prop
      · have : 0 < 2 * A * Qd lam A t := by positivity
        exact (sqrt_pos.2 this).ne')
    (by apply Measurable.aestronglyMeasurable; unfold Dint Qd QA P; fun_prop)
    (Eventually.of_forall fun t ht x hx => by
      have ht' := hIoc t ht
      have hx0 : 0 < x := by linarith [hx.1]
      have hQ := Qd_ge_one hlam hx0 ht'
      have hQA := QA_le hlam hx0 ht'
      simp only [Dint, Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      have t1 : 0 ≤ 1 / sqrt (2 * x * Qd lam x t) := by positivity
      have t2 : 0 ≤ sqrt (2 * x) * QA lam x t / (2 * Qd lam x t * sqrt (Qd lam x t)) := by
        have := hQA.1; positivity
      rw [abs_of_nonneg t1, abs_of_nonneg t2]
      have hb1 : 1 / sqrt (2 * x * Qd lam x t) ≤ 1 / sqrt A :=
        one_div_le_one_div_of_le (sqrt_pos.2 hA) (sqrt_le_sqrt (by nlinarith [hx.1]))
      have h2le : (2:ℝ) ≤ 2 * Qd lam x t * sqrt (Qd lam x t) := by
        have : 1 ≤ sqrt (Qd lam x t) := by rw [show (1:ℝ) = sqrt 1 by simp]; exact sqrt_le_sqrt hQ
        nlinarith
      have hb2 : sqrt (2 * x) * QA lam x t / (2 * Qd lam x t * sqrt (Qd lam x t))
          ≤ sqrt (2 * (2 * A)) * (1 + 2 * lam * (2 * A)) / 2 := by
        calc _ ≤ sqrt (2 * x) * QA lam x t / 2 :=
              div_le_div_of_nonneg_left (by have := hQA.1; positivity) (by norm_num) h2le
          _ ≤ _ := by
              gcongr
              · exact hQA.1
              · nlinarith [hx.2]
              · nlinarith [hQA.2, hx.2, mul_pos hlam hx0]
      exact add_le_add hb1 hb2)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht x hx =>
      hasDerivAt_integrand hlam (by linarith [hx.1]) (hIoc t ht))
  exact key.2

/-- **Transcendence at the fold.** At a pinch point where `dT/dA = 0`, the push `4 T(A)^2` is transcendental. -/
theorem fold_transcendental {lam A r : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hr : lam * r ^ 2 + r + 1 = 0)
    (hF : F lam A = F lam r) (hfold : deriv (fun A => TimeMap.T (P lam) A) A = 0) :
    Transcendental ℚ (4 * TimeMap.T (P lam) A ^ 2) :=
  crit_transcendental hlam hA hr hF (by rw [← (hasDerivAt_T hlam hA).deriv]; exact hfold)

/-! ## Existence of `lam*`: the `s`-parametrisation of the pinch curve -/

/-- The fold function in `s = sqrt(A/B)`: zero iff `dT/dA = 0` at the pinch point of parameter `s`. -/
noncomputable def chi (s : ℝ) : ℝ :=
  2 * s * (8 - 25 * s ^ 2 + 15 * s ^ 4) - 15 * s ^ 2 * (1 - s ^ 2) ^ 2 * (log (1 + s) - log (1 - s))

lemma L_upper : log (1 + 0.51728) - log (1 - 0.51728) < 2291 / 2000 := by
  rw [← log_div (by norm_num) (by norm_num), log_lt_iff_lt_exp (by norm_num)]
  refine lt_of_lt_of_le ?_ (sum_le_exp_of_nonneg (by norm_num) 12)
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma L_lower : 11453 / 10000 < log (1 + 0.51738) - log (1 - 0.51738) := by
  rw [← log_div (by norm_num) (by norm_num), lt_log_iff_exp_lt (by norm_num)]
  have h1 := exp_one_lt_d9
  have h2 := exp_bound' (x := 1453 / 10000) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  have h3 : exp (11453 / 10000 : ℝ) = exp 1 * exp (1453 / 10000) := by rw [← exp_add]; norm_num
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  rw [h3]
  calc exp 1 * exp (1453 / 10000) ≤ 2.7182818286 * exp (1453 / 10000) := by gcongr
    _ < _ := by nlinarith [exp_pos (1453 / 10000 : ℝ)]

lemma chi_s1 : 0 < chi 0.51728 := by
  unfold chi
  have := L_upper
  nlinarith

lemma chi_s2 : chi 0.51738 < 0 := by
  unfold chi
  have := L_lower
  nlinarith

lemma chi_cont : ContinuousOn chi (Icc 0.51728 0.51738) := by
  unfold chi
  have h1 : ContinuousOn (fun s : ℝ => log (1 + s)) (Icc 0.51728 0.51738) :=
    (continuousOn_const.add continuousOn_id).log (fun s hs => by show (1:ℝ) + s ≠ 0; norm_num at hs; linarith [hs.1])
  have h2 : ContinuousOn (fun s : ℝ => log (1 - s)) (Icc 0.51728 0.51738) :=
    (continuousOn_const.sub continuousOn_id).log (fun s hs => by show (1:ℝ) - s ≠ 0; norm_num at hs; linarith [hs.2])
  exact (by fun_prop : Continuous fun s : ℝ => 2 * s * (8 - 25 * s ^ 2 + 15 * s ^ 4)).continuousOn.sub
    ((by fun_prop : Continuous fun s : ℝ => 15 * s ^ 2 * (1 - s ^ 2) ^ 2).continuousOn.mul (h1.sub h2))

lemma chi_root : ∃ s ∈ Icc (0.51728 : ℝ) 0.51738, chi s = 0 := by
  have := intermediate_value_Icc' (by norm_num) chi_cont ⟨chi_s2.le, chi_s1.le⟩
  obtain ⟨s, hs, h⟩ := this
  exact ⟨s, hs, h⟩

/-- **Existence of `lam*`.** There is a pinch point with `lam* ∈ (0.0755, 0.0756)` at which the fold
`dT/dA = 0` holds; its push `4 T(A*)^2` is transcendental. -/
theorem lam_star_exists : ∃ lam A r : ℝ, 0.0755 < lam ∧ lam < 0.0756 ∧ 0 < A ∧
    lam * r ^ 2 + r + 1 = 0 ∧ F lam A = F lam r ∧
    deriv (fun A => TimeMap.T (P lam) A) A = 0 ∧ Transcendental ℚ (4 * TimeMap.T (P lam) A ^ 2) := by
  obtain ⟨s, hs, hchi⟩ := chi_root
  norm_num at hs
  obtain ⟨hs1, hs2⟩ := hs
  have hv1 : (0.51728:ℝ) ^ 2 ≤ s ^ 2 := by nlinarith
  have hv2 : s ^ 2 ≤ (0.51738:ℝ) ^ 2 := by nlinarith
  norm_num at hv1 hv2
  have h13 : 0 < 1 - 3 * s ^ 2 := by linarith
  have h1v : 0 < 1 - s ^ 2 := by linarith
  have h23 : 0 < 2 - 3 * s ^ 2 := by linarith
  have hs0 : 0 < s := by linarith
  have hp1 : 0 < 2 * (2 - 3 * s ^ 2) - (1 - 3 * s ^ 2) := by linarith
  have hp2 : 0 < 2 * (2 - 3 * s ^ 2) - 2 * (1 - 3 * s ^ 2) := by linarith
  have hp4 : 0 < 2 * (2 - 3 * s ^ 2) - 4 * (1 - 3 * s ^ 2) := by nlinarith
  obtain ⟨lam, hlamd⟩ : ∃ x : ℝ, x = 3 * (1 - s ^ 2) * (1 - 3 * s ^ 2) / (4 * (2 - 3 * s ^ 2) ^ 2) := ⟨_, rfl⟩
  obtain ⟨p, hpd⟩ : ∃ x : ℝ, x = 2 * (2 - 3 * s ^ 2) / (1 - 3 * s ^ 2) := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ x : ℝ, x = 2 * s ^ 2 * (2 - 3 * s ^ 2) / ((1 - 3 * s ^ 2) * (1 - s ^ 2)) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ x : ℝ, x = 2 * (2 - 3 * s ^ 2) / ((1 - 3 * s ^ 2) * (1 - s ^ 2)) := ⟨_, rfl⟩
  have hlam : 0 < lam := by rw [hlamd]; positivity
  have hA : 0 < A := by rw [hAd]; positivity
  have hB : 0 < B := by rw [hBd]; positivity
  have hp4' : 4 < p := by rw [hpd, lt_div_iff₀ h13]; linarith
  have hr : lam * (-p) ^ 2 + -p + 1 = 0 := by rw [hlamd, hpd]; field_simp; ring
  have hF : F lam A = F lam (-p) := by rw [hlamd, hAd, hpd]; unfold F; field_simp; ring
  have hAB : A - -p = B := by rw [hAd, hpd, hBd]; field_simp; ring
  have hl : lam = (p - 1) / p ^ 2 := by rw [hlamd, hpd]; field_simp; ring
  have e1 : p - 1 = 3 * (1 - s ^ 2) / (1 - 3 * s ^ 2) := by rw [hpd]; field_simp; ring
  have e2 : p - 2 = 2 / (1 - 3 * s ^ 2) := by rw [hpd]; field_simp; ring
  have e4 : p - 4 = 6 * s ^ 2 / (1 - 3 * s ^ 2) := by rw [hpd]; field_simp; ring
  have hA' : A = p * (p - 4) / (2 * (p - 1)) := by
    rw [e1, e4, hAd, hpd]; field_simp; ring
  have hD : D lam A = 0 := by
    rw [D_closed hlam hA hr hF, neg_neg, j0_val hp4' hl hA', j1_val hp4' hl hA', hAB]
    have hsA : sqrt A = s * sqrt B := by
      rw [show A = s ^ 2 * B by rw [hAd, hBd]; ring, sqrt_mul (sq_nonneg s), sqrt_sq hs0.le]
    have hsB := sq_sqrt hB.le
    have hsB0 : 0 < sqrt B := sqrt_pos.2 hB
    have hLg : Lg A B = log (1 + s) - log (1 - s) := by
      unfold Lg; rw [hsA, show sqrt B + s * sqrt B = (1 + s) * sqrt B by ring,
        show sqrt B - s * sqrt B = (1 - s) * sqrt B by ring, log_mul (by linarith) hsB0.ne',
        log_mul (by linarith) hsB0.ne']; ring
    rw [hLg, hsA]
    unfold chi at hchi
    generalize log (1 + s) - log (1 - s) = L at *
    apply mul_eq_zero_of_right
    rw [show 2 * (s * sqrt B) * sqrt B = 2 * s * B by linear_combination (2 * s) * hsB]
    have key : (2 * p ^ 2 + 7 * p - 12) / (8 * p ^ 2 * (p - 2) * (p - 4))
        + -5 * (p - 1) / (8 * p * (p - 2)) * (L / (2 * s * B))
        = (1 - 3 * s ^ 2) ^ 2 / (128 * s ^ 3 * (2 - 3 * s ^ 2) ^ 2) *
          (2 * s * (8 - 25 * s ^ 2 + 15 * s ^ 4) - 15 * s ^ 2 * (1 - s ^ 2) ^ 2 * L) := by
      rw [e1, e2, e4, hpd, hBd]; field_simp; ring
    rw [key, hchi, mul_zero]
  have hfold : deriv (fun A => TimeMap.T (P lam) A) A = 0 := by
    rw [(hasDerivAt_T hlam hA).deriv]; exact hD
  refine ⟨lam, A, -p, ?_, ?_, hA, hr, hF, hfold, fold_transcendental hlam hA hr hF hfold⟩
  · rw [hlamd, lt_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (s ^ 2 - 0.2676821), mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hv2)]
  · rw [hlamd, div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg (s ^ 2 - 0.2675786), mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hv2)]

end PinchBreak

#print axioms PinchBreak.hasDerivAt_integrand
#print axioms PinchBreak.hasDerivAt_T
#print axioms PinchBreak.fold_transcendental
#print axioms PinchBreak.L_upper
#print axioms PinchBreak.L_lower
#print axioms PinchBreak.chi_root
#print axioms PinchBreak.lam_star_exists
