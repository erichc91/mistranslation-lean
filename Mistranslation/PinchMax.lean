import Mathlib
import Mistranslation.PinchBreak
import Mistranslation.TimeMapExists

/-! # The lam* seat: its break is transcendental (2026-10-23)

Seat `x'' + mu (1 + x + lam x^2) = 0`, `x(0) = x(1) = 0`, at the pinch fold `lam* in (0.0755, 0.0756)` of
`Mistranslation/PinchBreak.lean`.

* `tangent` -- for `g(A) = A / (1 + aA + bA^2)`: exact identity
  `g - g0 - g0' (A - A0) = -(A - A0)^2 (a + b(2A0 + A) - b^2 A A0^2) / (Q Q0^2)`, plus `sqrt x <= sqrt y + (x-y)/(2 sqrt y)`,
  gives a tangent-line bound for the integrand `sqrt(2A/Q)` whenever `b^2 A A0^2 <= a + b(2A0 + A)`.
* `pointwise_le` -- the condition holds for every `t` when `A <= 7`, `A0 in [4.4, 4.5]`, `lam < 0.0756`.
* `pointwise_tail` -- for `A >= 7` each integrand is below its value at `7` (`7 b A >= 1`).
* `T_le` -- integrating (with `D(lam, A0) = 0`): `T(A) <= T(A0)` for every `A > 0`.
* `break_lam_star` -- `IsGreatest` of the push set (positive solutions) is `4 T(A*)^2`, and it is transcendental
  (packaging: `push_eq_time_map`, `time_map_exists`, `lam_star_exists`).

Prior art: time-map method (Laetsch 1970, Schaaf 1990); Hermite-Lindemann (1882).
-/

open Set Real intervalIntegral

namespace PinchMax

open Pinch

/-- Tangent-line bound for `sqrt(2A / Q(A))`, `Q(A) = 1 + aA + bA^2`, valid when
`b^2 A A0^2 <= a + b(2A0 + A)` (exact identity: `g - g0 - g0'(A - A0) = -(A-A0)^2 [..] / (Q Q0^2)`). -/
lemma tangent {a b A A0 : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hA : 0 < A) (hA0 : 0 < A0)
    (hc : b ^ 2 * A * A0 ^ 2 ≤ a + b * (2 * A0 + A)) :
    sqrt (2 * A / (1 + a * A + b * A ^ 2)) ≤ sqrt (2 * A0 / (1 + a * A0 + b * A0 ^ 2))
      + ((1 + a * A0 + b * A0 ^ 2) - A0 * (a + 2 * b * A0))
        / ((1 + a * A0 + b * A0 ^ 2) ^ 2 * sqrt (2 * A0 / (1 + a * A0 + b * A0 ^ 2))) * (A - A0) := by
  have hQ : 0 < 1 + a * A + b * A ^ 2 := by positivity
  have hQ0 : 0 < 1 + a * A0 + b * A0 ^ 2 := by positivity
  set Q := 1 + a * A + b * A ^ 2 with hQd
  set Q0 := 1 + a * A0 + b * A0 ^ 2 with hQ0d
  set x := 2 * A / Q
  set y := 2 * A0 / Q0
  have hx : 0 ≤ x := by positivity
  have hy : 0 < y := by positivity
  have hsy : 0 < sqrt y := sqrt_pos.2 hy
  have h1 : sqrt x ≤ sqrt y + (x - y) / (2 * sqrt y) := by
    have e1 := sq_sqrt hx; have e2 := sq_sqrt hy.le
    generalize sqrt x = X at *
    generalize sqrt y = Y at *
    rw [← e1, ← e2]
    have : Y + (X ^ 2 - Y ^ 2) / (2 * Y) - X = (X - Y) ^ 2 / (2 * Y) := by field_simp; ring
    nlinarith [div_nonneg (sq_nonneg (X - Y)) (by positivity : (0:ℝ) ≤ 2 * Y)]
  have h2 : x - y ≤ 2 * ((Q0 - A0 * (a + 2 * b * A0)) / Q0 ^ 2) * (A - A0) := by
    have key : x - y - 2 * ((Q0 - A0 * (a + 2 * b * A0)) / Q0 ^ 2) * (A - A0)
        = -(2 * (A - A0) ^ 2 * (a + b * (2 * A0 + A) - b ^ 2 * A * A0 ^ 2)) / (Q * Q0 ^ 2) := by
      simp only [x, y, hQd, hQ0d]; field_simp; ring
    have : -(2 * (A - A0) ^ 2 * (a + b * (2 * A0 + A) - b ^ 2 * A * A0 ^ 2)) / (Q * Q0 ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (A - A0)]) (by positivity)
    linarith
  calc sqrt x ≤ sqrt y + (x - y) / (2 * sqrt y) := h1
    _ ≤ sqrt y + 2 * ((Q0 - A0 * (a + 2 * b * A0)) / Q0 ^ 2) * (A - A0) / (2 * sqrt y) := by
        gcongr
    _ = _ := by field_simp

lemma Qd_eq (lam A t : ℝ) : Qd lam A t = 1 + ((1 + (1 - t ^ 2)) / 2) * A
    + (lam * (1 + (1 - t ^ 2) + (1 - t ^ 2) ^ 2) / 3) * A ^ 2 := by unfold Qd P; ring

lemma QA_eq (lam A t : ℝ) : QA lam A t = (1 + (1 - t ^ 2)) / 2
    + 2 * (lam * (1 + (1 - t ^ 2) + (1 - t ^ 2) ^ 2) / 3) * A := by unfold QA; ring

lemma integrand_eq {lam A t : ℝ} (hlam : 0 < lam) (hA : 0 < A) (ht : t ∈ Icc (-1:ℝ) 1) :
    TimeMap.integrand (P lam) A t = sqrt (2 * A / Qd lam A t) := by
  have hQ := PinchBreak.Qd_ge_one hlam hA ht
  show 2 * A / sqrt (2 * A * Qd lam A t) = _
  rw [sqrt_div (by positivity), sqrt_mul (by positivity)]
  have h1 := sq_sqrt (show 0 ≤ 2 * A by positivity)
  have : 0 < sqrt (2 * A) := sqrt_pos.2 (by positivity)
  have : 0 < sqrt (Qd lam A t) := sqrt_pos.2 (by positivity)
  generalize sqrt (2 * A) = a at *
  generalize sqrt (Qd lam A t) = q at *
  rw [← h1]; field_simp

lemma Dint_eq {lam A t : ℝ} (hlam : 0 < lam) (hA : 0 < A) (ht : t ∈ Icc (-1:ℝ) 1) :
    Dint lam A t = (Qd lam A t - A * QA lam A t) / (Qd lam A t ^ 2 * sqrt (2 * A / Qd lam A t)) := by
  have hQ := PinchBreak.Qd_ge_one hlam hA ht
  unfold Dint
  rw [sqrt_div (by positivity), sqrt_mul (by positivity)]
  have h1 := sq_sqrt (show 0 ≤ 2 * A by positivity)
  have h2 := sq_sqrt (show 0 ≤ Qd lam A t by positivity)
  have : 0 < sqrt (2 * A) := sqrt_pos.2 (by positivity)
  have : 0 < sqrt (Qd lam A t) := sqrt_pos.2 (by positivity)
  generalize sqrt (2 * A) = a at *
  generalize sqrt (Qd lam A t) = q at *
  generalize Qd lam A t = Q at *
  subst h2
  have hA' : A = a ^ 2 / 2 := by linarith
  subst hA'
  field_simp

/-- Pointwise tangent bound at the fold peak `A0`, for `A ∈ (0, 7]`. -/
lemma pointwise_le {lam A A0 t : ℝ} (hlam : 0 < lam) (hl : lam < 0.0756) (hA : 0 < A) (hA7 : A ≤ 7)
    (hA01 : 4.4 ≤ A0) (hA02 : A0 ≤ 4.5) (ht : t ∈ Icc (0:ℝ) 1) :
    TimeMap.integrand (P lam) A t ≤ TimeMap.integrand (P lam) A0 t + Dint lam A0 t * (A - A0) := by
  have ht' : t ∈ Icc (-1:ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have hA0 : 0 < A0 := by linarith
  rw [integrand_eq hlam hA ht', integrand_eq hlam hA0 ht', Dint_eq hlam hA0 ht', Qd_eq, Qd_eq, QA_eq]
  have hu0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hu1 : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  generalize 1 - t ^ 2 = u at *
  set a := (1 + u) / 2 with had
  set b := lam * (1 + u + u ^ 2) / 3 with hbd
  have ha : 0 < a := by positivity
  have hb : 0 ≤ b := by positivity
  have hb_le : b ≤ lam := by
    rw [hbd]; nlinarith [mul_nonneg hlam.le (show 0 ≤ 2 - u - u ^ 2 by nlinarith)]
  have h3b : 3 * b ≤ 4 * lam * a := by
    rw [hbd, had]; nlinarith [mul_nonneg hlam.le (show 0 ≤ 1 + u - u ^ 2 by nlinarith)]
  have e1 : b * A ≤ 0.0756 * 7 := mul_le_mul (hb_le.trans hl.le) hA7 hA.le (by norm_num)
  have e2 : A0 ^ 2 ≤ 20.25 := by nlinarith
  have e3 : b * A * A0 ^ 2 ≤ 0.0756 * 7 * 20.25 := mul_le_mul e1 e2 (by positivity) (by norm_num)
  have e5 : 9.9 * b ≤ a := by nlinarith [mul_le_mul_of_nonneg_right hl.le ha.le]
  have hc : b ^ 2 * A * A0 ^ 2 ≤ a + b * (2 * A0 + A) := by
    nlinarith [mul_le_mul_of_nonneg_left e3 hb, mul_nonneg hb hA.le]
  have := tangent ha hb hA hA0 hc
  convert this using 2

/-- Tail: for `A >= 7` (and `lam >= 0.0755`) the integrand is below its value at `7`. -/
lemma pointwise_tail {lam A t : ℝ} (hl : 0.0755 < lam) (hA7 : 7 ≤ A) (ht : t ∈ Icc (0:ℝ) 1) :
    TimeMap.integrand (P lam) A t ≤ TimeMap.integrand (P lam) 7 t := by
  have hlam : 0 < lam := by linarith
  have ht' : t ∈ Icc (-1:ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  rw [integrand_eq hlam (by linarith) ht', integrand_eq hlam (by norm_num) ht', Qd_eq, Qd_eq]
  have hu0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hu1 : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  generalize 1 - t ^ 2 = u at *
  apply sqrt_le_sqrt
  have hb : lam / 3 ≤ lam * (1 + u + u ^ 2) / 3 := by nlinarith [mul_nonneg hlam.le (add_nonneg hu0 (sq_nonneg u))]
  set a := (1 + u) / 2
  set b := lam * (1 + u + u ^ 2) / 3
  have ha : 0 < a := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hA7) (show 0 ≤ 7 * b * A - 1 by nlinarith)]

lemma integrand_cont {lam A : ℝ} (hlam : 0 < lam) (hA : 0 < A) :
    IntervalIntegrable (TimeMap.integrand (P lam) A) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hQ := PinchBreak.Qd_ge_one hlam hA ⟨by linarith [ht.1], ht.2⟩
  apply ContinuousAt.continuousWithinAt
  unfold TimeMap.integrand
  refine ContinuousAt.div continuousAt_const ?_ ?_
  · unfold P; fun_prop
  · have : 0 < 2 * A * Qd lam A t := by positivity
    exact (sqrt_pos.2 this).ne'

lemma Dint_cont {lam A : ℝ} (hlam : 0 < lam) (hA : 0 < A) :
    IntervalIntegrable (Dint lam A) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hQ := PinchBreak.Qd_ge_one hlam hA ⟨by linarith [ht.1], ht.2⟩
  apply ContinuousAt.continuousWithinAt
  have cQ : Continuous fun t => Qd lam A t := by unfold Qd P; fun_prop
  have cQA : Continuous fun t => QA lam A t := by unfold QA; fun_prop
  unfold Dint
  refine ContinuousAt.sub (ContinuousAt.div continuousAt_const ?_ ?_) (ContinuousAt.div ?_ ?_ ?_)
  · exact (continuous_sqrt.comp (continuous_const.mul cQ)).continuousAt
  · have : 0 < 2 * A * Qd lam A t := by positivity
    exact (sqrt_pos.2 this).ne'
  · exact (continuous_const.mul cQA).continuousAt
  · exact ((continuous_const.mul cQ).mul (continuous_sqrt.comp cQ)).continuousAt
  · have : 0 < sqrt (Qd lam A t) := sqrt_pos.2 (by positivity)
    positivity

/-- **The fold peak is the global maximum of `T`.** -/
theorem T_le {lam A0 : ℝ} (hl1 : 0.0755 < lam) (hl2 : lam < 0.0756) (hA01 : 4.4 ≤ A0) (hA02 : A0 ≤ 4.5)
    (hD : D lam A0 = 0) {A : ℝ} (hA : 0 < A) : TimeMap.T (P lam) A ≤ TimeMap.T (P lam) A0 := by
  have hlam : 0 < lam := by linarith
  have hA0 : 0 < A0 := by linarith
  have core : ∀ B, 0 < B → B ≤ 7 → TimeMap.T (P lam) B ≤ TimeMap.T (P lam) A0 := by
    intro B hB hB7
    have h := intervalIntegral.integral_mono_on zero_le_one (integrand_cont hlam hB)
      ((integrand_cont hlam hA0).add ((Dint_cont hlam hA0).mul_const (B - A0)))
      (fun t ht => pointwise_le hlam hl2 hB hB7 hA01 hA02 ht)
    rw [integral_add (integrand_cont hlam hA0) ((Dint_cont hlam hA0).mul_const (B - A0)),
      integral_mul_const] at h
    unfold TimeMap.T
    have : ∫ t in (0:ℝ)..1, Dint lam A0 t = 0 := hD
    rw [this] at h; simpa using h
  rcases le_or_gt A 7 with h7 | h7
  · exact core A hA h7
  · refine le_trans ?_ (core 7 (by norm_num) le_rfl)
    exact intervalIntegral.integral_mono_on zero_le_one (integrand_cont hlam hA)
      (integrand_cont hlam (by norm_num)) (fun t ht => pointwise_tail hl1 h7.le ht)

/-- The fold peak of `lam_star_exists` lies in `[4.4, 4.5]`. -/
lemma A_bounds {lam A r : ℝ} (hl1 : 0.0755 < lam) (hl2 : lam < 0.0756) (hA : 0 < A)
    (hr : lam * r ^ 2 + r + 1 = 0) (hF : F lam A = F lam r) : 4.4 ≤ A ∧ A ≤ 4.5 := by
  have hlam : 0 < lam := by linarith
  obtain ⟨hp, hl, hA'⟩ := pinch_param hlam hA hr hF
  generalize -r = p at *
  have hp0 : 0 < p := by linarith
  have hq : lam * p ^ 2 = p - 1 := by rw [hl]; field_simp
  have hp1 : 12.1 ≤ p := by
    by_contra h; push Not at h
    nlinarith [mul_pos (sub_pos.2 hp) (sub_pos.2 h), mul_lt_mul_of_pos_right hl2 (by positivity : (0:ℝ) < p ^ 2)]
  have hp2 : p ≤ 12.2 := by
    by_contra h; push Not at h
    nlinarith [mul_lt_mul_of_pos_right hl1 (by positivity : (0:ℝ) < p ^ 2)]
  rw [hA']
  constructor
  · rw [le_div_iff₀ (by linarith)]; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

lemma hasDerivAt_F (lam y : ℝ) : HasDerivAt (fun x => F lam x) (1 + y + lam * y ^ 2) y := by
  unfold F
  have := ((hasDerivAt_id y).add ((hasDerivAt_pow 2 y).div_const 2)).add
    (((hasDerivAt_pow 3 y).const_mul lam).div_const 3)
  convert this using 1
  · funext x; simp only [Pi.add_apply, id]
  · norm_num; ring

lemma P_pos {lam A y : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A) (hy : y ∈ Icc 0 A) : 0 < P lam A y := by
  unfold P
  have := mul_nonneg hA hy.1
  have : 0 ≤ lam * (A ^ 2 + A * y + y ^ 2) / 3 := by
    have : 0 ≤ A ^ 2 + A * y + y ^ 2 := by positivity
    positivity
  linarith [hy.1]

/-- **The break of the `lam*` seat is transcendental.** There is `lam* ∈ (0.0755, 0.0756)` such that the
set of pushes `mu > 0` admitting a positive solution of `x'' + mu (1 + x + lam* x^2) = 0`, `x(0) = x(1) = 0`,
has a greatest element, and that greatest element (the break `4 T(A*)^2`) is transcendental. -/
theorem break_lam_star : ∃ lam : ℝ, 0.0755 < lam ∧ lam < 0.0756 ∧ ∃ μs : ℝ,
    IsGreatest {μ : ℝ | 0 < μ ∧ ∃ v v' : ℝ → ℝ,
      TippingRule.Sol (fun y => 1 + y + lam * y ^ 2) μ v v' ∧ ∀ t ∈ Ioo (0:ℝ) 1, 0 < v t} μs ∧
    Transcendental ℚ μs := by
  obtain ⟨lam, A, r, hl1, hl2, hA, hr, hF, hfold, htr⟩ := PinchBreak.lam_star_exists
  have hlam : 0 < lam := by linarith
  have hD : D lam A = 0 := by rw [← (PinchBreak.hasDerivAt_T hlam hA).deriv]; exact hfold
  obtain ⟨hA1, hA2⟩ := A_bounds hl1 hl2 hA hr hF
  have hTpos : ∀ B, 0 ≤ B → 0 ≤ TimeMap.T (P lam) B := fun B hB =>
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => div_nonneg (by positivity) (sqrt_nonneg _))
  refine ⟨lam, hl1, hl2, 4 * TimeMap.T (P lam) A ^ 2, ⟨?_, ?_⟩, htr⟩
  · obtain ⟨x, x', hsol, hpos, -, -⟩ := TimeMapExists.time_map_exists (f := fun y => 1 + y + lam * y ^ 2)
      (F := fun x => F lam x) (P := P lam) (hasDerivAt_F lam) (factor lam A)
      (by unfold P; fun_prop) hA (fun y hy => P_pos hlam hA.le hy)
    refine ⟨?_, x, x', hsol, hpos⟩
    have : 0 < TimeMap.T (P lam) A := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on (integrand_cont hlam hA) _ zero_lt_one
      intro t ht
      have hQ := PinchBreak.Qd_ge_one hlam hA ⟨by linarith [ht.1], ht.2.le⟩
      have : 0 < 2 * A * Qd lam A t := by positivity
      exact div_pos (by positivity) (sqrt_pos.2 this)
    positivity
  · rintro μ ⟨hμ, v, v', hsol, hpos⟩
    have hcont : ContinuousOn v (Icc 0 1) := fun t ht => (hsol.1 t ht).1.continuousAt.continuousWithinAt
    obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one) hcont
    have hAm : 0 < v t0 := lt_of_lt_of_le (hpos (1/2) ⟨by norm_num, by norm_num⟩)
      (hmax ⟨by norm_num, by norm_num⟩)
    have hμeq := TimeMap.push_eq_time_map (f := fun y => 1 + y + lam * y ^ 2) (F := fun x => F lam x)
      (P := P lam) (by fun_prop) (hasDerivAt_F lam) (factor lam (v t0)) (by unfold P; fun_prop)
      (fun y hy => P_pos hlam hAm.le hy) hμ hsol hpos (fun t ht => hmax ht) ⟨t0, ht0, rfl⟩
    rw [hμeq]
    have h1 := T_le hl1 hl2 hA1 hA2 hD hAm
    have h0 := hTpos (v t0) hAm.le
    nlinarith

end PinchMax

#print axioms PinchMax.tangent
#print axioms PinchMax.pointwise_le
#print axioms PinchMax.pointwise_tail
#print axioms PinchMax.T_le
#print axioms PinchMax.A_bounds
#print axioms PinchMax.break_lam_star
