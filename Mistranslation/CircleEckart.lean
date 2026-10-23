import Mathlib
import Mistranslation.TimeMap

/-! # The circle Eckart seat reduced to the time map (2026-10-23)

Seat (v4/sql/precision_pass4.sql): `v'' = mu (cos v / sin^3 v + lam / sin^2 v)` on `[0,1]`,
`v(0) = v(1) = pi/3`. The force has poles at `v = 0, pi`, so `TimeMap.push_eq_time_map`
(global hypotheses) does not apply directly.

* `push_eq_time_map_local` -- the time-map theorem with hypotheses only on `[0, A]`:
  `F' = f` and `f` continuous on `[0, A]`, the seat's own factor `P(A, y) = dslope F A y`
  (the divided difference) positive on `[0, A]`, `0 <= x <= A` with peak `A > 0`. Proof: extend
  `f` by clamping to `[0, A]`, rebuild `F` as `F 0 + ∫ f`, check the divided differences agree on
  `[0, A]`, derive `x > 0` on `(0,1)` from energy, and apply `push_eq_time_map`.
* `Circle.circle_push_eq_time_map` -- with `y = pi/3 - v` the seat is `y'' + mu f(y) = 0`,
  `f(y) = g(pi/3 - y)`, `F(y) = 1/(2 sin^2(pi/3 - y)) + lam cot(pi/3 - y)` (= `Fce`). Every solution
  with `0 < v <= pi/3` on `[0,1]` (`lam >= 0`, `mu > 0`) has a turning point `vm` in `(0, pi/3)`
  and push `mu = 4 T(pi/3 - vm)^2` with `P = Circle.P lam` (the divided difference of `F`).
  No extra hypotheses: positivity of `P` is proved (the force is positive on `(0, pi/3]`).
* `Circle.circle_tip_reduction` -- consequently `mu` is algebraic iff `T(pi/3 - vm)` is.
  At the break (`lam = 1`, `mu* = 0.629387218175` numerically) `mu*` is algebraic iff
  `T(A*)` is. Whether `T(A*)` can be algebraic is OPEN; nothing is assumed about it.
-/

open Set Filter Topology MeasureTheory

namespace CircleEckart

open TimeMap

/-- **Local time map.** Hypotheses only on `[0, A]`; `P` is the divided difference of `F`. -/
theorem push_eq_time_map_local {f F : ℝ → ℝ} {A μ : ℝ} {x x' : ℝ → ℝ}
    (hF : ∀ y ∈ Icc 0 A, HasDerivAt F (f y) y) (hf : ContinuousOn f (Icc 0 A))
    (hP : ∀ y ∈ Icc 0 A, 0 < dslope F A y) (hA : 0 < A)
    (hμ : 0 < μ) (hsol : TippingRule.Sol f μ x x')
    (hnn : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ x t)
    (hmax : ∀ t ∈ Icc (0:ℝ) 1, x t ≤ A) (hpeak : ∃ t₀ ∈ Icc (0:ℝ) 1, x t₀ = A) :
    μ = 4 * T (fun a => dslope F a) A ^ 2 := by
  obtain ⟨t₀, ht₀, hxt₀⟩ := hpeak
  set cl : ℝ → ℝ := fun y => max 0 (min y A) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ y, cl y ∈ Icc 0 A := fun y => ⟨le_max_left _ _, max_le hA.le (min_le_right _ _)⟩
  have hcle : ∀ y ∈ Icc 0 A, cl y = y := fun y hy => by simp [hcl, hy.1, hy.2]
  set fe : ℝ → ℝ := fun y => f (cl y) with hfe
  have hfec : Continuous fe := hf.comp_continuous hclc hclm
  have hfe_eq : ∀ y ∈ Icc 0 A, fe y = f y := fun y hy => by simp only [hfe, hcle y hy]
  set Fe : ℝ → ℝ := fun y => F 0 + ∫ r in (0:ℝ)..y, fe r with hFe
  have hFed : ∀ y, HasDerivAt Fe (fe y) y := fun y =>
    (intervalIntegral.integral_hasDerivAt_right (hfec.intervalIntegrable _ _)
      (hfec.stronglyMeasurableAtFilter _ _) hfec.continuousAt).const_add _
  have hFe_eq : ∀ y ∈ Icc 0 A, Fe y = F y := by
    intro y hy
    have hsub : uIcc 0 y ⊆ Icc 0 A := uIcc_subset_Icc ⟨le_rfl, hA.le⟩ hy
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (f' := fe)
      (fun r hr => by rw [hfe_eq r (hsub hr)]; exact hF r (hsub hr)) (hfec.intervalIntegrable _ _)
    simp only [hFe, this]; ring
  have hAmem : A ∈ Icc 0 A := ⟨hA.le, le_rfl⟩
  have hds_eq : ∀ y ∈ Icc 0 A, dslope Fe A y = dslope F A y := by
    intro y hy
    by_cases hyA : y = A
    · rw [hyA, dslope_same, dslope_same, (hFed A).deriv, (hF A hAmem).deriv, hfe_eq A hAmem]
    · rw [dslope_of_ne _ hyA, dslope_of_ne _ hyA, slope_def_field, slope_def_field,
        hFe_eq y hy, hFe_eq A hAmem]
  have hPc : Continuous (dslope Fe A) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    by_cases h : y = A
    · rw [h]; exact continuousAt_dslope_same.mpr (hFed A).differentiableAt
    · exact (continuousAt_dslope_of_ne h).mpr (hFed y).continuousAt
  have hFP : ∀ y, Fe A - Fe y = (A - y) * dslope Fe A y := by
    intro y
    have := sub_smul_dslope Fe A y
    rw [smul_eq_mul] at this
    linear_combination this
  have hsol' : TippingRule.Sol fe μ x x' :=
    ⟨fun t ht => ⟨(hsol.1 t ht).1, by
      rw [hfe_eq _ ⟨hnn t ht, hmax t ht⟩]; exact (hsol.1 t ht).2⟩, hsol.2⟩
  have ht₀i : t₀ ∈ Ioo (0:ℝ) 1 := by
    refine ⟨lt_of_le_of_ne ht₀.1 ?_, lt_of_le_of_ne ht₀.2 ?_⟩
    · rintro rfl; rw [hsol.2.1] at hxt₀; linarith
    · rintro rfl; rw [hsol.2.2] at hxt₀; linarith
  have hpos : ∀ t ∈ Ioo (0:ℝ) 1, 0 < x t := by
    intro t ht
    have htI := Ioo_subset_Icc_self ht
    rcases (hnn t htI).lt_or_eq with h | h
    · exact h
    exfalso
    have hmin : IsLocalMin x t := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [← h]; exact hnn s (Ioo_subset_Icc_self hs)
    have hx't := hmin.hasDerivAt_eq_zero (hsol.1 t htI).1
    have hmx : IsLocalMax x t₀ := by
      filter_upwards [Ioo_mem_nhds ht₀i.1 ht₀i.2] with s hs
      rw [hxt₀]; exact hmax s (Ioo_subset_Icc_self hs)
    have hx't₀ := hmx.hasDerivAt_eq_zero (hsol.1 t₀ ht₀).1
    have e1 := energy hFed hsol' t htI
    have e0 := energy hFed hsol' t₀ ht₀
    rw [hx't, ← h] at e1
    rw [hx't₀, hxt₀] at e0
    have hp0 : 0 < dslope Fe A 0 := by
      rw [hds_eq 0 ⟨le_rfl, hA.le⟩]; exact hP 0 ⟨le_rfl, hA.le⟩
    have hd : 0 < Fe A - Fe 0 := by rw [hFP 0, sub_zero]; exact mul_pos hA hp0
    have := mul_pos (mul_pos two_pos hμ) hd
    linarith
  have hmain := push_eq_time_map (f := fe) (F := Fe) (P := fun a => dslope Fe a) hfec hFed hFP hPc
    (fun y hy => by rw [hds_eq y hy]; exact hP y hy) hμ hsol' hpos hmax ⟨t₀, ht₀, hxt₀⟩
  have hT : T (fun a => dslope Fe a) A = T (fun a => dslope F a) A := by
    unfold T
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    have harg : A - A * s ^ 2 ∈ Icc 0 A := ⟨by nlinarith, by nlinarith [sq_nonneg s]⟩
    simp only [integrand]
    rw [hds_eq _ harg]
  rw [hmain, hT]

namespace Circle

/-- The end value `pi/3`. -/
noncomputable def vb : ℝ := Real.pi / 3

/-- The circle Eckart force in `v`. -/
noncomputable def g (lam v : ℝ) : ℝ := Real.cos v / Real.sin v ^ 3 + lam / Real.sin v ^ 2

/-- The force in the shifted variable `y = pi/3 - v`. -/
noncomputable def f (lam y : ℝ) : ℝ := g lam (vb - y)

/-- The energy in `y` (`Fce(pi/3 - y)` of precision_pass4.sql): `F' = f`. -/
noncomputable def Fy (lam y : ℝ) : ℝ :=
  1 / (2 * Real.sin (vb - y) ^ 2) + lam * (Real.cos (vb - y) / Real.sin (vb - y))

/-- The circle seat's own factor: the divided difference `P(A, y) = (F(A) - F(y)) / (A - y)`. -/
noncomputable def P (lam : ℝ) : ℝ → ℝ → ℝ := fun a => dslope (Fy lam) a

lemma vb_pos : 0 < vb := by unfold vb; positivity

lemma trig_pos {z : ℝ} (hz0 : 0 ≤ z) (hz : z < vb) :
    0 < Real.sin (vb - z) ∧ 0 < Real.cos (vb - z) := by
  have hpi := Real.pi_pos
  have hvb : vb = Real.pi / 3 := rfl
  constructor
  · exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

lemma hasDerivAt_Fy (lam y : ℝ) (hs : Real.sin (vb - y) ≠ 0) :
    HasDerivAt (Fy lam) (f lam y) y := by
  have hw : HasDerivAt (fun y => vb - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub vb
  have hsd := hw.sin
  have hcd := hw.cos
  have h1 := (hasDerivAt_const y (1:ℝ)).div ((hsd.pow 2).const_mul 2)
    (mul_ne_zero two_ne_zero (pow_ne_zero _ hs))
  have h2 := (hcd.div hsd hs).const_mul lam
  have h := h1.add h2
  refine h.congr_deriv ?_
  have hsc := Real.sin_sq_add_cos_sq (vb - y)
  simp only [Pi.pow_apply, f, g]
  field_simp
  linear_combination (2 * lam * Real.sin (vb - y) ^ 2) * hsc

lemma f_pos {lam z : ℝ} (hlam : 0 ≤ lam) (hz0 : 0 ≤ z) (hz : z < vb) : 0 < f lam z := by
  obtain ⟨hs, hc⟩ := trig_pos hz0 hz
  unfold f g
  exact add_pos_of_pos_of_nonneg (div_pos hc (pow_pos hs 3)) (div_nonneg hlam (sq_nonneg _))

lemma P_pos {lam A : ℝ} (hlam : 0 ≤ lam) (hA : A < vb) :
    ∀ y ∈ Icc 0 A, 0 < P lam A y := by
  intro y hy
  have hd : ∀ z ∈ Icc 0 A, HasDerivAt (Fy lam) (f lam z) z := fun z hz =>
    hasDerivAt_Fy lam z (trig_pos hz.1 (by linarith [hz.2])).1.ne'
  rcases hy.2.lt_or_eq with hlt | heq
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (Fy lam) (f lam) hlt
      (fun z hz => (hd z ⟨by linarith [hz.1, hy.1], hz.2⟩).continuousAt.continuousWithinAt)
      (fun z hz => hd z ⟨by linarith [hz.1, hy.1], hz.2.le⟩)
    have hfc := f_pos hlam (by linarith [hc.1, hy.1]) (by linarith [hc.2] : c < vb)
    simp only [P]
    rw [dslope_of_ne _ hlt.ne, slope_def_field, ← neg_sub (Fy lam A), ← neg_sub A,
      neg_div_neg_eq, ← hcd]
    exact hfc
  · simp only [P]
    rw [heq, dslope_same, (hd A ⟨by linarith [hy.1], le_rfl⟩).deriv]
    exact f_pos hlam (by linarith [hy.1]) hA

/-- **Circle Eckart = time map.** Every solution of `v'' = mu g(v)`, `v(0) = v(1) = pi/3`, with
`0 < v <= pi/3` on `[0,1]` (`lam >= 0`, `mu > 0`) has its turning point `vm` in `(0, pi/3)` and
push `mu = 4 T(pi/3 - vm)^2`, `T` built from the seat's own factor `P lam`. -/
theorem circle_push_eq_time_map {lam μ : ℝ} {v v' : ℝ → ℝ} (hlam : 0 ≤ lam) (hμ : 0 < μ)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (v' t) t ∧ HasDerivAt v' (μ * g lam (v t)) t)
    (h0 : v 0 = vb) (h1 : v 1 = vb) (hvpos : ∀ t ∈ Icc (0:ℝ) 1, 0 < v t)
    (hvle : ∀ t ∈ Icc (0:ℝ) 1, v t ≤ vb) :
    ∃ vm, 0 < vm ∧ vm < vb ∧ (∃ t₀ ∈ Icc (0:ℝ) 1, v t₀ = vm) ∧
      (∀ t ∈ Icc (0:ℝ) 1, vm ≤ v t) ∧ μ = 4 * T (P lam) (vb - vm) ^ 2 := by
  have hvc : ContinuousOn v (Icc 0 1) := fun t ht => (hd t ht).1.continuousAt.continuousWithinAt
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hvc
  set vm := v t₀ with hvm
  have hvmin : ∀ t ∈ Icc (0:ℝ) 1, vm ≤ v t := fun t ht => hmin ht
  -- shifted solution
  set x : ℝ → ℝ := fun t => vb - v t with hx
  set x' : ℝ → ℝ := fun t => -v' t with hx'
  have hsol : TippingRule.Sol (f lam) μ x x' := by
    refine ⟨fun t ht => ⟨(hd t ht).1.const_sub vb, ?_⟩, by simp [hx, h0], by simp [hx, h1]⟩
    refine (hd t ht).2.neg.congr_deriv ?_
    simp only [hx, f, sub_sub_cancel]
  have hf0 : 0 < f lam 0 := f_pos hlam le_rfl vb_pos
  -- the turning point is strictly below pi/3
  have hvmlt : vm < vb := by
    by_contra hcon
    have hconst : ∀ t ∈ Icc (0:ℝ) 1, x t = 0 := fun t ht => by
      simp only [hx]; linarith [hvle t ht, hvmin t ht, hvle t₀ ht₀]
    have hx'0 : ∀ t ∈ Ioo (0:ℝ) 1, x' t = 0 := by
      intro t ht
      have hev : (fun _ => (0:ℝ)) =ᶠ[𝓝 t] x := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        exact (hconst s (Ioo_subset_Icc_self hs)).symm
      exact ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hev.symm).unique
        (hsol.1 t (Ioo_subset_Icc_self ht)).1 |>.symm
    have hhalf : (1/2 : ℝ) ∈ Ioo (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hev : x' =ᶠ[𝓝 (1/2)] fun _ => (0:ℝ) := by
      filter_upwards [Ioo_mem_nhds hhalf.1 hhalf.2] with s hs
      exact hx'0 s hs
    have hd2 := (hsol.1 (1/2) (Ioo_subset_Icc_self hhalf)).2
    have := ((hasDerivAt_const (1/2 : ℝ) (0:ℝ)).congr_of_eventuallyEq hev).unique hd2
    rw [hconst _ (Ioo_subset_Icc_self hhalf)] at this
    have := mul_pos hμ hf0
    linarith
  have hvm0 : 0 < vm := hvpos t₀ ht₀
  have hA : 0 < vb - vm := by linarith
  have hAlt : vb - vm < vb := by linarith
  have hfc : ContinuousOn (f lam) (Icc 0 (vb - vm)) := by
    intro y hy
    obtain ⟨hs, _⟩ := trig_pos hy.1 (by linarith [hy.2] : y < vb)
    have hsc : Continuous fun y => Real.sin (vb - y) := by fun_prop
    have hcc : Continuous fun y => Real.cos (vb - y) := by fun_prop
    exact ((hcc.continuousAt.div (hsc.pow 3).continuousAt (pow_ne_zero _ hs.ne')).add
      (continuousAt_const.div (hsc.pow 2).continuousAt (pow_ne_zero _ hs.ne'))).continuousWithinAt
  refine ⟨vm, hvm0, hvmlt, ⟨t₀, ht₀, rfl⟩, hvmin, ?_⟩
  exact push_eq_time_map_local (F := Fy lam)
    (fun y hy => hasDerivAt_Fy lam y (trig_pos hy.1 (by linarith [hy.2])).1.ne') hfc
    (P_pos hlam hAlt) hA hμ hsol
    (fun t ht => by simp only [hx]; linarith [hvle t ht])
    (fun t ht => by simp only [hx]; linarith [hvmin t ht])
    ⟨t₀, ht₀, rfl⟩

/-- **Circle tip reduction.** For every such solution, `mu` is algebraic iff `T(pi/3 - vm)` is.
At the break (`lam = 1`, `mu* = 4 T(A*)^2`, numerically `0.629387218175`) `mu*` is algebraic
iff `T(A*)` is. OPEN, NOT ASSUMED: whether `T(A*)` -- the period-type integral at the turning
point selected by the fold `T'(A*) = 0` -- can be algebraic. -/
theorem circle_tip_reduction {lam μ : ℝ} {v v' : ℝ → ℝ} (hlam : 0 ≤ lam) (hμ : 0 < μ)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (v' t) t ∧ HasDerivAt v' (μ * g lam (v t)) t)
    (h0 : v 0 = vb) (h1 : v 1 = vb) (hvpos : ∀ t ∈ Icc (0:ℝ) 1, 0 < v t)
    (hvle : ∀ t ∈ Icc (0:ℝ) 1, v t ≤ vb) :
    ∃ vm, 0 < vm ∧ vm < vb ∧ (∃ t₀ ∈ Icc (0:ℝ) 1, v t₀ = vm) ∧
      (IsAlgebraic ℚ μ ↔ IsAlgebraic ℚ (T (P lam) (vb - vm))) := by
  obtain ⟨vm, h1', h2', h3', -, h5⟩ := circle_push_eq_time_map hlam hμ hd h0 h1 hvpos hvle
  exact ⟨vm, h1', h2', h3', alg_iff h5⟩

end Circle

end CircleEckart

#print axioms CircleEckart.push_eq_time_map_local
#print axioms CircleEckart.Circle.hasDerivAt_Fy
#print axioms CircleEckart.Circle.P_pos
#print axioms CircleEckart.Circle.circle_push_eq_time_map
#print axioms CircleEckart.Circle.circle_tip_reduction
