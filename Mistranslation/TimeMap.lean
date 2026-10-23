import Mathlib
import Mistranslation.TippingRule

/-! # The time map: one hypothesis-free theorem for every polynomial seat (2026-10-23)

Seat `x'' + mu f(x) = 0` on `[0,1]`, `x(0) = x(1) = 0`, `F' = f`. For a peak `A > 0` write
`F(A) - F(y) = (A - y) P(A, y)` (`P(A, .)` continuous; for polynomial `F` it is the polynomial quotient,
`poly_factor`). The cancellation-free half time is

    T(A) = ∫_0^1 2A / sqrt(2A P(A, A - A s^2)) ds     (proper Riemann integral when P(A, .) > 0 on [0, A]).

Prior art: time-map / quadrature method (Gelfand 1963, Laetsch 1970). What this file adds: one
machine-checked theorem, no stand-in hypotheses, covering every polynomial seat at once.

* `push_eq_time_map` -- every solution with `x > 0` on `(0,1)`, `mu > 0`, peak `A`, `P(A, .) > 0` on
  `[0, A]` satisfies `mu = 4 T(A)^2`. Route: energy `x'^2 = 2 mu (A - x) P(A, x)`; the signed phase
  `s = x' / sqrt(2 mu A P(A, x))` has `s^2 = 1 - x/A`, `s(0) = 1`, `s(1) = -1`; `G(s(t)) + sqrt(mu) t` is
  constant (`G` = primitive of the integrand) off the countable set of peak touches (isolated by
  Rolle, `peak_set_countable`); evenness of the integrand gives `sqrt mu = 2 T(A)`.
* `poly_push_eq_time_map` -- the same, specialised to `f = p'`, `F = p` for any real polynomial `p`.
* `tip_reduction` / `tip_reduction_break` -- `mu = 4 T^2` is algebraic iff `T` is.

NOT PROVED here: the converse (every `A` with `P(A, .) > 0` on `[0, A]` is realised by a solution).
-/

open Set Filter Topology MeasureTheory

namespace TimeMap

/-- The cancellation-free half-time integrand `2A / sqrt(2A P(A, A - A s^2))`. -/
noncomputable def integrand (P : ℝ → ℝ → ℝ) (A s : ℝ) : ℝ :=
  2 * A / Real.sqrt (2 * A * P A (A - A * s ^ 2))

/-- The half time `T(A) = ∫_0^1 2A / sqrt(2A P(A, A - A s^2)) ds`. -/
noncomputable def T (P : ℝ → ℝ → ℝ) (A : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, integrand P A s

lemma const_on {a b : ℝ} {f : ℝ → ℝ} (h : ∀ t ∈ Icc a b, HasDerivAt f 0 t) :
    ∀ t ∈ Icc a b, f t = f a := by
  apply constant_of_has_deriv_right_zero
  · intro t ht; exact (h t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (h t (Ico_subset_Icc_self ht)).hasDerivWithinAt

/-- Energy `x'^2 + 2 mu F(x)` is conserved along a solution. -/
lemma energy {f F : ℝ → ℝ} (hF : ∀ y, HasDerivAt F (f y) y) {μ : ℝ} {x x' : ℝ → ℝ}
    (h : TippingRule.Sol f μ x x') :
    ∀ t ∈ Icc (0 : ℝ) 1, x' t * x' t + 2 * μ * F (x t) = x' 0 * x' 0 + 2 * μ * F (x 0) := by
  refine const_on (f := fun t => x' t * x' t + 2 * μ * F (x t)) ?_
  intro s hs
  obtain ⟨hd, hdd⟩ := h.1 s hs
  have h2 : HasDerivAt (fun t => F (x t)) (f (x s) * x' s) s := (hF (x s)).comp s hd
  exact ((hdd.mul hdd).add (h2.const_mul (2 * μ))).congr_deriv (by ring)

/-- The force at the peak is the factor at the diagonal: `f A = P(A, A)`. -/
lemma f_eq_P {f F q : ℝ → ℝ} {A : ℝ} (hF : HasDerivAt F (f A) A)
    (hFP : ∀ y, F A - F y = (A - y) * q y) (hq : ContinuousAt q A) : f A = q A := by
  have h1 := hasDerivAt_iff_tendsto_slope.mp hF
  have h2 : Tendsto q (𝓝[≠] A) (𝓝 (q A)) := hq.tendsto.mono_left nhdsWithin_le_nhds
  have h3 : slope F A =ᶠ[𝓝[≠] A] q := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y - A ≠ 0 := sub_ne_zero.mpr hy
    rw [slope_def_field]
    have := hFP y
    field_simp
    linarith
  exact tendsto_nhds_unique (h1.congr' h3) h2

/-- Peak touches are isolated (Rolle on `x'`, since `x'' = -mu f(A) < 0` near a touch), so the
set of interior times where `x = A` is countable. -/
lemma peak_set_countable {f : ℝ → ℝ} (hf : Continuous f) {μ A : ℝ} (hμ : 0 < μ) {x x' : ℝ → ℝ}
    (hsol : TippingRule.Sol f μ x x') (hfA : 0 < f A)
    (hzero : ∀ t ∈ Ioo (0:ℝ) 1, x t = A → x' t = 0) :
    {t | t ∈ Ioo (0:ℝ) 1 ∧ x t = A}.Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  refine IsDiscrete.of_nhdsWithin fun t ht => ?_
  rw [Filter.le_pure_iff, mem_nhdsWithin_iff_eventually]
  have hc : ContinuousAt (fun s => f (x s)) t :=
    hf.continuousAt.comp (hsol.1 t (Ioo_subset_Icc_self ht.1)).1.continuousAt
  have hft : 0 < f (x t) := by rw [ht.2]; exact hfA
  have hev : ∀ᶠ s in 𝓝 t, 0 < f (x s) ∧ s ∈ Ioo (0:ℝ) 1 :=
    (hc.eventually (lt_mem_nhds hft)).and (Ioo_mem_nhds ht.1.1 ht.1.2)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have key : ∀ a b, a < b → dist a t < ε → dist b t < ε → x' a = 0 → x' b = 0 → False := by
    intro a b hab ha hb hxa hxb
    have hin : ∀ c ∈ Icc a b, dist c t < ε := by
      intro c hc
      rw [Real.dist_eq, abs_lt] at ha hb ⊢
      constructor <;> linarith [hc.1, hc.2]
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope x' (fun s => -(μ * f (x s))) hab
      (fun s hs => (hsol.1 s (Ioo_subset_Icc_self (hball (hin s hs)).2)).2.continuousAt.continuousWithinAt)
      (fun s hs => (hsol.1 s (Ioo_subset_Icc_self (hball (hin s (Ioo_subset_Icc_self hs))).2)).2)
    rw [hxa, hxb, sub_self, zero_div] at hcd
    have h1 := (hball (hin c (Ioo_subset_Icc_self hc))).1
    have h2 : 0 < μ * f (x c) := mul_pos hμ h1
    linarith
  filter_upwards [Metric.ball_mem_nhds t hε] with s hs hsZ
  have h0 := hzero t ht.1 ht.2
  have h1 := hzero s hsZ.1 hsZ.2
  rcases lt_trichotomy s t with h | h | h
  · exact (key s t h hs (by simpa using hε) h1 h0).elim
  · exact h
  · exact (key t s h (by simpa using hε) hs h0 h1).elim

/-- **Push = time map.** Every positive solution with peak `A` (and `P(A, .) > 0` on `[0, A]`) has
`mu = 4 T(A)^2`. -/
theorem push_eq_time_map {f F : ℝ → ℝ} {P : ℝ → ℝ → ℝ} {A μ : ℝ} {x x' : ℝ → ℝ}
    (hf : Continuous f) (hF : ∀ y, HasDerivAt F (f y) y)
    (hFP : ∀ y, F A - F y = (A - y) * P A y) (hPc : Continuous (P A))
    (hP : ∀ y ∈ Icc 0 A, 0 < P A y)
    (hμ : 0 < μ) (hsol : TippingRule.Sol f μ x x')
    (hpos : ∀ t ∈ Ioo (0:ℝ) 1, 0 < x t)
    (hmax : ∀ t ∈ Icc (0:ℝ) 1, x t ≤ A) (hpeak : ∃ t₀ ∈ Icc (0:ℝ) 1, x t₀ = A) :
    μ = 4 * T P A ^ 2 := by
  set q := P A with hq
  obtain ⟨t₀, ht₀, hxt₀⟩ := hpeak
  have mem : ∀ t ∈ Ioo (0:ℝ) 1, t ∈ Icc (0:ℝ) 1 := fun t ht => Ioo_subset_Icc_self ht
  have hnn : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ x t := by
    intro t ht
    rcases ht.1.eq_or_lt with h | h
    · rw [← h, hsol.2.1]
    rcases ht.2.eq_or_lt with h' | h'
    · rw [h', hsol.2.2]
    exact (hpos t ⟨h, h'⟩).le
  have hA : 0 < A := by
    have := hpos (1/2) ⟨by norm_num, by norm_num⟩
    have := hmax (1/2) ⟨by norm_num, by norm_num⟩; linarith
  have ht₀i : t₀ ∈ Ioo (0:ℝ) 1 := by
    refine ⟨lt_of_le_of_ne ht₀.1 ?_, lt_of_le_of_ne ht₀.2 ?_⟩
    · rintro rfl; rw [hsol.2.1] at hxt₀; linarith
    · rintro rfl; rw [hsol.2.2] at hxt₀; linarith
  have hlocmax : ∀ t ∈ Ioo (0:ℝ) 1, x t = A → x' t = 0 := by
    intro t ht hxt
    have : IsLocalMax x t := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [hxt]; exact hmax s (mem s hs)
    exact this.hasDerivAt_eq_zero (hsol.1 t (mem t ht)).1
  -- energy: x'^2 = 2 mu (A - x) q(x)
  have hE : ∀ t ∈ Icc (0:ℝ) 1, x' t ^ 2 = 2 * μ * ((A - x t) * q (x t)) := by
    intro t ht
    have e1 := energy hF hsol t ht
    have e0 := energy hF hsol t₀ (mem _ ht₀i)
    rw [hlocmax t₀ ht₀i hxt₀, hxt₀] at e0
    rw [hq, ← hFP]; linear_combination e1 - e0
  have hqpos : ∀ t ∈ Icc (0:ℝ) 1, 0 < q (x t) := fun t ht => hP _ ⟨hnn t ht, hmax t ht⟩
  have hDpos : ∀ t ∈ Icc (0:ℝ) 1, 0 < Real.sqrt (2 * μ * A * q (x t)) := fun t ht =>
    Real.sqrt_pos.mpr (by have := hqpos t ht; positivity)
  -- the signed phase s = x' / sqrt(2 mu A q(x)), with s^2 = 1 - x/A
  set s : ℝ → ℝ := fun t => x' t / Real.sqrt (2 * μ * A * q (x t)) with hs
  have hs2 : ∀ t ∈ Icc (0:ℝ) 1, s t ^ 2 = 1 - x t / A := by
    intro t ht
    have hq0 := hqpos t ht
    simp only [hs, div_pow]
    rw [Real.sq_sqrt (by positivity), hE t ht]
    field_simp
  have hxs : ∀ t ∈ Icc (0:ℝ) 1, x' t = s t * Real.sqrt (2 * μ * A * q (x t)) := by
    intro t ht; exact (div_mul_cancel₀ _ (hDpos t ht).ne').symm
  have hxc : ContinuousOn x (Icc 0 1) := fun t ht => (hsol.1 t ht).1.continuousAt.continuousWithinAt
  have hx'c : ContinuousOn x' (Icc 0 1) :=
    fun t ht => (hsol.1 t ht).2.continuousAt.continuousWithinAt
  have hsc : ContinuousOn s (Icc 0 1) := by
    refine hx'c.div ?_ (fun t ht => (hDpos t ht).ne')
    exact Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul (hPc.comp_continuousOn hxc))
  have hsI : ∀ t ∈ Icc (0:ℝ) 1, s t ∈ Icc (-1:ℝ) 1 := by
    intro t ht
    have h1 : s t ^ 2 ≤ 1 := by
      rw [hs2 t ht]; have := div_nonneg (hnn t ht) hA.le; linarith
    exact abs_le.mp (sq_le_one_iff_abs_le_one _ |>.mp h1)
  -- the integrand g and its primitive G
  set g := integrand P A with hg
  have hgarg : ∀ r ∈ Icc (-1:ℝ) 1, A - A * r ^ 2 ∈ Icc 0 A := by
    intro r hr
    have : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
    constructor <;> nlinarith [sq_nonneg r]
  have hgpos : ∀ r ∈ Icc (-1:ℝ) 1, 0 < g r := by
    intro r hr
    have := hP _ (hgarg r hr)
    exact div_pos (by positivity) (Real.sqrt_pos.mpr (by positivity))
  have hgcont : ContinuousOn g (Icc (-1) 1) := by
    refine continuousOn_const.div ?_ ?_
    · exact Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul
        ((hPc.comp (continuous_const.sub (continuous_const.mul (continuous_pow 2)))).continuousOn))
    · intro r hr; have := hP _ (hgarg r hr)
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have hgint : ∀ u ∈ Icc (-1:ℝ) 1, IntervalIntegrable g volume 0 u := fun u hu =>
    (hgcont.mono (uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ hu)).intervalIntegrable
  set G : ℝ → ℝ := fun u => ∫ r in (0:ℝ)..u, g r with hG
  have hGd : ∀ u ∈ Ioo (-1:ℝ) 1, HasDerivAt G (g u) u := fun u hu =>
    intervalIntegral.integral_hasDerivAt_right (hgint u (Ioo_subset_Icc_self hu))
      ((hgcont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo u hu)
      (hgcont.continuousAt (Icc_mem_nhds hu.1 hu.2))
  have hGc : ContinuousOn G (Icc (-1) 1) := by
    have := intervalIntegral.continuousOn_primitive_interval' (a := 0)
      ((hgcont.mono (uIcc_subset_Icc ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩)).intervalIntegrable
        (μ := volume)) (show (0:ℝ) ∈ uIcc (-1) 1 by rw [uIcc_of_le (by norm_num)]; constructor <;> norm_num)
    rwa [uIcc_of_le (by norm_num)] at this
  -- the touch set is countable
  have hfA : 0 < f A := by
    rw [f_eq_P (hF A) hFP hPc.continuousAt]; exact hP A ⟨hA.le, le_rfl⟩
  have hZ := peak_set_countable hf hμ hsol hfA hlocmax
  -- H = G(s) + sqrt(mu) t has derivative 0 off the touch set
  set H : ℝ → ℝ := fun t => G (s t) + Real.sqrt μ * t with hH
  have hHc : ContinuousOn H (Icc 0 1) :=
    (hGc.comp hsc (fun t ht => hsI t ht)).add (continuousOn_const.mul continuousOn_id)
  have hHd : ∀ t ∈ Ioo (0:ℝ) 1 \ {t | t ∈ Ioo (0:ℝ) 1 ∧ x t = A}, HasDerivAt H 0 t := by
    rintro t ⟨ht, htZ⟩
    have htI := mem t ht
    have hxlt : x t < A := lt_of_le_of_ne (hmax t htI) (fun h => htZ ⟨ht, h⟩)
    have hqt := hqpos t htI
    have hx'ne : x' t ≠ 0 := by
      intro h0
      have e := hE t htI
      rw [h0] at e
      have : 0 < 2 * μ * ((A - x t) * q (x t)) := by
        have : 0 < A - x t := by linarith
        positivity
      nlinarith
    have hsIoo : s t ∈ Ioo (-1:ℝ) 1 := by
      have h1 : s t ^ 2 < 1 := by
        rw [hs2 t htI]; have := div_pos (hpos t ht) hA; linarith
      exact abs_lt.mp (sq_lt_one_iff_abs_lt_one _ |>.mp h1)
    have hrad : 1 - x t / A ≠ 0 := by
      have : x t / A < 1 := (div_lt_one hA).mpr hxlt
      linarith
    have hr := (((hsol.1 t htI).1.div_const A).const_sub 1).sqrt hrad
    have hrs : Real.sqrt (1 - x t / A) = |s t| := by
      rw [← hs2 t htI, Real.sqrt_sq_eq_abs]
    have hx'cont := (hsol.1 t htI).2.continuousAt
    have hsd : HasDerivAt s (-(x' t) / (2 * A * s t)) t := by
      rcases lt_or_gt_of_ne hx'ne with hneg | hposd
      · have hst : s t < 0 := div_neg_of_neg_of_pos hneg (hDpos t htI)
        have h1 := hr.neg.congr_of_eventuallyEq (f₁ := s) (by
          filter_upwards [hx'cont.eventually (gt_mem_nhds hneg), Ioo_mem_nhds ht.1 ht.2] with u hu1 hu2
          have hsu : s u < 0 := div_neg_of_neg_of_pos hu1 (hDpos u (mem u hu2))
          rw [Pi.neg_apply, ← hs2 u (mem u hu2), Real.sqrt_sq_eq_abs, abs_of_neg hsu, neg_neg])
        refine h1.congr_deriv ?_
        rw [hrs, abs_of_neg hst]
        field_simp
      · have hst : 0 < s t := div_pos hposd (hDpos t htI)
        have h1 := hr.congr_of_eventuallyEq (f₁ := s) (by
          filter_upwards [hx'cont.eventually (lt_mem_nhds hposd), Ioo_mem_nhds ht.1 ht.2] with u hu1 hu2
          have hsu : 0 < s u := div_pos hu1 (hDpos u (mem u hu2))
          rw [← hs2 u (mem u hu2), Real.sqrt_sq_eq_abs, abs_of_pos hsu])
        refine h1.congr_deriv ?_
        rw [hrs, abs_of_pos hst]
        field_simp
    have hstne : s t ≠ 0 := by
      intro h0; apply hx'ne; rw [hxs t htI, h0, zero_mul]
    have hsum := ((hGd (s t) hsIoo).comp t hsd).add ((hasDerivAt_id t).const_mul (Real.sqrt μ))
    refine hsum.congr_deriv ?_
    have harg : A - A * s t ^ 2 = x t := by rw [hs2 t htI]; field_simp; ring
    have hgst : g (s t) = 2 * A / Real.sqrt (2 * A * q (x t)) := by
      simp only [hg, integrand, hq]; rw [harg]
    have hS : 0 < Real.sqrt (2 * A * q (x t)) := Real.sqrt_pos.mpr (by positivity)
    have hsqrt : Real.sqrt (2 * μ * A * q (x t)) = Real.sqrt μ * Real.sqrt (2 * A * q (x t)) := by
      rw [← Real.sqrt_mul hμ.le]; ring_nf
    rw [hgst, hxs t htI, hsqrt]
    field_simp
    ring
  have hint := integral_eq_of_hasDerivAt_off_countable_of_le H (fun _ => (0:ℝ)) zero_le_one hZ hHc
    hHd intervalIntegrable_const
  simp only [intervalIntegral.integral_zero, hH] at hint
  have h01 : G (s 1) + Real.sqrt μ = G (s 0) := by linarith
  have hs0 : s 0 ^ 2 = 1 := by rw [hs2 0 ⟨le_rfl, zero_le_one⟩, hsol.2.1]; simp
  have hs1 : s 1 ^ 2 = 1 := by rw [hs2 1 ⟨zero_le_one, le_rfl⟩, hsol.2.2]; simp
  have hG1 : G 1 = T P A := rfl
  have hGm1 : G (-1) = - T P A := by
    have e : (∫ r in (0:ℝ)..(-1), g r) = ∫ r in (0:ℝ)..(-1), g (-r) :=
      intervalIntegral.integral_congr (fun r _ => by simp [hg, integrand])
    simp only [hG]
    rw [e, intervalIntegral.integral_comp_neg, intervalIntegral.integral_symm]
    simp [T, hg]
  have hT : 0 < T P A := intervalIntegral.intervalIntegral_pos_of_pos_on (hgint 1 ⟨by norm_num, le_rfl⟩)
    (fun r hr => hgpos r ⟨by linarith [hr.1], hr.2.le⟩) zero_lt_one
  have hsm := Real.sqrt_pos.mpr hμ
  have hsq : μ = Real.sqrt μ ^ 2 := (Real.sq_sqrt hμ.le).symm
  have c0 : (s 0 - 1) * (s 0 + 1) = 0 := by linear_combination hs0
  have c1 : (s 1 - 1) * (s 1 + 1) = 0 := by linear_combination hs1
  rcases mul_eq_zero.mp c0 with a0 | a0 <;> rcases mul_eq_zero.mp c1 with a1 | a1
  · rw [show s 0 = 1 by linarith, show s 1 = 1 by linarith] at h01; linarith
  · rw [show s 0 = 1 by linarith, show s 1 = -1 by linarith, hG1, hGm1] at h01
    rw [hsq, show Real.sqrt μ = 2 * T P A by linarith]; ring
  · rw [show s 0 = -1 by linarith, show s 1 = 1 by linarith, hG1, hGm1] at h01; linarith
  · rw [show s 0 = -1 by linarith, show s 1 = -1 by linarith] at h01; linarith

/-- For a polynomial potential `F = p`, the factor `P(A, y)` exists and is a polynomial in `y`
(division of `p - p(A)` by `X - A`). -/
theorem poly_factor (p : Polynomial ℝ) :
    ∃ P : ℝ → ℝ → ℝ, (∀ A, Continuous (P A)) ∧
      ∀ A y, p.eval A - p.eval y = (A - y) * P A y := by
  refine ⟨fun A y => ((p - Polynomial.C (p.eval A)) /ₘ (Polynomial.X - Polynomial.C A)).eval y,
    fun A => Polynomial.continuous _, fun A y => ?_⟩
  have hroot : (p - Polynomial.C (p.eval A)).IsRoot A := by simp
  have h := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have h2 := congrArg (Polynomial.eval y) h
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
  linear_combination h2

/-- `push_eq_time_map` specialised to polynomial seats `f = p'`, `F = p` (any polynomial `p`,
e.g. the donut / two-hole seats): the push is `4 T(A)^2` with `P` the polynomial quotient. -/
theorem poly_push_eq_time_map (p : Polynomial ℝ) :
    ∃ P : ℝ → ℝ → ℝ, (∀ A y, p.eval A - p.eval y = (A - y) * P A y) ∧
      ∀ {A μ : ℝ} {x x' : ℝ → ℝ}, (∀ y ∈ Icc 0 A, 0 < P A y) → 0 < μ →
        TippingRule.Sol (fun y => p.derivative.eval y) μ x x' →
        (∀ t ∈ Ioo (0:ℝ) 1, 0 < x t) → (∀ t ∈ Icc (0:ℝ) 1, x t ≤ A) →
        (∃ t₀ ∈ Icc (0:ℝ) 1, x t₀ = A) → μ = 4 * T P A ^ 2 := by
  obtain ⟨P, hPc, hFP⟩ := poly_factor p
  exact ⟨P, hFP, fun hP hμ hsol hpos hmax hpeak =>
    push_eq_time_map (F := fun y => p.eval y) (Polynomial.continuous _)
      (fun y => Polynomial.hasDerivAt p y) (hFP _) (hPc _) hP hμ hsol hpos hmax hpeak⟩

/-- `4 T^2` is algebraic over `Q` iff `T` is. -/
theorem alg_iff {μs T : ℝ} (h : μs = 4 * T ^ 2) : IsAlgebraic ℚ μs ↔ IsAlgebraic ℚ T := by
  constructor
  · intro hμ
    have h4 : IsAlgebraic ℚ ((1/4 : ℝ)) := by
      simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (1/4 : ℚ)
    rw [isAlgebraic_iff_isIntegral] at hμ h4
    have : IsIntegral ℚ (T ^ 2) := by
      have := h4.mul hμ; rw [h] at this; convert this using 1; ring
    exact IsAlgebraic.of_pow (n := 2) (by norm_num) (isAlgebraic_iff_isIntegral.mpr this)
  · intro hT
    have h4 : IsAlgebraic ℚ ((4 : ℝ)) := by
      simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (4 : ℚ)
    rw [isAlgebraic_iff_isIntegral] at hT h4 ⊢
    rw [h]; exact h4.mul (hT.pow 2)

/-- **Tip reduction.** For every solution as in `push_eq_time_map`, the push `mu = 4 T(A)^2`
is algebraic iff the half time `T(A)` is algebraic. In particular at the break
`mu* = 4 T(A*)^2` (with `A*` the peak where the fold condition `T'(A*) = 0` selects the top),
`mu*` is algebraic iff `T(A*)` is.

OPEN, NOT ASSUMED: whether `T(A*)` -- a hyperelliptic period-type integral evaluated at the
turning point selected by `T'(A*) = 0` -- can be algebraic. This file proves only the reduction;
nothing is assumed or claimed about the transcendence of `T(A*)`. -/
theorem tip_reduction {f F : ℝ → ℝ} {P : ℝ → ℝ → ℝ} {A μ : ℝ} {x x' : ℝ → ℝ}
    (hf : Continuous f) (hF : ∀ y, HasDerivAt F (f y) y)
    (hFP : ∀ y, F A - F y = (A - y) * P A y) (hPc : Continuous (P A))
    (hP : ∀ y ∈ Icc 0 A, 0 < P A y)
    (hμ : 0 < μ) (hsol : TippingRule.Sol f μ x x')
    (hpos : ∀ t ∈ Ioo (0:ℝ) 1, 0 < x t)
    (hmax : ∀ t ∈ Icc (0:ℝ) 1, x t ≤ A) (hpeak : ∃ t₀ ∈ Icc (0:ℝ) 1, x t₀ = A) :
    IsAlgebraic ℚ μ ↔ IsAlgebraic ℚ (T P A) :=
  alg_iff (push_eq_time_map hf hF hFP hPc hP hμ hsol hpos hmax hpeak)

/-- The break form: whenever `mu* = 4 T(A*)^2`, `mu*` is algebraic iff `T(A*)` is. -/
theorem tip_reduction_break {P : ℝ → ℝ → ℝ} {A μs : ℝ} (h : μs = 4 * T P A ^ 2) :
    IsAlgebraic ℚ μs ↔ IsAlgebraic ℚ (T P A) := alg_iff h

end TimeMap

#print axioms TimeMap.energy
#print axioms TimeMap.f_eq_P
#print axioms TimeMap.peak_set_countable
#print axioms TimeMap.push_eq_time_map
#print axioms TimeMap.poly_factor
#print axioms TimeMap.poly_push_eq_time_map
#print axioms TimeMap.alg_iff
#print axioms TimeMap.tip_reduction
#print axioms TimeMap.tip_reduction_break
