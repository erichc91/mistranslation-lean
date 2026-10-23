import Mathlib

/-! # The tipping rule: seat classes with no break number (2026-10-23)

Dirichlet seat `x'' + mu * f(x) = 0` on `[0,1]`, `x(0) = x(1) = 0`, for a general force `f`.
The *break* is the supremum of the pushes `mu > 0` that admit a solution; "no break number" means
the set of such pushes is all of `(0, oo)` (hence not bounded above).

Prior art: time-map / shooting for `x'' + mu f(x) = 0` (Sturm-Liouville 1836, Gelfand 1963),
maximum principle (Hopf 1927). What this file adds: machine-checked, hypothesis-free closures.

* `homogeneous_no_break`  -- `f 0 = 0`: the zero solution works for every push.
* `steady_no_break`       -- `f = const c`: explicit parabola `mu c t (1 - t) / 2`.
* `exp_spring_no_break`   -- `f y = c - a y`, `a > 0`: explicit cosh solution, never tips.
* `wrong_sign_power_only_zero` -- `x'' = mu x^m`, `x >= 0`, zero ends: only `x = 0` (convexity).
* `weakening_le_one`      -- `f y = 1 - y^k` (k >= 1): every solution satisfies `x <= 1`
  (interior-maximum argument). **Existence for every `mu > 0` (the full no-break claim for the
  weakening seat) is NOT proved here**; see the docstring of `weakening_le_one`.
-/

namespace TippingRule

/-- Solution of `x'' + mu f(x) = 0` on `[0,1]` with Dirichlet ends, `x'` the first derivative. -/
def Sol (f : ℝ → ℝ) (μ : ℝ) (x x' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt x (x' t) t ∧ HasDerivAt x' (-(μ * f (x t))) t) ∧
    x 0 = 0 ∧ x 1 = 0

/-- The pushes that admit a solution. The break is `sSup (Pushes f)`. -/
def Pushes (f : ℝ → ℝ) : Set ℝ := {μ : ℝ | 0 < μ ∧ ∃ x x' : ℝ → ℝ, Sol f μ x x'}

/-- If every positive push has a solution, the push set is `(0, oo)` and is not bounded above. -/
theorem no_break_of_forall {f : ℝ → ℝ} (h : ∀ μ : ℝ, 0 < μ → ∃ x x' : ℝ → ℝ, Sol f μ x x') :
    Pushes f = Set.Ioi 0 ∧ ¬ BddAbove (Pushes f) := by
  have hset : Pushes f = Set.Ioi 0 := by
    ext μ; exact ⟨fun hμ => hμ.1, fun hμ => ⟨hμ, h μ hμ⟩⟩
  refine ⟨hset, ?_⟩
  rw [hset]; exact not_bddAbove_Ioi 0

/-! ## 1. Homogeneous force: `f 0 = 0` -/

theorem homogeneous_sol {f : ℝ → ℝ} (hf : f 0 = 0) (μ : ℝ) :
    Sol f μ (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun t _ => ⟨hasDerivAt_const t 0, ?_⟩, rfl, rfl⟩
  simp only [hf, mul_zero, neg_zero]; exact hasDerivAt_const t 0

/-- **No push: oscillation shape.** If `f 0 = 0`, every push `mu > 0` has a solution. -/
theorem homogeneous_no_break {f : ℝ → ℝ} (hf : f 0 = 0) :
    Pushes f = Set.Ioi 0 ∧ ¬ BddAbove (Pushes f) :=
  no_break_of_forall fun μ _ => ⟨_, _, homogeneous_sol hf μ⟩

/-! ## 2. Steady push: `f = const c` -/

theorem steady_sol (c μ : ℝ) :
    Sol (fun _ => c) μ (fun t => μ * c * t * (1 - t) / 2) (fun t => μ * c * (1 - 2 * t) / 2) := by
  refine ⟨fun t _ => ⟨?_, ?_⟩, by ring, by ring⟩
  · have h1 := ((hasDerivAt_id t).const_mul (μ * c)).mul ((hasDerivAt_id t).const_sub 1)
    exact (h1.div_const 2).congr_deriv (by simp; ring) |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp)
  · have h1 := (((hasDerivAt_id t).const_mul 2).const_sub 1).const_mul (μ * c)
    exact (h1.div_const 2).congr_deriv (by simp; ring)

theorem steady_nonneg {c μ : ℝ} (h : 0 ≤ μ * c) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ μ * c * t * (1 - t) / 2 := by
  intro t ht
  have := mul_nonneg (mul_nonneg h ht.1) (sub_nonneg.mpr ht.2)
  linarith

/-- **Steady push.** A constant force never tips. -/
theorem steady_no_break (c : ℝ) :
    Pushes (fun _ => c) = Set.Ioi 0 ∧ ¬ BddAbove (Pushes (fun _ => c)) :=
  no_break_of_forall fun μ _ => ⟨_, _, steady_sol c μ⟩

/-! ## 3. Exponential spring: `f y = c - a y`, `a > 0` (equation `x'' = mu a x - mu c`) -/

lemma cosh_shift_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun t => Real.cosh (s * (t - 1 / 2))) (s * Real.sinh (s * (t - 1 / 2))) t := by
  have h := (Real.hasDerivAt_cosh (s * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul s)
  exact h.congr_deriv (by ring)

lemma sinh_shift_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun t => Real.sinh (s * (t - 1 / 2))) (s * Real.cosh (s * (t - 1 / 2))) t := by
  have h := (Real.hasDerivAt_sinh (s * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul s)
  exact h.congr_deriv (by ring)

/-- `x'' = A x + B` (`A > 0`, any `B`) with zero ends is solved by
`B/A (cosh(sqrt A (t - 1/2)) / cosh(sqrt A / 2) - 1)`. -/
theorem exp_spring_linear_sol {A : ℝ} (hA : 0 < A) (B : ℝ) :
    let s := Real.sqrt A
    (∀ t : ℝ, HasDerivAt (fun t => B / A * (Real.cosh (s * (t - 1 / 2)) / Real.cosh (s / 2) - 1))
        (B / A * (s * Real.sinh (s * (t - 1 / 2)) / Real.cosh (s / 2))) t ∧
      HasDerivAt (fun t => B / A * (s * Real.sinh (s * (t - 1 / 2)) / Real.cosh (s / 2)))
        (A * (B / A * (Real.cosh (s * (t - 1 / 2)) / Real.cosh (s / 2) - 1)) + B) t) ∧
    B / A * (Real.cosh (s * (0 - 1 / 2)) / Real.cosh (s / 2) - 1) = 0 ∧
    B / A * (Real.cosh (s * (1 - 1 / 2)) / Real.cosh (s / 2) - 1) = 0 := by
  intro s
  have hs2 : s * s = A := Real.mul_self_sqrt hA.le
  have hC : 0 < Real.cosh (s / 2) := Real.cosh_pos _
  refine ⟨fun t => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact ((((cosh_shift_hasDerivAt s t).div_const (Real.cosh (s / 2))).sub_const 1).const_mul (B / A))
  · refine ((((sinh_shift_hasDerivAt s t).const_mul s).div_const (Real.cosh (s / 2))).const_mul (B / A)).congr_deriv ?_
    field_simp
    rw [← hs2]; ring
  · rw [show s * (0 - 1 / 2) = -(s / 2) by ring, Real.cosh_neg, div_self hC.ne']; ring
  · rw [show s * (1 - 1 / 2) = s / 2 by ring, div_self hC.ne']; ring

theorem exp_spring_sol {a : ℝ} (ha : 0 < a) (c : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ∃ x x' : ℝ → ℝ, Sol (fun y => c - a * y) μ x x' := by
  obtain ⟨hd, h0, h1⟩ := exp_spring_linear_sol (mul_pos hμ ha) (-(μ * c))
  refine ⟨_, _, fun t _ => ⟨(hd t).1, (hd t).2.congr_deriv (by ring)⟩, h0, h1⟩

/-- **Exponential spring.** `f y = c - a y` with `a > 0` (non-restoring linear part): every push
`mu > 0` has a solution, so the push never tips. -/
theorem exp_spring_no_break {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Pushes (fun y => c - a * y) = Set.Ioi 0 ∧ ¬ BddAbove (Pushes (fun y => c - a * y)) :=
  no_break_of_forall fun _ hμ => exp_spring_sol ha c hμ

/-- The exponential-spring solution is nonnegative when `c >= 0`. -/
theorem exp_spring_nonneg {A B : ℝ} (hA : 0 < A) (hB : B ≤ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ B / A * (Real.cosh (Real.sqrt A * (t - 1 / 2)) / Real.cosh (Real.sqrt A / 2) - 1) := by
  intro t ht
  set s := Real.sqrt A
  have hs : 0 ≤ s := Real.sqrt_nonneg A
  have hC : 0 < Real.cosh (s / 2) := Real.cosh_pos _
  have hle : Real.cosh (s * (t - 1 / 2)) ≤ Real.cosh (s / 2) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith : 0 ≤ s / 2), abs_le]
    constructor <;> nlinarith [ht.1, ht.2]
  have hr : Real.cosh (s * (t - 1 / 2)) / Real.cosh (s / 2) - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hC]; exact hle
  exact mul_nonneg_of_nonpos_of_nonpos (div_nonpos_of_nonpos_of_nonneg hB hA.le) hr

/-! ## 4. Wrong-sign power: `x'' = mu x^m`, `x >= 0`, zero ends -/

/-- **Wrong-sign power.** With `f y = -y^m` (so `x'' = mu x^m`), `mu >= 0`, any nonnegative solution
is identically zero on `[0,1]`: `x'' >= 0` makes `x` convex, and convex with zero ends is `<= 0`. -/
theorem wrong_sign_power_only_zero (m : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) {x x' : ℝ → ℝ}
    (h : Sol (fun y => -y ^ m) μ x x') (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, x t = 0 := by
  have hcont : ContinuousOn x (Set.Icc 0 1) :=
    fun t ht => (h.1 t ht).1.continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), deriv x t = x' t := by
    intro t ht; rw [interior_Icc] at ht; exact (h.1 t (Set.Ioo_subset_Icc_self ht)).1.deriv
  have hmono' : MonotoneOn x' (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun t ht => (h.1 t ht).2.continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Icc] at ht
      exact (h.1 t (Set.Ioo_subset_Icc_self ht)).2.differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Icc] at ht
      have ht' := Set.Ioo_subset_Icc_self ht
      rw [(h.1 t ht').2.deriv]
      have := mul_nonneg hμ (pow_nonneg (hpos t ht') m)
      linarith
  have hconv : ConvexOn ℝ (Set.Icc 0 1) x := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1) hcont
    · intro t ht; rw [interior_Icc] at ht
      exact (h.1 t (Set.Ioo_subset_Icc_self ht)).1.differentiableAt.differentiableWithinAt
    · intro s hs t ht hst
      rw [hderiv s hs, hderiv t ht]
      exact hmono' (interior_subset hs) (interior_subset ht) hst
  intro t ht
  have key := hconv.2 (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) (sub_nonneg.mpr ht.2) ht.1 (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, h.2.1, h.2.2, add_zero] at key
  exact le_antisymm key (hpos t ht)

/-! ## 5. Weakening push: `f y = 1 - y^k` -- a-priori bound only -/

/-- **Weakening push, a-priori bound (partial result).** For `f y = 1 - y^k` with `k >= 1` and any
push `mu > 0`, every solution satisfies `x <= 1` on `[0,1]`.

Proof: if `max x > 1`, the maximum is interior (ends are 0), `x' = 0` there, and on a neighbourhood
where `x > 1` we have `x'' = mu (x^k - 1) > 0`, so `x` strictly increases just to the right of the
maximum -- contradiction.

NOT PROVED here: (a) the strict bound `x < 1` (needs ODE uniqueness at the equilibrium `x = 1`);
(b) existence of a solution `0 <= x < 1` for every `mu > 0`, i.e. the actual no-break claim for the
weakening seat (needs shooting / sub-super-solutions). This file does not claim the weakening seat
has no break number. -/
theorem weakening_le_one {k : ℕ} (hk : k ≠ 0) {μ : ℝ} (hμ : 0 < μ) {x x' : ℝ → ℝ}
    (h : Sol (fun y => 1 - y ^ k) μ x x') : ∀ t ∈ Set.Icc (0 : ℝ) 1, x t ≤ 1 := by
  have hcont : ContinuousOn x (Set.Icc 0 1) :=
    fun t ht => (h.1 t ht).1.continuousAt.continuousWithinAt
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one) hcont
  by_contra hcon
  push Not at hcon
  obtain ⟨t1, ht1, hx1⟩ := hcon
  have hM : 1 < x t0 := lt_of_lt_of_le hx1 (hmax ht1)
  have ht0lt : t0 < 1 := by
    rcases ht0.2.lt_or_eq with h' | h'
    · exact h'
    · rw [h', h.2.2] at hM; linarith
  have ht0pos : 0 < t0 := by
    rcases ht0.1.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', h.2.1] at hM; linarith
  -- x' t0 = 0 at the interior maximum
  have hmaxloc : IsLocalMax x t0 :=
    hmax.isLocalMax (Icc_mem_nhds ht0pos ht0lt)
  have hx't0 : x' t0 = 0 := hmaxloc.hasDerivAt_eq_zero (h.1 t0 ht0).1
  -- a right-neighbourhood [t0, t0 + d] inside [0,1] on which x > 1
  have hev : ∀ᶠ s in nhds t0, 1 < x s ∧ s ∈ Set.Ioo 0 1 :=
    ((h.1 t0 ht0).1.continuousAt.eventually (lt_mem_nhds hM)).and (Ioo_mem_nhds ht0pos ht0lt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set d := ε / 2 with hd
  have hdpos : 0 < d := by positivity
  have hin : ∀ s ∈ Set.Icc t0 (t0 + d), 1 < x s ∧ s ∈ Set.Ioo 0 1 := by
    intro s hs; apply hball
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
  have hIcc : ∀ s ∈ Set.Icc t0 (t0 + d), s ∈ Set.Icc (0 : ℝ) 1 :=
    fun s hs => Set.Ioo_subset_Icc_self (hin s hs).2
  -- x' strictly increasing on [t0, t0 + d]
  have hmono' : StrictMonoOn x' (Set.Icc t0 (t0 + d)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun s hs => (h.1 s (hIcc s hs)).2.continuousAt.continuousWithinAt
    · intro s hs; rw [interior_Icc] at hs
      have hs' := Set.Ioo_subset_Icc_self hs
      rw [(h.1 s (hIcc s hs')).2.deriv]
      have h1 : 1 < x s ^ k := one_lt_pow₀ (hin s hs').1 hk
      nlinarith
  -- hence x' > 0 on (t0, t0 + d], so x strictly increasing on [t0, t0 + d]
  have hmono : StrictMonoOn x (Set.Icc t0 (t0 + d)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun s hs => (h.1 s (hIcc s hs)).1.continuousAt.continuousWithinAt
    · intro s hs; rw [interior_Icc] at hs
      have hs' := Set.Ioo_subset_Icc_self hs
      rw [(h.1 s (hIcc s hs')).1.deriv, ← hx't0]
      exact hmono' ⟨le_rfl, by linarith⟩ hs' hs.1
  have hlt := hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : t0 < t0 + d)
  have := hmax (hIcc _ ⟨by linarith, le_rfl⟩)
  simp only [Set.mem_ofPred_eq] at this
  linarith

end TippingRule

#print axioms TippingRule.homogeneous_no_break
#print axioms TippingRule.steady_no_break
#print axioms TippingRule.steady_nonneg
#print axioms TippingRule.exp_spring_no_break
#print axioms TippingRule.exp_spring_nonneg
#print axioms TippingRule.wrong_sign_power_only_zero
#print axioms TippingRule.weakening_le_one
