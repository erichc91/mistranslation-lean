import Mathlib

/-!
# Break numbers (2026-10-22)

Seat `x'' + mu * f(x) = 0` with both ends pinned. First integral: the largest push mu with a solution of peak `A` is
`mu(A) = 4 I(A)^2`, and the break point is `mu* = max mu(A)`.

**Break-one** (`f = 1/(1-x)^3`): `I(A) = a * sqrt(1 - a^2)` with `a = 1 - A`, so `mu(a) = 4 a^2 (1 - a^2)`.
The algebraic core is proved here: the curve never exceeds 1, and it equals 1 exactly when `a^2 = 1/2`.
The step from the ODE to this formula is the hand derivation in `docs/GALLIUM_PREDICTION_2026-10-22.md`,
and it is NOT formalised yet.
-/

namespace Breaks

/-- Break-one's push curve, as a function of `a = 1 - A`. -/
def muOne (a : ℝ) : ℝ := 4 * a ^ 2 * (1 - a ^ 2)

/-- No push above 1 has a solution. -/
theorem muOne_le_one (a : ℝ) : muOne a ≤ 1 := by
  unfold muOne
  nlinarith [sq_nonneg (2 * a ^ 2 - 1)]

/-- The bound is reached exactly at `a^2 = 1/2`. -/
theorem muOne_eq_one_iff (a : ℝ) : muOne a = 1 ↔ a ^ 2 = 1 / 2 := by
  unfold muOne
  constructor
  · intro h
    have h2 : (2 * a ^ 2 - 1) ^ 2 = 0 := by nlinarith
    have : 2 * a ^ 2 - 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith
  · intro h
    rw [h]; norm_num

/-- The break point of the `1/(1-x)^3` seat is exactly 1: an upper bound that is attained. -/
theorem break_one : IsGreatest (Set.range muOne) 1 := by
  refine ⟨⟨Real.sqrt (1 / 2), ?_⟩, ?_⟩
  · rw [muOne_eq_one_iff, Real.sq_sqrt (by norm_num)]
  · rintro _ ⟨a, rfl⟩
    exact muOne_le_one a

/-- Gate check: the same statement with 1 replaced by 0.99 must be FALSE (the curve really reaches 1). -/
theorem not_le_099 : ¬ ∀ a : ℝ, muOne a ≤ 0.99 := by
  intro h
  have := h (Real.sqrt (1 / 2))
  rw [(muOne_eq_one_iff _).mpr (Real.sq_sqrt (by norm_num))] at this
  norm_num at this

/-! ## k = 3 from the ODE itself (2026-10-23): break = 1, no formula assumed

Seat `x'' + mu / (1 - x)^3 = 0`, `x(0) = x(1) = 0`. With `v = 1 - x` this is `v'' = mu / v^3`, `v(0) = v(1) = 1`
(Ermakov-Pinney). `Pinney mu v v'` says `v` is a positive C^2 solution on [0,1] (derivatives taken at every point
of [0,1]). Proof: the energy `E = v'^2 + mu / v^2` is conserved, `w = v^2` has `w'' = 2E`, so `w` is a parabola
through (0,1), (1,1); then `mu = E - E^2/4 <= 1`. The bound is reached by `v = sqrt (2t^2 - 2t + 1)`. -/

/-- `v` is a positive solution of `v'' = mu / v^3` on [0,1] with `v(0) = v(1) = 1` (`v'` its derivative). -/
def Pinney (μ : ℝ) (v v' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < v t ∧ HasDerivAt v (v' t) t ∧ HasDerivAt v' (μ / v t ^ 3) t) ∧
    v 0 = 1 ∧ v 1 = 1

lemma const_on_unit {f : ℝ → ℝ} (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f 0 t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = f 0 := by
  apply constant_of_has_deriv_right_zero
  · intro t ht; exact (h t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (h t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt

/-- No push above 1 has a solution: any solution forces `mu = E - E^2/4 <= 1`. -/
theorem pinney_le_one {μ : ℝ} {v v' : ℝ → ℝ} (h : Pinney μ v v') : μ ≤ 1 := by
  obtain ⟨hode, h0, h1⟩ := h
  have mem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have mem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- energy E = v'^2 + mu / v^2 is conserved (written with products so derivative shapes match)
  set e0 : ℝ := v' 0 * v' 0 + μ * (v 0 * v 0)⁻¹ with he0
  have hE : ∀ t ∈ Set.Icc (0 : ℝ) 1, v' t * v' t + μ * (v t * v t)⁻¹ = e0 := by
    refine const_on_unit (f := fun t => v' t * v' t + μ * (v t * v t)⁻¹) ?_
    intro s hs
    obtain ⟨hv, hd, hdd⟩ := hode s hs
    have hvv : v s * v s ≠ 0 := by positivity
    convert (hdd.mul hdd).add (((hd.mul hd).inv hvv).const_mul μ) using 1
    simp only [Pi.mul_apply]
    field_simp
    ring
  -- phi = (v^2)' = 2 v v' grows linearly with slope 2 e0
  have hphi : ∀ t ∈ Set.Icc (0 : ℝ) 1, 2 * v t * v' t - 2 * e0 * t = 2 * v 0 * v' 0 - 2 * e0 * 0 := by
    refine const_on_unit (f := fun t => 2 * v t * v' t - 2 * e0 * t) ?_
    intro s hs
    obtain ⟨hv, hd, hdd⟩ := hode s hs
    have hv0 : v s ≠ 0 := hv.ne'
    convert ((hd.const_mul 2).mul hdd).sub ((hasDerivAt_id' s).const_mul (2 * e0)) using 1
    rw [← hE s hs]
    field_simp
    ring
  -- so v^2 is the parabola 1 + phi0 t + e0 t^2
  have hw : ∀ t ∈ Set.Icc (0 : ℝ) 1, v t * v t - 2 * v 0 * v' 0 * t - e0 * (t * t)
      = v 0 * v 0 - 2 * v 0 * v' 0 * 0 - e0 * (0 * 0) := by
    refine const_on_unit (f := fun t => v t * v t - 2 * v 0 * v' 0 * t - e0 * (t * t)) ?_
    intro s hs
    obtain ⟨hv, hd, hdd⟩ := hode s hs
    convert ((hd.mul hd).sub ((hasDerivAt_id' s).const_mul (2 * v 0 * v' 0))).sub
      (((hasDerivAt_id' s).mul (hasDerivAt_id' s)).const_mul e0) using 1
    linear_combination (-1 : ℝ) * hphi s hs
  have hw1 := hw 1 mem1
  rw [h0, h1] at hw1
  have he0' : e0 = v' 0 ^ 2 + μ := by rw [he0, h0]; ring
  -- hw1 : 1 - 2 v'0 - e0 = 1, so v'0 = -e0/2; then mu = e0 - e0^2/4 = 1 - (1 - e0/2)^2
  nlinarith [sq_nonneg (e0 - 2), hw1, he0']

/-- The bound is reached: `v = sqrt (2t^2 - 2t + 1)` solves the seat with push exactly 1. -/
theorem pinney_one :
    Pinney 1 (fun t => Real.sqrt (2 * t ^ 2 - 2 * t + 1))
      (fun t => (2 * t - 1) / Real.sqrt (2 * t ^ 2 - 2 * t + 1)) := by
  have hq : ∀ t : ℝ, 0 < 2 * t ^ 2 - 2 * t + 1 := fun t => by nlinarith [sq_nonneg (2 * t - 1)]
  refine ⟨fun t _ => ⟨Real.sqrt_pos.mpr (hq t), ?_, ?_⟩, by norm_num, by norm_num⟩
  · have hpoly : HasDerivAt (fun t : ℝ => 2 * t ^ 2 - 2 * t + 1) (4 * t - 2) t := by
      have := (((hasDerivAt_pow 2 t).const_mul 2).sub ((hasDerivAt_id t).const_mul 2)).add_const 1
      convert this using 1; simp; ring
    convert hpoly.sqrt (hq t).ne' using 1
    have hs : 0 < Real.sqrt (2 * t ^ 2 - 2 * t + 1) := Real.sqrt_pos.mpr (hq t)
    field_simp; ring
  · have hpoly : HasDerivAt (fun t : ℝ => 2 * t ^ 2 - 2 * t + 1) (4 * t - 2) t := by
      have := (((hasDerivAt_pow 2 t).const_mul 2).sub ((hasDerivAt_id t).const_mul 2)).add_const 1
      convert this using 1; simp; ring
    have hs : 0 < Real.sqrt (2 * t ^ 2 - 2 * t + 1) := Real.sqrt_pos.mpr (hq t)
    have hss : Real.sqrt (2 * t ^ 2 - 2 * t + 1) ^ 2 = 2 * t ^ 2 - 2 * t + 1 := Real.sq_sqrt (hq t).le
    have hnum : HasDerivAt (fun t : ℝ => 2 * t - 1) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
    convert hnum.div (hpoly.sqrt (hq t).ne') hs.ne' using 1
    beta_reduce
    generalize Real.sqrt (2 * t ^ 2 - 2 * t + 1) = s at hs hss ⊢
    field_simp
    nlinarith [hss]

/-- **k = 3 from the ODE: the break number is exactly 1.** -/
theorem break_three_from_ode : IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Pinney μ v v'} 1 :=
  ⟨⟨_, _, pinney_one⟩, fun _ ⟨_, _, h⟩ => pinney_le_one h⟩

/-! ## Break(5/3) (docs/BREAK_LADDERS_2026-10-23.md)

Seat `x'' + mu / (1 - x)^(5/3) = 0`: with `r = (1 - A)^(2/3)` the push curve is `g r = 4/3 (r + 3 r^2 - 4 r^4)`.
Key identity: `(3 + 2 sqrt3)/4 - g r = 16/3 (r - (1 + sqrt3)/4)^2 (r^2 + (1 + sqrt3)/2 r + 3 sqrt3/8)`.
UNVERIFIED: written 2026-10-23 while Smart App Control blocks lean.exe. -/

/-- No push above (3 + 2√3)/4 has a solution. -/
theorem breakFiveThirds_le (r : ℝ) (hr : 0 ≤ r) :
    4 / 3 * (r + 3 * r ^ 2 - 4 * r ^ 4) ≤ (3 + 2 * Real.sqrt 3) / 4 := by
  have ht : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ht0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hq : 0 ≤ r ^ 2 + (1 + Real.sqrt 3) / 2 * r + 3 * Real.sqrt 3 / 8 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (r - (1 + Real.sqrt 3) / 4)) hq, ht, ht0]

/-- The bound is reached at `r = (1 + √3)/4`. -/
theorem breakFiveThirds_attained :
    4 / 3 * ((1 + Real.sqrt 3) / 4 + 3 * ((1 + Real.sqrt 3) / 4) ^ 2 - 4 * ((1 + Real.sqrt 3) / 4) ^ 4)
      = (3 + 2 * Real.sqrt 3) / 4 := by
  have ht : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h4 : Real.sqrt 3 ^ 4 = 9 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ht]; norm_num
  have h3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, ht]
  ring_nf
  rw [h4, h3, ht]
  ring

/-! ## Break(7/5): the third algebraic rung (2026-10-23)

Seat `x'' + mu / (1 - x)^(7/5)`, n = 2: push curve `g r = 4/45 r (1 - r) (8 r^2 + 4 r + 3)^2` on [0,1], whose
critical point solves `16 r^3 - 8 r^2 - 2 r - 1 = 0` (r* = 0.768486884048). Hand reduction mod that cubic:
the break is a perfect square, `((4 r* + 1)/3)^2`, and a root of `729 b^3 - 1215 b^2 - 225 b - 25`.
SQL (2026-10-23): curve value, square form and a 10^6-point scan all give 1.844116503072; cubic residual 0. -/

/-- At the critical root, the push curve's value is the square `((4r+1)/3)^2`. -/
theorem breakSevenFifths_square (r : ℝ) (h : 16 * r ^ 3 - 8 * r ^ 2 - 2 * r - 1 = 0) :
    4 / 45 * r * (1 - r) * (8 * r ^ 2 + 4 * r + 3) ^ 2 = ((4 * r + 1) / 3) ^ 2 := by
  linear_combination ((-16 * r ^ 3 - 8 * r ^ 2 - 6 * r + 5) / 45) * h

/-- ... and that square is a root of `729 b^3 - 1215 b^2 - 225 b - 25`, so break(7/5) is algebraic. -/
theorem breakSevenFifths_cubic (r : ℝ) (h : 16 * r ^ 3 - 8 * r ^ 2 - 2 * r - 1 = 0) :
    let b := ((4 * r + 1) / 3) ^ 2
    729 * b ^ 3 - 1215 * b ^ 2 - 225 * b - 25 = 0 := by
  intro b
  have hw : 27 * ((4 * r + 1) / 3) ^ 3 - 45 * ((4 * r + 1) / 3) ^ 2 + 15 * ((4 * r + 1) / 3) - 5 = 0 := by
    linear_combination 4 * h
  simp only [b]
  linear_combination (27 * ((4 * r + 1) / 3) ^ 3 + 45 * ((4 * r + 1) / 3) ^ 2
    + 15 * ((4 * r + 1) / 3) + 5) * hw

/-- The critical point really is the maximum on [0,1]: no push above the square has a solution. -/
theorem breakSevenFifths_le (r x : ℝ) (h : 16 * r ^ 3 - 8 * r ^ 2 - 2 * r - 1 = 0)
    (hr : 3 / 4 < r) (hr' : r < 4 / 5) (hx : 0 ≤ x) :
    4 / 45 * x * (1 - x) * (8 * x ^ 2 + 4 * x + 3) ^ 2 ≤ ((4 * r + 1) / 3) ^ 2 := by
  rw [← breakSevenFifths_square r h]
  -- gap = (x - r)^2 * D + (multiple of the critical cubic), D > 0 on [0,1] for r in (3/4, 4/5)
  have key : 4 / 45 * r * (1 - r) * (8 * r ^ 2 + 4 * r + 3) ^ 2
      - 4 / 45 * x * (1 - x) * (8 * x ^ 2 + 4 * x + 3) ^ 2
      = 4 / 45 * ((x - r) ^ 2 * (64 * (x ^ 4 + 2 * r * x ^ 3 + 3 * r ^ 2 * x ^ 2 + 4 * r ^ 3 * x + 5 * r ^ 4)
          - 40 * x - 80 * r - 15)
        + 3 * (x - r) * (8 * r ^ 2 + 4 * r + 3) * (16 * r ^ 3 - 8 * r ^ 2 - 2 * r - 1)) := by ring
  have hr0 : 0 < r := by linarith
  have hr3 : (3 / 4) ^ 3 < r ^ 3 := by gcongr
  have hr4 : (3 / 4) ^ 4 < r ^ 4 := by gcongr
  have hD : 0 ≤ 64 * (x ^ 4 + 2 * r * x ^ 3 + 3 * r ^ 2 * x ^ 2 + 4 * r ^ 3 * x + 5 * r ^ 4)
      - 40 * x - 80 * r - 15 := by
    have : 0 ≤ x ^ 4 + 2 * r * x ^ 3 + 3 * r ^ 2 * x ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hr3.le hx]
  rw [h, mul_zero, add_zero] at key
  nlinarith [mul_nonneg (sq_nonneg (x - r)) hD]

/-- The hypotheses above are satisfiable: the critical cubic has a root in (3/4, 4/5). -/
theorem breakSevenFifths_root_exists :
    ∃ r : ℝ, 3 / 4 < r ∧ r < 4 / 5 ∧ 16 * r ^ 3 - 8 * r ^ 2 - 2 * r - 1 = 0 := by
  have hc : ContinuousOn (fun r : ℝ => 16 * r ^ 3 - 8 * r ^ 2 - 2 * r - 1) (Set.Icc (3 / 4) (4 / 5)) := by
    fun_prop
  obtain ⟨r, ⟨h1, h2⟩, hr⟩ := intermediate_value_Ioo (by norm_num) hc
    (show (0 : ℝ) ∈ Set.Ioo _ _ by norm_num)
  exact ⟨r, h1, h2, hr⟩

/-! ## MEMS pull-in (k = 2) is transcendental, given Hermite-Lindemann

From docs/BREAK_LADDERS_2026-10-23.md: for the pole seat with k = 2 (p = 1) the break number is
`8 / (9 sinh^2 T)` where `T > 0` solves the critical equation `cosh T (2 - sinh^2 T) = 3 T sinh T`
(numerically T = 0.73017877, break = 1.4000165). The ODE-to-formula step is NOT formalised here; this is the
number-theory step only. Hermite-Lindemann is taken as a hypothesis `HL` (not in this Mathlib).
Checked by Lean 2026-10-23 (axioms: propext, Classical.choice, Quot.sound; HL is an explicit hypothesis). -/

/-- Hermite-Lindemann, stated for real arguments: `exp a` is transcendental for algebraic `a ≠ 0`. -/
def HermiteLindemann : Prop :=
  ∀ a : ℝ, IsAlgebraic ℚ a → a ≠ 0 → Transcendental ℚ (Real.exp a)

theorem mems_break_transcendental (HL : HermiteLindemann) (T : ℝ) (hT : 0 < T)
    (hcrit : Real.cosh T * (2 - Real.sinh T ^ 2) = 3 * T * Real.sinh T) :
    Transcendental ℚ (8 / (9 * Real.sinh T ^ 2)) := by
  intro hb
  have hs : Real.sinh T ≠ 0 := (Real.sinh_pos_iff.mpr hT).ne'
  -- sinh^2 T = 8 / (9 b) is algebraic
  have hs2 : IsAlgebraic ℚ (Real.sinh T ^ 2) := by
    have h89 : Real.sinh T ^ 2 = 8 / (9 * (8 / (9 * Real.sinh T ^ 2))) := by
      field_simp
    rw [h89]
    rw [div_eq_mul_inv]
    exact (isAlgebraic_algebraMap (8 : ℚ)).mul ((isAlgebraic_algebraMap (9 : ℚ)).mul hb).inv
  have hsinh : IsAlgebraic ℚ (Real.sinh T) := IsAlgebraic.of_pow (by norm_num) hs2
  have hc2 : IsAlgebraic ℚ (Real.cosh T ^ 2) := by
    rw [Real.cosh_sq]; exact hs2.add (isAlgebraic_one)
  have hcosh : IsAlgebraic ℚ (Real.cosh T) := IsAlgebraic.of_pow (by norm_num) hc2
  -- the critical equation makes T an algebraic expression in sinh T, cosh T
  have hTeq : T = Real.cosh T * (2 - Real.sinh T ^ 2) / (3 * Real.sinh T) := by
    field_simp; linarith [hcrit]
  have hTalg : IsAlgebraic ℚ T := by
    rw [hTeq, div_eq_mul_inv]
    exact (hcosh.mul ((isAlgebraic_algebraMap (2 : ℚ)).sub hs2)).mul
      ((isAlgebraic_algebraMap (3 : ℚ)).mul hsinh).inv
  -- then exp T = cosh T + sinh T is algebraic, contradicting Hermite-Lindemann
  have hexp : IsAlgebraic ℚ (Real.exp T) := by
    rw [← Real.cosh_add_sinh]; exact hcosh.add hsinh
  exact HL T hTalg hT.ne' hexp


/-- Bratu (f = e^x), the p -> 0 end of the pole family: break = 8 / sinh^2 s where s > 0 solves s tanh s = 1,
i.e. `s * sinh s = cosh s` (s = 1.19967864, break = 3.5138307). Same argument: s = cosh s / sinh s. -/
theorem bratu_break_transcendental (HL : HermiteLindemann) (s : ℝ) (hs : 0 < s)
    (hcrit : s * Real.sinh s = Real.cosh s) :
    Transcendental ℚ (8 / Real.sinh s ^ 2) := by
  intro hb
  have hsn : Real.sinh s ≠ 0 := (Real.sinh_pos_iff.mpr hs).ne'
  have hs2 : IsAlgebraic ℚ (Real.sinh s ^ 2) := by
    have h8 : Real.sinh s ^ 2 = 8 * (8 / Real.sinh s ^ 2)⁻¹ := by field_simp
    rw [h8]
    exact (isAlgebraic_algebraMap (8 : ℚ)).mul hb.inv
  have hsinh : IsAlgebraic ℚ (Real.sinh s) := IsAlgebraic.of_pow (by norm_num) hs2
  have hc2 : IsAlgebraic ℚ (Real.cosh s ^ 2) := by
    rw [Real.cosh_sq]; exact hs2.add (isAlgebraic_one)
  have hcosh : IsAlgebraic ℚ (Real.cosh s) := IsAlgebraic.of_pow (by norm_num) hc2
  have hseq : s = Real.cosh s * (Real.sinh s)⁻¹ := by
    field_simp; linarith [hcrit]
  have hsalg : IsAlgebraic ℚ s := by
    rw [hseq]; exact hcosh.mul hsinh.inv
  have hexp : IsAlgebraic ℚ (Real.exp s) := by
    rw [← Real.cosh_add_sinh]; exact hcosh.add hsinh
  exact HL s hsalg hs.ne' hexp

/-! ## The integer-p ladder engine

Every rung k = 1 + 1/n has break = c / sinh^2 T* with c a nonzero rational, and its critical equation
makes T* an algebraic expression in sinh T*, cosh T* (the `alpha_p T` term of `int cosh^{2p}`). That link is
the only rung-specific input; the rest is this one argument. -/

theorem break_transcendental_of_link (HL : HermiteLindemann) (T : ℝ) (hT : 0 < T)
    (c : ℝ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0)
    (hlink : IsAlgebraic ℚ (Real.sinh T) → IsAlgebraic ℚ (Real.cosh T) → IsAlgebraic ℚ T) :
    Transcendental ℚ (c / Real.sinh T ^ 2) := by
  intro hb
  have hsn : Real.sinh T ≠ 0 := (Real.sinh_pos_iff.mpr hT).ne'
  have hs2 : IsAlgebraic ℚ (Real.sinh T ^ 2) := by
    have h : Real.sinh T ^ 2 = c * (c / Real.sinh T ^ 2)⁻¹ := by field_simp
    rw [h]; exact hc.mul hb.inv
  have hsinh : IsAlgebraic ℚ (Real.sinh T) := IsAlgebraic.of_pow (by norm_num) hs2
  have hcosh : IsAlgebraic ℚ (Real.cosh T) :=
    IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [Real.cosh_sq]; exact hs2.add isAlgebraic_one)
  have hexp : IsAlgebraic ℚ (Real.exp T) := by
    rw [← Real.cosh_add_sinh]; exact hcosh.add hsinh
  exact HL T (hlink hsinh hcosh) hT.ne' hexp

/-- k = 3/2 (p = 2): `int_0^T cosh^4 = 3T/8 + sinh 2T / 4 + sinh 4T / 32`, critical equation
`5 sinh T * int_0^T cosh^4 = cosh^5 T`, break = 16 / (25 sinh^2 T).
Numerics (Lean Float bisection, 2026-10-23): T* = 0.572688, break = 1.751353 (matches the solver). -/
theorem k32_break_transcendental (HL : HermiteLindemann) (T : ℝ) (hT : 0 < T)
    (hcrit : 5 * Real.sinh T * (3 * T / 8 + Real.sinh (2 * T) / 4 + Real.sinh (4 * T) / 32)
      = Real.cosh T ^ 5) :
    Transcendental ℚ (16 / 25 / Real.sinh T ^ 2) := by
  refine break_transcendental_of_link HL T hT _ ?_ (by norm_num) ?_
  · simpa using (isAlgebraic_algebraMap (16 / 25 : ℚ) : IsAlgebraic ℚ (algebraMap ℚ ℝ (16 / 25)))
  · intro hs hc
    have hsn : Real.sinh T ≠ 0 := (Real.sinh_pos_iff.mpr hT).ne'
    have h2 : Real.sinh (2 * T) = 2 * Real.sinh T * Real.cosh T := Real.sinh_two_mul T
    have h4 : Real.sinh (4 * T) = 2 * (2 * Real.sinh T * Real.cosh T) *
        (Real.cosh T ^ 2 + Real.sinh T ^ 2) := by
      rw [show (4 : ℝ) * T = 2 * (2 * T) by ring, Real.sinh_two_mul, Real.cosh_two_mul, h2]
    have hTeq : T = (Real.cosh T ^ 5 - 5 * Real.sinh T *
        ((2 * Real.sinh T * Real.cosh T) / 4 +
          (2 * (2 * Real.sinh T * Real.cosh T) * (Real.cosh T ^ 2 + Real.sinh T ^ 2)) / 32)) *
        (8 / 15) * (Real.sinh T)⁻¹ := by
      rw [h2, h4] at hcrit; field_simp; linarith [hcrit]
    have q : ∀ r : ℚ, IsAlgebraic ℚ ((r : ℚ) : ℝ) := fun r =>
      (isAlgebraic_algebraMap r : IsAlgebraic ℚ (algebraMap ℚ ℝ r))
    have key := (((hc.pow 5).sub (((q 5).mul hs).mul
      ((((q 2).mul hs).mul hc).mul (q 4).inv |>.add
        ((((q 2).mul (((q 2).mul hs).mul hc)).mul ((hc.pow 2).add (hs.pow 2))).mul (q 32).inv)))).mul
      (q (8 / 15))).mul hs.inv
    rw [hTeq]
    convert key using 1
    push_cast
    ring

/-- k = 4/3 (p = 3): `int_0^T cosh^6 = 5T/16 + 15 sinh 2T/64 + 3 sinh 4T/64 + sinh 6T/192`, critical equation
`7 sinh T * int_0^T cosh^6 = cosh^7 T`, break = 24 / (49 sinh^2 T).
Numerics (Lean Float, 2026-10-23): antiderivative checked by central difference; T* = 0.486728, break = 1.911677. -/
theorem k43_break_transcendental (HL : HermiteLindemann) (T : ℝ) (hT : 0 < T)
    (hcrit : 7 * Real.sinh T * (5 * T / 16 + 15 * Real.sinh (2 * T) / 64 + 3 * Real.sinh (4 * T) / 64
      + Real.sinh (6 * T) / 192) = Real.cosh T ^ 7) :
    Transcendental ℚ (24 / 49 / Real.sinh T ^ 2) := by
  refine break_transcendental_of_link HL T hT _ ?_ (by norm_num) ?_
  · simpa using (isAlgebraic_algebraMap (24 / 49 : ℚ) : IsAlgebraic ℚ (algebraMap ℚ ℝ (24 / 49)))
  · intro hs hc
    have hsn : Real.sinh T ≠ 0 := (Real.sinh_pos_iff.mpr hT).ne'
    have q : ∀ r : ℚ, IsAlgebraic ℚ ((r : ℚ) : ℝ) := fun r =>
      (isAlgebraic_algebraMap r : IsAlgebraic ℚ (algebraMap ℚ ℝ r))
    -- sinh 2T, sinh 4T, sinh 6T are polynomials in sinh T, cosh T
    have a2 : IsAlgebraic ℚ (Real.sinh (2 * T)) := by
      rw [Real.sinh_two_mul]; exact ((q 2).mul hs).mul hc
    have c2 : IsAlgebraic ℚ (Real.cosh (2 * T)) := by
      rw [Real.cosh_two_mul]; exact (hc.pow 2).add (hs.pow 2)
    have a4 : IsAlgebraic ℚ (Real.sinh (4 * T)) := by
      rw [show (4 : ℝ) * T = 2 * (2 * T) by ring, Real.sinh_two_mul]; exact ((q 2).mul a2).mul c2
    have a6 : IsAlgebraic ℚ (Real.sinh (6 * T)) := by
      rw [show (6 : ℝ) * T = 2 * (3 * T) by ring, Real.sinh_two_mul, Real.sinh_three_mul,
        Real.cosh_three_mul]
      convert ((q 2).mul (((q 3).mul hs).add ((q 4).mul (hs.pow 3)))).mul
        (((q 4).mul (hc.pow 3)).sub ((q 3).mul hc)) using 1
      push_cast; ring
    have hTeq : T = (Real.cosh T ^ 7 - 7 * Real.sinh T * (15 * Real.sinh (2 * T) / 64
        + 3 * Real.sinh (4 * T) / 64 + Real.sinh (6 * T) / 192)) * (16 / 35) * (Real.sinh T)⁻¹ := by
      rw [eq_comm, mul_inv_eq_iff_eq_mul₀ hsn]
      linear_combination (-16 / 35 : ℝ) * hcrit
    have key := (((hc.pow 7).sub (((q 7).mul hs).mul
      ((((q 15).mul a2).mul (q 64).inv |>.add (((q 3).mul a4).mul (q 64).inv)).add
        (a6.mul (q 192).inv)))).mul (q (16 / 35))).mul hs.inv
    rw [hTeq]
    convert key using 1
    push_cast
    ring

/-! ## Every integer-p rung at once

For p = 1/(k-1) a positive integer, `int_0^T cosh^{2p} = alpha T + sum_j c_j sinh(2 j T)` with rational
`alpha = C(2p,p)/4^p != 0` and rational `c_j`. The theorem below takes ANY rational alpha != 0 and ANY rational c_j,
so it covers every rung k = 1 + 1/n with one proof. -/

theorem sinh_cosh_nat_mul_algebraic (T : ℝ) (hs : IsAlgebraic ℚ (Real.sinh T))
    (hc : IsAlgebraic ℚ (Real.cosh T)) (n : ℕ) :
    IsAlgebraic ℚ (Real.sinh (n * T)) ∧ IsAlgebraic ℚ (Real.cosh (n * T)) := by
  induction n with
  | zero => simp [isAlgebraic_zero, isAlgebraic_one]
  | succ n ih =>
    obtain ⟨ihs, ihc⟩ := ih
    rw [Nat.cast_succ, add_mul, one_mul, Real.sinh_add, Real.cosh_add]
    exact ⟨(ihs.mul hc).add (ihc.mul hs), (ihc.mul hc).add (ihs.mul hs)⟩

theorem ladderA_break_transcendental (HL : HermiteLindemann) (p : ℕ) (T : ℝ) (hT : 0 < T)
    (α : ℚ) (hα : α ≠ 0) (c : ℕ → ℚ) (κ : ℚ) (hκ : κ ≠ 0)
    (hcrit : (2 * p + 1) * Real.sinh T *
        ((α : ℝ) * T + ∑ j ∈ Finset.range (p + 1), (c j : ℝ) * Real.sinh (2 * j * T))
      = Real.cosh T ^ (2 * p + 1)) :
    Transcendental ℚ ((κ : ℝ) / Real.sinh T ^ 2) := by
  have qa : ∀ r : ℚ, IsAlgebraic ℚ ((r : ℚ) : ℝ) := fun r =>
    (isAlgebraic_algebraMap r : IsAlgebraic ℚ (algebraMap ℚ ℝ r))
  refine break_transcendental_of_link HL T hT _ (qa κ) (by exact_mod_cast hκ) ?_
  intro hs hc
  have hsn : Real.sinh T ≠ 0 := (Real.sinh_pos_iff.mpr hT).ne'
  have h2p : (2 * (p : ℝ) + 1) ≠ 0 := by positivity
  have hsum : IsAlgebraic ℚ (∑ j ∈ Finset.range (p + 1), (c j : ℝ) * Real.sinh (2 * j * T)) := by
    refine Finset.sum_induction _ (IsAlgebraic ℚ) (fun _ _ => IsAlgebraic.add) isAlgebraic_zero ?_
    intro j _
    have := (sinh_cosh_nat_mul_algebraic T hs hc (2 * j)).1
    push_cast at this
    exact (qa (c j)).mul this
  have hTeq : T = (Real.cosh T ^ (2 * p + 1) * ((2 * p + 1) * Real.sinh T)⁻¹ -
      ∑ j ∈ Finset.range (p + 1), (c j : ℝ) * Real.sinh (2 * j * T)) * ((α : ℝ))⁻¹ := by
    have hα' : (α : ℝ) ≠ 0 := by exact_mod_cast hα
    rw [← hcrit]; field_simp; ring
  rw [hTeq]
  have h2pa : IsAlgebraic ℚ (2 * (p : ℝ) + 1) := by
    simpa using qa (2 * p + 1)
  exact (((hc.pow _).mul (h2pa.mul hs).inv).sub hsum).mul (qa α).inv

/-- The general theorem really contains the hand-made rung: k = 2 (p = 1) as an instance. -/
example (HL : HermiteLindemann) (T : ℝ) (hT : 0 < T)
    (hcrit : 3 * Real.sinh T * ((1 / 2 : ℚ) * T + ∑ j ∈ Finset.range 2,
        ((if j = 1 then (1 / 4 : ℚ) else 0 : ℚ) : ℝ) * Real.sinh (2 * j * T)) = Real.cosh T ^ 3) :
    Transcendental ℚ (((8 / 9 : ℚ) : ℝ) / Real.sinh T ^ 2) :=
  ladderA_break_transcendental HL 1 T hT (1 / 2) (by norm_num) (fun j => if j = 1 then (1 / 4 : ℚ) else 0)
    (8 / 9) (by norm_num) (by convert hcrit using 3; norm_num)

end Breaks
