import Mathlib
import Mistranslation.TimeMap

/-! # The time map, converse: every admissible peak is realised (2026-10-23)

Companion to `Mistranslation/TimeMap.lean` (which proves every solution has push `4 T(A)^2`).

* `time_map_exists` -- for every `A > 0` with `P(A, .) > 0` on `[0, A]` and `P(A, .)` differentiable
  (automatic for polynomial seats), there is a `TippingRule.Sol` solution with push `4 T(A)^2`,
  `x > 0` on `(0,1)`, `x <= A`, and peak `x(1/2) = A`. Construction: `G` = primitive of the
  (clamped) integrand is an order isomorphism of the reals; `s(t) = G^{-1}(T (1 - 2t))`,
  `x = A - A s^2`, `x' = 2T s sqrt(2A P(A, x))`; `x'' = -mu f(x)` reduces to the derivative identity
  `f(y) = P(A,y) - (A - y) d/dy P(A,y)` (`deriv_identity`). No `f(A) > 0` hypothesis is needed.
* `Weakening.weakening_no_break` -- for `f y = 1 - y^k` (`k >= 1`) every push `mu > 0` is solvable:
  `T` is continuous on `(0,1)` (parametric integral), `T(A) <= 2 sqrt A` for `A <= 1/2`,
  `T(1 - c^2) >= log((1+c)/c) / sqrt(2k)` for `c <= 1/2`, then IVT + `time_map_exists`.
  This closes the existence half that `TippingRule.weakening_le_one` left open.

Prior art: time-map / quadrature method (Gelfand 1963, Laetsch 1970).
-/

open Set Filter Topology MeasureTheory

namespace TimeMapExists

open TimeMap

/-- Clamp to `[-1, 1]`. -/
noncomputable def clamp (r : ℝ) : ℝ := max (-1) (min r 1)

lemma clamp_mem (r : ℝ) : clamp r ∈ Icc (-1:ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

lemma clamp_of_mem {r : ℝ} (h : r ∈ Icc (-1:ℝ) 1) : clamp r = r := by
  simp [clamp, h.1, h.2]

lemma continuous_clamp : Continuous clamp :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The derivative identity: differentiating `F(A) - F(y) = (A - y) P(A, y)` in `y`. -/
lemma deriv_identity {f F q : ℝ → ℝ} {A : ℝ} (hF : ∀ y, HasDerivAt F (f y) y)
    (hFP : ∀ y, F A - F y = (A - y) * q y) (hqd : Differentiable ℝ q) (y : ℝ) :
    f y = q y - (A - y) * deriv q y := by
  have h1 : HasDerivAt (fun y => F A - F y) (-f y) y := (hF y).const_sub _
  have h2 : HasDerivAt (fun y => (A - y) * q y) (-1 * q y + (A - y) * deriv q y) y := by
    have := ((hasDerivAt_id y).const_sub A).mul (hqd y).hasDerivAt
    exact this.congr_deriv (by simp)
  have e : (fun y => F A - F y) = fun y => (A - y) * q y := funext hFP
  rw [e] at h1
  have := h1.unique h2
  linarith

/-- **Existence.** Every admissible peak `A` is realised by a solution with push `4 T(A)^2`. -/
theorem time_map_exists {f F : ℝ → ℝ} {P : ℝ → ℝ → ℝ} {A : ℝ}
    (hF : ∀ y, HasDerivAt F (f y) y) (hFP : ∀ y, F A - F y = (A - y) * P A y)
    (hPd : Differentiable ℝ (P A)) (hA : 0 < A) (hP : ∀ y ∈ Icc 0 A, 0 < P A y) :
    ∃ x x' : ℝ → ℝ, TippingRule.Sol f (4 * T P A ^ 2) x x' ∧
      (∀ t ∈ Ioo (0:ℝ) 1, 0 < x t) ∧ (∀ t ∈ Icc (0:ℝ) 1, x t ≤ A) ∧ x (1/2) = A := by
  set q := P A with hq
  have hid := deriv_identity hF hFP hPd
  have hPc : Continuous q := hPd.continuous
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
  set τ := T P A with hτ
  -- clamped integrand and its primitive
  set gc : ℝ → ℝ := fun r => g (clamp r) with hgc
  have hgcc : Continuous gc := hgcont.comp_continuous continuous_clamp clamp_mem
  have hgcpos : ∀ r, 0 < gc r := fun r => hgpos _ (clamp_mem r)
  have hgc_eq : ∀ r ∈ Icc (-1:ℝ) 1, gc r = g r := fun r hr => by simp only [hgc, clamp_of_mem hr]
  obtain ⟨r₀, hr₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by norm_num : (-1:ℝ) ≤ 1)) hgcont
  set m := g r₀
  have hm : 0 < m := hgpos r₀ hr₀
  have hmle : ∀ r, m ≤ gc r := fun r => hmin (clamp_mem r)
  set Gc : ℝ → ℝ := fun u => ∫ r in (0:ℝ)..u, gc r with hGc
  have hGcd : ∀ u, HasDerivAt Gc (gc u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hgcc.intervalIntegrable _ _)
      (hgcc.stronglyMeasurableAtFilter _ _) hgcc.continuousAt
  have hmono : StrictMono Gc := strictMono_of_hasDerivAt_pos hGcd hgcpos
  have hG0 : Gc 0 = 0 := by simp [hGc]
  have hlin : Monotone (fun u => Gc u - m * u) :=
    monotone_of_hasDerivAt_nonneg (fun u => (hGcd u).sub ((hasDerivAt_id u).const_mul m))
      (fun u => by simp; linarith [hmle u])
  have htop : Tendsto Gc atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop hm)
    filter_upwards [eventually_ge_atTop 0] with u hu
    have := hlin hu; simp only [hG0] at this; simp at this ⊢; linarith
  have hbot : Tendsto Gc atBot atBot := by
    refine tendsto_atBot_mono' atBot ?_ (tendsto_id.const_mul_atBot hm)
    filter_upwards [eventually_le_atBot 0] with u hu
    have := hlin hu; simp only [hG0] at this; simp at this ⊢; linarith
  have hsurj : Function.Surjective Gc :=
    (continuous_iff_continuousAt.mpr fun u => (hGcd u).continuousAt).surjective htop hbot
  set e := StrictMono.orderIsoOfSurjective Gc hmono hsurj with he_def
  have he : ∀ z, e z = Gc z := fun z => rfl
  have hG1 : Gc 1 = τ := by
    simp only [hGc, hτ, T]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le zero_le_one] at hr
    exact hgc_eq r ⟨by linarith [hr.1], hr.2⟩
  have hGm1 : Gc (-1) = -τ := by
    have e1 : (∫ r in (0:ℝ)..(-1), gc r) = ∫ r in (0:ℝ)..(-1), g (-r) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_ge (by norm_num)] at hr
      rw [hgc_eq r ⟨hr.1, by linarith [hr.2]⟩]
      simp [hg, integrand]
    simp only [hGc]
    rw [e1, intervalIntegral.integral_comp_neg, intervalIntegral.integral_symm]
    simp [hτ, T, hg]
  have hs1 : e.symm τ = 1 := e.symm_apply_eq.mpr (by rw [he, hG1])
  have hsm1 : e.symm (-τ) = -1 := e.symm_apply_eq.mpr (by rw [he, hGm1])
  have hs0 : e.symm 0 = 0 := e.symm_apply_eq.mpr (by rw [he, hG0])
  have hτpos : 0 < τ := by
    have := hmono (show (0:ℝ) < 1 by norm_num); rw [hG0, hG1] at this; exact this
  -- the phase s(t) = G⁻¹(τ (1 - 2t))
  set s : ℝ → ℝ := fun t => e.symm (τ * (1 - 2 * t)) with hs
  have hsd : ∀ t, HasDerivAt s ((gc (s t))⁻¹ * (τ * -(2 * 1))) t := by
    intro t
    have hinv : HasDerivAt e.symm (gc (e.symm (τ * (1 - 2 * t))))⁻¹ (τ * (1 - 2 * t)) :=
      HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (hGcd _) (hgcpos _).ne'
        (Eventually.of_forall fun y => by rw [← he]; exact e.apply_symm_apply y)
    exact hinv.comp t ((((hasDerivAt_id t).const_mul 2).const_sub 1).const_mul τ)
  have hsI : ∀ t ∈ Icc (0:ℝ) 1, s t ∈ Icc (-1:ℝ) 1 := by
    intro t ht
    constructor
    · rw [← hsm1]; exact e.symm.monotone (by nlinarith [ht.1, ht.2])
    · rw [← hs1]; exact e.symm.monotone (by nlinarith [ht.1, ht.2])
  have hsIoo : ∀ t ∈ Ioo (0:ℝ) 1, s t ∈ Ioo (-1:ℝ) 1 := by
    intro t ht
    constructor
    · rw [← hsm1]; exact e.symm.strictMono (by nlinarith [ht.1, ht.2])
    · rw [← hs1]; exact e.symm.strictMono (by nlinarith [ht.1, ht.2])
  -- k(r) = sqrt(2 A q(A - A r^2)), so g = 2A / k on [-1, 1]
  set k : ℝ → ℝ := fun r => Real.sqrt (2 * A * q (A - A * r ^ 2)) with hk
  have hkpos : ∀ r ∈ Icc (-1:ℝ) 1, 0 < k r := fun r hr => by
    have := hP _ (hgarg r hr); exact Real.sqrt_pos.mpr (by positivity)
  have hkd : ∀ r ∈ Icc (-1:ℝ) 1, HasDerivAt k
      (2 * A * (deriv q (A - A * r ^ 2) * -(A * (↑2 * r ^ (2 - 1)))) /
        (2 * Real.sqrt (2 * A * q (A - A * r ^ 2)))) r := by
    intro r hr
    have hin := (((hPd _).hasDerivAt.comp r (((hasDerivAt_pow 2 r).const_mul A).const_sub A)).const_mul
      (2 * A))
    have := hP _ (hgarg r hr)
    exact hin.sqrt (mul_pos (mul_pos two_pos hA) this).ne'
  refine ⟨fun t => A - A * s t ^ 2, fun t => 2 * τ * (s t * k (s t)), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro t ht
    have hst := hsI t ht
    have hK := hkpos _ hst
    have hgs : gc (s t) = 2 * A / k (s t) := by rw [hgc_eq _ hst]; rfl
    constructor
    · refine (((hsd t).pow 2).const_mul A).const_sub A |>.congr_deriv ?_
      rw [hgs]; field_simp; ring
    · refine (((hsd t).mul ((hkd _ hst).comp t (hsd t))).const_mul (2 * τ)).congr_deriv ?_
      rw [hgs, hid (A - A * s t ^ 2)]
      have hK2 : q (A - A * s t ^ 2) = k (s t) ^ 2 / (2 * A) := by
        simp only [hk]; rw [Real.sq_sqrt (by have := hP _ (hgarg _ hst); positivity)]; field_simp
      simp only [Function.comp_apply]
      rw [show Real.sqrt (2 * A * q (A - A * s t ^ 2)) = k (s t) from rfl, hK2]
      field_simp
      ring
  · show A - A * s 0 ^ 2 = 0
    simp only [hs]; rw [show τ * (1 - 2 * 0) = τ by ring, hs1]; ring
  · show A - A * s 1 ^ 2 = 0
    simp only [hs]; rw [show τ * (1 - 2 * 1) = -τ by ring, hsm1]; ring
  · intro t ht
    have h := hsIoo t ht
    have : s t ^ 2 < 1 := by nlinarith [h.1, h.2]
    show 0 < A - A * s t ^ 2
    nlinarith
  · intro t _
    show A - A * s t ^ 2 ≤ A
    nlinarith [sq_nonneg (s t)]
  · show A - A * s (1/2) ^ 2 = A
    simp only [hs]; rw [show τ * (1 - 2 * (1/2)) = 0 by ring, hs0]; ring

/-! ## The weakening seat `f y = 1 - y^k` -/

namespace Weakening

/-- `S = sum_{j <= k} A^j y^(k-j)`, so `A^(k+1) - y^(k+1) = (A - y) S`. -/
noncomputable def S (k : ℕ) (A y : ℝ) : ℝ := ∑ j ∈ Finset.range (k + 1), A ^ j * y ^ (k + 1 - 1 - j)

/-- The factor `P(A, y) = 1 - S / (k + 1)`. -/
noncomputable def P (k : ℕ) (A y : ℝ) : ℝ := 1 - S k A y / (k + 1)

/-- The potential `F y = y - y^(k+1) / (k+1)`, `F' = 1 - y^k`. -/
noncomputable def F (k : ℕ) (y : ℝ) : ℝ := y - y ^ (k + 1) / (k + 1)

lemma hasDerivAt_F (k : ℕ) (y : ℝ) : HasDerivAt (F k) (1 - y ^ k) y := by
  have h := (hasDerivAt_id y).sub ((hasDerivAt_pow (k + 1) y).div_const ((k : ℝ) + 1))
  refine h.congr_deriv ?_
  have : ((k : ℝ) + 1) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  field_simp

lemma factor (k : ℕ) (A y : ℝ) : F k A - F k y = (A - y) * P k A y := by
  have h : S k A y * (A - y) = A ^ (k + 1) - y ^ (k + 1) := geom_sum₂_mul A y (k + 1)
  calc F k A - F k y = (A - y) - (A ^ (k + 1) - y ^ (k + 1)) / (k + 1) := by simp only [F]; ring
    _ = (A - y) * P k A y := by rw [← h]; simp only [P]; ring

lemma S_bounds (k : ℕ) {A y : ℝ} (hy : 0 ≤ y) (hyA : y ≤ A) :
    ((k : ℝ) + 1) * y ^ k ≤ S k A y ∧ S k A y ≤ ((k : ℝ) + 1) * A ^ k := by
  have hA : 0 ≤ A := hy.trans hyA
  have hsplit : ∀ j ∈ Finset.range (k + 1), k + 1 - 1 - j + j = k := by
    intro j hj; have := Finset.mem_range.mp hj; omega
  constructor
  · have : ∑ _j ∈ Finset.range (k + 1), y ^ k ≤ S k A y := by
      refine Finset.sum_le_sum fun j hj => ?_
      calc y ^ k = y ^ j * y ^ (k + 1 - 1 - j) := by rw [← pow_add, add_comm, hsplit j hj]
        _ ≤ A ^ j * y ^ (k + 1 - 1 - j) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy hyA j) (pow_nonneg hy _)
    simpa using this
  · have : S k A y ≤ ∑ _j ∈ Finset.range (k + 1), A ^ k := by
      refine Finset.sum_le_sum fun j hj => ?_
      calc A ^ j * y ^ (k + 1 - 1 - j) ≤ A ^ j * A ^ (k + 1 - 1 - j) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hyA _) (pow_nonneg hA _)
        _ = A ^ k := by rw [← pow_add, add_comm, hsplit j hj]
    simpa using this

lemma P_bounds (k : ℕ) {A y : ℝ} (hy : 0 ≤ y) (hyA : y ≤ A) :
    1 - A ^ k ≤ P k A y ∧ P k A y ≤ 1 - y ^ k := by
  obtain ⟨h1, h2⟩ := S_bounds k hy hyA
  have hk : (0 : ℝ) < k + 1 := by positivity
  simp only [P]
  constructor
  · have : S k A y / (k + 1) ≤ A ^ k := by rw [div_le_iff₀ hk]; linarith
    linarith
  · have : y ^ k ≤ S k A y / (k + 1) := by rw [le_div_iff₀ hk]; linarith
    linarith

lemma P_differentiable (k : ℕ) (A : ℝ) : Differentiable ℝ (P k A) := by
  unfold P S; fun_prop

lemma P_pos (k : ℕ) (hk : 1 ≤ k) {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    ∀ y ∈ Icc 0 A, 0 < P k A y := by
  intro y hy
  have := (P_bounds k hy.1 hy.2).1
  have : A ^ k < 1 := pow_lt_one₀ hA0.le hA1 (by omega)
  linarith

lemma integrand_contOn (k : ℕ) (hk : 1 ≤ k) {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    ContinuousOn (integrand (P k) A) (Icc (-1) 1) := by
  have hP := P_pos k hk hA0 hA1
  have hgarg : ∀ r ∈ Icc (-1:ℝ) 1, A - A * r ^ 2 ∈ Icc 0 A := by
    intro r hr
    have : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
    constructor <;> nlinarith [sq_nonneg r]
  refine continuousOn_const.div ?_ ?_
  · exact Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul
      (((P_differentiable k A).continuous.comp
        (continuous_const.sub (continuous_const.mul (continuous_pow 2)))).continuousOn))
  · intro r hr; have := hP _ (hgarg r hr)
    exact (Real.sqrt_pos.mpr (by positivity)).ne'

lemma intInt (k : ℕ) (hk : 1 ≤ k) {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    IntervalIntegrable (integrand (P k) A) volume 0 1 :=
  ((integrand_contOn k hk hA0 hA1).mono (by rw [uIcc_of_le zero_le_one]; exact Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable

lemma integrand_le (k : ℕ) (hk : 1 ≤ k) {A s : ℝ} (hA : 0 < A) (hA2 : A ≤ 1/2)
    (hs : s ∈ Icc (0:ℝ) 1) : integrand (P k) A s ≤ 2 * Real.sqrt A := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  have hy0 : 0 ≤ A - A * s ^ 2 := by nlinarith
  have hyA : A - A * s ^ 2 ≤ A := by nlinarith [sq_nonneg s]
  have hP := (P_bounds k hy0 hyA).1
  have hAk : A ^ k ≤ A := pow_le_of_le_one hA.le (by linarith) (by omega)
  have hP2 : 1/2 ≤ P k A (A - A * s ^ 2) := by linarith
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hden : Real.sqrt A ≤ Real.sqrt (2 * A * P k A (A - A * s ^ 2)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  unfold integrand
  calc 2 * A / Real.sqrt (2 * A * P k A (A - A * s ^ 2)) ≤ 2 * A / Real.sqrt A :=
        div_le_div_of_nonneg_left (by positivity) hsA hden
    _ = 2 * Real.sqrt A := by
        rw [div_eq_iff hsA.ne']; nth_rewrite 1 [← Real.mul_self_sqrt hA.le]; ring

lemma two_k_pos (k : ℕ) (hk : 1 ≤ k) : (0:ℝ) < 2 * k := by
  have : (1:ℝ) ≤ k := by exact_mod_cast hk
  linarith

lemma integrand_ge (k : ℕ) (hk : 1 ≤ k) {c s : ℝ} (hc : 0 < c) (hc2 : c ≤ 1/2)
    (hs : s ∈ Icc (0:ℝ) 1) :
    (Real.sqrt (2 * k))⁻¹ * (s + c)⁻¹ ≤ integrand (P k) (1 - c ^ 2) s := by
  have hA : 1/2 ≤ 1 - c ^ 2 := by nlinarith
  have hA1 : 1 - c ^ 2 < 1 := by nlinarith
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  set A := 1 - c ^ 2 with hAdef
  set y := A - A * s ^ 2 with hy
  have hy0 : 0 ≤ y := by nlinarith
  have hyA : y ≤ A := by nlinarith [sq_nonneg s]
  have hPhi := (P_bounds k hy0 hyA).2
  have hPpos : 0 < P k A y := P_pos k hk (by linarith) hA1 y ⟨hy0, hyA⟩
  have hbern : 1 - y ^ k ≤ k * (1 - y) := by
    have := one_add_mul_le_pow (show (-2:ℝ) ≤ y - 1 by linarith) k
    simp only [add_sub_cancel] at this
    linarith
  have h1y : 1 - y ≤ (s + c) ^ 2 := by nlinarith [hs.1, hs.2]
  have hkpos := two_k_pos k hk
  have hP : 2 * A * P k A y ≤ 2 * k * (s + c) ^ 2 := by
    have h3 : P k A y ≤ k * (s + c) ^ 2 := by
      have : (0:ℝ) ≤ k := by positivity
      nlinarith
    nlinarith
  have hsc : 0 < s + c := by linarith [hs.1]
  have hD : Real.sqrt (2 * A * P k A y) ≤ Real.sqrt (2 * k) * (s + c) := by
    rw [← Real.sqrt_sq hsc.le, ← Real.sqrt_mul hkpos.le]; exact Real.sqrt_le_sqrt hP
  have hDpos : 0 < Real.sqrt (2 * A * P k A y) := Real.sqrt_pos.mpr (by positivity)
  unfold integrand
  rw [← mul_inv]
  calc (Real.sqrt (2 * k) * (s + c))⁻¹ ≤ (Real.sqrt (2 * A * P k A y))⁻¹ := inv_anti₀ hDpos hD
    _ ≤ 2 * A / Real.sqrt (2 * A * P k A y) := by
        rw [div_eq_mul_inv]; have := inv_pos.mpr hDpos; nlinarith

lemma T_le (k : ℕ) (hk : 1 ≤ k) {A : ℝ} (hA : 0 < A) (hA2 : A ≤ 1/2) :
    T (P k) A ≤ 2 * Real.sqrt A := by
  unfold T
  calc (∫ s in (0:ℝ)..1, integrand (P k) A s) ≤ ∫ s in (0:ℝ)..1, 2 * Real.sqrt A :=
        intervalIntegral.integral_mono_on zero_le_one (intInt k hk hA (by linarith))
          intervalIntegrable_const (fun s hs => integrand_le k hk hA hA2 hs)
    _ = 2 * Real.sqrt A := by simp

lemma T_ge (k : ℕ) (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1/2) :
    (Real.sqrt (2 * k))⁻¹ * Real.log ((1 + c) / c) ≤ T (P k) (1 - c ^ 2) := by
  have hA0 : 0 < 1 - c ^ 2 := by nlinarith
  have hA1 : 1 - c ^ 2 < 1 := by nlinarith
  have hli : IntervalIntegrable (fun s => (Real.sqrt (2 * k))⁻¹ * (s + c)⁻¹) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul ((continuousOn_id.add continuousOn_const).inv₀ ?_)
    intro s hs; rw [uIcc_of_le zero_le_one] at hs; show s + c ≠ 0; exact (by linarith [hs.1] : 0 < s + c).ne'
  have hval : (∫ s in (0:ℝ)..1, (Real.sqrt (2 * k))⁻¹ * (s + c)⁻¹) =
      (Real.sqrt (2 * k))⁻¹ * Real.log ((1 + c) / c) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun x => x⁻¹) c, zero_add,
      integral_inv_of_pos hc (by linarith), add_comm]
  rw [← hval]
  unfold T
  exact intervalIntegral.integral_mono_on zero_le_one hli (intInt k hk hA0 hA1)
    (fun s hs => integrand_ge k hk hc hc2 hs)

lemma T_contOn (k : ℕ) (hk : 1 ≤ k) : ContinuousOn (T (P k)) (Ioo 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  set Φ : (Ioo (0:ℝ) 1) × ℝ → ℝ := fun p =>
    2 * (p.1 : ℝ) / Real.sqrt (2 * p.1 * P k p.1 (p.1 - p.1 * clamp p.2 ^ 2)) with hΦ
  have hΦc : Continuous Φ := by
    refine Continuous.div (by fun_prop) ?_ ?_
    · refine Real.continuous_sqrt.comp ?_
      have hc : Continuous fun p : (Ioo (0:ℝ) 1) × ℝ => clamp p.2 :=
        continuous_clamp.comp continuous_snd
      unfold P S
      fun_prop
    · intro p
      have h1 := p.1.2
      have hr := clamp_mem p.2
      have : clamp p.2 ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
      have := P_pos k hk h1.1 h1.2 ((p.1 : ℝ) - p.1 * clamp p.2 ^ 2)
        ⟨by nlinarith [h1.1], by nlinarith [sq_nonneg (clamp p.2), h1.1]⟩
      exact (Real.sqrt_pos.mpr (by have := h1.1; positivity)).ne'
  have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun a s => Φ (a, s)) (μ := volume) hΦc 0 1
  convert this using 1
  funext a
  simp only [domRestrict_apply, T]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  simp only [hΦ, integrand, clamp_of_mem (⟨by linarith [hs.1], hs.2⟩ : s ∈ Icc (-1:ℝ) 1)]

/-- **The weakening seat has no break number.** For `f y = 1 - y^k` (`k >= 1`), every push
`mu > 0` has a solution: the half time `T` is continuous on `(0,1)`, `T(A) <= 2 sqrt A` near `0`,
`T(1 - c^2) >= log((1+c)/c) / sqrt(2k)` near `1`, so by the intermediate value theorem
`sqrt(mu)/2 = T(A)` for some `A`, and `time_map_exists` builds the solution. -/
theorem weakening_no_break {k : ℕ} (hk : 1 ≤ k) :
    TippingRule.Pushes (fun y => 1 - y ^ k) = Ioi 0 ∧
      ¬ BddAbove (TippingRule.Pushes (fun y => 1 - y ^ k)) := by
  refine TippingRule.no_break_of_forall fun μ hμ => ?_
  set τ := Real.sqrt μ / 2 with hτ
  have hτpos : 0 < τ := by have := Real.sqrt_pos.mpr hμ; positivity
  have hkpos := two_k_pos k hk
  -- small end
  set A₁ := min (1/2) (τ ^ 2 / 16) with hA₁
  have hA₁pos : 0 < A₁ := lt_min (by norm_num) (by positivity)
  have hA₁le : A₁ ≤ 1/2 := min_le_left _ _
  have hT₁ : T (P k) A₁ ≤ τ := by
    have h1 := T_le k hk hA₁pos hA₁le
    have h2 : Real.sqrt A₁ ≤ τ / 4 := by
      rw [show τ / 4 = Real.sqrt ((τ / 4) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      refine Real.sqrt_le_sqrt ((min_le_right _ _).trans (le_of_eq ?_))
      ring
    linarith
  -- large end
  set L := τ * Real.sqrt (2 * k) with hL
  set c := 1 / (Real.exp L + 2) with hc
  have hexp := Real.exp_pos L
  have hcpos : 0 < c := by positivity
  have hc2 : c ≤ 1/2 := by rw [hc, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hT₂ : τ ≤ T (P k) (1 - c ^ 2) := by
    have h1 := T_ge k hk hcpos hc2
    have hs := Real.sqrt_pos.mpr hkpos
    have hlog : L ≤ Real.log ((1 + c) / c) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      rw [hc]; field_simp; linarith
    have : τ = (Real.sqrt (2 * k))⁻¹ * L := by rw [hL]; field_simp
    rw [this]
    exact le_trans (mul_le_mul_of_nonneg_left hlog (by positivity)) h1
  have hA₂ : 1/2 ≤ 1 - c ^ 2 := by nlinarith
  have hA₂1 : 1 - c ^ 2 < 1 := by nlinarith
  have hsub : Icc A₁ (1 - c ^ 2) ⊆ Ioo 0 1 :=
    fun a ha => ⟨by linarith [ha.1], by linarith [ha.2]⟩
  obtain ⟨A, hA, hTA⟩ := intermediate_value_Icc (by linarith) ((T_contOn k hk).mono hsub)
    ⟨hT₁, hT₂⟩
  obtain ⟨x, x', hsol, -⟩ := time_map_exists (F := F k) (fun y => hasDerivAt_F k y) (factor k A)
    (P_differentiable k A) (hsub hA).1 (P_pos k hk (hsub hA).1 (hsub hA).2)
  have hμ4 : 4 * T (P k) A ^ 2 = μ := by
    rw [hTA, hτ, div_pow, Real.sq_sqrt hμ.le]; ring
  rw [hμ4] at hsol
  exact ⟨x, x', hsol⟩

end Weakening

end TimeMapExists

#print axioms TimeMapExists.deriv_identity
#print axioms TimeMapExists.time_map_exists
#print axioms TimeMapExists.Weakening.factor
#print axioms TimeMapExists.Weakening.T_contOn
#print axioms TimeMapExists.Weakening.T_le
#print axioms TimeMapExists.Weakening.T_ge
#print axioms TimeMapExists.Weakening.weakening_no_break
