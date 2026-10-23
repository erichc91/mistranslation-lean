import Mathlib
import Mistranslation.TimeMap

/-! # Pure-power seats: the peak height, reduced (2026-10-23, Classified Table C5)

Seat x'' + x^m = 0 (m >= 2), x(0) = x(1) = 0, no knob: the peak height A is a fixed number. With
F(y) = y^(m+1)/(m+1), F(A) - F(y) = (A - y) Pm(A, y), Pm(A, y) = (sum_i A^i y^(m-i))/(m+1), homogeneous of degree m,
so the time map scales: T(A) = A / sqrt(A^(m+1)) * T_m(1). Every solution has 1 = 4 T(A)^2 (`TimeMap.push_eq_time_map`),
hence A^(m-1) = 4 T_m(1)^2 and **A is algebraic iff the single integral T_m(1) is** (`peak_reduction`).
T_m(1) is a classical Beta value (sqrt((m+1)/2) B(1/(m+1), 1/2)/(m+1)); its transcendence is Schneider's 1937 theorem,
a proved result that is NOT formalized here, so these seats stay UNRESOLVED in Lean with this reduction. -/

open Set

namespace PurePower

noncomputable def Pm (m : ℕ) (A y : ℝ) : ℝ := (∑ i ∈ Finset.range (m + 1), A ^ i * y ^ (m - i)) / (m + 1)

lemma Pm_hom (m : ℕ) (A u : ℝ) : Pm m A (A * u) = A ^ m * Pm m 1 u := by
  unfold Pm
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mul_pow, one_pow, one_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hi']

lemma factor (m : ℕ) (A y : ℝ) : A ^ (m + 1) / (m + 1) - y ^ (m + 1) / (m + 1) = (A - y) * Pm m A y := by
  unfold Pm
  have h := geom_sum₂_mul A y (m + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [← sub_div, ← h]; ring

lemma integrand_scale (m : ℕ) {A : ℝ} (hA : 0 < A) (s : ℝ) :
    TimeMap.integrand (Pm m) A s = A / Real.sqrt (A ^ (m + 1)) * TimeMap.integrand (Pm m) 1 s := by
  unfold TimeMap.integrand
  rw [show A - A * s ^ 2 = A * (1 - s ^ 2) by ring, Pm_hom, show (1 : ℝ) - 1 * s ^ 2 = 1 - s ^ 2 by ring,
    show 2 * A * (A ^ m * Pm m 1 (1 - s ^ 2)) = A ^ (m + 1) * (2 * 1 * Pm m 1 (1 - s ^ 2)) by ring,
    Real.sqrt_mul (by positivity)]
  rcases eq_or_ne (Real.sqrt (2 * 1 * Pm m 1 (1 - s ^ 2))) 0 with h | h
  · rw [h]; simp
  · have : Real.sqrt (A ^ (m + 1)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp

/-- The time map scales: T(A) = A / sqrt(A^(m+1)) * T_m(1). -/
theorem T_scale (m : ℕ) {A : ℝ} (hA : 0 < A) :
    TimeMap.T (Pm m) A = A / Real.sqrt (A ^ (m + 1)) * TimeMap.T (Pm m) 1 := by
  unfold TimeMap.T
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun s _ => integrand_scale m hA s

/-- **The reduction (unconditional).** If A > 0 and 1 = 4 T(A)^2 with m >= 2, then A is algebraic iff T_m(1) is. -/
theorem alg_iff {m : ℕ} (hm : 2 ≤ m) {A : ℝ} (hA : 0 < A) (h : (1 : ℝ) = 4 * TimeMap.T (Pm m) A ^ 2) :
    IsAlgebraic ℚ A ↔ IsAlgebraic ℚ (TimeMap.T (Pm m) 1) := by
  set T1 := TimeMap.T (Pm m) 1
  rw [T_scale m hA] at h
  have hS : 0 < Real.sqrt (A ^ (m + 1)) := Real.sqrt_pos.mpr (by positivity)
  have hS2 : Real.sqrt (A ^ (m + 1)) ^ 2 = A ^ (m + 1) := Real.sq_sqrt (by positivity)
  -- A^(m-1) = 4 T1^2
  have key : A ^ (m - 1) = 4 * T1 ^ 2 := by
    have e : A ^ (m + 1) = A ^ 2 * A ^ (m - 1) := by rw [← pow_add]; congr 1; omega
    have h' : A ^ (m + 1) = 4 * A ^ 2 * T1 ^ 2 := by
      rw [← hS2]; field_simp at h; nlinarith [h]
    have hA2 : A ^ 2 ≠ 0 := by positivity
    rw [e] at h'
    have := mul_left_cancel₀ hA2 (h'.trans (by ring : 4 * A ^ 2 * T1 ^ 2 = A ^ 2 * (4 * T1 ^ 2)))
    exact this
  constructor
  · intro hAa
    have h4 : T1 ^ 2 = A ^ (m - 1) / 4 := by rw [key]; ring
    have : IsAlgebraic ℚ (T1 ^ 2) := by
      rw [h4, div_eq_mul_inv]
      exact (hAa.pow _).mul (by simpa using (isAlgebraic_algebraMap (4 : ℚ) (A := ℝ)).inv)
    exact IsAlgebraic.of_pow (n := 2) (by norm_num) this
  · intro hT
    have : IsAlgebraic ℚ (A ^ (m - 1)) := by
      rw [key]; simpa using (isAlgebraic_algebraMap (4 : ℚ) (A := ℝ)).mul (hT.pow 2)
    exact IsAlgebraic.of_pow (n := m - 1) (by omega) this

/-- **The pure-power seat, from the ODE.** Every positive solution of x'' + x^m = 0 with peak A has A algebraic iff the
classical integral T_m(1) is algebraic. -/
theorem peak_reduction {m : ℕ} (hm : 2 ≤ m) {A : ℝ} {x x' : ℝ → ℝ}
    (hsol : TippingRule.Sol (fun y => y ^ m) 1 x x') (hpos : ∀ t ∈ Ioo (0:ℝ) 1, 0 < x t)
    (hmax : ∀ t ∈ Icc (0:ℝ) 1, x t ≤ A) (hpeak : ∃ t₀ ∈ Icc (0:ℝ) 1, x t₀ = A) :
    IsAlgebraic ℚ A ↔ IsAlgebraic ℚ (TimeMap.T (Pm m) 1) := by
  have hA : 0 < A := by
    have := hpos (1/2) ⟨by norm_num, by norm_num⟩
    linarith [hmax (1/2) ⟨by norm_num, by norm_num⟩]
  have hF : ∀ y, HasDerivAt (fun y : ℝ => y ^ (m + 1) / (m + 1)) (y ^ m) y := by
    intro y
    have := (hasDerivAt_pow (m + 1) y).div_const ((m : ℝ) + 1)
    convert this using 1
    push_cast; field_simp
  have hPc : Continuous (Pm m A) := by unfold Pm; fun_prop
  have hP : ∀ y ∈ Icc 0 A, 0 < Pm m A y := by
    intro y hy
    unfold Pm
    apply div_pos _ (by positivity)
    rw [Finset.sum_range_succ]
    have : 0 ≤ ∑ i ∈ Finset.range m, A ^ i * y ^ (m - i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg hA.le _) (pow_nonneg hy.1 _)
    have : 0 < A ^ m * y ^ (m - m) := by simp; positivity
    linarith
  have h := TimeMap.push_eq_time_map (f := fun y => y ^ m) (F := fun y => y ^ (m + 1) / (m + 1)) (by fun_prop) hF
    (fun y => factor m A y) hPc hP one_pos hsol hpos hmax hpeak
  exact alg_iff hm hA h

end PurePower

#print axioms PurePower.T_scale
#print axioms PurePower.alg_iff
#print axioms PurePower.peak_reduction
