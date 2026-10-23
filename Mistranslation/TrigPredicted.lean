import Mathlib
import Mistranslation.PinneySpring
import Mistranslation.Recipe

/-! # The circle mirror of the predicted family (2026-10-23)

Seat v'' = mu cos v / sin^3 v with cos v = b at both ends (0 < b < 1). u = cos v obeys the plain spring
u'' = -w^2 u, so mu(w) = w^2 (1 - b^2 / cos^2(w/2)); at the top, w b^2 sin(w/2) = 2 cos(w/2) (cos^2(w/2) - b^2) and
  break = 4 (c^2 - b^2)^3 / (b^4 (1 - c^2)),   c = cos(w*/2)   (b = 1/2: 1.244976699699, = quadrature).
Mirror of HypGen's 4 (b^2 - C^2)^3 / (b^4 (C^2 - 1)). One circle clock -> Lindemann-for-sine decides it. -/

namespace TrigPredicted

open Polynomial PinneySpring

/-- **For every algebraic b != 0, the top of the circle-mirror curve is transcendental** (given Lindemann for sine). -/
theorem break_transcendental (LS : LindemannSin) {b w : ℝ} (hbA : IsAlgebraic ℚ b) (hb0 : b ≠ 0) (hb1 : b ^ 2 ≠ 1)
    (hw : 0 < w) (hs : 0 < Real.sin (w / 2)) (hgap : b ^ 2 < Real.cos (w / 2) ^ 2)
    (hcrit : w * b ^ 2 * Real.sin (w / 2) = 2 * Real.cos (w / 2) * (Real.cos (w / 2) ^ 2 - b ^ 2)) :
    Transcendental ℚ (4 * (Real.cos (w / 2) ^ 2 - b ^ 2) ^ 3 / (b ^ 4 * (1 - Real.cos (w / 2) ^ 2))) := by
  intro hμ
  set c := Real.cos (w / 2) with hc
  set s := Real.sin (w / 2) with hsd
  set μ := 4 * (c ^ 2 - b ^ 2) ^ 3 / (b ^ 4 * (1 - c ^ 2)) with hμd
  have hsc : s ^ 2 = 1 - c ^ 2 := by rw [hsd, hc]; linarith [Real.sin_sq_add_cos_sq (w / 2)]
  have h1c : 0 < 1 - c ^ 2 := by rw [← hsc]; positivity
  have hb4 : 0 < b ^ 4 := by positivity
  have hμpos : 0 < μ := by
    rw [hμd]; have : 0 < c ^ 2 - b ^ 2 := by linarith
    positivity
  -- ELIMINATE: c^2 is a root of 4 (X - b^2)^3 - mu b^4 (1 - X), which is -mu b^4 (1 - b^2) at X = b^2
  have hroot : 4 * (c ^ 2 - b ^ 2) ^ 3 - μ * b ^ 4 * (1 - c ^ 2) = 0 := by
    rw [hμd]; field_simp; ring
  let bK := Recipe.toK hbA
  let mK := Recipe.toK hμ
  let P : (algebraicClosure ℚ ℝ)[X] := 4 * (X - C (bK ^ 2)) ^ 3 - C mK * C (bK ^ 4) * (1 - X)
  have hev : ∀ x : ℝ, aeval x P = 4 * (x - b ^ 2) ^ 3 - μ * b ^ 4 * (1 - x) := by
    intro x; simp only [P, map_sub, map_mul, map_pow, map_one, map_ofNat, aeval_C, aeval_X]; rfl
  have hP0 : P ≠ 0 := by
    intro h0
    have := hev (b ^ 2)
    rw [h0, map_zero] at this
    have hne : μ * b ^ 4 * (1 - b ^ 2) ≠ 0 := by
      have : (1 - b ^ 2) ≠ 0 := fun h => hb1 (by linarith)
      exact mul_ne_zero (mul_ne_zero hμpos.ne' hb4.ne') this
    apply hne; linarith
  have hc2 : IsAlgebraic ℚ (c ^ 2) := Recipe.alg_of_root hP0 (by rw [hev]; exact hroot)
  -- DESCEND: c, s, then w from the critical equation
  have hca : IsAlgebraic ℚ c := IsAlgebraic.of_pow (by norm_num) hc2
  have hs2a : IsAlgebraic ℚ (s ^ 2) := by rw [hsc]; exact isAlgebraic_one.sub hc2
  have hsa : IsAlgebraic ℚ s := IsAlgebraic.of_pow (by norm_num) hs2a
  have hweq : w = 2 * c * (c ^ 2 - b ^ 2) * (b ^ 2 * s)⁻¹ := by
    have : b ^ 2 * s ≠ 0 := by positivity
    field_simp; linear_combination hcrit
  have h2 : IsAlgebraic ℚ (2 : ℝ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (2 : ℚ)
  have hwa : IsAlgebraic ℚ w := by
    rw [hweq]; exact ((h2.mul hca).mul (hc2.sub (hbA.pow 2))).mul ((hbA.pow 2).mul hsa).inv
  have hw2 : IsAlgebraic ℚ (w / 2) := by rw [div_eq_mul_inv]; exact hwa.mul h2.inv
  -- CONTRADICT: sin(w/2) algebraic with w/2 algebraic and nonzero
  exact LS (w / 2) hw2 (by positivity) hsa

end TrigPredicted
