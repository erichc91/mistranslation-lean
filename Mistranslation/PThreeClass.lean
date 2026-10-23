import Mathlib
import Mistranslation.Recipe
import Mistranslation.PinneySpring

/-! # P_3 pair: the class step through the recipe (2026-10-23)

P_3 (`v'' = mu v^(-5/3) + kap v^(-1/3)`, found by the closable-family generator). With u = v^(2/3), turning point x,
q = mu/kap and u = p + r cosh(eta) (p = (x - q/x)/2, r = (x + q/x)/2), the time condition and the top condition are
  (1) (x^2 - q) T + (x^2 + q) S = 2 k x,          k^2 = kap/3,
  (2) (x^2+q)^3 S T + (x^2-q)(x^2+q)^2 S^2 + 4 x^2 (q - 2 x q - x^2) = 0,
with cosh T = C, (x^2+q) C = 2x - x^2 + q, (x^2+q)^2 S^2 = 4x(1-x)(x+q). Both are LINEAR in the clock T.
Eliminating T: G(x) = x M^2 - (kap/3)(1-x)(x+q)(x^2+q)^4 = 0, M = 4qx(1-x)(x+q) - (x^2-q)(q - 2xq - x^2),
G(0) = -kap q^5/3 != 0. Checked numerically at the real tops (`v4/sql/p3_elimination_check.sql`, sign change of G). -/

namespace PThree

open Polynomial

/-- **P_3 class step (kap > 0, exponential clock).** -/
theorem class_of_crit (HL : Breaks.HermiteLindemann) {kap μ q x T S C k : ℝ}
    (hk0 : 0 < kap) (hkap : IsAlgebraic ℚ kap) (hμ0 : 0 < μ) (hq : q * kap = μ)
    (hx : 0 < x) (hT : 0 < T) (hS : 0 < S) (hk : 3 * k ^ 2 = kap)
    (hC : (x ^ 2 + q) * C = 2 * x - x ^ 2 + q) (hS2 : (x ^ 2 + q) ^ 2 * S ^ 2 = 4 * x * (1 - x) * (x + q))
    (h1 : (x ^ 2 - q) * T + (x ^ 2 + q) * S = 2 * k * x)
    (h2 : (x ^ 2 + q) ^ 3 * S * T + (x ^ 2 - q) * (x ^ 2 + q) ^ 2 * S ^ 2 + 4 * x ^ 2 * (q - 2 * x * q - x ^ 2) = 0)
    (hexp : Real.exp T = C + S) :
    Transcendental ℚ μ := by
  have hqpos : 0 < q := by
    rcases lt_or_ge 0 q with h | h
    · exact h
    · nlinarith
  have hD : 0 < x ^ 2 + q := by positivity
  set M := 4 * q * x * (1 - x) * (x + q) - (x ^ 2 - q) * (q - 2 * x * q - x ^ 2) with hM
  have hA : 4 * x ^ 2 * M = 2 * k * x * (x ^ 2 + q) ^ 3 * S := by
    rw [hM]
    linear_combination ((x ^ 2 + q) ^ 3 * S) * h1 - (x ^ 2 - q) * h2 - 4 * x ^ 2 * q * hS2
  have hB : 2 * x * M = k * (x ^ 2 + q) ^ 3 * S := by
    have : 2 * x * (2 * x * M - k * (x ^ 2 + q) ^ 3 * S) = 0 := by linear_combination hA
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · linarith
  have hG4 : 4 * x ^ 2 * (x * M ^ 2 - k ^ 2 * (x ^ 2 + q) ^ 4 * (1 - x) * (x + q)) = 0 := by
    linear_combination x * (2 * x * M + k * (x ^ 2 + q) ^ 3 * S) * hB + x * k ^ 2 * (x ^ 2 + q) ^ 4 * hS2
  have hG : x * M ^ 2 - kap / 3 * (1 - x) * (x + q) * (x ^ 2 + q) ^ 4 = 0 := by
    rcases mul_eq_zero.mp hG4 with h0 | h0
    · have : 0 < 4 * x ^ 2 := by positivity
      linarith
    · rw [← hk]; linear_combination h0
  have h2a : IsAlgebraic ℚ (2 : ℝ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (2 : ℚ)
  have h4a : IsAlgebraic ℚ (4 : ℝ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (4 : ℚ)
  have h1a : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_one
  have hqa : IsAlgebraic ℚ μ → IsAlgebraic ℚ q := fun hμa => by
    have : q = μ * kap⁻¹ := by field_simp; linarith
    rw [this]; exact hμa.mul hkap.inv
  refine Recipe.transcendental_of_recipe' HL (z := x) (T := T) (c1 := (x ^ 2 + q) ^ 3 * S)
    (c0 := -((x ^ 2 - q) * (x ^ 2 + q) ^ 2 * S ^ 2 + 4 * x ^ 2 * (q - 2 * x * q - x ^ 2)))
    hT.ne' (by linear_combination h2) (by positivity) (fun hμa => ?_) (fun hμa hxQ => ?_)
  · -- ELIMINATE
    let qK := Recipe.toK (hqa hμa)
    let kK := Recipe.toK hkap
    let MX : (algebraicClosure ℚ ℝ)[X] := 4 * Polynomial.C qK * X * (1 - X) * (X + Polynomial.C qK) - (X ^ 2 - Polynomial.C qK) * (Polynomial.C qK - 2 * X * Polynomial.C qK - X ^ 2)
    let P : (algebraicClosure ℚ ℝ)[X] := X * MX ^ 2 - Polynomial.C (kK / 3) * (1 - X) * (X + Polynomial.C qK) * (X ^ 2 + Polynomial.C qK) ^ 4
    have hev : ∀ y : ℝ, aeval y P = y * (4 * q * y * (1 - y) * (y + q) - (y ^ 2 - q) * (q - 2 * y * q - y ^ 2)) ^ 2
        - kap / 3 * (1 - y) * (y + q) * (y ^ 2 + q) ^ 4 := by
      intro y
      simp only [P, MX, map_sub, map_mul, map_pow, map_add, map_one, map_ofNat, aeval_C, aeval_X, map_div₀]
      rfl
    refine ⟨P, fun h0 => ?_, by rw [hev]; rw [hM] at hG; linear_combination hG⟩
    have := hev 0
    rw [h0, map_zero] at this
    have : 0 < kap / 3 * q ^ 5 := by positivity
    nlinarith
  · -- DESCEND
    have hqA := hqa hμa
    have hDa : IsAlgebraic ℚ (x ^ 2 + q) := (hxQ.pow 2).add hqA
    have hS2a : IsAlgebraic ℚ (S ^ 2) := by
      have : S ^ 2 = 4 * x * (1 - x) * (x + q) * ((x ^ 2 + q) ^ 2)⁻¹ := by field_simp; linear_combination hS2
      rw [this]; exact (((h4a.mul hxQ).mul (h1a.sub hxQ)).mul (hxQ.add hqA)).mul (hDa.pow 2).inv
    have hSa : IsAlgebraic ℚ S := IsAlgebraic.of_pow (by norm_num) hS2a
    have hCa : IsAlgebraic ℚ C := by
      have : C = (2 * x - x ^ 2 + q) * (x ^ 2 + q)⁻¹ := by field_simp; linear_combination hC
      rw [this]; exact (((h2a.mul hxQ).sub (hxQ.pow 2)).add hqA).mul hDa.inv
    refine ⟨(hDa.pow 3).mul hSa, ?_, by rw [hexp]; exact hCa.add hSa⟩
    exact ((((hxQ.pow 2).sub hqA).mul (hDa.pow 2)).mul (hSa.pow 2) |>.add
      ((h4a.mul (hxQ.pow 2)).mul ((hqA.sub ((h2a.mul hxQ).mul hqA)).sub (hxQ.pow 2)))).neg


/-- **P_3 class step, circle side (kap < 0): same polynomial G, clock = arccos, Lindemann for sine.**
Here u = p - r cos(eta), sin T = S, (x^2+q)^2 S^2 = -4x(1-x)(x+q), 3k^2 = -kap, and the top condition flips the
sign of its last term. -/
theorem class_of_crit_circle (LS : PinneySpring.LindemannSin) {kap μ q x T S C k : ℝ}
    (hk0 : kap < 0) (hkap : IsAlgebraic ℚ kap) (hμ0 : 0 < μ) (hq : q * kap = μ)
    (hx : 0 < x) (hD : x ^ 2 + q < 0) (hT : 0 < T) (hS : 0 < S) (hk : 3 * k ^ 2 = -kap)
    (hC : (x ^ 2 + q) * C = 2 * x - x ^ 2 + q) (hS2 : (x ^ 2 + q) ^ 2 * S ^ 2 = -(4 * x * (1 - x) * (x + q)))
    (h1 : (x ^ 2 - q) * T + (x ^ 2 + q) * S = 2 * k * x)
    (h2 : (x ^ 2 + q) ^ 3 * S * T + (x ^ 2 - q) * (x ^ 2 + q) ^ 2 * S ^ 2 - 4 * x ^ 2 * (q - 2 * x * q - x ^ 2) = 0)
    (hsin : Real.sin T = S) :
    Transcendental ℚ μ := by
  intro hμa
  have hDne : x ^ 2 + q ≠ 0 := hD.ne
  have hqneg : q < 0 := by nlinarith
  set M := 4 * q * x * (1 - x) * (x + q) - (x ^ 2 - q) * (q - 2 * x * q - x ^ 2) with hM
  have hA : -4 * x ^ 2 * M = 2 * k * x * (x ^ 2 + q) ^ 3 * S := by
    rw [hM]
    linear_combination ((x ^ 2 + q) ^ 3 * S) * h1 - (x ^ 2 - q) * h2 - 4 * x ^ 2 * q * hS2
  have hB : -2 * x * M = k * (x ^ 2 + q) ^ 3 * S := by
    have : 2 * x * (-2 * x * M - k * (x ^ 2 + q) ^ 3 * S) = 0 := by linear_combination hA
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · linarith
  have hG4 : 4 * x ^ 2 * (x * M ^ 2 + k ^ 2 * (x ^ 2 + q) ^ 4 * (1 - x) * (x + q)) = 0 := by
    linear_combination (-x * (2 * x * M - k * (x ^ 2 + q) ^ 3 * S)) * hB + x * k ^ 2 * (x ^ 2 + q) ^ 4 * hS2
  have hG : x * M ^ 2 - kap / 3 * (1 - x) * (x + q) * (x ^ 2 + q) ^ 4 = 0 := by
    rcases mul_eq_zero.mp hG4 with h0 | h0
    · have : 0 < 4 * x ^ 2 := by positivity
      linarith
    · have : kap = -(3 * k ^ 2) := by linarith
      rw [this]; linear_combination h0
  have h2a : IsAlgebraic ℚ (2 : ℝ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (2 : ℚ)
  have h4a : IsAlgebraic ℚ (4 : ℝ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (4 : ℚ)
  have h1a : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_one
  have hkne : kap ≠ 0 := hk0.ne
  have hqA : IsAlgebraic ℚ q := by
    have : q = μ * kap⁻¹ := by field_simp; linarith
    rw [this]; exact hμa.mul hkap.inv
  -- ELIMINATE (same polynomial as the exponential side)
  let qK := Recipe.toK hqA
  let kK := Recipe.toK hkap
  let MX : (algebraicClosure ℚ ℝ)[X] := 4 * Polynomial.C qK * X * (1 - X) * (X + Polynomial.C qK)
    - (X ^ 2 - Polynomial.C qK) * (Polynomial.C qK - 2 * X * Polynomial.C qK - X ^ 2)
  let P : (algebraicClosure ℚ ℝ)[X] := X * MX ^ 2 - Polynomial.C (kK / 3) * (1 - X) * (X + Polynomial.C qK)
    * (X ^ 2 + Polynomial.C qK) ^ 4
  have hev : ∀ y : ℝ, aeval y P = y * (4 * q * y * (1 - y) * (y + q) - (y ^ 2 - q) * (q - 2 * y * q - y ^ 2)) ^ 2
      - kap / 3 * (1 - y) * (y + q) * (y ^ 2 + q) ^ 4 := by
    intro y
    simp only [P, MX, map_sub, map_mul, map_pow, map_add, map_one, map_ofNat, aeval_C, aeval_X]
    rfl
  have hP0 : P ≠ 0 := by
    intro h0
    have := hev 0
    rw [h0, map_zero] at this
    have hnq : 0 < -q := by linarith
    have : 0 < -kap / 3 * (-q) ^ 5 := mul_pos (by linarith) (pow_pos hnq 5)
    nlinarith
  have hxQ : IsAlgebraic ℚ x := Recipe.alg_of_root hP0 (by rw [hev]; rw [hM] at hG; linear_combination hG)
  -- DESCEND
  have hDa : IsAlgebraic ℚ (x ^ 2 + q) := (hxQ.pow 2).add hqA
  have hS2a : IsAlgebraic ℚ (S ^ 2) := by
    have : S ^ 2 = -(4 * x * (1 - x) * (x + q)) * ((x ^ 2 + q) ^ 2)⁻¹ := by field_simp; linear_combination hS2
    rw [this]; exact ((((h4a.mul hxQ).mul (h1a.sub hxQ)).mul (hxQ.add hqA)).neg).mul (hDa.pow 2).inv
  have hSa : IsAlgebraic ℚ S := IsAlgebraic.of_pow (by norm_num) hS2a
  have hTeq : T = ((4 * x ^ 2 * (q - 2 * x * q - x ^ 2)) - (x ^ 2 - q) * (x ^ 2 + q) ^ 2 * S ^ 2)
      * ((x ^ 2 + q) ^ 3 * S)⁻¹ := by
    have : (x ^ 2 + q) ^ 3 * S ≠ 0 := mul_ne_zero (pow_ne_zero 3 hDne) hS.ne'
    field_simp; linear_combination h2
  have hTa : IsAlgebraic ℚ T := by
    rw [hTeq]
    exact (((h4a.mul (hxQ.pow 2)).mul ((hqA.sub ((h2a.mul hxQ).mul hqA)).sub (hxQ.pow 2))).sub
      ((((hxQ.pow 2).sub hqA).mul (hDa.pow 2)).mul (hSa.pow 2))).mul ((hDa.pow 3).mul hSa).inv
  exact LS T hTa hT.ne' (by rw [hsin]; exact hSa)

end PThree
