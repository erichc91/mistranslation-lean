import Mathlib
import Mistranslation.PairLaw

/-! # The csch^2 seat: unconditional pair reduction (2026-10-23; C3 rewrite: no Schanuel hypothesis)

Seat v'' = mu / sinh^2 v, cosh v = 2 at both ends (break 4.216700584248). With z = e^(2 v_m) at the turning point and
zb = 7 + 4 sqrt 3, its two clocks are L1 = ln X1, L2 = ln X2 (X1, X2 explicit algebraic functions of z), and at the
top they satisfy (`v4/sql/csch2_pair_hypotheses.sql`, residuals 3e-14 and 2e-10)
  (1) a1 L1 + a2 L2 = sqrt(mu)/2,       a1 = sqrt(z-1)/4,  a2 = a1/sqrt z
  (2) a1' L1 + a2' L2 = -(a1 L1' + a2 L2')
with determinant -(z-1)/(32 z sqrt z) != 0. An algebraic break would force both clocks and their exponentials algebraic over Q(z) (proved below, no
hypothesis). Whether that can happen is the open fact (Schanuel-type), NOT assumed. Clock independence over Q is
measured (no relation with integer coefficients up to 60, `v4/sql/pair_independence.sql`). -/

namespace Csch2Pair

open PairLaw IntermediateField

theorem break_reduction {μ z L1 L2 : ℝ} (hμ0 : 0 ≤ μ) (hz : 1 < z)
    (hzb : z < 7 + 4 * Real.sqrt 3)
    (hX1 : Real.exp L1 = (2 * Real.sqrt ((7 + 4 * Real.sqrt 3 - 1) * (7 + 4 * Real.sqrt 3 - z))
      + 2 * (7 + 4 * Real.sqrt 3) - 1 - z) / (z - 1))
    (hX2 : Real.exp L2 = (2 * z - (1 + z) * (7 + 4 * Real.sqrt 3)
      + 2 * Real.sqrt (z * ((7 + 4 * Real.sqrt 3 - 1) * (7 + 4 * Real.sqrt 3 - z)))) / ((1 - z) * (7 + 4 * Real.sqrt 3)))
    (h1 : Real.sqrt (z - 1) / 4 * L1 + Real.sqrt (z - 1) / (4 * Real.sqrt z) * L2 = Real.sqrt μ / 2)
    {d1 d2 : ℝ}
    (h2 : 1 / (8 * Real.sqrt (z - 1)) * L1
        + (1 / (8 * Real.sqrt (z - 1) * Real.sqrt z) - Real.sqrt (z - 1) / (8 * z * Real.sqrt z)) * L2
      = -(Real.sqrt (z - 1) / 4 * d1 + Real.sqrt (z - 1) / (4 * Real.sqrt z) * d2))
    (hd1 : d1 = (-(7 + 4 * Real.sqrt 3 - 1) / Real.sqrt ((7 + 4 * Real.sqrt 3 - 1) * (7 + 4 * Real.sqrt 3 - z)) - 1)
      / (2 * Real.sqrt ((7 + 4 * Real.sqrt 3 - 1) * (7 + 4 * Real.sqrt 3 - z)) + 2 * (7 + 4 * Real.sqrt 3) - 1 - z)
      - 1 / (z - 1))
    (hd2 : d2 = (2 - (7 + 4 * Real.sqrt 3) + ((7 + 4 * Real.sqrt 3 - 1) * (7 + 4 * Real.sqrt 3 - z) - z * (7 + 4 * Real.sqrt 3 - 1))
        / Real.sqrt (z * ((7 + 4 * Real.sqrt 3 - 1) * (7 + 4 * Real.sqrt 3 - z))))
      / (2 * z - (1 + z) * (7 + 4 * Real.sqrt 3) + 2 * Real.sqrt (z * ((7 + 4 * Real.sqrt 3 - 1) * (7 + 4 * Real.sqrt 3 - z))))
      - 1 / (z - 1)) :
    IsAlgebraic ℚ μ → PairAlg z L1 L2 := by
  set F := ℚ⟮z⟯
  have hzF : IsAlgebraic F z :=
    isAlgebraic_algebraMap (R := F) (A := ℝ) (⟨z, mem_adjoin_simple_self ℚ z⟩ : F)
  have hq : ∀ r : ℚ, IsAlgebraic F (r : ℝ) := fun r => alg_up (by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) r)
  have h1F : IsAlgebraic F (1 : ℝ) := isAlgebraic_one
  have h2F : IsAlgebraic F (2 : ℝ) := by simpa using hq 2
  have h4F : IsAlgebraic F (4 : ℝ) := by simpa using hq 4
  have h7F : IsAlgebraic F (7 : ℝ) := by simpa using hq 7
  have h8F : IsAlgebraic F (8 : ℝ) := by simpa using hq 8
  have h3F : IsAlgebraic F (3 : ℝ) := by simpa using hq 3
  have hsq : ∀ {y : ℝ}, 0 ≤ y → IsAlgebraic F y → IsAlgebraic F (Real.sqrt y) := fun hy ha =>
    IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [Real.sq_sqrt hy]; exact ha)
  have hs3 : IsAlgebraic F (Real.sqrt 3) := hsq (by norm_num) h3F
  have hzbF : IsAlgebraic F (7 + 4 * Real.sqrt 3) := h7F.add (h4F.mul hs3)
  have hz1 : 0 ≤ z - 1 := by linarith
  have hsz1 : IsAlgebraic F (Real.sqrt (z - 1)) := hsq hz1 (hzF.sub h1F)
  have hszF : IsAlgebraic F (Real.sqrt z) := hsq (by linarith) hzF
  have hpos1 : 0 < Real.sqrt (z - 1) := Real.sqrt_pos.mpr (by linarith)
  have hposz : 0 < Real.sqrt z := Real.sqrt_pos.mpr (by linarith)
  have hQ : 0 ≤ (7 + 4 * Real.sqrt 3 - 1) * (7 + 4 * Real.sqrt 3 - z) := by
    have : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    apply mul_nonneg <;> linarith
  have hQF : IsAlgebraic F ((7 + 4 * Real.sqrt 3 - 1) * (7 + 4 * Real.sqrt 3 - z)) := (hzbF.sub h1F).mul (hzbF.sub hzF)
  have hsQ := hsq hQ hQF
  have hsZQ := hsq (mul_nonneg (by linarith) hQ) (hzF.mul hQF)
  refine pair_reduction (z := z) h1 h2 ?_ ?_ ?_ ?_ ?_ ?_ (fun hμa => ?_) ?_ ?_
  · -- determinant = -(z-1)/(32 z sqrt z)
    have hs1 : Real.sqrt (z - 1) ^ 2 = z - 1 := Real.sq_sqrt hz1
    have : Real.sqrt (z - 1) / 4 * (1 / (8 * Real.sqrt (z - 1) * Real.sqrt z) - Real.sqrt (z - 1) / (8 * z * Real.sqrt z))
        - Real.sqrt (z - 1) / (4 * Real.sqrt z) * (1 / (8 * Real.sqrt (z - 1))) = -(z - 1) / (32 * z * Real.sqrt z) := by
      field_simp; rw [hs1]; ring
    rw [this]
    have : 0 < z - 1 := by linarith
    have : 0 < 32 * z * Real.sqrt z := by positivity
    exact div_ne_zero (by linarith) this.ne'
  · exact hsz1.mul h4F.inv
  · exact hsz1.mul (h4F.mul hszF).inv
  · exact h1F.mul (h8F.mul hsz1).inv
  · exact (h1F.mul ((h8F.mul hsz1).mul hszF).inv).sub (hsz1.mul ((h8F.mul hzF).mul hszF).inv)
  · have hzb1 : IsAlgebraic F (7 + 4 * Real.sqrt 3 - 1) := hzbF.sub h1F
    have hd1A : IsAlgebraic F d1 := by
      rw [hd1, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      exact (((hzb1.neg.mul hsQ.inv).sub h1F).mul
        ((((h2F.mul hsQ).add (h2F.mul hzbF)).sub h1F).sub hzF).inv).sub (h1F.mul (hzF.sub h1F).inv)
    have hd2A : IsAlgebraic F d2 := by
      rw [hd2, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      exact ((((h2F.sub hzbF).add ((hQF.sub (hzF.mul hzb1)).mul hsZQ.inv))).mul
        (((h2F.mul hzF).sub ((h1F.add hzF).mul hzbF)).add (h2F.mul hsZQ)).inv).sub (h1F.mul (hzF.sub h1F).inv)
    exact ((hsz1.mul h4F.inv).mul hd1A |>.add ((hsz1.mul (h4F.mul hszF).inv).mul hd2A)).neg
  · have hμA : IsAlgebraic ℚ (Real.sqrt μ) :=
      IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [Real.sq_sqrt hμ0]; exact hμa)
    exact (alg_up hμA).mul h2F.inv
  · rw [hX1]
    exact ((((h2F.mul hsQ).add (h2F.mul hzbF)).sub h1F).sub hzF).mul (hzF.sub h1F).inv
  · rw [hX2]
    exact (((h2F.mul hzF).sub ((h1F.add hzF).mul hzbF)).add (h2F.mul hsZQ)).mul ((h1F.sub hzF).mul hzbF).inv

end Csch2Pair
