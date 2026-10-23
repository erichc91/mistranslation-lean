import Mathlib
import Mistranslation.PairLaw

/-! # The Eckart bridge: unconditional pair reduction for every algebraic lam > 0 (2026-10-23; C3 rewrite: no Schanuel)

Seat v'' = mu (cosh v/sinh^3 v + lam/sinh^2 v), cosh v = 2 at both ends (lam = 1: 1.801237242870). With z = e^(2 v_m):
Fm = 2z/(z-1)^2 + lam (z+1)/(z-1), a = Fm - lam, c = Fm + lam, b = -2Fm - 2, N(w) = a w^2 + b w + c, zb = (2+sqrt3)^2:
  K = Lam1/(2 sqrt2 sqrt a) + Lam2/(2 sqrt2 sqrt c),  Lam1 = ln(A(zb)/A(z)), Lam2 = ln(X(zb)/X(z)),
closed form = quadrature to 1e-11; explicit top equation = numeric derivative (`v4/sql/eckart_pair.sql`).
Determinant lam Fm'/(8 a c sqrt a sqrt c): nonzero for lam != 0 (Fm' < 0). At lam = 0 the two clocks merge
(ratio sqrt(a/c) = 1): that is the predicted family, rank 1, decided unconditionally by HL.
Proved here with no hypothesis: an algebraic break forces both clocks and their exponentials algebraic over Q(z).
Whether that can happen is the open (Schanuel-type) fact, NOT assumed. -/

namespace EckartPair

open PairLaw IntermediateField

noncomputable def zb : ℝ := (2 + Real.sqrt 3) ^ 2
noncomputable def Fm (l z : ℝ) : ℝ := 2 * z / (z - 1) ^ 2 + l * (z + 1) / (z - 1)
noncomputable def Fd (l z : ℝ) : ℝ := (-2 * z - 2 - 2 * l * (z - 1)) / (z - 1) ^ 3
noncomputable def aa (l z : ℝ) : ℝ := Fm l z - l
noncomputable def cc (l z : ℝ) : ℝ := Fm l z + l
noncomputable def bb (l z : ℝ) : ℝ := -2 * Fm l z - 2
noncomputable def NB (l z : ℝ) : ℝ := aa l z * zb ^ 2 + bb l z * zb + cc l z
noncomputable def NBd (l z : ℝ) : ℝ := Fd l z * (zb - 1) ^ 2
noncomputable def AB (l z : ℝ) : ℝ := 2 * Real.sqrt (aa l z) * Real.sqrt (NB l z) + 2 * aa l z * zb + bb l z
noncomputable def ABd (l z : ℝ) : ℝ := 2 * (Fd l z / (2 * Real.sqrt (aa l z)) * Real.sqrt (NB l z)
  + Real.sqrt (aa l z) * NBd l z / (2 * Real.sqrt (NB l z))) + 2 * Fd l z * zb - 2 * Fd l z
noncomputable def AM (l z : ℝ) : ℝ := 2 * aa l z * z + bb l z
noncomputable def AMd (l z : ℝ) : ℝ := 2 * Fd l z * z + 2 * aa l z - 2 * Fd l z
noncomputable def XB (l z : ℝ) : ℝ := (2 * cc l z + bb l z * zb + 2 * Real.sqrt (cc l z) * Real.sqrt (NB l z)) / zb
noncomputable def XBd (l z : ℝ) : ℝ := (2 * Fd l z - 2 * Fd l z * zb + 2 * (Fd l z / (2 * Real.sqrt (cc l z))
  * Real.sqrt (NB l z) + Real.sqrt (cc l z) * NBd l z / (2 * Real.sqrt (NB l z)))) / zb
noncomputable def XM (l z : ℝ) : ℝ := (2 * cc l z + bb l z * z) / z
noncomputable def XMd (l z : ℝ) : ℝ := (2 * Fd l z - 2 * Fd l z * z + bb l z) / z - (2 * cc l z + bb l z * z) / (z * z)

theorem break_reduction {μ l z L1 L2 : ℝ} (hμ0 : 0 ≤ μ) (hl : 0 < l)
    (hlA : IsAlgebraic ℚ l) (hz : 1 < z) (ha : 0 < aa l z) (hNB : 0 ≤ NB l z)
    (hE1 : Real.exp L1 = AB l z / AM l z) (hE2 : Real.exp L2 = XB l z / XM l z)
    (h1 : 1 / (2 * Real.sqrt 2 * Real.sqrt (aa l z)) * L1 + 1 / (2 * Real.sqrt 2 * Real.sqrt (cc l z)) * L2
      = Real.sqrt μ / 2)
    (h2 : -Fd l z / (4 * Real.sqrt 2 * aa l z * Real.sqrt (aa l z)) * L1
        + -Fd l z / (4 * Real.sqrt 2 * cc l z * Real.sqrt (cc l z)) * L2
      = -(1 / (2 * Real.sqrt 2 * Real.sqrt (aa l z)) * (ABd l z / AB l z - AMd l z / AM l z)
        + 1 / (2 * Real.sqrt 2 * Real.sqrt (cc l z)) * (XBd l z / XB l z - XMd l z / XM l z))) :
    IsAlgebraic ℚ μ → PairAlg z L1 L2 := by
  set F := ℚ⟮z⟯
  have hzF : IsAlgebraic F z :=
    isAlgebraic_algebraMap (R := F) (A := ℝ) (⟨z, mem_adjoin_simple_self ℚ z⟩ : F)
  have hlF : IsAlgebraic F l := alg_up hlA
  have hn : ∀ n : ℕ, IsAlgebraic F (n : ℝ) := fun n =>
    alg_up (by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (n : ℚ))
  have h1F : IsAlgebraic F (1 : ℝ) := isAlgebraic_one
  have h2F : IsAlgebraic F (2 : ℝ) := by simpa using hn 2
  have h3F : IsAlgebraic F (3 : ℝ) := by simpa using hn 3
  have h4F : IsAlgebraic F (4 : ℝ) := by simpa using hn 4
  have hsq : ∀ {y : ℝ}, 0 ≤ y → IsAlgebraic F y → IsAlgebraic F (Real.sqrt y) := fun hy hA =>
    IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [Real.sq_sqrt hy]; exact hA)
  have hs2 := hsq (by norm_num) h2F
  have hzbF : IsAlgebraic F zb := by unfold zb; exact (h2F.add (hsq (by norm_num) h3F)).pow 2
  have hFm : IsAlgebraic F (Fm l z) := by
    unfold Fm; simp only [div_eq_mul_inv]
    exact ((h2F.mul hzF).mul ((hzF.sub h1F).pow 2).inv).add ((hlF.mul (hzF.add h1F)).mul (hzF.sub h1F).inv)
  have hFd : IsAlgebraic F (Fd l z) := by
    unfold Fd; simp only [div_eq_mul_inv]
    exact ((((h2F.neg.mul hzF).sub h2F).sub ((h2F.mul hlF).mul (hzF.sub h1F)))).mul ((hzF.sub h1F).pow 3).inv
  have haF : IsAlgebraic F (aa l z) := by unfold aa; exact hFm.sub hlF
  have hcF : IsAlgebraic F (cc l z) := by unfold cc; exact hFm.add hlF
  have hbF : IsAlgebraic F (bb l z) := by unfold bb; exact (h2F.neg.mul hFm).sub h2F
  have hc : 0 < cc l z := by unfold cc; unfold aa at ha; linarith
  have hNBF : IsAlgebraic F (NB l z) := by unfold NB; exact ((haF.mul (hzbF.pow 2)).add (hbF.mul hzbF)).add hcF
  have hNBdF : IsAlgebraic F (NBd l z) := by unfold NBd; exact hFd.mul ((hzbF.sub h1F).pow 2)
  have hsa := hsq ha.le haF
  have hsc := hsq hc.le hcF
  have hsN := hsq hNB hNBF
  have hAB : IsAlgebraic F (AB l z) := by
    unfold AB; exact (((h2F.mul hsa).mul hsN).add ((h2F.mul haF).mul hzbF)).add hbF
  have hABd : IsAlgebraic F (ABd l z) := by
    unfold ABd; simp only [div_eq_mul_inv]
    exact ((h2F.mul (((hFd.mul (h2F.mul hsa).inv).mul hsN).add ((hsa.mul hNBdF).mul (h2F.mul hsN).inv))).add
      ((h2F.mul hFd).mul hzbF)).sub (h2F.mul hFd)
  have hAM : IsAlgebraic F (AM l z) := by unfold AM; exact ((h2F.mul haF).mul hzF).add hbF
  have hAMd : IsAlgebraic F (AMd l z) := by
    unfold AMd; exact (((h2F.mul hFd).mul hzF).add (h2F.mul haF)).sub (h2F.mul hFd)
  have hXB : IsAlgebraic F (XB l z) := by
    unfold XB; simp only [div_eq_mul_inv]
    exact (((h2F.mul hcF).add (hbF.mul hzbF)).add ((h2F.mul hsc).mul hsN)).mul hzbF.inv
  have hXBd : IsAlgebraic F (XBd l z) := by
    unfold XBd; simp only [div_eq_mul_inv]
    exact ((((h2F.mul hFd).sub ((h2F.mul hFd).mul hzbF)).add (h2F.mul (((hFd.mul (h2F.mul hsc).inv).mul hsN).add
      ((hsc.mul hNBdF).mul (h2F.mul hsN).inv))))).mul hzbF.inv
  have hXM : IsAlgebraic F (XM l z) := by
    unfold XM; simp only [div_eq_mul_inv]; exact ((h2F.mul hcF).add (hbF.mul hzF)).mul hzF.inv
  have hXMd : IsAlgebraic F (XMd l z) := by
    unfold XMd; simp only [div_eq_mul_inv]
    exact ((((h2F.mul hFd).sub ((h2F.mul hFd).mul hzF)).add hbF).mul hzF.inv).sub
      (((h2F.mul hcF).add (hbF.mul hzF)).mul (hzF.mul hzF).inv)
  have hden1 : IsAlgebraic F (2 * Real.sqrt 2 * Real.sqrt (aa l z)) := (h2F.mul hs2).mul hsa
  have hden2 : IsAlgebraic F (2 * Real.sqrt 2 * Real.sqrt (cc l z)) := (h2F.mul hs2).mul hsc
  refine pair_reduction (z := z) h1 h2 ?_ ?_ ?_ ?_ ?_ ?_ (fun hμa => ?_) ?_ ?_
  · -- determinant = l Fd / (8 a c sqrt a sqrt c), nonzero since Fd < 0
    have hsa2 : Real.sqrt (aa l z) ^ 2 = aa l z := Real.sq_sqrt ha.le
    have hsc2 : Real.sqrt (cc l z) ^ 2 = cc l z := Real.sq_sqrt hc.le
    have hs22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpa : 0 < Real.sqrt (aa l z) := Real.sqrt_pos.mpr ha
    have hpc : 0 < Real.sqrt (cc l z) := Real.sqrt_pos.mpr hc
    have hp2 : 0 < Real.sqrt 2 := by positivity
    have hca : cc l z - aa l z = 2 * l := by unfold cc aa; ring
    have : 1 / (2 * Real.sqrt 2 * Real.sqrt (aa l z)) * (-Fd l z / (4 * Real.sqrt 2 * cc l z * Real.sqrt (cc l z)))
        - 1 / (2 * Real.sqrt 2 * Real.sqrt (cc l z)) * (-Fd l z / (4 * Real.sqrt 2 * aa l z * Real.sqrt (aa l z)))
        = l * Fd l z / (8 * aa l z * cc l z * Real.sqrt (aa l z) * Real.sqrt (cc l z)) := by
      field_simp; rw [hs22]; linear_combination (8 * Fd l z) * hca
    rw [this]
    have hFdneg : Fd l z < 0 := by
      unfold Fd; apply div_neg_of_neg_of_pos
      · nlinarith
      · have : 0 < z - 1 := by linarith
        positivity
    exact div_ne_zero (mul_ne_zero hl.ne' hFdneg.ne) (by positivity)
  · simp only [div_eq_mul_inv]; exact h1F.mul hden1.inv
  · simp only [div_eq_mul_inv]; exact h1F.mul hden2.inv
  · simp only [div_eq_mul_inv]; exact hFd.neg.mul (((h4F.mul hs2).mul haF).mul hsa).inv
  · simp only [div_eq_mul_inv]; exact hFd.neg.mul (((h4F.mul hs2).mul hcF).mul hsc).inv
  · simp only [div_eq_mul_inv]
    exact (((h1F.mul hden1.inv).mul ((hABd.mul hAB.inv).sub (hAMd.mul hAM.inv))).add
      ((h1F.mul hden2.inv).mul ((hXBd.mul hXB.inv).sub (hXMd.mul hXM.inv)))).neg
  · have hμA : IsAlgebraic ℚ (Real.sqrt μ) :=
      IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [Real.sq_sqrt hμ0]; exact hμa)
    simp only [div_eq_mul_inv]; exact (alg_up hμA).mul h2F.inv
  · rw [hE1]; simp only [div_eq_mul_inv]; exact hAB.mul hAM.inv
  · rw [hE2]; simp only [div_eq_mul_inv]; exact hXB.mul hXM.inv

end EckartPair
