import Mathlib
import Mistranslation.PairLaw

/-! # The first trio seat: unconditional trio reduction (2026-10-23; C3 rewrite: no Schanuel hypothesis)

Seat (designed from the pole count, not in the table): e^v = s(s-1), F = 1/(s-2)^2, v = ln 6 at both ends; break
0.418594214924. With del = s_m - 2 (0 < del < 1), sb = 3, its three clocks are
  Lam_inf = ln((1 + sqrt(1 - del^2))/del),   Lam_c = ln( Ncb_c (del + 2 - c) / ((3 - c) Ncm_c) ),  c = 0, 1,
and the time / top conditions are (`v4/sql/trio_hypotheses.sql`: residuals 8e-14, 1e-8; explicit derivative =
numeric derivative):
  a1 Lam_inf + a2 Lam_0 + a3 Lam_1 = sqrt(mu)/2,      a1 = sqrt2 del, a2 = sqrt2 del/sqrt Q0, a3 = del/(sqrt2 sqrt Q1),
  a1' Lam_inf + a2' Lam_0 + a3' Lam_1 = -(a1 Lam_inf' + a2 Lam_0' + a3 Lam_1').
Determinant of the (Lam_inf, Lam_0) block: 2 del^3 / (Q0 sqrt Q0) != 0.
Proved here with no hypothesis: an algebraic break forces all three clocks and their exponentials algebraic over
Q(del, Lam_1). Whether that can happen is the open (Schanuel-type) fact, NOT assumed. -/

namespace TrioSeat

open PairLaw IntermediateField

noncomputable def Q0 (δ : ℝ) : ℝ := 4 - δ ^ 2
noncomputable def Q1 (δ : ℝ) : ℝ := 1 - δ ^ 2
noncomputable def Ncb (c δ : ℝ) : ℝ := 2 * ((c - 2) ^ 2 - δ ^ 2) + 2 * (c - 2) * (3 - c)
  + 2 * Real.sqrt ((c - 2) ^ 2 - δ ^ 2) * Real.sqrt (1 - δ ^ 2)
noncomputable def Ncm (c δ : ℝ) : ℝ := 2 * ((c - 2) ^ 2 - δ ^ 2) + 2 * (c - 2) * (δ + 2 - c)
noncomputable def Ncbd (c δ : ℝ) : ℝ := -4 * δ + 2 * ((-δ / Real.sqrt ((c - 2) ^ 2 - δ ^ 2)) * Real.sqrt (1 - δ ^ 2)
  + Real.sqrt ((c - 2) ^ 2 - δ ^ 2) * (-δ / Real.sqrt (1 - δ ^ 2)))
noncomputable def Ncmd (c δ : ℝ) : ℝ := -4 * δ + 2 * (c - 2)
noncomputable def lamcd (c δ : ℝ) : ℝ := Ncbd c δ / Ncb c δ + 1 / (δ + 2 - c) - Ncmd c δ / Ncm c δ
noncomputable def laminfd (δ : ℝ) : ℝ := (-δ / Real.sqrt (1 - δ ^ 2)) / (1 + Real.sqrt (1 - δ ^ 2)) - 1 / δ

theorem break_reduction {μ δ Li L0 L1 : ℝ} (hμ0 : 0 ≤ μ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hEi : Real.exp Li = (1 + Real.sqrt (1 - δ ^ 2)) / δ)
    (hE0 : Real.exp L0 = Ncb 0 δ * (δ + 2 - 0) / ((3 - 0) * Ncm 0 δ))
    (hE1 : Real.exp L1 = Ncb 1 δ * (δ + 2 - 1) / ((3 - 1) * Ncm 1 δ))
    (h1 : Real.sqrt 2 * δ * Li + Real.sqrt 2 * δ / Real.sqrt (Q0 δ) * L0 + δ / (Real.sqrt 2 * Real.sqrt (Q1 δ)) * L1
      = Real.sqrt μ / 2)
    (h2 : Real.sqrt 2 * Li + Real.sqrt 2 * (1 / Real.sqrt (Q0 δ) + δ ^ 2 / (Q0 δ * Real.sqrt (Q0 δ))) * L0
        + 1 / Real.sqrt 2 * (1 / Real.sqrt (Q1 δ) + δ ^ 2 / (Q1 δ * Real.sqrt (Q1 δ))) * L1
      = -(Real.sqrt 2 * δ * laminfd δ + Real.sqrt 2 * δ / Real.sqrt (Q0 δ) * lamcd 0 δ
        + δ / (Real.sqrt 2 * Real.sqrt (Q1 δ)) * lamcd 1 δ)) :
    IsAlgebraic ℚ μ → TrioAlg δ L1 Li L0 L1 := by
  set F := ℚ⟮δ, L1⟯
  have hδF : IsAlgebraic F δ :=
    isAlgebraic_algebraMap (R := F) (A := ℝ) (⟨δ, subset_adjoin ℚ _ (by simp)⟩ : F)
  have hq : ∀ r : ℚ, IsAlgebraic F (r : ℝ) := fun r =>
    (by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) r : IsAlgebraic ℚ (r : ℝ)).extendScalars
      (algebraMap ℚ F).injective
  have hn : ∀ n : ℕ, IsAlgebraic F (n : ℝ) := fun n => by simpa using hq n
  have hsq : ∀ {y : ℝ}, 0 ≤ y → IsAlgebraic F y → IsAlgebraic F (Real.sqrt y) := fun hy ha =>
    IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [Real.sq_sqrt hy]; exact ha)
  have h1F : IsAlgebraic F (1 : ℝ) := isAlgebraic_one
  have h2F : IsAlgebraic F (2 : ℝ) := by simpa using hn 2
  have h3F : IsAlgebraic F (3 : ℝ) := by simpa using hn 3
  have h4F : IsAlgebraic F (4 : ℝ) := by simpa using hn 4
  have hs2 : IsAlgebraic F (Real.sqrt 2) := hsq (by norm_num) h2F
  have hδ2 : IsAlgebraic F (δ ^ 2) := hδF.pow 2
  have hQ0 : IsAlgebraic F (Q0 δ) := h4F.sub hδ2
  have hQ1 : IsAlgebraic F (Q1 δ) := h1F.sub hδ2
  have hQ0p : 0 < Q0 δ := by unfold Q0; nlinarith
  have hQ1p : 0 < Q1 δ := by unfold Q1; nlinarith
  have hsQ0 := hsq hQ0p.le hQ0
  have hsQ1 := hsq hQ1p.le hQ1
  have hc2 : ∀ c : ℝ, IsAlgebraic F c → 0 ≤ (c - 2) ^ 2 - δ ^ 2 →
      IsAlgebraic F (Real.sqrt ((c - 2) ^ 2 - δ ^ 2)) := fun c hc hp => hsq hp (((hc.sub h2F).pow 2).sub hδ2)
  have h0F : IsAlgebraic F (0 : ℝ) := isAlgebraic_zero
  have hp0 : 0 ≤ ((0 : ℝ) - 2) ^ 2 - δ ^ 2 := by nlinarith
  have hp1 : 0 ≤ ((1 : ℝ) - 2) ^ 2 - δ ^ 2 := by nlinarith
  have hsb : IsAlgebraic F (Real.sqrt (1 - δ ^ 2)) := hsq (by nlinarith) (h1F.sub hδ2)
  have hNcb : ∀ c : ℝ, IsAlgebraic F c → 0 ≤ (c - 2) ^ 2 - δ ^ 2 → IsAlgebraic F (Ncb c δ) := fun c hc hp => by
    unfold Ncb
    exact (((h2F.mul (((hc.sub h2F).pow 2).sub hδ2)).add ((h2F.mul (hc.sub h2F)).mul (h3F.sub hc))).add
      ((h2F.mul (hc2 c hc hp)).mul hsb))
  have hNcm : ∀ c : ℝ, IsAlgebraic F c → IsAlgebraic F (Ncm c δ) := fun c hc => by
    unfold Ncm
    exact (h2F.mul (((hc.sub h2F).pow 2).sub hδ2)).add ((h2F.mul (hc.sub h2F)).mul ((hδF.add h2F).sub hc))
  have hNcbd : ∀ c : ℝ, IsAlgebraic F c → 0 ≤ (c - 2) ^ 2 - δ ^ 2 → IsAlgebraic F (Ncbd c δ) := fun c hc hp => by
    unfold Ncbd
    simp only [div_eq_mul_inv]
    exact ((h4F.neg.mul hδF).add (h2F.mul ((((hδF.neg.mul (hc2 c hc hp).inv)).mul hsb).add
      ((hc2 c hc hp).mul (hδF.neg.mul hsb.inv)))))
  have hNcmd : ∀ c : ℝ, IsAlgebraic F c → IsAlgebraic F (Ncmd c δ) := fun c hc => by
    unfold Ncmd; exact (h4F.neg.mul hδF).add (h2F.mul (hc.sub h2F))
  have hlamcd : ∀ c : ℝ, IsAlgebraic F c → 0 ≤ (c - 2) ^ 2 - δ ^ 2 → IsAlgebraic F (lamcd c δ) := fun c hc hp => by
    unfold lamcd
    simp only [div_eq_mul_inv]
    exact (((hNcbd c hc hp).mul (hNcb c hc hp).inv).add (h1F.mul ((hδF.add h2F).sub hc).inv)).sub
      ((hNcmd c hc).mul (hNcm c hc).inv)
  have hlid : IsAlgebraic F (laminfd δ) := by
    unfold laminfd
    simp only [div_eq_mul_inv]
    exact ((hδF.neg.mul hsb.inv).mul (h1F.add hsb).inv).sub (h1F.mul hδF.inv)
  have hs2p : 0 < Real.sqrt 2 := by positivity
  have hsQ0p : 0 < Real.sqrt (Q0 δ) := Real.sqrt_pos.mpr hQ0p
  refine trio_reduction (z := δ) h1 h2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun hμa => ?_) ?_ ?_ ?_
  · -- determinant of the (Li, L0) block = 2 del^3 / (Q0 sqrt Q0)
    have hsQ : Real.sqrt (Q0 δ) ^ 2 = Q0 δ := Real.sq_sqrt hQ0p.le
    have hs22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have : Real.sqrt 2 * δ * (Real.sqrt 2 * (1 / Real.sqrt (Q0 δ) + δ ^ 2 / (Q0 δ * Real.sqrt (Q0 δ))))
        - Real.sqrt 2 * δ / Real.sqrt (Q0 δ) * Real.sqrt 2 = 2 * δ ^ 3 / (Q0 δ * Real.sqrt (Q0 δ)) := by
      field_simp; rw [hs22]; ring
    rw [this]; positivity
  · exact hs2.mul hδF
  · simp only [div_eq_mul_inv]; exact (hs2.mul hδF).mul hsQ0.inv
  · simp only [div_eq_mul_inv]; exact hδF.mul (hs2.mul hsQ1).inv
  · exact hs2
  · simp only [div_eq_mul_inv]
    exact hs2.mul ((h1F.mul hsQ0.inv).add (hδ2.mul (hQ0.mul hsQ0).inv))
  · simp only [div_eq_mul_inv]
    exact (h1F.mul hs2.inv).mul ((h1F.mul hsQ1.inv).add (hδ2.mul (hQ1.mul hsQ1).inv))
  · simp only [div_eq_mul_inv]
    exact (((hs2.mul hδF).mul hlid).add (((hs2.mul hδF).mul hsQ0.inv).mul (hlamcd 0 h0F hp0))).add
      ((hδF.mul (hs2.mul hsQ1).inv).mul (hlamcd 1 h1F hp1)) |>.neg
  · have hμA : IsAlgebraic ℚ (Real.sqrt μ) :=
      IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [Real.sq_sqrt hμ0]; exact hμa)
    simp only [div_eq_mul_inv]
    exact (hμA.extendScalars (algebraMap ℚ F).injective).mul h2F.inv
  · rw [hEi]; simp only [div_eq_mul_inv]; exact (h1F.add hsb).mul hδF.inv
  · rw [hE0]; simp only [div_eq_mul_inv]
    exact ((hNcb 0 h0F hp0).mul ((hδF.add h2F).sub h0F)).mul ((h3F.sub h0F).mul (hNcm 0 h0F)).inv
  · rw [hE1]; simp only [div_eq_mul_inv]
    exact ((hNcb 1 h1F hp1).mul ((hδF.add h2F).sub h1F)).mul ((h3F.sub h1F).mul (hNcm 1 h1F)).inv

end TrioSeat
