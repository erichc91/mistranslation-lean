import Mathlib
import Mistranslation.MorseBreak
import Mistranslation.Breaks
import Mistranslation.Recipe

/-! # The Morse break is transcendental for every algebraic lam >= 0 (2026-10-23)

Given Hermite-Lindemann (an explicit hypothesis, not in this Mathlib). No genericity assumption.
1. Calculus: the top c* of fm has fm'(c*) = 0; differentiating the energy tie implicitly turns that into the
   critical equation  c C s (p + lam) = 2 (2 Y p + (Y+1) lam + 2),  Y = s^2 = sinh^2(c/2), C = cosh(c/2).
2. Elimination: with mu = c^2 p, the tie and the critical equation force p to be a root of
     P(X) = mu (1 - (2+lam) X)(1 - X)^2 (X + lam)^2 - 4 X (lam + 2X - (2+lam) X^2)^2,
   and P(1/(2+lam)) = -4/(2+lam) (lam + 1/(2+lam))^2 < 0, so P is not the zero polynomial.
3. If mu were algebraic: p algebraic -> Y, s, C algebraic -> c algebraic (critical equation) -> e^(c/2) = C + s
   algebraic with c/2 algebraic and nonzero: contradicts Hermite-Lindemann. -/

namespace MorseOde

open Polynomial in
/-- **The class step**, pure algebra. -/
theorem class_of_crit (HL : Breaks.HermiteLindemann) {lam c s ch Y p μ : ℝ}
    (hl : 0 ≤ lam) (hlam : IsAlgebraic ℚ lam) (hc : 0 < c) (hs0 : 0 < s) (hch : 0 < ch) (hp : 0 < p)
    (hsY : s ^ 2 = Y) (hCY : ch ^ 2 = Y + 1)
    (hroot : Y * p ^ 2 + ((Y + 1) * lam + 2) * p - 1 = 0)
    (hcrit : c * (ch * s * (p + lam)) = 2 * (2 * Y * p + (Y + 1) * lam + 2))
    (hμ : μ = c ^ 2 * p) (hexp : Real.exp (c / 2) = ch + s) :
    Transcendental ℚ μ := by
  -- the squared critical equation, in Y only
  have H : μ * Y * (Y + 1) * (p + lam) ^ 2 = 4 * p * (2 * Y * p + (Y + 1) * lam + 2) ^ 2 := by
    linear_combination (Y * (Y + 1) * (p + lam) ^ 2) * hμ - (c ^ 2 * p * (p + lam) ^ 2 * ch ^ 2) * hsY
      - (c ^ 2 * p * (p + lam) ^ 2 * Y) * hCY
      + (p * (c * (ch * s * (p + lam)) + 2 * (2 * Y * p + (Y + 1) * lam + 2))) * hcrit
  have hA : Y * p * (p + lam) = 1 - (2 + lam) * p := by linear_combination hroot
  have hB : (Y + 1) * p * (p + lam) = (1 - p) ^ 2 := by linear_combination hroot
  have hD : p * (2 * Y * p + (Y + 1) * lam + 2) = Y * p ^ 2 + 1 := by linear_combination hroot
  have hE : (Y * p ^ 2 + 1) * (p + lam) = lam + 2 * p - (2 + lam) * p ^ 2 := by linear_combination p * hA
  have hF : p * (2 * Y * p + (Y + 1) * lam + 2) * (p + lam) = lam + 2 * p - (2 + lam) * p ^ 2 := by
    linear_combination (p + lam) * hD + hE
  have hG : (Y * p * (p + lam)) * ((Y + 1) * p * (p + lam)) = (1 - (2 + lam) * p) * (1 - p) ^ 2 := by
    linear_combination (1 - p) ^ 2 * hA + (Y * p * (p + lam)) * hB
  have T : μ * (1 - (2 + lam) * p) * (1 - p) ^ 2 * (p + lam) ^ 2
      - 4 * p * (lam + 2 * p - (2 + lam) * p ^ 2) ^ 2 = 0 := by
    linear_combination (-(μ * (p + lam) ^ 2)) * hG + (p ^ 2 * (p + lam) ^ 2) * H
      + (4 * p * (p * (2 * Y * p + (Y + 1) * lam + 2) * (p + lam) + (lam + 2 * p - (2 + lam) * p ^ 2))) * hF
  have hpl : 0 < p + lam := by linarith
  have h2 : IsAlgebraic ℚ (2 : ℝ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (2 : ℚ)
  have h1 : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_one
  refine Recipe.transcendental_of_recipe HL (z := p) (T := c / 2)
    (c1 := 2 * (ch * s * (p + lam))) (c0 := 2 * (2 * Y * p + (Y + 1) * lam + 2))
    (by positivity) (by linear_combination hcrit) (by positivity) (fun hμa => ?_) (fun hpQ => ?_)
  · -- ELIMINATE: p is a root of the quintic, nonzero at 1/(2+lam)
    let mK := Recipe.toK hμa
    let lK := Recipe.toK hlam
    let P : (algebraicClosure ℚ ℝ)[X] := C mK * (1 - C (2 + lK) * X) * (1 - X) ^ 2 * (X + C lK) ^ 2
      - 4 * X * (C lK + 2 * X - C (2 + lK) * X ^ 2) ^ 2
    have hev : ∀ x : ℝ, aeval x P = μ * (1 - (2 + lam) * x) * (1 - x) ^ 2 * (x + lam) ^ 2
        - 4 * x * (lam + 2 * x - (2 + lam) * x ^ 2) ^ 2 := by
      intro x
      simp only [P, map_sub, map_mul, map_pow, map_add, map_one, map_ofNat, aeval_C, aeval_X]
      rfl
    refine ⟨P, fun h0 => ?_, by rw [hev]; linarith [T]⟩
    have h1 := hev (1 / (2 + lam))
    rw [h0, map_zero] at h1
    have h2 : 0 < 2 + lam := by linarith
    have h3 : 1 - (2 + lam) * (1 / (2 + lam)) = 0 := by field_simp; ring
    have h4 : lam + 2 * (1 / (2 + lam)) - (2 + lam) * (1 / (2 + lam)) ^ 2 = lam + 1 / (2 + lam) := by
      field_simp; ring
    rw [h3, h4] at h1
    have h5 : 0 < lam + 1 / (2 + lam) := by positivity
    have h6 : 0 < 4 * (1 / (2 + lam)) * (lam + 1 / (2 + lam)) ^ 2 := by positivity
    linarith
  · -- DESCEND: p -> Y -> s, C -> the critical coefficients and e^(c/2) = C + s
    have hYeq : Y = (1 - (2 + lam) * p) * (p * (p + lam))⁻¹ := by
      field_simp; linear_combination hA
    have hYa : IsAlgebraic ℚ Y := by
      rw [hYeq]; exact (h1.sub ((h2.add hlam).mul hpQ)).mul (hpQ.mul (hpQ.add hlam)).inv
    have hsa : IsAlgebraic ℚ s := IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [hsY]; exact hYa)
    have hca : IsAlgebraic ℚ ch := IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [hCY]; exact hYa.add h1)
    exact ⟨h2.mul ((hca.mul hsa).mul (hpQ.add hlam)),
      h2.mul ((((h2.mul hYa).mul hpQ).add ((hYa.add h1).mul hlam)).add h2), by rw [hexp]; exact hca.add hsa⟩

/-- **The calculus step**: at a global top of fm, the critical equation holds. -/
theorem crit_of_max {lam cs : ℝ} (hl : 0 ≤ lam) (hcs : 0 < cs) (hmax : ∀ c, fm lam c ≤ fm lam cs) :
    cs * (Cm cs * Real.sinh (cs / 2) * (pm lam cs + lam))
      = 2 * (2 * (Cm cs ^ 2 - 1) * pm lam cs + Cm cs ^ 2 * lam + 2) := by
  have hCd : ∀ c, HasDerivAt Cm (Real.sinh (c / 2) * (1 / 2)) c := fun c => by
    have h : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) c := by simpa using (hasDerivAt_id c).div_const 2
    exact h.cosh
  have hQ : DifferentiableAt ℝ (Qm lam) cs := by
    have : DifferentiableAt ℝ (fun c => Cm c ^ 2 * lam + 2) cs :=
      (((hCd cs).differentiableAt.pow 2).mul_const lam).add_const 2
    exact this
  have hg0 : Qm lam cs ^ 2 + 4 * (Cm cs ^ 2 - 1) ≠ 0 := by
    have := Qm_ge hl cs; have := Cm_ge cs; nlinarith
  have hS : DifferentiableAt ℝ (Sm lam) cs := by
    have : DifferentiableAt ℝ (fun c => Qm lam c ^ 2 + 4 * (Cm c ^ 2 - 1)) cs :=
      (hQ.pow 2).add (((hCd cs).differentiableAt.pow 2).sub_const 1 |>.const_mul 4)
    exact this.sqrt hg0
  have hpd : DifferentiableAt ℝ (pm lam) cs :=
    (differentiableAt_const (2 : ℝ)).div (hQ.add hS) (den_pos hl cs).ne'
  set p' := deriv (pm lam) cs
  have hP : HasDerivAt (pm lam) p' cs := hpd.hasDerivAt
  -- the energy tie, differentiated implicitly
  have hF := ((((hCd cs).pow 2).sub_const 1).mul (hP.pow 2)).add
    ((((hCd cs).pow 2).mul_const lam |>.add_const 2).mul hP) |>.sub_const 1
  have hFz : (fun c => (Cm c ^ 2 - 1) * pm lam c ^ 2 + (Cm c ^ 2 * lam + 2) * pm lam c - 1) = fun _ => 0 := by
    funext c; have := pm_root hl c; unfold Qm at this; linarith
  have hF0 : HasDerivAt (fun c => (Cm c ^ 2 - 1) * pm lam c ^ 2 + (Cm c ^ 2 * lam + 2) * pm lam c - 1) 0 cs := by
    rw [hFz]; exact hasDerivAt_const _ _
  have hexpr := hF.unique hF0
  -- the top is flat
  have hfm : HasDerivAt (fm lam) (2 * cs * pm lam cs + cs ^ 2 * p') cs := by
    have := (hasDerivAt_pow 2 cs).mul hP
    exact this.congr_deriv (by push_cast; ring)
  have hz := (IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall hmax) hfm)
  have hz' : cs * p' + 2 * pm lam cs = 0 := by
    have : cs * (cs * p' + 2 * pm lam cs) = 0 := by linear_combination hz
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact h0
  have hp := pm_pos hl cs
  have key : pm lam cs * (cs * (Cm cs * Real.sinh (cs / 2) * (pm lam cs + lam))
      - 2 * (2 * (Cm cs ^ 2 - 1) * pm lam cs + Cm cs ^ 2 * lam + 2)) = 0 := by
    simp only [Pi.pow_apply] at hexpr
    push_cast at hexpr
    linear_combination cs * hexpr - (2 * (Cm cs ^ 2 - 1) * pm lam cs + Cm cs ^ 2 * lam + 2) * hz'
  rcases mul_eq_zero.mp key with h0 | h0
  · linarith
  · linarith

/-- **End to end: for every algebraic lam >= 0 the Morse break exists, is attained, and is transcendental**
(given Hermite-Lindemann). -/
theorem break_transcendental (HL : Breaks.HermiteLindemann) {lam : ℝ} (hl : 0 ≤ lam)
    (hlam : IsAlgebraic ℚ lam) :
    ∃ cs : ℝ, 0 < cs ∧ IsGreatest {μ : ℝ | ∃ x x' : ℝ → ℝ, Sol lam μ x x'} (fm lam cs) ∧
      Transcendental ℚ (fm lam cs) := by
  obtain ⟨cs, hcs, hg⟩ := break_exists hl
  refine ⟨cs, hcs, hg, ?_⟩
  have hmax : ∀ c, fm lam c ≤ fm lam cs := fun c => hg.2 ⟨_, _, exists_sol hl⟩
  have hcrit0 := crit_of_max hl hcs hmax
  have hroot0 := pm_root hl cs
  unfold Qm at hroot0
  have hCY : Cm cs ^ 2 = Real.sinh (cs / 2) ^ 2 + 1 := by unfold Cm; exact Real.cosh_sq _
  have hs0 : 0 < Real.sinh (cs / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hch : 0 < Cm cs := by linarith [Cm_ge cs]
  refine class_of_crit HL hl hlam hcs hs0 hch (pm_pos hl cs) rfl hCY ?_ ?_ rfl ?_
  · linear_combination hroot0 - (pm lam cs ^ 2 + lam * pm lam cs) * hCY
  · linear_combination hcrit0 + 2 * (2 * pm lam cs + lam) * hCY
  · unfold Cm; exact (Real.cosh_add_sinh _).symm

end MorseOde
