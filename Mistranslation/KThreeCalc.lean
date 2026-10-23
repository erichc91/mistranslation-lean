import Mathlib
import Mistranslation.KThreeClass
import Mistranslation.KeplerClass

/-! # K_3 bridge: the calculus step and the end-to-end class theorem for the push curve (2026-10-23)

The K_3 push curve in Kepler's variables (B = Bm, D = Dm, clock T = Tm = arcosh C, C = (1-B)/D):
  I3(m) = int_0^T (B + D cosh)^3 = (B^3 + 3/2 B D^2) T + sinh T (3 B^2 D + 3/2 B D^2 C + 2/3 D^3 + D^3 C^2/3),
  f3(m) = 12 I3^2 m^2 / (1 + 2 lam m).
(The closed form of the integral and f3 = the K_3 break curve are checked in SQL: `v4/sql/bridge_K3_closed.sql`
against independent quadrature, `v4/sql/bridge_Kq.sql`.) Here: at an interior top of f3 the critical equation of
`KThreeClass` holds, so the top value is transcendental for every algebraic lam > 0, given Hermite-Lindemann. -/

namespace KThree

open KeplerOde

noncomputable def I3 (lam m : ℝ) : ℝ :=
  (Bm lam m ^ 3 + 3 / 2 * Bm lam m * Dm lam m ^ 2) * Tm lam m
  + Real.sinh (Tm lam m) * (3 * Bm lam m ^ 2 * Dm lam m + 3 / 2 * Bm lam m * Dm lam m ^ 2 * Cy lam m
    + 2 / 3 * Dm lam m ^ 3 + Dm lam m ^ 3 * Cy lam m ^ 2 / 3)

noncomputable def f3 (lam m : ℝ) : ℝ := 12 * I3 lam m ^ 2 * m ^ 2 / (1 + 2 * lam * m)

/-- `SP12` with the tie term written as m^2 a^2 s^2 instead of S2n. -/
noncomputable def SP12S (l m s : ℝ) : ℝ := 6 * m ^ 4 * ct2 l m * Cn l m * WK l m * aK l m
  + 2 * EK l m * Cn l m * g6 l m * WK l m + 2 * aK l m * (m ^ 2 * aK l m ^ 2 * s ^ 2) * (gd6 l m + aK l m * g6 l m)

lemma I3_pos {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) (hm1 : m < 1) : 0 < I3 lam m := by
  have hy := Cy_gt hl hm hm1
  have hB := Bm_nonneg hl hm
  have hD := Dm_pos hl hm
  have hT : 0 < Tm lam m := Real.arcosh_pos hy
  have hS : 0 < Real.sinh (Tm lam m) := Real.sinh_pos_iff.mpr hT
  have hC : 0 < Cy lam m := by linarith
  unfold I3; positivity

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- **The calculus step.** -/
theorem crit_of_max {lam ms : ℝ} (hl : 0 ≤ lam) (hm0 : 0 < ms) (hm1 : ms < 1)
    (hmax : ∀ m ∈ Set.Ioo (0 : ℝ) 1, f3 lam m ≤ f3 lam ms) :
    6 * ms ^ 5 * aK lam ms ^ 3 * Sy lam ms * P12 lam ms * Tm lam ms + SP12S lam ms (Sy lam ms) = 0 := by
  have hw : 0 < 1 + 2 * lam * ms := by positivity
  have ha : 0 < 1 + lam * ms := by positivity
  have hD := Dm_pos hl hm0
  have hy1 := Cy_gt hl hm0 hm1
  have hIpos := I3_pos hl hm0 hm1
  have dW : HasDerivAt (fun x => 1 + 2 * lam * x) (2 * lam) ms := by
    simpa using ((hasDerivAt_id' ms).const_mul (2 * lam)).const_add 1
  have dB := ((hasDerivAt_pow 2 ms).const_mul lam).div dW hw.ne'
  have dD := ((hasDerivAt_id' ms).mul (((hasDerivAt_id' ms).const_mul lam).const_add 1)).div dW hw.ne'
  have dY := (dB.const_sub 1).div dD hD.ne'
  have dT := (Real.hasDerivAt_arcosh (show _ ∈ Set.Ioi (1 : ℝ) from hy1)).comp ms dY
  have dI := (((dB.pow 3).add ((dB.const_mul (3 / 2)).mul (dD.pow 2))).mul dT).add
    (dT.sinh.mul (((((dB.pow 2).const_mul 3).mul dD).add ((((dB.const_mul (3 / 2)).mul (dD.pow 2)).mul dY))).add
      (((dD.pow 3).const_mul (2 / 3)).add (((dD.pow 3).mul (dY.pow 2)).div_const 3))))
  have hI : HasDerivAt (I3 lam) _ ms := dI.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
    simp only [I3, Cy, Tm, Bm, Dm, Function.comp, Pi.div_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply]; ring)
  have dF := (((hI.pow 2).const_mul 12).mul (hasDerivAt_pow 2 ms)).div dW hw.ne'
  have hfk : HasDerivAt (f3 lam) _ ms := dF.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
    simp only [f3, Pi.div_apply, Pi.mul_apply, Pi.pow_apply])
  have hloc : IsLocalMax (f3 lam) ms :=
    Filter.mem_of_superset (Ioo_mem_nhds hm0 hm1) (fun m hm => hmax m hm)
  have hz := hloc.hasDerivAt_eq_zero hfk
  have hS : 0 < Sy lam ms := Real.sqrt_pos.mpr (by nlinarith)
  have hT : 0 < Tm lam ms := Real.arcosh_pos hy1
  have hcosh : Real.cosh (Real.arcosh (Cy lam ms)) = Cy lam ms := Real.cosh_arcosh hy1.le
  have hsinh : Real.sinh (Real.arcosh (Cy lam ms)) = Real.sqrt (Cy lam ms ^ 2 - 1) := Real.sinh_arcosh hy1.le
  simp only [Function.comp, Nat.cast_ofNat, Pi.div_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply,
    Nat.reduceSub, pow_one, I3, Tm] at hz hIpos
  rw [show (1 - Bm lam ms) / Dm lam ms = Cy lam ms from rfl] at hz hIpos
  rw [hcosh, hsinh] at hz
  rw [hsinh] at hIpos
  rw [show Tm lam ms = Real.arcosh (Cy lam ms) from rfl, show Sy lam ms = Real.sqrt (Cy lam ms ^ 2 - 1) from rfl]
  rw [show Tm lam ms = Real.arcosh (Cy lam ms) from rfl] at hT
  rw [show Sy lam ms = Real.sqrt (Cy lam ms ^ 2 - 1) from rfl] at hS
  generalize Real.arcosh (Cy lam ms) = T at hz hT hIpos ⊢
  generalize Real.sqrt (Cy lam ms ^ 2 - 1) = S at hz hS hIpos ⊢
  unfold Cy Bm Dm at hz hIpos
  have hm0' := hm0.ne'
  have hw' := hw.ne'
  have ha' := ha.ne'
  have hS' := hS.ne'
  have hDn : ms * (1 + lam * ms) ≠ 0 := by positivity
  have hDq : ms * (1 + lam * ms) / (1 + 2 * lam * ms) ≠ 0 := by positivity
  have hCx : 1 < ((1 - (lam * ms ^ 2 / (1 + 2 * lam * ms))) / (ms * (1 + lam * ms) / (1 + 2 * lam * ms))) := by unfold Cy Bm Dm at hy1; exact hy1
  have hBx : 0 ≤ (lam * ms ^ 2 / (1 + 2 * lam * ms)) := by positivity
  have hDx : 0 < (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) := by positivity
  have hIE : 0 < (((lam * ms ^ 2 / (1 + 2 * lam * ms)) ^ 3 + 3 / 2 * (lam * ms ^ 2 / (1 + 2 * lam * ms)) * (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) ^ 2) * T + S * (3 * (lam * ms ^ 2 / (1 + 2 * lam * ms)) ^ 2 * (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) + 3 / 2 * (lam * ms ^ 2 / (1 + 2 * lam * ms)) * (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) ^ 2 * ((1 - (lam * ms ^ 2 / (1 + 2 * lam * ms))) / (ms * (1 + lam * ms) / (1 + 2 * lam * ms))) + 2 / 3 * (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) ^ 3 + (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) ^ 3 * ((1 - (lam * ms ^ 2 / (1 + 2 * lam * ms))) / (ms * (1 + lam * ms) / (1 + 2 * lam * ms))) ^ 2 / 3)) := by
    have : 0 < ((1 - (lam * ms ^ 2 / (1 + 2 * lam * ms))) / (ms * (1 + lam * ms) / (1 + 2 * lam * ms))) := by linarith
    positivity
  have key : (6 * ms ^ 5 * aK lam ms ^ 3 * S * P12 lam ms * T + SP12S lam ms S) * (2 * (((lam * ms ^ 2 / (1 + 2 * lam * ms)) ^ 3 + 3 / 2 * (lam * ms ^ 2 / (1 + 2 * lam * ms)) * (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) ^ 2) * T + S * (3 * (lam * ms ^ 2 / (1 + 2 * lam * ms)) ^ 2 * (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) + 3 / 2 * (lam * ms ^ 2 / (1 + 2 * lam * ms)) * (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) ^ 2 * ((1 - (lam * ms ^ 2 / (1 + 2 * lam * ms))) / (ms * (1 + lam * ms) / (1 + 2 * lam * ms))) + 2 / 3 * (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) ^ 3 + (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) ^ 3 * ((1 - (lam * ms ^ 2 / (1 + 2 * lam * ms))) / (ms * (1 + lam * ms) / (1 + 2 * lam * ms))) ^ 2 / 3))) = 0 := by
    simp only [SP12S, P12, gd6, g6d, g6, ct2d, ct2, Cn, WK, aK, EK]
    linear_combination (norm := skip) (S * (1 + 2 * lam * ms) ^ 5 * (1 + lam * ms) ^ 3) * hz
    field_simp
    ring
  rcases mul_eq_zero.mp key with h0 | h0
  · exact h0
  · linarith


/-- **K_3, end to end on the push curve: for every algebraic lam > 0, the top of f3 on (0, 1) is
transcendental** (given Hermite-Lindemann). The top exists numerically for every lam tested
(`v4/sql/bridge_K3_closed.sql`); existence by compactness is not formalised here. -/
theorem top_transcendental (HL : Breaks.HermiteLindemann) {lam ms : ℝ} (hl : 0 < lam)
    (hlam : IsAlgebraic ℚ lam) (hm0 : 0 < ms) (hm1 : ms < 1)
    (hmax : ∀ m ∈ Set.Ioo (0 : ℝ) 1, f3 lam m ≤ f3 lam ms) :
    Transcendental ℚ (f3 lam ms) := by
  have hcrit' := crit_of_max hl.le hm0 hm1 hmax
  have hy1 := Cy_gt hl.le hm0 hm1
  have hw : 0 < 1 + 2 * lam * ms := by positivity
  have ha : 0 < 1 + lam * ms := by positivity
  have hS : 0 < Sy lam ms := Real.sqrt_pos.mpr (by nlinarith)
  have hSsq : Sy lam ms ^ 2 = Cy lam ms ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hC : ms * aK lam ms * Cy lam ms = EK lam ms := by unfold Cy Bm Dm aK EK; field_simp
  have hS2 : ms ^ 2 * aK lam ms ^ 2 * Sy lam ms ^ 2 = S2n lam ms := by
    unfold S2n; rw [hSsq]; linear_combination (ms * aK lam ms * Cy lam ms + EK lam ms) * hC
  have hsinh : Real.sinh (Tm lam ms) = Sy lam ms := Real.sinh_arcosh hy1.le
  have hf3pos : 0 < f3 lam ms := by unfold f3; have := I3_pos hl.le hm0 hm1; positivity
  refine class_of_crit HL hl hlam hm0 (Real.arcosh_pos hy1) hS hf3pos hC hS2 ?_ ?_ (Real.exp_arcosh hy1.le)
  · unfold SP12S at hcrit'; unfold SP12
    rw [show Tm lam ms = Real.arcosh (Cy lam ms) from rfl] at hcrit'
    linear_combination hcrit' - 2 * aK lam ms * (gd6 lam ms + aK lam ms * g6 lam ms) * hS2
  · have hm' := hm0.ne'
    have hD := Dm_pos hl.le hm0
    unfold f3 I3
    rw [hsinh]
    rw [show Tm lam ms = Real.arcosh (Cy lam ms) from rfl, show Sy lam ms = Real.sqrt (Cy lam ms ^ 2 - 1) from rfl]
    generalize Real.arcosh (Cy lam ms) = T
    generalize Real.sqrt (Cy lam ms ^ 2 - 1) = S
    unfold Cy Bm Dm
    simp only [ct2, g6, WK, aK, EK]
    have ha' := ha.ne'
    have hw' := hw.ne'
    field_simp
    ring

end KThree
