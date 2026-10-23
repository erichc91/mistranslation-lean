import Mathlib
import Mistranslation.KeplerOde
import Mistranslation.Breaks
import Mistranslation.Recipe

/-! # The Kepler break is transcendental for every algebraic lam > 0 (2026-10-23)

Given Hermite-Lindemann (explicit hypothesis). No genericity assumption. (lam = 0 is the algebraic case: break = 1.)
Notation at the top m: w = 1 + 2 lam m, a = 1 + lam m, E = w - lam m^2, C = cosh T = E/(m a), S = sinh T.
1. Calculus (`crit_of_max`): the top is flat; with the arcosh clock this is the critical equation
     3 lam m^2 a^2 T S + m a (2 + 4 lam m + 3 lam^2 m^2) S^2 = w (2 lam m a (1 - C) + C w^2),
   LINEAR in T with coefficient 3 lam m^2 a^2 S, nonzero exactly when lam > 0.
2. Elimination (`class_of_crit`): the break mu is tied to m alone by
     PI(m) = 9 a^4 w mu (E^2 - (m a)^2) - 4 m^2 (E^2 + E w^2 + (m a)^2 (2 lam - 1) - 2 lam m a E)^2 = 0,
   and PI(0) = 9 mu != 0. So algebraic mu -> m -> C, S -> T (critical equation) -> e^T = C + S algebraic, T != 0:
   contradiction with Hermite-Lindemann. -/

namespace KeplerOde

open Polynomial in
/-- **The class step**, pure algebra. -/
theorem class_of_crit (HL : Breaks.HermiteLindemann) {lam m T S C μ : ℝ}
    (hl : 0 < lam) (hlam : IsAlgebraic ℚ lam) (hm : 0 < m) (hT : 0 < T) (hS : 0 < S) (hμ0 : 0 < μ)
    (hC : m * (1 + lam * m) * C = 1 + 2 * lam * m - lam * m ^ 2) (hSC : S ^ 2 = C ^ 2 - 1)
    (hcrit : 3 * lam * m ^ 2 * (1 + lam * m) ^ 2 * T * S
      + m * (1 + lam * m) * (2 + 4 * lam * m + 3 * lam ^ 2 * m ^ 2) * S ^ 2
      - (1 + 2 * lam * m) * (2 * lam * m * (1 + lam * m) * (1 - C) + C * (1 + 2 * lam * m) ^ 2) = 0)
    (hμ : μ * (1 + 2 * lam * m) ^ 3 = 4 * m ^ 2 * (lam * m ^ 2 * T + m * (1 + lam * m) * S) ^ 2)
    (hexp : Real.exp T = C + S) :
    Transcendental ℚ μ := by
  have hw : 0 < 1 + 2 * lam * m := by positivity
  have ha : 0 < 1 + lam * m := by positivity
  set w := 1 + 2 * lam * m with hwdef
  set a := 1 + lam * m with hadef
  set E := w - lam * m ^ 2 with hEdef
  set L := lam * m ^ 2 * T + m * a * S with hLdef
  set N := m * a * S ^ 2 + C * w ^ 2 + 2 * lam * m * a * (1 - C) with hNdef
  have hC' : m * a * C = E := by rw [hEdef, hwdef]; linear_combination hC
  have hL : 3 * a ^ 2 * S * L = w * N := by
    rw [hLdef, hNdef, hwdef, hadef]; linear_combination hcrit
  have h3w : w ^ 2 * (9 * a ^ 4 * S ^ 2 * μ * w - 4 * m ^ 2 * N ^ 2) = 0 := by
    linear_combination (9 * a ^ 4 * S ^ 2) * hμ + (4 * m ^ 2 * (3 * a ^ 2 * S * L + w * N)) * hL
  have h3 : 9 * a ^ 4 * S ^ 2 * μ * w = 4 * m ^ 2 * N ^ 2 := by
    rcases mul_eq_zero.mp h3w with h0 | h0
    · nlinarith
    · linarith
  have h1 : S ^ 2 * (m * a) ^ 2 = E ^ 2 - (m * a) ^ 2 := by
    linear_combination (m * a) ^ 2 * hSC + (m * a * C + E) * hC'
  have h2 : m * a * N = E ^ 2 + E * w ^ 2 + (m * a) ^ 2 * (2 * lam - 1) - 2 * lam * m * a * E := by
    rw [hNdef]; linear_combination h1 + (w ^ 2 - 2 * lam * m * a) * hC'
  have hPI : 9 * a ^ 4 * w * μ * (E ^ 2 - (m * a) ^ 2)
      - 4 * m ^ 2 * (E ^ 2 + E * w ^ 2 + (m * a) ^ 2 * (2 * lam - 1) - 2 * lam * m * a * E) ^ 2 = 0 := by
    linear_combination (-(9 * a ^ 4 * w * μ)) * h1 + (m * a) ^ 2 * h3
      + (4 * m ^ 2 * (m * a * N + (E ^ 2 + E * w ^ 2 + (m * a) ^ 2 * (2 * lam - 1) - 2 * lam * m * a * E))) * h2
  clear_value L N
  have h2a : IsAlgebraic ℚ (2 : ℝ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (2 : ℚ)
  have h3a : IsAlgebraic ℚ (3 : ℝ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (3 : ℚ)
  have h4a : IsAlgebraic ℚ (4 : ℝ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (4 : ℚ)
  have h1a : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_one
  refine Recipe.transcendental_of_recipe HL (z := m) (T := T) (c1 := 3 * lam * m ^ 2 * a ^ 2 * S)
    (c0 := w * (2 * lam * m * a * (1 - C) + C * w ^ 2) - m * a * (2 + 4 * lam * m + 3 * lam ^ 2 * m ^ 2) * S ^ 2)
    hT.ne' (by linear_combination hcrit) (by positivity) (fun hμa => ?_) (fun hmQ => ?_)
  · -- ELIMINATE: m is a root of PI, and PI(0) = 9 mu
    let mK := Recipe.toK hμa
    let lK := Recipe.toK hlam
    let EX : (algebraicClosure ℚ ℝ)[X] := 1 + 2 * Polynomial.C lK * X - Polynomial.C lK * X ^ 2
    let P : (algebraicClosure ℚ ℝ)[X] := 9 * Polynomial.C mK * (1 + Polynomial.C lK * X) ^ 4
        * (1 + 2 * Polynomial.C lK * X) * (EX ^ 2 - (X * (1 + Polynomial.C lK * X)) ^ 2)
      - 4 * X ^ 2 * (EX ^ 2 + EX * (1 + 2 * Polynomial.C lK * X) ^ 2
        + (X * (1 + Polynomial.C lK * X)) ^ 2 * (2 * Polynomial.C lK - 1)
        - 2 * Polynomial.C lK * (X * (1 + Polynomial.C lK * X)) * EX) ^ 2
    have hev : ∀ x : ℝ, aeval x P = 9 * μ * (1 + lam * x) ^ 4 * (1 + 2 * lam * x)
        * ((1 + 2 * lam * x - lam * x ^ 2) ^ 2 - (x * (1 + lam * x)) ^ 2)
        - 4 * x ^ 2 * ((1 + 2 * lam * x - lam * x ^ 2) ^ 2 + (1 + 2 * lam * x - lam * x ^ 2) * (1 + 2 * lam * x) ^ 2
          + (x * (1 + lam * x)) ^ 2 * (2 * lam - 1)
          - 2 * lam * (x * (1 + lam * x)) * (1 + 2 * lam * x - lam * x ^ 2)) ^ 2 := by
      intro x
      simp only [P, EX, map_sub, map_mul, map_pow, map_add, map_one, map_ofNat, aeval_C, aeval_X]
      rfl
    refine ⟨P, fun h0 => ?_, by rw [hev]; linear_combination hPI⟩
    have h1 := hev 0
    rw [h0, map_zero] at h1
    norm_num at h1
    linarith
  · -- DESCEND: m -> C, S -> the critical coefficients and e^T = C + S
    have haa : IsAlgebraic ℚ a := by rw [hadef]; exact h1a.add (hlam.mul hmQ)
    have hwa : IsAlgebraic ℚ w := by rw [hwdef]; exact h1a.add ((h2a.mul hlam).mul hmQ)
    have hEa : IsAlgebraic ℚ E := by rw [hEdef]; exact hwa.sub (hlam.mul (hmQ.pow 2))
    have hCeq : C = E * (m * a)⁻¹ := by
      have : m * a ≠ 0 := by positivity
      field_simp; linear_combination hC'
    have hCa : IsAlgebraic ℚ C := by rw [hCeq]; exact hEa.mul (hmQ.mul haa).inv
    have hS2 : IsAlgebraic ℚ (S ^ 2) := by rw [hSC]; exact (hCa.pow 2).sub h1a
    have hSa : IsAlgebraic ℚ S := IsAlgebraic.of_pow (by norm_num) hS2
    have hn1 : IsAlgebraic ℚ (2 * lam * m * a * (1 - C) + C * w ^ 2) :=
      ((((h2a.mul hlam).mul hmQ).mul haa).mul (h1a.sub hCa)).add (hCa.mul (hwa.pow 2))
    have hn2 : IsAlgebraic ℚ (2 + 4 * lam * m + 3 * lam ^ 2 * m ^ 2) :=
      (h2a.add ((h4a.mul hlam).mul hmQ)).add ((h3a.mul (hlam.pow 2)).mul (hmQ.pow 2))
    exact ⟨(((h3a.mul hlam).mul (hmQ.pow 2)).mul (haa.pow 2)).mul hSa,
      (hwa.mul hn1).sub (((hmQ.mul haa).mul hn2).mul (hSa.pow 2)), by rw [hexp]; exact hCa.add hSa⟩


noncomputable def Cy (lam m : ℝ) : ℝ := (1 - Bm lam m) / Dm lam m
noncomputable def Sy (lam m : ℝ) : ℝ := Real.sqrt (Cy lam m ^ 2 - 1)

lemma Cy_gt {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) (hm1 : m < 1) : 1 < Cy lam m := by
  unfold Cy; rw [lt_div_iff₀ (Dm_pos hl hm)]; have := BD_sum hl hm; linarith

/-- **The calculus step**: at a top of fk inside (0, 1) the critical equation holds. -/
theorem crit_of_max {lam ms : ℝ} (hl : 0 ≤ lam) (hm0 : 0 < ms) (hm1 : ms < 1)
    (hmax : ∀ m ∈ Set.Ioo (0 : ℝ) 1, fk lam m ≤ fk lam ms) :
    3 * lam * ms ^ 2 * (1 + lam * ms) ^ 2 * Tm lam ms * Sy lam ms
      + ms * (1 + lam * ms) * (2 + 4 * lam * ms + 3 * lam ^ 2 * ms ^ 2) * Sy lam ms ^ 2
      - (1 + 2 * lam * ms) * (2 * lam * ms * (1 + lam * ms) * (1 - Cy lam ms)
        + Cy lam ms * (1 + 2 * lam * ms) ^ 2) = 0 := by
  have hw : 0 < 1 + 2 * lam * ms := by positivity
  have ha : 0 < 1 + lam * ms := by positivity
  have hD := Dm_pos hl hm0
  have hy1 := Cy_gt hl hm0 hm1
  have dW : HasDerivAt (fun x => 1 + 2 * lam * x) (2 * lam) ms := by
    simpa using ((hasDerivAt_id' ms).const_mul (2 * lam)).const_add 1
  have dB := ((hasDerivAt_pow 2 ms).const_mul lam).div dW hw.ne'
  have dD := ((hasDerivAt_id' ms).mul (((hasDerivAt_id' ms).const_mul lam).const_add 1)).div dW hw.ne'
  have dY := (dB.const_sub 1).div dD hD.ne'
  have dT := (Real.hasDerivAt_arcosh (show _ ∈ Set.Ioi (1 : ℝ) from hy1)).comp ms dY
  have dK := (dB.mul dT).add (dD.mul dT.sinh)
  have dF := (((dK.const_mul 2).pow 2).mul (hasDerivAt_pow 2 ms)).div dW hw.ne'
  have hfk : HasDerivAt (fk lam) _ ms := dF
  have hloc : IsLocalMax (fk lam) ms :=
    Filter.mem_of_superset (Ioo_mem_nhds hm0 hm1) (fun m hm => hmax m hm)
  have hz := hloc.hasDerivAt_eq_zero hfk
  have hS : 0 < Sy lam ms := Real.sqrt_pos.mpr (by nlinarith)
  have hT : 0 < Tm lam ms := Real.arcosh_pos hy1
  have hcosh : Real.cosh (Tm lam ms) = Cy lam ms := Real.cosh_arcosh hy1.le
  have hsinh : Real.sinh (Tm lam ms) = Sy lam ms := Real.sinh_arcosh hy1.le
  have hCdef : Cy lam ms = (1 - lam * ms ^ 2 / (1 + 2 * lam * ms)) / (ms * (1 + lam * ms) / (1 + 2 * lam * ms)) := rfl
  simp only [Function.comp, Nat.cast_ofNat, Pi.div_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply,
    Nat.reduceSub, pow_one] at hz
  have hcosh' : Real.cosh (Real.arcosh (Cy lam ms)) = Cy lam ms := hcosh
  have hsinh' : Real.sinh (Real.arcosh (Cy lam ms)) = Real.sqrt (Cy lam ms ^ 2 - 1) := hsinh
  rw [hcosh', hsinh'] at hz
  rw [show Tm lam ms = Real.arcosh (Cy lam ms) from rfl, show Sy lam ms = Real.sqrt (Cy lam ms ^ 2 - 1) from rfl]
  rw [show Tm lam ms = Real.arcosh (Cy lam ms) from rfl] at hT
  rw [show Sy lam ms = Real.sqrt (Cy lam ms ^ 2 - 1) from rfl] at hS
  generalize Real.arcosh (Cy lam ms) = T at hz hT ⊢
  generalize Real.sqrt (Cy lam ms ^ 2 - 1) = S at hz hS ⊢
  unfold Cy Bm Dm at hz ⊢
  have hm0' := hm0.ne'
  have hw' := hw.ne'
  have ha' := ha.ne'
  have hS' := hS.ne'
  have hL : 0 < lam * ms ^ 2 * T + ms * (1 + lam * ms) * S := by positivity
  have hL' := hL.ne'
  linear_combination (norm := skip) (S * (1 + 2 * lam * ms) ^ 4 * (1 + lam * ms)
    / (8 * ms * (lam * ms ^ 2 * T + ms * (1 + lam * ms) * S))) * hz
  field_simp
  ring

/-- **End to end: for every algebraic lam > 0 the Kepler break exists, is attained in (0, 1), and is
transcendental** (given Hermite-Lindemann). -/
theorem break_transcendental (HL : Breaks.HermiteLindemann) {lam : ℝ} (hl : 0 < lam)
    (hlam : IsAlgebraic ℚ lam) :
    ∃ ms : ℝ, 0 < ms ∧ ms < 1 ∧ IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol lam μ v v'} (fk lam ms) ∧
      Transcendental ℚ (fk lam ms) := by
  obtain ⟨ms, h0, h1, hg⟩ := break_exists hl.le
  refine ⟨ms, h0, h1, hg, ?_⟩
  have hmax : ∀ m ∈ Set.Ioo (0 : ℝ) 1, fk lam m ≤ fk lam ms :=
    fun m hm => hg.2 ⟨_, _, exists_sol hl.le hm.1 hm.2⟩
  have hcrit := crit_of_max hl.le h0 h1 hmax
  have hy1 := Cy_gt hl.le h0 h1
  have hw : 0 < 1 + 2 * lam * ms := by positivity
  have hD := Dm_pos hl.le h0
  refine class_of_crit HL hl hlam h0 (Real.arcosh_pos hy1) (Real.sqrt_pos.mpr (by nlinarith))
    (fk_pos hl.le h0 h1) ?_ (Real.sq_sqrt (by nlinarith)) hcrit ?_ (Real.exp_arcosh hy1.le)
  · unfold Cy Bm Dm; field_simp
  · have hsinh : Real.sinh (Tm lam ms) = Sy lam ms := Real.sinh_arcosh hy1.le
    simp only [show Real.arcosh (Cy lam ms) = Tm lam ms from rfl, show √(Cy lam ms ^ 2 - 1) = Sy lam ms from rfl]
    unfold fk Km; rw [hsinh]; unfold Bm Dm; field_simp; ring

end KeplerOde
