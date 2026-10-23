import Mathlib
import Mistranslation.Breaks

/-! # The break-classification recipe as one theorem (2026-10-23)

Every exponential-clock break closed so far (Bratu, MEMS ladder, predicted family, Pinney - spring, Morse, Kepler)
was classified by the same three moves. This file states them once:

  1. ELIMINATE   if the break mu were algebraic, a knob z would be a root of a NONZERO polynomial whose
                 coefficients are algebraic numbers (shown nonzero by evaluating at one point);
  2. DESCEND     an algebraic knob makes the tie (cosh / sinh of the clock) algebraic, and with it the two
                 coefficients of the critical equation, which is LINEAR in the clock: c1 * T = c0, c1 != 0;
  3. CONTRADICT  then T and e^T are both algebraic, T != 0: Hermite-Lindemann says no.

So a family needs only its own elimination polynomial, its tie and its critical equation. -/

namespace Recipe

open Polynomial

/-- Algebraic over the algebraic numbers inside ℝ means algebraic over ℚ. -/
theorem alg_of_root {z : ℝ} {P : (algebraicClosure ℚ ℝ)[X]} (hP : P ≠ 0) (hz : aeval z P = 0) :
    IsAlgebraic ℚ z :=
  (show IsAlgebraic (algebraicClosure ℚ ℝ) z from ⟨P, hP, hz⟩).restrictScalars (R := ℚ)

/-- An algebraic real seen as an element of the algebraic numbers inside ℝ. -/
def toK {x : ℝ} (hx : IsAlgebraic ℚ x) : algebraicClosure ℚ ℝ := ⟨x, mem_algebraicClosure_iff.2 hx⟩

@[simp] lemma algebraMap_toK {x : ℝ} (hx : IsAlgebraic ℚ x) : algebraMap _ ℝ (toK hx) = x := rfl

/-- **The recipe.** -/
theorem transcendental_of_recipe (HL : Breaks.HermiteLindemann) {μ z T c1 c0 : ℝ}
    (hT : T ≠ 0) (hlin : c1 * T = c0) (hc1 : c1 ≠ 0)
    (elim : IsAlgebraic ℚ μ → ∃ P : (algebraicClosure ℚ ℝ)[X], P ≠ 0 ∧ aeval z P = 0)
    (descend : IsAlgebraic ℚ z → IsAlgebraic ℚ c1 ∧ IsAlgebraic ℚ c0 ∧ IsAlgebraic ℚ (Real.exp T)) :
    Transcendental ℚ μ := by
  intro hμ
  obtain ⟨P, hP, hz⟩ := elim hμ
  obtain ⟨h1, h0, he⟩ := descend (alg_of_root hP hz)
  have hTeq : T = c0 * c1⁻¹ := by rw [← hlin]; field_simp
  exact HL T (by rw [hTeq]; exact h0.mul h1.inv) hT he


/-- **The recipe, with the break itself available to the descent** (for families where the push enters the tie,
like P_3 where q = mu/kap sits inside the polynomial and the cosh/sinh of the clock). -/
theorem transcendental_of_recipe' (HL : Breaks.HermiteLindemann) {μ z T c1 c0 : ℝ}
    (hT : T ≠ 0) (hlin : c1 * T = c0) (hc1 : c1 ≠ 0)
    (elim : IsAlgebraic ℚ μ → ∃ P : (algebraicClosure ℚ ℝ)[X], P ≠ 0 ∧ aeval z P = 0)
    (descend : IsAlgebraic ℚ μ → IsAlgebraic ℚ z →
      IsAlgebraic ℚ c1 ∧ IsAlgebraic ℚ c0 ∧ IsAlgebraic ℚ (Real.exp T)) :
    Transcendental ℚ μ := by
  intro hμ
  obtain ⟨P, hP, hz⟩ := elim hμ
  obtain ⟨h1, h0, he⟩ := descend hμ (alg_of_root hP hz)
  have hTeq : T = c0 * c1⁻¹ := by rw [← hlin]; field_simp
  exact HL T (by rw [hTeq]; exact h0.mul h1.inv) hT he

end Recipe
