import Mathlib

/-! # The pair-law and the trio-law as UNCONDITIONAL reductions (2026-10-23, rewritten in Classified Table phase C3)

Rank-1 breaks are decided outright (Hermite-Lindemann, proved in `LindemannBridge.lean`). A rank-2 break carries two
clocks L1, L2. If the break were algebraic, the time condition and the top condition form a LINEAR system for the clocks
whose coefficients, and the clocks' exponentials, are algebraic over Q(z) for the one unknown turning point z. Solving
it shows: an algebraic break forces L1, L2, e^L1, e^L2 ALL algebraic over Q(z). That is what is proved here, with no
hypothesis.

What would decide the class (NOT assumed, recorded as an open fact of the data): whether two Q-independent clocks can
live, with their exponentials, over a field of transcendence degree 1. Schanuel's conjecture (open since the 1960s)
says no; nothing here uses it. Same shape for three clocks over Q(z, L3). -/

namespace PairLaw

open IntermediateField

/-- The pair fact an algebraic break would force: both clocks and both exponentials algebraic over Q(z). -/
def PairAlg (z L1 L2 : ℝ) : Prop :=
  IsAlgebraic ℚ⟮z⟯ L1 ∧ IsAlgebraic ℚ⟮z⟯ L2 ∧ IsAlgebraic ℚ⟮z⟯ (Real.exp L1) ∧ IsAlgebraic ℚ⟮z⟯ (Real.exp L2)

/-- The trio fact: three clocks and their exponentials algebraic over Q(z, w). -/
def TrioAlg (z w L1 L2 L3 : ℝ) : Prop :=
  IsAlgebraic ℚ⟮z, w⟯ L1 ∧ IsAlgebraic ℚ⟮z, w⟯ L2 ∧ IsAlgebraic ℚ⟮z, w⟯ L3 ∧
    IsAlgebraic ℚ⟮z, w⟯ (Real.exp L1) ∧ IsAlgebraic ℚ⟮z, w⟯ (Real.exp L2) ∧ IsAlgebraic ℚ⟮z, w⟯ (Real.exp L3)

lemma alg_up {z x : ℝ} (hx : IsAlgebraic ℚ x) : IsAlgebraic ℚ⟮z⟯ x := hx.extendScalars (algebraMap ℚ ℚ⟮z⟯).injective

/-- **The pair reduction (unconditional).** If the break is algebraic, both clocks and their exponentials are algebraic
over Q(z). -/
theorem pair_reduction {μ z L1 L2 a1 a2 b1 b2 c d : ℝ}
    (h1 : a1 * L1 + a2 * L2 = c) (h2 : b1 * L1 + b2 * L2 = d) (hdet : a1 * b2 - a2 * b1 ≠ 0)
    (ha1 : IsAlgebraic ℚ⟮z⟯ a1) (ha2 : IsAlgebraic ℚ⟮z⟯ a2) (hb1 : IsAlgebraic ℚ⟮z⟯ b1)
    (hb2 : IsAlgebraic ℚ⟮z⟯ b2) (hd : IsAlgebraic ℚ⟮z⟯ d) (hc : IsAlgebraic ℚ μ → IsAlgebraic ℚ⟮z⟯ c)
    (he1 : IsAlgebraic ℚ⟮z⟯ (Real.exp L1)) (he2 : IsAlgebraic ℚ⟮z⟯ (Real.exp L2)) :
    IsAlgebraic ℚ μ → PairAlg z L1 L2 := by
  intro hμ
  have hcA := hc hμ
  have hL1 : L1 = (c * b2 - a2 * d) * (a1 * b2 - a2 * b1)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hdet]; linear_combination b2 * h1 - a2 * h2
  have hL2 : L2 = (a1 * d - c * b1) * (a1 * b2 - a2 * b1)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hdet]; linear_combination a1 * h2 - b1 * h1
  have hdetA : IsAlgebraic ℚ⟮z⟯ (a1 * b2 - a2 * b1) := (ha1.mul hb2).sub (ha2.mul hb1)
  refine ⟨?_, ?_, he1, he2⟩
  · rw [hL1]; exact ((hcA.mul hb2).sub (ha2.mul hd)).mul hdetA.inv
  · rw [hL2]; exact ((ha1.mul hd).sub (hcA.mul hb1)).mul hdetA.inv

/-- **The trio reduction (unconditional).** Two equations (time, top) in three clocks: with L3 left free, an algebraic
break forces all three clocks and exponentials algebraic over Q(z, L3). -/
theorem trio_reduction {μ z L1 L2 L3 a1 a2 a3 b1 b2 b3 c d : ℝ}
    (h1 : a1 * L1 + a2 * L2 + a3 * L3 = c) (h2 : b1 * L1 + b2 * L2 + b3 * L3 = d) (hdet : a1 * b2 - a2 * b1 ≠ 0)
    (ha1 : IsAlgebraic ℚ⟮z, L3⟯ a1) (ha2 : IsAlgebraic ℚ⟮z, L3⟯ a2) (ha3 : IsAlgebraic ℚ⟮z, L3⟯ a3)
    (hb1 : IsAlgebraic ℚ⟮z, L3⟯ b1) (hb2 : IsAlgebraic ℚ⟮z, L3⟯ b2) (hb3 : IsAlgebraic ℚ⟮z, L3⟯ b3)
    (hd : IsAlgebraic ℚ⟮z, L3⟯ d) (hc : IsAlgebraic ℚ μ → IsAlgebraic ℚ⟮z, L3⟯ c)
    (he1 : IsAlgebraic ℚ⟮z, L3⟯ (Real.exp L1)) (he2 : IsAlgebraic ℚ⟮z, L3⟯ (Real.exp L2))
    (he3 : IsAlgebraic ℚ⟮z, L3⟯ (Real.exp L3)) :
    IsAlgebraic ℚ μ → TrioAlg z L3 L1 L2 L3 := by
  intro hμ
  have hcA := hc hμ
  have hL3 : IsAlgebraic ℚ⟮z, L3⟯ L3 :=
    isAlgebraic_algebraMap (R := ℚ⟮z, L3⟯) (A := ℝ) (⟨L3, subset_adjoin ℚ _ (by simp)⟩ : ℚ⟮z, L3⟯)
  have hL1 : L1 = ((c - a3 * L3) * b2 - a2 * (d - b3 * L3)) * (a1 * b2 - a2 * b1)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hdet]; linear_combination b2 * h1 - a2 * h2
  have hL2 : L2 = (a1 * (d - b3 * L3) - (c - a3 * L3) * b1) * (a1 * b2 - a2 * b1)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hdet]; linear_combination a1 * h2 - b1 * h1
  have hdetA : IsAlgebraic ℚ⟮z, L3⟯ (a1 * b2 - a2 * b1) := (ha1.mul hb2).sub (ha2.mul hb1)
  have hr1 : IsAlgebraic ℚ⟮z, L3⟯ (c - a3 * L3) := hcA.sub (ha3.mul hL3)
  have hr2 : IsAlgebraic ℚ⟮z, L3⟯ (d - b3 * L3) := hd.sub (hb3.mul hL3)
  refine ⟨?_, ?_, hL3, he1, he2, he3⟩
  · rw [hL1]; exact ((hr1.mul hb2).sub (ha2.mul hr2)).mul hdetA.inv
  · rw [hL2]; exact ((ha1.mul hr2).sub (hr1.mul hb1)).mul hdetA.inv

end PairLaw
