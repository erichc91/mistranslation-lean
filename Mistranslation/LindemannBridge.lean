import Mathlib
import Mistranslation.Vendor.Lindemann.Basic
import Mistranslation.Breaks
import Mistranslation.PinneySpring

/-! # The two outside hypotheses, now theorems (2026-10-23, Classified Table phase C0)

`Breaks.HermiteLindemann` (e^a transcendental for real algebraic a != 0) and `PinneySpring.LindemannSin`
(sin a transcendental for real algebraic a != 0) were carried as hypotheses. Both follow from the Lindemann-Weierstrass
theorem, formalized by Yuyang Zhao (vendored in `Mistranslation/Vendor/Lindemann`, from github.com/astrainfinita/mathlib4,
branch `transcendental`; Mathlib already contains its analytic half). After this file no result in the break table
rests on an outside hypothesis. -/

namespace LindemannBridge

open Complex

/-- Algebraic over ℚ and over ℤ agree for complex numbers. -/
lemma alg_int_of_rat {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).2 h

lemma alg_rat_of_int {z : ℂ} (h : IsAlgebraic ℤ z) : IsAlgebraic ℚ z :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).1 h

lemma ofReal_alg {x : ℝ} (h : IsAlgebraic ℚ x) : IsAlgebraic ℚ (x : ℂ) := by
  simpa using IsAlgebraic.algebraMap (A := ℂ) h

lemma alg_of_ofReal {x : ℝ} (h : IsAlgebraic ℚ (x : ℂ)) : IsAlgebraic ℚ x :=
  (isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).1 (by simpa using h)

/-- **Hermite-Lindemann (real form), proved.** -/
theorem hermite_lindemann : Breaks.HermiteLindemann := by
  intro a ha ha0 hexp
  have hza : IsAlgebraic ℤ (a : ℂ) := alg_int_of_rat (ofReal_alg ha)
  have hne : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
  apply transcendental_exp hne hza
  have : IsAlgebraic ℚ (Complex.exp (a : ℂ)) := by
    rw [← Complex.ofReal_exp]; exact ofReal_alg hexp
  exact alg_int_of_rat this

/-- **Lindemann for sine, proved.** If sin a were algebraic, so would be cos a and e^(ia) = cos a + i sin a. -/
theorem lindemann_sin : PinneySpring.LindemannSin := by
  intro a ha ha0 hsin
  have hs : IsAlgebraic ℚ (Real.sin a : ℂ) := ofReal_alg hsin
  have hc2 : IsAlgebraic ℚ ((Real.cos a : ℂ) ^ 2) := by
    have : ((Real.cos a : ℂ)) ^ 2 = 1 - (Real.sin a : ℂ) ^ 2 := by
      have := Complex.cos_sq_add_sin_sq (a : ℂ)
      push_cast; linear_combination this
    rw [this]; exact isAlgebraic_one.sub (hs.pow 2)
  have hc : IsAlgebraic ℚ (Real.cos a : ℂ) := IsAlgebraic.of_pow (by norm_num) hc2
  have hI : IsAlgebraic ℚ Complex.I := by
    refine ⟨Polynomial.X ^ 2 + 1, ?_, by simp⟩
    intro h0
    have := congrArg (Polynomial.eval 0) h0
    simp at this
  have hia : IsAlgebraic ℤ (Complex.I * a) := alg_int_of_rat (hI.mul (ofReal_alg ha))
  have hne : Complex.I * a ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ha0)
  apply transcendental_exp hne hia
  have : Complex.exp (Complex.I * a) = (Real.cos a : ℂ) + Complex.I * (Real.sin a : ℂ) := by
    rw [mul_comm, Complex.exp_mul_I]; push_cast; ring
  rw [this]; exact alg_int_of_rat (hc.add (hI.mul hs))

end LindemannBridge
