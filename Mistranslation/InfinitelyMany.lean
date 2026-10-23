import Mathlib
import Mistranslation.SpringFamily

/-! # The law makes infinitely many transcendental break numbers (2026-10-23)

Every simple (algebraic) knob value in a one-clock family gives a break that is a real tipping point of its equation
AND is transcendental. Simple knobs never run out, so neither do these numbers. Proved here on the forced spring family
x'' + mu (1 + b x) = 0: the knobs b = 1, 2, 3, ... give infinitely many DIFFERENT breaks pi^2/b, each one the exact
tipping point of its equation and each one transcendental. -/

namespace InfinitelyMany

open SpringFamily

/-- The breaks the law certifies: tipping points of a simple-knob equation that are transcendental. -/
def certified : Set ℝ :=
  {B | ∃ b : ℝ, 0 < b ∧ IsAlgebraic ℚ b ∧
    IsLUB {μ : ℝ | 0 < μ ∧ ∃ x x' : ℝ → ℝ, Sol' b μ x x'} B ∧ Transcendental ℚ B}

/-- **Infinitely many transcendental break numbers.** -/
theorem certified_infinite : certified.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => Real.pi ^ 2 / ((n : ℝ) + 1)) := by
    intro m n h
    have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
    have h' : ((m : ℝ) + 1) = (n : ℝ) + 1 := by
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      field_simp at h
      nlinarith [h]
    exact_mod_cast (add_right_cancel h')
  refine Set.infinite_of_injective_forall_mem hinj fun n => ?_
  have hb : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbA : IsAlgebraic ℚ ((n : ℝ) + 1) := by
    simpa using (isAlgebraic_algebraMap ((n : ℚ) + 1) : IsAlgebraic ℚ (algebraMap ℚ ℝ ((n : ℚ) + 1)))
  exact ⟨(n : ℝ) + 1, hb, hbA, forced_break_transcendental hb hbA⟩

end InfinitelyMany

#print axioms InfinitelyMany.certified_infinite
