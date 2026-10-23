import Mathlib
import Mistranslation.PinneySpring
import Mistranslation.LinearOde

/-! # The cos/sin side of the web: classes from Lindemann-for-sine (2026-10-23)

`PinneySpring.LindemannSin` (sin a transcendental for algebraic a != 0; a theorem, not in this Mathlib) settles the
whole trigonometric band at once:
- the genus-0 linear seat's break pi^2 is transcendental (pi algebraic would make sin pi = 0 algebraic);
- the Ermakov-Pinney + spring break (w / sin w)^2 is transcendental for EVERY algebraic w in (0, pi/2). -/

namespace TrigClass

open PinneySpring

theorem pi_transcendental (LS : LindemannSin) : Transcendental ℚ Real.pi := by
  intro hpi
  exact LS Real.pi hpi Real.pi_ne_zero (by rw [Real.sin_pi]; exact isAlgebraic_zero)

/-- **The genus-0 band: break pi^2 (the least upper bound of the linear seat) is transcendental.** -/
theorem linear_break_transcendental (LS : LindemannSin) :
    IsLUB {μ : ℝ | 0 < μ ∧ ∃ x x' : ℝ → ℝ, LinearOde.Sol μ x x'} (Real.pi ^ 2) ∧ Transcendental ℚ (Real.pi ^ 2) :=
  ⟨LinearOde.linear_break_exact, fun h => pi_transcendental LS (IsAlgebraic.of_pow (by norm_num) h)⟩

/-- **Ermakov-Pinney with a spring: for every algebraic w in (0, pi/2) the break (w / sin w)^2 exists and is
transcendental.** -/
theorem pinney_spring_transcendental (LS : LindemannSin) {ω : ℝ} (hω : 0 < ω) (hωpi : ω < Real.pi / 2)
    (hωA : IsAlgebraic ℚ ω) :
    IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol ω μ v v'} (ω ^ 2 / Real.sin ω ^ 2) ∧
      Transcendental ℚ (ω ^ 2 / Real.sin ω ^ 2) := by
  refine ⟨break_exact hω hωpi, ?_⟩
  intro hB
  have hS : 0 < Real.sin ω := Real.sin_pos_of_pos_of_lt_pi hω (by linarith [Real.pi_pos])
  have hs2 : IsAlgebraic ℚ (Real.sin ω ^ 2) := by
    have : Real.sin ω ^ 2 = ω ^ 2 * (ω ^ 2 / Real.sin ω ^ 2)⁻¹ := by field_simp
    rw [this]; exact (hωA.pow 2).mul hB.inv
  exact LS ω hωA hω.ne' (IsAlgebraic.of_pow (by norm_num) hs2)

end TrigClass
