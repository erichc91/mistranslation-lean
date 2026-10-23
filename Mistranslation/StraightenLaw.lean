import Mathlib
import Mistranslation.PinneyInv
import Mistranslation.PinneySpring

/-! # The straightening law (2026-10-23)

Every bridge closed today ran the same five moves: straighten -> solve a spring -> read the push curve -> find the
top -> tie the knob to the clock. Moves 1-2 are one lemma: whatever the seat, its straightened coordinate u obeys a
SHIFTED SPRING `u'' = A u + beta` with equal ends `b`, and then the middle value and slope are forced:
  A > 0 (cosh):  u(1/2) = -beta/A + (b + beta/A) / cosh(sqrt A / 2),   u'(1/2) = 0
  A < 0 (cos):   u(1/2) = -beta/A + (b + beta/A) / cos(sqrt(-A) / 2), u'(1/2) = 0   (sqrt(-A) < pi)
Each seat is then an instance (examples below): Bratu, Morse, the predicted family, Ermakov-Pinney +- spring. -/

namespace StraightenLaw

/-- **Shifted cosh-spring.** -/
theorem shifted_spring {u u' : ℝ → ℝ} {A β b : ℝ} (hA : 0 < A)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (u' t) t ∧ HasDerivAt u' (A * u t + β) t)
    (h0 : u 0 = b) (h1 : u 1 = b) :
    u (1 / 2) = (b + β / A) / Real.cosh (Real.sqrt A / 2) - β / A ∧ u' (1 / 2) = 0 := by
  have hk := Real.sqrt_pos.mpr hA
  have hA0 : A ≠ 0 := hA.ne'
  have hk2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  have sol := PinneyInv.cosh_solve (z := fun t => u t + β / A) (z' := u') (k := Real.sqrt A) (z0 := b + β / A) hk
    (fun t ht => by
      obtain ⟨h1, h2⟩ := hd t ht
      refine ⟨(h1.add_const _).congr_deriv (by ring), h2.congr_deriv ?_⟩
      rw [hk2]; field_simp)
    (by simp [h0]) (by simp [h1])
  obtain ⟨hz, hz'⟩ := sol
  exact ⟨by beta_reduce at hz; linarith, hz'⟩

/-- **Shifted cos-spring** (for the ordinary-spring seats). -/
theorem shifted_spring_trig {u u' : ℝ → ℝ} {A β b : ℝ} (hA : A < 0) (hApi : Real.sqrt (-A) < Real.pi)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (u' t) t ∧ HasDerivAt u' (A * u t + β) t)
    (h0 : u 0 = b) (h1 : u 1 = b) :
    u (1 / 2) = (b + β / A) / Real.cos (Real.sqrt (-A) / 2) - β / A ∧ u' (1 / 2) = 0 := by
  have hk := Real.sqrt_pos.mpr (neg_pos.mpr hA)
  have hA0 : A ≠ 0 := hA.ne
  have hk2 : Real.sqrt (-A) ^ 2 = -A := Real.sq_sqrt (neg_pos.mpr hA).le
  have sol := PinneySpring.trig_solve (z := fun t => u t + β / A) (z' := u') (k := Real.sqrt (-A)) (z0 := b + β / A)
    hk hApi
    (fun t ht => by
      obtain ⟨h1, h2⟩ := hd t ht
      refine ⟨(h1.add_const _).congr_deriv (by ring), h2.congr_deriv ?_⟩
      rw [hk2]; field_simp)
    (by simp [h0]) (by simp [h1])
  obtain ⟨hz, hz'⟩ := sol
  exact ⟨by beta_reduce at hz; linarith, hz'⟩

end StraightenLaw
