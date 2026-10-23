import Mathlib
import Mistranslation.TimeMapExists

/-! # Weakening seats written with x'' on the other side (2026-10-23)

Two ledger seats read 1 - x'' - x^k = 0 (k = 2, 4), i.e. x'' + mu (x^k - 1) = 0. Flipping x -> -x turns any solution of
the weakening seat x'' + mu (1 - x^k) = 0 into one of these when k is even, so `weakening_no_break` carries over. -/

namespace WeakeningFlip

theorem flip_sol {k : ℕ} (hk : Even k) {μ : ℝ} {x x' : ℝ → ℝ}
    (h : TippingRule.Sol (fun y => 1 - y ^ k) μ x x') :
    TippingRule.Sol (fun y => y ^ k - 1) μ (fun t => -x t) (fun t => -x' t) := by
  refine ⟨fun t ht => ?_, by simp [h.2.1], by simp [h.2.2]⟩
  obtain ⟨hd, hdd⟩ := h.1 t ht
  refine ⟨hd.neg, hdd.neg.congr_deriv ?_⟩
  simp only [hk.neg_pow]; ring

/-- **x'' + mu (x^k - 1) = 0, k even: no break number.** -/
theorem flipped_no_break {k : ℕ} (hk1 : 1 ≤ k) (hk : Even k) :
    TippingRule.Pushes (fun y => y ^ k - 1) = Set.Ioi 0 ∧ ¬ BddAbove (TippingRule.Pushes (fun y => y ^ k - 1)) := by
  refine TippingRule.no_break_of_forall fun μ hμ => ?_
  have hm : μ ∈ TippingRule.Pushes (fun y => 1 - y ^ k) := by
    rw [(TimeMapExists.Weakening.weakening_no_break hk1).1]; exact hμ
  obtain ⟨_, x, x', hs⟩ := hm
  exact ⟨_, _, flip_sol hk hs⟩

end WeakeningFlip

#print axioms WeakeningFlip.flipped_no_break
