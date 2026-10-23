import Mathlib
import Mistranslation.ShiftedSpring

/-! # The last sign case of the linear seats: negative load, stiff spring (2026-10-23, Classified Table C5)

`ShiftedSpring.lean` left one sub-case open: load F < 0 with stiffness k > 4 pi^2. For the BREAK question (is the set
of solvable pushes bounded?) it is enough to find solvable stiffnesses that grow without bound: at k = (4 m pi)^2 the
explicit cos solution is (-F/k)(1 - cos(4 m pi (t - 1/2))) >= 0. So with negative load and b > 0 the solvable pushes are
unbounded: NO break number (the onset pi^2/b, from `forced_neg_class`, is where solutions start). Whether every
k > 4 pi^2 is solvable is NOT needed for the break and is not claimed. -/

namespace ShiftedSpringNeg

open ShiftedSpring

lemma sqrt_comb (m : ℕ) : Real.sqrt ((4 * m * Real.pi) ^ 2) = 4 * m * Real.pi :=
  Real.sqrt_sq (by positivity)

lemma cos_comb_half (m : ℕ) : Real.cos (Real.sqrt ((4 * m * Real.pi) ^ 2) / 2) = 1 := by
  rw [sqrt_comb, show 4 * (m : ℝ) * Real.pi / 2 = (m : ℕ) * (2 * Real.pi) by ring]
  exact Real.cos_nat_mul_two_pi _

/-- **Negative load, comb stiffness (4 m pi)^2: a nonnegative solution exists.** -/
theorem comb_sol {F : ℝ} (hF : F < 0) (m : ℕ) (hm : 0 < m) :
    FSol F ((4 * m * Real.pi) ^ 2) (cx F ((4 * m * Real.pi) ^ 2)) (cx' F ((4 * m * Real.pi) ^ 2)) := by
  set k := (4 * (m : ℝ) * Real.pi) ^ 2 with hkdef
  have hk : 0 < k := by have : (0 : ℝ) < m := by exact_mod_cast hm
                        positivity
  have hC := cos_comb_half m
  have hend : ∀ t : ℝ, t = 0 ∨ t = 1 → Real.cos (Real.sqrt k * (t - 1 / 2)) = 1 := by
    intro t ht
    rw [sqrt_comb]
    rcases ht with rfl | rfl
    · rw [show 4 * (m : ℝ) * Real.pi * (0 - 1 / 2) = -((m : ℕ) * (2 * Real.pi)) by ring,
        Real.cos_neg]; exact Real.cos_nat_mul_two_pi _
    · rw [show 4 * (m : ℝ) * Real.pi * (1 - 1 / 2) = (m : ℕ) * (2 * Real.pi) by ring]
      exact Real.cos_nat_mul_two_pi _
  refine ⟨fun t _ => ⟨?_, (cx_solves hk (by rw [hC]; norm_num) t).1, (cx_solves hk (by rw [hC]; norm_num) t).2⟩, ?_, ?_⟩
  · unfold cx; rw [hC, div_one]
    apply mul_nonneg_of_nonpos_of_nonpos
    · exact (div_neg_of_neg_of_pos hF hk).le
    · linarith [Real.cos_le_one (Real.sqrt k * (t - 1 / 2))]
  · unfold cx; rw [hC, hend 0 (Or.inl rfl)]; ring
  · unfold cx; rw [hC, hend 1 (Or.inr rfl)]; ring

/-- **Negative load for every push, stiffness growing with the push: no break number.** -/
theorem forced_neg_no_break {a b c0 c1 : ℝ} (hb : 0 < b) (hF : ∀ μ : ℝ, 0 < μ → c0 + c1 * μ < 0) :
    ¬ BddAbove (FPushes a b c0 c1) := by
  rintro ⟨M, hM⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (|a| + b * (|M| + 1) + 1)
  have hm1 : (1 : ℝ) ≤ m := by nlinarith [abs_nonneg a, abs_nonneg M]
  have hm0 : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have hbig : (m : ℝ) ≤ (4 * m * Real.pi) ^ 2 := by
    have h4 : (1 : ℝ) ≤ (4 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    have hmm : (m : ℝ) ≤ m * m := by nlinarith
    calc (m : ℝ) ≤ m * m := hmm
      _ ≤ m * m * (4 * Real.pi) ^ 2 := le_mul_of_one_le_right (by positivity) h4
      _ = (4 * m * Real.pi) ^ 2 := by ring
  set μ := ((4 * m * Real.pi) ^ 2 - a) / b with hμ
  have hμgt : |M| + 1 < μ := by
    rw [hμ, lt_div_iff₀ hb]; nlinarith [le_abs_self a]
  have hμpos : 0 < μ := by linarith [abs_nonneg M]
  have hk : a + b * μ = (4 * m * Real.pi) ^ 2 := by rw [hμ]; field_simp; ring
  have hmem : μ ∈ FPushes a b c0 c1 := ⟨hμpos, _, _, hk ▸ comb_sol (hF μ hμpos) m hm0⟩
  linarith [hM hmem, le_abs_self M]

end ShiftedSpringNeg

#print axioms ShiftedSpringNeg.comb_sol
#print axioms ShiftedSpringNeg.forced_neg_no_break
