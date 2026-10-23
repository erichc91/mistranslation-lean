import Mathlib

/-!
# Hot wire: Euler's gamma is the exact correction in a runaway threshold

A thin wire (radius `e`) heats itself at `mu * exp T` and leaks heat into a screened medium at
`L * T`, where `L = 2 pi e K1(e) / K0(e)`. Runaway threshold (break number): `mu* = L / exp 1`.

* `runaway_break` : for every leak `L > 0`, the largest `mu` with a steady state `mu * exp T = L * T`
  is exactly `L / exp 1`, reached at `T = 1`. No assumptions.
* `hot_wire_gamma` : if `k0, k1` behave like the Bessel functions `K0, K1` near 0 (two classical facts,
  DLMF 10.31.2 / 10.31.1, passed in as hypotheses because Mathlib has no Bessel K), then
  `log (2/e) - 2 pi / (exp 1 * mu*(e)) -> gamma` as `e -> 0+`, with `gamma = Real.eulerMascheroniConstant`.
-/

open Real Filter Topology

namespace HotWire

/-- `T * exp (-T) ≤ exp (-1)` for every real `T`, from `x + 1 ≤ exp x`. -/
lemma mul_exp_neg_le (T : ℝ) : T * exp (-T) ≤ exp (-1) := by
  have h := add_one_le_exp (T - 1)
  have hpos : 0 < exp (-T) := exp_pos _
  have : T ≤ exp (T - 1) := by linarith
  calc T * exp (-T) ≤ exp (T - 1) * exp (-T) := mul_le_mul_of_nonneg_right this hpos.le
    _ = exp (-1) := by rw [← exp_add]; ring_nf

/-- Runaway: the set of pushes `mu` that admit a steady state `mu * exp T = L * T` has greatest
element `L / exp 1`. -/
theorem runaway_break (L : ℝ) (hL : 0 < L) :
    IsGreatest {mu : ℝ | ∃ T : ℝ, mu * exp T = L * T} (L / exp 1) := by
  refine ⟨⟨1, ?_⟩, ?_⟩
  · field_simp
  · rintro mu ⟨T, hT⟩
    have hE : 0 < exp T := exp_pos T
    have hmu : mu = L * (T * exp (-T)) := by
      rw [exp_neg]; field_simp; linarith
    rw [hmu, div_eq_mul_inv, ← exp_neg]
    exact mul_le_mul_of_nonneg_left (mul_exp_neg_le T) hL.le

/-- The break number of the hot wire, given the two Bessel values. -/
noncomputable def muStar (k0 k1 : ℝ → ℝ) (e : ℝ) : ℝ := (2 * π * e * k1 e / k0 e) / exp 1

/-- Euler's gamma is the exact correction: `log (2/e) - 2π / (e · mu*) → γ`. -/
theorem hot_wire_gamma (k0 k1 : ℝ → ℝ)
    (hpos0 : ∀ᶠ e in 𝓝[>] (0:ℝ), 0 < k0 e)
    (hpos1 : ∀ᶠ e in 𝓝[>] (0:ℝ), 0 < k1 e)
    (hK0 : Tendsto (fun e => k0 e + log (e / 2)) (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)))
    (hK1 : Tendsto (fun e => e * k1 e) (𝓝[>] 0) (𝓝 1))
    (hK1log : Tendsto (fun e => (e * k1 e - 1) * log e) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun e => log (2 / e) - 2 * π / (exp 1 * muStar k0 k1 e)) (𝓝[>] 0)
      (𝓝 eulerMascheroniConstant) := by
  -- numerator / denominator form
  have hnum : Tendsto (fun e => -(k0 e + log (e / 2)) + log 2 * (e * k1 e - 1)
      - (e * k1 e - 1) * log e) (𝓝[>] 0) (𝓝 eulerMascheroniConstant) := by
    have h2 : Tendsto (fun e => log 2 * (e * k1 e - 1)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have := (hK1.sub_const 1).const_mul (log 2); simpa using this
    have := (hK0.neg.add h2).sub hK1log
    simpa using this
  have hq := hnum.div hK1 one_ne_zero
  rw [div_one] at hq
  refine hq.congr' ?_
  filter_upwards [hpos0, hpos1, self_mem_nhdsWithin] with e h0 h1 he
  have he' : (0:ℝ) < e := he
  have hek : 0 < e * k1 e := mul_pos he' h1
  have hlog : log (2 / e) = log 2 - log e := log_div (by norm_num) he'.ne'
  have hlog2 : log (e / 2) = log e - log 2 := log_div he'.ne' (by norm_num)
  show (-(k0 e + log (e / 2)) + log 2 * (e * k1 e - 1) - (e * k1 e - 1) * log e) / (e * k1 e)
    = log (2 / e) - 2 * π / (exp 1 * muStar k0 k1 e)
  unfold muStar
  rw [hlog, hlog2]
  have hk0 : k0 e ≠ 0 := h0.ne'
  have hk1 : k1 e ≠ 0 := h1.ne'
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp
  ring

end HotWire
