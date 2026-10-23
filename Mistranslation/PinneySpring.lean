import Mathlib
import Mistranslation.BratuOde
import Mistranslation.HypOde

/-! # Ermakov-Pinney with a spring (2026-10-23)

Seat `v'' + w^2 v = mu / v^3`, `v(0) = v(1) = 1`, `v > 0`, `0 < w < pi/2` (w = 1 is the table's 32-paper seat
'+[1] -[D2*y0^3] -[y0^4]'). Break = `(w / sin w)^2`, exactly. Route: `W = v^2` obeys the LINEAR equation
`W'' = 2E - 4 w^2 W`; a trig two-Wronskian solver pins W; the push is a quadratic in one knob. -/

namespace PinneySpring

def Sol (ω μ : ℝ) (v v' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < v t ∧ HasDerivAt v (v' t) t ∧
      HasDerivAt v' (μ / v t ^ 3 - ω ^ 2 * v t) t) ∧ v 0 = 1 ∧ v 1 = 1

lemma energy {ω μ : ℝ} {v v' : ℝ → ℝ} (h : Sol ω μ v v') :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, v' t * v' t + μ * (v t * v t)⁻¹ + ω ^ 2 * (v t * v t)
      = v' 0 * v' 0 + μ * (v 0 * v 0)⁻¹ + ω ^ 2 * (v 0 * v 0) := by
  refine BratuOde.const_on (f := fun t => v' t * v' t + μ * (v t * v t)⁻¹ + ω ^ 2 * (v t * v t)) ?_
  intro s hs
  obtain ⟨hv, hd, hdd⟩ := h.1 s hs
  have hvv : v s * v s ≠ 0 := by positivity
  have := ((hdd.mul hdd).add (((hd.mul hd).inv hvv).const_mul μ)).add ((hd.mul hd).const_mul (ω ^ 2))
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Trig two-Wronskian solver: `z'' = -k^2 z`, `z(0) = z(1) = z0`, `0 < k < pi` gives
`z(1/2) = z0 / cos(k/2)` and `z'(1/2) = 0`. -/
lemma trig_solve {z z' : ℝ → ℝ} {k z0 : ℝ} (hk : 0 < k) (hkpi : k < Real.pi)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt z (z' t) t ∧ HasDerivAt z' (-(k ^ 2) * z t) t)
    (h0 : z 0 = z0) (h1 : z 1 = z0) :
    z (1 / 2) = z0 / Real.cos (k / 2) ∧ z' (1 / 2) = 0 := by
  have hc : ∀ t, HasDerivAt (fun t => Real.cos (k * (t - 1 / 2))) (-(k * Real.sin (k * (t - 1 / 2)))) t := by
    intro t
    have h := (Real.hasDerivAt_cos (k * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul k)
    exact h.congr_deriv (by ring)
  have hs : ∀ t, HasDerivAt (fun t => Real.sin (k * (t - 1 / 2))) (k * Real.cos (k * (t - 1 / 2))) t := by
    intro t
    have h := (Real.hasDerivAt_sin (k * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul k)
    exact h.congr_deriv (by ring)
  have W1 := BratuOde.const_on (a := 0) (b := 1)
    (f := fun t => z t * (k * Real.cos (k * (t - 1 / 2))) - z' t * Real.sin (k * (t - 1 / 2))) (by
      intro s hs'
      obtain ⟨hz, hz'⟩ := hd s hs'
      exact ((hz.mul ((hc s).const_mul k)).sub (hz'.mul (hs s))).congr_deriv (by ring))
  have W2 := BratuOde.const_on (a := 0) (b := 1)
    (f := fun t => -(z t * (k * Real.sin (k * (t - 1 / 2)))) - z' t * Real.cos (k * (t - 1 / 2))) (by
      intro s hs'
      obtain ⟨hz, hz'⟩ := hd s hs'
      exact (((hz.mul ((hs s).const_mul k)).neg).sub (hz'.mul (hc s))).congr_deriv (by ring))
  have mem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have mem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have memh : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set A := z 0 * (k * Real.cos (k * (0 - 1 / 2))) - z' 0 * Real.sin (k * (0 - 1 / 2)) with hA
  set B := -(z 0 * (k * Real.sin (k * (0 - 1 / 2)))) - z' 0 * Real.cos (k * (0 - 1 / 2)) with hB
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      k * z t = A * Real.cos (k * (t - 1 / 2)) - B * Real.sin (k * (t - 1 / 2)) ∧
      z' t = -(A * Real.sin (k * (t - 1 / 2)) + B * Real.cos (k * (t - 1 / 2))) := by
    intro t ht
    have e1 : z t * (k * Real.cos (k * (t - 1 / 2))) - z' t * Real.sin (k * (t - 1 / 2)) = A := W1 t ht
    have e2 : -(z t * (k * Real.sin (k * (t - 1 / 2)))) - z' t * Real.cos (k * (t - 1 / 2)) = B := W2 t ht
    have hcs := Real.sin_sq_add_cos_sq (k * (t - 1 / 2))
    constructor
    · rw [← e1, ← e2]; linear_combination (-(k * z t)) * hcs
    · rw [← e1, ← e2]; linear_combination (-(z' t)) * hcs
  have hS : 0 < Real.sin (k / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hC : 0 < Real.cos (k / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have k0 := (key 0 mem0).1
  have k1 := (key 1 mem1).1
  rw [h0, show k * (0 - 1 / 2) = -(k / 2) by ring, Real.cos_neg, Real.sin_neg] at k0
  rw [h1, show k * (1 - 1 / 2) = k / 2 by ring] at k1
  have hB0 : B = 0 := by
    have : B * Real.sin (k / 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with hb | hs0
    · exact hb
    · linarith
  have hAv : A = k * z0 / Real.cos (k / 2) := by
    rw [hB0] at k1; field_simp; linarith
  obtain ⟨kh, kh'⟩ := key (1 / 2) memh
  simp only [sub_self, mul_zero, Real.cos_zero, Real.sin_zero, mul_one, zero_mul, sub_zero, add_zero, neg_zero] at kh kh'
  refine ⟨?_, by rw [kh', hB0]; ring⟩
  apply mul_left_cancel₀ hk.ne'
  rw [kh, hAv]; field_simp

/-- **No push above `(w / sin w)^2` has a solution.** -/
theorem break_le {ω μ : ℝ} {v v' : ℝ → ℝ} (hω : 0 < ω) (hωpi : ω < Real.pi / 2) (h : Sol ω μ v v') :
    μ ≤ ω ^ 2 / Real.sin ω ^ 2 := by
  set E := v' 0 * v' 0 + μ * (v 0 * v 0)⁻¹ + ω ^ 2 * (v 0 * v 0) with hE
  clear_value E
  have hω2 : 0 < ω ^ 2 := by positivity
  have memh : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  -- z = v^2 - E/(2 w^2) is a trig spring with k = 2w
  have sol := trig_solve (z := fun t => v t * v t - E / (2 * ω ^ 2)) (z' := fun t => 2 * v t * v' t)
    (k := 2 * ω) (z0 := 1 - E / (2 * ω ^ 2)) (by linarith) (by linarith)
    (fun t ht => by
      obtain ⟨hv, hd, hdd⟩ := h.1 t ht
      have hvt : v t ≠ 0 := hv.ne'
      refine ⟨((hd.mul hd).sub_const _).congr_deriv (by ring), ?_⟩
      have hEt := energy h t ht
      rw [← hE] at hEt
      refine ((hd.const_mul 2).mul hdd).congr_deriv ?_
      field_simp
      field_simp at hEt
      linear_combination (1 : ℝ) * hEt)
    (by simp [h.2.1]) (by simp [h.2.2])
  obtain ⟨hz, hz'⟩ := sol
  beta_reduce at hz hz'
  rw [show 2 * ω / 2 = ω by ring] at hz
  have hv := (h.1 (1 / 2) memh).1
  have hv'0 : v' (1 / 2) = 0 := by
    have : v (1 / 2) * v' (1 / 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact h0
  have hC : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hS : 0 < Real.sin ω := Real.sin_pos_of_pos_of_lt_pi hω (by linarith [Real.pi_pos])
  have hEm := energy h (1 / 2) memh
  rw [← hE, hv'0] at hEm
  set C := Real.cos ω
  set S := Real.sin ω
  have hCS : S ^ 2 + C ^ 2 = 1 := Real.sin_sq_add_cos_sq ω
  set s := E / (2 * ω ^ 2) with hs
  set wm := v (1 / 2) * v (1 / 2) with hwm
  have hwmpos : 0 < wm := by positivity
  have hwmC : wm * C = s * C + 1 - s := by
    have : wm = s + (1 - s) / C := by linarith
    rw [this]; field_simp; ring
  have hEs : E = 2 * ω ^ 2 * s := by rw [hs]; field_simp
  -- energy at the middle: E = mu / wm + w^2 wm
  have hmu : μ = E * wm - ω ^ 2 * wm ^ 2 := by
    field_simp at hEm
    nlinarith [hEm, hwmpos]
  have iden : ω ^ 2 * C ^ 2 - μ * S ^ 2 * C ^ 2 = ω ^ 2 * (s * S ^ 2 - 1) ^ 2 := by
    rw [hmu, hEs]
    linear_combination (ω ^ 2 * S ^ 2 * (wm * C + (s * C + 1 - s)) - 2 * ω ^ 2 * s * S ^ 2 * C) * hwmC
      + (ω ^ 2 * (1 - s ^ 2 * S ^ 2)) * hCS
  have h1 : μ * S ^ 2 * C ^ 2 ≤ ω ^ 2 * C ^ 2 := by nlinarith [iden, sq_nonneg (s * S ^ 2 - 1), hω2]
  have h2 : μ * S ^ 2 ≤ ω ^ 2 := le_of_mul_le_mul_right (by linarith) (pow_pos hC 2)
  rw [le_div_iff₀ (pow_pos hS 2)]; linarith

/-- The algebra behind existence, in plain variables (`R = sqrt w`, `c, s = cos, sin of 2w(t - 1/2)`). -/
lemma exist_alg {ω C S c s R W : ℝ} (hS : 0 < S) (hR : 0 < R) (hCS : S ^ 2 + C ^ 2 = 1) (hcs : s ^ 2 + c ^ 2 = 1)
    (hW : W = 1 / S ^ 2 - C / S ^ 2 * c) (hRW : R ^ 2 = W) :
    ((-(4 * ω ^ 2 * (-(C / S ^ 2)) * c)) * (2 * R) - (-(2 * ω * (-(C / S ^ 2)) * s)) * (2 * ((-(2 * ω * (-(C / S ^ 2)) * s)) / (2 * R))))
        / (2 * R) ^ 2
      = ω ^ 2 / S ^ 2 / R ^ 3 - ω ^ 2 * R := by
  rw [div_eq_iff (by positivity)]
  field_simp
  have hSR : S ^ 2 * R ^ 2 = 1 - C * c := by rw [hRW, hW]; field_simp
  linear_combination (4 * ω ^ 2 * C * c + 2 * ω ^ 2 * (S ^ 2 * R ^ 2 + (1 - C * c))) * hSR
    - 2 * ω ^ 2 * C ^ 2 * hcs - 2 * ω ^ 2 * hCS

theorem exists_top {ω : ℝ} (hω : 0 < ω) (hωpi : ω < Real.pi / 2) :
    Sol ω (ω ^ 2 / Real.sin ω ^ 2)
      (fun t => Real.sqrt (1 / Real.sin ω ^ 2 - Real.cos ω / Real.sin ω ^ 2 * Real.cos (2 * ω * (t - 1 / 2))))
      (fun t => (-(2 * ω * (-(Real.cos ω / Real.sin ω ^ 2)) * Real.sin (2 * ω * (t - 1 / 2)))) /
        (2 * Real.sqrt (1 / Real.sin ω ^ 2 - Real.cos ω / Real.sin ω ^ 2 * Real.cos (2 * ω * (t - 1 / 2))))) := by
  have hC : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hS : 0 < Real.sin ω := Real.sin_pos_of_pos_of_lt_pi hω (by linarith [Real.pi_pos])
  have hC1 : Real.cos ω < 1 := by
    have := Real.sin_sq_add_cos_sq ω; nlinarith
  have hCS := Real.sin_sq_add_cos_sq ω
  set C := Real.cos ω
  set S := Real.sin ω
  -- w > 0 everywhere
  have hwpos : ∀ t : ℝ, 0 < 1 / S ^ 2 - C / S ^ 2 * Real.cos (2 * ω * (t - 1 / 2)) := by
    intro t
    have hcle := Real.cos_le_one (2 * ω * (t - 1 / 2))
    have : C / S ^ 2 * Real.cos (2 * ω * (t - 1 / 2)) ≤ C / S ^ 2 := by
      have : 0 ≤ C / S ^ 2 := by positivity
      nlinarith
    have : C / S ^ 2 < 1 / S ^ 2 := by
      apply div_lt_div_of_pos_right hC1 (by positivity)
    linarith
  have hcd : ∀ t, HasDerivAt (fun t => Real.cos (2 * ω * (t - 1 / 2))) (-(2 * ω * Real.sin (2 * ω * (t - 1 / 2)))) t := by
    intro t
    have h := (Real.hasDerivAt_cos (2 * ω * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul (2 * ω))
    exact h.congr_deriv (by ring)
  have hsd : ∀ t, HasDerivAt (fun t => Real.sin (2 * ω * (t - 1 / 2))) (2 * ω * Real.cos (2 * ω * (t - 1 / 2))) t := by
    intro t
    have h := (Real.hasDerivAt_sin (2 * ω * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul (2 * ω))
    exact h.congr_deriv (by ring)
  have hw : ∀ t, HasDerivAt (fun t => 1 / S ^ 2 - C / S ^ 2 * Real.cos (2 * ω * (t - 1 / 2)))
      (-(2 * ω * (-(C / S ^ 2)) * Real.sin (2 * ω * (t - 1 / 2)))) t := by
    intro t
    exact (((hcd t).const_mul (C / S ^ 2)).const_sub (1 / S ^ 2)).congr_deriv (by ring)
  have hw' : ∀ t, HasDerivAt (fun t => -(2 * ω * (-(C / S ^ 2)) * Real.sin (2 * ω * (t - 1 / 2))))
      (-(4 * ω ^ 2 * (-(C / S ^ 2)) * Real.cos (2 * ω * (t - 1 / 2)))) t := by
    intro t
    exact (((hsd t).const_mul (2 * ω * (-(C / S ^ 2)))).neg).congr_deriv (by ring)
  refine ⟨fun t _ => ⟨Real.sqrt_pos.mpr (hwpos t), ?_, ?_⟩, ?_, ?_⟩
  · exact ((hw t).sqrt (hwpos t).ne').congr_deriv rfl
  · have hR := Real.sqrt_pos.mpr (hwpos t)
    have hsq := (hw t).sqrt (hwpos t).ne'
    refine ((hw' t).div (hsq.const_mul 2) (by positivity)).congr_deriv ?_
    have hRW := Real.sq_sqrt (hwpos t).le
    have hcs := Real.sin_sq_add_cos_sq (2 * ω * (t - 1 / 2))
    exact exist_alg hS hR hCS hcs rfl hRW
  · beta_reduce
    rw [show 2 * ω * (0 - 1 / 2) = -ω by ring, Real.cos_neg]
    rw [show 1 / S ^ 2 - C / S ^ 2 * C = 1 by field_simp; linarith, Real.sqrt_one]
  · beta_reduce
    rw [show 2 * ω * (1 - 1 / 2) = ω by ring]
    rw [show 1 / S ^ 2 - C / S ^ 2 * C = 1 by field_simp; linarith, Real.sqrt_one]

/-- **Ermakov-Pinney with a spring: the break is exactly `(w / sin w)^2`.** -/
theorem break_exact {ω : ℝ} (hω : 0 < ω) (hωpi : ω < Real.pi / 2) :
    IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol ω μ v v'} (ω ^ 2 / Real.sin ω ^ 2) :=
  ⟨⟨_, _, exists_top hω hωpi⟩, fun _ ⟨_, _, h⟩ => break_le hω hωpi h⟩

/-- Lindemann for sine: `sin a` is transcendental for algebraic `a != 0` (a theorem, not in this Mathlib). -/
def LindemannSin : Prop := ∀ a : ℝ, IsAlgebraic ℚ a → a ≠ 0 → Transcendental ℚ (Real.sin a)

/-- **The table's 32-paper Ermakov-Pinney seat `v'' + v = mu/v^3`: break = 1/sin^2(1), transcendental.** -/
theorem table_seat (LS : LindemannSin) :
    IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol 1 μ v v'} (1 / Real.sin 1 ^ 2) ∧ Transcendental ℚ (1 / Real.sin 1 ^ 2) := by
  have h1 : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  refine ⟨by simpa using break_exact one_pos h1, ?_⟩
  intro hB
  have hS : 0 < Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.pi_gt_three])
  have hs2 : IsAlgebraic ℚ (Real.sin 1 ^ 2) := by
    have : Real.sin 1 ^ 2 = (1 / Real.sin 1 ^ 2)⁻¹ := by field_simp
    rw [this]; exact hB.inv
  exact LS 1 isAlgebraic_one one_ne_zero (IsAlgebraic.of_pow (by norm_num) hs2)

end PinneySpring
