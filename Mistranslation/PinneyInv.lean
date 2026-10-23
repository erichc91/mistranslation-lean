import Mathlib
import Mistranslation.BratuOde
import Mistranslation.PinneySpring

/-! # Ermakov-Pinney with an INVERTED spring (2026-10-23)

Seat `v'' - w^2 v = mu / v^3`, `v(0) = v(1) = 1`, `v > 0`, any `w > 0` (w = 1 is the table seat
'+[1] -[D2*y0^3] +[y0^4]', 3 papers). Break = `(w / sinh w)^2` exactly; for algebraic w != 0 transcendental given
Hermite-Lindemann (real form). Mirror of PinneySpring with cosh in place of cos; uses BratuOde.spring_solve. -/

namespace PinneyInv

def Sol (ω μ : ℝ) (v v' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < v t ∧ HasDerivAt v (v' t) t ∧
      HasDerivAt v' (μ / v t ^ 3 + ω ^ 2 * v t) t) ∧ v 0 = 1 ∧ v 1 = 1

lemma energy {ω μ : ℝ} {v v' : ℝ → ℝ} (h : Sol ω μ v v') :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, v' t * v' t + μ * (v t * v t)⁻¹ - ω ^ 2 * (v t * v t)
      = v' 0 * v' 0 + μ * (v 0 * v 0)⁻¹ - ω ^ 2 * (v 0 * v 0) := by
  refine BratuOde.const_on (f := fun t => v' t * v' t + μ * (v t * v t)⁻¹ - ω ^ 2 * (v t * v t)) ?_
  intro s hs
  obtain ⟨hv, hd, hdd⟩ := h.1 s hs
  have hvv : v s * v s ≠ 0 := by positivity
  have := ((hdd.mul hdd).add (((hd.mul hd).inv hvv).const_mul μ)).sub ((hd.mul hd).const_mul (ω ^ 2))
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Cosh two-Wronskian solver: `z'' = k^2 z`, `z(0) = z(1) = z0`, `k > 0` gives `z(1/2) = z0 / cosh(k/2)`, `z'(1/2) = 0`. -/
lemma cosh_solve {z z' : ℝ → ℝ} {k z0 : ℝ} (hk : 0 < k)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt z (z' t) t ∧ HasDerivAt z' (k ^ 2 * z t) t)
    (h0 : z 0 = z0) (h1 : z 1 = z0) :
    z (1 / 2) = z0 / Real.cosh (k / 2) ∧ z' (1 / 2) = 0 := by
  have W1 := BratuOde.const_on (a := 0) (b := 1)
    (f := fun t => z t * (k * Real.cosh (k * (t - 1 / 2))) - z' t * Real.sinh (k * (t - 1 / 2))) (by
      intro s hs'
      obtain ⟨hz, hz'⟩ := hd s hs'
      exact ((hz.mul ((BratuOde.cosh_shift_hasDerivAt k s).const_mul k)).sub
        (hz'.mul (BratuOde.sinh_shift_hasDerivAt k s))).congr_deriv (by ring))
  have W2 := BratuOde.const_on (a := 0) (b := 1)
    (f := fun t => z t * (k * Real.sinh (k * (t - 1 / 2))) - z' t * Real.cosh (k * (t - 1 / 2))) (by
      intro s hs'
      obtain ⟨hz, hz'⟩ := hd s hs'
      exact ((hz.mul ((BratuOde.sinh_shift_hasDerivAt k s).const_mul k)).sub
        (hz'.mul (BratuOde.cosh_shift_hasDerivAt k s))).congr_deriv (by ring))
  have mem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have mem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have memh : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set A := z 0 * (k * Real.cosh (k * (0 - 1 / 2))) - z' 0 * Real.sinh (k * (0 - 1 / 2)) with hA
  set B := z 0 * (k * Real.sinh (k * (0 - 1 / 2))) - z' 0 * Real.cosh (k * (0 - 1 / 2)) with hB
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      k * z t = A * Real.cosh (k * (t - 1 / 2)) - B * Real.sinh (k * (t - 1 / 2)) ∧
      z' t = A * Real.sinh (k * (t - 1 / 2)) - B * Real.cosh (k * (t - 1 / 2)) := by
    intro t ht
    have e1 : z t * (k * Real.cosh (k * (t - 1 / 2))) - z' t * Real.sinh (k * (t - 1 / 2)) = A := W1 t ht
    have e2 : z t * (k * Real.sinh (k * (t - 1 / 2))) - z' t * Real.cosh (k * (t - 1 / 2)) = B := W2 t ht
    have hcs := Real.cosh_sq_sub_sinh_sq (k * (t - 1 / 2))
    constructor
    · rw [← e1, ← e2]; linear_combination (-(k * z t)) * hcs
    · rw [← e1, ← e2]; linear_combination (-(z' t)) * hcs
  have hS : 0 < Real.sinh (k / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hC : 0 < Real.cosh (k / 2) := Real.cosh_pos _
  have k0 := (key 0 mem0).1
  have k1 := (key 1 mem1).1
  rw [h0, show k * (0 - 1 / 2) = -(k / 2) by ring, Real.cosh_neg, Real.sinh_neg] at k0
  rw [h1, show k * (1 - 1 / 2) = k / 2 by ring] at k1
  have hB0 : B = 0 := by
    have : B * Real.sinh (k / 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with hb | hs0
    · exact hb
    · linarith
  have hAv : A = k * z0 / Real.cosh (k / 2) := by
    rw [hB0] at k1; field_simp; linarith
  obtain ⟨kh, kh'⟩ := key (1 / 2) memh
  simp only [sub_self, mul_zero, Real.cosh_zero, Real.sinh_zero, mul_one, zero_mul, sub_zero] at kh kh'
  refine ⟨?_, by rw [kh', hB0]; ring⟩
  apply mul_left_cancel₀ hk.ne'
  rw [kh, hAv]; field_simp

/-- **No push above `(w / sinh w)^2` has a solution.** -/
theorem break_le {ω μ : ℝ} {v v' : ℝ → ℝ} (hω : 0 < ω) (h : Sol ω μ v v') :
    μ ≤ ω ^ 2 / Real.sinh ω ^ 2 := by
  set E := v' 0 * v' 0 + μ * (v 0 * v 0)⁻¹ - ω ^ 2 * (v 0 * v 0) with hE
  clear_value E
  have hω2 : 0 < ω ^ 2 := by positivity
  have memh : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have sol := cosh_solve (z := fun t => v t * v t + E / (2 * ω ^ 2)) (z' := fun t => 2 * v t * v' t)
    (k := 2 * ω) (z0 := 1 + E / (2 * ω ^ 2)) (by linarith)
    (fun t ht => by
      obtain ⟨hv, hd, hdd⟩ := h.1 t ht
      have hvt : v t ≠ 0 := hv.ne'
      refine ⟨((hd.mul hd).add_const _).congr_deriv (by ring), ?_⟩
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
  have hC : 0 < Real.cosh ω := Real.cosh_pos ω
  have hS : 0 < Real.sinh ω := Real.sinh_pos_iff.mpr hω
  have hEm := energy h (1 / 2) memh
  rw [← hE, hv'0] at hEm
  set C := Real.cosh ω
  set S := Real.sinh ω
  have hCS : C ^ 2 - S ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq ω
  set s := E / (2 * ω ^ 2) with hs
  set wm := v (1 / 2) * v (1 / 2) with hwm
  have hwmpos : 0 < wm := by positivity
  have hwmC : wm * C = 1 + s - s * C := by
    have : wm = (1 + s) / C - s := by linarith
    rw [this]; field_simp
  have hEs : E = 2 * ω ^ 2 * s := by rw [hs]; field_simp
  have hmu : μ = E * wm + ω ^ 2 * wm ^ 2 := by
    field_simp at hEm
    nlinarith [hEm, hwmpos]
  have iden : ω ^ 2 * C ^ 2 - μ * S ^ 2 * C ^ 2 = ω ^ 2 * (s * S ^ 2 - 1) ^ 2 := by
    rw [hmu, hEs]
    linear_combination (-(2 * ω ^ 2 * s * S ^ 2 * C + ω ^ 2 * S ^ 2 * (wm * C + (1 + s - s * C)))) * hwmC
      + (ω ^ 2 * (1 + s ^ 2 * S ^ 2)) * hCS
  have h1 : μ * S ^ 2 * C ^ 2 ≤ ω ^ 2 * C ^ 2 := by nlinarith [iden, sq_nonneg (s * S ^ 2 - 1), hω2]
  have h2 : μ * S ^ 2 ≤ ω ^ 2 := le_of_mul_le_mul_right (by linarith) (pow_pos hC 2)
  rw [le_div_iff₀ (pow_pos hS 2)]; linarith

lemma exist_alg {ω C S c s R : ℝ} (hS : 0 < S) (hR : 0 < R) (hCS : C ^ 2 - S ^ 2 = 1) (hcs : c ^ 2 - s ^ 2 = 1)
    (hRW : R ^ 2 = C / S ^ 2 * c - 1 / S ^ 2) :
    (C / S ^ 2 * (2 * ω * (2 * ω * c)) * (2 * R) - C / S ^ 2 * (2 * ω * s) * (2 * (C / S ^ 2 * (2 * ω * s) / (2 * R))))
        / (2 * R) ^ 2
      = ω ^ 2 / S ^ 2 / R ^ 3 + ω ^ 2 * R := by
  have hSR : S ^ 2 * R ^ 2 = C * c - 1 := by rw [hRW]; field_simp
  rw [div_eq_iff (by positivity)]
  field_simp
  linear_combination (2 * C * ω ^ 2 * c - ω ^ 2 * (S ^ 2 * R ^ 2 + (C * c - 1))) * hSR + (ω ^ 2 * C ^ 2) * hcs + ω ^ 2 * hCS

theorem exists_top {ω : ℝ} (hω : 0 < ω) :
    Sol ω (ω ^ 2 / Real.sinh ω ^ 2)
      (fun t => Real.sqrt (Real.cosh ω / Real.sinh ω ^ 2 * Real.cosh (2 * ω * (t - 1 / 2)) - 1 / Real.sinh ω ^ 2))
      (fun t => Real.cosh ω / Real.sinh ω ^ 2 * (2 * ω * Real.sinh (2 * ω * (t - 1 / 2))) /
        (2 * Real.sqrt (Real.cosh ω / Real.sinh ω ^ 2 * Real.cosh (2 * ω * (t - 1 / 2)) - 1 / Real.sinh ω ^ 2))) := by
  have hS : 0 < Real.sinh ω := Real.sinh_pos_iff.mpr hω
  have hC1 : 1 < Real.cosh ω := Real.one_lt_cosh.mpr hω.ne'
  have hCS := Real.cosh_sq_sub_sinh_sq ω
  set C := Real.cosh ω
  set S := Real.sinh ω
  have hwpos : ∀ t : ℝ, 0 < C / S ^ 2 * Real.cosh (2 * ω * (t - 1 / 2)) - 1 / S ^ 2 := by
    intro t
    have hc1 := Real.one_le_cosh (2 * ω * (t - 1 / 2))
    have : C / S ^ 2 ≤ C / S ^ 2 * Real.cosh (2 * ω * (t - 1 / 2)) := by
      have : 0 ≤ C / S ^ 2 := by positivity
      nlinarith
    have : 1 / S ^ 2 < C / S ^ 2 := div_lt_div_of_pos_right hC1 (by positivity)
    linarith
  have hw : ∀ t, HasDerivAt (fun t => C / S ^ 2 * Real.cosh (2 * ω * (t - 1 / 2)) - 1 / S ^ 2)
      (C / S ^ 2 * (2 * ω * Real.sinh (2 * ω * (t - 1 / 2)))) t :=
    fun t => ((BratuOde.cosh_shift_hasDerivAt (2 * ω) t).const_mul (C / S ^ 2)).sub_const _
  have hw' : ∀ t, HasDerivAt (fun t => C / S ^ 2 * (2 * ω * Real.sinh (2 * ω * (t - 1 / 2))))
      (C / S ^ 2 * (2 * ω * (2 * ω * Real.cosh (2 * ω * (t - 1 / 2))))) t :=
    fun t => (((BratuOde.sinh_shift_hasDerivAt (2 * ω) t).const_mul (2 * ω)).const_mul (C / S ^ 2))
  refine ⟨fun t _ => ⟨Real.sqrt_pos.mpr (hwpos t), ?_, ?_⟩, ?_, ?_⟩
  · exact ((hw t).sqrt (hwpos t).ne').congr_deriv rfl
  · have hR := Real.sqrt_pos.mpr (hwpos t)
    have hsq := (hw t).sqrt (hwpos t).ne'
    refine ((hw' t).div (hsq.const_mul 2) (by positivity)).congr_deriv ?_
    have hRW := Real.sq_sqrt (hwpos t).le
    have hcs := Real.cosh_sq_sub_sinh_sq (2 * ω * (t - 1 / 2))
    exact exist_alg hS hR hCS hcs (by rw [hRW])
  · beta_reduce
    rw [show 2 * ω * (0 - 1 / 2) = -ω by ring, Real.cosh_neg]
    rw [show C / S ^ 2 * C - 1 / S ^ 2 = 1 by field_simp; linarith, Real.sqrt_one]
  · beta_reduce
    rw [show 2 * ω * (1 - 1 / 2) = ω by ring]
    rw [show C / S ^ 2 * C - 1 / S ^ 2 = 1 by field_simp; linarith, Real.sqrt_one]

/-- **Ermakov-Pinney with an inverted spring: the break is exactly `(w / sinh w)^2`**, for every w > 0. -/
theorem break_exact {ω : ℝ} (hω : 0 < ω) :
    IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol ω μ v v'} (ω ^ 2 / Real.sinh ω ^ 2) :=
  ⟨⟨_, _, exists_top hω⟩, fun _ ⟨_, _, h⟩ => break_le hω h⟩

/-- **For every algebraic w > 0 the break is transcendental** (given Hermite-Lindemann). w = 1 is the table seat. -/
theorem break_transcendental (HL : Breaks.HermiteLindemann) {ω : ℝ} (hω : 0 < ω) (hωA : IsAlgebraic ℚ ω) :
    Transcendental ℚ (ω ^ 2 / Real.sinh ω ^ 2) := by
  intro hB
  have hS : 0 < Real.sinh ω := Real.sinh_pos_iff.mpr hω
  have hs2 : IsAlgebraic ℚ (Real.sinh ω ^ 2) := by
    have : Real.sinh ω ^ 2 = ω ^ 2 * (ω ^ 2 / Real.sinh ω ^ 2)⁻¹ := by field_simp
    rw [this]; exact (hωA.pow 2).mul hB.inv
  have hsA : IsAlgebraic ℚ (Real.sinh ω) := IsAlgebraic.of_pow (by norm_num) hs2
  have hcA : IsAlgebraic ℚ (Real.cosh ω) :=
    IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [Real.cosh_sq]; exact hs2.add isAlgebraic_one)
  exact HL ω hωA hω.ne' (by rw [← Real.cosh_add_sinh]; exact hcA.add hsA)

end PinneyInv
