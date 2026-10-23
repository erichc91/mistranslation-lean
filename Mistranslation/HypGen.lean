import Mathlib
import Mistranslation.HypOde

/-! # The predicted seat for EVERY boundary value b > 1 (2026-10-23)

`v'' = mu cosh v / sinh^3 v`, `cosh v = b` at both ends, `v > 0`. For every b > 1 the largest solvable push exists and
is attained; for every ALGEBRAIC b > 1 it is transcendental (given Hermite-Lindemann). One theorem, infinitely many
new transcendental numbers (b = 2 is HypOde: 3.1666712). Same route as HypOde with 2 replaced by b. -/

namespace HypGen

def Sol (b μ : ℝ) (v v' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < v t ∧ HasDerivAt v (v' t) t ∧
      HasDerivAt v' (μ * Real.cosh (v t) / Real.sinh (v t) ^ 3) t) ∧
    Real.cosh (v 0) = b ∧ Real.cosh (v 1) = b

lemma energy {b μ : ℝ} {v v' : ℝ → ℝ} (h : Sol b μ v v') :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, v' t * v' t + μ * (Real.sinh (v t) ^ 2)⁻¹
      = v' 0 * v' 0 + μ * (Real.sinh (v 0) ^ 2)⁻¹ := by
  refine BratuOde.const_on (f := fun t => v' t * v' t + μ * (Real.sinh (v t) ^ 2)⁻¹) ?_
  intro s hs
  obtain ⟨hv, hd, hdd⟩ := h.1 s hs
  have hsh : Real.sinh (v s) ≠ 0 := (Real.sinh_pos_iff.mpr hv).ne'
  have := (hdd.mul hdd).add ((((Real.hasDerivAt_sinh (v s)).comp s hd).pow 2).inv (pow_ne_zero 2 hsh) |>.const_mul μ)
  refine this.congr_deriv ?_
  simp only [Function.comp, Pi.pow_apply]
  field_simp
  ring

lemma straighten {b μ : ℝ} {v v' : ℝ → ℝ} (h : Sol b μ v v') (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => Real.cosh (v s)) (Real.sinh (v t) * v' t) t ∧
    HasDerivAt (fun s => Real.sinh (v s) * v' s)
      ((v' 0 * v' 0 + μ * (Real.sinh (v 0) ^ 2)⁻¹) * Real.cosh (v t)) t := by
  obtain ⟨hv, hd, hdd⟩ := h.1 t ht
  have hsh : Real.sinh (v t) ≠ 0 := (Real.sinh_pos_iff.mpr hv).ne'
  refine ⟨((Real.hasDerivAt_cosh (v t)).comp t hd).congr_deriv (by ring), ?_⟩
  refine (((Real.hasDerivAt_sinh (v t)).comp t hd).mul hdd).congr_deriv ?_
  rw [← energy h t ht]
  simp only [Function.comp]
  field_simp

theorem mu_formula {b μ : ℝ} {v v' : ℝ → ℝ} (hb : 0 < b) (h : Sol b μ v v') (hμ : 0 < μ) :
    ∃ c : ℝ, 0 < c ∧ μ = c ^ 2 * (b ^ 2 / Real.cosh (c / 2) ^ 2 - 1) := by
  set E := v' 0 * v' 0 + μ * (Real.sinh (v 0) ^ 2)⁻¹ with hE
  have hv0 := (h.1 0 ⟨le_rfl, zero_le_one⟩).1
  have hEpos : 0 < E := by
    have : 0 < μ * (Real.sinh (v 0) ^ 2)⁻¹ := by
      have := Real.sinh_pos_iff.mpr hv0; positivity
    nlinarith [mul_self_nonneg (v' 0)]
  set c := Real.sqrt E with hc
  have hcpos : 0 < c := Real.sqrt_pos.mpr hEpos
  have hc2 : c ^ 2 = E := Real.sq_sqrt hEpos.le
  have hmid : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have sol := BratuOde.spring_solve (u := fun s => Real.cosh (v s) / b) (u' := fun s => Real.sinh (v s) * v' s / b)
    hcpos (fun t ht => by
      obtain ⟨h1, h2⟩ := straighten h t ht
      exact ⟨h1.div_const b, (h2.div_const b).congr_deriv (by rw [hc2]; ring)⟩)
    (by simp [h.2.1, hb.ne']) (by simp [h.2.2, hb.ne']) (1 / 2) hmid
  simp only [sub_self, mul_zero, Real.cosh_zero, Real.sinh_zero, zero_div] at sol
  obtain ⟨hu, hu'⟩ := sol
  have hvm := (h.1 (1 / 2) hmid).1
  have hshm : 0 < Real.sinh (v (1 / 2)) := Real.sinh_pos_iff.mpr hvm
  have hv'0 : v' (1 / 2) = 0 := by
    have : Real.sinh (v (1 / 2)) * v' (1 / 2) = 0 := by
      field_simp at hu'; linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact h0
  have hC := Real.cosh_pos (c / 2)
  have hcm : Real.cosh (v (1 / 2)) = b / Real.cosh (c / 2) := by
    field_simp at hu ⊢; linarith
  have hEm := energy h (1 / 2) hmid
  rw [hv'0] at hEm
  have hsq : Real.sinh (v (1 / 2)) ^ 2 = b ^ 2 / Real.cosh (c / 2) ^ 2 - 1 := by
    have := Real.cosh_sq (v (1 / 2)); rw [hcm, div_pow] at this; linarith
  refine ⟨c, hcpos, ?_⟩
  rw [← hsq, hc2]
  rw [← hE] at hEm
  field_simp at hEm ⊢
  linarith

noncomputable def f (b c : ℝ) : ℝ := c ^ 2 * (b ^ 2 / Real.cosh (c / 2) ^ 2 - 1)

lemma alg {b c W Z C S : ℝ} (hC : 0 < C) (hS : 0 < S) (hWZ : W ^ 2 - Z ^ 2 = 1)
    (hs2 : S ^ 2 = (b * W / C) ^ 2 - 1) :
    ((b * (c * (c * W)) / C) * S - b * (c * Z) / C * (2 * (b * W / C) * (b * (c * Z) / C) / (2 * S))) / S ^ 2
      = c ^ 2 * (b ^ 2 / C ^ 2 - 1) * (b * W / C) / S ^ 3 := by
  have key : c ^ 2 * S ^ 2 - (b * (c * Z) / C) ^ 2 = c ^ 2 * (b ^ 2 / C ^ 2 - 1) := by
    rw [hs2]; field_simp
    linear_combination (b ^ 2 * c ^ 2) * hWZ
  have e : ((b * (c * (c * W)) / C) * S - b * (c * Z) / C * (2 * (b * W / C) * (b * (c * Z) / C) / (2 * S))) / S ^ 2
      = (b * W / C) * (c ^ 2 * S ^ 2 - (b * (c * Z) / C) ^ 2) / S ^ 3 := by
    field_simp
  rw [e, key]; ring

theorem exists_sol {b c : ℝ} (hc : 0 < c) (hC2 : Real.cosh (c / 2) < b) :
    Sol b (f b c) (fun t => Real.arcosh (b * Real.cosh (c * (t - 1 / 2)) / Real.cosh (c / 2)))
      (fun t => (b * (c * Real.sinh (c * (t - 1 / 2))) / Real.cosh (c / 2)) /
        Real.sqrt ((b * Real.cosh (c * (t - 1 / 2)) / Real.cosh (c / 2)) ^ 2 - 1)) := by
  have hC := Real.cosh_pos (c / 2)
  have hb : 0 < b := by linarith
  have hU : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 < b * Real.cosh (c * (t - 1 / 2)) / Real.cosh (c / 2) := by
    intro t _
    rw [lt_div_iff₀ hC]
    have := Real.one_le_cosh (c * (t - 1 / 2))
    nlinarith
  refine ⟨fun t ht => ⟨Real.arcosh_pos (hU t ht), ?_, ?_⟩, ?_, ?_⟩
  · have hUd := ((BratuOde.cosh_shift_hasDerivAt c t).const_mul b).div_const (Real.cosh (c / 2))
    have h := (Real.hasDerivAt_arcosh (hU t ht)).comp t hUd
    exact h.congr_deriv (by ring)
  · have hU1 := hU t ht
    have hq : 0 < (b * Real.cosh (c * (t - 1 / 2)) / Real.cosh (c / 2)) ^ 2 - 1 := by nlinarith
    have hUd := ((BratuOde.cosh_shift_hasDerivAt c t).const_mul b).div_const (Real.cosh (c / 2))
    have hUd' := (((BratuOde.sinh_shift_hasDerivAt c t).const_mul c).const_mul b).div_const (Real.cosh (c / 2))
    have hsq := ((hUd.pow 2).sub_const 1).sqrt hq.ne'
    have hS := Real.sqrt_pos.mpr hq
    refine (hUd'.div hsq hS.ne').congr_deriv ?_
    rw [Real.cosh_arcosh hU1.le, Real.sinh_arcosh hU1.le]
    simp only [f, Pi.pow_apply]
    have hs2 := Real.sq_sqrt hq.le
    have hWZ := Real.cosh_sq_sub_sinh_sq (c * (t - 1 / 2))
    norm_num
    generalize Real.sqrt ((b * Real.cosh (c * (t - 1 / 2)) / Real.cosh (c / 2)) ^ 2 - 1) = S at hs2 hS ⊢
    generalize Real.cosh (c * (t - 1 / 2)) = W at hs2 hWZ ⊢
    generalize Real.sinh (c * (t - 1 / 2)) = Z at hWZ ⊢
    generalize Real.cosh (c / 2) = C at hs2 hC ⊢
    convert alg hC hS hWZ hs2 using 1
  · beta_reduce
    rw [Real.cosh_arcosh (hU 0 ⟨le_rfl, zero_le_one⟩).le, show c * (0 - 1 / 2) = -(c / 2) by ring, Real.cosh_neg]
    field_simp
  · beta_reduce
    rw [Real.cosh_arcosh (hU 1 ⟨zero_le_one, le_rfl⟩).le, show c * (1 - 1 / 2) = c / 2 by ring]
    field_simp

lemma f_cont (b : ℝ) : Continuous (f b) := by
  unfold f
  exact (continuous_pow 2).mul ((continuous_const.div ((Real.continuous_cosh.comp
    (continuous_id.div_const 2)).pow 2) (fun x => (pow_pos (Real.cosh_pos _) 2).ne')).sub continuous_const)

lemma f_pos {b c : ℝ} (hc : 0 < c) (hC2 : Real.cosh (c / 2) < b) : 0 < f b c := by
  unfold f
  have hC := Real.cosh_pos (c / 2)
  have : 1 < b ^ 2 / Real.cosh (c / 2) ^ 2 := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  have := pow_pos hc 2
  nlinarith

lemma cosh_lt_of_pos {b μ c : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hc : 0 < c)
    (h : μ = c ^ 2 * (b ^ 2 / Real.cosh (c / 2) ^ 2 - 1)) : Real.cosh (c / 2) < b := by
  have hC := Real.cosh_pos (c / 2)
  have h4 : 1 < b ^ 2 / Real.cosh (c / 2) ^ 2 := by
    by_contra hle; push_neg at hle
    have : c ^ 2 * (b ^ 2 / Real.cosh (c / 2) ^ 2 - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  rw [lt_div_iff₀ (by positivity)] at h4
  nlinarith

lemma f_hasDerivAt (b c : ℝ) : HasDerivAt (f b)
    (2 * c * (b ^ 2 / Real.cosh (c / 2) ^ 2 - 1) - b ^ 2 * c ^ 2 * Real.sinh (c / 2) / Real.cosh (c / 2) ^ 3) c := by
  have hC := (Real.cosh_pos (c / 2)).ne'
  have hch : HasDerivAt (fun c => Real.cosh (c / 2)) (Real.sinh (c / 2) * (1 / 2)) c := by
    have h := (Real.hasDerivAt_cosh (c / 2)).comp c ((hasDerivAt_id' c).div_const 2)
    exact h.congr_deriv (by ring)
  have h := (hasDerivAt_pow 2 c).mul (((hasDerivAt_const c (b ^ 2)).div (hch.pow 2) (pow_ne_zero 2 hC)).sub_const 1)
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.div_apply]
  field_simp
  ring

/-- **For every algebraic b > 1, the predicted seat's break exists, is attained, and is transcendental** (given HL). -/
theorem break_end_to_end (HL : Breaks.HermiteLindemann) {b : ℝ} (hb1 : 1 < b) (hbA : IsAlgebraic ℚ b) :
    ∃ B : ℝ, IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol b μ v v'} B ∧ Transcendental ℚ B := by
  have hb : 0 < b := by linarith
  set L := 2 * Real.arcosh b
  have hcoshL : Real.cosh (L / 2) = b := by
    rw [show L / 2 = Real.arcosh b by ring]; exact Real.cosh_arcosh hb1.le
  have hL : 0 < L := by have := Real.arcosh_pos hb1; linarith
  obtain ⟨cs, hcs, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc 0 L)).exists_isMaxOn
    ⟨0, le_rfl, hL.le⟩ (f_cont b).continuousOn
  have hmid : 0 < f b (L / 2) := by
    apply f_pos (by linarith)
    have := Real.cosh_lt_cosh.mpr (show |L / 2 / 2| < |L / 2| by
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith)
    rw [hcoshL] at this; exact this
  have hfcs : 0 < f b cs := lt_of_lt_of_le hmid (hmax ⟨by linarith, by linarith⟩)
  have hcs0 : 0 < cs := by
    rcases eq_or_lt_of_le hcs.1 with h0 | h0
    · rw [← h0] at hfcs; simp [f] at hfcs
    · exact h0
  have hcsL : Real.cosh (cs / 2) < b := cosh_lt_of_pos hb hfcs hcs0 rfl
  have hcsltL : cs < L := by
    have : Real.cosh (cs / 2) < Real.cosh (L / 2) := by rw [hcoshL]; exact hcsL
    rw [Real.cosh_lt_cosh, abs_of_pos (by linarith), abs_of_pos (by linarith)] at this
    linarith
  have hG : IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol b μ v v'} (f b cs) := by
    refine ⟨⟨_, _, exists_sol hcs0 hcsL⟩, ?_⟩
    rintro μ ⟨v, v', h⟩
    rcases le_or_gt μ 0 with hμ | hμ
    · linarith
    obtain ⟨c, hc, hμc⟩ := mu_formula hb h hμ
    have hcC := cosh_lt_of_pos hb hμ hc hμc
    have hcL : c ≤ L := by
      have : Real.cosh (c / 2) < Real.cosh (L / 2) := by rw [hcoshL]; exact hcC
      rw [Real.cosh_lt_cosh, abs_of_pos (by linarith), abs_of_pos (by linarith)] at this
      linarith
    rw [hμc]; exact hmax ⟨hc.le, hcL⟩
  refine ⟨f b cs, hG, ?_⟩
  have hloc : IsLocalMax (f b) cs := hmax.isLocalMax (Icc_mem_nhds hcs0 hcsltL)
  have hcrit := hloc.hasDerivAt_eq_zero (f_hasDerivAt b cs)
  intro hB
  set C := Real.cosh (cs / 2) with hCdef
  set Sh := Real.sinh (cs / 2) with hShdef
  have hC : 0 < C := Real.cosh_pos _
  have hSh : 0 < Sh := Real.sinh_pos_iff.mpr (by linarith)
  have hsh : Sh ^ 2 = C ^ 2 - 1 := by have := Real.cosh_sq (cs / 2); linarith
  have hlin : 2 * (b ^ 2 - C ^ 2) * C = cs * b ^ 2 * Sh := by
    field_simp at hcrit
    nlinarith [hcrit, hcs0, hC]
  set B := f b cs with hBdef
  have e2 : B * C ^ 2 = cs ^ 2 * (b ^ 2 - C ^ 2) := by simp only [hBdef, f, ← hCdef]; field_simp
  have e1 : 4 * (b ^ 2 - C ^ 2) ^ 2 * C ^ 2 = cs ^ 2 * b ^ 4 * Sh ^ 2 := by
    rw [show 4 * (b ^ 2 - C ^ 2) ^ 2 * C ^ 2 = (2 * (b ^ 2 - C ^ 2) * C) ^ 2 by ring, hlin]; ring
  have rel : 4 * (b ^ 2 - C ^ 2) ^ 3 = B * b ^ 4 * (C ^ 2 - 1) := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hC.ne')
    linear_combination (b ^ 2 - C ^ 2) * e1 - b ^ 4 * Sh ^ 2 * e2 + B * b ^ 4 * C ^ 2 * hsh
  have hX : (C ^ 2) ^ 3 + (-(3 * b ^ 2)) * (C ^ 2) ^ 2 + (3 * b ^ 4 + B * b ^ 4 * 4⁻¹) * C ^ 2
      + (-(b ^ 6 + B * b ^ 4 * 4⁻¹)) = 0 := by
    linear_combination (-1 / 4 : ℝ) * rel
  have q3 : IsAlgebraic ℚ (3 : ℝ) := by simpa using HypOde.qa 3
  have q4 : IsAlgebraic ℚ (4 : ℝ) := by simpa using HypOde.qa 4
  have hX2 : IsAlgebraic ℚ (C ^ 2) := HypOde.cubic_root_algebraic
    (q3.mul (hbA.pow 2)).neg
    ((q3.mul (hbA.pow 4)).add ((hB.mul (hbA.pow 4)).mul q4.inv))
    (((hbA.pow 6).add ((hB.mul (hbA.pow 4)).mul q4.inv)).neg) hX
  have hCa : IsAlgebraic ℚ C := IsAlgebraic.of_pow (by norm_num) hX2
  have hSa : IsAlgebraic ℚ Sh := IsAlgebraic.of_pow (n := 2) (by norm_num)
    (by rw [hsh]; exact hX2.sub isAlgebraic_one)
  have hcsa : IsAlgebraic ℚ (cs / 2) := by
    have : cs / 2 = (b ^ 2 - C ^ 2) * C * (b ^ 2 * Sh)⁻¹ := by field_simp; linarith
    rw [this]
    exact (((hbA.pow 2).sub (hCa.pow 2)).mul hCa).mul ((hbA.pow 2).mul hSa).inv
  have hexp : IsAlgebraic ℚ (Real.exp (cs / 2)) := by
    rw [← Real.cosh_add_sinh]; exact hCa.add hSa
  exact HL (cs / 2) hcsa (by positivity) hexp

end HypGen
