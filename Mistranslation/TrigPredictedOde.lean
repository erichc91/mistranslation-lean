import Mathlib
import Mistranslation.TrigPredicted
import Mistranslation.LindemannBridge

/-! # The circle twin of the predicted family, from the ODE (2026-10-23)

Seat `v'' = mu cos v / sin^3 v`, `cos v = b` at both ends (`0 < b < 1`), on the one-signed side `0 < v < pi/2`
(there `cos v > 0`, so the push keeps one direction, exactly as `cosh v / sinh^3 v > 0` does in `HypGen`).
`u = cos v` obeys the plain spring `u'' = -w^2 u`, `w^2 = v'^2 + mu / sin^2 v`; a Sturm comparison with `sin(pi t)`
forces `w < pi`, the trig two-Wronskian solver pins `u`, and every solution's push is
`mu(w) = w^2 (1 - b^2 / cos^2(w/2))`. Every `0 < w < pi` with `cos(w/2) > b` is realised by an explicit solution,
so the break is the top of `mu(w)`; `TrigPredicted.break_transcendental` with the proved Lindemann-for-sine closes it.

Why the side `v < pi/2`: on the whole strip `0 < v < pi` the higher spring branches `w` in `(pi, 3 pi), ...` are also
solutions (u changes sign), with pushes `w^2 (1 - b^2/cos^2(w/2))` near `4 pi^2 k^2 (1 - b^2)` -- unbounded, so no break.
The break of the docs (b = 1/2: 1.2449767) is the top of the first branch, which is exactly the `v < pi/2` seat.
Template: `HypGen.lean` (hyperbolic twin). -/

namespace TrigPredictedOde

def Sol (b μ : ℝ) (v v' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < v t ∧ v t < Real.pi / 2 ∧ HasDerivAt v (v' t) t ∧
      HasDerivAt v' (μ * Real.cos (v t) / Real.sin (v t) ^ 3) t) ∧
    Real.cos (v 0) = b ∧ Real.cos (v 1) = b

lemma sin_pos_of {x : ℝ} (h0 : 0 < x) (h1 : x < Real.pi / 2) : 0 < Real.sin x :=
  Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])

lemma cos_pos_of {x : ℝ} (h0 : 0 < x) (h1 : x < Real.pi / 2) : 0 < Real.cos x :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩

lemma energy {b μ : ℝ} {v v' : ℝ → ℝ} (h : Sol b μ v v') :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, v' t * v' t + μ * (Real.sin (v t) ^ 2)⁻¹
      = v' 0 * v' 0 + μ * (Real.sin (v 0) ^ 2)⁻¹ := by
  refine BratuOde.const_on (f := fun t => v' t * v' t + μ * (Real.sin (v t) ^ 2)⁻¹) ?_
  intro s hs
  obtain ⟨hv, hv2, hd, hdd⟩ := h.1 s hs
  have hsn : Real.sin (v s) ≠ 0 := (sin_pos_of hv hv2).ne'
  have := (hdd.mul hdd).add ((((Real.hasDerivAt_sin (v s)).comp s hd).pow 2).inv (pow_ne_zero 2 hsn) |>.const_mul μ)
  refine this.congr_deriv ?_
  simp only [Function.comp, Pi.pow_apply]
  field_simp
  ring

lemma straighten {b μ : ℝ} {v v' : ℝ → ℝ} (h : Sol b μ v v') (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => Real.cos (v s)) (-(Real.sin (v t) * v' t)) t ∧
    HasDerivAt (fun s => -(Real.sin (v s) * v' s))
      (-((v' 0 * v' 0 + μ * (Real.sin (v 0) ^ 2)⁻¹) * Real.cos (v t))) t := by
  obtain ⟨hv, hv2, hd, hdd⟩ := h.1 t ht
  have hsn : Real.sin (v t) ≠ 0 := (sin_pos_of hv hv2).ne'
  refine ⟨((Real.hasDerivAt_cos (v t)).comp t hd).congr_deriv (by ring), ?_⟩
  refine ((((Real.hasDerivAt_sin (v t)).comp t hd).mul hdd).neg).congr_deriv ?_
  rw [← energy h t ht]
  simp only [Function.comp]
  field_simp

/-- **Sturm comparison with `sin(pi t)`**: a spring `u'' = -k^2 u` that stays positive on [0, 1] with equal positive
ends has `k^2 < pi^2`. -/
lemma sturm {u u' : ℝ → ℝ} {k b : ℝ} (hb : 0 < b)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (u' t) t ∧ HasDerivAt u' (-(k ^ 2) * u t) t)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < u t) (h0 : u 0 = b) (h1 : u 1 = b) : k ^ 2 < Real.pi ^ 2 := by
  by_contra hk
  push_neg at hk
  have hc : ∀ t, HasDerivAt (fun t => Real.cos (Real.pi * t)) (-(Real.pi * Real.sin (Real.pi * t))) t := by
    intro t
    have h := (Real.hasDerivAt_cos (Real.pi * t)).comp t ((hasDerivAt_id' t).const_mul Real.pi)
    exact h.congr_deriv (by ring)
  have hs : ∀ t, HasDerivAt (fun t => Real.sin (Real.pi * t)) (Real.pi * Real.cos (Real.pi * t)) t := by
    intro t
    have h := (Real.hasDerivAt_sin (Real.pi * t)).comp t ((hasDerivAt_id' t).const_mul Real.pi)
    exact h.congr_deriv (by ring)
  obtain ⟨c, hc01, hsl⟩ := exists_hasDerivAt_eq_slope
    (fun t => u t * (Real.pi * Real.cos (Real.pi * t)) - u' t * Real.sin (Real.pi * t))
    (fun t => (k ^ 2 - Real.pi ^ 2) * u t * Real.sin (Real.pi * t)) (zero_lt_one' ℝ)
    (fun t ht => by
      obtain ⟨hu, hu'⟩ := hd t ht
      exact ((hu.mul ((hc t).const_mul Real.pi)).sub (hu'.mul (hs t))).continuousAt.continuousWithinAt)
    (fun t ht => by
      obtain ⟨hu, hu'⟩ := hd t (Set.Ioo_subset_Icc_self ht)
      exact ((hu.mul ((hc t).const_mul Real.pi)).sub (hu'.mul (hs t))).congr_deriv (by ring))
  have hsc : 0 < Real.sin (Real.pi * c) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, hc01.1]) (by nlinarith [Real.pi_pos, hc01.2])
  have huc := hpos c (Set.Ioo_subset_Icc_self hc01)
  have hW : 0 ≤ (k ^ 2 - Real.pi ^ 2) * u c * Real.sin (Real.pi * c) := by
    have : 0 ≤ k ^ 2 - Real.pi ^ 2 := by linarith
    positivity
  rw [hsl] at hW
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_one, Real.cos_pi, Real.sin_pi, h0, h1] at hW
  have := Real.pi_pos
  nlinarith

/-- **Every solution sits on the circle curve** `mu = w^2 (1 - b^2 / cos^2(w/2))`, `0 < w < pi`. -/
theorem mu_formula {b μ : ℝ} {v v' : ℝ → ℝ} (hb : 0 < b) (h : Sol b μ v v') (hμ : 0 < μ) :
    ∃ w : ℝ, 0 < w ∧ w < Real.pi ∧ μ = w ^ 2 * (1 - b ^ 2 / Real.cos (w / 2) ^ 2) := by
  set E := v' 0 * v' 0 + μ * (Real.sin (v 0) ^ 2)⁻¹ with hE
  have hv0 := h.1 0 ⟨le_rfl, zero_le_one⟩
  have hEpos : 0 < E := by
    have : 0 < μ * (Real.sin (v 0) ^ 2)⁻¹ := by
      have := sin_pos_of hv0.1 hv0.2.1; positivity
    nlinarith [mul_self_nonneg (v' 0)]
  set w := Real.sqrt E with hw
  have hwpos : 0 < w := Real.sqrt_pos.mpr hEpos
  have hw2 : w ^ 2 = E := Real.sq_sqrt hEpos.le
  have hdu : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun s => Real.cos (v s)) (-(Real.sin (v t) * v' t)) t ∧
      HasDerivAt (fun s => -(Real.sin (v s) * v' s)) (-(w ^ 2) * Real.cos (v t)) t := fun t ht => by
    obtain ⟨h1, h2⟩ := straighten h t ht
    exact ⟨h1, h2.congr_deriv (by rw [hw2]; ring)⟩
  have hk := sturm (u := fun s => Real.cos (v s)) hb hdu
    (fun t ht => cos_pos_of (h.1 t ht).1 (h.1 t ht).2.1) h.2.1 h.2.2
  have hwpi : w < Real.pi := by nlinarith [Real.pi_pos]
  have sol := PinneySpring.trig_solve (z := fun s => Real.cos (v s)) (z' := fun s => -(Real.sin (v s) * v' s))
    hwpos hwpi hdu h.2.1 h.2.2
  obtain ⟨hu, hu'⟩ := sol
  have hmid : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hvm := h.1 (1 / 2) hmid
  have hsm : 0 < Real.sin (v (1 / 2)) := sin_pos_of hvm.1 hvm.2.1
  have hv'0 : v' (1 / 2) = 0 := by
    have : Real.sin (v (1 / 2)) * v' (1 / 2) = 0 := by simpa using hu'
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact h0
  have hC : 0 < Real.cos (w / 2) := cos_pos_of (by linarith) (by linarith)
  have hEm := energy h (1 / 2) hmid
  rw [hv'0, ← hE] at hEm
  have hsq : Real.sin (v (1 / 2)) ^ 2 = 1 - b ^ 2 / Real.cos (w / 2) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (v (1 / 2))
    rw [hu, div_pow] at this; linarith
  refine ⟨w, hwpos, hwpi, ?_⟩
  have hEm' : μ = E * Real.sin (v (1 / 2)) ^ 2 := by rw [← hEm]; field_simp; ring
  rw [← hsq, hw2]; exact hEm'

/-! Existence: every `0 < w < pi` with `cos(w/2) > b` is a solution. -/

noncomputable def f (b w : ℝ) : ℝ := w ^ 2 * (1 - b ^ 2 / Real.cos (w / 2) ^ 2)

lemma cos_ge_half {w x : ℝ} (hwpi : w < Real.pi) (hx : |x| ≤ w / 2) : Real.cos (w / 2) ≤ Real.cos x := by
  have := abs_nonneg x
  rw [← Real.cos_abs x]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith) hx

theorem exists_sol {b w : ℝ} (hb : 0 < b) (hw : 0 < w) (hwpi : w < Real.pi) (hgap : b < Real.cos (w / 2)) :
    Sol b (f b w) (fun t => Real.arccos (b * Real.cos (w * (t - 1 / 2)) / Real.cos (w / 2)))
      (fun t => (b * (w * Real.sin (w * (t - 1 / 2))) / Real.cos (w / 2)) /
        Real.sqrt (1 - (b * Real.cos (w * (t - 1 / 2)) / Real.cos (w / 2)) ^ 2)) := by
  have hC : 0 < Real.cos (w / 2) := by linarith
  have hU : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < b * Real.cos (w * (t - 1 / 2)) / Real.cos (w / 2) ∧
      b * Real.cos (w * (t - 1 / 2)) / Real.cos (w / 2) < 1 := by
    intro t ht
    have hx : |w * (t - 1 / 2)| ≤ w / 2 := by
      rw [abs_mul, abs_of_pos hw]
      have : |t - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      nlinarith
    have h1 := cos_ge_half hwpi hx
    have h2 := Real.cos_le_one (w * (t - 1 / 2))
    constructor
    · have : 0 < Real.cos (w * (t - 1 / 2)) := by linarith
      positivity
    · rw [div_lt_one hC]; nlinarith
  have hcs : ∀ t, HasDerivAt (fun t => Real.cos (w * (t - 1 / 2))) (-(w * Real.sin (w * (t - 1 / 2)))) t := by
    intro t
    have h := (Real.hasDerivAt_cos (w * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul w)
    exact h.congr_deriv (by ring)
  have hsn : ∀ t, HasDerivAt (fun t => Real.sin (w * (t - 1 / 2))) (w * Real.cos (w * (t - 1 / 2))) t := by
    intro t
    have h := (Real.hasDerivAt_sin (w * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul w)
    exact h.congr_deriv (by ring)
  refine ⟨fun t ht => ⟨Real.arccos_pos.mpr (hU t ht).2, Real.arccos_lt_pi_div_two.mpr (hU t ht).1, ?_, ?_⟩, ?_, ?_⟩
  · have hUd := ((hcs t).const_mul b).div_const (Real.cos (w / 2))
    have h := (Real.hasDerivAt_arccos (by linarith [(hU t ht).1]) (hU t ht).2.ne).comp t hUd
    refine h.congr_deriv ?_
    have hq : 0 < 1 - (b * Real.cos (w * (t - 1 / 2)) / Real.cos (w / 2)) ^ 2 := by
      have := (hU t ht).1; have := (hU t ht).2; nlinarith
    have hS := Real.sqrt_pos.mpr hq
    field_simp
  · obtain ⟨hU0, hU1⟩ := hU t ht
    have hq : 0 < 1 - (b * Real.cos (w * (t - 1 / 2)) / Real.cos (w / 2)) ^ 2 := by nlinarith
    have hUd := ((hcs t).const_mul b).div_const (Real.cos (w / 2))
    have hNd := (((hsn t).const_mul w).const_mul b).div_const (Real.cos (w / 2))
    have hsq := ((hUd.pow 2).const_sub 1).sqrt hq.ne'
    have hS := Real.sqrt_pos.mpr hq
    refine (hNd.div hsq hS.ne').congr_deriv ?_
    rw [Real.cos_arccos (by linarith) hU1.le, Real.sin_arccos]
    simp only [f, Pi.pow_apply]
    have hs2 := Real.sq_sqrt hq.le
    have hWZ := Real.sin_sq_add_cos_sq (w * (t - 1 / 2))
    norm_num
    generalize Real.sqrt (1 - (b * Real.cos (w * (t - 1 / 2)) / Real.cos (w / 2)) ^ 2) = S at hs2 hS ⊢
    generalize Real.cos (w * (t - 1 / 2)) = W at hs2 hWZ ⊢
    generalize Real.sin (w * (t - 1 / 2)) = Z at hWZ ⊢
    generalize Real.cos (w / 2) = C at hs2 hC ⊢
    field_simp
    have hs2' : C ^ 2 * S ^ 2 = C ^ 2 - b ^ 2 * W ^ 2 := by rw [hs2]; field_simp
    linear_combination W * hs2' + (-(W * b ^ 2)) * hWZ
  · beta_reduce
    have h0 := hU 0 ⟨le_rfl, zero_le_one⟩
    rw [Real.cos_arccos (by linarith [h0.1]) h0.2.le, show w * (0 - 1 / 2) = -(w / 2) by ring, Real.cos_neg]
    field_simp
  · beta_reduce
    have h1 := hU 1 ⟨zero_le_one, le_rfl⟩
    rw [Real.cos_arccos (by linarith [h1.1]) h1.2.le, show w * (1 - 1 / 2) = w / 2 by ring]
    field_simp

/-! The break: top of `f b` on (0, 2 arccos b), attained, transcendental. -/

lemma f_pos {b w : ℝ} (hb : 0 < b) (hw : 0 < w) (hgap : b < Real.cos (w / 2)) : 0 < f b w := by
  unfold f
  have hC : 0 < Real.cos (w / 2) := by linarith
  have : b ^ 2 / Real.cos (w / 2) ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  have := pow_pos hw 2
  nlinarith

lemma gap_of_pos {b μ w : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hw : 0 < w) (hwpi : w < Real.pi)
    (h : μ = f b w) : b < Real.cos (w / 2) := by
  have hC : 0 < Real.cos (w / 2) := cos_pos_of (by linarith) (by linarith)
  have h4 : b ^ 2 / Real.cos (w / 2) ^ 2 < 1 := by
    by_contra hle; push_neg at hle
    have : f b w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  rw [div_lt_one (by positivity)] at h4
  nlinarith

lemma f_contOn {b L : ℝ} (hLpi : L < Real.pi) : ContinuousOn (f b) (Set.Icc 0 L) := by
  have hne : ∀ x ∈ Set.Icc 0 L, Real.cos (x / 2) ^ 2 ≠ 0 := fun x hx =>
    (pow_pos (cos_pos_of' hx) 2).ne'
  unfold f
  exact (continuousOn_pow 2).mul (continuousOn_const.sub (continuousOn_const.div
    ((Real.continuous_cos.comp (continuous_id.div_const 2)).pow 2).continuousOn hne))
where
  cos_pos_of' {x : ℝ} (hx : x ∈ Set.Icc 0 L) : 0 < Real.cos (x / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩

lemma f_hasDerivAt (b w : ℝ) (hC : Real.cos (w / 2) ≠ 0) : HasDerivAt (f b)
    (2 * w * (1 - b ^ 2 / Real.cos (w / 2) ^ 2) - w ^ 2 * b ^ 2 * Real.sin (w / 2) / Real.cos (w / 2) ^ 3) w := by
  have hch : HasDerivAt (fun w => Real.cos (w / 2)) (-Real.sin (w / 2) * (1 / 2)) w := by
    have h := (Real.hasDerivAt_cos (w / 2)).comp w ((hasDerivAt_id' w).div_const 2)
    exact h.congr_deriv (by ring)
  have h := (hasDerivAt_pow 2 w).mul (((hasDerivAt_const w (b ^ 2)).div (hch.pow 2) (pow_ne_zero 2 hC)).const_sub 1)
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.div_apply]
  field_simp
  ring

/-- **Circle twin of the predicted family, end to end from the ODE: for every algebraic b with 0 < b < 1, the
largest solvable push of `v'' = mu cos v / sin^3 v`, `cos v = b` at both ends, `0 < v < pi/2`, exists, is
attained, and is transcendental.** No hypotheses: Lindemann for sine is the proved `LindemannBridge.lindemann_sin`. -/
theorem break_end_to_end {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hbA : IsAlgebraic ℚ b) :
    ∃ B : ℝ, IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol b μ v v'} B ∧ Transcendental ℚ B := by
  set L := 2 * Real.arccos b with hLdef
  have hcosL : Real.cos (L / 2) = b := by
    rw [show L / 2 = Real.arccos b by ring]; exact Real.cos_arccos (by linarith) hb1.le
  have hL : 0 < L := by have := Real.arccos_pos.mpr hb1; linarith
  have hLpi : L < Real.pi := by have := Real.arccos_lt_pi_div_two.mpr hb0; linarith
  -- a strict cosine comparison on [0, pi/2]
  have hlt_iff : ∀ x, 0 ≤ x → x ≤ L → b < Real.cos (x / 2) → x < L := by
    intro x hx0 hxL hb
    rcases eq_or_lt_of_le hxL with h | h
    · rw [h, hcosL] at hb; linarith
    · exact h
  obtain ⟨cs, hcs, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc 0 L)).exists_isMaxOn
    ⟨0, le_rfl, hL.le⟩ (f_contOn (b := b) hLpi)
  have hmid : 0 < f b (L / 2) := by
    apply f_pos hb0 (by linarith)
    have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (show 0 ≤ L / 2 / 2 by linarith)
      (show L / 2 ≤ Real.pi / 2 by linarith) (show L / 2 / 2 < L / 2 by linarith)
    rw [hcosL] at this; exact this
  have hfcs : 0 < f b cs := lt_of_lt_of_le hmid (hmax ⟨by linarith, by linarith⟩)
  have hcs0 : 0 < cs := by
    rcases eq_or_lt_of_le hcs.1 with h0 | h0
    · rw [← h0] at hfcs; simp [f] at hfcs
    · exact h0
  have hcspi : cs < Real.pi := by linarith [hcs.2]
  have hcsg : b < Real.cos (cs / 2) := gap_of_pos hb0 hfcs hcs0 hcspi rfl
  have hcsL : cs < L := hlt_iff cs hcs0.le hcs.2 hcsg
  have hG : IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol b μ v v'} (f b cs) := by
    refine ⟨⟨_, _, exists_sol hb0 hcs0 hcspi hcsg⟩, ?_⟩
    rintro μ ⟨v, v', h⟩
    rcases le_or_gt μ 0 with hμ | hμ
    · linarith
    obtain ⟨w, hw, hwpi, hμw⟩ := mu_formula hb0 h hμ
    have hwg := gap_of_pos hb0 hμ hw hwpi hμw
    have hwL : w ≤ L := by
      by_contra hc; push_neg at hc
      have := Real.cos_le_cos_of_nonneg_of_le_pi (show 0 ≤ L / 2 by linarith) (show w / 2 ≤ Real.pi by linarith)
        (show L / 2 ≤ w / 2 by linarith)
      rw [hcosL] at this; linarith
    rw [hμw]; exact hmax ⟨hw.le, hwL⟩
  refine ⟨f b cs, hG, ?_⟩
  have hC : 0 < Real.cos (cs / 2) := by linarith
  have hloc : IsLocalMax (f b) cs := hmax.isLocalMax (Icc_mem_nhds hcs0 hcsL)
  have hz := hloc.hasDerivAt_eq_zero (f_hasDerivAt b cs hC.ne')
  have hs : 0 < Real.sin (cs / 2) := sin_pos_of (by linarith) (by linarith)
  have hgap2 : b ^ 2 < Real.cos (cs / 2) ^ 2 := by nlinarith
  have hcrit : cs * b ^ 2 * Real.sin (cs / 2)
      = 2 * Real.cos (cs / 2) * (Real.cos (cs / 2) ^ 2 - b ^ 2) := by
    field_simp at hz
    nlinarith [hz, hcs0, hC]
  have hval : f b cs = 4 * (Real.cos (cs / 2) ^ 2 - b ^ 2) ^ 3 / (b ^ 4 * (1 - Real.cos (cs / 2) ^ 2)) := by
    have hsc : Real.sin (cs / 2) ^ 2 = 1 - Real.cos (cs / 2) ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq (cs / 2)]
    rw [← hsc]
    unfold f
    generalize Real.cos (cs / 2) = C at hC hcrit hgap2 ⊢
    generalize Real.sin (cs / 2) = S at hs hcrit ⊢
    field_simp
    linear_combination (cs * b ^ 2 * S + 2 * C * (C ^ 2 - b ^ 2)) * hcrit
  rw [hval]
  exact TrigPredicted.break_transcendental LindemannBridge.lindemann_sin hbA hb0.ne'
    (by nlinarith) hcs0 hs hgap2 hcrit

end TrigPredictedOde
