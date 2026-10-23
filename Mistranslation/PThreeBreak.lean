import Mathlib
import Mistranslation.PThreeOde
import Mistranslation.PThreeClass
import Mistranslation.LindemannBridge

/-! # P_3 pair at kap = 1: the break exists, is attained, and is transcendental (2026-10-23)

Seat `v'' = mu v^(-5/3) + v^(-1/3)`, `v(0) = v(1) = 1` (`PThreeOde.Sol 1`). The clock angle `T` parametrizes
every solution: with `k = sqrt(1/3)` the two wall conditions `p + r cosh T = 1`, `p T + r sinh T = k` are LINEAR
in `(p, r)`, so `r = (k - T)/(sinh T - T cosh T)`, `p = 1 - r cosh T`, and the push is `mu = F T = r^2 - p^2`.
Step 1 (existence): every `T` with `r > 0`, `p + r > 0` gives a solution (inverse clock; `p < 0` allowed).
Step 2 (break): `F` is continuous on `[k, 10]`, `F k = -1`, `F 1 > 0`, and `F <= 0` for `T >= 10`, so its top on
`[k, 10]` is interior and is the largest solvable push (via `PThreeOde.tau_link`).
Step 3 (implicit step): Fermat at the interior top gives `F' = 0`, i.e. `r^2 S T = p C + r - r p S^2`, which in
the variables `x = p + r`, `q = mu` is exactly the top condition `h2` of `PThree.class_of_crit`.
Step 5: `class_of_crit` with the PROVED `LindemannBridge.hermite_lindemann`. -/

namespace PThreeBreak

open PThreeOde KeplerOde

/-! Step 1: the inverse clock for any `p` with `r > 0`, `p + r > 0`. -/

lemma φ_strictMono {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) : StrictMono (φk p r) := by
  apply strictMono_of_deriv_pos
  intro η
  rw [(φk_hasDerivAt p r η).deriv]
  have := Real.one_le_cosh η
  nlinarith

lemma φ_surj {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) : Function.Surjective (φk p r) := by
  have hc : Continuous (φk p r) := continuous_iff_continuousAt.mpr fun x => (φk_hasDerivAt p r x).continuousAt
  apply hc.surjective
  · apply Filter.tendsto_atTop_mono' Filter.atTop _ (Filter.tendsto_id.const_mul_atTop hx)
    filter_upwards [Filter.eventually_ge_atTop 0] with x hx0
    have : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx0
    simp only [φk, id]; nlinarith
  · apply Filter.tendsto_atBot_mono' Filter.atBot _ (Filter.tendsto_id.const_mul_atBot hx)
    filter_upwards [Filter.eventually_le_atBot 0] with x hx0
    have : Real.sinh x ≤ x := Real.sinh_le_self_iff.mpr hx0
    simp only [φk, id]; nlinarith

noncomputable def ψ (p r : ℝ) (hr : 0 < r) (hx : 0 < p + r) : ℝ → ℝ :=
  (StrictMono.orderIsoOfSurjective (φk p r) (φ_strictMono hr hx) (φ_surj hr hx)).symm

lemma φ_ψ {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) (y : ℝ) : φk p r (ψ p r hr hx y) = y :=
  (StrictMono.orderIsoOfSurjective (φk p r) (φ_strictMono hr hx) (φ_surj hr hx)).apply_symm_apply y

lemma ψ_φ {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) (x : ℝ) : ψ p r hr hx (φk p r x) = x :=
  (StrictMono.orderIsoOfSurjective (φk p r) (φ_strictMono hr hx) (φ_surj hr hx)).symm_apply_apply x

lemma w_pos {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) (η : ℝ) : 0 < p + r * Real.cosh η := by
  have := Real.one_le_cosh η; nlinarith

lemma ψ_hasDerivAt {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) (y : ℝ) :
    HasDerivAt (ψ p r hr hx) (p + r * Real.cosh (ψ p r hr hx y))⁻¹ y := by
  have hc : Continuous (ψ p r hr hx) :=
    (StrictMono.orderIsoOfSurjective (φk p r) (φ_strictMono hr hx) (φ_surj hr hx)).symm.continuous
  exact HasDerivAt.of_local_left_inverse hc.continuousAt (φk_hasDerivAt p r _) (w_pos hr hx _).ne'
    (Filter.Eventually.of_forall (φ_ψ hr hx))

lemma cube_rpow {a : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ) (hb : 3 * b = -n) : (a ^ 3) ^ b = (a ^ n)⁻¹ := by
  rw [← Real.rpow_natCast a 3, ← Real.rpow_mul ha.le, ← Real.rpow_natCast a n, ← Real.rpow_neg ha.le]
  congr 1

/-- **Existence.** Wall data `p + r cosh T = 1`, `p T + r sinh T = k` (`3 k^2 = 1`) with `r > 0`, `p + r > 0`
give an explicit solution of the P_3 seat at kap = 1 with push `r^2 - p^2`. -/
theorem exists_sol {p r T k : ℝ} (hr : 0 < r) (hx : 0 < p + r) (hpT : p + r * Real.cosh T = 1)
    (hkT : p * T + r * Real.sinh T = k) (hk2 : 3 * k ^ 2 = 1) :
    ∃ v v' : ℝ → ℝ, PThreeOde.Sol 1 (r ^ 2 - p ^ 2) v v' := by
  set η := fun t : ℝ => ψ p r hr hx (2 * k * (t - 1 / 2)) with hηdef
  set w := fun t : ℝ => p + r * Real.cosh (η t) with hwdef
  have hw : ∀ t, 0 < w t := fun t => w_pos hr hx _
  have hη : ∀ t, HasDerivAt η ((w t)⁻¹ * (2 * k)) t := by
    intro t
    have := (ψ_hasDerivAt hr hx (2 * k * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul (2 * k))
    exact this.congr_deriv (by simp [hwdef, hηdef])
  have hwd : ∀ t, HasDerivAt w (r * (Real.sinh (η t) * ((w t)⁻¹ * (2 * k)))) t := fun t =>
    (((Real.hasDerivAt_cosh _).comp t (hη t)).const_mul r).const_add p
  have had : ∀ t, HasDerivAt (fun s => Real.sqrt (w s))
      (r * (Real.sinh (η t) * ((w t)⁻¹ * (2 * k))) / (2 * Real.sqrt (w t))) t := fun t =>
    (hwd t).sqrt (hw t).ne'
  have hud : ∀ t, HasDerivAt (fun s => 2 * k * r * Real.sinh (η s) / w s)
      ((2 * k * r * (Real.cosh (η t) * ((w t)⁻¹ * (2 * k))) * w t
        - 2 * k * r * Real.sinh (η t) * (r * (Real.sinh (η t) * ((w t)⁻¹ * (2 * k))))) / w t ^ 2) t := fun t =>
    (((Real.hasDerivAt_sinh _).comp t (hη t)).const_mul (2 * k * r)).div (hwd t) (hw t).ne'
  refine ⟨fun t => Real.sqrt (w t) ^ 3, fun t => 3 / 2 * Real.sqrt (w t) * (2 * k * r * Real.sinh (η t) / w t),
    fun t _ => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have := Real.sqrt_pos.mpr (hw t); positivity
  · refine ((had t).pow 3).congr_deriv ?_
    have ha := Real.sqrt_pos.mpr (hw t)
    have hwt := (hw t).ne'
    beta_reduce
    generalize Real.sqrt (w t) = a at ha ⊢
    field_simp
    ring
  · have := ((had t).const_mul (3 / 2)).mul (hud t)
    refine this.congr_deriv ?_
    have ha := Real.sqrt_pos.mpr (hw t)
    have ha2 := Real.sq_sqrt (hw t).le
    have hcs := Real.cosh_sq_sub_sinh_sq (η t)
    rw [cube_rpow ha (-(5 / 3)) 5 (by norm_num), cube_rpow ha (-(1 / 3)) 1 (by norm_num)]
    simp only [hwdef] at ha2 ⊢
    generalize Real.sqrt (p + r * Real.cosh (η t)) = a at ha ha2 ⊢
    generalize Real.cosh (η t) = c at ha2 hcs ⊢
    generalize Real.sinh (η t) = s at hcs ⊢
    have hp : p = a ^ 2 - r * c := by linarith
    subst hp
    field_simp
    linear_combination (r ^ 2 * a ^ 6) * hcs + (2 * r * a ^ 8 * c - r ^ 2 * a ^ 6 * s ^ 2) * hk2
  · show Real.sqrt (w 0) ^ 3 = 1
    have : w 0 = 1 := by
      simp only [hwdef, hηdef]
      rw [show 2 * k * (0 - 1 / 2) = -k by ring, ← hkT, show -(p * T + r * Real.sinh T) = φk p r (-T) by
        simp [φk, Real.sinh_neg]; ring, ψ_φ, Real.cosh_neg, hpT]
    rw [this]; simp
  · show Real.sqrt (w 1) ^ 3 = 1
    have : w 1 = 1 := by
      simp only [hwdef, hηdef]
      rw [show 2 * k * (1 - 1 / 2) = k by ring, ← hkT, show p * T + r * Real.sinh T = φk p r T by
        simp [φk], ψ_φ, hpT]
    rw [this]; simp

/-! Step 2: the curve `F` in the clock angle. -/

noncomputable def k3 : ℝ := Real.sqrt (1 / 3)

lemma k3_sq : k3 ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
lemma k3_pos : 0 < k3 := Real.sqrt_pos.mpr (by norm_num)
lemma k3_gt : 0.57 < k3 := by nlinarith [k3_sq, k3_pos]
lemma k3_lt : k3 < 0.58 := by nlinarith [k3_sq, k3_pos]

noncomputable def Dn (T : ℝ) : ℝ := Real.sinh T - T * Real.cosh T
noncomputable def R (T : ℝ) : ℝ := (k3 - T) / Dn T
noncomputable def P (T : ℝ) : ℝ := 1 - R T * Real.cosh T
noncomputable def F (T : ℝ) : ℝ := R T ^ 2 - P T ^ 2

lemma Dn_neg {T : ℝ} (hT : 0 < T) : Dn T < 0 := by
  obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope Dn (fun x => -(x * Real.sinh x)) hT
    (fun x _ => by
      unfold Dn
      exact ((Real.continuous_sinh.sub (continuous_id.mul Real.continuous_cosh)).continuousAt).continuousWithinAt)
    (fun x _ => by
      have := (Real.hasDerivAt_sinh x).sub ((hasDerivAt_id' x).mul (Real.hasDerivAt_cosh x))
      exact this.congr_deriv (by ring))
  have h0 : Dn 0 = 0 := by simp [Dn]
  rw [h0, sub_zero, sub_zero] at hsl
  have hs : 0 < Real.sinh c := Real.sinh_pos_iff.mpr hc.1
  have : -(c * Real.sinh c) < 0 := by have := mul_pos hc.1 hs; linarith
  rw [hsl] at this
  exact (div_neg_iff.mp this).elim (fun h => by linarith [h.2]) (fun h => h.1)

lemma R_pos {T : ℝ} (hT : k3 < T) : 0 < R T :=
  div_pos_of_neg_of_neg (by linarith) (Dn_neg (by linarith [k3_pos]))

lemma R_nonpos {T : ℝ} (hT0 : 0 < T) (hT : T ≤ k3) : R T ≤ 0 :=
  div_nonpos_iff.mpr (Or.inl ⟨by linarith, (Dn_neg hT0).le⟩)

lemma wall1 (T : ℝ) : P T + R T * Real.cosh T = 1 := by unfold P; ring

lemma wall2 {T : ℝ} (hT : 0 < T) : P T * T + R T * Real.sinh T = k3 := by
  have hD := (Dn_neg hT).ne
  unfold P R; unfold Dn at hD ⊢
  field_simp
  ring

lemma F_k3 : F k3 = -1 := by simp [F, P, R]

/-- `R + P <= 0` with `R > 0` forces `F <= 0`. -/
lemma F_nonpos {T : ℝ} (hR : 0 < R T) (hs : R T + P T ≤ 0) : F T ≤ 0 := by
  unfold F; nlinarith

lemma F_one_pos : 0 < F 1 := by
  set e := Real.exp 1 with he
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hepos : 0 < e := Real.exp_pos 1
  have hC : Real.cosh 1 = (e + e⁻¹) / 2 := by rw [Real.cosh_eq, Real.exp_neg]
  have hSn : Real.sinh 1 = (e - e⁻¹) / 2 := by rw [Real.sinh_eq, Real.exp_neg]
  have hR1 : R 1 = (1 - k3) * e := by
    unfold R Dn; rw [hC, hSn]; field_simp; ring
  have hsum : R 1 + P 1 = 1 - (1 - k3) * (e - 1) ^ 2 / 2 := by
    unfold P; rw [hR1, hC]; field_simp; ring
  have hk1 := k3_gt
  have hk2 := k3_lt
  have hsum_pos : 0 < R 1 + P 1 := by
    rw [hsum]; nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - k3) (by nlinarith : (0 : ℝ) < (e - 1) ^ 2)]
  have hC1 : 1 ≤ Real.cosh 1 := Real.one_le_cosh 1
  have hRb : 1.1 < R 1 := by rw [hR1]; nlinarith
  have hdiff : 0 < R 1 - P 1 := by unfold P; nlinarith
  unfold F; nlinarith

lemma F_big {T : ℝ} (hT : 10 ≤ T) : F T ≤ 0 := by
  have hk1 := k3_gt
  have hk2 := k3_lt
  have hR := R_pos (show k3 < T by linarith)
  apply F_nonpos hR
  have hD := Dn_neg (show 0 < T by linarith)
  have hsum : R T + P T = 1 - R T * (Real.cosh T - 1) := by unfold P; ring
  rw [hsum, sub_nonpos]
  unfold R
  rw [div_mul_eq_mul_div, le_div_iff_of_neg hD]
  unfold Dn
  set e := Real.exp T
  have hC : Real.cosh T = (e + e⁻¹) / 2 := by rw [Real.cosh_eq, Real.exp_neg]
  have hSn : Real.sinh T = (e - e⁻¹) / 2 := by rw [Real.sinh_eq, Real.exp_neg]
  have hq : 1 + T + T ^ 2 / 2 ≤ e := Real.quadratic_le_exp_of_nonneg (by linarith)
  have he1 : 1 ≤ e := by nlinarith
  have hinv : e⁻¹ ≤ 1 := inv_le_one_of_one_le₀ he1
  have hinv0 : 0 < e⁻¹ := by positivity
  rw [hC, hSn]
  nlinarith [mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ 1 - k3), mul_le_mul_of_nonneg_left hinv
    (by linarith : (0 : ℝ) ≤ 1 + k3)]

noncomputable def Rp (T : ℝ) : ℝ := (-Dn T + (k3 - T) * T * Real.sinh T) / Dn T ^ 2

lemma F_hasDerivAt {T : ℝ} (hT : 0 < T) :
    HasDerivAt F (2 * R T * Rp T + 2 * P T * (Rp T * Real.cosh T + R T * Real.sinh T)) T := by
  have hD := (Dn_neg hT).ne
  have hDd : HasDerivAt Dn (Real.cosh T - (1 * Real.cosh T + T * Real.sinh T)) T :=
    (Real.hasDerivAt_sinh T).sub ((hasDerivAt_id' T).mul (Real.hasDerivAt_cosh T))
  have hRd := ((hasDerivAt_id' T).const_sub k3).div hDd hD
  have hPd := (hRd.mul (Real.hasDerivAt_cosh T)).const_sub 1
  have := (hRd.pow 2).sub (hPd.pow 2)
  refine this.congr_deriv ?_
  simp only [Pi.div_apply, Pi.mul_apply]
  beta_reduce
  unfold Rp P R
  generalize Dn T = d at hD ⊢
  field_simp
  ring_nf
  field_simp
  ring

lemma F_contOn : ContinuousOn F (Set.Icc k3 10) := fun T hT =>
  (F_hasDerivAt (lt_of_lt_of_le k3_pos hT.1)).continuousAt.continuousWithinAt

/-- Every solvable positive push lies on the curve `F`, at an angle with `R > 0`. -/
lemma on_curve {μ : ℝ} {v v' : ℝ → ℝ} (h : PThreeOde.Sol 1 μ v v') (hμ : 0 < μ) :
    ∃ T, 0 < T ∧ 0 < R T ∧ F T = μ := by
  obtain ⟨x, hx, hx1, hG⟩ := tau_link h hμ one_pos
  simp only [div_one] at hG
  set p0 := (x - μ / x) / 2 with hp0
  set r0 := (x + μ / x) / 2 with hr0
  have hr : 0 < r0 := by rw [hr0]; positivity
  have hsum : p0 + r0 = x := by rw [hp0, hr0]; ring
  have hy : 1 < (1 - p0) / r0 := by rw [lt_div_iff₀ hr]; linarith
  set T0 := Real.arcosh ((1 - p0) / r0) with hT0
  have hT : 0 < T0 := Real.arcosh_pos hy
  have hc : Real.cosh T0 = (1 - p0) / r0 := Real.cosh_arcosh hy.le
  have hs : Real.sinh T0 = Real.sqrt (((1 - p0) / r0) ^ 2 - 1) := Real.sinh_arcosh hy.le
  have hw1 : p0 + r0 * Real.cosh T0 = 1 := by rw [hc]; field_simp; ring
  have hw2 : p0 * T0 + r0 * Real.sinh T0 = k3 := by
    rw [hs, hT0]; unfold k3; rw [← hG]; unfold Gk; ring
  have hD := (Dn_neg hT).ne
  have hRr : R T0 = r0 := by
    unfold R; rw [div_eq_iff hD]; unfold Dn
    linear_combination -hw2 + T0 * hw1
  have hPp : P T0 = p0 := by unfold P; rw [hRr]; linarith
  refine ⟨T0, hT, hRr ▸ hr, ?_⟩
  unfold F; rw [hRr, hPp, hp0, hr0]; field_simp; ring

/-! Step 3: the critical equation in the variables of `PThree.class_of_crit`. -/

lemma top_eq {T : ℝ} (hT : 0 < T)
    (hF : 2 * R T * Rp T + 2 * P T * (Rp T * Real.cosh T + R T * Real.sinh T) = 0) :
    R T ^ 2 * Real.sinh T * T - R T - P T * Real.cosh T + P T * R T * Real.sinh T ^ 2 = 0 := by
  have hD := (Dn_neg hT).ne
  have hRD : R T * Dn T = k3 - T := by unfold R; field_simp
  have hDRp : Dn T * Rp T = R T * T * Real.sinh T - 1 := by
    unfold Rp; field_simp
    linear_combination (-(T * Real.sinh T)) * hRD
  have hDn : Dn T = Real.sinh T - T * Real.cosh T := rfl
  linear_combination (Dn T / 2) * hF - (R T + P T * Real.cosh T) * hDRp - (P T * R T * Real.sinh T) * hDn

lemma h2_of_top {R P T S C : ℝ} (hw1 : P + R * C = 1)
    (hE : R ^ 2 * S * T - R - P * C + P * R * S ^ 2 = 0) :
    ((P + R) ^ 2 + (R ^ 2 - P ^ 2)) ^ 3 * S * T
      + ((P + R) ^ 2 - (R ^ 2 - P ^ 2)) * ((P + R) ^ 2 + (R ^ 2 - P ^ 2)) ^ 2 * S ^ 2
      + 4 * (P + R) ^ 2 * ((R ^ 2 - P ^ 2) - 2 * (P + R) * (R ^ 2 - P ^ 2) - (P + R) ^ 2) = 0 := by
  linear_combination (8 * R * (P + R) ^ 3) * hE + (8 * (P + R) ^ 3 * P) * hw1

/-! Step 5: assembly. -/

/-- **P_3 at kap = 1, end to end.** The set of pushes for which the seat `v'' = mu v^(-5/3) + v^(-1/3)`,
`v(0) = v(1) = 1` has a solution has a greatest element (the break), and the break is transcendental. -/
theorem break_end_to_end :
    ∃ μs : ℝ, IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, PThreeOde.Sol 1 μ v v'} μs ∧ Transcendental ℚ μs := by
  have hk1 := k3_gt
  have hk2 := k3_lt
  obtain ⟨Ts, hTs, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc k3 (10 : ℝ))).exists_isMaxOn
    ⟨k3, le_rfl, by linarith⟩ F_contOn
  have hF1 : F 1 ≤ F Ts := hmax ⟨by linarith, by norm_num⟩
  have hF1p := F_one_pos
  have hFs : 0 < F Ts := by linarith
  have hTk : k3 < Ts := by
    rcases eq_or_lt_of_le hTs.1 with h | h
    · rw [← h, F_k3] at hFs; linarith
    · exact h
  have hT10 : Ts < 10 := by
    rcases eq_or_lt_of_le hTs.2 with h | h
    · rw [h] at hFs; linarith [F_big (le_refl (10 : ℝ))]
    · exact h
  have hT0 : 0 < Ts := by linarith
  have hR := R_pos hTk
  have hx : 0 < P Ts + R Ts := by
    by_contra hc; push Not at hc
    linarith [F_nonpos hR (by linarith)]
  have hk3 : 3 * k3 ^ 2 = 1 := by rw [k3_sq]; norm_num
  refine ⟨F Ts, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨v, v', hv⟩ := exists_sol hR (by linarith) (wall1 Ts) (wall2 hT0) hk3
    exact ⟨v, v', hv⟩
  · rintro μ ⟨v, v', h⟩
    rcases le_or_gt μ 0 with hμ | hμ
    · linarith
    obtain ⟨T, hT, hRT, hFT⟩ := on_curve h hμ
    rw [← hFT]
    have hTk' : k3 < T := by
      by_contra hc; push Not at hc; linarith [R_nonpos hT hc]
    have hT10' : T ≤ 10 := by
      by_contra hc; push Not at hc; linarith [F_big hc.le]
    exact hmax ⟨hTk'.le, hT10'⟩
  · -- Fermat at the interior top
    have hloc : IsLocalMax F Ts := hmax.isLocalMax (Icc_mem_nhds hTk hT10)
    have hF0 := hloc.hasDerivAt_eq_zero (F_hasDerivAt hT0)
    have hE := top_eq hT0 hF0
    have hw1 := wall1 Ts
    have hw2 := wall2 hT0
    have hcs := Real.cosh_sq_sub_sinh_sq Ts
    set r := R Ts
    set p := P Ts
    set C := Real.cosh Ts
    set S := Real.sinh Ts
    have hFdef : F Ts = r ^ 2 - p ^ 2 := rfl
    rw [hFdef] at hFs ⊢
    refine PThree.class_of_crit LindemannBridge.hermite_lindemann (kap := 1) (q := r ^ 2 - p ^ 2)
      (x := p + r) (T := Ts) (S := S) (C := C) (k := k3) one_pos isAlgebraic_one hFs (by ring) hx hT0
      (Real.sinh_pos_iff.mpr hT0) hk3 ?_ ?_ ?_ (h2_of_top hw1 hE) (by rw [← Real.cosh_add_sinh])
    · linear_combination (2 * (p + r)) * hw1
    · linear_combination (-4 * (p + r) ^ 2 * r ^ 2) * hcs + (4 * (p + r) ^ 2 * (r * C + 1 - p)) * hw1
    · linear_combination (2 * (p + r)) * hw2

end PThreeBreak
