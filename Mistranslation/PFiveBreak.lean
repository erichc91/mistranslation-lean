import Mathlib
import Mistranslation.PFiveOde
import Mistranslation.PFiveClass
import Mistranslation.PThreeBreak
import Mistranslation.LindemannBridge

/-! # P_5 pair at kap = 1: the break exists, is attained, and is transcendental (2026-10-23)

Seat `v'' = mu v^(-7/5) + v^(-3/5)`, `v(0) = v(1) = 1` (`PFiveOde.Sol 1`); numerically the break is 1.208168022773.
Clock angle `T`, `k = sqrt(1/5)`, wall `p = 1 - r cosh T`. The time condition `int_0^T (p + r cosh)^2 = k` becomes
the quadratic `a r^2 - 2 m r + (T - k) = 0` with `m = T cosh T - sinh T = int (C - cosh) > 0` and
`a = T (C^2 + 1/2) - (3/2) S C = int (C - cosh)^2`. Since `a <= (C - 1) m` and an admissible root has
`(C - 1) r < 1`, every admissible root is the SMALL root `R T = (T - k) / (m + sqrt(m^2 - a (T - k)))`.
The push is `F T = R^2 - P^2`, `P = 1 - R cosh T`. `H T = (C-1)^2 Q(1/(C-1)) < 0` at every admissible angle and
`H >= 0` for `T >= 5`, so admissible angles live in `(k, 5)`. The top of `F` on `{T in [k,5] | disc >= 0}` is
interior; Fermat plus the implicit identity `Q(T, R T) = 0` give the top condition `h2` of `PFive.class_of_crit`. -/

namespace PFiveBreak

open PFiveOde

/-! Step 1: the weight-2 inverse clock and existence. -/

noncomputable def Φ (p r η : ℝ) : ℝ :=
  (p ^ 2 + r ^ 2 / 2) * η + Real.sinh η * (2 * p * r + r ^ 2 * Real.cosh η / 2)

lemma Φ_hasDerivAt (p r η : ℝ) : HasDerivAt (Φ p r) ((p + r * Real.cosh η) ^ 2) η := by
  have := ((hasDerivAt_id' η).const_mul (p ^ 2 + r ^ 2 / 2)).add ((Real.hasDerivAt_sinh η).mul
    ((((Real.hasDerivAt_cosh η).const_mul (r ^ 2)).div_const 2).const_add (2 * p * r)))
  refine this.congr_deriv ?_
  have hcs := Real.cosh_sq_sub_sinh_sq η
  linear_combination (-(r ^ 2) / 2) * hcs

lemma Φ_zero (p r : ℝ) : Φ p r 0 = 0 := by simp [Φ]

lemma Φ_neg (p r η : ℝ) : Φ p r (-η) = -Φ p r η := by simp [Φ, Real.sinh_neg, Real.cosh_neg]; ring

lemma Φ_strictMono {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) : StrictMono (Φ p r) := by
  apply strictMono_of_deriv_pos
  intro η
  rw [(Φ_hasDerivAt p r η).deriv]
  have := PThreeBreak.w_pos hr hx η
  positivity

lemma Φ_lin_mono {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) : Monotone (fun η => Φ p r η - (p + r) ^ 2 * η) := by
  apply monotone_of_deriv_nonneg
  · intro η
    exact ((Φ_hasDerivAt p r η).sub ((hasDerivAt_id' η).const_mul _)).differentiableAt
  · intro η
    rw [show (fun η => Φ p r η - (p + r) ^ 2 * η) = (Φ p r - fun y => (p + r) ^ 2 * y) from rfl,
      ((Φ_hasDerivAt p r η).sub ((hasDerivAt_id' η).const_mul ((p + r) ^ 2))).deriv]
    have h1 := Real.one_le_cosh η
    have : p + r ≤ p + r * Real.cosh η := by nlinarith
    nlinarith

lemma Φ_surj {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) : Function.Surjective (Φ p r) := by
  have hc : Continuous (Φ p r) := continuous_iff_continuousAt.mpr fun x => (Φ_hasDerivAt p r x).continuousAt
  have hm := Φ_lin_mono hr hx
  have hx2 : 0 < (p + r) ^ 2 := by positivity
  apply hc.surjective
  · apply Filter.tendsto_atTop_mono' Filter.atTop _ (Filter.tendsto_id.const_mul_atTop hx2)
    filter_upwards [Filter.eventually_ge_atTop 0] with x hx0
    have := hm hx0
    simp only [Φ_zero, mul_zero, sub_zero] at this
    simp only [id]; linarith
  · apply Filter.tendsto_atBot_mono' Filter.atBot _ (Filter.tendsto_id.const_mul_atBot hx2)
    filter_upwards [Filter.eventually_le_atBot 0] with x hx0
    have := hm hx0
    simp only [Φ_zero, mul_zero, sub_zero] at this
    simp only [id]; linarith

noncomputable def ψ (p r : ℝ) (hr : 0 < r) (hx : 0 < p + r) : ℝ → ℝ :=
  (StrictMono.orderIsoOfSurjective (Φ p r) (Φ_strictMono hr hx) (Φ_surj hr hx)).symm

lemma Φ_ψ {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) (y : ℝ) : Φ p r (ψ p r hr hx y) = y :=
  (StrictMono.orderIsoOfSurjective (Φ p r) (Φ_strictMono hr hx) (Φ_surj hr hx)).apply_symm_apply y

lemma ψ_Φ {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) (x : ℝ) : ψ p r hr hx (Φ p r x) = x :=
  (StrictMono.orderIsoOfSurjective (Φ p r) (Φ_strictMono hr hx) (Φ_surj hr hx)).symm_apply_apply x

lemma ψ_hasDerivAt {p r : ℝ} (hr : 0 < r) (hx : 0 < p + r) (y : ℝ) :
    HasDerivAt (ψ p r hr hx) ((p + r * Real.cosh (ψ p r hr hx y)) ^ 2)⁻¹ y := by
  have hc : Continuous (ψ p r hr hx) :=
    (StrictMono.orderIsoOfSurjective (Φ p r) (Φ_strictMono hr hx) (Φ_surj hr hx)).symm.continuous
  have := PThreeBreak.w_pos hr hx (ψ p r hr hx y)
  exact HasDerivAt.of_local_left_inverse hc.continuousAt (Φ_hasDerivAt p r _) (by positivity)
    (Filter.Eventually.of_forall (Φ_ψ hr hx))

lemma fifth_rpow {a : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ) (hb : 5 * b = -n) : (a ^ 5) ^ b = (a ^ n)⁻¹ := by
  rw [← Real.rpow_natCast a 5, ← Real.rpow_mul ha.le, ← Real.rpow_natCast a n, ← Real.rpow_neg ha.le]
  congr 1

/-- **Existence.** Wall data `p + r cosh T = 1`, `Phi p r T = k` (`5 k^2 = 1`) with `r > 0`, `p + r > 0` give an
explicit solution of the P_5 seat at kap = 1 with push `r^2 - p^2`. -/
theorem exists_sol {p r T k : ℝ} (hr : 0 < r) (hx : 0 < p + r) (hpT : p + r * Real.cosh T = 1)
    (hkT : Φ p r T = k) (hk2 : 5 * k ^ 2 = 1) :
    ∃ v v' : ℝ → ℝ, PFiveOde.Sol 1 (r ^ 2 - p ^ 2) v v' := by
  set η := fun t : ℝ => ψ p r hr hx (2 * k * (t - 1 / 2)) with hηdef
  set w := fun t : ℝ => p + r * Real.cosh (η t) with hwdef
  have hw : ∀ t, 0 < w t := fun t => PThreeBreak.w_pos hr hx _
  have hη : ∀ t, HasDerivAt η (((w t) ^ 2)⁻¹ * (2 * k)) t := by
    intro t
    have := (ψ_hasDerivAt hr hx (2 * k * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul (2 * k))
    exact this.congr_deriv (by simp [hwdef, hηdef])
  have hwd : ∀ t, HasDerivAt w (r * (Real.sinh (η t) * (((w t) ^ 2)⁻¹ * (2 * k)))) t := fun t =>
    (((Real.hasDerivAt_cosh _).comp t (hη t)).const_mul r).const_add p
  have had : ∀ t, HasDerivAt (fun s => Real.sqrt (w s))
      (r * (Real.sinh (η t) * (((w t) ^ 2)⁻¹ * (2 * k))) / (2 * Real.sqrt (w t))) t := fun t =>
    (hwd t).sqrt (hw t).ne'
  have hw2 : ∀ t, w t ^ 2 ≠ 0 := fun t => pow_ne_zero 2 (hw t).ne'
  have hud : ∀ t, HasDerivAt (fun s => 2 * k * r * Real.sinh (η s) / w s ^ 2)
      ((2 * k * r * (Real.cosh (η t) * (((w t) ^ 2)⁻¹ * (2 * k))) * w t ^ 2
        - 2 * k * r * Real.sinh (η t) * (↑2 * w t ^ (2 - 1) * (r * (Real.sinh (η t) * (((w t) ^ 2)⁻¹ * (2 * k))))))
        / (w t ^ 2) ^ 2) t := fun t =>
    (((Real.hasDerivAt_sinh _).comp t (hη t)).const_mul (2 * k * r)).div ((hwd t).pow 2) (hw2 t)
  refine ⟨fun t => Real.sqrt (w t) ^ 5,
    fun t => 5 / 2 * Real.sqrt (w t) ^ 3 * (2 * k * r * Real.sinh (η t) / w t ^ 2),
    fun t _ => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have := Real.sqrt_pos.mpr (hw t); positivity
  · refine ((had t).pow 5).congr_deriv ?_
    have ha := Real.sqrt_pos.mpr (hw t)
    have ha2 := Real.sq_sqrt (hw t).le
    have hwt := (hw t).ne'
    beta_reduce
    generalize Real.sqrt (w t) = a at ha ha2 ⊢
    generalize w t = W at hwt ha2 ⊢
    subst ha2
    field_simp
    ring
  · have := (((had t).pow 3).const_mul (5 / 2)).mul (hud t)
    refine this.congr_deriv ?_
    have ha := Real.sqrt_pos.mpr (hw t)
    have ha2 := Real.sq_sqrt (hw t).le
    have hcs := Real.cosh_sq_sub_sinh_sq (η t)
    rw [fifth_rpow ha (-(7 / 5)) 7 (by norm_num), fifth_rpow ha (-(3 / 5)) 3 (by norm_num)]
    simp only [Pi.pow_apply]
    simp only [hwdef] at ha2 ⊢
    beta_reduce
    generalize Real.sqrt (p + r * Real.cosh (η t)) = a at ha ha2 ⊢
    generalize Real.cosh (η t) = c at ha2 hcs ⊢
    generalize Real.sinh (η t) = s at hcs ⊢
    have hp : p = a ^ 2 - r * c := by linarith
    subst hp
    push_cast
    field_simp
    linear_combination (a ^ 10 * r ^ 2) * hcs + (2 * r * a ^ 12 * c - a ^ 10 * r ^ 2 * s ^ 2) * hk2
  · show Real.sqrt (w 0) ^ 5 = 1
    have : w 0 = 1 := by
      simp only [hwdef, hηdef]
      rw [show 2 * k * (0 - 1 / 2) = -k by ring, ← hkT, ← Φ_neg, ψ_Φ, Real.cosh_neg, hpT]
    rw [this]; simp
  · show Real.sqrt (w 1) ^ 5 = 1
    have : w 1 = 1 := by
      simp only [hwdef, hηdef]
      rw [show 2 * k * (1 - 1 / 2) = k by ring, ← hkT, ψ_Φ, hpT]
    rw [this]; simp

/-! Step 2: the curve in the clock angle. -/

noncomputable def k5 : ℝ := Real.sqrt (1 / 5)

lemma k5_sq : k5 ^ 2 = 1 / 5 := Real.sq_sqrt (by norm_num)
lemma k5_pos : 0 < k5 := Real.sqrt_pos.mpr (by norm_num)
lemma k5_gt : 0.447 < k5 := by nlinarith [k5_sq, k5_pos]
lemma k5_lt : k5 < 0.4473 := by nlinarith [k5_sq, k5_pos]

noncomputable def m (T : ℝ) : ℝ := T * Real.cosh T - Real.sinh T
noncomputable def aa (T : ℝ) : ℝ := T * (Real.cosh T ^ 2 + 1 / 2) - 3 / 2 * Real.sinh T * Real.cosh T
noncomputable def Disc (T : ℝ) : ℝ := m T ^ 2 - aa T * (T - k5)
noncomputable def R (T : ℝ) : ℝ := (T - k5) / (m T + Real.sqrt (Disc T))
noncomputable def P (T : ℝ) : ℝ := 1 - R T * Real.cosh T
noncomputable def F (T : ℝ) : ℝ := R T ^ 2 - P T ^ 2
noncomputable def H (T : ℝ) : ℝ :=
  3 / 2 * T + Real.sinh T * Real.cosh T / 2 - 2 * Real.sinh T - k5 * (Real.cosh T - 1) ^ 2
/-- The quadratic time condition at angle `T` for radius `r` (wall `p = 1 - r cosh T` substituted). -/
noncomputable def Qd (T r : ℝ) : ℝ := aa T * r ^ 2 - 2 * m T * r + (T - k5)

lemma m_pos {T : ℝ} (hT : 0 < T) : 0 < m T := by
  have := PThreeBreak.Dn_neg hT; unfold PThreeBreak.Dn at this; unfold m; linarith

lemma den_pos {T : ℝ} (hT : 0 < T) : 0 < m T + Real.sqrt (Disc T) := by
  have := m_pos hT; have := Real.sqrt_nonneg (Disc T); linarith

/-- `a <= (C - 1) m`, i.e. `int (C - cosh)^2 <= (C - 1) int (C - cosh)`. -/
lemma a_le {T : ℝ} (hT : 0 < T) : aa T ≤ (Real.cosh T - 1) * m T := by
  set g := fun T : ℝ => (Real.cosh T - 1) * m T - aa T with hg
  obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope g (fun x => Real.sinh x * (Real.sinh x - x)) hT
    (fun x _ => by
      simp only [hg, m, aa]
      fun_prop)
    (fun x _ => by
      have hC := Real.hasDerivAt_cosh x
      have hS := Real.hasDerivAt_sinh x
      have hI := hasDerivAt_id' x
      have := ((hC.sub_const 1).mul ((hI.mul hC).sub hS)).sub
        ((hI.mul ((hC.pow 2).add_const (1 / 2))).sub ((hS.const_mul (3 / 2)).mul hC))
      refine this.congr_deriv ?_
      have hcs := Real.cosh_sq_sub_sinh_sq x
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply]
      beta_reduce
      simp only [Nat.cast_ofNat]
      linear_combination (1 / 2) * hcs)
  have h0 : g 0 = 0 := by simp [hg, m, aa]
  rw [h0, sub_zero, sub_zero] at hsl
  have hs : 0 < Real.sinh c := Real.sinh_pos_iff.mpr hc.1
  have hsc : c ≤ Real.sinh c := Real.self_le_sinh_iff.mpr hc.1.le
  have : 0 ≤ Real.sinh c * (Real.sinh c - c) := mul_nonneg hs.le (by linarith)
  rw [hsl] at this
  have := (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])
  simp only [hg] at this
  linarith

/-- `H = (C-1)^2 Q(1/(C-1))`, factored through an admissible root. -/
lemma H_identity (T r : ℝ) :
    H T = (1 - (Real.cosh T - 1) * r) * (aa T + aa T * (Real.cosh T - 1) * r - 2 * m T * (Real.cosh T - 1))
      + (Real.cosh T - 1) ^ 2 * Qd T r := by
  unfold H Qd aa m; ring

/-- **Admissible roots are the small root.** -/
lemma valid {T r : ℝ} (hT : 0 < T) (hr : 0 < r) (hx : 0 < 1 - r * (Real.cosh T - 1)) (hQ : Qd T r = 0) :
    aa T * r < m T ∧ Disc T = (m T - aa T * r) ^ 2 ∧ R T = r ∧ H T < 0 ∧ k5 < T := by
  have hm := m_pos hT
  have ha := a_le hT
  have hs : 0 < Real.cosh T - 1 := by have := Real.one_lt_cosh.mpr hT.ne'; linarith
  have h1 : aa T * r < m T := by
    have : aa T * r ≤ (Real.cosh T - 1) * m T * r := mul_le_mul_of_nonneg_right ha hr.le
    nlinarith
  have h2 : Disc T = (m T - aa T * r) ^ 2 := by
    unfold Disc; unfold Qd at hQ; linear_combination (-aa T) * hQ
  have h3 : R T = r := by
    unfold R; rw [h2, Real.sqrt_sq (by linarith)]
    rw [div_eq_iff (by linarith)]
    unfold Qd at hQ; linear_combination hQ
  have h4 : H T < 0 := by
    rw [H_identity T r, hQ, mul_zero, add_zero]
    apply mul_neg_of_pos_of_neg (by linarith)
    nlinarith
  have h5 : k5 < T := by
    unfold Qd at hQ; nlinarith
  exact ⟨h1, h2, h3, h4, h5⟩

lemma H_nonneg {T : ℝ} (hT : 5 ≤ T) : 0 ≤ H T := by
  have hk := k5_lt
  have hk0 := k5_pos
  set e := Real.exp T with he
  set f := Real.exp (-T) with hf
  have hef : e * f = 1 := by rw [he, hf, ← Real.exp_add]; simp
  have hf0 : 0 < f := Real.exp_pos _
  have he3 : e = Real.exp (T / 3) ^ 3 := by rw [he, ← Real.exp_nat_mul]; ring_nf
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ T / 3 by linarith)
  have hy : (4 : ℝ) ≤ Real.exp (T / 3) := by nlinarith
  have he64 : 64 ≤ e := by rw [he3]; nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hy 3]
  have hf1 : f ≤ 1 := by nlinarith
  have hC : Real.cosh T = (e + f) / 2 := by rw [Real.cosh_eq]
  have hS : Real.sinh T = (e - f) / 2 := by rw [Real.sinh_eq]
  unfold H
  rw [hC, hS]
  have hC33 : 32 ≤ (e + f) / 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hk.le (sq_nonneg ((e + f) / 2 - 1)), mul_pos hf0 hf0,
    mul_le_mul_of_nonneg_left hC33 (by linarith : (0 : ℝ) ≤ (e + f) / 2 - 1)]

/-- Where the discriminant is nonnegative, `R` solves the quadratic. -/
lemma Q_of_disc {T : ℝ} (hT : 0 < T) (hD : 0 ≤ Disc T) : Qd T (R T) = 0 := by
  have hden := den_pos hT
  have hs2 := Real.sq_sqrt hD
  have hRd : R T * (m T + Real.sqrt (Disc T)) = T - k5 := by unfold R; field_simp
  set s := Real.sqrt (Disc T)
  have hms : m T - s = aa T * R T := by
    have : (m T - s - aa T * R T) * (m T + s) = 0 := by
      unfold Disc at hs2; linear_combination (-1 : ℝ) * hs2 - aa T * hRd
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  unfold Qd
  linear_combination -hRd - R T * hms

lemma R_nonneg {T : ℝ} (hT : k5 ≤ T) : 0 ≤ R T :=
  div_nonneg (by linarith) (den_pos (lt_of_lt_of_le k5_pos hT)).le

lemma F_k5 : F k5 = -1 := by simp [F, P, R]

lemma F_nonpos {T : ℝ} (hR : 0 ≤ R T) (hs : R T + P T ≤ 0) : F T ≤ 0 := by unfold F; nlinarith

/-- An angle in `[k, 5]` with nonnegative discriminant and positive push is admissible. -/
lemma admissible {T : ℝ} (hT : k5 ≤ T) (hD : 0 ≤ Disc T) (hF : 0 < F T) :
    0 < R T ∧ 0 < 1 - R T * (Real.cosh T - 1) ∧ Qd T (R T) = 0 := by
  have hR0 := R_nonneg hT
  have hRpos : 0 < R T := by
    rcases eq_or_lt_of_le hR0 with h | h
    · unfold F P at hF; rw [← h] at hF; simp at hF; linarith
    · exact h
  have hx : 0 < 1 - R T * (Real.cosh T - 1) := by
    by_contra hc; push Not at hc
    have : R T + P T ≤ 0 := by unfold P; linarith
    linarith [F_nonpos hR0 this]
  exact ⟨hRpos, hx, Q_of_disc (lt_of_lt_of_le k5_pos hT) hD⟩

/-- The test angle `T = 1`: discriminant nonnegative and positive push. -/
lemma at_one : 0 ≤ Disc 1 ∧ 0 < F 1 := by
  have hk1 := k5_gt
  have hk2 := k5_lt
  set e := Real.exp 1 with he
  set f := Real.exp (-1) with hf
  have hef : e * f = 1 := by rw [he, hf, ← Real.exp_add]; simp
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hf1 : 0.3678794411 < f := by nlinarith
  have hf2 : f < 0.3678794412 := by nlinarith
  have hC : Real.cosh 1 = (e + f) / 2 := by rw [Real.cosh_eq]
  have hS : Real.sinh 1 = (e - f) / 2 := by rw [Real.sinh_eq]
  have hm : m 1 = f := by unfold m; rw [hC, hS]; ring
  have ha : aa 1 = (-(e ^ 2) / 2 + 5 * f ^ 2 / 2 + 4) / 4 := by
    unfold aa; rw [hC, hS]; linear_combination (1 / 2) * hef
  have ha1 : 0.16 < aa 1 := by rw [ha]; nlinarith
  have ha2 : aa 1 < 0.162 := by rw [ha]; nlinarith
  have hD : 0 ≤ Disc 1 := by unfold Disc; rw [hm]; nlinarith
  have hD1 : Disc 1 ≤ 1 := by unfold Disc; rw [hm]; nlinarith
  have hsq0 := Real.sqrt_nonneg (Disc 1)
  have hsq1 : Real.sqrt (Disc 1) ≤ 1 := Real.sqrt_le_one.mpr hD1
  have hden : 0 < m 1 + Real.sqrt (Disc 1) := den_pos one_pos
  have hRd : R 1 * (m 1 + Real.sqrt (Disc 1)) = 1 - k5 := by unfold R; field_simp
  rw [hm] at hden hRd
  have hRlo : 0.404 < R 1 := by nlinarith
  have hRhi : R 1 < 1.51 := by nlinarith
  refine ⟨hD, ?_⟩
  have hC1 : Real.cosh 1 = (e + f) / 2 := hC
  unfold F P
  rw [hC1]
  nlinarith [mul_pos (by nlinarith : (0 : ℝ) < R 1 * (1 + (e + f) / 2) - 1)
    (by nlinarith : (0 : ℝ) < 1 - R 1 * ((e + f) / 2 - 1))]

/-! Step 3: derivatives, the implicit identity, the top condition. -/

lemma m_hasDerivAt (T : ℝ) : HasDerivAt m (T * Real.sinh T) T := by
  have := ((hasDerivAt_id' T).mul (Real.hasDerivAt_cosh T)).sub (Real.hasDerivAt_sinh T)
  exact this.congr_deriv (by ring)

lemma aa_hasDerivAt (T : ℝ) : HasDerivAt aa (2 * Real.sinh T * m T) T := by
  have hC := Real.hasDerivAt_cosh T
  have hS := Real.hasDerivAt_sinh T
  have := ((hasDerivAt_id' T).mul ((hC.pow 2).add_const (1 / 2))).sub ((hS.const_mul (3 / 2)).mul hC)
  refine this.congr_deriv ?_
  have hcs := Real.cosh_sq_sub_sinh_sq T
  unfold m
  simp only [Nat.cast_ofNat, Pi.pow_apply, Pi.mul_apply]
  linear_combination (-1 / 2) * hcs

lemma Disc_hasDerivAt (T : ℝ) :
    HasDerivAt Disc (2 * m T * (T * Real.sinh T) - (2 * Real.sinh T * m T * (T - k5) + aa T * 1)) T := by
  have := ((m_hasDerivAt T).pow 2).sub ((aa_hasDerivAt T).mul ((hasDerivAt_id' T).sub_const k5))
  exact this.congr_deriv (by simp only [Nat.cast_ofNat]; ring)

lemma Disc_cont : Continuous Disc :=
  continuous_iff_continuousAt.mpr fun T => (Disc_hasDerivAt T).continuousAt

lemma R_contAt {T : ℝ} (hT : 0 < T) : ContinuousAt R T := by
  have hm : Continuous m := continuous_iff_continuousAt.mpr fun T => (m_hasDerivAt T).continuousAt
  exact ((continuous_id.sub continuous_const).continuousAt).div
    ((hm.add (Disc_cont.sqrt)).continuousAt) (den_pos hT).ne'

lemma F_contAt {T : ℝ} (hT : 0 < T) : ContinuousAt F T := by
  have hR := R_contAt hT
  unfold F P
  exact (hR.pow 2).sub ((continuousAt_const.sub (hR.mul Real.continuous_cosh.continuousAt)).pow 2)

lemma R_hasDerivAt {T : ℝ} (hT : 0 < T) (hD : 0 < Disc T) : ∃ ρ, HasDerivAt R ρ T :=
  ⟨_, ((hasDerivAt_id' T).sub_const k5).div ((m_hasDerivAt T).add ((Disc_hasDerivAt T).sqrt hD.ne'))
    (den_pos hT).ne'⟩

lemma F_hasDerivAt_of {T ρ : ℝ} (hR : HasDerivAt R ρ T) :
    HasDerivAt F (2 * R T * ρ + 2 * P T * (ρ * Real.cosh T + R T * Real.sinh T)) T := by
  have hP := (hR.mul (Real.hasDerivAt_cosh T)).const_sub 1
  have := (hR.pow 2).sub (hP.pow 2)
  refine this.congr_deriv ?_
  unfold P; simp only [Nat.cast_ofNat, Pi.pow_apply, Pi.mul_apply]; ring

/-- The implicit identity `Q(T, R T) = 0` holds near any angle with positive discriminant, so its derivative
vanishes there. -/
lemma implicit {T ρ : ℝ} (hT : 0 < T) (hD : 0 < Disc T) (hR : HasDerivAt R ρ T) :
    2 * Real.sinh T * m T * R T ^ 2 + aa T * (2 * R T * ρ) - 2 * (T * Real.sinh T * R T + m T * ρ) + 1 = 0 := by
  have hd : HasDerivAt (fun y => Qd y (R y))
      (2 * Real.sinh T * m T * R T ^ 2 + aa T * (2 * R T * ρ) - 2 * (T * Real.sinh T * R T + m T * ρ) + 1) T := by
    have := (((aa_hasDerivAt T).mul (hR.pow 2)).sub (((m_hasDerivAt T).const_mul 2).mul hR)).add
      ((hasDerivAt_id' T).sub_const k5)
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Pi.pow_apply, Pi.mul_apply]; ring
  have hev : (fun y => Qd y (R y)) =ᶠ[nhds T] fun _ => 0 := by
    have h1 : ∀ᶠ y in nhds T, 0 < Disc y := Disc_cont.continuousAt.eventually (lt_mem_nhds hD)
    have h2 : ∀ᶠ y in nhds T, 0 < y := lt_mem_nhds hT
    filter_upwards [h1, h2] with y hy1 hy2
    exact Q_of_disc hy2 hy1.le
  exact hd.unique ((hasDerivAt_const T (0 : ℝ)).congr_of_eventuallyEq hev)

/-- Fermat + the implicit identity: the top condition at an interior critical angle (raw form). -/
lemma top5 {T ρ : ℝ}
    (E1 : 2 * R T * ρ + 2 * P T * (ρ * Real.cosh T + R T * Real.sinh T) = 0)
    (E2 : 2 * Real.sinh T * m T * R T ^ 2 + aa T * (2 * R T * ρ) - 2 * (T * Real.sinh T * R T + m T * ρ) + 1 = 0) :
    (2 * Real.sinh T * m T * R T ^ 2 - 2 * T * Real.sinh T * R T + 1) * (R T + P T * Real.cosh T)
      - (2 * aa T * R T - 2 * m T) * P T * R T * Real.sinh T = 0 := by
  linear_combination (R T + P T * Real.cosh T) * E2 - (aa T * R T - m T) * E1

/-- The raw top condition is the `h2` of `PFive.class_of_crit` (wall `p = 1 - R C` substituted). -/
lemma h2_of_top5 {R T S C : ℝ}
    (htop : (2 * S * (T * C - S) * R ^ 2 - 2 * T * S * R + 1) * (R + (1 - R * C) * C)
      - (2 * (T * (C ^ 2 + 1 / 2) - 3 / 2 * S * C) * R - 2 * (T * C - S)) * (1 - R * C) * R * S = 0) :
    4 * ((1 - R * C) + R) ^ 3 * PFive.CdN (R ^ 2 - (1 - R * C) ^ 2) ((1 - R * C) + R)
      + 3 * PFive.pN (R ^ 2 - (1 - R * C) ^ 2) ((1 - R * C) + R)
        * PFive.DD (R ^ 2 - (1 - R * C) ^ 2) ((1 - R * C) + R) ^ 3 * S * T
      + PFive.DD (R ^ 2 - (1 - R * C) ^ 2) ((1 - R * C) + R) ^ 2 * S ^ 2
        * (2 * PFive.pN (R ^ 2 - (1 - R * C) ^ 2) ((1 - R * C) + R) ^ 2
          + 2 * PFive.DD (R ^ 2 - (1 - R * C) ^ 2) ((1 - R * C) + R) ^ 2
          + PFive.pN (R ^ 2 - (1 - R * C) ^ 2) ((1 - R * C) + R)
            * PFive.DD (R ^ 2 - (1 - R * C) ^ 2) ((1 - R * C) + R) * C) = 0 := by
  simp only [PFive.CdN, PFive.pN, PFive.DD]
  linear_combination (-16 * R * ((1 - R * C) + R) ^ 4) * htop

/-- Every solvable positive push lies on the curve at an admissible angle in `(k, 5)`. -/
lemma on_curve {μ : ℝ} {v v' : ℝ → ℝ} (h : PFiveOde.Sol 1 μ v v') (hμ : 0 < μ) :
    ∃ T, k5 < T ∧ T < 5 ∧ 0 ≤ Disc T ∧ F T = μ := by
  obtain ⟨x, hx, hx1, hG⟩ := PFiveOde.tau_link h hμ one_pos
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
  have hTime : (p0 ^ 2 + r0 ^ 2 / 2) * T0 + Real.sinh T0 * (2 * p0 * r0 + r0 ^ 2 * Real.cosh T0 / 2) = k5 := by
    unfold G5 at hG
    rw [hs, hc, hT0]; unfold k5; rw [← hG]
  have hQ : Qd T0 r0 = 0 := by
    unfold Qd aa m
    linear_combination hTime - (T0 * (p0 + 1 - r0 * Real.cosh T0) + 2 * r0 * Real.sinh T0) * hw1
  have hxx : 0 < 1 - r0 * (Real.cosh T0 - 1) := by linarith
  obtain ⟨h1, h2, h3, h4, h5⟩ := valid hT hr hxx hQ
  have hT5 : T0 < 5 := by
    by_contra hc5; push Not at hc5; linarith [H_nonneg hc5]
  refine ⟨T0, h5, hT5, by rw [h2]; positivity, ?_⟩
  have hPp : P T0 = p0 := by unfold P; rw [h3]; linarith
  unfold F; rw [h3, hPp, hp0, hr0]; field_simp; ring

/-! Step 5: assembly. -/

set_option maxHeartbeats 1000000 in
/-- **P_5 at kap = 1, end to end.** The set of pushes for which the seat `v'' = mu v^(-7/5) + v^(-3/5)`,
`v(0) = v(1) = 1` has a solution has a greatest element (the break, numerically 1.208168022773), and the break is
transcendental. -/
theorem break_end_to_end :
    ∃ μs : ℝ, IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, PFiveOde.Sol 1 μ v v'} μs ∧ Transcendental ℚ μs := by
  have hk1 := k5_gt
  have hk2 := k5_lt
  have hk5 : 5 * k5 ^ 2 = 1 := by rw [k5_sq]; norm_num
  set K := Set.Icc k5 (5 : ℝ) ∩ {T | 0 ≤ Disc T} with hKdef
  have hKc : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const Disc_cont)
  have hFc : ContinuousOn F K := fun T hT =>
    (F_contAt (lt_of_lt_of_le k5_pos hT.1.1)).continuousWithinAt
  have h1K : (1 : ℝ) ∈ K := ⟨⟨by linarith, by norm_num⟩, at_one.1⟩
  obtain ⟨Ts, hTs, hmax⟩ := hKc.exists_isMaxOn ⟨1, h1K⟩ hFc
  have hFs : 0 < F Ts := lt_of_lt_of_le at_one.2 (hmax h1K)
  obtain ⟨hR, hx, hQ⟩ := admissible hTs.1.1 hTs.2 hFs
  have hT0 : 0 < Ts := lt_of_lt_of_le k5_pos hTs.1.1
  obtain ⟨ha, hD2, -, hH, hTk⟩ := valid hT0 hR hx hQ
  have hT5 : Ts < 5 := by
    rcases eq_or_lt_of_le hTs.1.2 with h | h
    · have := H_nonneg (le_of_eq h.symm); linarith
    · exact h
  have hDpos : 0 < Disc Ts := by rw [hD2]; have : 0 < m Ts - aa Ts * R Ts := by linarith
                                 positivity
  have hwall : P Ts + R Ts * Real.cosh Ts = 1 := by unfold P; ring
  have hΦ : Φ (P Ts) (R Ts) Ts = k5 := by
    unfold Qd aa m at hQ; unfold Φ P; linear_combination hQ
  refine ⟨F Ts, ⟨?_, ?_⟩, ?_⟩
  · have hpr : 0 < P Ts + R Ts := by unfold P; linarith
    obtain ⟨v, v', hv⟩ := exists_sol hR hpr hwall hΦ hk5
    exact ⟨v, v', by unfold F at *; exact hv⟩
  · rintro μ ⟨v, v', h⟩
    rcases le_or_gt μ 0 with hμ | hμ
    · linarith
    obtain ⟨T, hTk', hT5', hD', hFT⟩ := on_curve h hμ
    rw [← hFT]
    exact hmax ⟨⟨hTk'.le, hT5'.le⟩, hD'⟩
  · have hKn : K ∈ nhds Ts := Filter.inter_mem (Icc_mem_nhds hTk hT5)
      ((Disc_cont.continuousAt.eventually (lt_mem_nhds hDpos)).mono fun y hy => le_of_lt hy)
    have hloc : IsLocalMax F Ts := hmax.isLocalMax hKn
    obtain ⟨ρ, hρ⟩ := R_hasDerivAt hT0 hDpos
    have E1 := hloc.hasDerivAt_eq_zero (F_hasDerivAt_of hρ)
    have E2 := implicit hT0 hDpos hρ
    have htop := top5 E1 E2
    have hcs := Real.cosh_sq_sub_sinh_sq Ts
    have hDn := PThreeBreak.Dn_neg hT0
    unfold PThreeBreak.Dn at hDn
    have hS0 : 0 < Real.sinh Ts := Real.sinh_pos_iff.mpr hT0
    unfold F at hFs ⊢
    unfold P at htop hΦ hFs ⊢
    unfold m aa at htop
    unfold Qd m aa at hQ
    set r := R Ts
    set C := Real.cosh Ts
    set S := Real.sinh Ts
    have hxp : 0 < (1 - r * C) + r := by linarith
    -- the switch pN = 2 p x is nonzero: p = 0 would force S = 1, C^2 = 2 and contradict sinh T < T cosh T
    have hp0 : 1 - r * C ≠ 0 := by
      intro hp
      have hrC : r * C = 1 := by linarith
      rw [hp] at htop
      have hQT : 1 - 2 * S ^ 2 * r ^ 2 = 0 := by
        have : (2 * S * (Ts * C - S) * r ^ 2 - 2 * Ts * S * r + 1) * r = 0 := by linear_combination htop
        rcases mul_eq_zero.mp this with h | h
        · linear_combination h - (2 * Ts * S * r) * hrC
        · linarith
      have hC0 : 0 < C := Real.cosh_pos Ts
      have h3 : 2 * S ^ 2 = C ^ 2 := by
        linear_combination (-(C ^ 2)) * hQT - (2 * S ^ 2 * (1 + r * C)) * hrC
      have hS2 : S ^ 2 = 1 := by linear_combination hcs + h3
      have hS1 : S = 1 := by
        have : (S - 1) * (S + 1) = 0 := by linear_combination hS2
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · linarith
      have hC2 : C ^ 2 = 2 := by linear_combination -h3 + 2 * hS2
      have hr' : r = 1 / C := by field_simp; linarith
      have hTC : Ts + C - 4 * k5 = 0 := by
        rw [hr', hS1] at hQ
        field_simp at hQ
        linear_combination hQ + 2 * k5 * hC2
      rw [hS1] at hDn
      clear_value r C S
      clear htop hQ hΦ hFs E1 E2 hx hρ
      nlinarith
    have hpN : PFive.pN (r ^ 2 - (1 - r * C) ^ 2) ((1 - r * C) + r) ≠ 0 := by
      unfold PFive.pN
      have : ((1 - r * C) + r) ^ 2 - (r ^ 2 - (1 - r * C) ^ 2) = 2 * (1 - r * C) * ((1 - r * C) + r) := by ring
      rw [this]; exact mul_ne_zero (mul_ne_zero two_ne_zero hp0) hxp.ne'
    refine PFive.class_of_crit LindemannBridge.hermite_lindemann (kap := 1) (Q := r ^ 2 - (1 - r * C) ^ 2)
      (x := (1 - r * C) + r) (T := Ts) (S := S) (C := C) (k := k5) one_pos isAlgebraic_one hFs (by ring) hxp
      hT0 hS0 hpN hk5 ?_ ?_ ?_ ?_ ?_
    · simp only [PFive.DD, PFive.CN]; ring
    · simp only [PFive.DD, PFive.S2N]
      linear_combination (-4 * ((1 - r * C) + r) ^ 2 * r ^ 2) * hcs
    · unfold Φ at hΦ
      simp only [PFive.pN, PFive.DD]
      linear_combination (8 * ((1 - r * C) + r) ^ 2) * hΦ
    · exact h2_of_top5 htop
    · rw [← Real.cosh_add_sinh]

end PFiveBreak
