import Mathlib
import Mistranslation.Breaks

/-! # MEMS pull-in (k = 2) from the ODE (2026-10-23)

Seat `x'' + mu / (1 - x)^2 = 0`, `x(0) = x(1) = 0`; with `v = 1 - x`: `v'' = mu / v^2`, `v(0) = v(1) = 1`.
Goal: every positive solution has `mu = 8 (T/2 + sinh 2T / 4)^2 / cosh^6 T` for some `T >= 0`
(the one formula of docs/BREAK_LADDERS_2026-10-23.md, p = 1), derived with no integral:
the clock `G = theta/2 + sinh(2 theta)/4`, `v = m cosh^2 theta`, runs linearly in t.
Step 1: energy, the lowest point (Rolle), and the sign of v' on either side. -/

namespace MemsOde

def Sol (μ : ℝ) (v v' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < v t ∧ HasDerivAt v (v' t) t ∧ HasDerivAt v' (μ / v t ^ 2) t) ∧
    v 0 = 1 ∧ v 1 = 1

lemma const_on {a b : ℝ} {f : ℝ → ℝ} (h : ∀ t ∈ Set.Icc a b, HasDerivAt f 0 t) :
    ∀ t ∈ Set.Icc a b, f t = f a := by
  apply constant_of_has_deriv_right_zero
  · intro t ht; exact (h t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (h t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt

/-- Energy `v'^2 + 2 mu / v` is conserved on [0,1]. -/
lemma energy {μ : ℝ} {v v' : ℝ → ℝ} (h : Sol μ v v') :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, v' t * v' t + 2 * μ * (v t)⁻¹ = v' 0 * v' 0 + 2 * μ * (v 0)⁻¹ := by
  refine const_on (f := fun t => v' t * v' t + 2 * μ * (v t)⁻¹) ?_
  intro s hs
  obtain ⟨hv, hd, hdd⟩ := h.1 s hs
  convert (hdd.mul hdd).add ((hd.inv hv.ne').const_mul (2 * μ)) using 1
  field_simp
  ring

/-- There is an interior lowest point where `v' = 0` (Rolle). -/
lemma rolle {μ : ℝ} {v v' : ℝ → ℝ} (h : Sol μ v v') : ∃ t0 ∈ Set.Ioo (0 : ℝ) 1, v' t0 = 0 := by
  have hc : ContinuousOn v (Set.Icc 0 1) := fun t ht => (h.1 t ht).2.1.continuousAt.continuousWithinAt
  exact exists_hasDerivAt_eq_zero (by norm_num) hc (by rw [h.2.1, h.2.2])
    (fun t ht => (h.1 t (Set.Ioo_subset_Icc_self ht)).2.1)

/-- For `mu > 0`, `v'` is strictly increasing, so `v' > 0` right of `t0` and `v' < 0` left of it. -/
lemma vprime_pos {μ : ℝ} {v v' : ℝ → ℝ} (h : Sol μ v v') (hμ : 0 < μ) {t0 t : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hlt : t0 < t) : v' t0 < v' t := by
  have hsub : Set.Icc t0 t ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc ht0.1 ht.2
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope v' (fun s => μ / v s ^ 2) hlt
    (fun s hs => (h.1 s (hsub hs)).2.2.continuousAt.continuousWithinAt)
    (fun s hs => (h.1 s (hsub (Set.Ioo_subset_Icc_self hs))).2.2)
  have hvc := (h.1 c (hsub (Set.Ioo_subset_Icc_self hc))).1
  have hpos : 0 < μ / v c ^ 2 := by positivity
  rw [hslope] at hpos
  have := (div_pos_iff_of_pos_right (sub_pos.mpr hlt)).mp hpos
  linarith

/-! Step 2: the clock `G m v = (arsinh s + c s) / 2`, `s = sqrt (v/m - 1)` (= sinh theta), `c = sqrt (v/m)`
(= cosh theta), i.e. `G = theta/2 + sinh(2 theta)/4` with `v = m cosh^2 theta`. -/

noncomputable def G (m x : ℝ) : ℝ :=
  (Real.arsinh (Real.sqrt (x / m - 1)) + Real.sqrt (x / m) * Real.sqrt (x / m - 1)) / 2

/-- Chain rule for the clock along `v`, at a point where `v > m > 0`. -/
lemma clock_hasDerivAt {m : ℝ} {v : ℝ → ℝ} {w t : ℝ} (hm : 0 < m) (hvt : m < v t)
    (hd : HasDerivAt v w t) :
    HasDerivAt (fun s => G m (v s))
      (Real.sqrt (v t / m) * w / (2 * m * Real.sqrt (v t / m - 1))) t := by
  have hq : 0 < v t / m - 1 := by rw [sub_pos, one_lt_div hm]; exact hvt
  have hc : 0 < v t / m := by linarith
  have hqd : HasDerivAt (fun s => v s / m - 1) (w / m) t := (hd.div_const m).sub_const 1
  have hcd : HasDerivAt (fun s => v s / m) (w / m) t := hd.div_const m
  have hS := hqd.sqrt hq.ne'
  have hC := hcd.sqrt hc.ne'
  have hA := hS.arsinh
  have := (hA.add (hC.mul hS)).div_const 2
  convert this using 1
  · funext s; simp only [G, Pi.add_apply, Pi.mul_apply]
  have hS2 : Real.sqrt (v t / m - 1) ^ 2 = v t / m - 1 := Real.sq_sqrt hq.le
  have hC2 : Real.sqrt (v t / m) ^ 2 = v t / m := Real.sq_sqrt hc.le
  have h1s : Real.sqrt (1 + Real.sqrt (v t / m - 1) ^ 2) = Real.sqrt (v t / m) := by
    rw [hS2]; ring_nf
  rw [h1s]
  have hSp : 0 < Real.sqrt (v t / m - 1) := Real.sqrt_pos.mpr hq
  have hCp : 0 < Real.sqrt (v t / m) := Real.sqrt_pos.mpr hc
  generalize Real.sqrt (v t / m - 1) = S at hS2 hSp ⊢
  generalize Real.sqrt (v t / m) = C at hC2 hCp ⊢
  simp only [smul_eq_mul]
  field_simp
  have hCS : C ^ 2 = 1 + S ^ 2 := by rw [hC2, hS2]; ring
  linear_combination w * hCS

/-- On the energy shell `w^2 = 2 mu (1/m - 1/v)`, the clock speed is `+- sqrt(2 mu / m) / (2 m)`. -/
lemma clock_speed {μ m x w : ℝ} (hm : 0 < m) (hx : m < x) (hμ : 0 < μ)
    (hE : w * w = 2 * μ * (m⁻¹ - x⁻¹)) :
    (Real.sqrt (x / m) * w / (2 * m * Real.sqrt (x / m - 1))) ^ 2
      = (Real.sqrt (2 * μ / m) / (2 * m)) ^ 2 := by
  have hq : 0 < x / m - 1 := by rw [sub_pos, one_lt_div hm]; exact hx
  have hc : 0 < x / m := by linarith
  have hx0 : 0 < x := by linarith
  rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hq.le,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * μ / m), sq w]
  rw [hE]
  field_simp

/-! Step 3: run the clock up both sides of the lowest point. -/

lemma G_self {m : ℝ} (hm : 0 < m) : G m m = 0 := by simp [G, div_self hm.ne']

lemma G_cont (m : ℝ) : Continuous (G m) := by
  unfold G
  exact ((Real.continuous_arsinh.comp ((continuous_id.div_const m).sub continuous_const).sqrt).add
    ((continuous_id.div_const m).sqrt.mul ((continuous_id.div_const m).sub continuous_const).sqrt)).div_const 2

lemma vcont {μ : ℝ} {v v' : ℝ → ℝ} (h : Sol μ v v') {a b : ℝ} (hab : Set.Icc a b ⊆ Set.Icc 0 1) :
    ContinuousOn v (Set.Icc a b) := fun t ht => (h.1 t (hab ht)).2.1.continuousAt.continuousWithinAt

/-- Energy shell measured from the lowest point. -/
lemma shell {μ : ℝ} {v v' : ℝ → ℝ} (h : Sol μ v v') {t0 : ℝ} (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1)
    (hz : v' t0 = 0) : ∀ t ∈ Set.Icc (0 : ℝ) 1, v' t * v' t = 2 * μ * ((v t0)⁻¹ - (v t)⁻¹) := by
  intro t ht
  have h1 := energy h t ht
  have h2 := energy h t0 ht0
  rw [hz] at h2
  linear_combination h1 - h2

/-- Away from the lowest point, `v` is strictly above it. -/
lemma above {μ : ℝ} {v v' : ℝ → ℝ} (h : Sol μ v v') (hμ : 0 < μ) {t0 s : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hz : v' t0 = 0) (hne : s ≠ t0) :
    v t0 < v s := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope v v' hlt
      (vcont h (Set.Icc_subset_Icc hs.1 ht0.2))
      (fun x hx => (h.1 x (Set.Icc_subset_Icc hs.1 ht0.2 (Set.Ioo_subset_Icc_self hx))).2.1)
    have hneg : v' c < 0 := by
      have := vprime_pos h hμ (Set.Icc_subset_Icc hs.1 ht0.2 (Set.Ioo_subset_Icc_self hc)) ht0 hc.2
      linarith
    rw [hsl] at hneg
    have := (div_neg_iff.mp hneg)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith [sub_pos.mpr hc.1, sub_pos.mpr hlt]
    · linarith
  · obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope v v' hlt
      (vcont h (Set.Icc_subset_Icc ht0.1 hs.2))
      (fun x hx => (h.1 x (Set.Icc_subset_Icc ht0.1 hs.2 (Set.Ioo_subset_Icc_self hx))).2.1)
    have hpos : 0 < v' c := by
      have := vprime_pos h hμ ht0 (Set.Icc_subset_Icc ht0.1 hs.2 (Set.Ioo_subset_Icc_self hc)) hc.1
      linarith
    rw [hsl] at hpos
    have := (div_pos_iff_of_pos_right (sub_pos.mpr hlt)).mp hpos
    linarith

lemma pos_of_sq_eq {D K : ℝ} (hD : 0 < D) (hK : 0 < K) (h : D ^ 2 = K ^ 2) : D = K := by nlinarith

/-- The clock runs at speed exactly `+K` right of the lowest point and `-K` left of it. -/
lemma clock_rate {μ : ℝ} {v v' : ℝ → ℝ} (h : Sol μ v v') (hμ : 0 < μ) {t0 s : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hz : v' t0 = 0) (hne : s ≠ t0) :
    HasDerivAt (fun x => G (v t0) (v x))
      ((if t0 < s then 1 else -1) * (Real.sqrt (2 * μ / v t0) / (2 * v t0))) s := by
  have hm : 0 < v t0 := (h.1 t0 ht0).1
  have hab := above h hμ ht0 hs hz hne
  have hd := (h.1 s hs).2.1
  have hD := clock_hasDerivAt hm hab hd
  have hsp := clock_speed hm hab hμ (shell h ht0 hz s hs)
  have hq : 0 < v s / v t0 - 1 := by rw [sub_pos, one_lt_div hm]; exact hab
  have hc : 0 < v s / v t0 := by linarith
  have hK : 0 < Real.sqrt (2 * μ / v t0) / (2 * v t0) := by
    have : 0 < Real.sqrt (2 * μ / v t0) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hS := Real.sqrt_pos.mpr hq
  have hC := Real.sqrt_pos.mpr hc
  split_ifs with hlt
  · have hw : 0 < v' s := by have := vprime_pos h hμ ht0 hs hlt; linarith
    convert hD using 1
    rw [one_mul]
    exact (pos_of_sq_eq (by positivity) hK hsp).symm
  · have hlt' : s < t0 := lt_of_le_of_ne (not_lt.mp hlt) hne
    have hw : v' s < 0 := by have := vprime_pos h hμ hs ht0 hlt'; linarith
    convert hD using 1
    have hneg : 0 < -(Real.sqrt (v s / v t0) * v' s / (2 * v t0 * Real.sqrt (v s / v t0 - 1))) := by
      rw [neg_pos]
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hC hw) (by positivity)
    have := pos_of_sq_eq hneg hK (by rw [neg_sq]; exact hsp)
    linarith

/-- Right half: the clock gains `K (1 - t0)` between the lowest point and t = 1. -/
lemma half_right {μ : ℝ} {v v' : ℝ → ℝ} (h : Sol μ v v') (hμ : 0 < μ) {t0 : ℝ}
    (ht0 : t0 ∈ Set.Ioo (0 : ℝ) 1) (hz : v' t0 = 0) :
    G (v t0) (v 1) = G (v t0) (v t0) + Real.sqrt (2 * μ / v t0) / (2 * v t0) * (1 - t0) := by
  set K := Real.sqrt (2 * μ / v t0) / (2 * v t0)
  have ht0' := Set.Ioo_subset_Icc_self ht0
  have hsub : Set.Icc t0 1 ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc ht0.1.le le_rfl
  obtain ⟨c, _, hsl⟩ := exists_hasDerivAt_eq_slope (fun x => G (v t0) (v x) - K * x) (fun _ => (0 : ℝ))
    ht0.2 (((G_cont _).comp_continuousOn (vcont h hsub)).sub (continuousOn_const.mul continuousOn_id))
    (fun s hs => by
      have hr := clock_rate h hμ ht0' (hsub (Set.Ioo_subset_Icc_self hs)) hz (ne_of_gt hs.1)
      rw [if_pos hs.1, one_mul] at hr
      convert hr.sub ((hasDerivAt_id' s).const_mul K) using 1
      simp [K])
  have hne : (1 : ℝ) - t0 ≠ 0 := by linarith [ht0.2]
  field_simp at hsl
  linarith

/-- Left half: the clock gains `K t0` between the lowest point and t = 0. -/
lemma half_left {μ : ℝ} {v v' : ℝ → ℝ} (h : Sol μ v v') (hμ : 0 < μ) {t0 : ℝ}
    (ht0 : t0 ∈ Set.Ioo (0 : ℝ) 1) (hz : v' t0 = 0) :
    G (v t0) (v 0) = G (v t0) (v t0) + Real.sqrt (2 * μ / v t0) / (2 * v t0) * t0 := by
  set K := Real.sqrt (2 * μ / v t0) / (2 * v t0)
  have ht0' := Set.Ioo_subset_Icc_self ht0
  have hsub : Set.Icc 0 t0 ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc le_rfl ht0.2.le
  obtain ⟨c, _, hsl⟩ := exists_hasDerivAt_eq_slope (fun x => G (v t0) (v x) + K * x) (fun _ => (0 : ℝ))
    ht0.1 (((G_cont _).comp_continuousOn (vcont h hsub)).add (continuousOn_const.mul continuousOn_id))
    (fun s hs => by
      have hr := clock_rate h hμ ht0' (hsub (Set.Ioo_subset_Icc_self hs)) hz (ne_of_lt hs.2)
      rw [if_neg (not_lt.mpr hs.2.le)] at hr
      convert hr.add ((hasDerivAt_id' s).const_mul K) using 1
      simp [K])
  have hne : t0 - 0 ≠ 0 := by linarith [ht0.1]
  field_simp at hsl
  linarith

/-- **Every MEMS solution sits on the one formula**: `mu = 8 (T/2 + sinh 2T / 4)^2 / cosh^6 T`
for some `T >= 0`. Derived from the ODE alone; no integral, no assumed critical equation. -/
theorem mems_mu_formula {μ : ℝ} {v v' : ℝ → ℝ} (h : Sol μ v v') (hμ : 0 < μ) :
    ∃ T : ℝ, 0 ≤ T ∧ μ = 8 * (T / 2 + Real.sinh (2 * T) / 4) ^ 2 / Real.cosh T ^ 6 := by
  obtain ⟨t0, ht0, hz⟩ := rolle h
  have ht0' := Set.Ioo_subset_Icc_self ht0
  have hR := half_right h hμ ht0 hz
  have hL := half_left h hμ ht0 hz
  have hm : 0 < v t0 := (h.1 t0 ht0').1
  have hm1 : v t0 < 1 := by
    have := above h hμ ht0' ⟨zero_le_one, le_rfl⟩ hz (ne_of_gt ht0.2); rwa [h.2.2] at this
  rw [h.2.2, G_self hm] at hR
  rw [h.2.1, G_self hm] at hL
  set m := v t0 with hmdef
  set K := Real.sqrt (2 * μ / m) / (2 * m) with hKdef
  have hK2 : K ^ 2 = 2 * μ / m / (4 * m ^ 2) := by
    rw [hKdef, div_pow, Real.sq_sqrt (by positivity)]; ring
  have hG1 : G m 1 = K / 2 := by linarith
  have hx : 0 ≤ 1 / m - 1 := by rw [sub_nonneg, le_div_iff₀ hm]; linarith
  set x := Real.sqrt (1 / m - 1) with hxdef
  have hx2 : x ^ 2 = 1 / m - 1 := Real.sq_sqrt hx
  refine ⟨Real.arsinh x, Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg _), ?_⟩
  have hsh : Real.sinh (Real.arsinh x) = x := Real.sinh_arsinh x
  have hch : Real.cosh (Real.arsinh x) = Real.sqrt (1 / m) := by
    rw [Real.cosh_arsinh, hx2]; congr 1; ring
  have hc2 : Real.sqrt (1 / m) ^ 2 = 1 / m := Real.sq_sqrt (by positivity)
  have hGdef : G m 1 = (Real.arsinh x + Real.sqrt (1 / m) * x) / 2 := by
    simp only [G, hxdef]
  rw [Real.sinh_two_mul, hsh, hch]
  have key : Real.arsinh x / 2 + 2 * x * Real.sqrt (1 / m) / 4 = K / 2 := by
    rw [← hG1, hGdef]; ring
  rw [key]
  have h6 : Real.sqrt (1 / m) ^ 6 = (1 / m) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hc2]
  rw [h6]
  field_simp
  field_simp at hK2
  nlinarith [hK2]

/-! Step 4: the formula's maximum sits at the MEMS critical equation. -/

noncomputable def F (T : ℝ) : ℝ := 8 * (T / 2 + Real.sinh (2 * T) / 4) ^ 2 / Real.cosh T ^ 6

noncomputable def hc (T : ℝ) : ℝ := Real.cosh T * (2 - Real.sinh T ^ 2) - 3 * T * Real.sinh T

lemma I_hasDerivAt (T : ℝ) :
    HasDerivAt (fun T => T / 2 + Real.sinh (2 * T) / 4) (Real.cosh T ^ 2) T := by
  have h2 := ((Real.hasDerivAt_sinh (2 * T)).comp T ((hasDerivAt_id T).const_mul 2)).div_const 4
  convert ((hasDerivAt_id T).div_const 2).add h2 using 1
  · funext x; simp [Function.comp]
  rw [Real.cosh_two_mul, Real.cosh_sq]
  ring

lemma F_hasDerivAt (T : ℝ) :
    HasDerivAt F (8 * (T / 2 + Real.sinh (2 * T) / 4) * hc T / Real.cosh T ^ 7) T := by
  have hc0 : Real.cosh T ≠ 0 := (Real.cosh_pos T).ne'
  have := (((I_hasDerivAt T).pow 2).const_mul 8).div ((Real.hasDerivAt_cosh T).pow 6) (pow_ne_zero 6 hc0)
  convert this using 1
  · funext x; simp [F]
  simp only [Pi.pow_apply, hc]
  have hcs := Real.cosh_sq T
  rw [div_eq_div_iff (by positivity) (by positivity)]
  norm_num
  rw [Real.sinh_two_mul]
  linear_combination (-16 * (T / 2 + 2 * Real.sinh T * Real.cosh T / 4) * Real.cosh T ^ 13) * hcs

lemma hc_hasDerivAt (T : ℝ) :
    HasDerivAt hc (-3 * (Real.sinh T ^ 3 + Real.sinh T + T * Real.cosh T)) T := by
  have := ((Real.hasDerivAt_cosh T).mul ((hasDerivAt_const T (2 : ℝ)).sub ((Real.hasDerivAt_sinh T).pow 2))).sub
    (((hasDerivAt_id T).const_mul 3).mul (Real.hasDerivAt_sinh T))
  convert this using 1
  · funext x; simp [hc]
  have hcs := Real.cosh_sq T
  simp only [id]
  norm_num
  linear_combination (2 * Real.sinh T : ℝ) * hcs

lemma hc_strictAnti : StrictAntiOn hc (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact fun x _ => (hc_hasDerivAt x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hc_hasDerivAt x).deriv]
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
    have hc' : 0 < Real.cosh x := Real.cosh_pos x
    have : 0 < x * Real.cosh x := mul_pos hx hc'
    nlinarith [pow_pos hs 3]

lemma I_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ T / 2 + Real.sinh (2 * T) / 4 := by
  have : 0 ≤ Real.sinh (2 * T) := Real.sinh_nonneg_iff.mpr (by linarith)
  positivity

/-- The formula peaks where the MEMS critical equation holds. -/
lemma F_le_max {Ts : ℝ} (hTs : 0 < Ts) (hcrit : hc Ts = 0) : ∀ T, 0 ≤ T → F T ≤ F Ts := by
  intro T hT
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun x => (F_hasDerivAt x).continuousAt
  have hFd : Differentiable ℝ F := fun x => (F_hasDerivAt x).differentiableAt
  rcases le_total T Ts with hle | hge
  · have hmono : MonotoneOn F (Set.Icc 0 Ts) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 Ts) hFc.continuousOn hFd.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      rw [(F_hasDerivAt x).deriv]
      have hpos : 0 < hc x := by
        have := hc_strictAnti (Set.mem_Ici.mpr hx.1.le) (Set.mem_Ici.mpr hTs.le) hx.2
        linarith
      have := I_nonneg hx.1.le
      have := Real.cosh_pos x
      positivity
    exact hmono ⟨hT, hle⟩ ⟨hTs.le, le_rfl⟩ hle
  · have hanti : AntitoneOn F (Set.Ici Ts) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici Ts) hFc.continuousOn hFd.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [(F_hasDerivAt x).deriv]
      have hneg : hc x < 0 := by
        have := hc_strictAnti (Set.mem_Ici.mpr hTs.le) (Set.mem_Ici.mpr (hTs.le.trans hx.le)) hx
        linarith
      have hI := I_nonneg (hTs.le.trans hx.le)
      have hc7 := pow_pos (Real.cosh_pos x) 7
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hc7.le
    exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hge) hge

/-- At the critical point the formula equals `8 / (9 sinh^2 Ts)` (the form used in Breaks.lean). -/
lemma F_at_crit {Ts : ℝ} (hTs : 0 < Ts) (hcrit : hc Ts = 0) : F Ts = 8 / (9 * Real.sinh Ts ^ 2) := by
  have hs : 0 < Real.sinh Ts := Real.sinh_pos_iff.mpr hTs
  have hc' : 0 < Real.cosh Ts := Real.cosh_pos Ts
  have hcs := Real.cosh_sq Ts
  have hI : Ts / 2 + Real.sinh (2 * Ts) / 4 = Real.cosh Ts ^ 3 / (3 * Real.sinh Ts) := by
    rw [Real.sinh_two_mul, eq_div_iff (by positivity)]
    simp only [hc] at hcrit
    linear_combination (-1 / 2 : ℝ) * hcrit - (Real.cosh Ts : ℝ) * hcs
  simp only [F]
  rw [hI]
  field_simp
  ring

/-- **MEMS bound from the ODE**: every push with a solution is at most `8 / (9 sinh^2 Ts)`, where `Ts > 0`
solves the critical equation `cosh T (2 - sinh^2 T) = 3 T sinh T`. -/
theorem mems_break_le {μ : ℝ} {v v' : ℝ → ℝ} (h : Sol μ v v') {Ts : ℝ} (hTs : 0 < Ts)
    (hcrit : Real.cosh Ts * (2 - Real.sinh Ts ^ 2) = 3 * Ts * Real.sinh Ts) :
    μ ≤ 8 / (9 * Real.sinh Ts ^ 2) := by
  have hcz : hc Ts = 0 := by simp only [hc]; linarith
  rcases le_or_gt μ 0 with hμ | hμ
  · have : 0 < 8 / (9 * Real.sinh Ts ^ 2) := by
      have := Real.sinh_pos_iff.mpr hTs; positivity
    linarith
  · obtain ⟨T, hT, hμT⟩ := mems_mu_formula h hμ
    rw [← F_at_crit hTs hcz, hμT]
    exact F_le_max hTs hcz T hT

/-! Step 5: existence -- every value of the formula is attained (run the clock backwards). -/

noncomputable def φ (T : ℝ) : ℝ := T / 2 + Real.sinh (2 * T) / 4

lemma φ_hasDerivAt (x : ℝ) : HasDerivAt φ (Real.cosh x ^ 2) x := I_hasDerivAt x

lemma φ_strictMono : StrictMono φ := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(φ_hasDerivAt x).deriv]
  exact pow_pos (Real.cosh_pos x) 2

lemma φ_cont : Continuous φ := continuous_iff_continuousAt.mpr fun x => (φ_hasDerivAt x).continuousAt

lemma φ_neg (T : ℝ) : φ (-T) = -φ T := by simp [φ, mul_neg, Real.sinh_neg]; ring

lemma φ_surj : Function.Surjective φ := by
  apply φ_cont.surjective
  · apply Filter.tendsto_atTop_mono' Filter.atTop _ (Filter.tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2))
    filter_upwards [Filter.eventually_ge_atTop 0] with x hx
    have : 0 ≤ Real.sinh (2 * x) := Real.sinh_nonneg_iff.mpr (by linarith)
    simp only [φ, id]; linarith
  · apply Filter.tendsto_atBot_mono' Filter.atBot _ (Filter.tendsto_id.atBot_div_const (by norm_num : (0:ℝ) < 2))
    filter_upwards [Filter.eventually_le_atBot 0] with x hx
    have : Real.sinh (2 * x) ≤ 0 := Real.sinh_nonpos_iff.mpr (by linarith)
    simp only [φ, id]; linarith

noncomputable def ψ : ℝ → ℝ := (StrictMono.orderIsoOfSurjective φ φ_strictMono φ_surj).symm

lemma φ_ψ (y : ℝ) : φ (ψ y) = y :=
  (StrictMono.orderIsoOfSurjective φ φ_strictMono φ_surj).apply_symm_apply y

lemma ψ_φ (x : ℝ) : ψ (φ x) = x :=
  (StrictMono.orderIsoOfSurjective φ φ_strictMono φ_surj).symm_apply_apply x

lemma ψ_hasDerivAt (y : ℝ) : HasDerivAt ψ (Real.cosh (ψ y) ^ 2)⁻¹ y := by
  have hc : Continuous ψ := (StrictMono.orderIsoOfSurjective φ φ_strictMono φ_surj).symm.continuous
  exact HasDerivAt.of_local_left_inverse hc.continuousAt (φ_hasDerivAt (ψ y))
    (pow_pos (Real.cosh_pos _) 2).ne' (Filter.Eventually.of_forall φ_ψ)

/-- For every `T`, the formula value `F T` is attained by an explicit solution. -/
theorem mems_exists (T : ℝ) :
    Sol (F T) (fun t => Real.cosh (ψ (2 * φ T * (t - 1 / 2))) ^ 2 / Real.cosh T ^ 2)
      (fun t => 2 * (2 * φ T) * Real.sinh (ψ (2 * φ T * (t - 1 / 2))) /
        (Real.cosh (ψ (2 * φ T * (t - 1 / 2))) * Real.cosh T ^ 2)) := by
  set K := 2 * φ T with hK
  have hcT : 0 < Real.cosh T := Real.cosh_pos T
  have hθ : ∀ t : ℝ, HasDerivAt (fun t => ψ (K * (t - 1 / 2)))
      ((Real.cosh (ψ (K * (t - 1 / 2))) ^ 2)⁻¹ * K) t := by
    intro t
    have := (ψ_hasDerivAt (K * (t - 1 / 2))).comp t (((hasDerivAt_id t).sub_const (1 / 2)).const_mul K)
    exact this.congr_deriv (by simp)
  refine ⟨fun t _ => ⟨by positivity, ?_, ?_⟩, ?_, ?_⟩
  · -- v' = d/dt [cosh^2 theta / cosh^2 T]
    have := (((Real.hasDerivAt_cosh _).comp t (hθ t)).pow 2).div_const (Real.cosh T ^ 2)
    refine this.congr_deriv ?_
    have hc0 := (Real.cosh_pos (ψ (K * (t - 1 / 2)))).ne'
    simp only [Function.comp, Pi.pow_apply]
    field_simp
    ring
  · -- v'' = mu / v^2
    have hc0 := Real.cosh_pos (ψ (K * (t - 1 / 2)))
    have := ((((Real.hasDerivAt_sinh _).comp t (hθ t)).const_mul (2 * K)).div
      (((Real.hasDerivAt_cosh _).comp t (hθ t)).mul_const (Real.cosh T ^ 2))
      (by positivity : Real.cosh (ψ (K * (t - 1 / 2))) * Real.cosh T ^ 2 ≠ 0))
    refine this.congr_deriv ?_
    have hcs := Real.cosh_sq (ψ (K * (t - 1 / 2)))
    simp only [F, Function.comp]
    rw [show T / 2 + Real.sinh (2 * T) / 4 = K / 2 by rw [hK]; simp [φ]]
    field_simp
    have hcs2 := Real.cosh_sq (ψ (K * (2 * t - 1) / 2))
    linear_combination (32 * φ T ^ 2 : ℝ) * hcs2
  · simp only
    rw [show K * (0 - 1 / 2) = -φ T by rw [hK]; ring, ← φ_neg, ψ_φ, Real.cosh_neg]
    field_simp
  · simp only
    rw [show K * (1 - 1 / 2) = φ T by rw [hK]; ring, ψ_φ]
    field_simp

/-! Step 6: assemble. -/

/-- The critical equation has a root in (0, 1) (IVT; hc 0 = 2, hc 1 < 0 from e's decimal bounds). -/
lemma crit_root : ∃ Ts ∈ Set.Ioo (0 : ℝ) 1, hc Ts = 0 := by
  have hcont : ContinuousOn hc (Set.Icc 0 1) := fun x _ => (hc_hasDerivAt x).continuousAt.continuousWithinAt
  have h0 : hc 0 = 2 := by simp [hc]
  have h1 : hc 1 < 0 := by
    have he1 := Real.exp_one_gt_d9
    have he2 := Real.exp_one_lt_d9
    have hinv : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    have hpos : 0 < Real.exp (-1) := Real.exp_pos _
    simp only [hc, Real.sinh_eq, Real.cosh_eq, mul_one]
    nlinarith [hinv, hpos, he1, he2, mul_pos hpos hpos]
  obtain ⟨Ts, hTs, hz⟩ := intermediate_value_Ioo' (by norm_num : (0 : ℝ) ≤ 1) hcont
    (show (0 : ℝ) ∈ Set.Ioo (hc 1) (hc 0) by rw [h0]; exact ⟨h1, two_pos⟩)
  exact ⟨Ts, hTs, hz⟩

/-- **MEMS pull-in, exact, from the ODE**: the largest push with a solution is `8 / (9 sinh^2 Ts)`. -/
theorem mems_break_exact {Ts : ℝ} (hTs : 0 < Ts)
    (hcrit : Real.cosh Ts * (2 - Real.sinh Ts ^ 2) = 3 * Ts * Real.sinh Ts) :
    IsGreatest {μ | ∃ v v' : ℝ → ℝ, Sol μ v v'} (8 / (9 * Real.sinh Ts ^ 2)) := by
  have hcz : hc Ts = 0 := by simp only [hc]; linarith
  exact ⟨⟨_, _, by rw [← F_at_crit hTs hcz]; exact mems_exists Ts⟩, fun μ ⟨_, _, h⟩ => mems_break_le h hTs hcrit⟩

/-- **End to end**: the MEMS pull-in number (largest push with a solution, from the ODE) exists and is
transcendental, given Hermite-Lindemann. -/
theorem mems_break_end_to_end (HL : Breaks.HermiteLindemann) :
    ∃ B : ℝ, IsGreatest {μ | ∃ v v' : ℝ → ℝ, Sol μ v v'} B ∧ Transcendental ℚ B := by
  obtain ⟨Ts, hTs, hz⟩ := crit_root
  have hcrit : Real.cosh Ts * (2 - Real.sinh Ts ^ 2) = 3 * Ts * Real.sinh Ts := by
    simp only [hc] at hz; linarith
  exact ⟨_, mems_break_exact hTs.1 hcrit, Breaks.mems_break_transcendental HL Ts hTs.1 hcrit⟩

end MemsOde
