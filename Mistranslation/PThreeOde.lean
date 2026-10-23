import Mathlib
import Mistranslation.KeplerOde

/-! # P_3 pair from the ODE: the time condition (2026-10-23)

Seat `v'' = mu v^(-5/3) + kap v^(-1/3)`, `v(0) = v(1) = 1`, `v > 0`, `kap, mu > 0`. With the cube root
`c = v^(1/3)` and `u = c^2 = v^(2/3)`, energy `v'^2 + 3 mu / u - 3 kap u` is conserved, and on the shell
`(u u')^2 = (4 kap / 3) ((u - p)^2 - r^2)` with turning point `x = u(t0)`, `q = mu / kap`, `p = (x - q/x)/2`,
`r = (x + q/x)/2`. So the Kepler clock `Gk p r u = p arcosh((u-p)/r) + r sqrt(((u-p)/r)^2 - 1)` runs at constant
speed `sqrt(4 kap / 3)`; running it up both halves gives `t0 = 1/2` and `Gk p r 1 = sqrt(kap/3)`, which in the
variables of `PThree.class_of_crit` is the time condition `(x^2 - q) T + (x^2 + q) S = 2 k x`. -/

namespace PThreeOde

open KeplerOde

def Sol (κ μ : ℝ) (v v' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < v t ∧ HasDerivAt v (v' t) t ∧
      HasDerivAt v' (μ * v t ^ (-(5 / 3 : ℝ)) + κ * v t ^ (-(1 / 3 : ℝ))) t) ∧ v 0 = 1 ∧ v 1 = 1

/-! Step 0: the cube root. -/

lemma cr_pos {v : ℝ} (hv : 0 < v) : 0 < v ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hv _

lemma cr_pow {v : ℝ} (hv : 0 < v) (a : ℝ) (n : ℕ) (ha : a = (1 / 3 : ℝ) * n) :
    v ^ a = (v ^ (1 / 3 : ℝ)) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le, ha]

lemma cr_npow {v : ℝ} (hv : 0 < v) (a : ℝ) (n : ℕ) (ha : a = -((1 / 3 : ℝ) * n)) :
    v ^ a = ((v ^ (1 / 3 : ℝ)) ^ n)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le, ← Real.rpow_neg hv.le, ha]

lemma cr_cube {v : ℝ} (hv : 0 < v) : (v ^ (1 / 3 : ℝ)) ^ 3 = v := by
  rw [← cr_pow hv 1 3 (by norm_num), Real.rpow_one]

lemma cr_hasDerivAt {v : ℝ → ℝ} {w t : ℝ} (hv : 0 < v t) (hd : HasDerivAt v w t) :
    HasDerivAt (fun s => v s ^ (1 / 3 : ℝ)) (w / (3 * (v t ^ (1 / 3 : ℝ)) ^ 2)) t := by
  have := hd.rpow_const (p := 1 / 3) (Or.inl hv.ne')
  refine this.congr_deriv ?_
  rw [cr_npow hv _ 2 (by norm_num)]
  field_simp

/-! Step 1: energy, lowest point, sign of v'. -/

lemma rhs_eq {μ κ v : ℝ} (hv : 0 < v) :
    μ * v ^ (-(5 / 3 : ℝ)) + κ * v ^ (-(1 / 3 : ℝ))
      = μ * ((v ^ (1 / 3 : ℝ)) ^ 5)⁻¹ + κ * ((v ^ (1 / 3 : ℝ)) ^ 1)⁻¹ := by
  rw [cr_npow hv (-(5 / 3 : ℝ)) 5 (by norm_num), cr_npow hv (-(1 / 3 : ℝ)) 1 (by norm_num)]

lemma energy {κ μ : ℝ} {v v' : ℝ → ℝ} (h : Sol κ μ v v') :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, v' t * v' t + 3 * μ * ((v t ^ (1 / 3 : ℝ)) ^ 2)⁻¹ - 3 * κ * (v t ^ (1 / 3 : ℝ)) ^ 2
      = v' 0 * v' 0 + 3 * μ * ((v 0 ^ (1 / 3 : ℝ)) ^ 2)⁻¹ - 3 * κ * (v 0 ^ (1 / 3 : ℝ)) ^ 2 := by
  refine MemsOde.const_on (f := fun t => v' t * v' t + 3 * μ * ((v t ^ (1 / 3 : ℝ)) ^ 2)⁻¹
    - 3 * κ * (v t ^ (1 / 3 : ℝ)) ^ 2) ?_
  intro s hs
  obtain ⟨hv, hd, hdd⟩ := h.1 s hs
  have hc := cr_pos hv
  have hcd := cr_hasDerivAt hv hd
  have hc2 : (v s ^ (1 / 3 : ℝ)) ^ 2 ≠ 0 := by positivity
  have := ((hdd.mul hdd).add (((hcd.pow 2).inv hc2).const_mul (3 * μ))).sub ((hcd.pow 2).const_mul (3 * κ))
  refine this.congr_deriv ?_
  simp only [Pi.pow_apply]
  rw [rhs_eq hv]
  generalize v s ^ (1 / 3 : ℝ) = c at hc ⊢
  field_simp
  ring

lemma rolle {κ μ : ℝ} {v v' : ℝ → ℝ} (h : Sol κ μ v v') : ∃ t0 ∈ Set.Ioo (0 : ℝ) 1, v' t0 = 0 := by
  have hc : ContinuousOn v (Set.Icc 0 1) := fun t ht => (h.1 t ht).2.1.continuousAt.continuousWithinAt
  exact exists_hasDerivAt_eq_zero (by norm_num) hc (by rw [h.2.1, h.2.2])
    (fun t ht => (h.1 t (Set.Ioo_subset_Icc_self ht)).2.1)

lemma vprime_pos {κ μ : ℝ} {v v' : ℝ → ℝ} (h : Sol κ μ v v') (hμ : 0 < μ) (hκ : 0 < κ) {t0 t : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hlt : t0 < t) : v' t0 < v' t := by
  have hsub : Set.Icc t0 t ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc ht0.1 ht.2
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope v'
    (fun s => μ * v s ^ (-(5 / 3 : ℝ)) + κ * v s ^ (-(1 / 3 : ℝ))) hlt
    (fun s hs => (h.1 s (hsub hs)).2.2.continuousAt.continuousWithinAt)
    (fun s hs => (h.1 s (hsub (Set.Ioo_subset_Icc_self hs))).2.2)
  have hvc := (h.1 c (hsub (Set.Ioo_subset_Icc_self hc))).1
  have hpos : 0 < μ * v c ^ (-(5 / 3 : ℝ)) + κ * v c ^ (-(1 / 3 : ℝ)) := by
    have := Real.rpow_pos_of_pos hvc (-(5 / 3 : ℝ))
    have := Real.rpow_pos_of_pos hvc (-(1 / 3 : ℝ))
    positivity
  rw [hslope] at hpos
  have := (div_pos_iff_of_pos_right (sub_pos.mpr hlt)).mp hpos
  linarith

lemma vcont {κ μ : ℝ} {v v' : ℝ → ℝ} (h : Sol κ μ v v') {a b : ℝ} (hab : Set.Icc a b ⊆ Set.Icc 0 1) :
    ContinuousOn v (Set.Icc a b) := fun t ht => (h.1 t (hab ht)).2.1.continuousAt.continuousWithinAt

lemma above {κ μ : ℝ} {v v' : ℝ → ℝ} (h : Sol κ μ v v') (hμ : 0 < μ) (hκ : 0 < κ) {t0 s : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hz : v' t0 = 0) (hne : s ≠ t0) :
    v t0 < v s := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope v v' hlt
      (vcont h (Set.Icc_subset_Icc hs.1 ht0.2))
      (fun x hx => (h.1 x (Set.Icc_subset_Icc hs.1 ht0.2 (Set.Ioo_subset_Icc_self hx))).2.1)
    have hneg : v' c < 0 := by
      have := vprime_pos h hμ hκ (Set.Icc_subset_Icc hs.1 ht0.2 (Set.Ioo_subset_Icc_self hc)) ht0 hc.2
      linarith
    rw [hsl] at hneg
    rcases (div_neg_iff.mp hneg) with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith [sub_pos.mpr hc.1, sub_pos.mpr hlt]
    · linarith
  · obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope v v' hlt
      (vcont h (Set.Icc_subset_Icc ht0.1 hs.2))
      (fun x hx => (h.1 x (Set.Icc_subset_Icc ht0.1 hs.2 (Set.Ioo_subset_Icc_self hx))).2.1)
    have hpos : 0 < v' c := by
      have := vprime_pos h hμ hκ ht0 (Set.Icc_subset_Icc ht0.1 hs.2 (Set.Ioo_subset_Icc_self hc)) hc.1
      linarith
    rw [hsl] at hpos
    have := (div_pos_iff_of_pos_right (sub_pos.mpr hlt)).mp hpos
    linarith

/-! Step 2: u = v^(2/3) and its shell. -/

/-- `u = (v^(1/3))^2`. -/
noncomputable def U (v : ℝ → ℝ) (t : ℝ) : ℝ := (v t ^ (1 / 3 : ℝ)) ^ 2

lemma U_pos {v : ℝ → ℝ} {t : ℝ} (hv : 0 < v t) : 0 < U v t := by unfold U; have := cr_pos hv; positivity

lemma U_hasDerivAt {v : ℝ → ℝ} {w t : ℝ} (hv : 0 < v t) (hd : HasDerivAt v w t) :
    HasDerivAt (U v) (2 * w / (3 * v t ^ (1 / 3 : ℝ))) t := by
  have := (cr_hasDerivAt hv hd).pow 2
  refine this.congr_deriv ?_
  have hc := cr_pos hv
  generalize v t ^ (1 / 3 : ℝ) = c at hc ⊢
  field_simp
  ring

lemma U_lt {v : ℝ → ℝ} {a b : ℝ} (ha : 0 < v a) (hab : v a < v b) : U v a < U v b := by
  unfold U
  have h1 := Real.rpow_lt_rpow ha.le hab (by norm_num : (0 : ℝ) < 1 / 3)
  have := cr_pos ha
  nlinarith

lemma U_cont {κ μ : ℝ} {v v' : ℝ → ℝ} (h : Sol κ μ v v') {a b : ℝ} (hab : Set.Icc a b ⊆ Set.Icc 0 1) :
    ContinuousOn (U v) (Set.Icc a b) := fun t ht =>
  (U_hasDerivAt (h.1 t (hab ht)).1 (h.1 t (hab ht)).2.1).continuousAt.continuousWithinAt

/-- The shell, in clock coordinates. -/
lemma shell {κ μ : ℝ} {v v' : ℝ → ℝ} (h : Sol κ μ v v') (hκ : 0 < κ) {t0 : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (hz : v' t0 = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, (2 * v' t / (3 * v t ^ (1 / 3 : ℝ))) ^ 2 * U v t ^ 2 = 4 * κ / 3 *
      ((U v t - (U v t0 - μ / κ / U v t0) / 2) ^ 2 - ((U v t0 + μ / κ / U v t0) / 2) ^ 2) := by
  intro t ht
  have hv0 := (h.1 t0 ht0).1
  have hv := (h.1 t ht).1
  have e1 := energy h t ht
  have e2 := energy h t0 ht0
  rw [hz, ← e1] at e2
  have hc := cr_pos hv
  have hc0 := cr_pos hv0
  unfold U
  generalize v t ^ (1 / 3 : ℝ) = c at hc e2 ⊢
  generalize v t0 ^ (1 / 3 : ℝ) = c0 at hc0 e2 ⊢
  have hv2 : v' t ^ 2 * c ^ 2 * c0 ^ 2 = 3 * (c ^ 2 - c0 ^ 2) * (κ * c ^ 2 * c0 ^ 2 + μ) := by
    field_simp at e2
    linear_combination -e2
  have hκ0 := hκ
  have : (c ^ 2 - (c0 ^ 2 - μ / κ / c0 ^ 2) / 2) ^ 2 - ((c0 ^ 2 + μ / κ / c0 ^ 2) / 2) ^ 2
      = (c ^ 2 - c0 ^ 2) * (κ * c ^ 2 * c0 ^ 2 + μ) / (κ * c0 ^ 2) := by field_simp; ring
  rw [this]
  field_simp
  linear_combination 4 * hv2

/-! Step 3: run the clock up both halves. -/

lemma pos_of_sq_eq {X K : ℝ} (hX : 0 < X) (hK : 0 < K) (h : X ^ 2 = K ^ 2) : X = K := by nlinarith

lemma clock_rate {κ μ : ℝ} {v v' : ℝ → ℝ} (h : Sol κ μ v v') (hμ : 0 < μ) (hκ : 0 < κ) {t0 s : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hz : v' t0 = 0) (hne : s ≠ t0) :
    HasDerivAt (fun y => Gk ((U v t0 - μ / κ / U v t0) / 2) ((U v t0 + μ / κ / U v t0) / 2) (U v y))
      ((if t0 < s then 1 else -1) * Real.sqrt (4 * κ / 3)) s := by
  have hx := U_pos (h.1 t0 ht0).1
  set x := U v t0 with hxdef
  set B := (x - μ / κ / x) / 2 with hB
  set D := (x + μ / κ / x) / 2 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hE : 0 < 4 * κ / 3 := by positivity
  have hab := U_lt (h.1 t0 ht0).1 (above h hμ hκ ht0 hs hz hne)
  have hBD : B + D < U v s := by rw [hB, hD]; linarith
  have hvs := (h.1 s hs).1
  have hd := U_hasDerivAt hvs (h.1 s hs).2.1
  have hcl := clock_hasDerivAt hDpos hBD hd
  have hsp := clock_speed hDpos hBD hE (shell h hκ ht0 hz s hs)
  have hy : 1 < (U v s - B) / D := by rw [lt_div_iff₀ hDpos]; linarith
  have hq : 0 < ((U v s - B) / D) ^ 2 - 1 := by nlinarith
  have hQ := Real.sqrt_pos.mpr hq
  have hUs := U_pos hvs
  have hcs := cr_pos hvs
  have hK := Real.sqrt_pos.mpr hE
  split_ifs with hlt
  · have hw : 0 < v' s := by have := vprime_pos h hμ hκ ht0 hs hlt; linarith
    convert hcl using 1
    rw [one_mul]
    exact (pos_of_sq_eq (by positivity) hK hsp).symm
  · have hlt' : s < t0 := lt_of_le_of_ne (not_lt.mp hlt) hne
    have hw : v' s < 0 := by have := vprime_pos h hμ hκ hs ht0 hlt'; linarith
    convert hcl using 1
    have hw2 : 2 * v' s / (3 * v s ^ (1 / 3 : ℝ)) < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
    have hneg : 0 < -(2 * v' s / (3 * v s ^ (1 / 3 : ℝ)) * U v s / (D * Real.sqrt (((U v s - B) / D) ^ 2 - 1))) := by
      rw [neg_pos]; exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hw2 hUs) (by positivity)
    have := pos_of_sq_eq hneg hK (by rw [neg_sq]; exact hsp)
    linarith

/-- **ODE -> time condition for P_3.** Every solution has its lowest point at `t = 1/2` and its turning value
`x = v(1/2)^(2/3)` in `(0,1)` satisfies `Gk p r 1 = sqrt(kap/3)` (half-time = 1/2). -/
theorem tau_link {κ μ : ℝ} {v v' : ℝ → ℝ} (h : Sol κ μ v v') (hμ : 0 < μ) (hκ : 0 < κ) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧
      Gk ((x - μ / κ / x) / 2) ((x + μ / κ / x) / 2) 1 = Real.sqrt (κ / 3) := by
  obtain ⟨t0, ht0, hz⟩ := rolle h
  have ht0' := Set.Ioo_subset_Icc_self ht0
  have hx := U_pos (h.1 t0 ht0').1
  set x := U v t0 with hxdef
  set B := (x - μ / κ / x) / 2 with hB
  set D := (x + μ / κ / x) / 2 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  set K := Real.sqrt (4 * κ / 3) with hK
  have hcont : ∀ a b : ℝ, Set.Icc a b ⊆ Set.Icc 0 1 → ContinuousOn (fun y => Gk B D (U v y)) (Set.Icc a b) := by
    intro a b hab
    have hvc := U_cont h hab
    have hmaps : Set.MapsTo (fun y => (U v y - B) / D) (Set.Icc a b) (Set.Ici 1) := by
      intro y hy
      have hxm : x ≤ U v y := by
        rcases eq_or_ne y t0 with hy0 | hy0
        · rw [hy0]
        · exact (U_lt (h.1 t0 ht0').1 (above h hμ hκ ht0' (hab hy) hz hy0)).le
      show 1 ≤ (U v y - B) / D
      rw [le_div_iff₀ hDpos, hB, hD]; linarith
    unfold Gk
    exact (continuousOn_const.mul (Real.continuousOn_arcosh.comp ((hvc.sub continuousOn_const).div_const D) hmaps)).add
      (continuousOn_const.mul ((((hvc.sub continuousOn_const).div_const D).pow 2).sub continuousOn_const).sqrt)
  have hG0 : Gk B D x = 0 := by
    have : x - B = D := by rw [hB, hD]; ring
    unfold Gk
    rw [this, div_self hDpos.ne']
    simp [Real.arcosh_zero]
  have hR : Gk B D (U v 1) = K * (1 - t0) := by
    obtain ⟨c, _, hsl⟩ := exists_hasDerivAt_eq_slope (fun y => Gk B D (U v y) - K * y) (fun _ => (0 : ℝ))
      ht0.2 ((hcont t0 1 (Set.Icc_subset_Icc ht0.1.le le_rfl)).sub (continuousOn_const.mul continuousOn_id))
      (fun s hs => by
        have hr := clock_rate h hμ hκ ht0' (Set.Icc_subset_Icc ht0.1.le le_rfl (Set.Ioo_subset_Icc_self hs)) hz
          (ne_of_gt hs.1)
        rw [if_pos hs.1, one_mul] at hr
        convert hr.sub ((hasDerivAt_id' s).const_mul K) using 1
        ring)
    have hne : (1 : ℝ) - t0 ≠ 0 := by linarith [ht0.2]
    field_simp at hsl
    rw [← hxdef, hG0] at hsl
    linarith
  have hL : Gk B D (U v 0) = K * t0 := by
    obtain ⟨c, _, hsl⟩ := exists_hasDerivAt_eq_slope (fun y => Gk B D (U v y) + K * y) (fun _ => (0 : ℝ))
      ht0.1 ((hcont 0 t0 (Set.Icc_subset_Icc le_rfl ht0.2.le)).add (continuousOn_const.mul continuousOn_id))
      (fun s hs => by
        have hr := clock_rate h hμ hκ ht0' (Set.Icc_subset_Icc le_rfl ht0.2.le (Set.Ioo_subset_Icc_self hs)) hz
          (ne_of_lt hs.2)
        rw [if_neg (not_lt.mpr hs.2.le)] at hr
        convert hr.add ((hasDerivAt_id' s).const_mul K) using 1
        ring)
    have hne : t0 - 0 ≠ 0 := by linarith [ht0.1]
    field_simp at hsl
    rw [← hxdef, hG0] at hsl
    linarith
  have hU1 : U v 1 = 1 := by simp [U, h.2.2]
  have hU0 : U v 0 = 1 := by simp [U, h.2.1]
  rw [hU1] at hR
  rw [hU0] at hL
  have hx1 : x < 1 := by
    have := U_lt (h.1 t0 ht0').1 (above h hμ hκ ht0' ⟨zero_le_one, le_rfl⟩ hz (ne_of_gt ht0.2))
    rw [hU1] at this; exact this
  refine ⟨x, hx, hx1, ?_⟩
  have hK2 : K = 2 * Real.sqrt (κ / 3) := by
    rw [hK, show 4 * κ / 3 = 2 ^ 2 * (κ / 3) by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [← hB, ← hD]
  linarith

/-- The clock value at the wall, in the variables of `PThree.class_of_crit`. -/
lemma clock_vars {q x : ℝ} (hq : 0 < q) (hx : 0 < x) (hx1 : x < 1) :
    let C := (2 * x - x ^ 2 + q) / (x ^ 2 + q)
    1 < C ∧ (x ^ 2 + q) ^ 2 * Real.sqrt (C ^ 2 - 1) ^ 2 = 4 * x * (1 - x) * (x + q) ∧
    2 * x * Gk ((x - q / x) / 2) ((x + q / x) / 2) 1
      = (x ^ 2 - q) * Real.arcosh C + (x ^ 2 + q) * Real.sqrt (C ^ 2 - 1) := by
  intro C
  have hD : 0 < x ^ 2 + q := by positivity
  have hC1 : 1 < C := by
    show 1 < (2 * x - x ^ 2 + q) / (x ^ 2 + q)
    rw [lt_div_iff₀ hD]; nlinarith
  have hCe : (1 - (x - q / x) / 2) / ((x + q / x) / 2) = C := by
    show _ = (2 * x - x ^ 2 + q) / (x ^ 2 + q)
    field_simp; ring
  refine ⟨hC1, ?_, ?_⟩
  · rw [Real.sq_sqrt (by nlinarith)]
    show (x ^ 2 + q) ^ 2 * (((2 * x - x ^ 2 + q) / (x ^ 2 + q)) ^ 2 - 1) = _
    field_simp; ring
  · unfold Gk; rw [hCe]; field_simp

/-- **ODE -> time condition, in the variables of `PThree.class_of_crit`.** Every solution of the P_3 seat
(kap, mu > 0) produces `x, T, S, C` satisfying every hypothesis of `class_of_crit` EXCEPT the top condition `h2`
(which is the critical-point equation, true only at the break): the tie, `cosh`/`exp` of the clock, and the time
condition `(x^2 - q) T + (x^2 + q) S = 2 k x` with `k = sqrt(kap/3)`. -/
theorem time_condition {κ μ : ℝ} {v v' : ℝ → ℝ} (h : Sol κ μ v v') (hμ : 0 < μ) (hκ : 0 < κ) :
    ∃ x T S C : ℝ, 0 < x ∧ x < 1 ∧ 0 < T ∧ 0 < S ∧
      (x ^ 2 + μ / κ) * C = 2 * x - x ^ 2 + μ / κ ∧
      (x ^ 2 + μ / κ) ^ 2 * S ^ 2 = 4 * x * (1 - x) * (x + μ / κ) ∧
      (x ^ 2 - μ / κ) * T + (x ^ 2 + μ / κ) * S = 2 * Real.sqrt (κ / 3) * x ∧
      Real.exp T = C + S := by
  obtain ⟨x, hx, hx1, hG⟩ := tau_link h hμ hκ
  have hq : 0 < μ / κ := div_pos hμ hκ
  obtain ⟨hC1, hS2, hGx⟩ := clock_vars hq hx hx1
  set C := (2 * x - x ^ 2 + μ / κ) / (x ^ 2 + μ / κ) with hCdef
  have hD : 0 < x ^ 2 + μ / κ := by positivity
  refine ⟨x, Real.arcosh C, Real.sqrt (C ^ 2 - 1), C, hx, hx1, Real.arcosh_pos hC1,
    Real.sqrt_pos.mpr (by nlinarith), ?_, hS2, ?_, Real.exp_arcosh hC1.le⟩
  · rw [hCdef]; field_simp
  · rw [← hGx, hG]; ring

/-- The P_3 time condition at kap = 1 in the exact shape `PThree.class_of_crit` consumes (`3 k^2 = kap`). -/
theorem time_condition_crit_vars {κ μ : ℝ} {v v' : ℝ → ℝ} (h : Sol κ μ v v') (hμ : 0 < μ) (hκ : 0 < κ) :
    ∃ q x T S C k : ℝ, q * κ = μ ∧ 0 < x ∧ x < 1 ∧ 0 < T ∧ 0 < S ∧ 3 * k ^ 2 = κ ∧
      (x ^ 2 + q) * C = 2 * x - x ^ 2 + q ∧ (x ^ 2 + q) ^ 2 * S ^ 2 = 4 * x * (1 - x) * (x + q) ∧
      (x ^ 2 - q) * T + (x ^ 2 + q) * S = 2 * k * x ∧ Real.exp T = C + S := by
  obtain ⟨x, T, S, C, hx, hx1, hT, hS, hC, hS2, h1, he⟩ := time_condition h hμ hκ
  refine ⟨μ / κ, x, T, S, C, Real.sqrt (κ / 3), by field_simp, hx, hx1, hT, hS, ?_, hC, hS2, h1, he⟩
  rw [Real.sq_sqrt (by positivity)]; ring

end PThreeOde
