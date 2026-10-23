import Mathlib
import Mistranslation.MemsOde

/-! # The Kepler bridge vdW -> MEMS from the ODE (2026-10-23)

Seat `v'' = mu (1/v^3 + lam/v^2)`, `v(0) = v(1) = 1`, `v > 0`, `lam >= 0`. Slowed clock `dt = v dtau` gives
`v = B + D cosh(sqrt E tau)`, so `G(v) = B arcosh((v-B)/D) + D sqrt(((v-B)/D)^2 - 1)` runs at constant speed sqrt E.
Step 1: energy, lowest point, sign of v' (copies of the MemsOde pattern). -/

namespace KeplerOde

def Sol (lam μ : ℝ) (v v' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < v t ∧ HasDerivAt v (v' t) t ∧
      HasDerivAt v' (μ / v t ^ 3 + μ * lam / v t ^ 2) t) ∧ v 0 = 1 ∧ v 1 = 1

lemma energy {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, v' t * v' t + μ * (v t * v t)⁻¹ + 2 * μ * lam * (v t)⁻¹
      = v' 0 * v' 0 + μ * (v 0 * v 0)⁻¹ + 2 * μ * lam * (v 0)⁻¹ := by
  refine MemsOde.const_on (f := fun t => v' t * v' t + μ * (v t * v t)⁻¹ + 2 * μ * lam * (v t)⁻¹) ?_
  intro s hs
  obtain ⟨hv, hd, hdd⟩ := h.1 s hs
  have hvv : v s * v s ≠ 0 := by positivity
  have := ((hdd.mul hdd).add (((hd.mul hd).inv hvv).const_mul μ)).add ((hd.inv hv.ne').const_mul (2 * μ * lam))
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

lemma rolle {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') : ∃ t0 ∈ Set.Ioo (0 : ℝ) 1, v' t0 = 0 := by
  have hc : ContinuousOn v (Set.Icc 0 1) := fun t ht => (h.1 t ht).2.1.continuousAt.continuousWithinAt
  exact exists_hasDerivAt_eq_zero (by norm_num) hc (by rw [h.2.1, h.2.2])
    (fun t ht => (h.1 t (Set.Ioo_subset_Icc_self ht)).2.1)

lemma vprime_pos {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') (hμ : 0 < μ) (hl : 0 ≤ lam) {t0 t : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hlt : t0 < t) : v' t0 < v' t := by
  have hsub : Set.Icc t0 t ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc ht0.1 ht.2
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope v' (fun s => μ / v s ^ 3 + μ * lam / v s ^ 2) hlt
    (fun s hs => (h.1 s (hsub hs)).2.2.continuousAt.continuousWithinAt)
    (fun s hs => (h.1 s (hsub (Set.Ioo_subset_Icc_self hs))).2.2)
  have hvc := (h.1 c (hsub (Set.Ioo_subset_Icc_self hc))).1
  have hpos : 0 < μ / v c ^ 3 + μ * lam / v c ^ 2 := by
    have : 0 ≤ μ * lam / v c ^ 2 := by positivity
    have : 0 < μ / v c ^ 3 := by positivity
    linarith
  rw [hslope] at hpos
  have := (div_pos_iff_of_pos_right (sub_pos.mpr hlt)).mp hpos
  linarith

/-! Step 2: the Kepler clock. -/

noncomputable def Gk (B D x : ℝ) : ℝ := B * Real.arcosh ((x - B) / D) + D * Real.sqrt (((x - B) / D) ^ 2 - 1)

lemma clock_hasDerivAt {B D : ℝ} {v : ℝ → ℝ} {w t : ℝ} (hD : 0 < D) (hx : B + D < v t)
    (hd : HasDerivAt v w t) :
    HasDerivAt (fun s => Gk B D (v s)) (w * v t / (D * Real.sqrt (((v t - B) / D) ^ 2 - 1))) t := by
  have hy : 1 < (v t - B) / D := by rw [lt_div_iff₀ hD]; linarith
  have hq : 0 < ((v t - B) / D) ^ 2 - 1 := by nlinarith
  have hyd : HasDerivAt (fun s => (v s - B) / D) (w / D) t := (hd.sub_const B).div_const D
  have hA := (Real.hasDerivAt_arcosh hy).comp t hyd
  have hS := ((hyd.pow 2).sub_const 1).sqrt hq.ne'
  have := (hA.const_mul B).add (hS.const_mul D)
  refine this.congr_deriv ?_
  have hsq := Real.sqrt_pos.mpr hq
  have hD0 : D ≠ 0 := hD.ne'
  generalize Real.sqrt (((v t - B) / D) ^ 2 - 1) = Q at hsq ⊢
  field_simp
  ring_nf
  field_simp
  ring

lemma clock_speed {B D E x w : ℝ} (hD : 0 < D) (hx : B + D < x) (hE : 0 < E)
    (hshell : w ^ 2 * x ^ 2 = E * ((x - B) ^ 2 - D ^ 2)) :
    (w * x / (D * Real.sqrt (((x - B) / D) ^ 2 - 1))) ^ 2 = Real.sqrt E ^ 2 := by
  have hy : 1 < (x - B) / D := by rw [lt_div_iff₀ hD]; linarith
  have hpos : 0 < (x - B) ^ 2 - D ^ 2 := by nlinarith
  have hq : 0 < ((x - B) / D) ^ 2 - 1 := by nlinarith
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hE.le, hshell]
  field_simp

/-! Step 3: run the clock up both halves. -/

lemma vcont {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') {a b : ℝ} (hab : Set.Icc a b ⊆ Set.Icc 0 1) :
    ContinuousOn v (Set.Icc a b) := fun t ht => (h.1 t (hab ht)).2.1.continuousAt.continuousWithinAt

lemma above {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') (hμ : 0 < μ) (hl : 0 ≤ lam) {t0 s : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hz : v' t0 = 0) (hne : s ≠ t0) :
    v t0 < v s := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope v v' hlt
      (vcont h (Set.Icc_subset_Icc hs.1 ht0.2))
      (fun x hx => (h.1 x (Set.Icc_subset_Icc hs.1 ht0.2 (Set.Ioo_subset_Icc_self hx))).2.1)
    have hneg : v' c < 0 := by
      have := vprime_pos h hμ hl (Set.Icc_subset_Icc hs.1 ht0.2 (Set.Ioo_subset_Icc_self hc)) ht0 hc.2
      linarith
    rw [hsl] at hneg
    rcases (div_neg_iff.mp hneg) with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith [sub_pos.mpr hc.1, sub_pos.mpr hlt]
    · linarith
  · obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope v v' hlt
      (vcont h (Set.Icc_subset_Icc ht0.1 hs.2))
      (fun x hx => (h.1 x (Set.Icc_subset_Icc ht0.1 hs.2 (Set.Ioo_subset_Icc_self hx))).2.1)
    have hpos : 0 < v' c := by
      have := vprime_pos h hμ hl ht0 (Set.Icc_subset_Icc ht0.1 hs.2 (Set.Ioo_subset_Icc_self hc)) hc.1
      linarith
    rw [hsl] at hpos
    have := (div_pos_iff_of_pos_right (sub_pos.mpr hlt)).mp hpos
    linarith

/-- The energy shell measured from the lowest point `m`, in clock coordinates. -/
lemma shell {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') {t0 : ℝ} (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1)
    (hz : v' t0 = 0) (hE : 0 < μ / v t0 ^ 2 + 2 * μ * lam / v t0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, v' t ^ 2 * v t ^ 2 = (μ / v t0 ^ 2 + 2 * μ * lam / v t0) *
      ((v t - μ * lam / (μ / v t0 ^ 2 + 2 * μ * lam / v t0)) ^ 2
        - (v t0 - μ * lam / (μ / v t0 ^ 2 + 2 * μ * lam / v t0)) ^ 2) := by
  intro t ht
  have hm := (h.1 t0 ht0).1
  have hv := (h.1 t ht).1
  have e1 := energy h t ht
  have e2 := energy h t0 ht0
  rw [hz] at e2
  set E := μ / v t0 ^ 2 + 2 * μ * lam / v t0 with hEdef
  have hEm : E * v t0 ^ 2 = μ + 2 * μ * lam * v t0 := by rw [hEdef]; field_simp
  have hEt : v' t * v' t + μ * (v t * v t)⁻¹ + 2 * μ * lam * (v t)⁻¹ = E := by
    rw [e1, ← e2, hEdef]; field_simp; ring
  field_simp at hEt ⊢
  nlinarith [hEt, hEm, hE, hm, hv]

lemma pos_of_sq_eq {X K : ℝ} (hX : 0 < X) (hK : 0 < K) (h : X ^ 2 = K ^ 2) : X = K := by nlinarith

/-- The Kepler clock runs at `+sqrt E` right of the lowest point and `-sqrt E` left of it. -/
lemma clock_rate {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') (hμ : 0 < μ) (hl : 0 ≤ lam) {t0 s : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hz : v' t0 = 0) (hne : s ≠ t0) :
    HasDerivAt (fun x => Gk (μ * lam / (μ / v t0 ^ 2 + 2 * μ * lam / v t0))
        (v t0 - μ * lam / (μ / v t0 ^ 2 + 2 * μ * lam / v t0)) (v x))
      ((if t0 < s then 1 else -1) * Real.sqrt (μ / v t0 ^ 2 + 2 * μ * lam / v t0)) s := by
  have hm := (h.1 t0 ht0).1
  set E := μ / v t0 ^ 2 + 2 * μ * lam / v t0 with hEdef
  have hE : 0 < E := by
    have : 0 ≤ 2 * μ * lam / v t0 := by positivity
    have : 0 < μ / v t0 ^ 2 := by positivity
    linarith
  set B := μ * lam / E with hB
  set D := v t0 - B with hD
  have hDpos : 0 < D := by
    rw [hD, hB, sub_pos, div_lt_iff₀ hE, hEdef]
    have : μ * lam ≤ 2 * μ * lam := by nlinarith
    have : 0 < μ / v t0 ^ 2 * v t0 := by positivity
    field_simp
    nlinarith [mul_pos hμ hm]
  have hab := above h hμ hl ht0 hs hz hne
  have hx : B + D < v s := by rw [hD]; linarith
  have hd := (h.1 s hs).2.1
  have hcl := clock_hasDerivAt hDpos hx hd
  have hsp := clock_speed hDpos hx hE (shell h ht0 hz hE s hs)
  have hy : 1 < (v s - B) / D := by rw [lt_div_iff₀ hDpos]; linarith
  have hq : 0 < ((v s - B) / D) ^ 2 - 1 := by nlinarith
  have hQ := Real.sqrt_pos.mpr hq
  have hvs := (h.1 s hs).1
  have hK := Real.sqrt_pos.mpr hE
  split_ifs with hlt
  · have hw : 0 < v' s := by have := vprime_pos h hμ hl ht0 hs hlt; linarith
    convert hcl using 1
    rw [one_mul]
    exact (pos_of_sq_eq (by positivity) hK hsp).symm
  · have hlt' : s < t0 := lt_of_le_of_ne (not_lt.mp hlt) hne
    have hw : v' s < 0 := by have := vprime_pos h hμ hl hs ht0 hlt'; linarith
    convert hcl using 1
    have hneg : 0 < -(v' s * v s / (D * Real.sqrt (((v s - B) / D) ^ 2 - 1))) := by
      rw [neg_pos]; exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hw hvs) (by positivity)
    have := pos_of_sq_eq hneg hK (by rw [neg_sq]; exact hsp)
    linarith

/-- **Every solution of the Kepler bridge sits on the closed formula**
`mu = 4 m^2 (B T + D sinh T)^2 / (1 + 2 lam m)`, `B = lam m^2/(1+2 lam m)`, `D = m(1+lam m)/(1+2 lam m)`,
`T = arcosh((1-B)/D)`, for some `0 < m`. Derived from the ODE (slowed clock, no integrals). -/
theorem mu_formula {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') (hμ : 0 < μ) (hl : 0 ≤ lam) :
    ∃ m : ℝ, 0 < m ∧ m < 1 ∧ μ = 4 * m ^ 2 * (lam * m ^ 2 / (1 + 2 * lam * m) *
        Real.arcosh ((1 - lam * m ^ 2 / (1 + 2 * lam * m)) / (m * (1 + lam * m) / (1 + 2 * lam * m)))
      + m * (1 + lam * m) / (1 + 2 * lam * m) *
        Real.sinh (Real.arcosh ((1 - lam * m ^ 2 / (1 + 2 * lam * m)) / (m * (1 + lam * m) / (1 + 2 * lam * m)))))
        ^ 2 / (1 + 2 * lam * m) := by
  obtain ⟨t0, ht0, hz⟩ := rolle h
  have ht0' := Set.Ioo_subset_Icc_self ht0
  have hm := (h.1 t0 ht0').1
  set m := v t0 with hmdef
  set E := μ / m ^ 2 + 2 * μ * lam / m with hEdef
  have hE : 0 < E := by
    have : 0 ≤ 2 * μ * lam / m := by positivity
    have : 0 < μ / m ^ 2 := by positivity
    linarith
  set B := μ * lam / E with hB
  set D := m - B with hD
  have hDpos : 0 < D := by
    rw [hD, hB, sub_pos, div_lt_iff₀ hE, hEdef]
    field_simp
    nlinarith [mul_pos hμ hm, mul_nonneg hμ.le hl]
  set K := Real.sqrt E with hK
  -- continuity of the clock along v on any [a, b] inside [0,1] (v >= m = B + D there)
  have hcont : ∀ a b : ℝ, Set.Icc a b ⊆ Set.Icc 0 1 → ContinuousOn (fun x => Gk B D (v x)) (Set.Icc a b) := by
    intro a b hab
    have hvc := vcont h hab
    have hmaps : Set.MapsTo (fun x => (v x - B) / D) (Set.Icc a b) (Set.Ici 1) := by
      intro x hx
      have hxm : m ≤ v x := by
        rcases eq_or_ne x t0 with hx0 | hx0
        · rw [hx0]
        · exact (above h hμ hl ht0' (hab hx) hz hx0).le
      show 1 ≤ (v x - B) / D
      rw [le_div_iff₀ hDpos]; linarith
    unfold Gk
    exact (continuousOn_const.mul (Real.continuousOn_arcosh.comp ((hvc.sub continuousOn_const).div_const D) hmaps)).add
      (continuousOn_const.mul ((((hvc.sub continuousOn_const).div_const D).pow 2).sub continuousOn_const).sqrt)
  have hG0 : Gk B D m = 0 := by
    unfold Gk
    rw [← hD, div_self hDpos.ne']
    simp [Real.arcosh_zero]
  -- right half
  have hR : Gk B D (v 1) = K * (1 - t0) := by
    obtain ⟨c, _, hsl⟩ := exists_hasDerivAt_eq_slope (fun x => Gk B D (v x) - K * x) (fun _ => (0 : ℝ))
      ht0.2 ((hcont t0 1 (Set.Icc_subset_Icc ht0.1.le le_rfl)).sub (continuousOn_const.mul continuousOn_id))
      (fun s hs => by
        have hr := clock_rate h hμ hl ht0' (Set.Icc_subset_Icc ht0.1.le le_rfl (Set.Ioo_subset_Icc_self hs)) hz
          (ne_of_gt hs.1)
        rw [if_pos hs.1, one_mul] at hr
        convert hr.sub ((hasDerivAt_id' s).const_mul K) using 1
        simp only [← hmdef, ← hEdef, ← hK]; ring)
    have hne : (1 : ℝ) - t0 ≠ 0 := by linarith [ht0.2]
    field_simp at hsl
    rw [← hmdef, hG0] at hsl
    linarith
  -- left half
  have hL : Gk B D (v 0) = K * t0 := by
    obtain ⟨c, _, hsl⟩ := exists_hasDerivAt_eq_slope (fun x => Gk B D (v x) + K * x) (fun _ => (0 : ℝ))
      ht0.1 ((hcont 0 t0 (Set.Icc_subset_Icc le_rfl ht0.2.le)).add (continuousOn_const.mul continuousOn_id))
      (fun s hs => by
        have hr := clock_rate h hμ hl ht0' (Set.Icc_subset_Icc le_rfl ht0.2.le (Set.Ioo_subset_Icc_self hs)) hz
          (ne_of_lt hs.2)
        rw [if_neg (not_lt.mpr hs.2.le)] at hr
        convert hr.add ((hasDerivAt_id' s).const_mul K) using 1
        simp only [← hmdef, ← hEdef, ← hK]; ring)
    have hne : t0 - 0 ≠ 0 := by linarith [ht0.1]
    field_simp at hsl
    rw [← hmdef, hG0] at hsl
    linarith
  rw [h.2.2] at hR
  rw [h.2.1] at hL
  have hG1 : Gk B D 1 = K / 2 := by linarith
  have hm1 : m < 1 := by
    have := above h hμ hl ht0' ⟨zero_le_one, le_rfl⟩ hz (ne_of_gt ht0.2)
    rw [h.2.2] at this; exact this
  have h12 : 0 < 1 + 2 * lam * m := by positivity
  refine ⟨m, hm, hm1, ?_⟩
  have hB' : lam * m ^ 2 / (1 + 2 * lam * m) = B := by rw [hB, hEdef]; field_simp
  have hD' : m * (1 + lam * m) / (1 + 2 * lam * m) = D := by rw [hD, ← hB']; field_simp; ring
  rw [hB', hD']
  have hy : 1 ≤ (1 - B) / D := by rw [le_div_iff₀ hDpos, hD]; linarith
  rw [Real.sinh_arcosh hy]
  have hGk : Gk B D 1 = B * Real.arcosh ((1 - B) / D) + D * Real.sqrt (((1 - B) / D) ^ 2 - 1) := rfl
  rw [← hGk, hG1, div_pow, hK, Real.sq_sqrt hE.le, hEdef]
  field_simp
  ring

/-! Step 4: existence -- the inverse Kepler clock. -/

noncomputable def φk (B D η : ℝ) : ℝ := B * η + D * Real.sinh η

lemma φk_hasDerivAt (B D η : ℝ) : HasDerivAt (φk B D) (B + D * Real.cosh η) η := by
  have := ((hasDerivAt_id' η).const_mul B).add ((Real.hasDerivAt_sinh η).const_mul D)
  exact this.congr_deriv (by ring)

lemma φk_strictMono {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D) : StrictMono (φk B D) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(φk_hasDerivAt B D x).deriv]
  have := Real.cosh_pos x
  positivity

lemma φk_surj {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D) : Function.Surjective (φk B D) := by
  have hc : Continuous (φk B D) := continuous_iff_continuousAt.mpr fun x => (φk_hasDerivAt B D x).continuousAt
  apply hc.surjective
  · apply Filter.tendsto_atTop_mono' Filter.atTop _ (Filter.tendsto_id.const_mul_atTop hD)
    filter_upwards [Filter.eventually_ge_atTop 0] with x hx
    have : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx
    simp only [φk, id]; nlinarith
  · apply Filter.tendsto_atBot_mono' Filter.atBot _ (Filter.tendsto_id.const_mul_atBot hD)
    filter_upwards [Filter.eventually_le_atBot 0] with x hx
    have : Real.sinh x ≤ x := Real.sinh_le_self_iff.mpr hx
    simp only [φk, id]; nlinarith

lemma φk_neg (B D η : ℝ) : φk B D (-η) = -φk B D η := by simp [φk, Real.sinh_neg]; ring

noncomputable def ψk (B D : ℝ) (hB : 0 ≤ B) (hD : 0 < D) : ℝ → ℝ :=
  (StrictMono.orderIsoOfSurjective (φk B D) (φk_strictMono hB hD) (φk_surj hB hD)).symm

lemma φk_ψk {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D) (y : ℝ) : φk B D (ψk B D hB hD y) = y :=
  (StrictMono.orderIsoOfSurjective (φk B D) (φk_strictMono hB hD) (φk_surj hB hD)).apply_symm_apply y

lemma ψk_φk {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D) (x : ℝ) : ψk B D hB hD (φk B D x) = x :=
  (StrictMono.orderIsoOfSurjective (φk B D) (φk_strictMono hB hD) (φk_surj hB hD)).symm_apply_apply x

lemma ψk_hasDerivAt {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D) (y : ℝ) :
    HasDerivAt (ψk B D hB hD) (B + D * Real.cosh (ψk B D hB hD y))⁻¹ y := by
  have hc : Continuous (ψk B D hB hD) :=
    (StrictMono.orderIsoOfSurjective (φk B D) (φk_strictMono hB hD) (φk_surj hB hD)).symm.continuous
  have hpos : 0 < B + D * Real.cosh (ψk B D hB hD y) := by have := Real.cosh_pos (ψk B D hB hD y); positivity
  exact HasDerivAt.of_local_left_inverse hc.continuousAt (φk_hasDerivAt B D _) hpos.ne'
    (Filter.Eventually.of_forall (φk_ψk hB hD))

noncomputable def Bm (lam m : ℝ) : ℝ := lam * m ^ 2 / (1 + 2 * lam * m)
noncomputable def Dm (lam m : ℝ) : ℝ := m * (1 + lam * m) / (1 + 2 * lam * m)
noncomputable def Tm (lam m : ℝ) : ℝ := Real.arcosh ((1 - Bm lam m) / Dm lam m)
noncomputable def Km (lam m : ℝ) : ℝ := 2 * (Bm lam m * Tm lam m + Dm lam m * Real.sinh (Tm lam m))
noncomputable def fk (lam m : ℝ) : ℝ := Km lam m ^ 2 * m ^ 2 / (1 + 2 * lam * m)

lemma Bm_nonneg {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) : 0 ≤ Bm lam m := by unfold Bm; positivity
lemma Dm_pos {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) : 0 < Dm lam m := by unfold Dm; positivity
lemma BD_sum {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) : Bm lam m + Dm lam m = m := by
  unfold Bm Dm; have : 0 < 1 + 2 * lam * m := by positivity
  field_simp; ring

/-- Every lowest point `0 < m < 1` gives an explicit solution with push exactly `fk lam m`. -/
theorem exists_sol {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) (hm1 : m < 1) :
    Sol lam (fk lam m)
      (fun t => Bm lam m + Dm lam m * Real.cosh (ψk (Bm lam m) (Dm lam m) (Bm_nonneg hl hm) (Dm_pos hl hm)
        (Km lam m * (t - 1 / 2))))
      (fun t => Km lam m * Dm lam m * Real.sinh (ψk (Bm lam m) (Dm lam m) (Bm_nonneg hl hm) (Dm_pos hl hm)
        (Km lam m * (t - 1 / 2))) / (Bm lam m + Dm lam m * Real.cosh (ψk (Bm lam m) (Dm lam m)
          (Bm_nonneg hl hm) (Dm_pos hl hm) (Km lam m * (t - 1 / 2))))) := by
  have hB := Bm_nonneg hl hm
  have hD := Dm_pos hl hm
  have h12 : 0 < 1 + 2 * lam * m := by positivity
  set B := Bm lam m with hBdef
  set D := Dm lam m with hDdef
  set K := Km lam m with hKdef
  set ψ := ψk B D hB hD with hψ
  have hsum : B + D = m := BD_sum hl hm
  -- identities: K^2 B = fk lam * lam, K^2 (D^2 - B^2) = fk
  have hfk : fk lam m = K ^ 2 * m ^ 2 / (1 + 2 * lam * m) := rfl
  have hDB : D ^ 2 - B ^ 2 = m ^ 2 / (1 + 2 * lam * m) := by
    rw [hBdef, hDdef]; unfold Bm Dm; field_simp; ring
  have hKB : K ^ 2 * B = fk lam m * lam := by rw [hfk, hBdef]; unfold Bm; field_simp
  have hKD : K ^ 2 * (D ^ 2 - B ^ 2) = fk lam m := by rw [hDB, hfk]; field_simp
  -- eta(t) and its derivative
  have hη : ∀ t, HasDerivAt (fun t => ψ (K * (t - 1 / 2))) ((B + D * Real.cosh (ψ (K * (t - 1 / 2))))⁻¹ * K) t := by
    intro t
    have := (ψk_hasDerivAt hB hD (K * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul K)
    exact this.congr_deriv (by ring)
  have hw : ∀ t, 0 < B + D * Real.cosh (ψ (K * (t - 1 / 2))) := fun t => by
    have := Real.cosh_pos (ψ (K * (t - 1 / 2))); positivity
  -- boundary: K/2 = phi(T), so eta(0) = -T, eta(1) = T
  have hy : 1 < (1 - B) / D := by rw [lt_div_iff₀ hD]; linarith
  have hT : Real.cosh (Tm lam m) = (1 - B) / D := Real.cosh_arcosh hy.le
  have hKT : K / 2 = φk B D (Tm lam m) := by rw [hKdef]; unfold Km φk; ring
  refine ⟨fun t _ => ⟨hw t, ?_, ?_⟩, ?_, ?_⟩
  · have := ((Real.hasDerivAt_cosh _).comp t (hη t)).const_mul D |>.const_add B
    refine this.congr_deriv ?_
    have hwt := (hw t).ne'
    simp only [Function.comp, ← hBdef, ← hDdef] at hwt ⊢
    generalize Real.cosh (ψ (K * (t - 1 / 2))) = c at hwt ⊢
    generalize Real.sinh (ψ (K * (t - 1 / 2))) = s
    field_simp
  · have hc := (Real.hasDerivAt_cosh _).comp t (hη t)
    have hs := (Real.hasDerivAt_sinh _).comp t (hη t)
    have := ((hs.const_mul (K * D)).div ((hc.const_mul D).const_add B) (hw t).ne')
    refine this.congr_deriv ?_
    have hwt := (hw t).ne'
    have hcs := Real.cosh_sq_sub_sinh_sq (ψ (K * (t - 1 / 2)))
    simp only [Function.comp, ← hBdef, ← hDdef] at hwt ⊢
    generalize Real.cosh (ψ (K * (t - 1 / 2))) = c at hwt hcs ⊢
    generalize Real.sinh (ψ (K * (t - 1 / 2))) = s at hcs ⊢
    field_simp
    linear_combination (D * c + B) * hKB + K ^ 2 * D ^ 2 * hcs + hKD
  · show B + D * Real.cosh (ψ (K * (0 - 1 / 2))) = 1
    rw [show K * (0 - 1 / 2) = -(K / 2) by ring, hKT, ← φk_neg, hψ, ψk_φk, Real.cosh_neg, hT]
    field_simp; ring
  · show B + D * Real.cosh (ψ (K * (1 - 1 / 2))) = 1
    rw [show K * (1 - 1 / 2) = K / 2 by ring, hKT, hψ, ψk_φk, hT]
    field_simp; ring

/-! Step 5: the break -- top of the curve fk on (0, 1). -/

lemma arg_ge_one {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) (hm1 : m ≤ 1) : 1 ≤ (1 - Bm lam m) / Dm lam m := by
  rw [le_div_iff₀ (Dm_pos hl hm)]; have := BD_sum hl hm; linarith

lemma fk_le {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) (hm1 : m ≤ 1) : fk lam m ≤ 16 * m ^ 2 := by
  have hB := Bm_nonneg hl hm
  have hD := Dm_pos hl hm
  have hy := arg_ge_one hl hm hm1
  have hT0 : 0 ≤ Tm lam m := Real.arcosh_nonneg hy
  have hc : Real.cosh (Tm lam m) = (1 - Bm lam m) / Dm lam m := Real.cosh_arcosh hy
  have hTs : Tm lam m ≤ Real.sinh (Tm lam m) := Real.self_le_sinh_iff.mpr hT0
  have hsc : Real.sinh (Tm lam m) < Real.cosh (Tm lam m) := Real.sinh_lt_cosh _
  have hsum := BD_sum hl hm
  have hBD : Bm lam m ≤ Dm lam m := by
    unfold Bm Dm; have : 0 < 1 + 2 * lam * m := by positivity
    rw [div_le_div_iff_of_pos_right this]; nlinarith
  -- B T <= D cosh T = 1 - B <= 1 and D sinh T <= 1 - B <= 1
  have hDc : Dm lam m * Real.cosh (Tm lam m) = 1 - Bm lam m := by rw [hc]; field_simp
  have h1 : Bm lam m * Tm lam m ≤ 1 := by nlinarith
  have h2 : Dm lam m * Real.sinh (Tm lam m) ≤ 1 := by nlinarith
  have h3 : 0 ≤ Bm lam m * Tm lam m + Dm lam m * Real.sinh (Tm lam m) := by
    have : 0 ≤ Real.sinh (Tm lam m) := by linarith
    positivity
  have h12 : 1 ≤ 1 + 2 * lam * m := by nlinarith
  unfold fk Km
  rw [div_le_iff₀ (by positivity)]
  set X := Bm lam m * Tm lam m + Dm lam m * Real.sinh (Tm lam m)
  have hX : X ≤ 2 := by linarith
  have hX2 : (2 * X) ^ 2 ≤ 16 := by nlinarith
  have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
  calc (2 * X) ^ 2 * m ^ 2 ≤ 16 * m ^ 2 := by nlinarith
    _ ≤ 16 * m ^ 2 * (1 + 2 * lam * m) := by nlinarith

lemma fk_contOn {lam δ : ℝ} (hl : 0 ≤ lam) (hδ : 0 < δ) : ContinuousOn (fk lam) (Set.Icc δ 1) := by
  have hden : ∀ x ∈ Set.Icc δ 1, 1 + 2 * lam * x ≠ 0 := fun x hx => by
    have : 0 < x := by linarith [hx.1]
    positivity
  have hBc : ContinuousOn (Bm lam) (Set.Icc δ 1) := by
    unfold Bm
    exact (continuousOn_const.mul (continuousOn_id.pow 2)).div
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) hden
  have hDc : ContinuousOn (Dm lam) (Set.Icc δ 1) := by
    unfold Dm
    exact (continuousOn_id.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id))).div
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) hden
  have hargc : ContinuousOn (fun x => (1 - Bm lam x) / Dm lam x) (Set.Icc δ 1) :=
    (continuousOn_const.sub hBc).div hDc (fun x hx => (Dm_pos hl (by linarith [hx.1])).ne')
  have hmaps : Set.MapsTo (fun x => (1 - Bm lam x) / Dm lam x) (Set.Icc δ 1) (Set.Ici 1) :=
    fun x hx => arg_ge_one hl (by linarith [hx.1]) hx.2
  have hTc : ContinuousOn (Tm lam) (Set.Icc δ 1) := Real.continuousOn_arcosh.comp hargc hmaps
  have hKc : ContinuousOn (Km lam) (Set.Icc δ 1) := by
    unfold Km
    exact continuousOn_const.mul ((hBc.mul hTc).add (hDc.mul (Real.continuous_sinh.comp_continuousOn hTc)))
  unfold fk
  exact ((hKc.pow 2).mul (continuousOn_id.pow 2)).div
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) hden

lemma fk_pos {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) (hm1 : m < 1) : 0 < fk lam m := by
  have hB := Bm_nonneg hl hm
  have hD := Dm_pos hl hm
  have hy : 1 < (1 - Bm lam m) / Dm lam m := by
    rw [lt_div_iff₀ hD]; have := BD_sum hl hm; linarith
  have hT : 0 < Tm lam m := Real.arcosh_pos hy
  have hs : 0 < Real.sinh (Tm lam m) := Real.sinh_pos_iff.mpr hT
  have hK : 0 < Km lam m := by unfold Km; positivity
  unfold fk; positivity

lemma fk_one {lam : ℝ} (hl : 0 ≤ lam) : fk lam 1 = 0 := by
  have hB := Bm_nonneg hl one_pos
  have hD := Dm_pos hl one_pos
  have hsum := BD_sum hl one_pos
  have h1 : (1 - Bm lam 1) / Dm lam 1 = 1 := by rw [div_eq_one_iff_eq hD.ne']; linarith
  unfold fk Km Tm; rw [h1]; simp [Real.arcosh_zero]

/-- **The Kepler bridge's break exists, is attained, and is the top of fk on (0, 1)**, for every lam >= 0. -/
theorem break_exists {lam : ℝ} (hl : 0 ≤ lam) :
    ∃ ms : ℝ, 0 < ms ∧ ms < 1 ∧ IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol lam μ v v'} (fk lam ms) := by
  set f2 := fk lam (1 / 2)
  have hf2 : 0 < f2 := fk_pos hl (by norm_num) (by norm_num)
  set δ := min (1 / 2) (Real.sqrt f2 / 8)
  have hδ : 0 < δ := lt_min (by norm_num) (by have := Real.sqrt_pos.mpr hf2; positivity)
  have hδ2 : 16 * δ ^ 2 < f2 := by
    have h1 : δ ≤ Real.sqrt f2 / 8 := min_le_right _ _
    have h0 : 0 ≤ δ := hδ.le
    have : δ ^ 2 ≤ (Real.sqrt f2 / 8) ^ 2 := pow_le_pow_left₀ h0 h1 2
    rw [div_pow, Real.sq_sqrt hf2.le] at this
    linarith
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  obtain ⟨ms, hms, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc δ 1)).exists_isMaxOn
    ⟨1, by linarith, le_rfl⟩ (fk_contOn hl hδ)
  have hfms : f2 ≤ fk lam ms := hmax ⟨hδ1, by norm_num⟩
  have hms0 : 0 < ms := by linarith [hms.1]
  have hms1 : ms < 1 := by
    rcases eq_or_lt_of_le hms.2 with h1 | h1
    · rw [h1, fk_one hl] at hfms; linarith
    · exact h1
  refine ⟨ms, hms0, hms1, ⟨_, _, exists_sol hl hms0 hms1⟩, ?_⟩
  rintro μ ⟨v, v', h⟩
  rcases le_or_gt μ 0 with hμ | hμ
  · linarith
  obtain ⟨m, hm, hm1, hμm⟩ := mu_formula h hμ hl
  have hfm : μ = fk lam m := by rw [hμm]; unfold fk Km Tm Bm Dm; ring
  rw [hfm]
  rcases le_or_gt δ m with hδm | hδm
  · exact hmax ⟨hδm, hm1.le⟩
  · have := fk_le hl hm hm1.le
    have : m ^ 2 < δ ^ 2 := by nlinarith
    linarith

end KeplerOde
