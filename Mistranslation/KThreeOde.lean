import Mathlib
import Mistranslation.KThreeCalc
import Mistranslation.LindemannBridge

/-! # The K_3 bridge from the ODE (2026-10-23)

Seat `v'' = mu (v^(-5/3) + lam v^(-4/3))`, `v(0) = v(1) = 1`, `v > 0`, `lam >= 0`.
With `s = v^(1/3)` the energy reads `3 s^6 s'^2 = E ((s - B)^2 - D^2)` -- Kepler's quadratic, same `B`, `D`, `E` --
and the clock `Phi3(eta) = int_0^eta (B + D cosh)^3` with `s = B + D cosh eta` runs at constant speed `sqrt(E/3)`.
So every solution's push is `KThree.f3 lam m` (`m` = cube root of the lowest value), every `0 < m < 1` is realised
by an explicit solution, and the break is the top of `f3` on (0, 1). With `KThree.top_transcendental` and the proved
Hermite-Lindemann: the K_3 break exists, is attained, and is transcendental for every algebraic `lam > 0`.
Template: `KeplerOde.lean` (same steps, weight (B + D cosh)^3 instead of (B + D cosh)). -/

namespace KThreeOde

def Sol (lam μ : ℝ) (v v' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < v t ∧ HasDerivAt v (v' t) t ∧
      HasDerivAt v' (μ * (v t ^ (-(5 / 3) : ℝ) + lam * v t ^ (-(4 / 3) : ℝ))) t) ∧ v 0 = 1 ∧ v 1 = 1

/-! Step 0: the cube root. -/

noncomputable def cr (x : ℝ) : ℝ := x ^ ((1 : ℝ) / 3)

lemma cr_pos {x : ℝ} (hx : 0 < x) : 0 < cr x := Real.rpow_pos_of_pos hx _

lemma cr_cube {x : ℝ} (hx : 0 ≤ x) : cr x ^ 3 = x := by
  unfold cr; rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma cr_of_cube {s : ℝ} (hs : 0 ≤ s) : cr (s ^ 3) = s := by
  unfold cr; rw [← Real.rpow_natCast, ← Real.rpow_mul hs]; norm_num

lemma rpow_third {x : ℝ} (hx : 0 < x) (k : ℕ) : x ^ (-((k : ℝ) / 3)) = (cr x ^ k)⁻¹ := by
  unfold cr
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_neg hx.le]
  ring_nf

lemma rpow53 {x : ℝ} (hx : 0 < x) : x ^ (-(5 / 3) : ℝ) = (cr x ^ 5)⁻¹ := by
  rw [← rpow_third hx 5]; norm_num

lemma rpow43 {x : ℝ} (hx : 0 < x) : x ^ (-(4 / 3) : ℝ) = (cr x ^ 4)⁻¹ := by
  rw [← rpow_third hx 4]; norm_num

lemma cr_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : cr x < cr y :=
  Real.rpow_lt_rpow hx hxy (by norm_num)

/-- The cube root of a solution moves with speed `v' / (3 s^2)`. -/
lemma s_deriv {v : ℝ → ℝ} {w t : ℝ} (hv : 0 < v t) (hd : HasDerivAt v w t) :
    HasDerivAt (fun x => cr (v x)) (w / (3 * cr (v t) ^ 2)) t := by
  have h := hd.rpow_const (p := (1 : ℝ) / 3) (Or.inl hv.ne')
  have e : v t ^ ((1 : ℝ) / 3 - 1) = (cr (v t) ^ 2)⁻¹ := by
    rw [← rpow_third hv 2]; norm_num
  rw [e] at h
  have hc := cr_pos hv
  exact h.congr_deriv (by field_simp)

/-! Step 1: energy, lowest point, sign of v'. -/

lemma energy {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, v' t * v' t + 3 * μ * (cr (v t) ^ 2)⁻¹ + 6 * μ * lam * (cr (v t))⁻¹
      = v' 0 * v' 0 + 3 * μ * (cr (v 0) ^ 2)⁻¹ + 6 * μ * lam * (cr (v 0))⁻¹ := by
  refine MemsOde.const_on (f := fun t => v' t * v' t + 3 * μ * (cr (v t) ^ 2)⁻¹ + 6 * μ * lam * (cr (v t))⁻¹) ?_
  intro x hx
  obtain ⟨hv, hd, hdd⟩ := h.1 x hx
  rw [rpow53 hv, rpow43 hv] at hdd
  have hs := s_deriv hv hd
  have hc := cr_pos hv
  have := ((hdd.mul hdd).add (((hs.pow 2).inv (pow_pos hc 2).ne').const_mul (3 * μ))).add
    ((hs.inv hc.ne').const_mul (6 * μ * lam))
  refine this.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma rolle {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') : ∃ t0 ∈ Set.Ioo (0 : ℝ) 1, v' t0 = 0 := by
  have hc : ContinuousOn v (Set.Icc 0 1) := fun t ht => (h.1 t ht).2.1.continuousAt.continuousWithinAt
  exact exists_hasDerivAt_eq_zero (by norm_num) hc (by rw [h.2.1, h.2.2])
    (fun t ht => (h.1 t (Set.Ioo_subset_Icc_self ht)).2.1)

lemma vprime_pos {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') (hμ : 0 < μ) (hl : 0 ≤ lam) {t0 t : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hlt : t0 < t) : v' t0 < v' t := by
  have hsub : Set.Icc t0 t ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc ht0.1 ht.2
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope v'
    (fun s => μ * (v s ^ (-(5 / 3) : ℝ) + lam * v s ^ (-(4 / 3) : ℝ))) hlt
    (fun s hs => (h.1 s (hsub hs)).2.2.continuousAt.continuousWithinAt)
    (fun s hs => (h.1 s (hsub (Set.Ioo_subset_Icc_self hs))).2.2)
  have hvc := (h.1 c (hsub (Set.Ioo_subset_Icc_self hc))).1
  have hpos : 0 < μ * (v c ^ (-(5 / 3) : ℝ) + lam * v c ^ (-(4 / 3) : ℝ)) := by
    have h1 : 0 < v c ^ (-(5 / 3) : ℝ) := Real.rpow_pos_of_pos hvc _
    have h2 : 0 ≤ lam * v c ^ (-(4 / 3) : ℝ) := mul_nonneg hl (Real.rpow_pos_of_pos hvc _).le
    positivity
  rw [hslope] at hpos
  have := (div_pos_iff_of_pos_right (sub_pos.mpr hlt)).mp hpos
  linarith

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

/-! Step 2: the K_3 clock `Phi3 = int_0^eta (B + D cosh)^3`, read through `s = B + D cosh eta`. -/

noncomputable def Φ3 (B D η : ℝ) : ℝ :=
  (B ^ 3 + 3 / 2 * B * D ^ 2) * η + Real.sinh η * (3 * B ^ 2 * D + 3 / 2 * B * D ^ 2 * Real.cosh η
    + 2 / 3 * D ^ 3 + D ^ 3 * Real.cosh η ^ 2 / 3)

lemma Φ3_hasDerivAt (B D η : ℝ) : HasDerivAt (Φ3 B D) ((B + D * Real.cosh η) ^ 3) η := by
  have hc := Real.hasDerivAt_cosh η
  have hs := Real.hasDerivAt_sinh η
  have h := ((hasDerivAt_id' η).const_mul (B ^ 3 + 3 / 2 * B * D ^ 2)).add
    (hs.mul ((((hc.const_mul (3 / 2 * B * D ^ 2)).const_add (3 * B ^ 2 * D)).add_const (2 / 3 * D ^ 3)).add
      ((hc.pow 2).const_mul (D ^ 3 / 3))))
  have hcs := Real.cosh_sq_sub_sinh_sq η
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
    simp only [Φ3, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; ring)).congr_deriv ?_
  simp only [Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat]
  linear_combination (-(3 / 2 * B * D ^ 2) - 2 / 3 * D ^ 3 * Real.cosh η) * hcs

lemma Φ3_cont (B D : ℝ) : Continuous (Φ3 B D) :=
  continuous_iff_continuousAt.mpr fun x => (Φ3_hasDerivAt B D x).continuousAt

lemma Φ3_zero (B D : ℝ) : Φ3 B D 0 = 0 := by simp [Φ3]

noncomputable def G3 (B D x : ℝ) : ℝ := Φ3 B D (Real.arcosh ((x - B) / D))

lemma clock_hasDerivAt {B D : ℝ} {s : ℝ → ℝ} {w t : ℝ} (hD : 0 < D) (hx : B + D < s t)
    (hd : HasDerivAt s w t) :
    HasDerivAt (fun x => G3 B D (s x)) (s t ^ 3 * w / (D * Real.sqrt (((s t - B) / D) ^ 2 - 1))) t := by
  have hy : 1 < (s t - B) / D := by rw [lt_div_iff₀ hD]; linarith
  have hq : 0 < ((s t - B) / D) ^ 2 - 1 := by nlinarith
  have hyd : HasDerivAt (fun x => (s x - B) / D) (w / D) t := (hd.sub_const B).div_const D
  have hA := (Real.hasDerivAt_arcosh hy).comp t hyd
  have h := (Φ3_hasDerivAt B D _).comp t hA
  refine h.congr_deriv ?_
  simp only [Function.comp]
  rw [Real.cosh_arcosh hy.le]
  have hsq := Real.sqrt_pos.mpr hq
  have hD0 : D ≠ 0 := hD.ne'
  generalize Real.sqrt (((s t - B) / D) ^ 2 - 1) = Q at hsq ⊢
  field_simp
  ring

lemma clock_speed {B D E x w : ℝ} (hD : 0 < D) (hx : B + D < x) (hE : 0 < E)
    (hshell : 3 * x ^ 6 * w ^ 2 = E * ((x - B) ^ 2 - D ^ 2)) :
    (x ^ 3 * w / (D * Real.sqrt (((x - B) / D) ^ 2 - 1))) ^ 2 = Real.sqrt (E / 3) ^ 2 := by
  have hy : 1 < (x - B) / D := by rw [lt_div_iff₀ hD]; linarith
  have hpos : 0 < (x - B) ^ 2 - D ^ 2 := by nlinarith
  have hq : 0 < ((x - B) / D) ^ 2 - 1 := by nlinarith
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt (by positivity)]
  have e : D ^ 2 * (((x - B) / D) ^ 2 - 1) = (x - B) ^ 2 - D ^ 2 := by field_simp
  rw [e, div_eq_iff hpos.ne']
  linear_combination hshell / 3

/-! Step 3: the shell and the clock rate along `s = v^(1/3)`. -/

lemma shell {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') (hμ : 0 < μ) (hl : 0 ≤ lam) {t0 : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1)
    (hz : v' t0 = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 3 * cr (v t) ^ 6 * (v' t / (3 * cr (v t) ^ 2)) ^ 2
      = (μ / cr (v t0) ^ 2 + 2 * μ * lam / cr (v t0)) *
      ((cr (v t) - μ * lam / (μ / cr (v t0) ^ 2 + 2 * μ * lam / cr (v t0))) ^ 2
        - (cr (v t0) - μ * lam / (μ / cr (v t0) ^ 2 + 2 * μ * lam / cr (v t0))) ^ 2) := by
  intro t ht
  have hm := cr_pos (h.1 t0 ht0).1
  have hs := cr_pos (h.1 t ht).1
  have e1 := energy h t ht
  have e2 := energy h t0 ht0
  rw [hz] at e2
  set m := cr (v t0)
  set s := cr (v t)
  set E := μ / m ^ 2 + 2 * μ * lam / m with hEdef
  have hEm : E * m ^ 2 = μ + 2 * μ * lam * m := by rw [hEdef]; field_simp
  have hEt : v' t ^ 2 = 3 * E - 3 * μ / s ^ 2 - 6 * μ * lam / s := by
    rw [hEdef]; field_simp at e1 e2 ⊢; nlinarith [e1, e2]
  have hE0 : E ≠ 0 := by rw [hEdef]; positivity
  have L : 3 * s ^ 6 * (v' t / (3 * s ^ 2)) ^ 2 = s ^ 2 * v' t ^ 2 / 3 := by field_simp
  have R : E * ((s - μ * lam / E) ^ 2 - (m - μ * lam / E) ^ 2)
      = E * s ^ 2 - 2 * μ * lam * s - E * m ^ 2 + 2 * μ * lam * m := by field_simp; ring
  rw [L, R, hEt]
  have : s ^ 2 * (3 * E - 3 * μ / s ^ 2 - 6 * μ * lam / s) / 3 = E * s ^ 2 - μ - 2 * μ * lam * s := by
    field_simp; ring
  rw [this]; linarith [hEm]

lemma pos_of_sq_eq {X K : ℝ} (hX : 0 < X) (hK : 0 < K) (h : X ^ 2 = K ^ 2) : X = K := by nlinarith

lemma above_s {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') (hμ : 0 < μ) (hl : 0 ≤ lam) {t0 s : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hz : v' t0 = 0) (hne : s ≠ t0) :
    cr (v t0) < cr (v s) := cr_lt (h.1 t0 ht0).1.le (above h hμ hl ht0 hs hz hne)

/-- The K_3 clock runs at `+sqrt(E/3)` right of the lowest point and `-sqrt(E/3)` left of it. -/
lemma clock_rate {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') (hμ : 0 < μ) (hl : 0 ≤ lam) {t0 s : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hz : v' t0 = 0) (hne : s ≠ t0) :
    HasDerivAt (fun x => G3 (μ * lam / (μ / cr (v t0) ^ 2 + 2 * μ * lam / cr (v t0)))
        (cr (v t0) - μ * lam / (μ / cr (v t0) ^ 2 + 2 * μ * lam / cr (v t0))) (cr (v x)))
      ((if t0 < s then 1 else -1) * Real.sqrt ((μ / cr (v t0) ^ 2 + 2 * μ * lam / cr (v t0)) / 3)) s := by
  have hm := cr_pos (h.1 t0 ht0).1
  set E := μ / cr (v t0) ^ 2 + 2 * μ * lam / cr (v t0) with hEdef
  have hE : 0 < E := by
    have : 0 ≤ 2 * μ * lam / cr (v t0) := by positivity
    have : 0 < μ / cr (v t0) ^ 2 := by positivity
    linarith
  set B := μ * lam / E with hB
  set D := cr (v t0) - B with hD
  have hDpos : 0 < D := by
    rw [hD, hB, sub_pos, div_lt_iff₀ hE, hEdef]
    field_simp
    nlinarith [mul_pos hμ hm, mul_nonneg hμ.le hl]
  have hab := above_s h hμ hl ht0 hs hz hne
  have hx : B + D < cr (v s) := by rw [hD]; linarith
  have hvs := (h.1 s hs).1
  have hd := s_deriv hvs (h.1 s hs).2.1
  have hcl := clock_hasDerivAt (s := fun x => cr (v x)) hDpos hx hd
  have hsp := clock_speed hDpos hx hE (shell h hμ hl ht0 hz s hs)
  have hy : 1 < (cr (v s) - B) / D := by rw [lt_div_iff₀ hDpos]; linarith
  have hq : 0 < ((cr (v s) - B) / D) ^ 2 - 1 := by nlinarith
  have hQ := Real.sqrt_pos.mpr hq
  have hcs := cr_pos hvs
  have hK := Real.sqrt_pos.mpr (show 0 < E / 3 by positivity)
  split_ifs with hlt
  · have hw : 0 < v' s := by have := vprime_pos h hμ hl ht0 hs hlt; linarith
    convert hcl using 1
    rw [one_mul]
    exact (pos_of_sq_eq (by positivity) hK hsp).symm
  · have hlt' : s < t0 := lt_of_le_of_ne (not_lt.mp hlt) hne
    have hw : v' s < 0 := by have := vprime_pos h hμ hl hs ht0 hlt'; linarith
    convert hcl using 1
    have hw3 : v' s / (3 * cr (v s) ^ 2) < 0 := div_neg_of_neg_of_pos hw (by positivity)
    have hneg : 0 < -(cr (v s) ^ 3 * (v' s / (3 * cr (v s) ^ 2)) / (D * Real.sqrt (((cr (v s) - B) / D) ^ 2 - 1))) := by
      rw [neg_pos]; exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hw3) (by positivity)
    have := pos_of_sq_eq hneg hK (by rw [neg_sq]; exact hsp)
    linarith

lemma cr_one : cr 1 = 1 := by simp [cr]

lemma cr_contOn {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') {a b : ℝ} (hab : Set.Icc a b ⊆ Set.Icc 0 1) :
    ContinuousOn (fun x => cr (v x)) (Set.Icc a b) := fun t ht =>
  (s_deriv (h.1 t (hab ht)).1 (h.1 t (hab ht)).2.1).continuousAt.continuousWithinAt

/-- **Every solution of the K_3 bridge sits on the push curve `KThree.f3`**: `mu = f3 lam m` for some `0 < m < 1`
(`m` = cube root of the lowest value). Derived from the ODE through the clock `Phi3`, no integrals. -/
theorem mu_formula {lam μ : ℝ} {v v' : ℝ → ℝ} (h : Sol lam μ v v') (hμ : 0 < μ) (hl : 0 ≤ lam) :
    ∃ m : ℝ, 0 < m ∧ m < 1 ∧ μ = KThree.f3 lam m := by
  obtain ⟨t0, ht0, hz⟩ := rolle h
  have ht0' := Set.Ioo_subset_Icc_self ht0
  have hm := cr_pos (h.1 t0 ht0').1
  set m := cr (v t0) with hmdef
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
  set K := Real.sqrt (E / 3) with hK
  have hcont : ∀ a b : ℝ, Set.Icc a b ⊆ Set.Icc 0 1 →
      ContinuousOn (fun x => G3 B D (cr (v x))) (Set.Icc a b) := by
    intro a b hab
    have hvc := cr_contOn h hab
    have hmaps : Set.MapsTo (fun x => (cr (v x) - B) / D) (Set.Icc a b) (Set.Ici 1) := by
      intro x hx
      have hxm : m ≤ cr (v x) := by
        rcases eq_or_ne x t0 with hx0 | hx0
        · rw [hx0]
        · exact (above_s h hμ hl ht0' (hab hx) hz hx0).le
      show 1 ≤ (cr (v x) - B) / D
      rw [le_div_iff₀ hDpos]; linarith
    unfold G3
    exact (Φ3_cont B D).comp_continuousOn
      (Real.continuousOn_arcosh.comp ((hvc.sub continuousOn_const).div_const D) hmaps)
  have hG0 : G3 B D m = 0 := by
    unfold G3
    rw [show m - B = D from rfl, div_self hDpos.ne', Real.arcosh_zero, Φ3_zero]
  -- right half
  have hR : G3 B D (cr (v 1)) = K * (1 - t0) := by
    obtain ⟨c, _, hsl⟩ := exists_hasDerivAt_eq_slope (fun x => G3 B D (cr (v x)) - K * x) (fun _ => (0 : ℝ))
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
  have hL : G3 B D (cr (v 0)) = K * t0 := by
    obtain ⟨c, _, hsl⟩ := exists_hasDerivAt_eq_slope (fun x => G3 B D (cr (v x)) + K * x) (fun _ => (0 : ℝ))
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
  rw [h.2.2, cr_one] at hR
  rw [h.2.1, cr_one] at hL
  have hG1 : G3 B D 1 = K / 2 := by linarith
  have hm1 : m < 1 := by
    have := above_s h hμ hl ht0' ⟨zero_le_one, le_rfl⟩ hz (ne_of_gt ht0.2)
    rw [h.2.2, cr_one] at this; exact this
  have h12 : 0 < 1 + 2 * lam * m := by positivity
  refine ⟨m, hm, hm1, ?_⟩
  have hB' : KeplerOde.Bm lam m = B := by unfold KeplerOde.Bm; rw [hB, hEdef]; field_simp
  have hD' : KeplerOde.Dm lam m = D := by
    rw [hD, ← hB']; unfold KeplerOde.Bm KeplerOde.Dm; field_simp; ring
  have hy : 1 ≤ (1 - B) / D := by rw [le_div_iff₀ hDpos, hD]; linarith
  have hI : KThree.I3 lam m = G3 B D 1 := by
    unfold KThree.I3 G3 Φ3 KeplerOde.Tm KeplerOde.Cy
    rw [hB', hD', Real.cosh_arcosh hy]
  have hK2 : K ^ 2 = E / 3 := Real.sq_sqrt (by positivity)
  have hEm : E * m ^ 2 = μ * (1 + 2 * lam * m) := by rw [hEdef]; field_simp
  unfold KThree.f3
  rw [hI, hG1, eq_div_iff h12.ne']
  linear_combination (-(m ^ 2) * 3) * hK2 - hEm

/-! Step 4: existence -- the inverse K_3 clock. -/

lemma Φ3_strictMono {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D) : StrictMono (Φ3 B D) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(Φ3_hasDerivAt B D x).deriv]
  have := Real.cosh_pos x
  positivity

lemma Φ3_neg (B D η : ℝ) : Φ3 B D (-η) = -Φ3 B D η := by simp [Φ3, Real.sinh_neg]; ring

lemma Φ3_ge {B D η : ℝ} (hB : 0 ≤ B) (hD : 0 < D) (hη : 0 ≤ η) : D ^ 3 * η ≤ Φ3 B D η := by
  have hsh : η ≤ Real.sinh η := Real.self_le_sinh_iff.mpr hη
  have hs0 : 0 ≤ Real.sinh η := by linarith
  have hc1 := Real.one_le_cosh η
  have hc0 : 0 ≤ Real.cosh η := by linarith
  have h1 : 0 ≤ (B ^ 3 + 3 / 2 * B * D ^ 2) * η := by positivity
  have h2 : 0 ≤ Real.sinh η * (3 * B ^ 2 * D + 3 / 2 * B * D ^ 2 * Real.cosh η) := by positivity
  have h3 : D ^ 3 * η ≤ D ^ 3 * Real.sinh η := mul_le_mul_of_nonneg_left hsh (by positivity)
  have h4 : 0 ≤ Real.sinh η * (D ^ 3 * (Real.cosh η ^ 2 - 1) / 3) := by
    have : 0 ≤ Real.cosh η ^ 2 - 1 := by nlinarith
    positivity
  unfold Φ3
  nlinarith [h1, h2, h3, h4]

lemma Φ3_surj {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D) : Function.Surjective (Φ3 B D) := by
  have hD3 : 0 < D ^ 3 := by positivity
  apply (Φ3_cont B D).surjective
  · apply Filter.tendsto_atTop_mono' Filter.atTop _ (Filter.tendsto_id.const_mul_atTop hD3)
    filter_upwards [Filter.eventually_ge_atTop 0] with x hx
    exact Φ3_ge hB hD hx
  · apply Filter.tendsto_atBot_mono' Filter.atBot _ (Filter.tendsto_id.const_mul_atBot hD3)
    filter_upwards [Filter.eventually_le_atBot 0] with x hx
    have := Φ3_ge hB hD (show 0 ≤ -x by linarith)
    rw [Φ3_neg] at this
    simp only [id]; linarith

noncomputable def ψ3 (B D : ℝ) (hB : 0 ≤ B) (hD : 0 < D) : ℝ → ℝ :=
  (StrictMono.orderIsoOfSurjective (Φ3 B D) (Φ3_strictMono hB hD) (Φ3_surj hB hD)).symm

lemma Φ3_ψ3 {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D) (y : ℝ) : Φ3 B D (ψ3 B D hB hD y) = y :=
  (StrictMono.orderIsoOfSurjective (Φ3 B D) (Φ3_strictMono hB hD) (Φ3_surj hB hD)).apply_symm_apply y

lemma ψ3_Φ3 {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D) (x : ℝ) : ψ3 B D hB hD (Φ3 B D x) = x :=
  (StrictMono.orderIsoOfSurjective (Φ3 B D) (Φ3_strictMono hB hD) (Φ3_surj hB hD)).symm_apply_apply x

lemma ψ3_hasDerivAt {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D) (y : ℝ) :
    HasDerivAt (ψ3 B D hB hD) ((B + D * Real.cosh (ψ3 B D hB hD y)) ^ 3)⁻¹ y := by
  have hc : Continuous (ψ3 B D hB hD) :=
    (StrictMono.orderIsoOfSurjective (Φ3 B D) (Φ3_strictMono hB hD) (Φ3_surj hB hD)).symm.continuous
  have hpos : 0 < (B + D * Real.cosh (ψ3 B D hB hD y)) ^ 3 := by
    have := Real.cosh_pos (ψ3 B D hB hD y); positivity
  exact HasDerivAt.of_local_left_inverse hc.continuousAt (Φ3_hasDerivAt B D _) hpos.ne'
    (Filter.Eventually.of_forall (Φ3_ψ3 hB hD))

lemma I3_eq {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) (hm1 : m ≤ 1) :
    KThree.I3 lam m = Φ3 (KeplerOde.Bm lam m) (KeplerOde.Dm lam m) (KeplerOde.Tm lam m) := by
  have hy := KeplerOde.arg_ge_one hl hm hm1
  unfold KThree.I3 Φ3
  rw [show KeplerOde.Tm lam m = Real.arcosh ((1 - KeplerOde.Bm lam m) / KeplerOde.Dm lam m) from rfl,
    Real.cosh_arcosh hy]
  rfl

/-- Every cube-rooted lowest point `0 < m < 1` gives an explicit solution with push exactly `f3 lam m`. -/
theorem exists_sol {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) (hm1 : m < 1) :
    ∃ v v' : ℝ → ℝ, Sol lam (KThree.f3 lam m) v v' := by
  have hB := KeplerOde.Bm_nonneg hl hm
  have hD := KeplerOde.Dm_pos hl hm
  have h12 : 0 < 1 + 2 * lam * m := by positivity
  have hI := I3_eq hl hm hm1.le
  set B := KeplerOde.Bm lam m with hBdef
  set D := KeplerOde.Dm lam m with hDdef
  set K := 2 * KThree.I3 lam m with hKdef
  set μ := KThree.f3 lam m with hμdef
  set ψ := ψ3 B D hB hD with hψ
  have hsum : B + D = m := KeplerOde.BD_sum hl hm
  have hμK : μ * (1 + 2 * lam * m) = 3 * K ^ 2 * m ^ 2 := by
    rw [hμdef, hKdef]; unfold KThree.f3; field_simp; ring
  have hKB : 3 * K ^ 2 * B = μ * lam := by
    rw [hBdef]; unfold KeplerOde.Bm; field_simp; linear_combination (-lam) * hμK
  have hKD : 3 * K ^ 2 * D ^ 2 = μ * (1 + lam * B) := by
    rw [hBdef, hDdef]; unfold KeplerOde.Bm KeplerOde.Dm; field_simp
    linear_combination (-(1 + lam * m) ^ 2) * hμK
  have hη : ∀ t, HasDerivAt (fun t => ψ (K * (t - 1 / 2)))
      (((B + D * Real.cosh (ψ (K * (t - 1 / 2)))) ^ 3)⁻¹ * K) t := by
    intro t
    have := (ψ3_hasDerivAt hB hD (K * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul K)
    exact this.congr_deriv (by ring)
  have hw : ∀ t, 0 < B + D * Real.cosh (ψ (K * (t - 1 / 2))) := fun t => by
    have := Real.cosh_pos (ψ (K * (t - 1 / 2))); positivity
  have hy : 1 < (1 - B) / D := by rw [lt_div_iff₀ hD]; linarith
  have hT : Real.cosh (KeplerOde.Tm lam m) = (1 - B) / D := Real.cosh_arcosh hy.le
  have hKT : K / 2 = Φ3 B D (KeplerOde.Tm lam m) := by rw [hKdef, hI]; ring
  refine ⟨fun t => (B + D * Real.cosh (ψ (K * (t - 1 / 2)))) ^ 3,
    fun t => 3 * K * D * Real.sinh (ψ (K * (t - 1 / 2))) / (B + D * Real.cosh (ψ (K * (t - 1 / 2)))),
    fun t _ => ⟨pow_pos (hw t) 3, ?_, ?_⟩, ?_, ?_⟩
  · have := ((((Real.hasDerivAt_cosh _).comp t (hη t)).const_mul D).const_add B).pow 3
    refine this.congr_deriv ?_
    have hwt := (hw t).ne'
    simp only [Function.comp] at hwt ⊢
    generalize Real.cosh (ψ (K * (t - 1 / 2))) = c at hwt ⊢
    generalize Real.sinh (ψ (K * (t - 1 / 2))) = s
    field_simp
    ring
  · have hc := (Real.hasDerivAt_cosh _).comp t (hη t)
    have hs := (Real.hasDerivAt_sinh _).comp t (hη t)
    have := ((hs.const_mul (3 * K * D)).div ((hc.const_mul D).const_add B) (hw t).ne')
    have hS := hw t
    rw [rpow53 (pow_pos hS 3), rpow43 (pow_pos hS 3), cr_of_cube hS.le]
    refine this.congr_deriv ?_
    have hcs := Real.cosh_sq_sub_sinh_sq (ψ (K * (t - 1 / 2)))
    simp only [Function.comp] at hS ⊢
    generalize Real.cosh (ψ (K * (t - 1 / 2))) = c at hS hcs ⊢
    generalize Real.sinh (ψ (K * (t - 1 / 2))) = s at hcs ⊢
    have htarget : μ * (((B + D * c) ^ 5)⁻¹ + lam * ((B + D * c) ^ 4)⁻¹)
        = (3 * K ^ 2 * D ^ 2 + 3 * K ^ 2 * B * D * c) / (B + D * c) ^ 5 := by
      rw [show μ * (((B + D * c) ^ 5)⁻¹ + lam * ((B + D * c) ^ 4)⁻¹)
          = (μ * (1 + lam * B) + μ * lam * D * c) / (B + D * c) ^ 5 by field_simp; ring, ← hKD, ← hKB]
    rw [htarget]
    field_simp
    linear_combination (4 * KThree.I3 lam m ^ 2 * D) * hcs
  · show (B + D * Real.cosh (ψ (K * (0 - 1 / 2)))) ^ 3 = 1
    rw [show K * (0 - 1 / 2) = -(K / 2) by ring, hKT, ← Φ3_neg, hψ, ψ3_Φ3, Real.cosh_neg, hT]
    field_simp; ring
  · show (B + D * Real.cosh (ψ (K * (1 - 1 / 2)))) ^ 3 = 1
    rw [show K * (1 - 1 / 2) = K / 2 by ring, hKT, hψ, ψ3_Φ3, hT]
    field_simp; ring

/-! Step 5: the break -- top of `f3` on (0, 1), attained, and transcendental. -/

lemma I3_bounds {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) (hm1 : m ≤ 1) :
    0 ≤ KThree.I3 lam m ∧ KThree.I3 lam m ≤ 8 := by
  have hB := KeplerOde.Bm_nonneg hl hm
  have hD := KeplerOde.Dm_pos hl hm
  have hy := KeplerOde.arg_ge_one hl hm hm1
  have hT0 : 0 ≤ KeplerOde.Tm lam m := Real.arcosh_nonneg hy
  have hc : Real.cosh (KeplerOde.Tm lam m) = KeplerOde.Cy lam m := Real.cosh_arcosh hy
  have hTs : KeplerOde.Tm lam m ≤ Real.sinh (KeplerOde.Tm lam m) := Real.self_le_sinh_iff.mpr hT0
  have hsc : Real.sinh (KeplerOde.Tm lam m) < Real.cosh (KeplerOde.Tm lam m) := Real.sinh_lt_cosh _
  have hsum := KeplerOde.BD_sum hl hm
  have hBD : KeplerOde.Bm lam m ≤ KeplerOde.Dm lam m := by
    unfold KeplerOde.Bm KeplerOde.Dm; have : 0 < 1 + 2 * lam * m := by positivity
    rw [div_le_div_iff_of_pos_right this]; nlinarith
  have hDc : KeplerOde.Dm lam m * KeplerOde.Cy lam m = 1 - KeplerOde.Bm lam m := by
    unfold KeplerOde.Cy; field_simp
  set B := KeplerOde.Bm lam m
  set D := KeplerOde.Dm lam m
  set T := KeplerOde.Tm lam m
  set C := KeplerOde.Cy lam m
  set sh := Real.sinh T
  have hs0 : 0 ≤ sh := by linarith
  have hB1 : B ≤ 1 := by linarith
  have hD1 : D ≤ 1 := by linarith
  have hY0 : 0 ≤ D * C := by rw [hDc]; linarith
  have hY1 : D * C ≤ 1 := by rw [hDc]; linarith
  have hX0 : 0 ≤ D * sh := by positivity
  have hX1 : D * sh ≤ 1 := by
    have : D * sh ≤ D * C := by rw [← hc]; exact mul_le_mul_of_nonneg_left hsc.le hD.le
    linarith
  have hBT0 : 0 ≤ B * T := by positivity
  have hBT1 : B * T ≤ 1 := by
    have h1 : B * T ≤ D * T := mul_le_mul_of_nonneg_right hBD hT0
    have h2 : D * T ≤ D * sh := mul_le_mul_of_nonneg_left hTs hD.le
    linarith
  have hB2 : B ^ 2 ≤ 1 := by nlinarith
  have hD2 : D ^ 2 ≤ 1 := by nlinarith
  have e : KThree.I3 lam m = B ^ 2 * (B * T) + 3 / 2 * D ^ 2 * (B * T) + 3 * B ^ 2 * (D * sh)
      + 3 / 2 * B * (D * sh) * (D * C) + 2 / 3 * D ^ 2 * (D * sh) + (D * sh) * (D * C) ^ 2 / 3 := by
    unfold KThree.I3; ring
  rw [e]
  refine ⟨by positivity, ?_⟩
  have p1 : B ^ 2 * (B * T) ≤ 1 := mul_le_one₀ hB2 hBT0 hBT1
  have p2 : D ^ 2 * (B * T) ≤ 1 := mul_le_one₀ hD2 hBT0 hBT1
  have p3 : B ^ 2 * (D * sh) ≤ 1 := mul_le_one₀ hB2 hX0 hX1
  have p4 : B * (D * sh) * (D * C) ≤ 1 := mul_le_one₀ (mul_le_one₀ hB1 hX0 hX1) hY0 hY1
  have p5 : D ^ 2 * (D * sh) ≤ 1 := mul_le_one₀ hD2 hX0 hX1
  have p6 : (D * sh) * (D * C) ^ 2 ≤ 1 := mul_le_one₀ hX1 (by positivity) (by nlinarith)
  linarith

lemma f3_le {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) (hm1 : m ≤ 1) : KThree.f3 lam m ≤ 768 * m ^ 2 := by
  obtain ⟨h0, h8⟩ := I3_bounds hl hm hm1
  have hI2 : KThree.I3 lam m ^ 2 ≤ 64 := by nlinarith
  have h12 : 1 ≤ 1 + 2 * lam * m := by nlinarith
  unfold KThree.f3
  rw [div_le_iff₀ (by positivity)]
  have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
  calc 12 * KThree.I3 lam m ^ 2 * m ^ 2 ≤ 768 * m ^ 2 := by nlinarith
    _ ≤ 768 * m ^ 2 * (1 + 2 * lam * m) := by nlinarith

lemma f3_contOn {lam δ : ℝ} (hl : 0 ≤ lam) (hδ : 0 < δ) : ContinuousOn (KThree.f3 lam) (Set.Icc δ 1) := by
  have hden : ∀ x ∈ Set.Icc δ 1, 1 + 2 * lam * x ≠ 0 := fun x hx => by
    have : 0 < x := by linarith [hx.1]
    positivity
  have hBc : ContinuousOn (KeplerOde.Bm lam) (Set.Icc δ 1) := by
    unfold KeplerOde.Bm
    exact (continuousOn_const.mul (continuousOn_id.pow 2)).div
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) hden
  have hDc : ContinuousOn (KeplerOde.Dm lam) (Set.Icc δ 1) := by
    unfold KeplerOde.Dm
    exact (continuousOn_id.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id))).div
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) hden
  have hCc : ContinuousOn (KeplerOde.Cy lam) (Set.Icc δ 1) :=
    (continuousOn_const.sub hBc).div hDc (fun x hx => (KeplerOde.Dm_pos hl (by linarith [hx.1])).ne')
  have hmaps : Set.MapsTo (KeplerOde.Cy lam) (Set.Icc δ 1) (Set.Ici 1) :=
    fun x hx => KeplerOde.arg_ge_one hl (by linarith [hx.1]) hx.2
  have hTc : ContinuousOn (KeplerOde.Tm lam) (Set.Icc δ 1) := Real.continuousOn_arcosh.comp hCc hmaps
  have hSc : ContinuousOn (fun x => Real.sinh (KeplerOde.Tm lam x)) (Set.Icc δ 1) :=
    Real.continuous_sinh.comp_continuousOn hTc
  have hIc : ContinuousOn (KThree.I3 lam) (Set.Icc δ 1) := by
    unfold KThree.I3
    exact (((hBc.pow 3).add ((continuousOn_const.mul hBc).mul (hDc.pow 2))).mul hTc).add
      (hSc.mul (((((continuousOn_const.mul (hBc.pow 2)).mul hDc).add
        (((continuousOn_const.mul hBc).mul (hDc.pow 2)).mul hCc)).add (continuousOn_const.mul (hDc.pow 3))).add
        (((hDc.pow 3).mul (hCc.pow 2)).div_const 3)))
  unfold KThree.f3
  exact ((continuousOn_const.mul (hIc.pow 2)).mul (continuousOn_id.pow 2)).div
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) hden

lemma f3_pos {lam m : ℝ} (hl : 0 ≤ lam) (hm : 0 < m) (hm1 : m < 1) : 0 < KThree.f3 lam m := by
  have := KThree.I3_pos hl hm hm1
  unfold KThree.f3; positivity

lemma f3_one {lam : ℝ} (hl : 0 ≤ lam) : KThree.f3 lam 1 = 0 := by
  have hD := KeplerOde.Dm_pos hl one_pos
  have hsum := KeplerOde.BD_sum hl one_pos
  have h1 : KeplerOde.Cy lam 1 = 1 := by
    unfold KeplerOde.Cy; rw [div_eq_one_iff_eq hD.ne']; linarith
  have hT : KeplerOde.Tm lam 1 = 0 := by
    rw [show KeplerOde.Tm lam 1 = Real.arcosh (KeplerOde.Cy lam 1) from rfl, h1, Real.arcosh_zero]
  unfold KThree.f3 KThree.I3; rw [hT]; simp

/-- **The K_3 break exists, is attained, and is the top of `f3` on (0, 1)**, for every lam >= 0. -/
theorem break_exists {lam : ℝ} (hl : 0 ≤ lam) :
    ∃ ms : ℝ, 0 < ms ∧ ms < 1 ∧ (∀ m ∈ Set.Ioo (0 : ℝ) 1, KThree.f3 lam m ≤ KThree.f3 lam ms) ∧
      IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol lam μ v v'} (KThree.f3 lam ms) := by
  set f2 := KThree.f3 lam (1 / 2)
  have hf2 : 0 < f2 := f3_pos hl (by norm_num) (by norm_num)
  set δ := min (1 / 2) (Real.sqrt f2 / 32)
  have hδ : 0 < δ := lt_min (by norm_num) (by have := Real.sqrt_pos.mpr hf2; positivity)
  have hδ2 : 768 * δ ^ 2 < f2 := by
    have h1 : δ ≤ Real.sqrt f2 / 32 := min_le_right _ _
    have h0 : 0 ≤ δ := hδ.le
    have : δ ^ 2 ≤ (Real.sqrt f2 / 32) ^ 2 := pow_le_pow_left₀ h0 h1 2
    rw [div_pow, Real.sq_sqrt hf2.le] at this
    linarith
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  obtain ⟨ms, hms, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc δ 1)).exists_isMaxOn
    ⟨1, by linarith, le_rfl⟩ (f3_contOn hl hδ)
  have hfms : f2 ≤ KThree.f3 lam ms := hmax ⟨hδ1, by norm_num⟩
  have hms0 : 0 < ms := by linarith [hms.1]
  have hms1 : ms < 1 := by
    rcases eq_or_lt_of_le hms.2 with h1 | h1
    · rw [h1, f3_one hl] at hfms; linarith
    · exact h1
  have htop : ∀ m, 0 < m → m ≤ 1 → KThree.f3 lam m ≤ KThree.f3 lam ms := by
    intro m hm hm1
    rcases le_or_gt δ m with hδm | hδm
    · exact hmax ⟨hδm, hm1⟩
    · have := f3_le hl hm hm1
      have : m ^ 2 < δ ^ 2 := by nlinarith
      linarith
  refine ⟨ms, hms0, hms1, fun m hm => htop m hm.1 hm.2.le, exists_sol hl hms0 hms1, ?_⟩
  rintro μ ⟨v, v', h⟩
  rcases le_or_gt μ 0 with hμ | hμ
  · linarith
  obtain ⟨m, hm, hm1, hμm⟩ := mu_formula h hμ hl
  rw [hμm]
  exact htop m hm hm1.le

/-- **K_3 bridge, end to end from the ODE: for every algebraic lam > 0 the largest solvable push of
`v'' = mu (v^(-5/3) + lam v^(-4/3))`, `v(0) = v(1) = 1` exists, is attained, and is transcendental.**
No hypotheses: Hermite-Lindemann is the proved `LindemannBridge.hermite_lindemann`. -/
theorem break_end_to_end {lam : ℝ} (hl : 0 < lam) (hlam : IsAlgebraic ℚ lam) :
    ∃ B : ℝ, IsGreatest {μ : ℝ | ∃ v v' : ℝ → ℝ, Sol lam μ v v'} B ∧ Transcendental ℚ B := by
  obtain ⟨ms, hms0, hms1, hmax, hG⟩ := break_exists hl.le
  exact ⟨_, hG, KThree.top_transcendental LindemannBridge.hermite_lindemann hl hlam hms0 hms1 hmax⟩

end KThreeOde
