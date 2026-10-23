import Mathlib
import Mistranslation.Breaks

/-! # Bratu from the ODE (2026-10-23)

Seat `x'' + mu e^x = 0`, `x(0) = x(1) = 0`. The substitution `u = e^(-x/2)` turns it into the linear spring
`u'' = c^2 u` (`c^2` = energy / 4), so `u = cosh(c(t - 1/2)) / cosh(c/2)` exactly and
`mu = 8 s^2 / cosh^2 s` with `s = c/2`; the largest is `8 / sinh^2 s*`, `s* tanh s* = 1` (3.5138307).
Same shape of proof as k = 3 (a straightening substitution), no inverse function needed. -/

namespace BratuOde

def Sol (μ : ℝ) (x x' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt x (x' t) t ∧ HasDerivAt x' (-(μ * Real.exp (x t))) t) ∧
    x 0 = 0 ∧ x 1 = 0

lemma const_on {a b : ℝ} {f : ℝ → ℝ} (h : ∀ t ∈ Set.Icc a b, HasDerivAt f 0 t) :
    ∀ t ∈ Set.Icc a b, f t = f a := by
  apply constant_of_has_deriv_right_zero
  · intro t ht; exact (h t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (h t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt

/-- Energy `x'^2 + 2 mu e^x` is conserved. -/
lemma energy {μ : ℝ} {x x' : ℝ → ℝ} (h : Sol μ x x') :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, x' t * x' t + 2 * μ * Real.exp (x t) = x' 0 * x' 0 + 2 * μ * Real.exp (x 0) := by
  refine const_on (f := fun t => x' t * x' t + 2 * μ * Real.exp (x t)) ?_
  intro s hs
  obtain ⟨hd, hdd⟩ := h.1 s hs
  convert (hdd.mul hdd).add ((hd.exp).const_mul (2 * μ)) using 1
  ring

/-- Straightening: `u = e^(-x/2)` has `u' = -x' u / 2` and `u'' = (E/4) u`, E the energy. -/
lemma straighten {μ : ℝ} {x x' : ℝ → ℝ} (h : Sol μ x x') (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => Real.exp (-(x s) / 2)) (-(x' t) * Real.exp (-(x t) / 2) / 2) t ∧
    HasDerivAt (fun s => -(x' s) * Real.exp (-(x s) / 2) / 2)
      ((x' 0 * x' 0 + 2 * μ * Real.exp (x 0)) / 4 * Real.exp (-(x t) / 2)) t := by
  obtain ⟨hd, hdd⟩ := h.1 t ht
  have hu : HasDerivAt (fun s => Real.exp (-(x s) / 2)) (-(x' t) * Real.exp (-(x t) / 2) / 2) t := by
    convert ((hd.neg).div_const 2).exp using 1
    simp only [Pi.neg_apply]; ring
  refine ⟨hu, ?_⟩
  have := ((hdd.neg).mul hu).div_const 2
  convert this using 1
  rw [← energy h t ht]
  simp only [Pi.neg_apply]
  ring

lemma cosh_shift_hasDerivAt (c t : ℝ) :
    HasDerivAt (fun t => Real.cosh (c * (t - 1 / 2))) (c * Real.sinh (c * (t - 1 / 2))) t := by
  have h := (Real.hasDerivAt_cosh (c * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul c)
  exact h.congr_deriv (by ring)

lemma sinh_shift_hasDerivAt (c t : ℝ) :
    HasDerivAt (fun t => Real.sinh (c * (t - 1 / 2))) (c * Real.cosh (c * (t - 1 / 2))) t := by
  have h := (Real.hasDerivAt_sinh (c * (t - 1 / 2))).comp t (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul c)
  exact h.congr_deriv (by ring)

/-- A linear spring `u'' = c^2 u` with `u(0) = u(1) = 1` is exactly `cosh(c(t - 1/2)) / cosh(c/2)`.
Proof by two constant Wronskians, no ODE uniqueness theorem. -/
lemma spring_solve {u u' : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (u' t) t ∧ HasDerivAt u' (c ^ 2 * u t) t)
    (h0 : u 0 = 1) (h1 : u 1 = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, u t = Real.cosh (c * (t - 1 / 2)) / Real.cosh (c / 2) ∧
      u' t = c * Real.sinh (c * (t - 1 / 2)) / Real.cosh (c / 2) := by
  have W1 := const_on (a := 0) (b := 1)
    (f := fun t => u t * (c * Real.cosh (c * (t - 1 / 2))) - u' t * Real.sinh (c * (t - 1 / 2))) (by
      intro s hs
      obtain ⟨hu, hu'⟩ := hd s hs
      convert (hu.mul ((cosh_shift_hasDerivAt c s).const_mul c)).sub (hu'.mul (sinh_shift_hasDerivAt c s)) using 1
      ring)
  have W2 := const_on (a := 0) (b := 1)
    (f := fun t => u t * (c * Real.sinh (c * (t - 1 / 2))) - u' t * Real.cosh (c * (t - 1 / 2))) (by
      intro s hs
      obtain ⟨hu, hu'⟩ := hd s hs
      convert (hu.mul ((sinh_shift_hasDerivAt c s).const_mul c)).sub (hu'.mul (cosh_shift_hasDerivAt c s)) using 1
      ring)
  have mem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have mem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set A := u 0 * (c * Real.cosh (c * (0 - 1 / 2))) - u' 0 * Real.sinh (c * (0 - 1 / 2)) with hAdef
  set B := u 0 * (c * Real.sinh (c * (0 - 1 / 2))) - u' 0 * Real.cosh (c * (0 - 1 / 2)) with hBdef
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      c * u t = A * Real.cosh (c * (t - 1 / 2)) - B * Real.sinh (c * (t - 1 / 2)) ∧
      u' t = A * Real.sinh (c * (t - 1 / 2)) - B * Real.cosh (c * (t - 1 / 2)) := by
    intro t ht
    have e1 : u t * (c * Real.cosh (c * (t - 1 / 2))) - u' t * Real.sinh (c * (t - 1 / 2)) = A := W1 t ht
    have e2 : u t * (c * Real.sinh (c * (t - 1 / 2))) - u' t * Real.cosh (c * (t - 1 / 2)) = B := W2 t ht
    have hcs : Real.cosh (c * (t - 1 / 2)) ^ 2 - Real.sinh (c * (t - 1 / 2)) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
    constructor
    · rw [← e1, ← e2]; linear_combination (-(c * u t)) * hcs
    · rw [← e1, ← e2]; linear_combination (-(u' t)) * hcs
  have hC : 0 < Real.cosh (c / 2) := Real.cosh_pos _
  have hS : 0 < Real.sinh (c / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have k0 := (key 0 mem0).1
  have k1 := (key 1 mem1).1
  rw [h0, show c * (0 - 1 / 2) = -(c / 2) by ring, Real.cosh_neg, Real.sinh_neg] at k0
  rw [h1, show c * (1 - 1 / 2) = c / 2 by ring] at k1
  have hB : B = 0 := by
    have hBS : B * Real.sinh (c / 2) = 0 := by linarith
    rcases mul_eq_zero.mp hBS with hb | hs
    · exact hb
    · linarith
  have hA : A = c / Real.cosh (c / 2) := by
    rw [hB] at k1; field_simp; linarith
  intro t ht
  obtain ⟨kt, kt'⟩ := key t ht
  rw [hA, hB] at kt kt'
  constructor
  · apply mul_left_cancel₀ hc.ne'; rw [kt]; ring
  · rw [kt']; ring

/-- **Every Bratu solution sits on `mu = 8 s^2 / cosh^2 s`** for some `s > 0` (derived from the ODE). -/
theorem bratu_mu_formula {μ : ℝ} {x x' : ℝ → ℝ} (h : Sol μ x x') (hμ : 0 < μ) :
    ∃ s : ℝ, 0 < s ∧ μ = 8 * s ^ 2 / Real.cosh s ^ 2 := by
  set E := x' 0 * x' 0 + 2 * μ * Real.exp (x 0) with hE
  have hEpos : 0 < E := by have := Real.exp_pos (x 0); nlinarith [mul_self_nonneg (x' 0)]
  set c := Real.sqrt E / 2 with hc
  have hcpos : 0 < c := by have := Real.sqrt_pos.mpr hEpos; positivity
  have hc2 : c ^ 2 = E / 4 := by rw [hc, div_pow, Real.sq_sqrt hEpos.le]; ring
  have hmid : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have sol := spring_solve (u := fun s => Real.exp (-(x s) / 2)) (u' := fun s => -(x' s) * Real.exp (-(x s) / 2) / 2)
    hcpos (fun t ht => by
      obtain ⟨h1, h2⟩ := straighten h t ht
      exact ⟨h1, by rw [hc2]; exact h2⟩)
    (by simp [h.2.1]) (by simp [h.2.2]) (1 / 2) hmid
  simp only [sub_self, mul_zero, Real.cosh_zero, Real.sinh_zero, zero_div] at sol
  obtain ⟨hu, hu'⟩ := sol
  have hupos := Real.exp_pos (-(x (1 / 2)) / 2)
  have hx'0 : x' (1 / 2) = 0 := by
    have : x' (1 / 2) * Real.exp (-(x (1 / 2)) / 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · linarith
  have hC := Real.cosh_pos (c / 2)
  have hexp : Real.exp (x (1 / 2)) = Real.cosh (c / 2) ^ 2 := by
    have e : Real.exp (x (1 / 2)) * Real.exp (-(x (1 / 2)) / 2) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; simp; ring
    rw [hu] at e; field_simp at e; linarith
  have hEmid := energy h (1 / 2) hmid
  rw [hx'0, hexp] at hEmid
  refine ⟨c / 2, by positivity, ?_⟩
  field_simp
  nlinarith [hEmid, hc2]

/-! Step 4: the maximum of `s / cosh s` sits at `s tanh s = 1`. -/

noncomputable def g (s : ℝ) : ℝ := s / Real.cosh s
noncomputable def hb (s : ℝ) : ℝ := Real.cosh s - s * Real.sinh s

lemma g_hasDerivAt (s : ℝ) : HasDerivAt g (hb s / Real.cosh s ^ 2) s := by
  have := (hasDerivAt_id' s).div (Real.hasDerivAt_cosh s) (Real.cosh_pos s).ne'
  exact this.congr_deriv (by simp only [hb]; ring)

lemma hb_hasDerivAt (s : ℝ) : HasDerivAt hb (-(s * Real.cosh s)) s := by
  have := (Real.hasDerivAt_cosh s).sub ((hasDerivAt_id' s).mul (Real.hasDerivAt_sinh s))
  exact this.congr_deriv (by ring)

lemma hb_strictAnti : StrictAntiOn hb (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact fun x _ => (hb_hasDerivAt x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hb_hasDerivAt x).deriv]
    have := mul_pos (Set.mem_Ioi.mp hx) (Real.cosh_pos x)
    linarith

lemma g_le_max {ss : ℝ} (hss : 0 < ss) (hz : hb ss = 0) : ∀ s, 0 ≤ s → g s ≤ g ss := by
  intro s hs
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (g_hasDerivAt x).continuousAt
  have hgd : Differentiable ℝ g := fun x => (g_hasDerivAt x).differentiableAt
  rcases le_total s ss with hle | hge
  · have hmono : MonotoneOn g (Set.Icc 0 ss) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 ss) hgc.continuousOn hgd.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      rw [(g_hasDerivAt x).deriv]
      have : 0 < hb x := by
        have := hb_strictAnti (Set.mem_Ici.mpr hx.1.le) (Set.mem_Ici.mpr hss.le) hx.2; linarith
      have := Real.cosh_pos x
      positivity
    exact hmono ⟨hs, hle⟩ ⟨hss.le, le_rfl⟩ hle
  · have hanti : AntitoneOn g (Set.Ici ss) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici ss) hgc.continuousOn hgd.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [(g_hasDerivAt x).deriv]
      have : hb x < 0 := by
        have := hb_strictAnti (Set.mem_Ici.mpr hss.le) (Set.mem_Ici.mpr (hss.le.trans hx.le)) hx; linarith
      exact div_nonpos_of_nonpos_of_nonneg this.le (by positivity)
    exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hge) hge

/-- Every solvable push is at most `8 / sinh^2 ss`, where `ss sinh ss = cosh ss`. -/
theorem bratu_break_le {μ : ℝ} {x x' : ℝ → ℝ} (h : Sol μ x x') {ss : ℝ} (hss : 0 < ss)
    (hcrit : ss * Real.sinh ss = Real.cosh ss) : μ ≤ 8 / Real.sinh ss ^ 2 := by
  have hS := Real.sinh_pos_iff.mpr hss
  rcases le_or_gt μ 0 with hμ | hμ
  · have : 0 < 8 / Real.sinh ss ^ 2 := by positivity
    linarith
  obtain ⟨s, hs, hμs⟩ := bratu_mu_formula h hμ
  have hz : hb ss = 0 := by simp only [hb]; linarith
  have hle := g_le_max hss hz s hs.le
  have hg0 : 0 ≤ g s := by unfold g; have := Real.cosh_pos s; positivity
  have hgss : g ss = 1 / Real.sinh ss := by
    unfold g; field_simp; linarith
  have : μ = 8 * g s ^ 2 := by rw [hμs]; unfold g; ring
  rw [this]
  have := pow_le_pow_left₀ hg0 hle 2
  rw [hgss] at this
  calc 8 * g s ^ 2 ≤ 8 * (1 / Real.sinh ss) ^ 2 := by linarith
    _ = 8 / Real.sinh ss ^ 2 := by ring

/-! Step 5: existence, explicitly (no inverse function: the straightened spring is solved in closed form). -/

theorem bratu_exists {c : ℝ} (hc : 0 < c) :
    Sol (2 * c ^ 2 / Real.cosh (c / 2) ^ 2)
      (fun t => 2 * Real.log (Real.cosh (c / 2)) - 2 * Real.log (Real.cosh (c * (t - 1 / 2))))
      (fun t => -(2 * c * Real.sinh (c * (t - 1 / 2)) / Real.cosh (c * (t - 1 / 2)))) := by
  refine ⟨fun t _ => ⟨?_, ?_⟩, ?_, ?_⟩
  · have hw := (Real.cosh_pos (c * (t - 1 / 2))).ne'
    have := ((cosh_shift_hasDerivAt c t).log hw).const_mul 2 |>.const_sub (2 * Real.log (Real.cosh (c / 2)))
    exact this.congr_deriv (by ring)
  · have hw := (Real.cosh_pos (c * (t - 1 / 2))).ne'
    have := (((sinh_shift_hasDerivAt c t).const_mul (2 * c)).div (cosh_shift_hasDerivAt c t) hw).neg
    refine this.congr_deriv ?_
    have hC := (Real.cosh_pos (c / 2)).ne'
    have hcs := Real.cosh_sq_sub_sinh_sq (c * (t - 1 / 2))
    rw [Real.exp_sub, show (2 : ℝ) * Real.log (Real.cosh (c / 2)) = Real.log (Real.cosh (c / 2) ^ 2) by
        rw [Real.log_pow]; norm_num,
      show (2 : ℝ) * Real.log (Real.cosh (c * (t - 1 / 2))) = Real.log (Real.cosh (c * (t - 1 / 2)) ^ 2) by
        rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity), Real.exp_log (by positivity)]
    generalize c * (t - 1 / 2) = a at hcs ⊢
    field_simp
    linear_combination (-1 : ℝ) * hcs
  · beta_reduce; rw [show c * (0 - 1 / 2) = -(c / 2) by ring, Real.cosh_neg]; ring
  · beta_reduce; rw [show c * (1 - 1 / 2) = c / 2 by ring]; ring

/-! Step 6: assemble. -/

lemma crit_root : ∃ ss ∈ Set.Ioo (0 : ℝ) 2, hb ss = 0 := by
  have hcont : ContinuousOn hb (Set.Icc 0 2) := fun x _ => (hb_hasDerivAt x).continuousAt.continuousWithinAt
  have h0 : hb 0 = 1 := by simp [hb]
  have h2 : hb 2 < 0 := by
    have he : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have hinv : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-2)
    simp only [hb, Real.sinh_eq, Real.cosh_eq]
    nlinarith [mul_pos hpos hpos]
  obtain ⟨ss, hss, hz⟩ := intermediate_value_Ioo' (by norm_num : (0 : ℝ) ≤ 2) hcont
    (show (0 : ℝ) ∈ Set.Ioo (hb 2) (hb 0) by rw [h0]; exact ⟨h2, one_pos⟩)
  exact ⟨ss, hss, hz⟩

/-- **Bratu, exact, from the ODE**: the largest push with a solution is `8 / sinh^2 ss`, `ss tanh ss = 1`. -/
theorem bratu_break_exact {ss : ℝ} (hss : 0 < ss) (hcrit : ss * Real.sinh ss = Real.cosh ss) :
    IsGreatest {μ | ∃ x x' : ℝ → ℝ, Sol μ x x'} (8 / Real.sinh ss ^ 2) := by
  refine ⟨?_, fun μ ⟨_, _, h⟩ => bratu_break_le h hss hcrit⟩
  have hS := Real.sinh_pos_iff.mpr hss
  have hval : 8 / Real.sinh ss ^ 2 = 2 * (2 * ss) ^ 2 / Real.cosh (2 * ss / 2) ^ 2 := by
    rw [show 2 * ss / 2 = ss by ring, ← hcrit]; field_simp; ring
  rw [Set.mem_setOf_eq, hval]
  exact ⟨_, _, bratu_exists (by linarith)⟩

/-- **End to end**: the Bratu critical push (largest with a solution, from the ODE) exists and is
transcendental, given Hermite-Lindemann. -/
theorem bratu_break_end_to_end (HL : Breaks.HermiteLindemann) :
    ∃ B : ℝ, IsGreatest {μ | ∃ x x' : ℝ → ℝ, Sol μ x x'} B ∧ Transcendental ℚ B := by
  obtain ⟨ss, hss, hz⟩ := crit_root
  have hcrit : ss * Real.sinh ss = Real.cosh ss := by simp only [hb] at hz; linarith
  exact ⟨_, bratu_break_exact hss.1 hcrit, Breaks.bratu_break_transcendental HL ss hss.1 hcrit⟩

end BratuOde
