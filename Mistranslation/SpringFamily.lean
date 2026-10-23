import Mathlib
import Mistranslation.LinearOde
import Mistranslation.TrigClass
import Mistranslation.LindemannBridge

/-! # The spring family: breaks and first wobbles at pi^2 / b (2026-10-23)

Prior art: the first Dirichlet eigenvalue of `-x''` on [0,1] is pi^2 (Sturm-Liouville, 1836); pi is transcendental
(Lindemann, 1882; here via the vendored Lindemann-Weierstrass through `LindemannBridge.lindemann_sin`).
What this file adds: machine-checked, hypothesis-free closures for the ledger's pi^2/b spring seats.

1. Forced spring with stiffness knob `b > 0`: `x'' + mu (1 + b x) = 0`, Dirichlet, `x >= 0`. Break = pi^2 / b,
   obtained by scaling `LinearOde.linear_break_exact` (y = b x solves the b = 1 seat at push b mu).
2. Free spring `x'' + mu b x = 0`, Dirichlet: `sin (pi t)` solves at mu = pi^2 / b, and below that there is no
   nonnegative solution that is not identically zero on [0,1] (W-function trick). So pi^2 / b is the first wobble.
3. Restoring spring = the b = 1 case: first wobble pi^2.
All values pi^2 / b with b algebraic, b != 0, are transcendental -- unconditionally. -/

namespace SpringFamily

/-! ## 1. Forced spring with stiffness b -/

/-- Forced spring with stiffness knob `b`: `x'' = -(mu (1 + b x))`, `x(0) = x(1) = 0`, `x >= 0`. -/
def Sol' (b μ : ℝ) (x x' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x t ∧ HasDerivAt x (x' t) t ∧ HasDerivAt x' (-(μ * (1 + b * x t))) t) ∧
    x 0 = 0 ∧ x 1 = 0

/-- Scaling down: a stiffness-b solution at push mu gives a b = 1 solution at push b mu. -/
theorem scale_to_linear {b μ : ℝ} (hb : 0 < b) {x x' : ℝ → ℝ} (h : Sol' b μ x x') :
    LinearOde.Sol (b * μ) (fun t => b * x t) (fun t => b * x' t) := by
  refine ⟨fun t ht => ?_, by simp [h.2.1], by simp [h.2.2]⟩
  obtain ⟨hx, hd, hdd⟩ := h.1 t ht
  refine ⟨mul_nonneg hb.le hx, hd.const_mul b, (hdd.const_mul b).congr_deriv (by ring)⟩

/-- Scaling up: a b = 1 solution at push nu gives a stiffness-b solution at push nu / b. -/
theorem scale_from_linear {b ν : ℝ} (hb : 0 < b) {y y' : ℝ → ℝ} (h : LinearOde.Sol ν y y') :
    Sol' b (ν / b) (fun t => y t / b) (fun t => y' t / b) := by
  refine ⟨fun t ht => ?_, by simp [h.2.1], by simp [h.2.2]⟩
  obtain ⟨hy, hd, hdd⟩ := h.1 t ht
  refine ⟨div_nonneg hy hb.le, hd.div_const b, (hdd.div_const b).congr_deriv ?_⟩
  field_simp

/-- **Forced spring, stiffness b > 0: the break is pi^2 / b.** -/
theorem forced_break_exact {b : ℝ} (hb : 0 < b) :
    IsLUB {μ : ℝ | 0 < μ ∧ ∃ x x' : ℝ → ℝ, Sol' b μ x x'} (Real.pi ^ 2 / b) := by
  constructor
  · rintro μ ⟨hμ, x, x', h⟩
    have := LinearOde.lt_pi_sq (scale_to_linear hb h) (mul_pos hb hμ)
    rw [le_div_iff₀ hb]; linarith
  · intro c hc
    rw [div_le_iff₀ hb]
    -- b c bounds the b = 1 set, so pi^2 <= b c by leastness there
    apply LinearOde.linear_break_exact.2
    rintro ν ⟨hν, y, y', h⟩
    have := hc ⟨div_pos hν hb, _, _, scale_from_linear hb h⟩
    rw [div_le_iff₀ hb] at this; linarith

/-! ## Transcendence, unconditional -/

theorem pi_transcendental : Transcendental ℚ Real.pi :=
  TrigClass.pi_transcendental LindemannBridge.lindemann_sin

theorem pi_sq_transcendental : Transcendental ℚ (Real.pi ^ 2) :=
  fun h => pi_transcendental (IsAlgebraic.of_pow (by norm_num) h)

/-- **pi^2 / b is transcendental for every algebraic b != 0.** -/
theorem pi_sq_div_transcendental {b : ℝ} (hbA : IsAlgebraic ℚ b) (hb0 : b ≠ 0) :
    Transcendental ℚ (Real.pi ^ 2 / b) := by
  intro h
  apply pi_sq_transcendental
  have : Real.pi ^ 2 = b * (Real.pi ^ 2 / b) := by field_simp
  rw [this]; exact hbA.mul h

/-- **Forced spring seat, closed: break pi^2 / b exists and is transcendental (b > 0 algebraic).** -/
theorem forced_break_transcendental {b : ℝ} (hb : 0 < b) (hbA : IsAlgebraic ℚ b) :
    IsLUB {μ : ℝ | 0 < μ ∧ ∃ x x' : ℝ → ℝ, Sol' b μ x x'} (Real.pi ^ 2 / b) ∧
      Transcendental ℚ (Real.pi ^ 2 / b) :=
  ⟨forced_break_exact hb, pi_sq_div_transcendental hbA hb.ne'⟩

/-! ## 2. Free spring: first wobble pi^2 / b -/

/-- Free spring `x'' + mu b x = 0` with Dirichlet ends (no sign condition). -/
def FreeSol (b μ : ℝ) (x x' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt x (x' t) t ∧ HasDerivAt x' (-(μ * b * x t)) t) ∧ x 0 = 0 ∧ x 1 = 0

/-- (a) `sin (pi t)` wobbles at mu = pi^2 / b. -/
theorem sin_solves {b : ℝ} (hb : b ≠ 0) :
    FreeSol b (Real.pi ^ 2 / b) (fun t => Real.sin (Real.pi * t)) (fun t => Real.pi * Real.cos (Real.pi * t)) := by
  refine ⟨fun t _ => ⟨?_, ?_⟩, by simp, by simp⟩
  · have h := (Real.hasDerivAt_sin (Real.pi * t)).comp t ((hasDerivAt_id' t).const_mul Real.pi)
    exact h.congr_deriv (by ring)
  · have h := ((Real.hasDerivAt_cos (Real.pi * t)).comp t ((hasDerivAt_id' t).const_mul Real.pi)).const_mul Real.pi
    refine h.congr_deriv ?_
    field_simp

/-- (b) Below pi^2 / b, every nonnegative Dirichlet solution vanishes on [0,1].
(Holds for all mu with mu b < pi^2, in particular 0 < mu < pi^2 / b.) -/
theorem no_wobble_below {b μ : ℝ} (hb : 0 < b) (hμ : μ < Real.pi ^ 2 / b) {x x' : ℝ → ℝ}
    (h : FreeSol b μ x x') (hx : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x t) : ∀ t ∈ Set.Icc (0 : ℝ) 1, x t = 0 := by
  have hk : 0 < Real.pi ^ 2 - μ * b := by rw [lt_div_iff₀ hb] at hμ; linarith
  set W : ℝ → ℝ := fun t => x' t * Real.sin (Real.pi * t) - x t * (Real.pi * Real.cos (Real.pi * t))
  have hW : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt W ((Real.pi ^ 2 - μ * b) * x t * Real.sin (Real.pi * t)) t := by
    intro t ht
    obtain ⟨hd, hdd⟩ := h.1 t ht
    have hs : HasDerivAt (fun t => Real.sin (Real.pi * t)) (Real.cos (Real.pi * t) * Real.pi) t := by
      have h := (Real.hasDerivAt_sin (Real.pi * t)).comp t ((hasDerivAt_id' t).const_mul Real.pi)
      exact h.congr_deriv (by ring)
    have hc : HasDerivAt (fun t => Real.pi * Real.cos (Real.pi * t))
        (Real.pi * (-Real.sin (Real.pi * t) * Real.pi)) t := by
      have h := ((Real.hasDerivAt_cos (Real.pi * t)).comp t ((hasDerivAt_id' t).const_mul Real.pi)).const_mul Real.pi
      exact h.congr_deriv (by ring)
    exact ((hdd.mul hs).sub (hd.mul hc)).congr_deriv (by ring)
  have hsin : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < Real.sin (Real.pi * t) := fun t ht =>
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, ht.1]) (by nlinarith [Real.pi_pos, ht.2])
  have hmono : MonotoneOn W (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun t ht => (hW t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hW t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hW t (Set.Ioo_subset_Icc_self ht)).deriv]
      exact mul_nonneg (mul_nonneg hk.le (hx t (Set.Ioo_subset_Icc_self ht))) (hsin t ht).le
  have hW0 : W 0 = 0 := by simp [W, h.2.1]
  have hW1 : W 1 = 0 := by simp [W, h.2.2]
  have hWz : ∀ t ∈ Set.Icc (0 : ℝ) 1, W t = 0 := by
    intro t ht
    have a := hmono ⟨le_rfl, zero_le_one⟩ ht ht.1
    have c := hmono ht ⟨zero_le_one, le_rfl⟩ ht.2
    linarith
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0]; exact h.2.1
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · rw [h1]; exact h.2.2
  have htI : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have hev : W =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with s hs using hWz s (Set.Ioo_subset_Icc_self hs)
  have hder := (hW t ht).unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev)
  have hs := hsin t htI
  have : x t * ((Real.pi ^ 2 - μ * b) * Real.sin (Real.pi * t)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h'
  · exact h'
  · exact absurd h' (mul_pos hk hs).ne'

/-- Pushes at which the free spring has a nonnegative, not identically zero, Dirichlet solution. -/
def Wobbles (b : ℝ) : Set ℝ :=
  {μ | 0 < μ ∧ ∃ x x' : ℝ → ℝ, FreeSol b μ x x' ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x t) ∧
    ∃ t ∈ Set.Icc (0 : ℝ) 1, x t ≠ 0}

/-- **Free spring, stiffness b > 0: the first wobble is pi^2 / b.** -/
theorem free_first_wobble {b : ℝ} (hb : 0 < b) : IsLeast (Wobbles b) (Real.pi ^ 2 / b) := by
  constructor
  · refine ⟨div_pos (pow_pos Real.pi_pos 2) hb, _, _, sin_solves hb.ne', fun t ht => ?_, 1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    · exact Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le ht.1)
        (by nlinarith [Real.pi_pos, ht.2])
    · show Real.sin (Real.pi * (1 / 2)) ≠ 0
      rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]; norm_num
  · rintro μ ⟨_, x, x', h, hx, t, ht, hne⟩
    by_contra hlt
    push Not at hlt
    exact hne (no_wobble_below hb hlt h hx t ht)

/-- **Free spring seat, closed: first wobble pi^2 / b, transcendental for algebraic b > 0.** -/
theorem free_first_wobble_transcendental {b : ℝ} (hb : 0 < b) (hbA : IsAlgebraic ℚ b) :
    IsLeast (Wobbles b) (Real.pi ^ 2 / b) ∧ Transcendental ℚ (Real.pi ^ 2 / b) :=
  ⟨free_first_wobble hb, pi_sq_div_transcendental hbA hb.ne'⟩

/-! ## 3. Restoring spring: b = 1, first wobble pi^2 -/

/-- **Restoring spring `x'' + mu x = 0`: first wobble pi^2, transcendental.** -/
theorem restoring_first_wobble : IsLeast (Wobbles 1) (Real.pi ^ 2) ∧ Transcendental ℚ (Real.pi ^ 2) := by
  have := free_first_wobble (b := 1) one_pos
  rw [div_one] at this
  exact ⟨this, pi_sq_transcendental⟩

end SpringFamily

#print axioms SpringFamily.scale_to_linear
#print axioms SpringFamily.scale_from_linear
#print axioms SpringFamily.forced_break_exact
#print axioms SpringFamily.pi_transcendental
#print axioms SpringFamily.pi_sq_transcendental
#print axioms SpringFamily.pi_sq_div_transcendental
#print axioms SpringFamily.forced_break_transcendental
#print axioms SpringFamily.sin_solves
#print axioms SpringFamily.no_wobble_below
#print axioms SpringFamily.free_first_wobble
#print axioms SpringFamily.free_first_wobble_transcendental
#print axioms SpringFamily.restoring_first_wobble
