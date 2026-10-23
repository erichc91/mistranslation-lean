import Mathlib
import Mistranslation.LinearOde
import Mistranslation.SpringFamily
import Mistranslation.TippingRule

/-! # Shifted springs: sign-blind closures of the linear Dirichlet seats (2026-10-23)

Prior art: first Dirichlet mode `pi^2` of `-x''` on [0,1] and Sturm/Wronskian comparison (Sturm 1836);
resonance of forced linear springs (classical). What this file adds: sign-blind, hypothesis-free Lean
closures for the ledger's linear seats whose term signs were unreadable.

Every sign choice reduces to one of two shapes on [0,1] with `x(0) = x(1) = 0` and push `mu > 0`:

* (H) homogeneous `x'' + (a + b mu) x = 0`
* (F) forced      `x'' + (c0 + c1 mu) + (a + b mu) x = 0`

Write `k = a + b mu` (stiffness) and `F = c0 + c1 mu` (load). One tool does all the work: the
Wronskian-type function `W = x' sin(pi t) - x pi cos(pi t)`, which vanishes at both ends and has
`W' = (pi^2 - k) x sin(pi t) - F sin(pi t)`; a one-signed `W'` forces `W' = 0` on (0,1).

**(H) closed.** `wobble_iff`: a nonnegative, not identically zero solution exists iff `k = pi^2`.
`wobble_set_class`: the wobble set is empty or the single point `(pi^2 - a)/b`, transcendental for
algebraic `a, b`.

**(F) pointwise classification of nonnegative solutions** (LinearOde's convention `x >= 0`):

| load `F`  | stiffness `k`          | nonnegative solution?                          |
|-----------|------------------------|------------------------------------------------|
| `F > 0`   | `k < pi^2`             | yes (`cosh` / parabola / `cos` formula)        |
| `F > 0`   | `k >= pi^2`            | no  (W strictly decreasing)                    |
| `F = 0`   | any                    | yes (zero)                                     |
| `F < 0`   | `k <= pi^2`            | no  (W strictly increasing)                    |
| `F < 0`   | `pi^2 < k <= 4 pi^2`   | yes (`cos` formula, `cos(sqrt k / 2) < 0`)     |
| `F < 0`   | `k > 4 pi^2`           | **OPEN -- not proved here** (see below)        |

Bonus: `resonance_no_sol` -- at `k = pi^2` with `F != 0` there is no solution at all, any sign.

**(F) push level.** If the load is positive for every push (`c0 + c1 mu > 0` for all `mu > 0`), the
push set is exactly `{mu > 0 | a + b mu < pi^2}` (`fpushes_eq`), so:
`b > 0, a < pi^2`: break `(pi^2 - a)/b`, transcendental (`forced_break_transcendental`);
`b <= 0, a < pi^2`: no break (`forced_no_break`); `b >= 0, a >= pi^2`: empty (`forced_empty`);
`b < 0, a >= pi^2`: the push set is `(r, oo)` with onset `r = (pi^2 - a)/b` -- unbounded, no break
(`forced_onset`). If the load is `0` for all pushes: no break. If the load is negative for all
pushes and the stiffness stays `<= pi^2`: empty (`forced_neg_empty`).

**Remaining sub-case (not proved):** load `F < 0` with stiffness `k > 4 pi^2`. There the answer is
irregular: for non-resonant `k` the solution is unique and equals the `cos` formula, which is
nonnegative exactly when `cos(sqrt k u) >= cos(sqrt k / 2)` for `|u| <= 1/2` (fails for
`4 pi^2 < k < 9 pi^2`, holds again e.g. at `k = 16 pi^2`). Proving the "no" half needs ODE uniqueness,
which this file does not develop. A push-level classification for loads that change sign
(`c0`, `c1` of opposite signs) follows pointwise from the table but is not packaged here.
-/

namespace ShiftedSpring

noncomputable section

open Real

/-- (H) Homogeneous seat with stiffness `k`: `x'' = -(k x)`, Dirichlet, no sign condition. -/
def HSol (k : ℝ) (x x' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt x (x' t) t ∧ HasDerivAt x' (-(k * x t)) t) ∧ x 0 = 0 ∧ x 1 = 0

/-- (F) Forced seat with load `F` and stiffness `k`: `x'' = -(F + k x)`, Dirichlet, `x >= 0`. -/
def FSol (F k : ℝ) (x x' : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x t ∧ HasDerivAt x (x' t) t ∧ HasDerivAt x' (-(F + k * x t)) t) ∧
    x 0 = 0 ∧ x 1 = 0

theorem hsol_iff_free {k : ℝ} {x x' : ℝ → ℝ} : HSol k x x' ↔ SpringFamily.FreeSol 1 k x x' := by
  simp only [HSol, SpringFamily.FreeSol, mul_one]

/-! ## The one tool: a one-signed derivative with zero ends vanishes -/

theorem deriv_zero_of_nonneg {g g' : ℝ → ℝ} (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (h0 : g 0 = 0) (h1 : g 1 = 0) (hpos : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ g' t) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, g' t = 0 := by
  have hmono : MonotoneOn g (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun t ht => (hg t ht).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Icc] at ht
      exact (hg t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Icc] at ht
      rw [(hg t (Set.Ioo_subset_Icc_self ht)).deriv]; exact hpos t ht
  have hz : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t = 0 := by
    intro t ht
    have a := hmono ⟨le_rfl, zero_le_one⟩ ht ht.1
    have c := hmono ht ⟨zero_le_one, le_rfl⟩ ht.2
    linarith
  intro t ht
  have hev : g =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using hz s (Set.Ioo_subset_Icc_self hs)
  exact (hg t (Set.Ioo_subset_Icc_self ht)).unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev)

theorem deriv_zero_of_nonpos {g g' : ℝ → ℝ} (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (h0 : g 0 = 0) (h1 : g 1 = 0) (hneg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, g' t ≤ 0) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, g' t = 0 := by
  intro t ht
  have := deriv_zero_of_nonneg (g := fun t => -g t) (g' := fun t => -g' t) (fun t ht => (hg t ht).neg)
    (by simp [h0]) (by simp [h1]) (fun t ht => by simpa using hneg t ht) t ht
  linarith

theorem not_strict_pos {g g' : ℝ → ℝ} (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (h0 : g 0 = 0) (h1 : g 1 = 0) (hpos : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < g' t) : False := by
  have hh : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  exact (hpos _ hh).ne' (deriv_zero_of_nonneg hg h0 h1 (fun t ht => (hpos t ht).le) _ hh)

theorem not_strict_neg {g g' : ℝ → ℝ} (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (h0 : g 0 = 0) (h1 : g 1 = 0) (hneg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, g' t < 0) : False := by
  have hh : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  exact (hneg _ hh).ne (deriv_zero_of_nonpos hg h0 h1 (fun t ht => (hneg t ht).le) _ hh)

/-! ## The Wronskian against sin(pi t) -/

def W (x x' : ℝ → ℝ) (t : ℝ) : ℝ := x' t * Real.sin (Real.pi * t) - x t * (Real.pi * Real.cos (Real.pi * t))

theorem W_hasDerivAt {F k t : ℝ} {x x' : ℝ → ℝ} (hd : HasDerivAt x (x' t) t)
    (hdd : HasDerivAt x' (-(F + k * x t)) t) :
    HasDerivAt (W x x') ((Real.pi ^ 2 - k) * x t * Real.sin (Real.pi * t) - F * Real.sin (Real.pi * t)) t := by
  have hs : HasDerivAt (fun t => Real.sin (Real.pi * t)) (Real.cos (Real.pi * t) * Real.pi) t := by
    have h := (Real.hasDerivAt_sin (Real.pi * t)).comp t ((hasDerivAt_id' t).const_mul Real.pi)
    exact h.congr_deriv (by ring)
  have hc : HasDerivAt (fun t => Real.pi * Real.cos (Real.pi * t))
      (Real.pi * (-Real.sin (Real.pi * t) * Real.pi)) t := by
    have h := ((Real.hasDerivAt_cos (Real.pi * t)).comp t ((hasDerivAt_id' t).const_mul Real.pi)).const_mul Real.pi
    exact h.congr_deriv (by ring)
  exact ((hdd.mul hs).sub (hd.mul hc)).congr_deriv (by ring)

theorem W_zero {x x' : ℝ → ℝ} (h : x 0 = 0) : W x x' 0 = 0 := by simp [W, h]

theorem W_one {x x' : ℝ → ℝ} (h : x 1 = 0) : W x x' 1 = 0 := by simp [W, h]

theorem sin_pos_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : 0 < Real.sin (Real.pi * t) :=
  Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, ht.1]) (by nlinarith [Real.pi_pos, ht.2])

/-! ## 1. (H): wobble iff k = pi^2 -/

/-- Above pi^2, every nonnegative Dirichlet solution of `x'' + k x = 0` vanishes on [0,1]. -/
theorem no_wobble_above {k : ℝ} (hk : Real.pi ^ 2 < k) {x x' : ℝ → ℝ} (h : HSol k x x')
    (hx : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x t) : ∀ t ∈ Set.Icc (0 : ℝ) 1, x t = 0 := by
  have hW : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (W x x')
      ((Real.pi ^ 2 - k) * x t * Real.sin (Real.pi * t) - 0 * Real.sin (Real.pi * t)) t :=
    fun t ht => W_hasDerivAt (h.1 t ht).1 ((h.1 t ht).2.congr_deriv (by ring))
  have hz := deriv_zero_of_nonpos hW (W_zero h.2.1) (W_one h.2.2) (by
    intro t ht
    have := mul_nonneg (hx t (Set.Ioo_subset_Icc_self ht)) (sin_pos_Ioo ht).le
    nlinarith)
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0]; exact h.2.1
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · rw [h1]; exact h.2.2
  have e := hz t ⟨h0, h1⟩
  have hs := sin_pos_Ioo (t := t) ⟨h0, h1⟩
  have : x t * ((Real.pi ^ 2 - k) * Real.sin (Real.pi * t)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h'
  · exact h'
  · exact absurd h' (mul_neg_of_neg_of_pos (by linarith) hs).ne

/-- **(H) closed: a nonnegative, not identically zero Dirichlet solution of `x'' + k x = 0`
exists iff `k = pi^2`.** -/
theorem wobble_iff (k : ℝ) :
    (∃ x x' : ℝ → ℝ, HSol k x x' ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x t) ∧
      ∃ t ∈ Set.Icc (0 : ℝ) 1, x t ≠ 0) ↔ k = Real.pi ^ 2 := by
  constructor
  · rintro ⟨x, x', h, hx, t, ht, hne⟩
    rcases lt_trichotomy k (Real.pi ^ 2) with hlt | heq | hgt
    · exact absurd (SpringFamily.no_wobble_below one_pos (by rwa [div_one]) (hsol_iff_free.mp h) hx t ht) hne
    · exact heq
    · exact absurd (no_wobble_above hgt h hx t ht) hne
  · rintro rfl
    have hs := SpringFamily.sin_solves (b := 1) one_ne_zero
    rw [div_one] at hs
    refine ⟨_, _, hsol_iff_free.mpr hs, fun t ht => ?_, 1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    · exact Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le ht.1)
        (by nlinarith [Real.pi_pos, ht.2])
    · show Real.sin (Real.pi * (1 / 2)) ≠ 0
      rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]; norm_num

/-! ## 2. (H): the wobble set in the push -/

/-- Pushes `mu > 0` at which `x'' + (a + b mu) x = 0` has a nonnegative, nonzero Dirichlet solution. -/
def WobSet (a b : ℝ) : Set ℝ :=
  {μ | 0 < μ ∧ ∃ x x' : ℝ → ℝ, HSol (a + b * μ) x x' ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x t) ∧
    ∃ t ∈ Set.Icc (0 : ℝ) 1, x t ≠ 0}

theorem wobset_eq (a b : ℝ) : WobSet a b = {μ | 0 < μ ∧ a + b * μ = Real.pi ^ 2} := by
  ext μ; simp only [WobSet, Set.mem_ofPred_eq, wobble_iff]

/-- `(pi^2 - a) / b` is transcendental for algebraic `a`, `b` with `b != 0`. -/
theorem shifted_transcendental {a b : ℝ} (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) (hb0 : b ≠ 0) :
    Transcendental ℚ ((Real.pi ^ 2 - a) / b) := by
  intro h
  apply SpringFamily.pi_sq_transcendental
  have : Real.pi ^ 2 = a + b * ((Real.pi ^ 2 - a) / b) := by field_simp; ring
  rw [this]; exact ha.add (hb.mul h)

/-- **(H) wobble set: empty, or the single transcendental point `(pi^2 - a)/b`.** -/
theorem wobble_set_class {a b : ℝ} (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) :
    WobSet a b = ∅ ∨
      (b ≠ 0 ∧ 0 < (Real.pi ^ 2 - a) / b ∧ WobSet a b = {(Real.pi ^ 2 - a) / b} ∧
        Transcendental ℚ ((Real.pi ^ 2 - a) / b)) := by
  rw [wobset_eq]
  by_cases hb0 : b = 0
  · left
    ext μ
    simp only [hb0, zero_mul, add_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hapi
    exact SpringFamily.pi_sq_transcendental (hapi ▸ ha)
  by_cases hpos : 0 < (Real.pi ^ 2 - a) / b
  · right
    refine ⟨hb0, hpos, ?_, shifted_transcendental ha hb hb0⟩
    ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, he⟩; rw [eq_div_iff hb0]; linarith
    · rintro rfl; refine ⟨hpos, ?_⟩; field_simp; ring
  · left
    ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hμ he
    apply hpos
    have : μ = (Real.pi ^ 2 - a) / b := by rw [eq_div_iff hb0]; linarith
    rw [← this]; exact hμ

/-! ## 3. (F): pointwise classification -/

/-- No nonnegative solution when the load is positive and the stiffness has reached pi^2. -/
theorem forced_pos_high {F k : ℝ} (hF : 0 < F) (hk : Real.pi ^ 2 ≤ k) {x x' : ℝ → ℝ}
    (h : FSol F k x x') : False := by
  refine not_strict_neg (g := W x x') (fun t ht => W_hasDerivAt (h.1 t ht).2.1 (h.1 t ht).2.2)
    (W_zero h.2.1) (W_one h.2.2) (fun t ht => ?_)
  have hs := sin_pos_Ioo ht
  have := mul_nonneg (h.1 t (Set.Ioo_subset_Icc_self ht)).1 hs.le
  nlinarith [mul_pos hF hs]

/-- No nonnegative solution when the load is negative and the stiffness is at most pi^2. -/
theorem forced_neg_low {F k : ℝ} (hF : F < 0) (hk : k ≤ Real.pi ^ 2) {x x' : ℝ → ℝ}
    (h : FSol F k x x') : False := by
  refine not_strict_pos (g := W x x') (fun t ht => W_hasDerivAt (h.1 t ht).2.1 (h.1 t ht).2.2)
    (W_zero h.2.1) (W_one h.2.2) (fun t ht => ?_)
  have hs := sin_pos_Ioo ht
  have := mul_nonneg (h.1 t (Set.Ioo_subset_Icc_self ht)).1 hs.le
  nlinarith [mul_pos (neg_pos.mpr hF) hs]

/-- Resonance: at `k = pi^2` a nonzero load admits no Dirichlet solution at all (any sign). -/
theorem resonance_no_sol {F : ℝ} (hF : F ≠ 0) {x x' : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt x (x' t) t ∧ HasDerivAt x' (-(F + Real.pi ^ 2 * x t)) t)
    (h0 : x 0 = 0) (h1 : x 1 = 0) : False := by
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (W x x')
      ((Real.pi ^ 2 - Real.pi ^ 2) * x t * Real.sin (Real.pi * t) - F * Real.sin (Real.pi * t)) t :=
    fun t ht => W_hasDerivAt (hd t ht).1 (hd t ht).2
  rcases lt_or_gt_of_ne hF with hn | hp
  · exact not_strict_pos hg (W_zero h0) (W_one h1) fun t ht => by
      have := sin_pos_Ioo ht; nlinarith
  · exact not_strict_neg hg (W_zero h0) (W_one h1) fun t ht => by
      have := sin_pos_Ioo ht; nlinarith

/-- Zero load: the zero solution, any stiffness. -/
theorem forced_zero_sol (k : ℝ) : FSol 0 k (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun t _ => ⟨le_rfl, hasDerivAt_const t 0, ?_⟩, rfl, rfl⟩
  simpa using hasDerivAt_const t (0 : ℝ)

/-- Explicit `cos` solution of `x'' = -(F + k x)`, Dirichlet, valid whenever `cos(sqrt k / 2) != 0`. -/
def cx (F k t : ℝ) : ℝ :=
  F / k * (Real.cos (Real.sqrt k * (t - 1 / 2)) / Real.cos (Real.sqrt k / 2) - 1)

def cx' (F k t : ℝ) : ℝ :=
  F / k * (-(Real.sqrt k * Real.sin (Real.sqrt k * (t - 1 / 2))) / Real.cos (Real.sqrt k / 2))

theorem cx_solves {F k : ℝ} (hk : 0 < k) (hC : Real.cos (Real.sqrt k / 2) ≠ 0) (t : ℝ) :
    HasDerivAt (cx F k) (cx' F k t) t ∧ HasDerivAt (cx' F k) (-(F + k * cx F k t)) t := by
  set s := Real.sqrt k with hsdef
  have hs2 : s ^ 2 = k := Real.sq_sqrt hk.le
  have hk0 : k ≠ 0 := hk.ne'
  constructor
  · have := (Real.hasDerivAt_cos (s * (t - 1 / 2))).comp t (((hasDerivAt_id t).sub_const (1 / 2)).const_mul s)
    refine (((this.div_const (Real.cos (s / 2))).sub_const 1).const_mul (F / k)).congr_deriv ?_
    simp only [cx', ← hsdef, mul_one]
    ring
  · have := (Real.hasDerivAt_sin (s * (t - 1 / 2))).comp t (((hasDerivAt_id t).sub_const (1 / 2)).const_mul s)
    refine ((((this.const_mul s).neg).div_const (Real.cos (s / 2))).const_mul (F / k)).congr_deriv ?_
    simp only [cx, ← hsdef, mul_one]
    have e : s * (Real.cos (s * (t - 1 / 2)) * s) = k * Real.cos (s * (t - 1 / 2)) := by
      rw [← hs2]; ring
    rw [e]
    field_simp
    ring

theorem cx_ends {F k : ℝ} (hC : Real.cos (Real.sqrt k / 2) ≠ 0) : cx F k 0 = 0 ∧ cx F k 1 = 0 := by
  constructor
  · simp only [cx]
    rw [show Real.sqrt k * (0 - 1 / 2) = -(Real.sqrt k / 2) by ring, Real.cos_neg, div_self hC]; ring
  · simp only [cx]
    rw [show Real.sqrt k * (1 - 1 / 2) = Real.sqrt k / 2 by ring, div_self hC]; ring

/-- Negative load, `pi^2 < k <= 4 pi^2`: the `cos` solution is nonnegative. -/
theorem forced_neg_mid_sol {F k : ℝ} (hF : F < 0) (hk1 : Real.pi ^ 2 < k) (hk2 : k ≤ 4 * Real.pi ^ 2) :
    FSol F k (cx F k) (cx' F k) := by
  have hk : 0 < k := lt_of_le_of_lt (sq_nonneg _) hk1
  set s := Real.sqrt k with hsdef
  have hs1 : Real.pi < s := (Real.lt_sqrt Real.pi_pos.le).mpr hk1
  have hs2 : s ≤ 2 * Real.pi := by
    have := Real.sqrt_le_sqrt hk2
    rwa [show 4 * Real.pi ^ 2 = (2 * Real.pi) ^ 2 by ring, Real.sqrt_sq (by positivity)] at this
  have hCneg : Real.cos (s / 2) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos])
  have hC : Real.cos (s / 2) ≠ 0 := hCneg.ne
  refine ⟨fun t ht => ⟨?_, (cx_solves hk hC t).1, (cx_solves hk hC t).2⟩, (cx_ends hC).1, (cx_ends hC).2⟩
  have hle : Real.cos (s / 2) ≤ Real.cos (s * (t - 1 / 2)) := by
    rw [← Real.cos_abs (s * (t - 1 / 2))]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
    rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2, Real.pi_pos]
  have hbr : Real.cos (s * (t - 1 / 2)) / Real.cos (s / 2) - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one_of_neg hCneg]; exact hle
  exact mul_nonneg_of_nonpos_of_nonpos (div_nonpos_of_nonpos_of_nonneg hF.le hk.le) hbr

/-- Nonnegative load, stiffness below pi^2: a nonnegative solution exists (cosh / parabola / cos). -/
theorem forced_nonneg_low_sol {F k : ℝ} (hF : 0 ≤ F) (hk : k < Real.pi ^ 2) :
    ∃ x x' : ℝ → ℝ, FSol F k x x' := by
  rcases lt_trichotomy k 0 with hneg | rfl | hposk
  · -- k < 0: cosh solution of x'' = (-k) x + (-F)
    have hA : 0 < -k := neg_pos.mpr hneg
    obtain ⟨hd, h0, h1⟩ := TippingRule.exp_spring_linear_sol hA (-F)
    have hnn := TippingRule.exp_spring_nonneg hA (B := -F) (by linarith)
    exact ⟨_, _, fun t ht => ⟨hnn t ht, (hd t).1, (hd t).2.congr_deriv (by ring)⟩, h0, h1⟩
  · -- k = 0: parabola
    obtain ⟨hd, h0, h1⟩ := TippingRule.steady_sol F 1
    have hnn := TippingRule.steady_nonneg (c := F) (μ := 1) (by linarith)
    exact ⟨_, _, fun t ht => ⟨hnn t ht, (hd t ht).1, (hd t ht).2.congr_deriv (by ring)⟩, h0, h1⟩
  · -- 0 < k < pi^2: scale LinearOde.exists_below (y'' = -(k (1 + y))) by F / k
    obtain ⟨hd, h0, h1⟩ := LinearOde.exists_below hposk hk
    refine ⟨cx F k, cx' F k, fun t ht => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact mul_nonneg (div_nonneg hF hposk.le) (hd t ht).1
    · exact (hd t ht).2.1.const_mul (F / k)
    · refine ((hd t ht).2.2.const_mul (F / k)).congr_deriv ?_
      simp only [cx]; field_simp
    · show F / k * _ = 0; beta_reduce at h0; rw [h0, mul_zero]
    · show F / k * _ = 0; beta_reduce at h1; rw [h1, mul_zero]

/-- **(F), positive load: a nonnegative solution exists iff the stiffness is below pi^2.** -/
theorem forced_pos_iff {F k : ℝ} (hF : 0 < F) : (∃ x x' : ℝ → ℝ, FSol F k x x') ↔ k < Real.pi ^ 2 := by
  constructor
  · rintro ⟨x, x', h⟩
    by_contra hk; push Not at hk
    exact forced_pos_high hF hk h
  · exact forced_nonneg_low_sol hF.le

/-- **(F), negative load: none for `k <= pi^2`, one for `pi^2 < k <= 4 pi^2`** (`k > 4 pi^2` open). -/
theorem forced_neg_class {F k : ℝ} (hF : F < 0) :
    (k ≤ Real.pi ^ 2 → ¬ ∃ x x' : ℝ → ℝ, FSol F k x x') ∧
      (Real.pi ^ 2 < k → k ≤ 4 * Real.pi ^ 2 → ∃ x x' : ℝ → ℝ, FSol F k x x') :=
  ⟨fun hk ⟨_, _, h⟩ => forced_neg_low hF hk h, fun hk1 hk2 => ⟨_, _, forced_neg_mid_sol hF hk1 hk2⟩⟩

/-! ## 4. (F): push level -/

/-- Pushes `mu > 0` at which `x'' + (c0 + c1 mu) + (a + b mu) x = 0` has a nonnegative Dirichlet solution. -/
def FPushes (a b c0 c1 : ℝ) : Set ℝ :=
  {μ | 0 < μ ∧ ∃ x x' : ℝ → ℝ, FSol (c0 + c1 * μ) (a + b * μ) x x'}

/-- **Positive load for every push: solvable exactly where the stiffness is below pi^2.** -/
theorem fpushes_eq {a b c0 c1 : ℝ} (hF : ∀ μ : ℝ, 0 < μ → 0 < c0 + c1 * μ) :
    FPushes a b c0 c1 = {μ | 0 < μ ∧ a + b * μ < Real.pi ^ 2} := by
  ext μ
  simp only [FPushes, Set.mem_ofPred_eq]
  exact ⟨fun ⟨hμ, hs⟩ => ⟨hμ, (forced_pos_iff (hF μ hμ)).mp hs⟩,
    fun ⟨hμ, hk⟩ => ⟨hμ, (forced_pos_iff (hF μ hμ)).mpr hk⟩⟩

/-- Positive load, stiffness rising through pi^2 (`b > 0`, `a < pi^2`): break `(pi^2 - a)/b`. -/
theorem forced_break {a b c0 c1 : ℝ} (hF : ∀ μ : ℝ, 0 < μ → 0 < c0 + c1 * μ) (hb : 0 < b)
    (ha : a < Real.pi ^ 2) :
    FPushes a b c0 c1 = Set.Ioo 0 ((Real.pi ^ 2 - a) / b) ∧
      IsLUB (FPushes a b c0 c1) ((Real.pi ^ 2 - a) / b) := by
  have hset : FPushes a b c0 c1 = Set.Ioo 0 ((Real.pi ^ 2 - a) / b) := by
    rw [fpushes_eq hF]; ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_Ioo, lt_div_iff₀ hb]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  refine ⟨hset, ?_⟩
  rw [hset]
  exact isLUB_Ioo (div_pos (by linarith) hb)

/-- **Closed: positive load, rising stiffness, algebraic `a, b` -- the break is transcendental.** -/
theorem forced_break_transcendental {a b c0 c1 : ℝ} (hF : ∀ μ : ℝ, 0 < μ → 0 < c0 + c1 * μ)
    (hb : 0 < b) (ha : a < Real.pi ^ 2) (haA : IsAlgebraic ℚ a) (hbA : IsAlgebraic ℚ b) :
    IsLUB (FPushes a b c0 c1) ((Real.pi ^ 2 - a) / b) ∧ Transcendental ℚ ((Real.pi ^ 2 - a) / b) :=
  ⟨(forced_break hF hb ha).2, shifted_transcendental haA hbA hb.ne'⟩

/-- Positive load, stiffness never reaching pi^2 (`b <= 0`, `a < pi^2`): every push solvable, no break. -/
theorem forced_no_break {a b c0 c1 : ℝ} (hF : ∀ μ : ℝ, 0 < μ → 0 < c0 + c1 * μ) (hb : b ≤ 0)
    (ha : a < Real.pi ^ 2) :
    FPushes a b c0 c1 = Set.Ioi 0 ∧ ¬ BddAbove (FPushes a b c0 c1) := by
  have hset : FPushes a b c0 c1 = Set.Ioi 0 := by
    rw [fpushes_eq hF]; ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi, and_iff_left_iff_imp]
    intro hμ; nlinarith
  exact ⟨hset, by rw [hset]; exact not_bddAbove_Ioi 0⟩

/-- Positive load, stiffness starting at or above pi^2 and not falling (`b >= 0`, `a >= pi^2`): empty. -/
theorem forced_empty {a b c0 c1 : ℝ} (hF : ∀ μ : ℝ, 0 < μ → 0 < c0 + c1 * μ) (hb : 0 ≤ b)
    (ha : Real.pi ^ 2 ≤ a) : FPushes a b c0 c1 = ∅ := by
  rw [fpushes_eq hF]; ext μ
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  intro hμ; nlinarith

/-- Positive load, stiffness falling from at/above pi^2 (`b < 0`, `a >= pi^2`): the push set is
`(r, oo)` with onset `r = (pi^2 - a)/b >= 0` -- unbounded, no break. -/
theorem forced_onset {a b c0 c1 : ℝ} (hF : ∀ μ : ℝ, 0 < μ → 0 < c0 + c1 * μ) (hb : b < 0)
    (ha : Real.pi ^ 2 ≤ a) :
    FPushes a b c0 c1 = Set.Ioi ((Real.pi ^ 2 - a) / b) ∧ ¬ BddAbove (FPushes a b c0 c1) := by
  have hr : 0 ≤ (Real.pi ^ 2 - a) / b := div_nonneg_of_nonpos (by linarith) hb.le
  have hset : FPushes a b c0 c1 = Set.Ioi ((Real.pi ^ 2 - a) / b) := by
    rw [fpushes_eq hF]; ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi, div_lt_iff_of_neg hb]
    constructor
    · rintro ⟨_, h⟩; linarith
    · intro h
      refine ⟨?_, by linarith⟩
      by_contra hμ; push Not at hμ
      nlinarith
  exact ⟨hset, by rw [hset]; exact not_bddAbove_Ioi _⟩

/-- Zero load for every push: every push solvable (zero solution), no break. -/
theorem forced_zero_no_break (a b : ℝ) :
    FPushes a b 0 0 = Set.Ioi 0 ∧ ¬ BddAbove (FPushes a b 0 0) := by
  have hset : FPushes a b 0 0 = Set.Ioi 0 := by
    ext μ
    simp only [FPushes, Set.mem_ofPred_eq, Set.mem_Ioi, zero_mul, add_zero, and_iff_left_iff_imp]
    exact fun _ => ⟨_, _, forced_zero_sol _⟩
  exact ⟨hset, by rw [hset]; exact not_bddAbove_Ioi 0⟩

/-- Negative load for every push, stiffness never above pi^2: no push is solvable. -/
theorem forced_neg_empty {a b c0 c1 : ℝ} (hF : ∀ μ : ℝ, 0 < μ → c0 + c1 * μ < 0)
    (hk : ∀ μ : ℝ, 0 < μ → a + b * μ ≤ Real.pi ^ 2) : FPushes a b c0 c1 = ∅ := by
  ext μ
  simp only [FPushes, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro hμ ⟨x, x', h⟩
  exact forced_neg_low (hF μ hμ) (hk μ hμ) h

end

end ShiftedSpring

#print axioms ShiftedSpring.deriv_zero_of_nonneg
#print axioms ShiftedSpring.deriv_zero_of_nonpos
#print axioms ShiftedSpring.W_hasDerivAt
#print axioms ShiftedSpring.no_wobble_above
#print axioms ShiftedSpring.wobble_iff
#print axioms ShiftedSpring.wobset_eq
#print axioms ShiftedSpring.shifted_transcendental
#print axioms ShiftedSpring.wobble_set_class
#print axioms ShiftedSpring.forced_pos_high
#print axioms ShiftedSpring.forced_neg_low
#print axioms ShiftedSpring.resonance_no_sol
#print axioms ShiftedSpring.forced_zero_sol
#print axioms ShiftedSpring.cx_solves
#print axioms ShiftedSpring.forced_neg_mid_sol
#print axioms ShiftedSpring.forced_nonneg_low_sol
#print axioms ShiftedSpring.forced_pos_iff
#print axioms ShiftedSpring.forced_neg_class
#print axioms ShiftedSpring.fpushes_eq
#print axioms ShiftedSpring.forced_break
#print axioms ShiftedSpring.forced_break_transcendental
#print axioms ShiftedSpring.forced_no_break
#print axioms ShiftedSpring.forced_empty
#print axioms ShiftedSpring.forced_onset
#print axioms ShiftedSpring.forced_zero_no_break
#print axioms ShiftedSpring.forced_neg_empty
