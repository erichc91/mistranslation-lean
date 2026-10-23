import Mathlib
import Mistranslation.TimeMap
import Mistranslation.LindemannBridge

/-! # The pinch: a closed member inside the open ring family (2026-10-23)

Seat `x'' + mu f(x) = 0`, `x(0) = x(1) = 0`, `f = 1 + x + lam x^2`, `F = x + x^2/2 + lam x^3/3`, factor
`P(A, y) = (F(A) - F(y)) / (A - y)`; time map `T(A)` from `Mistranslation/TimeMap.lean` (`push_eq_time_map`: every
solution has `mu = 4 T(A)^2`). A *pinch point* is `lam > 0`, `A > 0`, `r` a root of `f`, `F(A) = F(r)`.

Prior art: Hermite-Lindemann (1882; proved in this build as `LindemannBridge.hermite_lindemann`);
time-map method (Laetsch 1970, Schaaf 1990). What this file adds: the first closed member inside the open
ring family, end to end in Lean via the elementary pinch.

* `pinch_sq` -- at a pinch point `P(A, y) = (lam/3)(y - r)^2`.
* `T_closed`, `T_sq_closed` -- `T(A) = c L`, `4 T(A)^2 = 6 L^2 / (lam (A - r))`,
  `L = log(sqrt B + sqrt A) - log(sqrt B - sqrt A)`, `B = A - r`.
* `D_closed` -- `D(lam, A) := ∫_0^1 d/dA[integrand] dt` equals `S (j0 + j1 L / (2 sqrt A sqrt B))`,
  `S = sqrt(2A)/sqrt(lam/3)`; `j0_val`, `j1_val` give `j0, j1` as rational functions of `p = -r`.
* `crit_value` -- if `D = 0` at a pinch point then `4 T(A)^2 = V(p) = 12p(2p^2+7p-12)^2 / (25(p-4)(p-1)^4)`.
* `crit_transcendental` -- if `D = 0` at a pinch point then `4 T(A)^2` is transcendental.
  Route: `4T^2` algebraic => `p` algebraic (`alg_of_V`: `N - beta M` is never the zero polynomial since
  `V(5) != V(6)`) => `A, B, sqrt A, sqrt B, e^L` algebraic and `L^2 = 4T^2 lam B / 6` algebraic
  => `L != 0` algebraic with `e^L` algebraic, contradicting Hermite-Lindemann.

NOT PROVED here: that `D(lam, A)` is the derivative `dT/dA` (differentiation under the integral sign;
`hasDerivAt_Qd` proves only the pointwise `Q_A`); existence of `lam*`; that the critical value is the break.
-/

open Set Real intervalIntegral

namespace Pinch

/-- Factor `P(A, y) = (F(A) - F(y)) / (A - y)` of the seat `f = 1 + x + lam x^2`. -/
noncomputable def P (lam A y : ℝ) : ℝ := 1 + (A + y) / 2 + lam * (A ^ 2 + A * y + y ^ 2) / 3

/-- Potential `F = x + x^2/2 + lam x^3/3`. -/
noncomputable def F (lam x : ℝ) : ℝ := x + x ^ 2 / 2 + lam * x ^ 3 / 3

lemma factor (lam A y : ℝ) : F lam A - F lam y = (A - y) * P lam A y := by unfold F P; ring

lemma fold_rel {lam A r : ℝ} (hr : lam * r ^ 2 + r + 1 = 0) (hF : F lam A = F lam r) (hAr : A ≠ r) :
    1 / 2 + lam * (A + 2 * r) / 3 = 0 := by
  have h1 : (A - r) * P lam A r = 0 := by rw [← factor]; linarith
  have h2 : P lam A r = 0 := (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hAr)
  have h3 : (A - r) * (1 / 2 + lam * (A + 2 * r) / 3) = 0 := by
    unfold P at h2; linear_combination h2 - hr
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hAr)

lemma r_neg {lam r : ℝ} (hlam : 0 < lam) (hr : lam * r ^ 2 + r + 1 = 0) : r < 0 := by
  by_contra h; push Not at h; nlinarith [sq_nonneg r]

/-- **The pinch.** At a pinch point the factor is a perfect square. -/
lemma pinch_sq {lam A r : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hr : lam * r ^ 2 + r + 1 = 0)
    (hF : F lam A = F lam r) (y : ℝ) : P lam A y = lam / 3 * (y - r) ^ 2 := by
  have hAr : A ≠ r := by have := r_neg hlam hr; intro h; linarith
  have hh := fold_rel hr hF hAr
  have h1 : (A - r) * P lam A r = 0 := by rw [← factor]; linarith
  have h2 : P lam A r = 0 := (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hAr)
  unfold P at h2 ⊢
  linear_combination (y - r) * hh + h2

/-- `L = log(sqrt B + sqrt A) - log(sqrt B - sqrt A)`. -/
noncomputable def Lg (A B : ℝ) : ℝ := log (sqrt B + sqrt A) - log (sqrt B - sqrt A)

/-- The log primitive of `1 / (B - A s^2)`. -/
noncomputable def G (A B s : ℝ) : ℝ :=
  (log (sqrt B + sqrt A * s) - log (sqrt B - sqrt A * s)) / (2 * sqrt A * sqrt B)

lemma hasDerivAt_G {A B s : ℝ} (hA : 0 < A) (hAB : A < B) (hs : s ∈ Icc (0:ℝ) 1) :
    HasDerivAt (G A B) (1 / (B - A * s ^ 2)) s := by
  have sa := sq_sqrt hA.le; have sb := sq_sqrt (hA.trans hAB).le
  have hsa : 0 < sqrt A := sqrt_pos.2 hA
  have hsab : sqrt A < sqrt B := sqrt_lt_sqrt hA.le hAB
  have p1 : 0 < sqrt B + sqrt A * s := by nlinarith [hs.1]
  have p2 : 0 < sqrt B - sqrt A * s := by nlinarith [hs.2]
  have d1 : HasDerivAt (fun s => sqrt B + sqrt A * s) (sqrt A) s := by
    simpa using ((hasDerivAt_id s).const_mul (sqrt A)).const_add (sqrt B)
  have d2 : HasDerivAt (fun s => sqrt B - sqrt A * s) (-sqrt A) s := by
    simpa using ((hasDerivAt_id s).const_mul (sqrt A)).const_sub (sqrt B)
  have := ((d1.log p1.ne').sub (d2.log p2.ne')).div_const (2 * sqrt A * sqrt B)
  unfold G
  convert this using 1
  have hW : B - A * s ^ 2 = (sqrt B + sqrt A * s) * (sqrt B - sqrt A * s) := by
    linear_combination s ^ 2 * sa - sb
  have hsb : 0 < sqrt B := hsa.trans hsab
  rw [hW]; field_simp; ring

lemma W_pos {A B s : ℝ} (hA : 0 < A) (hAB : A < B) (hs : s ∈ Icc (0:ℝ) 1) : 0 < B - A * s ^ 2 := by
  have : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  nlinarith

lemma int_inv {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∫ s in (0:ℝ)..1, 1 / (B - A * s ^ 2) = Lg A B / (2 * sqrt A * sqrt B) := by
  rw [integral_eq_sub_of_hasDerivAt (f := G A B)]
  · simp [G, Lg]
  · intro s hs; rw [uIcc_of_le zero_le_one] at hs; exact hasDerivAt_G hA hAB hs
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.div (by fun_prop) (fun s hs => (W_pos hA hAB hs).ne')

/-- **Closed form 1.** At a pinch point `T(A) = c L` with `c = 2A / sqrt(2A lam/3) / (2 sqrt A sqrt B)`,
`B = A - r`. -/
theorem T_closed {lam A r : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hr : lam * r ^ 2 + r + 1 = 0)
    (hF : F lam A = F lam r) :
    TimeMap.T (P lam) A = 2 * A / sqrt (2 * A * (lam / 3)) * (Lg A (A - r) / (2 * sqrt A * sqrt (A - r))) := by
  have hr0 := r_neg hlam hr
  have hAB : A < A - r := by linarith
  rw [← int_inv hA hAB, ← integral_const_mul]
  unfold TimeMap.T
  apply integral_congr
  intro s hs; rw [uIcc_of_le zero_le_one] at hs
  have hW := W_pos hA hAB hs
  simp only [TimeMap.integrand]
  rw [pinch_sq hlam hA hr hF, show 2 * A * (lam / 3 * (A - A * s ^ 2 - r) ^ 2)
      = 2 * A * (lam / 3) * (A - r - A * s ^ 2) ^ 2 by ring,
    sqrt_mul (by positivity), sqrt_sq hW.le]
  have : 0 < sqrt (2 * A * (lam / 3)) := sqrt_pos.2 (by positivity)
  field_simp

/-- The break form: `4 T(A)^2 = 6 L^2 / (lam (A - r))`. -/
theorem T_sq_closed {lam A r : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hr : lam * r ^ 2 + r + 1 = 0)
    (hF : F lam A = F lam r) :
    4 * TimeMap.T (P lam) A ^ 2 = 6 * Lg A (A - r) ^ 2 / (lam * (A - r)) := by
  have hr0 := r_neg hlam hr
  rw [T_closed hlam hA hr hF]
  have h1 := sq_sqrt (show 0 ≤ 2 * A * (lam / 3) by positivity)
  have h2 := sq_sqrt hA.le
  have h3 := sq_sqrt (show 0 ≤ A - r by linarith)
  have : 0 < sqrt (2 * A * (lam / 3)) := sqrt_pos.2 (by positivity)
  have : 0 < sqrt A := sqrt_pos.2 hA
  have : 0 < sqrt (A - r) := sqrt_pos.2 (by linarith)
  have : 0 < A - r := by linarith
  generalize sqrt (2 * A * (lam / 3)) = q at *
  generalize sqrt A = a at *
  generalize sqrt (A - r) = b at *
  field_simp
  rw [h1, h2, h3]; ring

/-! ## The A-derivative of the time map at a pinch point -/

/-- `Q(A, t) = P(A, A - A t^2)`. -/
noncomputable def Qd (lam A t : ℝ) : ℝ := P lam A (A - A * t ^ 2)

/-- `Q_A(A, t)`, the partial derivative of `Q` in `A` (`hasDerivAt_Qd`). -/
noncomputable def QA (lam A t : ℝ) : ℝ :=
  (1 + (1 - t ^ 2)) / 2 + 2 * lam * A * (1 + (1 - t ^ 2) + (1 - t ^ 2) ^ 2) / 3

lemma hasDerivAt_Qd (lam A t : ℝ) : HasDerivAt (fun A => Qd lam A t) (QA lam A t) A := by
  have : (fun A => Qd lam A t) = fun A => 1 + A * (1 + (1 - t ^ 2)) / 2
      + lam * A ^ 2 * (1 + (1 - t ^ 2) + (1 - t ^ 2) ^ 2) / 3 := by
    funext A; unfold Qd P; ring
  rw [this]
  have h := (((hasDerivAt_id A).mul_const ((1 + (1 - t ^ 2)) / 2)).const_add 1).add
    (((hasDerivAt_pow 2 A).const_mul lam).mul_const ((1 + (1 - t ^ 2) + (1 - t ^ 2) ^ 2) / 3))
  convert h using 1
  · funext A; simp; ring
  · unfold QA; simp; ring

/-- The `A`-derivative of the time-map integrand `sqrt(2A) / sqrt(Q)`, written in `t`. -/
noncomputable def Dint (lam A t : ℝ) : ℝ :=
  1 / sqrt (2 * A * Qd lam A t) - sqrt (2 * A) * QA lam A t / (2 * Qd lam A t * sqrt (Qd lam A t))

/-- `dT/dA` as the integral of the differentiated integrand. -/
noncomputable def D (lam A : ℝ) : ℝ := ∫ t in (0:ℝ)..1, Dint lam A t

/-- Coefficients, generic in `lam, A, p` (`p = -r`, `B = A + p`, `k = lam/3`). -/
noncomputable def al1 (lam A p : ℝ) : ℝ := 1 / (2 * A) + 2 * (lam / 3) * (1 - 2 * p / A)
noncomputable def al0 (lam A p : ℝ) : ℝ := 1 / 2 - p / (2 * A) + 2 * (lam / 3) * (A - p + p ^ 2 / A)
noncomputable def e2 (lam A p : ℝ) : ℝ := -al0 lam A p / (2 * (lam / 3)) / (4 * (A + p))
noncomputable def e1 (lam A p : ℝ) : ℝ :=
  (-al1 lam A p / (2 * (lam / 3)) + 3 * e2 lam A p) / (2 * (A + p))
noncomputable def j1 (lam A p : ℝ) : ℝ := -1 / (2 * A) + e1 lam A p
noncomputable def j0 (lam A p : ℝ) : ℝ := e1 lam A p / p + e2 lam A p / p ^ 2

lemma Dint_pinch {lam A r t : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hr : lam * r ^ 2 + r + 1 = 0)
    (hF : F lam A = F lam r) (ht : t ∈ Icc (0:ℝ) 1) :
    Dint lam A t = sqrt (2 * A) / sqrt (lam / 3) *
      (-1 / (2 * A) / (A - r - A * t ^ 2)
        + (-al1 lam A (-r) / (2 * (lam / 3))) / (A - r - A * t ^ 2) ^ 2
        + (-al0 lam A (-r) / (2 * (lam / 3))) / (A - r - A * t ^ 2) ^ 3) := by
  have hr0 := r_neg hlam hr
  have hW := W_pos hA (show A < A - r by linarith) ht
  have hQ : Qd lam A t = lam / 3 * (A - r - A * t ^ 2) ^ 2 := by
    unfold Qd; rw [pinch_sq hlam hA hr hF]; ring
  have hQA : QA lam A t = al0 lam A (-r) + al1 lam A (-r) * (A - r - A * t ^ 2)
      + 2 * (lam / 3) / A * (A - r - A * t ^ 2) ^ 2 := by
    unfold QA al0 al1; field_simp; ring
  have s1 : sqrt (2 * A * (lam / 3 * (A - r - A * t ^ 2) ^ 2))
      = sqrt (2 * A) * sqrt (lam / 3) * (A - r - A * t ^ 2) := by
    rw [show 2 * A * (lam / 3 * (A - r - A * t ^ 2) ^ 2)
      = (2 * A * (lam / 3)) * (A - r - A * t ^ 2) ^ 2 by ring,
      sqrt_mul (by positivity), sqrt_sq hW.le, sqrt_mul (by positivity)]
  have s2 : sqrt (lam / 3 * (A - r - A * t ^ 2) ^ 2) = sqrt (lam / 3) * (A - r - A * t ^ 2) := by
    rw [sqrt_mul (by positivity), sqrt_sq hW.le]
  unfold Dint
  rw [hQA, hQ, s1, s2]
  have h1 := sq_sqrt (show 0 ≤ 2 * A by positivity)
  have : 0 < sqrt (2 * A) := sqrt_pos.2 (by positivity)
  have : 0 < sqrt (lam / 3) := sqrt_pos.2 (by positivity)
  generalize sqrt (2 * A) = a at *
  generalize sqrt (lam / 3) = b at *
  generalize A - r - A * t ^ 2 = W at *
  unfold al0 al1
  field_simp
  rw [h1]
  ring

/-- Explicit primitive of the pinched derivative integrand (bracket only). -/
noncomputable def H (lam A r t : ℝ) : ℝ :=
  e1 lam A (-r) * (t / (A - r - A * t ^ 2)) + e2 lam A (-r) * (t / (A - r - A * t ^ 2) ^ 2)
    + j1 lam A (-r) * G A (A - r) t

lemma hasDerivAt_H {lam A r t : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hr0 : r < 0) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (H lam A r)
      (-1 / (2 * A) / (A - r - A * t ^ 2)
        + (-al1 lam A (-r) / (2 * (lam / 3))) / (A - r - A * t ^ 2) ^ 2
        + (-al0 lam A (-r) / (2 * (lam / 3))) / (A - r - A * t ^ 2) ^ 3) t := by
  have hAB : A < A - r := by linarith
  have hW := W_pos hA hAB ht
  have hWd : HasDerivAt (fun t => A - r - A * t ^ 2) (-(A * (2 * t))) t := by
    have := ((hasDerivAt_pow 2 t).const_mul A).const_sub (A - r)
    simpa using this
  have d1 := (hasDerivAt_id t).div hWd hW.ne'
  have d2 := (hasDerivAt_id t).div (hWd.pow 2) (pow_ne_zero 2 hW.ne')
  have d3 := hasDerivAt_G hA hAB ht
  have := ((d1.const_mul (e1 lam A (-r))).add (d2.const_mul (e2 lam A (-r)))).add
    (d3.const_mul (j1 lam A (-r)))
  convert this using 1
  · funext y; simp only [H, Pi.add_apply, Pi.div_apply, Pi.pow_apply, id]
  have hk : lam ≠ 0 := hlam.ne'
  have hB : A + -r ≠ 0 := by linarith
  have hA0 : A ≠ 0 := hA.ne'
  have hW0 := hW.ne'
  simp only [id, j1, e1, e2, Pi.pow_apply]
  norm_num
  field_simp
  ring

/-- **Closed form 2.** At a pinch point `dT/dA = P0 + Q0 L` with
`P0 = S j0`, `Q0 = S j1 / (2 sqrt A sqrt B)`, `S = sqrt(2A)/sqrt(lam/3)`, `B = A - r`. -/
theorem D_closed {lam A r : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hr : lam * r ^ 2 + r + 1 = 0)
    (hF : F lam A = F lam r) :
    D lam A = sqrt (2 * A) / sqrt (lam / 3) *
      (j0 lam A (-r) + j1 lam A (-r) * (Lg A (A - r) / (2 * sqrt A * sqrt (A - r)))) := by
  have hr0 := r_neg hlam hr
  have hAB : A < A - r := by linarith
  unfold D
  rw [integral_congr (g := fun t => sqrt (2 * A) / sqrt (lam / 3) *
      (-1 / (2 * A) / (A - r - A * t ^ 2)
        + (-al1 lam A (-r) / (2 * (lam / 3))) / (A - r - A * t ^ 2) ^ 2
        + (-al0 lam A (-r) / (2 * (lam / 3))) / (A - r - A * t ^ 2) ^ 3))
      (fun t ht => by rw [uIcc_of_le zero_le_one] at ht; exact Dint_pinch hlam hA hr hF ht),
    integral_const_mul, integral_eq_sub_of_hasDerivAt (f := H lam A r)]
  · congr 1
    have h0 : G A (A - r) 0 = 0 := by simp [G]
    have h1 : G A (A - r) 1 = Lg A (A - r) / (2 * sqrt A * sqrt (A - r)) := by simp [G, Lg]
    simp only [H, h0, h1, j0]
    have : -r ≠ 0 := by linarith
    rw [show A - r - A * 1 ^ 2 = -r by ring]
    simp; ring
  · intro t ht; rw [uIcc_of_le zero_le_one] at ht; exact hasDerivAt_H hlam hA hr0 ht
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    have hW : ∀ t ∈ Icc (0:ℝ) 1, A - r - A * t ^ 2 ≠ 0 := fun t ht => (W_pos hA hAB ht).ne'
    refine ((continuousOn_const.div (by fun_prop) hW).add
      (continuousOn_const.div (by fun_prop) (fun t ht => pow_ne_zero 2 (hW t ht)))).add
      (continuousOn_const.div (by fun_prop) (fun t ht => pow_ne_zero 3 (hW t ht)))

/-! ## Transcendence of the critical value -/

/-- Pinch points are rationally parametrised by `p = -r > 4`. -/
lemma pinch_param {lam A r : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hr : lam * r ^ 2 + r + 1 = 0)
    (hF : F lam A = F lam r) :
    4 < -r ∧ lam = (-r - 1) / (-r) ^ 2 ∧ A = -r * (-r - 4) / (2 * (-r - 1)) := by
  have hr0 := r_neg hlam hr
  have hh := fold_rel hr hF (by intro h; linarith)
  have hp1 : 1 < -r := by nlinarith [mul_pos hlam (show 0 < r ^ 2 by have := hr0.ne; positivity)]
  have hl : lam = (-r - 1) / (-r) ^ 2 := by
    rw [eq_div_iff (by positivity)]; linear_combination hr
  have hA' : A = -r * (-r - 4) / (2 * (-r - 1)) := by
    have hE : lam * (A * (2 * (-r - 1)) - (-r * (-r - 4))) = 0 := by
      linear_combination (-6 * r - 6) * hh + 3 * hr
    have := (mul_eq_zero.1 hE).resolve_left hlam.ne'
    rw [eq_div_iff (by linarith)]; linarith
  refine ⟨?_, hl, hA'⟩
  by_contra h; push Not at h
  have : -r * (-r - 4) / (2 * (-r - 1)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)
  linarith

lemma j1_val {lam A p : ℝ} (hp : 4 < p) (hl : lam = (p - 1) / p ^ 2) (hA : A = p * (p - 4) / (2 * (p - 1))) :
    j1 lam A p = -5 * (p - 1) / (8 * p * (p - 2)) := by
  subst hl hA
  have : p - 1 ≠ 0 := by linarith
  have : p - 2 ≠ 0 := by linarith
  have : p - 4 ≠ 0 := by linarith
  have : p ≠ 0 := by linarith
  have : p * (p - 4) + 2 * (p - 1) * p ≠ 0 := by nlinarith
  have hB : p * (p - 4) / (2 * (p - 1)) + p = 3 * p * (p - 2) / (2 * (p - 1)) := by field_simp; ring
  unfold j1 e1 e2 al0 al1; rw [hB]; field_simp; ring

lemma j0_val {lam A p : ℝ} (hp : 4 < p) (hl : lam = (p - 1) / p ^ 2) (hA : A = p * (p - 4) / (2 * (p - 1))) :
    j0 lam A p = (2 * p ^ 2 + 7 * p - 12) / (8 * p ^ 2 * (p - 2) * (p - 4)) := by
  subst hl hA
  have : p - 1 ≠ 0 := by linarith
  have : p - 2 ≠ 0 := by linarith
  have : p - 4 ≠ 0 := by linarith
  have : p ≠ 0 := by linarith
  have : p * (p - 4) + 2 * (p - 1) * p ≠ 0 := by nlinarith
  have hB : p * (p - 4) / (2 * (p - 1)) + p = 3 * p * (p - 2) / (2 * (p - 1)) := by field_simp; ring
  unfold j0 e1 e2 al0 al1; rw [hB]; field_simp; ring

/-- The critical value along the pinch curve, as a rational function of `p = -r`. -/
noncomputable def V (p : ℝ) : ℝ := 12 * p * (2 * p ^ 2 + 7 * p - 12) ^ 2 / (25 * (p - 4) * (p - 1) ^ 4)

lemma Lg_pos {A B : ℝ} (hA : 0 < A) (hAB : A < B) : 0 < Lg A B := by
  unfold Lg
  have hsa : 0 < sqrt A := sqrt_pos.2 hA
  have hsab : sqrt A < sqrt B := sqrt_lt_sqrt hA.le hAB
  have := log_lt_log (by linarith) (show sqrt B - sqrt A < sqrt B + sqrt A by linarith)
  linarith

lemma exp_Lg {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    exp (Lg A B) = (sqrt B + sqrt A) / (sqrt B - sqrt A) := by
  have hsa : 0 < sqrt A := sqrt_pos.2 hA
  have hsab : sqrt A < sqrt B := sqrt_lt_sqrt hA.le hAB
  unfold Lg; rw [exp_sub, exp_log (by linarith), exp_log (by linarith)]

lemma memA {x : ℝ} : x ∈ algebraicClosure ℚ ℝ ↔ IsAlgebraic ℚ x := mem_algebraicClosure_iff

/-- Non-constancy of `V`: a root of `N - beta M` (`beta` algebraic) is algebraic, because `N - beta M`
takes two different values ratios at `p = 5, 6` and so is never the zero polynomial. -/
lemma alg_of_V {p β : ℝ} (hβ : IsAlgebraic ℚ β)
    (hV : 12 * p * (2 * p ^ 2 + 7 * p - 12) ^ 2 = β * (25 * (p - 4) * (p - 1) ^ 4)) :
    IsAlgebraic ℚ p := by
  open Polynomial in
  let b : algebraicClosure ℚ ℝ := ⟨β, memA.2 hβ⟩
  have hpK : IsAlgebraic (algebraicClosure ℚ ℝ) p := by
    refine ⟨12 * X * (2 * X ^ 2 + 7 * X - 12) ^ 2 - C b * (25 * (X - 4) * (X - 1) ^ 4), ?_, ?_⟩
    · intro h
      have e5 := congrArg (Polynomial.aeval (5:ℝ)) h
      have e6 := congrArg (Polynomial.aeval (6:ℝ)) h
      simp [b, map_ofNat] at e5 e6
      norm_num at e5 e6
      linarith
    · simp [b, map_ofNat]; linear_combination hV
  exact hpK.restrictScalars ℚ

lemma crit_alg {p m L : ℝ} (hp : 4 < p) (hm0 : 0 < m)
    (hm2 : m ^ 2 = p * (p - 4) / (2 * (p - 1)) * (p * (p - 4) / (2 * (p - 1)) + p))
    (hJ : (2 * p ^ 2 + 7 * p - 12) / (8 * p ^ 2 * (p - 2) * (p - 4))
      + -5 * (p - 1) / (8 * p * (p - 2)) * (L / (2 * m)) = 0) :
    6 * L ^ 2 / ((p - 1) / p ^ 2 * (p * (p - 4) / (2 * (p - 1)) + p)) = V p := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : p - 2 ≠ 0 := by linarith
  have h4 : p - 4 ≠ 0 := by linarith
  have h0 : p ≠ 0 := by linarith
  set a := (2 * p ^ 2 + 7 * p - 12) / (8 * p ^ 2 * (p - 2) * (p - 4)) with ha
  set b := -5 * (p - 1) / (8 * p * (p - 2)) with hb
  have hb0 : b ≠ 0 := by
    rw [hb]; exact div_ne_zero (mul_ne_zero (by norm_num) h1) (mul_ne_zero (mul_ne_zero (by norm_num) h0) h2)
  have hX : L / (2 * m) = -a / b := by rw [eq_div_iff hb0]; linear_combination hJ
  have hL : L = 2 * m * (-a / b) := by rw [← hX]; field_simp
  rw [hL, mul_pow, mul_pow, hm2, ha, hb]
  unfold V
  have : p * (p - 4) + 2 * (p - 1) * p ≠ 0 := by nlinarith
  have hB : p * (p - 4) / (2 * (p - 1)) + p = 3 * p * (p - 2) / (2 * (p - 1)) := by field_simp; ring
  rw [hB]
  field_simp
  ring

/-- At a pinch fold the critical value is the rational function `V(p)`, `p = -r`. -/
theorem crit_value {lam A r : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hr : lam * r ^ 2 + r + 1 = 0)
    (hF : F lam A = F lam r) (hD : D lam A = 0) :
    4 * TimeMap.T (P lam) A ^ 2 = V (-r) := by
  obtain ⟨hp, hl, hA'⟩ := pinch_param hlam hA hr hF
  have hr0 := r_neg hlam hr
  have hS : 0 < sqrt (2 * A) / sqrt (lam / 3) :=
    div_pos (sqrt_pos.2 (by positivity)) (sqrt_pos.2 (by positivity))
  rw [D_closed hlam hA hr hF] at hD
  have hJ := (mul_eq_zero.1 hD).resolve_left hS.ne'
  rw [j0_val hp hl hA', j1_val hp hl hA'] at hJ
  have hm2 : (sqrt A * sqrt (A - r)) ^ 2 = A * (A - r) := by
    rw [mul_pow, sq_sqrt hA.le, sq_sqrt (by linarith)]
  have hm0 : 0 < sqrt A * sqrt (A - r) := mul_pos (sqrt_pos.2 hA) (sqrt_pos.2 (by linarith))
  rw [T_sq_closed hlam hA hr hF]
  rw [show 2 * sqrt A * sqrt (A - r) = 2 * (sqrt A * sqrt (A - r)) by ring] at hJ
  generalize sqrt A * sqrt (A - r) = m at *
  generalize Lg A (A - r) = L at *
  rw [show A - r = A + -r by ring] at hm2 ⊢
  generalize -r = p at *
  subst hl hA'
  exact crit_alg hp hm0 hm2 hJ

/-- **Transcendence of the critical value.** At any pinch point where the fold condition
`dT/dA = 0` holds, the push `4 T(A)^2` is transcendental. -/
theorem crit_transcendental {lam A r : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hr : lam * r ^ 2 + r + 1 = 0)
    (hF : F lam A = F lam r) (hD : D lam A = 0) :
    Transcendental ℚ (4 * TimeMap.T (P lam) A ^ 2) := by
  intro hβ
  obtain ⟨hp, hl, hA'⟩ := pinch_param hlam hA hr hF
  have hr0 := r_neg hlam hr
  have hAB : A < A - r := by linarith
  have hV := crit_value hlam hA hr hF hD
  have hpa : IsAlgebraic ℚ (-r) := by
    refine alg_of_V hβ ?_
    rw [hV]; unfold V
    have : (-r) - 1 ≠ 0 := by linarith
    have : (-r) - 4 ≠ 0 := by linarith
    field_simp
  have hpK := memA.2 hpa
  have hAK : A ∈ algebraicClosure ℚ ℝ := by
    rw [hA']
    exact div_mem (mul_mem hpK (sub_mem hpK (ofNat_mem _ 4)))
      (mul_mem (ofNat_mem _ 2) (sub_mem hpK (one_mem _)))
  have hlK : lam ∈ algebraicClosure ℚ ℝ := by
    rw [hl]; exact div_mem (sub_mem hpK (one_mem _)) (pow_mem hpK 2)
  have hBK : A - r ∈ algebraicClosure ℚ ℝ := by
    rw [show A - r = A + -r by ring]; exact add_mem hAK hpK
  have hsA : IsAlgebraic ℚ (sqrt A) :=
    IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [sq_sqrt hA.le]; exact memA.1 hAK)
  have hsB : IsAlgebraic ℚ (sqrt (A - r)) :=
    IsAlgebraic.of_pow (n := 2) (by norm_num) (by rw [sq_sqrt (by linarith)]; exact memA.1 hBK)
  have hexp : IsAlgebraic ℚ (exp (Lg A (A - r))) := by
    rw [exp_Lg hA hAB]
    exact memA.1 (div_mem (add_mem (memA.2 hsB) (memA.2 hsA)) (sub_mem (memA.2 hsB) (memA.2 hsA)))
  have hL2 : IsAlgebraic ℚ (Lg A (A - r) ^ 2) := by
    have hT := T_sq_closed hlam hA hr hF
    have : Lg A (A - r) ^ 2 = 4 * TimeMap.T (P lam) A ^ 2 * (lam * (A - r)) / 6 := by
      have hB0 : A - r ≠ 0 := by linarith
      rw [hT]; field_simp
    rw [this]
    exact memA.1 (div_mem (mul_mem (memA.2 hβ) (mul_mem hlK hBK)) (ofNat_mem _ 6))
  have hLa : IsAlgebraic ℚ (Lg A (A - r)) := IsAlgebraic.of_pow (n := 2) (by norm_num) hL2
  exact LindemannBridge.hermite_lindemann _ hLa (Lg_pos hA hAB).ne' hexp

end Pinch

#print axioms Pinch.pinch_sq
#print axioms Pinch.T_closed
#print axioms Pinch.T_sq_closed
#print axioms Pinch.hasDerivAt_Qd
#print axioms Pinch.D_closed
#print axioms Pinch.j0_val
#print axioms Pinch.j1_val
#print axioms Pinch.alg_of_V
#print axioms Pinch.crit_value
#print axioms Pinch.crit_transcendental
