import Mathlib
import Mistranslation.Recipe

/-! # K_3 bridge: the class step through the recipe (2026-10-23)

K_3 (`v'' = mu (v^(-5/3) + lam v^(-4/3))`, found by the closable-family generator) is Kepler with weight
(B + D cosh)^3: I = c_T T + sinh(T) g, break = max of 12 I^2 m^2 / W. The critical equation is linear in the clock T.
Eliminating T leaves PI576(m) = 0, a polynomial with integer coefficients in (lam, m, mu) whose value at m = 0 is
32400 mu lam^2. So for every algebraic lam > 0 the K_3 break is transcendental, given Hermite-Lindemann and the
critical equation (here a hypothesis; checked numerically in `v4/sql/k3_elimination_check.sql`). -/

namespace KThree

open Polynomial

section Pieces
variable {R : Type*} [CommRing R]

def aK (l m : R) : R := 1 + l * m
def WK (l m : R) : R := 1 + 2 * l * m
def EK (l m : R) : R := 1 + 2 * l * m - l * m ^ 2
def ct2 (l m : R) : R := 2 * l ^ 3 * m ^ 2 + 3 * l * aK l m ^ 2
def ct2d (l m : R) : R := 4 * l ^ 3 * m + 6 * l ^ 2 * aK l m
def P12 (l m : R) : R := ct2 l m * (5 + 3 * l * m) + m * ct2d l m * WK l m
def g6 (l m : R) : R := 18 * l ^ 2 * m ^ 4 * aK l m + 9 * l * m ^ 2 * aK l m * EK l m + 4 * m ^ 2 * aK l m ^ 3
  + 2 * aK l m * EK l m ^ 2
def g6d (l m : R) : R := 18 * l ^ 2 * (4 * m ^ 3 * aK l m + m ^ 4 * l)
  + 9 * l * (2 * m * aK l m * EK l m + m ^ 2 * l * EK l m + m ^ 2 * aK l m * (2 * l - 2 * l * m))
  + 4 * (2 * m * aK l m ^ 3 + 3 * m ^ 2 * aK l m ^ 2 * l)
  + 2 * (l * EK l m ^ 2 + 2 * aK l m * EK l m * (2 * l - 2 * l * m))
def gd6 (l m : R) : R := (g6 l m + m * g6d l m) * WK l m - 6 * l * m * g6 l m
def Cn (l m : R) : R := (2 * l - 2 * l * m) * m * aK l m - EK l m * (1 + 2 * l * m)
def S2n (l m : R) : R := EK l m ^ 2 - (m * aK l m) ^ 2
def SP12 (l m : R) : R := 6 * m ^ 4 * ct2 l m * Cn l m * WK l m * aK l m + 2 * EK l m * Cn l m * g6 l m * WK l m
  + 2 * aK l m * S2n l m * (gd6 l m + aK l m * g6 l m)
def N24 (l m : R) : R := 2 * S2n l m * g6 l m * P12 l m * aK l m - ct2 l m * SP12 l m
def PI576 (l m μ : R) : R := 144 * μ * WK l m ^ 7 * aK l m ^ 4 * S2n l m * P12 l m ^ 2 - 12 * m ^ 2 * N24 l m ^ 2

variable {S : Type*} [CommRing S]

lemma map_PI576 (f : R →+* S) (l m μ : R) : f (PI576 l m μ) = PI576 (f l) (f m) (f μ) := by
  simp [PI576, N24, SP12, S2n, Cn, gd6, g6d, g6, P12, ct2d, ct2, EK, WK, aK, map_ofNat]

lemma map_c1 (f : R →+* S) (l m s : R) :
    f (6 * m ^ 5 * aK l m ^ 3 * s * P12 l m) = 6 * f m ^ 5 * aK (f l) (f m) ^ 3 * f s * P12 (f l) (f m) := by
  simp [P12, ct2d, ct2, WK, aK, map_ofNat]

lemma map_c0 (f : R →+* S) (l m : R) : f (-SP12 l m) = -SP12 (f l) (f m) := by
  simp [SP12, S2n, Cn, gd6, g6d, g6, ct2, EK, WK, aK, map_ofNat]

lemma map_S2n (f : R →+* S) (l m : R) : f (S2n l m) = S2n (f l) (f m) := by
  simp [S2n, EK, aK, map_ofNat]

lemma map_EK (f : R →+* S) (l m : R) : f (EK l m) = EK (f l) (f m) := by simp [EK, map_ofNat]
lemma map_aK (f : R →+* S) (l m : R) : f (aK l m) = aK (f l) (f m) := by simp [aK]

end Pieces

lemma PI576_zero (l μ : ℝ) : PI576 l 0 μ = 32400 * μ * l ^ 2 := by
  simp [PI576, N24, SP12, S2n, Cn, gd6, g6d, g6, P12, ct2d, ct2, EK, WK, aK]; ring

lemma P12_pos {l m : ℝ} (hl : 0 < l) (hm : 0 < m) : 0 < P12 l m := by
  unfold P12 ct2d ct2 WK aK; positivity

/-- An algebraic real, seen in the algebraic numbers inside ℝ, mapped back. -/
lemma alg_of_map {K : IntermediateField ℚ ℝ} (x : K) (hK : ∀ y : K, IsAlgebraic ℚ (y : ℝ)) :
    IsAlgebraic ℚ (algebraMap K ℝ x) := hK x

/-- **K_3 class step.** -/
theorem class_of_crit (HL : Breaks.HermiteLindemann) {lam m T S C μ : ℝ}
    (hl : 0 < lam) (hlam : IsAlgebraic ℚ lam) (hm : 0 < m) (hT : 0 < T) (hS : 0 < S) (hμ0 : 0 < μ)
    (hC : m * aK lam m * C = EK lam m) (hS2 : m ^ 2 * aK lam m ^ 2 * S ^ 2 = S2n lam m)
    (hcrit : 6 * m ^ 5 * aK lam m ^ 3 * S * P12 lam m * T + SP12 lam m = 0)
    (hμ : 3 * μ * WK lam m ^ 7 = m ^ 4 * (3 * m ^ 3 * ct2 lam m * T + S * g6 lam m) ^ 2)
    (hexp : Real.exp T = C + S) :
    Transcendental ℚ μ := by
  have ha : 0 < aK lam m := by unfold aK; positivity
  have hP := P12_pos hl hm
  set Y := 3 * m ^ 3 * ct2 lam m * T + S * g6 lam m with hYdef
  have hY : 2 * m ^ 2 * aK lam m ^ 3 * S * P12 lam m * Y = N24 lam m := by
    rw [hYdef]; unfold N24
    linear_combination ct2 lam m * hcrit + 2 * g6 lam m * P12 lam m * aK lam m * hS2
  have hPI : PI576 lam m μ = 0 := by
    unfold PI576
    linear_combination (48 * aK lam m ^ 4 * S2n lam m * P12 lam m ^ 2) * hμ
      - (48 * m ^ 4 * Y ^ 2 * aK lam m ^ 4 * P12 lam m ^ 2) * hS2
      + (12 * m ^ 2 * (2 * m ^ 2 * aK lam m ^ 3 * S * P12 lam m * Y + N24 lam m)) * hY
  refine Recipe.transcendental_of_recipe HL (z := m) (T := T)
    (c1 := 6 * m ^ 5 * aK lam m ^ 3 * S * P12 lam m) (c0 := -SP12 lam m)
    hT.ne' (by linear_combination hcrit) (by positivity) (fun hμa => ?_) (fun hmQ => ?_)
  · -- ELIMINATE: m is a root of PI576 (lam, X, mu), which is 32400 mu lam^2 at X = 0
    let P : (algebraicClosure ℚ ℝ)[X] := PI576 (Polynomial.C (Recipe.toK hlam)) X (Polynomial.C (Recipe.toK hμa))
    have hev : ∀ x : ℝ, aeval x P = PI576 lam x μ := by
      intro x
      rw [show aeval x P = (aeval x : (algebraicClosure ℚ ℝ)[X] →ₐ[_] ℝ).toRingHom P from rfl, map_PI576]
      simp
      rfl
    refine ⟨P, fun h0 => ?_, by rw [hev]; exact hPI⟩
    have := hev 0
    rw [h0, map_zero, PI576_zero] at this
    have : 0 < 32400 * μ * lam ^ 2 := by positivity
    linarith
  · -- DESCEND: everything is a ring expression in lam, m, S, plus C = E/(m a)
    let K := algebraicClosure ℚ ℝ
    have hK : ∀ y : K, IsAlgebraic ℚ (y : ℝ) := fun y => mem_algebraicClosure_iff.1 y.2
    have hS2a : IsAlgebraic ℚ (S ^ 2) := by
      have hne : m ^ 2 * aK lam m ^ 2 ≠ 0 := by positivity
      have : S ^ 2 = S2n lam m * (m ^ 2 * aK lam m ^ 2)⁻¹ := by field_simp; linear_combination hS2
      rw [this]
      have h1 : IsAlgebraic ℚ (S2n lam m) := by
        have := hK (S2n (Recipe.toK hlam) (Recipe.toK hmQ))
        rwa [show ((S2n (Recipe.toK hlam) (Recipe.toK hmQ) : K) : ℝ)
          = algebraMap K ℝ (S2n (Recipe.toK hlam) (Recipe.toK hmQ)) from rfl, map_S2n] at this
      have h2 : IsAlgebraic ℚ (aK lam m) := by
        have := hK (aK (Recipe.toK hlam) (Recipe.toK hmQ))
        rwa [show ((aK (Recipe.toK hlam) (Recipe.toK hmQ) : K) : ℝ)
          = algebraMap K ℝ (aK (Recipe.toK hlam) (Recipe.toK hmQ)) from rfl, map_aK] at this
      exact h1.mul ((hmQ.pow 2).mul (h2.pow 2)).inv
    have hSa : IsAlgebraic ℚ S := IsAlgebraic.of_pow (by norm_num) hS2a
    have hCa : IsAlgebraic ℚ C := by
      have hne : m * aK lam m ≠ 0 := by positivity
      have : C = EK lam m * (m * aK lam m)⁻¹ := by field_simp; linear_combination hC
      rw [this]
      have h1 : IsAlgebraic ℚ (EK lam m) := by
        have := hK (EK (Recipe.toK hlam) (Recipe.toK hmQ))
        rwa [show ((EK (Recipe.toK hlam) (Recipe.toK hmQ) : K) : ℝ)
          = algebraMap K ℝ (EK (Recipe.toK hlam) (Recipe.toK hmQ)) from rfl, map_EK] at this
      have h2 : IsAlgebraic ℚ (aK lam m) := by
        have := hK (aK (Recipe.toK hlam) (Recipe.toK hmQ))
        rwa [show ((aK (Recipe.toK hlam) (Recipe.toK hmQ) : K) : ℝ)
          = algebraMap K ℝ (aK (Recipe.toK hlam) (Recipe.toK hmQ)) from rfl, map_aK] at this
      exact h1.mul (hmQ.mul h2).inv
    let sK := Recipe.toK hSa
    refine ⟨?_, ?_, by rw [hexp]; exact hCa.add hSa⟩
    · have := hK (6 * Recipe.toK hmQ ^ 5 * aK (Recipe.toK hlam) (Recipe.toK hmQ) ^ 3 * sK
        * P12 (Recipe.toK hlam) (Recipe.toK hmQ))
      rwa [show ((6 * Recipe.toK hmQ ^ 5 * aK (Recipe.toK hlam) (Recipe.toK hmQ) ^ 3 * sK
        * P12 (Recipe.toK hlam) (Recipe.toK hmQ) : K) : ℝ) = algebraMap K ℝ (6 * Recipe.toK hmQ ^ 5
        * aK (Recipe.toK hlam) (Recipe.toK hmQ) ^ 3 * sK * P12 (Recipe.toK hlam) (Recipe.toK hmQ)) from rfl,
        map_c1] at this
    · have := hK (-SP12 (Recipe.toK hlam) (Recipe.toK hmQ))
      rwa [show ((-SP12 (Recipe.toK hlam) (Recipe.toK hmQ) : K) : ℝ)
        = algebraMap K ℝ (-SP12 (Recipe.toK hlam) (Recipe.toK hmQ)) from rfl, map_c0] at this

end KThree
