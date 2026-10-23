import Mathlib
import Mistranslation.Recipe

/-! # P_5 pair: the class step through the recipe (2026-10-23)

P_5 (`v'' = mu v^(-7/5) + kap v^(-3/5)`): u = v^(2/5), turning point x, Q = mu/kap, u = p + r cosh(eta), weight
(p + r cosh)^2. With pN = x^2 - Q, D = x^2 + Q, D C = 2x - x^2 + Q, D^2 S^2 = 4x(1-x)(x+Q):
  time  (2 pN^2 + D^2) T + (4 pN D + D^2 C) S = 8 x^2 k,            k^2 = kap/5
  top   4 x^3 CdN + 3 pN D^3 S T + D^2 S^2 (2 pN^2 + 2 D^2 + pN D C) = 0,   CdN = 2(Q - 2xQ - x^2)
both LINEAR in the clock T (clock coefficient 3 pN D^3 S: the switch is pN = x^2 - Q). Eliminating T:
  G5 = 5 Lam^2 - 576 kap x^4 D^4 S2N pN^2,  Lam = S2N Delta - 4x^3 (2pN^2 + D^2) CdN,
  G5(1) = 320 (2(1-Q)^2 + (1+Q)^2)^2 (1+Q)^2 != 0.  Checked at the real tops: `v4/sql/p5_elimination_check.sql`. -/

namespace PFive

open Polynomial

section Pieces
variable {R : Type*} [CommRing R]
def pN (Q x : R) : R := x ^ 2 - Q
def DD (Q x : R) : R := x ^ 2 + Q
def CN (Q x : R) : R := 2 * x - x ^ 2 + Q
def CdN (Q x : R) : R := 2 * (Q - 2 * x * Q - x ^ 2)
def S2N (Q x : R) : R := 4 * x * (1 - x) * (x + Q)
def Dl (Q x : R) : R := 3 * pN Q x * DD Q x ^ 2 * (4 * pN Q x + CN Q x)
  - (2 * pN Q x ^ 2 + DD Q x ^ 2) * (2 * pN Q x ^ 2 + 2 * DD Q x ^ 2 + pN Q x * CN Q x)
def Lm (Q x : R) : R := S2N Q x * Dl Q x - 4 * x ^ 3 * (2 * pN Q x ^ 2 + DD Q x ^ 2) * CdN Q x
def G5 (kap Q x : R) : R := 5 * Lm Q x ^ 2 - 576 * kap * x ^ 4 * DD Q x ^ 4 * S2N Q x * pN Q x ^ 2

variable {S : Type*} [CommRing S]
lemma map_G5 (f : R →+* S) (kap Q x : R) : f (G5 kap Q x) = G5 (f kap) (f Q) (f x) := by
  simp [G5, Lm, Dl, S2N, CdN, CN, DD, pN, map_ofNat]
lemma map_c1 (f : R →+* S) (Q x s : R) :
    f (3 * pN Q x * DD Q x ^ 3 * s) = 3 * pN (f Q) (f x) * DD (f Q) (f x) ^ 3 * f s := by
  simp [DD, pN, map_ofNat]
lemma map_c0 (f : R →+* S) (Q x s c : R) :
    f (-(4 * x ^ 3 * CdN Q x + DD Q x ^ 2 * s ^ 2 * (2 * pN Q x ^ 2 + 2 * DD Q x ^ 2 + pN Q x * DD Q x * c)))
      = -(4 * f x ^ 3 * CdN (f Q) (f x) + DD (f Q) (f x) ^ 2 * f s ^ 2 * (2 * pN (f Q) (f x) ^ 2
        + 2 * DD (f Q) (f x) ^ 2 + pN (f Q) (f x) * DD (f Q) (f x) * f c)) := by
  simp [CdN, DD, pN, map_ofNat]
lemma map_DD (f : R →+* S) (Q x : R) : f (DD Q x) = DD (f Q) (f x) := by simp [DD]
lemma map_CN (f : R →+* S) (Q x : R) : f (CN Q x) = CN (f Q) (f x) := by simp [CN, map_ofNat]
lemma map_S2N (f : R →+* S) (Q x : R) : f (S2N Q x) = S2N (f Q) (f x) := by simp [S2N, map_ofNat]
end Pieces

lemma G5_one (kap Q : ℝ) : G5 kap Q 1 = 320 * (2 * (1 - Q) ^ 2 + (1 + Q) ^ 2) ^ 2 * (1 + Q) ^ 2 := by
  simp [G5, Lm, Dl, S2N, CdN, CN, DD, pN]; ring

/-- **P_5 class step (kap > 0).** -/
theorem class_of_crit (HL : Breaks.HermiteLindemann) {kap μ Q x T S C k : ℝ}
    (hk0 : 0 < kap) (hkap : IsAlgebraic ℚ kap) (hμ0 : 0 < μ) (hQ : Q * kap = μ)
    (hx : 0 < x) (hT : 0 < T) (hS : 0 < S) (hp : pN Q x ≠ 0) (hk : 5 * k ^ 2 = kap)
    (hC : DD Q x * C = CN Q x) (hS2 : DD Q x ^ 2 * S ^ 2 = S2N Q x)
    (h1 : (2 * pN Q x ^ 2 + DD Q x ^ 2) * T + (4 * pN Q x * DD Q x + DD Q x ^ 2 * C) * S = 8 * x ^ 2 * k)
    (h2 : 4 * x ^ 3 * CdN Q x + 3 * pN Q x * DD Q x ^ 3 * S * T
      + DD Q x ^ 2 * S ^ 2 * (2 * pN Q x ^ 2 + 2 * DD Q x ^ 2 + pN Q x * DD Q x * C) = 0)
    (hexp : Real.exp T = C + S) :
    Transcendental ℚ μ := by
  have hQpos : 0 < Q := by
    rcases lt_or_ge 0 Q with h | h
    · exact h
    · nlinarith
  have hD : 0 < DD Q x := by unfold DD; positivity
  have hL : Lm Q x = 24 * x ^ 2 * k * pN Q x * DD Q x ^ 3 * S := by
    unfold Lm Dl
    linear_combination (3 * pN Q x * DD Q x ^ 3 * S) * h1 - (2 * pN Q x ^ 2 + DD Q x ^ 2) * h2
      + (-3 * pN Q x * DD Q x ^ 2 * S2N Q x + (2 * pN Q x ^ 2 + DD Q x ^ 2) * pN Q x * S2N Q x) * hC
      + (-3 * pN Q x * DD Q x ^ 2 * (4 * pN Q x + DD Q x * C)
        + (2 * pN Q x ^ 2 + DD Q x ^ 2) * (2 * pN Q x ^ 2 + 2 * DD Q x ^ 2 + pN Q x * DD Q x * C)) * hS2
  have hG : G5 kap Q x = 0 := by
    unfold G5; rw [← hk]
    linear_combination 5 * (Lm Q x + 24 * x ^ 2 * k * pN Q x * DD Q x ^ 3 * S) * hL
      + 2880 * x ^ 4 * k ^ 2 * pN Q x ^ 2 * DD Q x ^ 4 * hS2
  have hqa : IsAlgebraic ℚ μ → IsAlgebraic ℚ Q := fun hμa => by
    have hkne : kap ≠ 0 := hk0.ne'
    have : Q = μ * kap⁻¹ := by field_simp; linarith
    rw [this]; exact hμa.mul hkap.inv
  refine Recipe.transcendental_of_recipe' HL (z := x) (T := T) (c1 := 3 * pN Q x * DD Q x ^ 3 * S)
    (c0 := -(4 * x ^ 3 * CdN Q x + DD Q x ^ 2 * S ^ 2 * (2 * pN Q x ^ 2 + 2 * DD Q x ^ 2 + pN Q x * DD Q x * C)))
    hT.ne' (by linear_combination h2) (by have := hD.ne'; have := hS.ne'; simp_all) (fun hμa => ?_) (fun hμa hxQ => ?_)
  · -- ELIMINATE: x is a root of G5(kap, Q, X); G5 at X = 1 is 320 (...)^2 (1+Q)^2 > 0
    let P : (algebraicClosure ℚ ℝ)[X] := G5 (Polynomial.C (Recipe.toK hkap)) (Polynomial.C (Recipe.toK (hqa hμa))) X
    have hev : ∀ y : ℝ, aeval y P = G5 kap Q y := by
      intro y
      rw [show aeval y P = (aeval y : (algebraicClosure ℚ ℝ)[X] →ₐ[_] ℝ).toRingHom P from rfl, map_G5]
      simp; rfl
    refine ⟨P, fun h0 => ?_, by rw [hev]; exact hG⟩
    have := hev 1
    rw [h0, map_zero, G5_one] at this
    have : 0 < 320 * (2 * (1 - Q) ^ 2 + (1 + Q) ^ 2) ^ 2 * (1 + Q) ^ 2 := by positivity
    linarith
  · -- DESCEND
    let K := algebraicClosure ℚ ℝ
    have hK : ∀ y : K, IsAlgebraic ℚ (y : ℝ) := fun y => mem_algebraicClosure_iff.1 y.2
    have hQA := hqa hμa
    let qK := Recipe.toK hQA
    let xK := Recipe.toK hxQ
    have alg_of : ∀ (e : K) (r : ℝ), (algebraMap K ℝ e = r) → IsAlgebraic ℚ r := fun e r h => h ▸ hK e
    have hDa : IsAlgebraic ℚ (DD Q x) := alg_of (DD qK xK) _ (by rw [map_DD]; rfl)
    have hCa : IsAlgebraic ℚ C := by
      have : C = CN Q x * (DD Q x)⁻¹ := by field_simp; linear_combination hC
      rw [this]; exact (alg_of (CN qK xK) _ (by rw [map_CN]; rfl)).mul hDa.inv
    have hS2a : IsAlgebraic ℚ (S ^ 2) := by
      have : S ^ 2 = S2N Q x * (DD Q x ^ 2)⁻¹ := by field_simp; linear_combination hS2
      rw [this]; exact (alg_of (S2N qK xK) _ (by rw [map_S2N]; rfl)).mul (hDa.pow 2).inv
    have hSa : IsAlgebraic ℚ S := IsAlgebraic.of_pow (by norm_num) hS2a
    let sK := Recipe.toK hSa
    let cK := Recipe.toK hCa
    refine ⟨alg_of (3 * pN qK xK * DD qK xK ^ 3 * sK) _ (by rw [map_c1]; rfl),
      alg_of (-(4 * xK ^ 3 * CdN qK xK + DD qK xK ^ 2 * sK ^ 2 * (2 * pN qK xK ^ 2 + 2 * DD qK xK ^ 2
        + pN qK xK * DD qK xK * cK))) _ (by rw [map_c0]; rfl), by rw [hexp]; exact hCa.add hSa⟩

end PFive
