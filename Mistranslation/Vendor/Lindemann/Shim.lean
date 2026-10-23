-- VENDORED (2026-10-23) from upstream leanprover-community/mathlib4 master, Mathlib/Algebra/MonoidAlgebra/Basic.lean,
-- section comapDomAlgAut (Apache 2.0, Mathlib contributors). Present in upstream Mathlib, newer than our pinned version;
-- needed by the Lindemann-Weierstrass algebraic part. Copied verbatim except for the surrounding namespace/imports.
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finsupp.Quotient
import Mathlib.Data.Set.Finite.Lattice

noncomputable section

namespace AddMonoidAlgebra

open scoped AddMonoidAlgebra

variable {R M : Type*}

section comapDomAlgAut

variable {G : Type*} [Group G] [AddMonoid M] [DistribMulAction G M] [CommSemiring R]

variable (R M G) in
/-- An action of `G` on `M` by additive automorphisms induces an action of `G` on `R[M]`
by `R`-algebra automorphisms, through the exponents. -/
def comapDomAlgAut : G →* R[M] ≃ₐ[R] R[M] :=
  (AddMonoidHom.toMultiplicative (domCongrAut R R (M := M))).comp (DistribMulAction.toAddAut G M)

theorem comapDomAlgAut_apply (g : G) :
    comapDomAlgAut R M G g = domCongr R R (DistribMulAction.toAddEquiv M g) :=
  rfl

/-- The action of `G` on `R[M]` through the exponents, `(g • x).coeff m = x.coeff (g⁻¹ • m)`. -/
@[instance_reducible]
def comapMulSemiringAction : MulSemiringAction G R[M] :=
  .compHom _ (comapDomAlgAut R M G)

attribute [local instance] comapMulSemiringAction

theorem comapSMul_def (g : G) (x : R[M]) : g • x = comapDomAlgAut R M G g x :=
  rfl

@[simp]
theorem coeff_comapSMul (g : G) (x : R[M]) (m : M) : (g • x).coeff m = x.coeff (g⁻¹ • m) := by
  simp [comapSMul_def, comapDomAlgAut_apply]

@[simp]
theorem comapSMul_single (g : G) (m : M) (r : R) : g • single m r = single (g • m) r := by
  simp [comapSMul_def, comapDomAlgAut_apply]

theorem comapSMulCommClass : SMulCommClass G R R[M] where
  smul_comm g r x := by simp [comapSMul_def]

end comapDomAlgAut

end AddMonoidAlgebra
end

-- VENDORED (2026-10-23) from upstream Mathlib/Data/Finsupp/Quotient.lean (Apache 2.0, Mathlib contributors), verbatim.
section liftFinsupp
open Finsupp
variable {α β : Type*}
namespace Setoid

variable (s : Setoid α) [Zero β]

/-- Finitely supported functions on `α` that are constant on the classes of `s` correspond to
finitely supported functions on `Quotient s`, provided the classes are finite. -/
noncomputable def liftFinsuppEquiv (hs : ∀ a, {b | s b a}.Finite) :
    {f : α →₀ β // ∀ a b, s a b → f a = f b} ≃ (Quotient s →₀ β) where
  toFun f := Quotient.liftFinsupp f.1 f.2
  invFun f := ⟨Finsupp.ofSupportFinite (f ∘ Quotient.mk s) <| by
    rw [Function.support_comp_eq_preimage]
    refine f.hasFiniteSupport.preimage' fun q _ ↦ ?_
    induction q using Quotient.inductionOn with | h a => ?_
    convert hs a using 1
    ext b
    simp [Quotient.eq], fun a b h ↦ by simp [Quotient.sound h]⟩
  left_inv _ := Subtype.ext <| Finsupp.ext fun _ ↦ rfl
  right_inv f := Finsupp.ext fun q ↦ Quotient.inductionOn q fun _ ↦ rfl

variable {s}

@[simp]
theorem liftFinsuppEquiv_apply_mk (hs : ∀ a, {b | s b a}.Finite)
    (f : {f : α →₀ β // ∀ a b, s a b → f a = f b}) (a : α) :
    liftFinsuppEquiv s hs f ⟦a⟧ = f.1 a :=
  rfl

@[simp]
theorem liftFinsuppEquiv_symm_apply (hs : ∀ a, {b | s b a}.Finite) (f : Quotient s →₀ β) (a : α) :
    ((liftFinsuppEquiv s hs).symm f).val a = f ⟦a⟧ :=
  rfl

end Setoid
end liftFinsupp
