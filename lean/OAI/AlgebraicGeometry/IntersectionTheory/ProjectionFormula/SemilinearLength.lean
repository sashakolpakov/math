import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiltrationBaseLength

/-! # Semilinear Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilinearLength

noncomputable section

/-! Module length is invariant under a ring isomorphism and a
compatible semilinear module equivalence. In particular, the length
after base change does not depend on the chosen localization model. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

attribute [local instance] RingHomInvPair.of_ringEquiv

universe u

theorem length {R S : Type u} [CommRing R] [CommRing S] (σ : R ≃+* S)
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : M ≃ₛₗ[RingHomClass.toRingHom σ] N) :
    Module.length R M = Module.length S N := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

def tensorEquiv (e : S ≃ₐ[R] T) (M : ModuleCat.{u} R) :
    S ⊗[R] M ≃ₛₗ[RingHomClass.toRingHom e.toRingEquiv] T ⊗[R] M where
  toEquiv := (e.toLinearEquiv.rTensor M).toEquiv
  map_add' x y := (e.toLinearEquiv.rTensor M).map_add x y
  map_smul' a x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      change e (a * b) ⊗ₜ[R] m = e a • (e b ⊗ₜ[R] m)
      rw [map_mul, TensorProduct.smul_tmul']
      rfl
    | add x y hx hy =>
      change (e.toLinearEquiv.rTensor M) (a • (x + y)) =
        e a • ((e.toLinearEquiv.rTensor M) (x + y))
      simp only [smul_add, map_add]
      exact congrArg₂ (· + ·) hx hy

theorem baseChange_length (e : S ≃ₐ[R] T) (M : ModuleCat.{u} R) :
    FiltrationBaseLength.length R S M = FiltrationBaseLength.length R T M :=
  SemilinearLength.length e.toRingEquiv (tensorEquiv R S T e M)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilinearLength
