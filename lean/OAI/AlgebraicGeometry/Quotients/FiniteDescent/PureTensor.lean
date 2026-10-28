import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorProducts
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Pure Tensor -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PureTensor

noncomputable section

/-! Nonvanishing of canonical tensors passes from an iterated residue
extension to the scalar extension used by the geometric fiber. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

namespace Construction.PureTensorSurvival

variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]

theorem zero_comp (f : R →+* S) (g : S →+* A) (M : ModuleCat.{u} R) (m : M)
    (h : ((1 : S) ⊗ₜ[R,f] m : (ModuleCat.extendScalars f).obj M) = 0) :
    ((1 : A) ⊗ₜ[R,g.comp f] m : (ModuleCat.extendScalars (g.comp f)).obj M) = 0 := by
  let : Algebra S A := g.toAlgebra
  let e := (ModuleCat.extendScalarsComp f g).app M
  apply e.toLinearEquiv.injective
  rw [map_zero]
  change (ModuleCat.extendScalarsComp f g).hom.app M ((1 : A) ⊗ₜ[R,g.comp f] m) = 0
  rw [ModuleCat.extendScalarsComp_hom_app_one_tmul, h]
  exact TensorProduct.tmul_zero _ _

theorem nested_ne_zero [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    (M : Type u) [AddCommGroup M] [Module R M] (m : M)
    (h : (1 : A) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m) ≠ 0) : (1 : A) ⊗ₜ[R] m ≠ 0 := by
  intro hz
  apply h
  have he := congrArg (TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A M).symm hz
  simpa only [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, map_zero] using he

end Construction.PureTensorSurvival

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PureTensor
