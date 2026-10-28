import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.OpenPullbackValues
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Tensor Source -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.TensorSource

noncomputable section

/-! Restriction to an open subscheme gives the actual coefficient-linear equivalence on section values and hence on their scalar extensions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : Y ⟶ X) [IsOpenImmersion a] (f : R →+* Γ(X, ⊤)) (M : X.Modules)

theorem coefficientPullbackSectionValueMap_bijective_of_open (U : X.Opens) (hU : U ≤ a.opensRange) :
    Function.Bijective (Coefficient.PullbackSectionValues.coefficientPullbackSectionValueMap a f M U) :=
  (ConcreteCategory.isIso_iff_bijective (Coefficient.OpenPullbackValues.coefficientOpenPullbackValueIso a f M U hU).hom).mp inferInstance

def coefficientOpenPullbackSectionEquiv (U : X.Opens) (hU : U ≤ a.opensRange) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U) ≃ₗ[R]
      (Coefficient.ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp f) ((Scheme.Modules.pullback a).obj M)).obj (.op (a ⁻¹ᵁ U)) :=
  LinearEquiv.ofBijective (Coefficient.PullbackSectionValues.coefficientPullbackSectionValueMap a f M U)
    (coefficientPullbackSectionValueMap_bijective_of_open a f M U hU)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.TensorSource
