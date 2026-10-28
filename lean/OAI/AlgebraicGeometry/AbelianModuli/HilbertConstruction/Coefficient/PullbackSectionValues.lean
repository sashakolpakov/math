import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardModuleComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionMap

/-! # Pullback Section Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionValues

noncomputable section

/-! Actual pullback of section values is linear over the original coefficient ring, with its target coefficient action transported to inverse-image opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : X.Modules)

def coefficientPullbackSectionValueMap (U : X.Opens) :
    (ModulePresheaf.coefficientModulePresheaf f M).obj (.op U) →ₗ[R]
      (ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp f) ((Scheme.Modules.pullback a).obj M)).obj (.op (a ⁻¹ᵁ U)) :=
  (PushforwardModuleComparison.coefficientPushforwardModuleComponent a f ((Scheme.Modules.pullback a).obj M) U).toLinearMap.comp
    ((PullbackSectionMap.coefficientPullbackSectionPresheafMap a f M).app (.op U)).hom

theorem coefficientPullbackSectionValueMap_apply (U : X.Opens)
    (x : (ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    coefficientPullbackSectionValueMap a f M U x =
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app U x := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionValues
