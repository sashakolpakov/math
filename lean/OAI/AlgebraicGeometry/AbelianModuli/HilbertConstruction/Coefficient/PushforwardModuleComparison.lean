import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

/-! # Pushforward Module Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardModuleComparison

noncomputable section

/-! Pushed-forward module sections identify with the module sections on inverse-image opens, preserving their structural coefficient action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : Y.Modules)

def inverseImageCoefficientModulePresheaf : TopCat.Presheaf (ModuleCat.{u} R) X :=
  (TopologicalSpace.Opens.map a.base).op ⋙ ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp f) M

def coefficientPushforwardModuleComponent (U : X.Opens) :
    (ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj M)).obj (.op U) ≃ₗ[R]
      (inverseImageCoefficientModulePresheaf a f M).obj (.op U) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change Γ(M, a ⁻¹ᵁ U) at x
    change a.app U (X.presheaf.map U.leTop.op (f r)) • x =
      Y.presheaf.map (a ⁻¹ᵁ U).leTop.op (a.appTop (f r)) • x
    exact congrArg (fun z : Γ(Y, a ⁻¹ᵁ U) => z • x) (Global.ScalarBaseChange.globalFunction_pullback_restrict a (f r) U).symm

def coefficientPushforwardModuleIso :
    ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj M) ≅
      inverseImageCoefficientModulePresheaf a f M :=
  NatIso.ofComponents (fun U => (coefficientPushforwardModuleComponent a f M U.unop).toModuleIso) (by
    intro U V h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardModuleComparison
