import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.StructureModuleComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionModules
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

/-! # Pushforward Structure Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardStructureComparison

noncomputable section

/-! Coefficient sections of the pushed-forward structure module are the ordinary functions on inverse-image opens, with their correct coefficient action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R] (a : Y ⟶ X) (f : R →+* Γ(X, ⊤))

def coefficientPushforwardStructureComponent (U : X.Opens) :
    (ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj (Line.Bundles.structureModule Y))).obj (.op U) ≃ₗ[R]
      (Tensor.SectionModules.inverseImageSectionModules a f).obj (.op U) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change Γ(Y, a ⁻¹ᵁ U) at x
    change a.app U (X.presheaf.map U.leTop.op (f r)) * x =
      Y.presheaf.map (a ⁻¹ᵁ U).leTop.op (a.appTop (f r)) * x
    exact congrArg (fun z : Γ(Y, a ⁻¹ᵁ U) => z * x) (Global.ScalarBaseChange.globalFunction_pullback_restrict a (f r) U).symm

def coefficientPushforwardStructureIso :
    ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj (Line.Bundles.structureModule Y)) ≅
      Tensor.SectionModules.inverseImageSectionModules a f :=
  NatIso.ofComponents (fun U => (coefficientPushforwardStructureComponent a f U.unop).toModuleIso) (by
    intro U V h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardStructureComparison
