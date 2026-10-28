import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

/-! # Pushforward Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardSections

noncomputable section

/-! Sections of a direct image agree with source sections on inverse-image opens, including coefficient actions and restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (f : X ⟶ Y) (c : R →+* Γ(Y, ⊤)) (M : X.Modules)

def coefficientPushforwardSectionEquiv (U : Y.Opens) :
    (ModulePresheaf.coefficientModulePresheaf c ((Scheme.Modules.pushforward f).obj M)).obj (.op U) ≃ₗ[R]
      (ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp c) M).obj (.op (f ⁻¹ᵁ U)) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change (M.smul (f.app U (Y.presheaf.map U.leTop.op (c r)))).hom m =
      (M.smul (X.presheaf.map (f ⁻¹ᵁ U).leTop.op (f.appTop (c r)))).hom m
    exact congrArg (fun a : Γ(X, f ⁻¹ᵁ U) => (M.smul a).hom m)
      (Global.ScalarBaseChange.globalFunction_pullback_restrict f (c r) U).symm

theorem coefficientPushforwardSectionEquiv_naturality {U V : Y.Opens} (i : U ⟶ V) :
    (coefficientPushforwardSectionEquiv f c M U).toLinearMap.comp
      ((ModulePresheaf.coefficientModulePresheaf c ((Scheme.Modules.pushforward f).obj M)).map i.op).hom =
    ((ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp c) M).map
      ((TopologicalSpace.Opens.map f.base).map i).op).hom.comp
        (coefficientPushforwardSectionEquiv f c M V).toLinearMap := by
  ext m
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardSections
