import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor

/-! # Global Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalSections

noncomputable section

/-! Actual global sections of the glued frame sheaf identify linearly with compatible coefficients on its open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

def openFrameGlobalSectionsRawEquiv :
    (Global.RingModulePresheaf.globalRingModulePresheaf (ModuleSheaf.openFrameModuleSheaf D)).obj (.op ⊤) ≃ₗ[Γ(X, ⊤)]
      SectionModules.openFrameSectionModule U D ⊤ where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    let z : SectionModules.openFrameSectionModule U D ⊤ := x
    change (X.presheaf.map (𝟙 (.op (⊤ : X.Opens))) r) • z = r • z
    exact congrArg (fun a : Γ(X, ⊤) => a • z) (ConcreteCategory.congr_hom
      (X.presheaf.map_id (.op (⊤ : X.Opens))) r)

def openFrameGlobalSectionsEquiv :
    (Global.RingModulePresheaf.globalRingModulePresheaf (ModuleSheaf.openFrameModuleSheaf D)).obj (.op ⊤) ≃ₗ[Γ(X, ⊤)]
      GlobalCompatibility.openFrameGlobalCompatibleModule D :=
  (openFrameGlobalSectionsRawEquiv D).trans (GlobalCompatibility.openFrameGlobalSectionEquiv D)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalSections
