import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars

/-! # Section Linear Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.SectionLinearCoordinates

noncomputable section

/-! Global-section coordinates preserve addition and the actual
action of regular functions on a module sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars

universe u
variable {X : Scheme.{u}} (M : X.Modules)

theorem moduleSectionHomEquiv_add (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) :
    AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M (s + t) = AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s + AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M t := rfl

theorem moduleSectionHomEquiv_scalar (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (r : Γ(X, ⊤)) :
    AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M (s ≫ AbelianModuli.HilbertConstruction.Global.ModuleScalars.globalModuleScalar M r) = r • AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s := by
  change X.presheaf.map (𝟙 (.op (⊤ : X.Opens))) r • s.app ⊤ (1 : Γ(X, ⊤)) =
    r • s.app ⊤ (1 : Γ(X, ⊤))
  rw [X.presheaf.map_id]
  rfl

theorem moduleSectionHomEquiv_symm_add (s t : Γ(M, ⊤)) :
    (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm (s + t) = (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm s + (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm t := by
  apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).injective
  rw [Equiv.apply_symm_apply, moduleSectionHomEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem moduleSectionHomEquiv_symm_smul (s : Γ(M, ⊤)) (r : Γ(X, ⊤)) :
    (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm (r • s) = (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm s ≫ AbelianModuli.HilbertConstruction.Global.ModuleScalars.globalModuleScalar M r := by
  apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).injective
  rw [Equiv.apply_symm_apply, moduleSectionHomEquiv_scalar, Equiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.SectionLinearCoordinates
