import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSections

/-! # Multiplication Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MultiplicationProduct

noncomputable section

/-! Applying section multiplication to a section is its actual tensor product. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

theorem section_comp_moduleSectionMultiply (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (t : Line.Bundles.structureModule X ⟶ M) :
    t ≫ Module.SectionMultiplication.moduleSectionMultiply L M s = Tensor.ProductSections.tensorProductSection s t := by
  rw [Module.SectionMultiplication.moduleSectionMultiply, ← Category.assoc, Tensor.UnitLeftNaturality.tensorModuleUnitLeftIso_inv_natural,
    Category.assoc, Tensor.Bifunctor.tensorModuleMap_comp]
  simp only [Category.id_comp, Category.comp_id]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MultiplicationProduct
