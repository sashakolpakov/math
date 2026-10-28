import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.TensorSectionFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers

/-! # Section Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionNonvanishing

noncomputable section

/-! Multiplication by any regular function can only shrink the nonvanishing open of a line-bundle section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem scalarSection_nonvanishing {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (r : Γ(X, ⊤)) (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    Ample.LineBundles.sectionNonvanishing (SectionValues.scalarSection r s) =
      Ample.LineBundles.sectionNonvanishing ((Global.Sections.structureModuleEndRingEquiv X).symm r) ⊓ Ample.LineBundles.sectionNonvanishing s := by
  unfold SectionValues.scalarSection
  rw [← TensorSectionFormula.tensorProductSection_unitLeft_formula]
  exact (Ample.Powers.sectionNonvanishing_comp_iso _ (Tensor.ProductSheaf.tensorModuleUnitLeftIso L.sheaf)).trans
    (Tensor.SectionNonvanishing.sectionNonvanishing_tensorProduct (Line.Bundles.LineBundle.trivial X) L _ s)

theorem scalarSection_nonvanishing_le {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (r : Γ(X, ⊤)) (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    Ample.LineBundles.sectionNonvanishing (SectionValues.scalarSection r s) ≤ Ample.LineBundles.sectionNonvanishing s := by
  rw [scalarSection_nonvanishing]
  exact inf_le_right

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionNonvanishing
