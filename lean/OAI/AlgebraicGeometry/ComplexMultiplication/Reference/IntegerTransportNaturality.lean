import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HomPullback

/-! # Integer Transport Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntegerTransportNaturality

noncomputable section

/-! # Naturality of the original integer source transport

The original extended integer complex and original single-complex source
commute under the genuine inverse-image transport, with their original maps.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint

variable {X Y : Over (Spec (.of ℂ))}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual inverse image preserves precisely the original map to the integer single object. -/
theorem originalIntegerComplexInverseImageIso_inv_comp (f : X ⟶ Y) :
    (AnalyticInverseImage.originalIntegerComplexInverseImageIso f).inv ≫
      ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle Y).hom =
      (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom ≫
        (HomPullback.originalIntegerSingleInverseImageIso f).inv := by
  rw [HomPullback.originalIntegerComplexInverseImageIso_factor]
  dsimp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  have hi := ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex
    (ComplexShape.up ℤ)).map_id
      (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
  rw [hi]
  simp only [Category.comp_id]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntegerTransportNaturality
