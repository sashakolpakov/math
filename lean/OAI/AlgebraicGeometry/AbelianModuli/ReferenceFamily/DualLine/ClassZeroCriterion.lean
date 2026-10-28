import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ReductionFrameIndependence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.TensorAdditivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.DeformationTriviality

/-! # Class Zero Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassZeroCriterion

noncomputable section

/-! The intrinsic algebraic deformation class vanishes exactly for
actually trivial line sheaves on the dual-number family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]

theorem dualLineDeformationClass_unit :
    DeformationClass.dualLineDeformationClass X (HilbertConstruction.Line.Bundles.LineBundle.trivial (LieRanks.dualNumberTest ℂ ⊗ X).left)
      (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left) = 0 := by
  let L := HilbertConstruction.Line.Bundles.LineBundle.trivial (LieRanks.dualNumberTest ℂ ⊗ X).left
  let e := ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left
  have ht := TensorAdditivity.dualLineDeformationClass_tensor X L L e e
  have hi := ReductionFrameIndependence.dualLineDeformationClass_of_iso X L (L.tensor L) e (NormalizedDual.TensorFrames.dualTensorReductionFrame X L L e e)
    (HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso L.sheaf)
  exact add_left_cancel (ht.symm.trans (hi.trans (add_zero (DeformationClass.dualLineDeformationClass X L e)).symm))

theorem dualLineDeformationClass_trivial
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    (hL : Nonempty (L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule (LieRanks.dualNumberTest ℂ ⊗ X).left)) :
    DeformationClass.dualLineDeformationClass X L e = 0 := by
  obtain ⟨q⟩ := hL
  exact (ReductionFrameIndependence.dualLineDeformationClass_of_iso X (HilbertConstruction.Line.Bundles.LineBundle.trivial (LieRanks.dualNumberTest ℂ ⊗ X).left) L
    (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left) e q).trans (dualLineDeformationClass_unit X)

theorem dualLineDeformationClass_zero_iff
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left) :
    DeformationClass.dualLineDeformationClass X L e = 0 ↔ Nonempty (L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule (LieRanks.dualNumberTest ℂ ⊗ X).left) :=
  ⟨DeformationTriviality.dualLineDeformationClass_zero_trivial X L e, dualLineDeformationClass_trivial X L e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassZeroCriterion
