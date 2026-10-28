import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.CoefficientNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionEvaluation

/-! # Reduction Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ReductionCoefficients

noncomputable section

/-! The first coordinate of the actual affine coefficient equivalence
is precisely pullback along the original reduction morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [IsReduced X.left]

theorem dualAffineSectionCoefficients_fst (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤)) :
    (SectionCoefficients.dualAffineSectionCoefficients X s).fst = (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.appTop s := by
  apply RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections.complexSectionValue_top_ext X
  intro p
  have h := congrArg TrivSqZeroExt.fst (SectionCoefficients.dualAffineSectionCoefficients_evaluation X p s)
  change (RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left s).fst =
    Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p (SectionCoefficients.dualAffineSectionCoefficients X s).fst at h
  rw [Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_eval, ← Complex.TopSectionValues.complexSectionValue_top_formula] at h
  exact h.symm.trans (Dual.ReductionEvaluation.dualReduction_sectionValue X p s)

theorem dualAffineUnit_normalized (u : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤)ˣ)
    (hu : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.appTop u.val = 1) :
    (Units.map (SectionCoefficients.dualAffineSectionCoefficients X).toMonoidHom u).val.fst = 1 :=
  (dualAffineSectionCoefficients_fst X u.val).trans hu

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ReductionCoefficients
