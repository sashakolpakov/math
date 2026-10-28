import OAI.AlgebraicGeometry.Picard.ThetaConstruction.AmpleComplexDifferenceSurjectivity
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceBaseChangeValues
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.HomogeneousBaseChangeForgetting
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation

/-! # Reference Complex Ample Difference -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceComplexAmpleDifference.Geometric

noncomputable section

/-! Surjectivity of translation by an ample line, for the original
complex abelian scheme and the original relative Picard values. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (hL : L.IsAmple)

include hL

theorem original_ampleDifference_complex_surjective
    (q : A.homogeneousPicardSheaf.obj.obj (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))) :
    ∃ a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme,
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle A L) a =
        A.homogeneousPicardSheafInclusion.hom.app (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) q := by
  let P := AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation (hL.projectivePresentation A.scheme.hom)
  let B := AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P
  exact AmpleComplexDifferenceSurjectivity.Geometric.ampleDifference_complex_surjective B L hL q

theorem original_ampleDifference_realizes_homogeneous_line
    (M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (hM : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    ∃ a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme,
      (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback (snd (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) A.scheme).left)) := by
  let U := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
  let r : A.homogeneousPicardPresheaf.obj (.op U) :=
    ⟨AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M), hM⟩
  let q := (toSheafify (Scheme.fppfTopology.over Foundations.Scheme.ProjectiveSpace.complexBase) A.homogeneousPicardPresheaf).app (.op U) r
  obtain ⟨a, ha⟩ := original_ampleDifference_complex_surjective A L hL q
  exact ⟨a, (DifferenceBaseChangeValues.Geometric.relativeDifference_value_native A L a).trans (ha.trans (HomogeneousBaseChangeForgetting.Geometric.homogeneousForget_toSheafify A U r))⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceComplexAmpleDifference.Geometric
