import OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedSectionCharts
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineOpenChartDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.PresentationDimension

/-! # Complex Presentation Dimension -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexPresentationDimension

noncomputable section

/-! The actual finite complex coordinates of any standard-smooth
affine open have the native scheme's intrinsic complex dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedSectionCharts.Abelian.RelativeCharts

theorem complexPresentation_dimension
    {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    (A : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (Q : ArithmeticGeometry.Descent.CMVariety.LocalizedSectionCharts.Abelian.RelativeCharts.ComplexPresentation A) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Module.finrank ℂ (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates Q.presentation.map → ℂ) =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
  calc
    Module.finrank ℂ (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates Q.presentation.map → ℂ) = Q.presentation.dimension :=
      Foundations.Scheme.PresentationDimension.Algebraic.finrank_free_variables_eq_dimension ℂ Q.presentation.toPreSubmersivePresentation
    _ = Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A :=
      Foundations.Scheme.SmoothDomainDimension.Algebraic.submersive_dimension_eq_rankAtStalk Q.presentation ⟨⊥, inferInstance⟩
    _ = Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom :=
      HodgeConjecture.DegreeTwo.AffineOpenChartDimension.Constructions.affineOpen_genericRank_eq_nativeDimension A i x

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexPresentationDimension
