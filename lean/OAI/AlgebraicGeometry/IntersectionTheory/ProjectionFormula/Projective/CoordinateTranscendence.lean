import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LineParameter
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FormStalkComparison
import Mathlib.RingTheory.Algebraic.MvPolynomial

/-! # Coordinate Transcendence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.CoordinateTranscendence

noncomputable section

/-! A coordinate ratio on projective space is transcendental over
the coefficient field: its affine coordinate polynomial embeds into
the actual generic stalk. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LineParameter.RationalFractions

def chartMap (n : ℕ) (i : Fin (n + 1)) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
    Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i →ₐ[ℂ] (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).functionField := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
  exact (Stalk.ScalarMaps.germ (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) (LineParameter.RationalFractions.generic_coordinate n i)).comp
      (CoordinateAlgebra.algebraEquiv n i).toAlgHom

theorem chartMap_injective (n : ℕ) (i : Fin (n + 1)) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
    Function.Injective (chartMap n i) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  exact (germ_injective_of_isIntegral (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) (LineParameter.RationalFractions.generic_coordinate n i)).comp
      (CoordinateAlgebra.ringEquiv n i).injective

theorem chartMap_X (n : ℕ) (i j : Fin (n + 1)) (hji : j ≠ i) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
    chartMap n i (MvPolynomial.X ⟨j, hji⟩) = LineParameter.RationalFractions.ratio n j i := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  have he := congrArg ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.germ (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) (LineParameter.RationalFractions.generic_coordinate n i))
    (FormStalkComparison.chart_form n i (LineParameter.RationalFractions.coordinate n j))
  have hg := PointJets.StalkFractions.germ n (genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
    (LineParameter.RationalFractions.coordinate n j) (LineParameter.RationalFractions.coordinate n i) (LineParameter.RationalFractions.generic_coordinate n i)
  have hX : MvPolynomial.X ⟨j, hji⟩ =
      Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i (LineParameter.RationalFractions.coordinate n j).val :=
    (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_of_ne i j hji).symm
  exact (congrArg (chartMap n i) hX).trans (he.trans hg)

theorem transcendental (n : ℕ) (i j : Fin (n + 1)) (hji : j ≠ i) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
    Transcendental ℂ (LineParameter.RationalFractions.ratio n j i) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  rw [← chartMap_X n i j hji]
  intro h
  exact MvPolynomial.transcendental_X ℂ (⟨j, hji⟩ : {j : Fin (n + 1) // j ≠ i})
    ((isAlgebraic_algHom_iff (chartMap n i) (chartMap_injective n i)).mp h)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.CoordinateTranscendence
