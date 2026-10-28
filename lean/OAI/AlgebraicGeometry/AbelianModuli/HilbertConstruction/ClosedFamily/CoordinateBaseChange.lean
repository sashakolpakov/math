import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.HomogeneousCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SaturationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality

/-! # Coordinate Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical homogeneous coordinates of an actual coefficient pullback are the saturation of the extended coordinate ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A : CommRingCat.{u}} {n : ℕ}
variable (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)) (φ : R ⟶ A)

theorem Closed.Families.FlatClosedFamily.homogeneousIdeal_coefficientBaseChange :
    letI : Algebra R A := φ.hom.toAlgebra
    (F.pullbackAlong (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) (Spec.map φ)
      (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n)).homogeneousIdeal =
        HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) F.homogeneousIdeal) := by
  let : Algebra R A := φ.hom.toAlgebra
  have hF : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion F.homogeneousIdeal).ker = F.ideal :=
    HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf F.ideal
  have he : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) F.homogeneousIdeal)).ker =
      F.ideal.comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) :=
    (Projective.IdealBaseChange.projectiveQuotientIdeal_baseChange F.homogeneousIdeal).trans
      (congrArg (fun I => I.comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)) hF)
  exact congrArg HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf he.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
