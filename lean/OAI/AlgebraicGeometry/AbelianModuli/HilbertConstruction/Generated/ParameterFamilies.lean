import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterClosedFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Families
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.RankTests

/-! # Parameter Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterFamilies

noncomputable section

/-! A parameter map produces an actual relative projective Hilbert family on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} {n B N : ℕ} {P : Polynomial ℚ}
variable (g : T ⟶ (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N).left)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : RankTests.GeneratedHilbertRankTest n P N)

def generatedParameterHilbertFamily : RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P where
  family := ParameterClosedFamilies.generatedParameterClosedFamily g hflat
  fieldHilbert K _ x := by
    let D := Truncated.AffineUniversalData.truncatedAffineUniversalData
      ((x ≫ g) ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N).left)
    have hi : ((ParameterClosedFamilies.generatedParameterClosedFamily g hflat).affineProjectivePullback x).homogeneousIdeal =
        HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation D.generatedIdeal :=
      congrArg HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf ((ParameterClosedFamilies.generatedParameterIdealData g).glue_comap x)
    rw [hi]
    apply (HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff D.generatedIdeal P).mpr
    exact (D.generated_hilbertPolynomial_finite_test N ((Nat.le_add_right N _).trans hflat)
      (Truncated.GeneratedFamily.truncatedGeneratedAffineData_condition (x ≫ g)) htest P).mpr
        ⟨hr.1, RankTests.generatedHilbertRanks_finite_test hr⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterFamilies
