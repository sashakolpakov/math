import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.UniversalBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.FamilyFunctoriality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ParameterEquivalence

/-! # Universal Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.UniversalBaseChange

noncomputable section

/-! The actual relative Hilbert families induced by parameter maps, including the universal family, commute with arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T U : Scheme.{u}} {n B N : ℕ} {P : Polynomial ℚ}
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N)

theorem generatedParameterHilbertFamily_comp
    (g : U ⟶ (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N).left) (f : T ⟶ U) :
    (Generated.ParameterFamilies.generatedParameterHilbertFamily g hflat htest hr).pullback f =
      Generated.ParameterFamilies.generatedParameterHilbertFamily (f ≫ g) hflat htest hr :=
  RelativeProjective.Families.RelativeProjectiveHilbertFamily.ext (Generated.FamilyFunctoriality.generatedParameterClosedFamily_comp g f hflat)

theorem generatedUniversalHilbertFamily_baseChange (f : T ⟶ S) (hN : N ≤ B) :
    (Generated.ParameterFamilies.generatedParameterHilbertFamily
      (𝟙 (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N).left) hflat htest hr).pullback
        (Generated.ParameterBaseMaps.generatedParameterBaseMap f n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N hN) =
    Generated.ParameterFamilies.generatedParameterHilbertFamily
      (𝟙 (Truncated.GeneratedParameters.truncatedGeneratedParameters T n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N).left) hflat htest hr :=
  RelativeProjective.Families.RelativeProjectiveHilbertFamily.ext (Generated.UniversalBaseChange.generatedUniversalClosedFamily_baseChange f hN hflat)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.UniversalBaseChange
