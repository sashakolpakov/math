import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayTopology
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedAwayHomeomorph

/-! # Rational Away Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayCoordinates.CM

noncomputable section

/-! Recover the complete native away element continuously from the
remaining finite-place coordinates of the actual rational range. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayTopology.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

theorem native_recovery (g : FactorTheta.CM.RationalWeilFactorization.Away E L f) :
    RestrictedAwayHomeomorph.CM.insert
      (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (QadicPlace.CM.place E f) (RationalAwayTopology.CM.coordinates E L f g) = RationalAwayTopology.CM.nativeCoordinates E L f g :=
  RestrictedAwayHomeomorph.CM.insert_forget
    (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (QadicPlace.CM.place E f) (RationalAwayTopology.CM.nativeCoordinates E L f g)

theorem native_continuous : Continuous (RationalAwayTopology.CM.nativeCoordinates E L f) :=
  ((RestrictedAwayHomeomorph.CM.insert_continuous
    (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (QadicPlace.CM.place E f)).comp (RationalAwayTopology.CM.coordinates_continuous E L f)).congr
      (native_recovery E L f)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayCoordinates.CM
