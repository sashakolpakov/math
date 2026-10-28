import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.CharacterNormalization
import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Ball Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallCharacter.CM

noncomputable section

/-! The source ball datum satisfies the full geometric AdelicTheta additive
character convention with its already constructed adelic character. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool} (L : GeometricSource.CM.LinePeriod E B places d)

theorem standard : RepresentationTheory.Theta.Adelic.DataTheta.Descent.StandardArchCharacter
    (A := BallArithmetic.CM.data E L) (HeckeCycles.NumberField.AdelicCharacter.CM.character (QuadraticConjugation.CM.Field.RealField E)) :=
  fun v t => Real.CharacterNormalization.CM.standard_real (QuadraticConjugation.CM.Field.RealField E)
    (ArchimedeanPlaces.CM.enumeration E places v) t

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallCharacter.CM
