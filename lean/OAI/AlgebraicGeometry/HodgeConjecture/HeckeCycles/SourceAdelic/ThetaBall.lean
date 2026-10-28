import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaBall
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallCharacter
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.GlobalFrames

/-! # Theta Ball -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaBall.CM

noncomputable section

/-! Apply the adelic theta input to the source forms, global frames,
ball arithmetic, and standard adelic character. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool} (L : GeometricSource.CM.LinePeriod E B places d)

theorem source_output (hAdelicTheta : Adelic.ThetaBall.CM.AdelicThetaInput)
    (inputs : RepresentationTheory.Theta.Adelic.Prerequisites.Inputs.{0, 0}) :
    Adelic.ThetaBall.CM.Output (Source.QuadraticConjugation.CM.Field.RealField E)
      (Source.QuadraticConjugation.CM.Field.discriminant E (OppositeCoordinates.CM.coordinates E L.coordinates)) 1
      (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (Source.QuadraticForms.CM.skewForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (Source.QuadraticConjugation.CM.Field.discriminant_ne_zero E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (HeckeCycles.NumberField.AdelicCharacter.CM.character (Source.QuadraticConjugation.CM.Field.RealField E))
      (Source.GlobalFrames.CM.frames E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (Source.BallArithmetic.CM.data E L) :=
  Adelic.ThetaBall.CM.of_full (Source.QuadraticConjugation.CM.Field.RealField E)
    (Source.QuadraticConjugation.CM.Field.discriminant E (OppositeCoordinates.CM.coordinates E L.coordinates)) 1
    (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.QuadraticForms.CM.skewForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.QuadraticConjugation.CM.Field.discriminant_ne_zero E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (HeckeCycles.NumberField.AdelicCharacter.CM.character (Source.QuadraticConjugation.CM.Field.RealField E))
    (Source.GlobalFrames.CM.frames E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.BallArithmetic.CM.data E L) hAdelicTheta inputs
    (Source.QuadraticConjugation.CM.Field.discriminant_not_square E (OppositeCoordinates.CM.coordinates E L.coordinates)) (Or.inl rfl)
    (Source.QuadraticForms.CM.hermitianForm_hermitian E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.QuadraticForms.CM.skewForm_skewHermitian E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (HeckeCycles.NumberField.AdelicCharacter.CM.character_continuous (Source.QuadraticConjugation.CM.Field.RealField E))
    (HeckeCycles.NumberField.AdelicCharacter.CM.character_unitary (Source.QuadraticConjugation.CM.Field.RealField E))
    (HeckeCycles.NumberField.AdelicCharacter.CM.character_nontrivial (Source.QuadraticConjugation.CM.Field.RealField E))
    (HeckeCycles.NumberField.AdelicCharacter.CM.character_rational (Source.QuadraticConjugation.CM.Field.RealField E)) (Source.BallCharacter.CM.standard E L)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaBall.CM
