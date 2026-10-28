import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.GlobalFrames
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.AdelicCharacter
import OAI.RepresentationTheory.Theta.Adelic.Characters

/-! # Characters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Characters.CM

noncomputable section

/-! Construct the source's full global splitting characters, including
their actual quadratic norm restrictions. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)

theorem exists_characters :
    ∃ C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) 3 1,
      C.ψ = HeckeCycles.NumberField.AdelicCharacter.CM.character (QuadraticConjugation.CM.Field.RealField E) ∧
      RepresentationTheory.Theta.Adelic.Data.CharacterConclusion (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) 3 1 C :=
  RepresentationTheory.Theta.Adelic.Characters.complete_character_conclusion
    (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (QuadraticConjugation.CM.Field.discriminant_ne_zero E Q) (QuadraticConjugation.CM.Field.discriminant_not_square E Q) 3 1
    (HeckeCycles.NumberField.AdelicCharacter.CM.character (QuadraticConjugation.CM.Field.RealField E))
    (HeckeCycles.NumberField.AdelicCharacter.CM.character_continuous (QuadraticConjugation.CM.Field.RealField E))
    (HeckeCycles.NumberField.AdelicCharacter.CM.character_unitary (QuadraticConjugation.CM.Field.RealField E))
    (HeckeCycles.NumberField.AdelicCharacter.CM.character_nontrivial (QuadraticConjugation.CM.Field.RealField E))
    (HeckeCycles.NumberField.AdelicCharacter.CM.character_rational (QuadraticConjugation.CM.Field.RealField E))

def characters : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) 3 1 :=
  (exists_characters E Q).choose

theorem character_eq : (characters E Q).ψ = HeckeCycles.NumberField.AdelicCharacter.CM.character (QuadraticConjugation.CM.Field.RealField E) :=
  (exists_characters E Q).choose_spec.1

theorem character_conclusion :
    RepresentationTheory.Theta.Adelic.Data.CharacterConclusion (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) 3 1 (characters E Q) :=
  (exists_characters E Q).choose_spec.2

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Characters.CM
