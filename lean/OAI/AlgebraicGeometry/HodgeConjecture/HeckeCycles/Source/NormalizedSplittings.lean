import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Characters
import OAI.RepresentationTheory.Theta.Adelic.ConstructNormalizedSplittings
import OAI.RepresentationTheory.Theta.Adelic.CongruenceLevel
import OAI.RepresentationTheory.Weil.AdelicSplitting.No

/-! # Normalized Splittings -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormalizedSplittings.CM

noncomputable section

/-! Actual normalized local unitary splittings for the source, with their
adelic/rational compatibility and smooth finite action. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)

theorem exists_splittings : Nonempty
    (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) 3 1
      (QuadraticForms.CM.hermitianForm E Q) (QuadraticForms.CM.skewForm E Q) (QuadraticConjugation.CM.Field.discriminant_ne_zero E Q)
      (Characters.CM.characters E Q) (GlobalFrames.CM.frames E Q)) :=
  RepresentationTheory.Theta.Adelic.ConstructNormalizedSplittings.exists_normalized_local_splittings
    (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (QuadraticConjugation.CM.Field.discriminant_ne_zero E Q) (QuadraticConjugation.CM.Field.discriminant_not_square E Q) 3 1
    (by norm_num) (QuadraticForms.CM.hermitianForm E Q) (QuadraticForms.CM.skewForm E Q)
    (QuadraticForms.CM.hermitianForm_hermitian E Q) (QuadraticForms.CM.skewForm_skewHermitian E Q)
    (Characters.CM.characters E Q) (GlobalFrames.CM.frames E Q)

def splittings : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) 3 1
    (QuadraticForms.CM.hermitianForm E Q) (QuadraticForms.CM.skewForm E Q) (QuadraticConjugation.CM.Field.discriminant_ne_zero E Q)
    (Characters.CM.characters E Q) (GlobalFrames.CM.frames E Q) :=
  Classical.choice (exists_splittings E Q)

theorem adelic_conclusion :
    RepresentationTheory.Theta.Adelic.Data.AdelicConclusion (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) 3 1
      (QuadraticForms.CM.hermitianForm E Q) (QuadraticForms.CM.skewForm E Q) (QuadraticConjugation.CM.Field.discriminant_ne_zero E Q)
      (Characters.CM.characters E Q) (GlobalFrames.CM.frames E Q) (splittings E Q) :=
  RepresentationTheory.Weil.AdelicSplitting.No.adelic_unitary_splitting_compatible_with_rational_points
    (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) ⟨QuadraticConjugation.CM.Field.discriminant_ne_zero E Q, QuadraticConjugation.CM.Field.discriminant_not_square E Q⟩ 3 1
    (QuadraticForms.CM.hermitianForm E Q) (QuadraticForms.CM.skewForm E Q) (QuadraticForms.CM.hermitianForm_hermitian E Q) (QuadraticForms.CM.skewForm_skewHermitian E Q)
    (Characters.CM.characters E Q) (GlobalFrames.CM.frames E Q) (splittings E Q)

theorem finite_conclusion :
    RepresentationTheory.Theta.Adelic.Data.FiniteConclusion (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) 3 1
      (QuadraticForms.CM.hermitianForm E Q) (QuadraticForms.CM.skewForm E Q) (QuadraticConjugation.CM.Field.discriminant_ne_zero E Q)
      (Characters.CM.characters E Q) (GlobalFrames.CM.frames E Q) (splittings E Q) := by
  exact ⟨RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction_smooth
    (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) (QuadraticForms.CM.skewForm E Q) (QuadraticConjugation.CM.Field.discriminant_ne_zero E Q)
    (Characters.CM.characters E Q) (GlobalFrames.CM.frames E Q) (splittings E Q) (by norm_num),
    RepresentationTheory.Theta.Adelic.CongruenceLevel.finite_family_congruence_level
    (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (QuadraticConjugation.CM.Field.discriminant_ne_zero E Q) 3 1 (by norm_num)
    (QuadraticForms.CM.hermitianForm E Q) (QuadraticForms.CM.skewForm E Q) (Characters.CM.characters E Q)
    (GlobalFrames.CM.frames E Q) (splittings E Q)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormalizedSplittings.CM
