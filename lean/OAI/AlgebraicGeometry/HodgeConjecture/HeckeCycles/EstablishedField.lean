import OAI.RepresentationTheory.Hecke.RadialDilation.Prerequisites
import OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicComposition
import OAI.AlgebraicGeometry.HodgeConjecture.Lefschetz
import OAI.NumberTheory.CMField.NormOneApproximation
import OAI.RepresentationTheory.Weil.Local.Formulas

/-! # Established Field -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedField.CM

noncomputable section

/-! Complete original LefschetzNormalization, NormOneApproximation and LocalWeil consumer inputs. The LefschetzNormalization
supplier retains its four original algebraicity-interface hypotheses;
its separate graph prerequisites are supplied by their actual native
proofs. NormOneApproximation retains every valuation and simultaneous congruence clause.
LocalWeil retains the generators, normalization and double-cover conclusion. -/

open scoped Classical

universe u

theorem active_embedding (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E] :
    RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LefschetzNormalization.Proposition E := by
  have hP := IntrinsicComposition.LefschetzNormalization.Geometry.of_ChernClass Lefschetz.Normalization.Geometry.lefschetzInput_proved
  exact LefschetzNormalization.normalization_of_active_embedding E
    GeometricNormalization.Lefschetz.Geometry.scalarTraceInput_proved hP.1 hP.2.1 hP.2.2

theorem norm_one_scalar : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.NormOneApproximation.Proposition := by
  intro E _ _ _ _ _ w wbar hconj hsplit
  exact NumberTheory.CMField.NormOneApproximation.Construction.exists_norm_one_scalar_unconditional w wbar hconj hsplit

theorem schrodinger_generators : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition :=
  RepresentationTheory.Weil.Local.Formulas.schrodinger_generator_formulas

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedField.CM
