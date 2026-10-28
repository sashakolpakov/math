import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceFrame
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TensorRepresentatives
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg

/-! # Trace Tests -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceTests.CM

noncomputable section

/-! Actual restricted tensor tests for every source-indexed finite test
in the constructed trace polarization, with exact values everywhere. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def equivalence : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions (QuadraticConjugation.CM.Field.RealField E) 3 :=
  (Finite.ReindexHeisenberg.CM.Pairing.testEquiv (TraceFrame.CM.indexEquiv E C)).trans
    (Finite.AdelicTestCoordinates.CM.equivalence (QuadraticConjugation.CM.Field.RealField E) 3)

def representative : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) →ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (QuadraticConjugation.CM.Field.RealField E) 3 :=
  (Finite.TensorRepresentatives.CM.sectionMap (QuadraticConjugation.CM.Field.RealField E) 3).comp
    (equivalence E C).toLinearMap

theorem representative_value (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (x : Fin 3 → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (QuadraticConjugation.CM.Field.RealField E)) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction (QuadraticConjugation.CM.Field.RealField E) 3 (representative E C φ) x =
      (equivalence E C φ).val x :=
  Finite.TensorRepresentatives.CM.section_value (QuadraticConjugation.CM.Field.RealField E) 3 _ x

theorem representative_rational_value (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (x : Fin 3 → QuadraticConjugation.CM.Field.RealField E) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction (QuadraticConjugation.CM.Field.RealField E) 3 (representative E C φ) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (fun i => CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates
        (QuadraticConjugation.CM.Field.RealField E) (Fin 3) x (TraceFrame.CM.indexEquiv E C i))) := by
  rw [representative_value]
  exact Finite.AdelicTestCoordinates.CM.rational_value (QuadraticConjugation.CM.Field.RealField E) 3 _ x

theorem representative_injective : Function.Injective (representative E C) := by
  intro φ ψ h
  apply (equivalence E C).injective
  apply Subtype.ext
  funext x
  exact (representative_value E C φ x).symm.trans
    ((congrArg (fun f => RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction (QuadraticConjugation.CM.Field.RealField E) 3 f x) h).trans
      (representative_value E C ψ x))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceTests.CM
