import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FunctionAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SurjectiveRepresentationSmoothness
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormalizedSplittings
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceTests
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Topology
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant

/-! # Trace Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceAction.CM

noncomputable section

/-! The actual source finite unitary group acts smoothly on the genuine
PoissonAutomorphy Schwartz functions in trace polarization. The action is derived from
the normalized local splittings and the proved evaluation quotient. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)

def tensorAction : SourceFinite.Product.CM.FiniteGroup E Q →*
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (QuadraticConjugation.CM.Field.RealField E) 3 ≃ₗ[ℂ]
      RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (QuadraticConjugation.CM.Field.RealField E) 3) :=
  RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) (QuadraticForms.CM.skewForm E Q) (QuadraticConjugation.CM.Field.discriminant_ne_zero E Q)
    (Characters.CM.characters E Q) (GlobalFrames.CM.frames E Q)
    (NormalizedSplittings.CM.splittings E Q)

def functionAction : SourceFinite.Product.CM.FiniteGroup E Q →*
    (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions (QuadraticConjugation.CM.Field.RealField E) 3 ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions (QuadraticConjugation.CM.Field.RealField E) 3) :=
  Finite.FunctionAction.CM.functionAction (QuadraticConjugation.CM.Field.RealField E) 3 (SourceFinite.Product.CM.levels E Q)
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUAction (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) (QuadraticForms.CM.skewForm E Q) (QuadraticConjugation.CM.Field.discriminant_ne_zero E Q)
      (Characters.CM.characters E Q) (GlobalFrames.CM.frames E Q)
      (NormalizedSplittings.CM.splittings E Q))
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUAction_unramified (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) (QuadraticForms.CM.skewForm E Q) (QuadraticConjugation.CM.Field.discriminant_ne_zero E Q)
      (Characters.CM.characters E Q) (GlobalFrames.CM.frames E Q)
      (NormalizedSplittings.CM.splittings E Q))

theorem evaluation_intertwines (g : SourceFinite.Product.CM.FiniteGroup E Q)
    (φ : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (QuadraticConjugation.CM.Field.RealField E) 3) :
    functionAction E Q g (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz (QuadraticConjugation.CM.Field.RealField E) 3 φ) =
      RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz (QuadraticConjugation.CM.Field.RealField E) 3 (tensorAction E Q g φ) :=
  Finite.FunctionAction.CM.intertwines (QuadraticConjugation.CM.Field.RealField E) 3 _ _ _ g φ

theorem function_smooth (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions (QuadraticConjugation.CM.Field.RealField E) 3) :
    IsOpen {g : SourceFinite.Product.CM.FiniteGroup E Q | functionAction E Q g φ = φ} :=
  SurjectiveRepresentationSmoothness.CM.smooth
    (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz (QuadraticConjugation.CM.Field.RealField E) 3)
    (Finite.TensorRepresentatives.CM.sectionMap (QuadraticConjugation.CM.Field.RealField E) 3)
    (Finite.FunctionAction.CM.section_identity (QuadraticConjugation.CM.Field.RealField E) 3)
    (tensorAction E Q) _ (NormalizedSplittings.CM.finite_conclusion E Q).1 φ

def traceAction : SourceFinite.Product.CM.FiniteGroup E Q →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ]
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :=
  (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut (TraceTests.CM.equivalence E Q).symm).comp
    (functionAction E Q)

theorem traceAction_intertwines (g : SourceFinite.Product.CM.FiniteGroup E Q)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    TraceTests.CM.equivalence E Q (traceAction E Q g φ) =
      functionAction E Q g (TraceTests.CM.equivalence E Q φ) :=
  (TraceTests.CM.equivalence E Q).apply_symm_apply _

theorem trace_smooth (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    IsOpen {g : SourceFinite.Product.CM.FiniteGroup E Q | traceAction E Q g φ = φ} :=
  SurjectiveRepresentationSmoothness.CM.conjugate_smooth
    (TraceTests.CM.equivalence E Q) (functionAction E Q) (function_smooth E Q) φ

variable {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

def productAction : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × SourceFinite.Product.CM.Away E Q f →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ]
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :=
  (traceAction E Q).comp (SourceFinite.Product.CM.equivalence E Q f).toMonoidHom

theorem product_smooth (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    IsOpen {g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × SourceFinite.Product.CM.Away E Q f |
      productAction E Q f g φ = φ} :=
  (trace_smooth E Q φ).preimage (SourceFinite.Topology.CM.equivalence_continuous E Q f)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceAction.CM
