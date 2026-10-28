import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FunctionUnitarity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TraceTestUnitarity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceAction

/-! # Function Unitarity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FunctionUnitarity.CM

noncomputable section

/-! The source's actual finite representations preserve the full Haar
pairing, both on number-field functions and on source-indexed rational tests. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (QuadraticConjugation.CM.Field.RealField E)) : MeasurableSpace (v.adicCompletion (QuadraticConjugation.CM.Field.RealField E)) := borel _
local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (QuadraticConjugation.CM.Field.RealField E)) : BorelSpace (v.adicCompletion (QuadraticConjugation.CM.Field.RealField E)) := ⟨rfl⟩

theorem function_unitary (g : SourceFinite.Product.CM.FiniteGroup E C)
    (f h : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions (QuadraticConjugation.CM.Field.RealField E) 3) :
    HeckeCycles.NumberField.FunctionUnitarity.CM.GlobalPairing.pairing (QuadraticConjugation.CM.Field.RealField E) 3
      (TraceAction.CM.functionAction E C g f) (TraceAction.CM.functionAction E C g h) =
      HeckeCycles.NumberField.FunctionUnitarity.CM.GlobalPairing.pairing (QuadraticConjugation.CM.Field.RealField E) 3 f h :=
  HeckeCycles.NumberField.FunctionUnitarity.CM.unitary (QuadraticConjugation.CM.Field.RealField E) 3 (SourceFinite.Product.CM.levels E C)
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUAction (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C) (QuadraticForms.CM.skewForm E C) (QuadraticConjugation.CM.Field.discriminant_ne_zero E C)
      (Characters.CM.characters E C) (GlobalFrames.CM.frames E C)
      (NormalizedSplittings.CM.splittings E C))
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUAction_unramified (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C) (QuadraticForms.CM.skewForm E C) (QuadraticConjugation.CM.Field.discriminant_ne_zero E C)
      (Characters.CM.characters E C) (GlobalFrames.CM.frames E C)
      (NormalizedSplittings.CM.splittings E C))
    (fun v u f h => HeckeCycles.NumberField.LocalPairing.CM.unitary (QuadraticConjugation.CM.Field.RealField E) 3 v
      (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter (QuadraticConjugation.CM.Field.RealField E) (Characters.CM.characters E C).ψ (.inr v))
      (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C) (QuadraticForms.CM.skewForm E C) (QuadraticConjugation.CM.Field.discriminant_ne_zero E C)
        (Characters.CM.characters E C) (GlobalFrames.CM.frames E C)
        (NormalizedSplittings.CM.splittings E C) (.inr v) u) f h) g f h

theorem trace_unitary (g : SourceFinite.Product.CM.FiniteGroup E C)
    (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    Finite.FiniteOscillator.CM.integralPairing (TraceAction.CM.traceAction E C g f)
      (TraceAction.CM.traceAction E C g h) = Finite.FiniteOscillator.CM.integralPairing f h :=
  TraceTestUnitarity.CM.unitary (QuadraticConjugation.CM.Field.RealField E) 3 (TraceFrame.CM.indexEquiv E C)
    (TraceAction.CM.traceAction E C g) (TraceAction.CM.functionAction E C g)
    (function_unitary E C g) (TraceAction.CM.traceAction_intertwines E C g) f h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FunctionUnitarity.CM
