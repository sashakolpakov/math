import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FunctionCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitaryHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.FieldAction

/-! # Function Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FunctionCovariance.CM

noncomputable section

/-! Actual global Heisenberg covariance of the source's constructed
finite Schwartz representation, with its actual symplectic projection. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem covariance (g : SourceFinite.Product.CM.FiniteGroup E C)
    (z : (Fin 3 ⊕ Fin 3) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (QuadraticConjugation.CM.Field.RealField E))
    (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions (QuadraticConjugation.CM.Field.RealField E) 3) :
    TraceAction.CM.functionAction E C g
      (Finite.TraceHeisenberg.CM.operator (QuadraticConjugation.CM.Field.RealField E) 3 (fun i => z (.inr i)) (fun i => z (.inl i)) φ) =
      Finite.TraceHeisenberg.CM.operator (QuadraticConjugation.CM.Field.RealField E) 3
        (fun i => ((SourceFinite.FieldAction.CM.assembled E C g).val *ᵥ z) (.inr i))
        (fun i => ((SourceFinite.FieldAction.CM.assembled E C g).val *ᵥ z) (.inl i))
        (TraceAction.CM.functionAction E C g φ) :=
  HeckeCycles.NumberField.FunctionCovariance.CM.covariance (QuadraticConjugation.CM.Field.RealField E) 3
    (Characters.CM.characters E C).ψ (Characters.CM.characters E C).ψ_unitary
    (Characters.CM.characters E C).ψ_continuous (Characters.CM.character_eq E C)
    (SourceFinite.Product.CM.levels E C)
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUAction (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C) (QuadraticForms.CM.skewForm E C) (QuadraticConjugation.CM.Field.discriminant_ne_zero E C)
      (Characters.CM.characters E C) (GlobalFrames.CM.frames E C)
      (NormalizedSplittings.CM.splittings E C))
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUAction_unramified (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C) (QuadraticForms.CM.skewForm E C) (QuadraticConjugation.CM.Field.discriminant_ne_zero E C)
      (Characters.CM.characters E C) (GlobalFrames.CM.frames E C)
      (NormalizedSplittings.CM.splittings E C))
    g z ((SourceFinite.FieldAction.CM.assembled E C g).val *ᵥ z)
    (Finite.UnitaryHeisenberg.CM.local_covariance (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) 3 1
      (QuadraticForms.CM.hermitianForm E C) (QuadraticForms.CM.skewForm E C) (QuadraticConjugation.CM.Field.discriminant_ne_zero E C)
      (Characters.CM.characters E C) (GlobalFrames.CM.frames E C)
      (NormalizedSplittings.CM.splittings E C) g z) φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FunctionCovariance.CM
