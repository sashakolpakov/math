import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FunctionUnitarity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TraceTestHeisenberg

/-! # Trace Test Unitarity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TraceTestUnitarity.CM

noncomputable section

/-! Haar unitarity survives the actual integral-basis test comparison
and reindexing, with the proved positive Haar scalar cancelled explicitly. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TraceTestHeisenberg.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  {I : Type*} [Fintype I] (e : I ≃ Finite.AdelicTestCoordinates.CM.Index F N)

theorem pairing (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    HeckeCycles.NumberField.FunctionUnitarity.CM.GlobalPairing.pairing F N (TraceTestHeisenberg.CM.tests F N e f) (TraceTestHeisenberg.CM.tests F N e h) =
      (Finite.ReindexHeisenberg.CM.Pairing.factor e : ℂ) * Finite.FiniteOscillator.CM.integralPairing f h :=
  (HeckeCycles.NumberField.FunctionUnitarity.CM.GlobalPairing.rational_pairing F N _ _).trans
    (Finite.ReindexHeisenberg.CM.Pairing.pairing e f h)

theorem unitary (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (T : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N)
    (hT : ∀ f h, HeckeCycles.NumberField.FunctionUnitarity.CM.GlobalPairing.pairing F N (T f) (T h) =
      HeckeCycles.NumberField.FunctionUnitarity.CM.GlobalPairing.pairing F N f h)
    (he : ∀ f, TraceTestHeisenberg.CM.tests F N e (U f) = T (TraceTestHeisenberg.CM.tests F N e f)) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    Finite.FiniteOscillator.CM.integralPairing (U f) (U h) = Finite.FiniteOscillator.CM.integralPairing f h := by
  have hp := hT (TraceTestHeisenberg.CM.tests F N e f) (TraceTestHeisenberg.CM.tests F N e h)
  rw [← he, ← he, pairing, pairing] at hp
  apply mul_left_cancel₀ (show (Finite.ReindexHeisenberg.CM.Pairing.factor e : ℂ) ≠ 0 from ?_) hp
  exact_mod_cast (Finite.ReindexHeisenberg.CM.Pairing.factor_pos e).ne'

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TraceTestUnitarity.CM
