import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisAdd
import OAI.RepresentationTheory.Weil.UnitarySplitting.StandardTransvections

/-! # Weyl Synthesis Covariance -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisCovariance.Construction

noncomputable section

/-! The exact Weyl translation law for a synthesis amplitude. -/

open _root_.MeasureTheory

theorem weylSynthesis_heisenberg
    {F : Type} [NormedField F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (ψ : AddChar F ℂ) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (a : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) (w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ w (WeylSynthesisAdd.Construction.weylSynthesis ψ ν a f) =
      WeylSynthesisAdd.Construction.weylSynthesis ψ ν (fun v => ψ (Oscillator.Construction.standardSymplecticPairing d w v / 2) * a (v - w)) f := by
  funext x
  have hphase (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : Oscillator.Construction.standardSymplecticPairing d w (v + w) =
      Oscillator.Construction.standardSymplecticPairing d w v := by
    change (StandardTransvections.Construction.standardSymplecticBilinear F d) w (v + w) = _
    rw [map_add, (StandardTransvections.Construction.standardSymplecticBilinear_alternating d) w, add_zero]
    rfl
  calc
    _ = ∫ v, a v * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ w (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) x ∂ν := by
      rw [FourierCovariance.Construction.heisenbergFunction_dot]
      change ψ _ * (∫ v, a v * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f (x - FourierCovariance.Construction.phasePosition w) ∂ν) = _
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        dsimp only
        rw [FourierCovariance.Construction.heisenbergFunction_dot ψ w (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) x]
        ring
    _ = ∫ v, ψ (Oscillator.Construction.standardSymplecticPairing d w v / 2) * a v *
        Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (v + w) f x ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        dsimp only
        rw [Heisenberg.Construction.heisenbergFunction_composition]
        change a v * (ψ (Oscillator.Construction.standardSymplecticPairing d w v / 2) * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (w + v) f x) = _
        rw [add_comm w v]
        ring
    _ = _ := by
      unfold WeylSynthesisAdd.Construction.weylSynthesis
      rw [← integral_add_right_eq_self
        (fun v => (ψ (Oscillator.Construction.standardSymplecticPairing d w v / 2) * a (v - w)) *
          Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f x) w]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        dsimp only
        rw [add_sub_cancel_right, hphase]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisCovariance.Construction
