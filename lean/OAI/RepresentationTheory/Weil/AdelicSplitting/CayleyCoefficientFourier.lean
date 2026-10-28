import OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizedWeylCoefficients
import OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyMatrixBaseChange

/-! # Cayley Coefficient Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyCoefficientFourier.Construction

noncomputable section

/-! The weak Cayley normalization acts on Weyl coefficients by explicit
quadratic phases, Fourier transform, and an invertible linear substitution. -/

open _root_.MeasureTheory
open scoped ComplexConjugate _root_.Matrix

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (μ : Measure k) [μ.IsAddHaarMeasure]
variable (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
variable (D : CayleyMatrixBaseChange.Construction.PhaseMatrixUnit k N) (hD : D.val = g.val - 1)
variable (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N → Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (c : ℂ)
variable (hU : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
  (∫ x, (U f).val x * conj (h.val x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
    c * CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) g hg f.val h.val)

include hk hc hu hD hU in
theorem normalized_weyl_coefficient_fourier (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (x : Local.FunctionsMetaplectic.Construction.Position k (N + N)) :
    WeylCoefficientTransport.Construction.positionWeylCoefficient ψ (Measure.pi (fun _ : Fin N => μ)) (U f).val h.val x =
      c * (Normalization.Construction.openCellScale k N g : ℂ)⁻¹ * ψ (Local.FunctionsMetaplectic.Construction.quadratic (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic k N D).val x) *
        Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin (N + N) => μ))
          (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic k N D).val
            (WeylCoefficientTransport.Construction.positionWeylCoefficient ψ (Measure.pi (fun _ : Fin N => μ)) f.val h.val))
          ((CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear k N D)⁻¹.val *ᵥ x) := by
  rw [WeylCoefficientTransport.Construction.positionWeylCoefficient, NormalizedWeylCoefficients.Construction.normalized_weyl_coefficient_haar hk ψ hc hu _ g hg U c hU,
    PhaseFourier.Construction.phaseFourier_coordinate_formula]
  have hn : -(PhaseMeasure.Construction.phaseCoordinates k N (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k N)
      (-((SchrodingerPairing.Construction.openCellDifference k N g hg).symm ((PhaseMeasure.Construction.phaseCoordinates k N).symm x))))) =
      PhaseMeasure.Construction.phaseCoordinates k N (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k N)
        ((SchrodingerPairing.Construction.openCellDifference k N g hg).symm ((PhaseMeasure.Construction.phaseCoordinates k N).symm x))) := by
    change -(PhaseMeasure.Construction.phaseCoordinates k N ((Local.Generators.Construction.weylSymplectic k N).val *ᵥ
      (-((SchrodingerPairing.Construction.openCellDifference k N g hg).symm ((PhaseMeasure.Construction.phaseCoordinates k N).symm x))))) = _
    rw [Matrix.mulVec_neg, map_neg, neg_neg]
    rfl
  rw [hn, ← CayleyMatrixBaseChange.Construction.cayleyCoefficientLinear_local N g hg D hD]
  have hq (y : Local.FunctionsMetaplectic.Construction.Position k (N + N)) :
      SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg ((PhaseMeasure.Construction.phaseCoordinates k N).symm y) =
        Local.FunctionsMetaplectic.Construction.quadratic (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic k N D).val y :=
    (CayleyMatrixBaseChange.Construction.cayleyCoefficientQuadratic_local N g hg D hD y).symm
  simp only [hq]
  rw [← mul_assoc]
  rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyCoefficientFourier.Construction
