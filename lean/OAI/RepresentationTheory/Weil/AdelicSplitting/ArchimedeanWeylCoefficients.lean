import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierIntertwiner
import OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylMatrixCoefficients

/-! # Archimedean Weyl Coefficients -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylCoefficients.LocalAnalysis

noncomputable section

/-! Rapid decay of archimedean Weyl matrix coefficients. Position decay
comes from translated correlations; an actual Fourier oscillator gives
momentum decay by covariance. No open-cell operator is assumed. -/

open _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction

variable {k : Type} [NormedField k] [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
  [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] {N : ℕ}

theorem archimedean_weyl_coefficient_position_decay (ψ : AddChar k ℂ)
    (hu : ∀ t, ‖ψ t‖ = 1) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N,
      (1 + ‖UnitarySplitting.FourierCovariance.Construction.phasePosition v‖) ^ j *
        ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val v‖ ≤ C := by
  obtain ⟨φ, hφ⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp f.property
  obtain ⟨χ, hχ⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp h.property
  obtain ⟨C, hC, hb⟩ := RapidFunctions.LocalAnalysis.rapid_translated_correlation_bound (RapidFunctions.LocalAnalysis.schwartzRapidFunction φ)
    (RapidFunctions.LocalAnalysis.schwartzRapidFunction χ) (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) j
  refine ⟨C, hC, fun v => ?_⟩
  have hv := hb (UnitarySplitting.FourierCovariance.Construction.phasePosition v)
    (fun x => ψ (Local.FunctionsMetaplectic.Construction.dot (UnitarySplitting.FourierCovariance.Construction.phaseMomentum v) (x - (2 : k)⁻¹ • UnitarySplitting.FourierCovariance.Construction.phasePosition v))) (fun x => hu _)
  change (1 + ‖UnitarySplitting.FourierCovariance.Construction.phasePosition v‖) ^ j * ‖∫ x,
    ψ (Local.FunctionsMetaplectic.Construction.dot (UnitarySplitting.FourierCovariance.Construction.phaseMomentum v) (x - (2 : k)⁻¹ • UnitarySplitting.FourierCovariance.Construction.phasePosition v)) *
      φ (x - UnitarySplitting.FourierCovariance.Construction.phasePosition v) * star (χ x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k N‖ ≤ C at hv
  simpa only [UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient, UnitarySplitting.FourierCovariance.Construction.heisenbergFunction_dot,
    hφ, hχ] using! hv

omit [NormedAlgebra ℝ k] [FiniteDimensional ℝ k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] in
theorem phaseSpace_norm_eq_max (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    ‖v‖ = max ‖UnitarySplitting.FourierCovariance.Construction.phasePosition v‖ ‖UnitarySplitting.FourierCovariance.Construction.phaseMomentum v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))).mpr
    intro i
    cases i with
    | inl j => exact (norm_le_pi_norm (UnitarySplitting.FourierCovariance.Construction.phasePosition v) j).trans (le_max_left _ _)
    | inr j => exact (norm_le_pi_norm (UnitarySplitting.FourierCovariance.Construction.phaseMomentum v) j).trans (le_max_right _ _)
  · apply max_le
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr (fun j => norm_le_pi_norm v (.inl j))
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr (fun j => norm_le_pi_norm v (.inr j))

variable [CompleteSpace k] [CharZero k] [SecondCountableTopology k]

omit [NormedAlgebra ℝ k] [FiniteDimensional ℝ k] [SecondCountableTopology k] in
theorem localOscillator_heisenberg_covariance (hk : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (a : Oscillator.Construction.LocalCover k N ψ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Oscillator.Construction.localOperator k N ψ a (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f) =
      UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu (Local.FunctionsMetaplectic.Construction.symplecticAction (Oscillator.Construction.localProjection k N ψ a) v)
        (Oscillator.Construction.localOperator k N ψ a f) := by
  apply Subtype.ext
  exact (a.property.2 v f (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f)).mp rfl

def archimedeanWeylCoefficientRapid (hk : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (a : Oscillator.Construction.LocalCover k N ψ) (ha : Oscillator.Construction.localProjection k N ψ a = Local.Generators.Construction.weylSymplectic k N)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : RapidFunctions.LocalAnalysis.RapidFunction (Local.FunctionsMetaplectic.Construction.PhaseSpace k N) where
  toContinuousMap := ⟨UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val,
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_continuous ψ hc hu _ f h⟩
  decay j := by
    obtain ⟨C, hC, hpos⟩ := archimedean_weyl_coefficient_position_decay ψ hu f h j
    obtain ⟨D, hD, hrot⟩ := archimedean_weyl_coefficient_position_decay ψ hu
      (Oscillator.Construction.localOperator k N ψ a f) (Oscillator.Construction.localOperator k N ψ a h) j
    have hcov (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
        UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
          (Oscillator.Construction.localOperator k N ψ a f).val (Oscillator.Construction.localOperator k N ψ a h).val
          (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k N) v) =
        UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val v := by
      rw [← ha]
      exact UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_covariance hk ψ hc hu
        (Oscillator.Construction.localOperator k N ψ a) a.property.1 _
        (localOscillator_heisenberg_covariance hk ψ hc hu a) f h v
    refine ⟨max C D, hC.trans (le_max_left _ _), fun v => ?_⟩
    change (1 + ‖v‖) ^ j * ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val v‖ ≤ _
    rw [phaseSpace_norm_eq_max]
    by_cases hp : ‖UnitarySplitting.FourierCovariance.Construction.phaseMomentum v‖ ≤ ‖UnitarySplitting.FourierCovariance.Construction.phasePosition v‖
    · rw [max_eq_left hp]
      exact (hpos v).trans (le_max_left _ _)
    · rw [max_eq_right (le_of_not_ge hp)]
      have hr := hrot (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k N) v)
      rw [hcov] at hr
      have hphase : UnitarySplitting.FourierCovariance.Construction.phasePosition (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k N) v) = UnitarySplitting.FourierCovariance.Construction.phaseMomentum v :=
        FourierIntertwiner.LocalAnalysis.positionPart_weyl v
      rw [hphase] at hr
      exact hr.trans (le_max_right _ _)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylCoefficients.LocalAnalysis
