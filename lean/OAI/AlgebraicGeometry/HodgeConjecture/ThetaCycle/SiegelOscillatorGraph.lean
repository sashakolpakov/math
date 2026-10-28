import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PositiveSiegelFrame
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.OscillatorPhaseOrder
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianAmplitude

/-! # Siegel Oscillator Graph -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelOscillatorGraph.CM

noncomputable section

/-! ThetaCycle: the oscillator's actual positive-frame action has exactly the
classical Siegel denominator, numerator, and transformed period. -/

open scoped Classical _root_.Matrix

theorem real_swapped_symplectic_matrix {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ) :
    RepresentationTheory.Weil.Local.SiegelGaussian.Construction.realSymplecticComplexMatrix (OscillatorPhaseOrder.CM.swapSymplecticPhase g) =
      (OscillatorPhaseOrder.CM.swapSymplecticPhase (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp Complex.ofRealHom g)).val := by
  ext i j
  cases i <;> cases j <;> rfl

theorem siegel_frame_swapped_matrix {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    ((PositiveSiegelFrame.CM.siegelPositiveFrame Z).act (OscillatorPhaseOrder.CM.swapSymplecticPhase g)).matrix =
      Matrix.fromRows ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).complexify.denominator Z.matrix)
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).complexify.numerator Z.matrix) := by
  change RepresentationTheory.Weil.Local.SiegelGaussian.Construction.realSymplecticComplexMatrix (OscillatorPhaseOrder.CM.swapSymplecticPhase g) * Matrix.fromRows 1 Z.matrix = _
  rw [real_swapped_symplectic_matrix]
  exact OscillatorPhaseOrder.CM.swap_symplectic_phase_graph (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp Complex.ofRealHom g) Z.matrix

theorem siegel_frame_swapped_position {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    ((PositiveSiegelFrame.CM.siegelPositiveFrame Z).act (OscillatorPhaseOrder.CM.swapSymplecticPhase g)).position =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).complexify.denominator Z.matrix :=
  congrArg Matrix.toRows₁ (siegel_frame_swapped_matrix g Z)

theorem siegel_frame_swapped_momentum {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    ((PositiveSiegelFrame.CM.siegelPositiveFrame Z).act (OscillatorPhaseOrder.CM.swapSymplecticPhase g)).momentum =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).complexify.numerator Z.matrix :=
  congrArg Matrix.toRows₂ (siegel_frame_swapped_matrix g Z)

theorem siegel_frame_swapped_quadratic {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    ((PositiveSiegelFrame.CM.siegelPositiveFrame Z).act (OscillatorPhaseOrder.CM.swapSymplecticPhase g)).quadraticMatrix =
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z).matrix := by
  rw [RepresentationTheory.Weil.Local.SiegelGaussian.Construction.PositiveLagrangianFrame.quadraticMatrix, siegel_frame_swapped_position,
    siegel_frame_swapped_momentum, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.transformSiegel_matrix]
  rfl

theorem real_oscillator_siegel_amplitudes {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ)
    (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))
    (ha : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a = OscillatorPhaseOrder.CM.swapSymplecticPhase g) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N), ∃ c : ℂ,
      c ^ 2 * ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).complexify.denominator Z.matrix).det = z ^ 2 ∧
      RepresentationTheory.Weil.Local.RealOscillator.Construction.realL2Oscillator N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a (PositiveSiegelFrame.CM.siegelPositiveFrame Z).gaussianLp =
        c • ((PositiveSiegelFrame.CM.siegelPositiveFrame Z).act (OscillatorPhaseOrder.CM.swapSymplecticPhase g)).gaussianLp := by
  obtain ⟨z, hz, h⟩ := RealGaussianAmplitude.CM.real_oscillator_gaussian_amplitudes a
  refine ⟨z, hz, fun Z => ?_⟩
  obtain ⟨c, hc, hU⟩ := h (PositiveSiegelFrame.CM.siegelPositiveFrame Z)
  rw [ha, siegel_frame_swapped_position, PositiveSiegelFrame.CM.siegel_positive_frame_position, Matrix.det_one, mul_one] at hc
  rw [ha] at hU
  exact ⟨c, hc, hU⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelOscillatorGraph.CM
