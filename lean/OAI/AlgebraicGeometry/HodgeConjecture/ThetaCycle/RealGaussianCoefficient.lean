import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelOscillatorGraph
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelGaussian

/-! # Real Gaussian Coefficient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM

noncomputable section

/-! ThetaCycle: identify the real oscillator's Gaussian amplitude by evaluating
the actual transformed Schwartz function at zero. -/

open scoped Classical _root_.Matrix

def realSiegelGaussian {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N :=
  RepresentationTheory.Weil.Local.RealTestSpace.Construction.realSchwartzToBruhat (SiegelGaussian.CM.siegelGaussianSchwartz Z z)

theorem real_siegel_gaussian_apply {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ)
    (x : Fin N → ℝ) : (realSiegelGaussian Z z).val x = RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z x :=
  SiegelGaussian.CM.siegel_gaussian_schwartz_apply Z z x

theorem real_siegel_gaussian_zero_jacobi {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    (realSiegelGaussian Z 0).val = RepresentationTheory.Weil.Local.SiegelGaussian.Construction.siegelGaussian Z.matrix := by
  funext x
  rw [real_siegel_gaussian_apply]
  simp only [RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction, RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent, ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase, RepresentationTheory.Weil.Local.SiegelGaussian.Construction.siegelGaussian,
    ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
    ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

theorem real_siegel_gaussian_at_zero {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    (realSiegelGaussian Z 0).val 0 = 1 := by
  rw [real_siegel_gaussian_zero_jacobi, RepresentationTheory.Weil.Local.SiegelGaussian.Construction.siegelGaussian_zero]

theorem real_siegel_gaussian_toLp {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2 ℝ N (realSiegelGaussian Z 0) = (PositiveSiegelFrame.CM.siegelPositiveFrame Z).gaussianLp := by
  apply MeasureTheory.MemLp.toLp_congr (RepresentationTheory.Weil.Local.UnitaryInner.Construction.test_memLp_two ℝ N (realSiegelGaussian Z 0))
    (PositiveSiegelFrame.CM.siegelPositiveFrame Z).gaussian_memLp
  apply Filter.Eventually.of_forall
  intro x
  rw [real_siegel_gaussian_zero_jacobi, PositiveSiegelFrame.CM.siegel_positive_frame_quadratic]

theorem positive_frame_gaussianLp_congr {N : ℕ} (P Q : RepresentationTheory.Weil.Local.SiegelGaussian.Construction.PositiveLagrangianFrame N)
    (h : P.quadraticMatrix = Q.quadraticMatrix) : P.gaussianLp = Q.gaussianLp := by
  apply MeasureTheory.MemLp.toLp_congr P.gaussian_memLp Q.gaussian_memLp
  apply Filter.Eventually.of_forall
  intro x
  rw [h]

theorem real_oscillator_siegel_gaussian {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ)
    (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))
    (ha : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a = OscillatorPhaseOrder.CM.swapSymplecticPhase g) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N), ∃ c : ℂ,
      c ^ 2 * ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).complexify.denominator Z.matrix).det = z ^ 2 ∧
      a.val.2 (realSiegelGaussian Z 0) = c • realSiegelGaussian ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z) 0 := by
  obtain ⟨z, hz, h⟩ := SiegelOscillatorGraph.CM.real_oscillator_siegel_amplitudes g a ha
  refine ⟨z, hz, fun Z => ?_⟩
  obtain ⟨c, hc, hU⟩ := h Z
  refine ⟨c, hc, ?_⟩
  apply RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2_injective ℝ N
  rw [map_smul, ← RepresentationTheory.Weil.Local.RealOscillator.Construction.realL2Oscillator_apply, real_siegel_gaussian_toLp, real_siegel_gaussian_toLp]
  refine hU.trans (congrArg (fun v => c • v) ?_)
  apply positive_frame_gaussianLp_congr
  rw [SiegelOscillatorGraph.CM.siegel_frame_swapped_quadratic, PositiveSiegelFrame.CM.siegel_positive_frame_quadratic]

def realGaussianCoefficient {N : ℕ} (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) : ℂ :=
  (a.val.2 (realSiegelGaussian Z 0)).val 0

theorem real_oscillator_gaussian_coefficient {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ)
    (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))
    (ha : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a = OscillatorPhaseOrder.CM.swapSymplecticPhase g) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N),
      realGaussianCoefficient a Z ^ 2 * ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).complexify.denominator Z.matrix).det = z ^ 2 ∧
      a.val.2 (realSiegelGaussian Z 0) =
        realGaussianCoefficient a Z • realSiegelGaussian ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z) 0 := by
  obtain ⟨z, hz, h⟩ := real_oscillator_siegel_gaussian g a ha
  refine ⟨z, hz, fun Z => ?_⟩
  obtain ⟨c, hc, hU⟩ := h Z
  have he := congrArg (fun f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N => f.val 0) hU
  change realGaussianCoefficient a Z = c * (realSiegelGaussian ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z) 0).val 0 at he
  rw [real_siegel_gaussian_at_zero, mul_one] at he
  exact ⟨he.symm ▸ hc, he.symm ▸ hU⟩

theorem real_gaussian_coefficient_ne_zero {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ)
    (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))
    (ha : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a = OscillatorPhaseOrder.CM.swapSymplecticPhase g)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) : realGaussianCoefficient a Z ≠ 0 := by
  obtain ⟨z, hz, h⟩ := real_oscillator_gaussian_coefficient g a ha
  have hz0 : z ≠ 0 := by
    intro hzero
    exact zero_ne_one (by simpa only [hzero, norm_zero] using hz)
  intro hc
  have hs := (h Z).1
  rw [hc, zero_pow (by decide : 2 ≠ 0), zero_mul] at hs
  exact pow_ne_zero 2 hz0 hs.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM
