import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCovariance
import OAI.RepresentationTheory.Weil.Local.RealStandardBareKernel

/-! # Metaplectic Gaussian Coefficient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MetaplecticGaussianCoefficient.CM

noncomputable section

/-! For an actual bare metaplectic lift, the computed Gaussian
coefficient has precisely the inverse determinant square. -/

open OAI.RepresentationTheory.Weil.Local.RealStandardBareKernel.Construction

theorem metaplectic_gaussian_coefficient_square {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ)
    (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)) (hm : a ∈ RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))
    (ha : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a = OscillatorPhaseOrder.CM.swapSymplecticPhase g)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    RealGaussianCoefficient.CM.realGaussianCoefficient a Z ^ 2 * ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).complexify.denominator Z.matrix).det = 1 := by
  have hin : RepresentationTheory.Weil.Local.FrameGaussianAction.Construction.realGaussianGraph (PositiveSiegelFrame.CM.siegelPositiveFrame Z) (PositiveSiegelFrame.CM.siegelPositiveFrame Z).gaussianLp :=
    ⟨1, by rw [one_pow, one_mul, PositiveSiegelFrame.CM.siegel_positive_frame_position, Matrix.det_one], by rw [one_smul]⟩
  have hout := ((RepresentationTheory.Weil.Local.RealStandardBareKernel.Construction.real_standard_metaplectic_le_gaussianSubgroup N hm)
    (PositiveSiegelFrame.CM.siegelPositiveFrame Z) (PositiveSiegelFrame.CM.siegelPositiveFrame Z).gaussianLp).mp hin
  rw [ha] at hout
  obtain ⟨c, hc, he⟩ := hout
  have ht : a.val.2 (RealGaussianCoefficient.CM.realSiegelGaussian Z 0) =
      c • RealGaussianCoefficient.CM.realSiegelGaussian ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z) 0 := by
    apply RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2_injective ℝ N
    rw [map_smul, ← RepresentationTheory.Weil.Local.RealOscillator.Construction.realL2Oscillator_apply, RealGaussianCoefficient.CM.real_siegel_gaussian_toLp, RealGaussianCoefficient.CM.real_siegel_gaussian_toLp]
    refine he.trans (congrArg (fun q => c • q) ?_)
    apply RealGaussianCoefficient.CM.positive_frame_gaussianLp_congr
    rw [SiegelOscillatorGraph.CM.siegel_frame_swapped_quadratic, PositiveSiegelFrame.CM.siegel_positive_frame_quadratic]
  have hcoeff : RealGaussianCoefficient.CM.realGaussianCoefficient a Z = c := by
    have h := congrArg (fun f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N => f.val 0) ht
    change RealGaussianCoefficient.CM.realGaussianCoefficient a Z = c * (RealGaussianCoefficient.CM.realSiegelGaussian ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z) 0).val 0 at h
    simpa only [RealGaussianCoefficient.CM.real_siegel_gaussian_at_zero, mul_one] using h
  rw [hcoeff]
  simpa only [SiegelOscillatorGraph.CM.siegel_frame_swapped_position] using hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MetaplecticGaussianCoefficient.CM
