import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MetaplecticGaussianCoefficient
import OAI.RepresentationTheory.Theta.Adelic.FieldCoverPullback

/-! # Real Field Gaussian -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealFieldGaussian.CM

noncomputable section

/-! Exact transport of Gaussian tests and their actual oscillator
coefficients from a native real completion to standard real coordinates. -/

open OAI.RepresentationTheory.Theta.Adelic.FieldCoverTopology OAI.RepresentationTheory.Theta.Adelic.FieldCoverPullback

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
  (e : k ≃+* ℝ) (he : Continuous e) (hi : Continuous e.symm) {N : ℕ}
  (ψ : AddChar k ℂ) (hψ : RepresentationTheory.Weil.Local.FieldFourier.Construction.fieldCharacter e ψ = RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)

def realFieldStandardCover : RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ →ₜ* RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) :=
  (RepresentationTheory.Theta.Adelic.FieldCoverPullback.coverCharacterCongr hψ).comp (RepresentationTheory.Theta.Adelic.FieldCoverTopology.fieldCoverContinuous e he hi N ψ)

theorem real_field_standard_cover_projection (a : RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) :
    RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (realFieldStandardCover e he hi ψ hψ a) =
      RepresentationTheory.Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ a) :=
  RepresentationTheory.Theta.Adelic.FieldCoverPullback.coverCharacterCongr_projection hψ (RepresentationTheory.Theta.Adelic.FieldCoverTopology.fieldCoverContinuous e he hi N ψ a)

theorem real_field_standard_cover_operator (a : RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (realFieldStandardCover e he hi ψ hψ a).val.2
      (RepresentationTheory.Weil.Local.FieldCoordinates.Construction.testSpaceTransport (RepresentationTheory.Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N) f) =
        RepresentationTheory.Weil.Local.FieldCoordinates.Construction.testSpaceTransport (RepresentationTheory.Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N) (a.val.2 f) := by
  change RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)
    (RepresentationTheory.Theta.Adelic.FieldCoverPullback.coverCharacterCongr hψ (RepresentationTheory.Theta.Adelic.FieldCoverTopology.fieldCoverContinuous e he hi N ψ a)) _ = _
  rw [RepresentationTheory.Theta.Adelic.FieldCoverPullback.coverCharacterCongr_operator]
  exact RepresentationTheory.Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport_apply e he hi N ψ a f

omit [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] in
def realFieldGaussian (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (ξ : Fin N → ℂ) : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N :=
  (RepresentationTheory.Weil.Local.FieldCoordinates.Construction.testSpaceTransport (RepresentationTheory.Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N)).symm (RealGaussianCoefficient.CM.realSiegelGaussian Z ξ)

def realFieldGaussianCoefficient (a : RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) : ℂ :=
  (a.val.2 (realFieldGaussian e he hi Z 0)).val 0

theorem real_field_gaussian_coefficient (a : RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    RealGaussianCoefficient.CM.realGaussianCoefficient (realFieldStandardCover e he hi ψ hψ a) Z =
      realFieldGaussianCoefficient e he hi ψ a Z := by
  have h := real_field_standard_cover_operator e he hi ψ hψ a (realFieldGaussian e he hi Z 0)
  change (realFieldStandardCover e he hi ψ hψ a).val.2
    ((RepresentationTheory.Weil.Local.FieldCoordinates.Construction.testSpaceTransport (RepresentationTheory.Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N))
      ((RepresentationTheory.Weil.Local.FieldCoordinates.Construction.testSpaceTransport (RepresentationTheory.Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N)).symm (RealGaussianCoefficient.CM.realSiegelGaussian Z 0))) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  have hh := congrArg (fun f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N => f.val 0) h
  change RealGaussianCoefficient.CM.realGaussianCoefficient (realFieldStandardCover e he hi ψ hψ a) Z =
    (a.val.2 (realFieldGaussian e he hi Z 0)).val
      ((RepresentationTheory.Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm 0) at hh
  simpa only [realFieldGaussianCoefficient, map_zero] using! hh

include hψ in
theorem real_field_gaussian_covariance (a : RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ)
    (hg : RepresentationTheory.Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ a) = OscillatorPhaseOrder.CM.swapSymplecticPhase g)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (ξ : Fin N → ℂ) :
    a.val.2 (realFieldGaussian e he hi Z ξ) =
      (realFieldGaussianCoefficient e he hi ψ a Z * Complex.exp (-(RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).thetaCorrectionForm Z ξ ξ)) •
        realFieldGaussian e he hi ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).jacobiChange Z ξ) := by
  let T := RepresentationTheory.Weil.Local.FieldCoordinates.Construction.testSpaceTransport (RepresentationTheory.Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N)
  apply T.injective
  change T (a.val.2 (T.symm (RealGaussianCoefficient.CM.realSiegelGaussian Z ξ))) =
    T (_ • T.symm (RealGaussianCoefficient.CM.realSiegelGaussian ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).jacobiChange Z ξ)))
  rw [map_smul, T.apply_symm_apply]
  have h := real_field_standard_cover_operator e he hi ψ hψ a (T.symm (RealGaussianCoefficient.CM.realSiegelGaussian Z ξ))
  change (realFieldStandardCover e he hi ψ hψ a).val.2 (T (T.symm (RealGaussianCoefficient.CM.realSiegelGaussian Z ξ))) = _ at h
  rw [T.apply_symm_apply] at h
  rw [← h, ← real_field_gaussian_coefficient e he hi ψ hψ a Z]
  exact RealGaussianCovariance.CM.real_oscillator_full_gaussian_covariance g (realFieldStandardCover e he hi ψ hψ a)
    ((real_field_standard_cover_projection e he hi ψ hψ a).trans hg) Z ξ

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealFieldGaussian.CM
