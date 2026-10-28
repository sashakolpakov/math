import OAI.RepresentationTheory.Theta.Adelic.GaussianWeakContinuity

/-! # Gaussian Coefficient Continuity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GaussianCoefficientContinuity.CM

noncomputable section

/-! Continuity of the actual oscillator coefficient, recovered from
weak Gaussian pairings and the previously proved Gaussian action. -/

open scoped Classical _root_.Matrix.Norms.Elementwise ComplexConjugate InnerProductSpace _root_.Topology
open _root_.Matrix _root_.MeasureTheory
open OAI.RepresentationTheory.Theta.Adelic.GaussianWeakContinuity

variable {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ) (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))

theorem oscillator_gaussian_pairing
    (ha : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a = OscillatorPhaseOrder.CM.swapSymplecticPhase g)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) :
    RepresentationTheory.Theta.Adelic.GaussianWeakContinuity.gaussianPairing Z (a.val.2.symm f) =
      RealGaussianCoefficient.CM.realGaussianCoefficient a Z * RepresentationTheory.Theta.Adelic.GaussianWeakContinuity.gaussianPairing ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z) f := by
  obtain ⟨_, _, hc⟩ := RealGaussianCoefficient.CM.real_oscillator_gaussian_coefficient g a ha
  have h := RepresentationTheory.Weil.Local.UnitaryInner.Construction.energy_preserving_inner ℝ N a.val.2.toLinearMap a.property.1
    (a.val.2.symm f) (RealGaussianCoefficient.CM.realSiegelGaussian Z 0)
  change inner ℂ (RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2 ℝ N (a.val.2 (a.val.2.symm f)))
    (RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2 ℝ N (a.val.2 (RealGaussianCoefficient.CM.realSiegelGaussian Z 0))) =
    inner ℂ (RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2 ℝ N (a.val.2.symm f)) (RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2 ℝ N (RealGaussianCoefficient.CM.realSiegelGaussian Z 0)) at h
  rw [LinearEquiv.apply_symm_apply, (hc Z).2, map_smul, inner_smul_right] at h
  rw [← RepresentationTheory.Theta.Adelic.GaussianWeakContinuity.gaussianPairing_inner, ← RepresentationTheory.Theta.Adelic.GaussianWeakContinuity.gaussianPairing_inner] at h
  exact h.symm

theorem real_gaussian_coefficient_continuous
    (ha : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a = OscillatorPhaseOrder.CM.swapSymplecticPhase g)
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (Z : X → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (hZ : Continuous (fun x => (Z x).matrix))
    (hT : Continuous (fun x => ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel (Z x)).matrix)) :
    Continuous (fun x => RealGaussianCoefficient.CM.realGaussianCoefficient a (Z x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let f := RealGaussianCoefficient.CM.realSiegelGaussian ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel (Z x)) 0
  let u := fun y => RepresentationTheory.Theta.Adelic.GaussianWeakContinuity.gaussianPairing (Z y) (a.val.2.symm f)
  let v := fun y => RepresentationTheory.Theta.Adelic.GaussianWeakContinuity.gaussianPairing ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel (Z y)) f
  have hu : Continuous u := RepresentationTheory.Theta.Adelic.GaussianWeakContinuity.gaussianPairing_continuous Z hZ (a.val.2.symm f)
  have hv : Continuous v := RepresentationTheory.Theta.Adelic.GaussianWeakContinuity.gaussianPairing_continuous (fun y => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel (Z y)) hT f
  have hn : v x ≠ 0 := RepresentationTheory.Theta.Adelic.GaussianWeakContinuity.gaussianPairing_self_nonzero ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel (Z x))
  apply (hu.continuousAt.div hv.continuousAt hn).congr_of_eventuallyEq
  filter_upwards [hv.continuousAt.eventually_ne hn] with y hy
  exact (eq_div_iff hy).mpr (oscillator_gaussian_pairing g a ha (Z y) f).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GaussianCoefficientContinuity.CM
