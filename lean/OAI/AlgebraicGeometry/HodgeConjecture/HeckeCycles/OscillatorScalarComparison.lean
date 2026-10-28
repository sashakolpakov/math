import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.BareGenerators
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.RealCover
import OAI.RepresentationTheory.Weil.Local.OscillatorSchur

/-! # Oscillator Scalar Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorScalarComparison.CM

noncomputable section

/-! Two actual oscillator operators above the same symplectic matrix
differ by a scalar, separately at the real and finite factors. -/

open scoped Classical
open OAI.RepresentationTheory.Weil.Local.OscillatorSchur.Construction

theorem real (n : ℕ) (a b : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))
    (hab : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a = RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) b) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n, a.val.2 f = c • b.val.2 f := by
  have hp : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  obtain ⟨c, hc, hf⟩ := RepresentationTheory.Weil.Local.OscillatorSchur.Construction.real_oscillator_kernel_scalar (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)
    (RepresentationTheory.Weil.Local.RealTestSpace.Construction.realCharacter_temperate 1).1.continuous (RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction.realCharacter_unitary 1)
    RepresentationTheory.Weil.Local.RealStandardBareKernel.Construction.real_standard_character_nontrivial (a * b⁻¹) hp
  refine ⟨c, hc, ?_⟩
  intro f
  have h := hf (b.val.2 f)
  change a.val.2 (b.val.2.symm (b.val.2 f)) = _ at h
  rwa [LinearEquiv.symm_apply_apply] at h

theorem finite {I : Type*} [Fintype I]
    (a b : Finite.FiniteOscillator.CM.Oscillator (I := I))
    (hab : Finite.FiniteOscillator.CM.projection a = Finite.FiniteOscillator.CM.projection b) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I,
      Finite.FiniteOscillator.CM.action a f = c • Finite.FiniteOscillator.CM.action b f := by
  have hp : Finite.FiniteOscillator.CM.projection (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  obtain ⟨c, hc, hf⟩ := Finite.BareNe.CM.OscillatorKernel.kernel_scalar (a * b⁻¹) hp
  refine ⟨c, hc, ?_⟩
  intro f
  have h := hf (Finite.FiniteOscillator.CM.action b f)
  rw [map_mul, map_inv] at h
  change Finite.FiniteOscillator.CM.action a ((Finite.FiniteOscillator.CM.action b).symm
    (Finite.FiniteOscillator.CM.action b f)) = _ at h
  rwa [LinearEquiv.symm_apply_apply] at h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorScalarComparison.CM
