import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianTransport
import OAI.RepresentationTheory.Weil.Local.RealFourierFamily

/-! # Intrinsic Oscillator Gaussian -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicOscillatorGaussian.Intrinsic

noncomputable section

/-! Every actual circle-scalar oscillator transports the positive
Gaussian line. This includes normalized multiplicity-space operators,
whose scalar character need not belong to the bare double cover. -/

open OAI.RepresentationTheory.Weil.Local.RealFourierFamily.Construction OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianTransport.Intrinsic

theorem oscillator_same_projection_scalar {n : ℕ}
    (a b : Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1))
    (hab : Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a =
      Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) b) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n, a.val.2 f = z • b.val.2 f := by
  have hk : Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) (a * b⁻¹) = 1 := by
    rw [map_mul,map_inv,hab,mul_inv_cancel]
  obtain ⟨z,hz,hs⟩ := Weil.Local.OscillatorSchur.Construction.real_oscillator_kernel_scalar (Weil.Local.Gaussian.Construction.realCharacter 1)
    (Weil.Local.RealTestSpace.Construction.realCharacter_temperate 1).1.continuous (Weil.Local.QuadraticIntertwiner.Construction.realCharacter_unitary 1)
    Weil.Local.RealStandardBareKernel.Construction.real_standard_character_nontrivial (a * b⁻¹) hk
  refine ⟨z,hz,fun f => ?_⟩
  have h := hs (b.val.2 f)
  change a.val.2 (b.val.2.symm (b.val.2 f)) = z • b.val.2 f at h
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem oscillator_gaussian_test {n : ℕ}
    (a : Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1)) (P : Weil.Local.SiegelGaussian.Construction.PositiveLagrangianFrame n)
    (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (hφ : φ.val = Weil.Local.SiegelGaussian.Construction.siegelGaussian P.quadraticMatrix) :
    ∃ c : ℂ, c ≠ 0 ∧ (a.val.2 φ).val =
      c • Weil.Local.SiegelGaussian.Construction.siegelGaussian (P.act (Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a)).quadraticMatrix := by
  obtain ⟨b,hb⟩ := Weil.Local.RealFourierFamily.Construction.real_metaplecticProjection_surjective_parameter n 1 one_ne_zero
    (Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a)
  have hb' : Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) b.val =
      Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a := hb
  obtain ⟨z,hz,hs⟩ := oscillator_same_projection_scalar a b.val hb'.symm
  obtain ⟨c,hc,_,hT⟩ := IntrinsicGaussianTransport.Intrinsic.metaplectic_gaussian_test b P φ hφ
  refine ⟨z * c,mul_ne_zero (norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)) hc,?_⟩
  rw [hs]
  change z • (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) b φ).val = _
  rw [hT,hb,smul_smul]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicOscillatorGaussian.Intrinsic
