import OAI.RepresentationTheory.Weil.Local.RealStandardBareKernel

/-! # Real Gaussian Amplitude -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianAmplitude.CM

noncomputable section

/-! ThetaCycle: actual real oscillator operators preserve the Gaussian lines
of positive Lagrangian frames. The residual unit scalar is independent of
the frame, and the amplitude has the exact determinant-square relation. -/

open OAI.RepresentationTheory.Weil.Local.RealStandardBareKernel.Construction

theorem real_gaussian_subgroup_amplitude {N : ℕ}
    (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)) (ha : a ∈ RepresentationTheory.Weil.Local.FrameGaussianAction.Construction.realGaussianSubgroup N)
    (P : RepresentationTheory.Weil.Local.SiegelGaussian.Construction.PositiveLagrangianFrame N) :
    ∃ c : ℂ, c ^ 2 * (P.act (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a)).position.det =
        P.position.det ∧
      RepresentationTheory.Weil.Local.RealOscillator.Construction.realL2Oscillator N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a P.gaussianLp =
        c • (P.act (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a)).gaussianLp := by
  obtain ⟨_, d, hd, rfl⟩ := RepresentationTheory.Weil.Local.FrameGaussianAction.Construction.realGaussianGraph_exists P
  have hd0 : d ≠ 0 := by
    intro h
    simp only [h, zero_pow (by decide : 2 ≠ 0), zero_mul] at hd
    exact zero_ne_one hd
  obtain ⟨e, he, hU⟩ := (ha P (d • P.gaussianLp)).mp ⟨d, hd, rfl⟩
  refine ⟨e / d, ?_, ?_⟩
  · calc
      (e / d) ^ 2 * (P.act (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a)).position.det =
          (e ^ 2 * (P.act (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a)).position.det) / d ^ 2 := by ring
      _ = 1 / d ^ 2 := by rw [he]
      _ = P.position.det := (div_eq_iff (pow_ne_zero 2 hd0)).mpr (by rw [mul_comm, hd])
  · rw [map_smul] at hU
    have h := congrArg (fun x => d⁻¹ • x) hU
    simpa only [smul_smul, inv_mul_cancel₀ hd0, one_smul, div_eq_mul_inv, mul_comm] using h

theorem real_oscillator_gaussian_amplitudes {N : ℕ} (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ P : RepresentationTheory.Weil.Local.SiegelGaussian.Construction.PositiveLagrangianFrame N,
      ∃ c : ℂ,
        c ^ 2 * (P.act (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a)).position.det =
          z ^ 2 * P.position.det ∧
        RepresentationTheory.Weil.Local.RealOscillator.Construction.realL2Oscillator N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a P.gaussianLp =
          c • (P.act (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a)).gaussianLp := by
  have hmap : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a ∈
      (RepresentationTheory.Weil.Local.FrameGaussianAction.Construction.realGaussianSubgroup N).map (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)) := by
    rw [RepresentationTheory.Weil.Local.RealStandardBareKernel.Construction.realGaussianSubgroup_projection]
    trivial
  obtain ⟨b, hb, hba⟩ := hmap
  have hker : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hba, mul_inv_cancel]
  obtain ⟨z, hz, hs⟩ := RepresentationTheory.Weil.Local.OscillatorSchur.Construction.real_oscillator_kernel_scalar (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)
    (RepresentationTheory.Weil.Local.RealTestSpace.Construction.realCharacter_temperate 1).1.continuous (RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction.realCharacter_unitary 1)
    RepresentationTheory.Weil.Local.RealStandardBareKernel.Construction.real_standard_character_nontrivial (a * b⁻¹) hker
  refine ⟨z, hz, fun P => ?_⟩
  obtain ⟨c, hc, hU⟩ := real_gaussian_subgroup_amplitude b hb P
  rw [hba] at hc hU
  refine ⟨z * c, ?_, ?_⟩
  · rw [mul_pow, mul_assoc, hc]
  · have he : a = (a * b⁻¹) * b := by simp
    conv_lhs => rw [he, RepresentationTheory.Weil.Local.RealOscillator.Construction.realL2Oscillator_mul]
    change RepresentationTheory.Weil.Local.RealOscillator.Construction.realL2Oscillator N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (a * b⁻¹)
      (RepresentationTheory.Weil.Local.RealOscillator.Construction.realL2Oscillator N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) b P.gaussianLp) = _
    rw [RepresentationTheory.Weil.Local.RealOscillator.Construction.realL2Oscillator_scalar N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (a * b⁻¹) z hs, hU, smul_smul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianAmplitude.CM
