import OAI.RepresentationTheory.Weil.Local.RealStandardBareKernel

/-! # Intrinsic Gaussian Transport -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianTransport.Intrinsic

noncomputable section

/-! The actual real metaplectic operator carries every positive Gaussian
to the Gaussian of the moved positive frame, with the determinant-square
normalization. This uses the intrinsic LocalWeil Gaussian subgroup theorem. -/

open _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.Local.RealStandardBareKernel.Construction

theorem metaplectic_gaussian_amplitude {n : ℕ}
    (a : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1)) (P : Weil.Local.SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    ∃ c : ℂ, c ≠ 0 ∧
      c ^ 2 * (P.act (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a)).position.det = P.position.det ∧
      Weil.Local.RealOscillator.Construction.realL2Oscillator n (Weil.Local.Gaussian.Construction.realCharacter 1) a.val P.gaussianLp =
        c • (P.act (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a)).gaussianLp := by
  obtain ⟨v,d,hd,rfl⟩ := Weil.Local.FrameGaussianAction.Construction.realGaussianGraph_exists P
  have hd0 : d ≠ 0 := by
    intro h
    rw [h,zero_pow (by decide),zero_mul] at hd
    exact zero_ne_one hd
  have h := ((Weil.Local.RealStandardBareKernel.Construction.real_standard_metaplectic_le_gaussianSubgroup n a.property) P
    (d • P.gaussianLp)).mp ⟨d,hd,rfl⟩
  obtain ⟨e,he,hU⟩ := h
  have he0 : e ≠ 0 := by
    intro h
    rw [h,zero_pow (by decide),zero_mul] at he
    exact zero_ne_one he
  refine ⟨e / d,div_ne_zero he0 hd0,?_,?_⟩
  · change (e / d) ^ 2 * (P.act (Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a.val)).position.det = _
    rw [div_pow]
    calc
      _ = (e ^ 2 * (P.act (Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a.val)).position.det) / d ^ 2 := by ring
      _ = 1 / d ^ 2 := by rw [he]
      _ = P.position.det := by apply (div_eq_iff (pow_ne_zero _ hd0)).mpr; rw [mul_comm]; exact hd.symm
  · rw [map_smul] at hU
    have hU' := congrArg (fun w => d⁻¹ • w) hU
    change Weil.Local.RealOscillator.Construction.realL2Oscillator n (Weil.Local.Gaussian.Construction.realCharacter 1) a.val P.gaussianLp =
      (e / d) • (P.act (Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a.val)).gaussianLp
    simpa only [smul_smul,inv_mul_cancel₀ hd0,one_smul,div_eq_mul_inv,mul_comm] using hU'

theorem metaplectic_gaussian_test {n : ℕ}
    (a : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1)) (P : Weil.Local.SiegelGaussian.Construction.PositiveLagrangianFrame n)
    (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (hφ : φ.val = Weil.Local.SiegelGaussian.Construction.siegelGaussian P.quadraticMatrix) :
    ∃ c : ℂ, c ≠ 0 ∧
      c ^ 2 * (P.act (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a)).position.det = P.position.det ∧
      (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a φ).val =
        c • Weil.Local.SiegelGaussian.Construction.siegelGaussian (P.act (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a)).quadraticMatrix := by
  obtain ⟨c,hc,hd,hU⟩ := metaplectic_gaussian_amplitude a P
  refine ⟨c,hc,hd,?_⟩
  have hLp : Weil.Local.UnitaryInner.Construction.testToL2 ℝ n φ = P.gaussianLp := by
    apply (MemLp.toLp_eq_toLp_iff (Weil.Local.UnitaryInner.Construction.test_memLp_two ℝ n φ) P.gaussian_memLp).mpr
    exact Filter.Eventually.of_forall (congrFun hφ)
  rw [← hLp,Weil.Local.RealOscillator.Construction.realL2Oscillator_apply] at hU
  let Q := P.act (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a)
  have ha : (a.val.val.2 φ).val =ᵐ[Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n] c • Weil.Local.SiegelGaussian.Construction.siegelGaussian Q.quadraticMatrix := by
    apply (MemLp.toLp_eq_toLp_iff (Weil.Local.UnitaryInner.Construction.test_memLp_two ℝ n (a.val.val.2 φ))
      (Q.gaussian_memLp.const_smul c)).mp
    exact hU
  exact Measure.eq_of_ae_eq ha (Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat_continuous (a.val.val.2 φ).property)
    ((Weil.Local.SiegelGaussian.Construction.siegelGaussian_continuous Q.quadraticMatrix).const_smul c)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianTransport.Intrinsic
