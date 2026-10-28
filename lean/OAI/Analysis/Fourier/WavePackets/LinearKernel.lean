import OAI.Analysis.Fourier.WavePackets.Poisson

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace

theorem det_adjoint_real {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n)) : LinearMap.det A.adjoint = LinearMap.det A := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
    Matrix.det_conjTranspose, LinearMap.det_toMatrix]
  simp

/-- Exact change of variables for the Fourier kernel under an arbitrary
invertible linear frequency transformation, including anisotropic ones. -/
theorem fourierInv_comp_linearEquiv {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    𝓕⁻ (φ ∘ A) x = |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| •
      𝓕⁻ φ (A.symm.toLinearEquiv.toLinearMap.adjoint x) := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  let g := fun ξ : EuclideanSpace ℝ (Fin n) =>
    Real.fourierChar ⟪A.symm ξ, x⟫ • φ ξ
  have hchange := A.toHomeomorph.measurableEmbedding.integral_map (μ := volume) g
  change (∫ ξ, g ξ ∂Measure.map A volume) = ∫ ξ, g (A ξ) at hchange
  have hd : LinearMap.det A.toLinearEquiv.toLinearMap ≠ 0 :=
    A.toLinearEquiv.isUnit_det'.ne_zero
  have hmap : Measure.map A volume =
      ENNReal.ofReal |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at hchange
  calc
    _ = ∫ ξ, g (A ξ) := by simp [g]
    _ = |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • ∫ ξ, g ξ := hchange.symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      dsimp [g]
      rw [LinearMap.adjoint_inner_right]
      rfl

/-- Jacobian-normalized spatial changes of variables preserve kernel L1
norms. The transpose determinant is what cancels the frequency Jacobian. -/
theorem eLpNorm_normalized_linear_kernel {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {K : EuclideanSpace ℝ (Fin n) → ℂ} (hK : Measurable K) :
    eLpNorm (fun x => |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| •
      K (A.symm.toLinearEquiv.toLinearMap.adjoint x)) 1 volume = eLpNorm K 1 volume := by
  let B := A.symm.toLinearEquiv.toLinearMap.adjoint
  let d := LinearMap.det A.toLinearEquiv.toLinearMap
  have hd : d ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  have hB : LinearMap.det B = d⁻¹ := by
    rw [det_adjoint_real]
    exact A.toLinearEquiv.det_coe_symm
  have hBm : Measurable B := B.continuous_of_finiteDimensional.measurable
  have hmap : Measure.map B volume = ENNReal.ofReal |d| • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hB]; exact inv_ne_zero hd), hB, inv_inv]
  have hKB : Measurable (fun x => K (B x)) := hK.comp hBm
  change eLpNorm (|d⁻¹| • (fun x => K (B x))) 1 volume = _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (abs_nonneg _),
    eLpNorm_one_eq_lintegral_enorm hKB.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hK.aestronglyMeasurable]
  rw [← lintegral_map hK.enorm hBm, hmap, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  simp [hd]

/-- In particular, rotating and anisotropically rescaling a multiplier
does not change the L1 norm of its inverse-Fourier kernel. -/
theorem eLpNorm_fourierInv_comp_linearEquiv {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (hφ : Measurable (𝓕⁻ φ)) :
    eLpNorm (𝓕⁻ (φ ∘ A)) 1 volume = eLpNorm (𝓕⁻ φ) 1 volume := by
  have he := funext (fourierInv_comp_linearEquiv A φ)
  rw [he]
  exact eLpNorm_normalized_linear_kernel A hφ

end OAI.Analysis.Fourier.WavePackets
