import OAI.RepresentationTheory.Weil.Local.ComplexFourierStandard
import OAI.RepresentationTheory.Weil.Local.FourierTensor

/-! # Complex Standard Normalization -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexStandardNormalization.Construction

noncomputable section

/-! Tensor calibration of complex Fourier inversion for the actual product
of the prescribed one-dimensional self-dual measures. -/

open _root_.MeasureTheory
open scoped FourierTransform ComplexConjugate NNReal SchwartzMap ContDiff

theorem complex_fourier_square_with_factor (n : ℕ)
    (f : SchwartzMap (FunctionsMetaplectic.Construction.Position ℂ n) ℂ) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume
      (FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f) x =
      (ComplexFourierStandard.Construction.complexPositionHaarFactor n : ℂ) ^ 2 * f (-x) := by
  have hf : (ComplexFourierStandard.Construction.complexSchwartzFourier n f : FunctionsMetaplectic.Construction.Position ℂ n → ℂ) =
      FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f :=
    funext (ComplexFourierStandard.Construction.complexSchwartzFourier_apply n f)
  rw [← hf, ← ComplexFourierStandard.Construction.complexSchwartzFourier_apply, ComplexFourierStandard.Construction.complexSchwartzFourier_square]

theorem complexPositionHaarFactor_one (n : ℕ) : ComplexFourierStandard.Construction.complexPositionHaarFactor n = 1 := by
  let b : ContDiffBump (0 : ℂ) := default
  let φ : ℂ → ℂ := fun z => (b z : ℂ)
  have hφs : HasCompactSupport φ := b.hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ) = 0 from rfl)
  have hφc : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : SchwartzMap ℂ ℂ := hφs.toSchwartzMap hφc
  have hf0 : f 0 = 1 := by
    change (b 0 : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    rfl
  have htc : ContDiff ℝ ∞ (FourierTensor.Construction.tensorFunction n φ) := by
    apply contDiff_prod
    intro i _
    exact hφc.comp (ContinuousLinearMap.proj i : FunctionsMetaplectic.Construction.Position ℂ n →L[ℝ] ℂ).contDiff
  let g : SchwartzMap (FunctionsMetaplectic.Construction.Position ℂ n) ℂ :=
    (FourierTensor.Construction.tensorFunction_compactSupport n hφs).toSchwartzMap htc
  have he := complex_fourier_square_with_factor n g 0
  have hg0 : g (-0) = 1 := by
    have hφ0 : φ 0 = 1 := hf0
    simp [g, FourierTensor.Construction.tensorFunction, hφ0]
  rw [hg0, mul_one] at he
  change FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter (Measure.pi (fun _ : Fin n => volume))
    (FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter (Measure.pi (fun _ : Fin n => volume))
      (FourierTensor.Construction.tensorFunction n f)) 0 = (ComplexFourierStandard.Construction.complexPositionHaarFactor n : ℂ) ^ 2 at he
  rw [FourierTensor.Construction.fourierIntegral_tensorFunction, FourierTensor.Construction.fourierIntegral_tensorFunction] at he
  change (∏ _ : Fin n, FourierTensor.Construction.scalarFourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume
    (FourierTensor.Construction.scalarFourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f) 0) = _ at he
  simp only [ComplexFourierStandard.Construction.scalarFourierIntegral_complex_standard_square, neg_zero, hf0, Finset.prod_const_one] at he
  have hr : (ComplexFourierStandard.Construction.complexPositionHaarFactor n : ℝ) ^ 2 = 1 ^ 2 := by
    simpa only [one_pow] using (show (ComplexFourierStandard.Construction.complexPositionHaarFactor n : ℝ) ^ 2 = 1 by exact_mod_cast he.symm)
  have h := (sq_eq_sq₀ (ComplexFourierStandard.Construction.complexPositionHaarFactor n).coe_nonneg (by norm_num)).mp hr
  exact NNReal.coe_injective h

theorem complex_fourier_inversion_standard (n : ℕ)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume
      (FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f.val) x = f.val (-x) := by
  obtain ⟨φ, hφ⟩ := ArchimedeanTestSpace.Construction.schwartzBruhat_archimedean_iff.mp f.property
  rw [hφ, complex_fourier_square_with_factor, complexPositionHaarFactor_one]
  simp

theorem complex_fourier_mem_standard (n : ℕ) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat ℂ n := by
  obtain ⟨φ, hφ⟩ := ArchimedeanTestSpace.Construction.schwartzBruhat_archimedean_iff.mp f.property
  refine ArchimedeanTestSpace.Construction.schwartzBruhat_archimedean_iff.mpr ⟨ComplexFourierStandard.Construction.complexSchwartzFourier n φ, ?_⟩
  rw [hφ]
  exact (funext (ComplexFourierStandard.Construction.complexSchwartzFourier_apply n φ)).symm

theorem positionMeasure_complex_standard (n : ℕ) :
    FunctionsMetaplectic.Construction.positionMeasure ℂ n ArchimedeanTestSpace.Construction.complexStandardCharacter = volume := by
  simp [FunctionsMetaplectic.Construction.positionMeasure, ComplexFourierStandard.Construction.selfDualMeasure_complex_standard, volume_pi]

theorem complex_fourier_inversion_selfDual (n : ℕ)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter (FunctionsMetaplectic.Construction.positionMeasure ℂ n ArchimedeanTestSpace.Construction.complexStandardCharacter)
      (FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter (FunctionsMetaplectic.Construction.positionMeasure ℂ n ArchimedeanTestSpace.Construction.complexStandardCharacter) f.val) x =
      f.val (-x) := by
  rw [positionMeasure_complex_standard]
  exact complex_fourier_inversion_standard n f x

end

end OAI.RepresentationTheory.Weil.Local.ComplexStandardNormalization.Construction
