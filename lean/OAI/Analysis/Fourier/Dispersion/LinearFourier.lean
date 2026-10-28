import OAI.Analysis.Fourier.WavePackets.LinearKernel
import OAI.Analysis.Fourier.Dispersion.Frequency

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal

/-- The transpose change of spatial coordinates associated to a frequency map. -/
def adjointEquiv {n : ℕ} (A : Space n ≃L[ℝ] Space n) : Space n ≃L[ℝ] Space n :=
  { A.toLinearEquiv.toLinearMap.adjoint with
    invFun := A.symm.toLinearEquiv.toLinearMap.adjoint
    left_inv := by
      intro x
      apply ext_inner_right ℝ
      intro y
      change inner ℝ (A.symm.toLinearEquiv.toLinearMap.adjoint
        (A.toLinearEquiv.toLinearMap.adjoint x)) y = inner ℝ x y
      rw [LinearMap.adjoint_inner_left,LinearMap.adjoint_inner_left]
      simp
    right_inv := by
      intro x
      apply ext_inner_right ℝ
      intro y
      change inner ℝ (A.toLinearEquiv.toLinearMap.adjoint
        (A.symm.toLinearEquiv.toLinearMap.adjoint x)) y = inner ℝ x y
      rw [LinearMap.adjoint_inner_left,LinearMap.adjoint_inner_left]
      simp
    continuous_toFun := A.toLinearEquiv.toLinearMap.adjoint.continuous_of_finiteDimensional
    continuous_invFun := A.symm.toLinearEquiv.toLinearMap.adjoint.continuous_of_finiteDimensional }

@[simp] theorem adjointEquiv_apply {n : ℕ} (A : Space n ≃L[ℝ] Space n) (x : Space n) :
    adjointEquiv A x = A.toLinearEquiv.toLinearMap.adjoint x := rfl

@[simp] theorem adjointEquiv_symm {n : ℕ} (A : Space n ≃L[ℝ] Space n) :
    (adjointEquiv A).symm = adjointEquiv A.symm := rfl

@[simp] theorem adjointEquiv_adjointEquiv {n : ℕ} (A : Space n ≃L[ℝ] Space n) :
    adjointEquiv (adjointEquiv A) = A := by
  apply ContinuousLinearEquiv.ext
  funext x
  exact congrArg (fun T : Space n →ₗ[ℝ] Space n => T x)
    (LinearMap.adjoint_adjoint A.toLinearEquiv.toLinearMap)

theorem angularFourier_comp_linearEquiv {n : ℕ} (A : Space n ≃L[ℝ] Space n)
    (f : Space n → ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (f ∘ A) ξ = |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| •
      OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (adjointEquiv A.symm ξ) := by
  let g := fun x : Space n =>
    Complex.exp (-Complex.I * (inner ℝ (A.symm x) ξ : ℂ)) * f x
  have hchange := A.toHomeomorph.measurableEmbedding.integral_map (μ := volume) g
  change (∫ x, g x ∂Measure.map A volume) = ∫ x, g (A x) at hchange
  have hd := A.toLinearEquiv.isUnit_det'.ne_zero
  have hmap : Measure.map A volume =
      ENNReal.ofReal |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  rw [hmap,integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)] at hchange
  calc
    _ = ∫ x, g (A x) := by simp [g,OAI.Analysis.Fourier.LocalSmoothing.angularFourier]
    _ = |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • ∫ x, g x := hchange.symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [g,adjointEquiv_apply,LinearMap.adjoint_inner_right]
      rfl

theorem angularInverse_comp_linearEquiv {n : ℕ} (A : Space n ≃L[ℝ] Space n)
    (f : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (f ∘ A) x = |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| •
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse f (adjointEquiv A.symm x) := by
  let g := fun ξ : Space n =>
    Complex.exp (Complex.I * (inner ℝ x (A.symm ξ) : ℂ)) * f ξ
  have hchange := A.toHomeomorph.measurableEmbedding.integral_map (μ := volume) g
  change (∫ ξ, g ξ ∂Measure.map A volume) = ∫ ξ, g (A ξ) at hchange
  have hd := A.toLinearEquiv.isUnit_det'.ne_zero
  have hmap : Measure.map A volume =
      ENNReal.ofReal |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  rw [hmap,integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)] at hchange
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  rw [smul_comm |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹|]
  congr 1
  calc
    _ = ∫ ξ, g (A ξ) := by simp [g]
    _ = |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • ∫ ξ, g ξ := hchange.symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [g,adjointEquiv_apply,LinearMap.adjoint_inner_left]
      rfl

/-- The exact L¹ invariance needed for anisotropic low-frequency kernels. -/
theorem eLpNorm_angularInverse_comp_linearEquiv {n : ℕ}
    (A : Space n ≃L[ℝ] Space n) (f : Space n → ℂ)
    (hf : Measurable (OAI.Analysis.Fourier.LocalSmoothing.angularInverse f)) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (f ∘ A)) 1 volume = eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse f) 1 volume := by
  rw [show OAI.Analysis.Fourier.LocalSmoothing.angularInverse (f ∘ A) = fun x =>
      |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • OAI.Analysis.Fourier.LocalSmoothing.angularInverse f (adjointEquiv A.symm x)
      from funext (angularInverse_comp_linearEquiv A f)]
  exact OAI.Analysis.Fourier.WavePackets.eLpNorm_normalized_linear_kernel A hf

end OAI.Analysis.Fourier.Dispersion
