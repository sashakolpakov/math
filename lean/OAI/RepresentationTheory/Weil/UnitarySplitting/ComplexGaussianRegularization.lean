import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianRegularizationProducts

/-! # Complex Gaussian Regularization -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ComplexGaussianRegularization.Construction

noncomputable section

/-! The complex norm Gaussian supplies the one-coordinate regularization. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

def complexNormGaussianRegularization (t : ℝ) (ht : t ≠ 0) :
    ComplexGaussianFourier.Construction.GaussianFourierRegularization (volume : Measure ℂ)
      (fun z => Complex.exp (Complex.I * t * (Complex.normSq z : ℂ)))
      (fun w => Complex.exp (-Complex.I * t * (Complex.normSq w : ℂ)))
      (fun z w => Complex.exp (2 * Complex.I * t * (inner ℝ w z : ℂ)))
      (ComplexGaussianFourier.Construction.complexNormGaussianValue t) where
  gaussian := ComplexGaussianFourier.Construction.complexDampedNormGaussian t
  transform := ComplexGaussianFourier.Construction.complexDampedNormTransform t
  bound := Real.pi / |t|
  bound_pos := div_pos Real.pi_pos (abs_pos.mpr ht)
  kernel_continuous := by fun_prop
  kernel_norm := fun z w => ComplexGaussianFourier.Construction.complexNormBilinearPhase_norm t w z
  gaussian_continuous := ComplexGaussianFourier.Construction.complexDampedNormGaussian_continuous t
  gaussian_integrable := ComplexGaussianFourier.Construction.complexDampedNormGaussian_integrable t
  gaussian_norm := fun ε hε => ComplexGaussianFourier.Construction.complexDampedNormGaussian_norm_le_one t ε hε.le
  gaussian_limit := ComplexGaussianFourier.Construction.complexDampedNormGaussian_tendsto t
  transform_continuous := ComplexGaussianFourier.Construction.complexDampedNormTransform_continuous t
  transform_bound := fun ε hε => ComplexGaussianFourier.Construction.complexDampedNormTransform_norm_le t ε ht hε.le
  transform_limit := ComplexGaussianFourier.Construction.complexDampedNormTransform_tendsto t ht
  integral_transform := ComplexGaussianFourier.Construction.complex_damped_norm_fourier t

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ComplexGaussianRegularization.Construction
