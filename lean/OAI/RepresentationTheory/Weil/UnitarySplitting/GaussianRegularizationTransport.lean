import OAI.RepresentationTheory.Weil.UnitarySplitting.ComplexGaussianFourier

/-! # Gaussian Regularization Transport -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting

noncomputable section

/-! Coordinate changes and positive Haar rescalings of Gaussian regularizations. -/

open _root_.MeasureTheory Filter _root_.Topology
open scoped NNReal

def ComplexGaussianFourier.Construction.GaussianFourierRegularization.comp_right {V : Type} [TopologicalSpace V] [MeasurableSpace V]
    {μ : Measure V} {phase dual : V → ℂ} {kernel : V → V → ℂ} {Γ : ℂ}
    (R : ComplexGaussianFourier.Construction.GaussianFourierRegularization μ phase dual kernel Γ)
    (L : V → V) (hL : Continuous L) :
    ComplexGaussianFourier.Construction.GaussianFourierRegularization μ phase (fun w => dual (L w))
      (fun v w => kernel v (L w)) Γ where
  gaussian := R.gaussian
  transform ε w := R.transform ε (L w)
  bound := R.bound
  bound_pos := R.bound_pos
  kernel_continuous := R.kernel_continuous.comp (continuous_fst.prodMk (hL.comp continuous_snd))
  kernel_norm := fun v w => R.kernel_norm v (L w)
  gaussian_continuous := R.gaussian_continuous
  gaussian_integrable := R.gaussian_integrable
  gaussian_norm := R.gaussian_norm
  gaussian_limit := R.gaussian_limit
  transform_continuous := fun ε => (R.transform_continuous ε).comp hL
  transform_bound := fun ε hε w => R.transform_bound ε hε (L w)
  transform_limit := fun w => R.transform_limit (L w)
  integral_transform := fun ε hε w => R.integral_transform ε hε (L w)

def ComplexGaussianFourier.Construction.GaussianFourierRegularization.smul_measure {V : Type} [TopologicalSpace V] [MeasurableSpace V]
    {μ : Measure V} {phase dual : V → ℂ} {kernel : V → V → ℂ} {Γ : ℂ}
    (R : ComplexGaussianFourier.Construction.GaussianFourierRegularization μ phase dual kernel Γ) (c : ℝ≥0) (hc : 0 < c) :
    ComplexGaussianFourier.Construction.GaussianFourierRegularization (c • μ) phase dual kernel ((c : ℂ) * Γ) where
  gaussian := R.gaussian
  transform ε w := (c : ℂ) * R.transform ε w
  bound := c * R.bound
  bound_pos := mul_pos hc R.bound_pos
  kernel_continuous := R.kernel_continuous
  kernel_norm := R.kernel_norm
  gaussian_continuous := R.gaussian_continuous
  gaussian_integrable := fun ε hε => (R.gaussian_integrable ε hε).smul_measure_nnreal
  gaussian_norm := R.gaussian_norm
  gaussian_limit := R.gaussian_limit
  transform_continuous := fun ε => continuous_const.mul (R.transform_continuous ε)
  transform_bound := by
    intro ε hε w
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg c.coe_nonneg]
    exact mul_le_mul_of_nonneg_left (R.transform_bound ε hε w) c.coe_nonneg
  transform_limit := by
    intro w
    simpa only [mul_assoc] using tendsto_const_nhds.mul (R.transform_limit w)
  integral_transform := by
    intro ε hε w
    rw [integral_smul_nnreal_measure, R.integral_transform ε hε w, NNReal.smul_def, Complex.real_smul]

def ComplexGaussianFourier.Construction.GaussianFourierRegularization.homeomorph {V W : Type} [TopologicalSpace V] [TopologicalSpace W]
    [MeasurableSpace V] [MeasurableSpace W] [BorelSpace V] [BorelSpace W]
    {μ : Measure V} {ν : Measure W} {phase dual : W → ℂ} {kernel : W → W → ℂ} {Γ : ℂ}
    (R : ComplexGaussianFourier.Construction.GaussianFourierRegularization ν phase dual kernel Γ)
    (e : V ≃ₜ W) (he : μ.map e = ν) :
    ComplexGaussianFourier.Construction.GaussianFourierRegularization μ (fun v => phase (e v)) (fun w => dual (e w))
      (fun v w => kernel (e v) (e w)) Γ where
  gaussian ε v := R.gaussian ε (e v)
  transform ε w := R.transform ε (e w)
  bound := R.bound
  bound_pos := R.bound_pos
  kernel_continuous := R.kernel_continuous.comp
    ((e.continuous.comp continuous_fst).prodMk (e.continuous.comp continuous_snd))
  kernel_norm := fun v w => R.kernel_norm (e v) (e w)
  gaussian_continuous := fun ε => (R.gaussian_continuous ε).comp e.continuous
  gaussian_integrable := by
    intro ε hε
    have hp : MeasurePreserving e μ ν := ⟨e.measurable, he⟩
    exact hp.integrable_comp_of_integrable (R.gaussian_integrable ε hε)
  gaussian_norm := fun ε hε v => R.gaussian_norm ε hε (e v)
  gaussian_limit := fun v => R.gaussian_limit (e v)
  transform_continuous := fun ε => (R.transform_continuous ε).comp e.continuous
  transform_bound := fun ε hε w => R.transform_bound ε hε (e w)
  transform_limit := fun w => R.transform_limit (e w)
  integral_transform := by
    intro ε hε w
    calc
      _ = ∫ v, R.gaussian ε v * kernel v (e w) ∂μ.map e :=
        (e.isClosedEmbedding.integral_map _).symm
      _ = ∫ v, R.gaussian ε v * kernel v (e w) ∂ν := by rw [he]
      _ = _ := R.integral_transform ε hε (e w)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting
