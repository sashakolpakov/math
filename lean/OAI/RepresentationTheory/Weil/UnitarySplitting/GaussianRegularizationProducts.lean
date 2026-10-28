import OAI.RepresentationTheory.Weil.UnitarySplitting.ComplexGaussianFourier
import Mathlib.MeasureTheory.Integral.Pi

/-! # Gaussian Regularization Products -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting

noncomputable section

/-! Gaussian Fourier regularizations multiply over independent coordinates. -/

open _root_.MeasureTheory Filter _root_.Topology
open scoped BigOperators

def ComplexGaussianFourier.Construction.GaussianFourierRegularization.finite_product {I V : Type} [Fintype I] [TopologicalSpace V] [MeasurableSpace V]
    (μ : I → Measure V) [∀ i, SigmaFinite (μ i)]
    (phase dual : I → V → ℂ) (kernel : I → V → V → ℂ) (Γ : I → ℂ)
    (R : ∀ i, ComplexGaussianFourier.Construction.GaussianFourierRegularization (μ i) (phase i) (dual i) (kernel i) (Γ i)) :
    ComplexGaussianFourier.Construction.GaussianFourierRegularization (Measure.pi μ)
      (fun v => ∏ i, phase i (v i)) (fun w => ∏ i, dual i (w i))
      (fun v w => ∏ i, kernel i (v i) (w i)) (∏ i, Γ i) where
  gaussian ε v := ∏ i, (R i).gaussian ε (v i)
  transform ε w := ∏ i, (R i).transform ε (w i)
  bound := ∏ i, (R i).bound
  bound_pos := Finset.prod_pos fun i _ => (R i).bound_pos
  kernel_continuous := by
    apply continuous_finsetProd
    intro i _
    have hc : Continuous (fun p : (I → V) × (I → V) => (p.1 i, p.2 i)) := by fun_prop
    exact (R i).kernel_continuous.comp hc
  kernel_norm := by
    intro v w
    rw [norm_prod]
    simp only [(R _).kernel_norm, Finset.prod_const_one]
  gaussian_continuous := by
    intro ε
    exact continuous_finsetProd _ fun i _ => ((R i).gaussian_continuous ε).comp (continuous_apply i)
  gaussian_integrable := fun ε hε => Integrable.fintype_prod fun i => (R i).gaussian_integrable ε hε
  gaussian_norm := by
    intro ε hε v
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => (R i).gaussian_norm ε hε (v i))
  gaussian_limit := by
    intro v
    exact tendsto_finsetProd _ fun i _ => (R i).gaussian_limit (v i)
  transform_continuous := by
    intro ε
    exact continuous_finsetProd _ fun i _ => ((R i).transform_continuous ε).comp (continuous_apply i)
  transform_bound := by
    intro ε hε w
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => (R i).transform_bound ε hε (w i))
  transform_limit := by
    intro w
    simpa only [Finset.prod_mul_distrib] using
      (tendsto_finsetProd Finset.univ fun i _ => (R i).transform_limit (w i))
  integral_transform := by
    intro ε hε w
    simp only [← Finset.prod_mul_distrib]
    calc
      _ = ∏ i, ∫ v, (R i).gaussian ε v * kernel i v (w i) ∂μ i :=
        integral_fintype_prod_eq_prod (fun i v => (R i).gaussian ε v * kernel i v (w i))
      _ = _ := Finset.prod_congr rfl fun i _ => (R i).integral_transform ε hε (w i)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting
