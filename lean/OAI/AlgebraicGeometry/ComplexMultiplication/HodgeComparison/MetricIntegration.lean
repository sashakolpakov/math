import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricJacobian
import Mathlib.MeasureTheory.Function.Jacobian

/-! # Metric Integration -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricIntegration.CM.Construction

noncomputable section

/-! Change of coordinates for integration against the actual projective metric. -/

open scoped ContDiff _root_.Manifold ENNReal
open Set _root_.MeasureTheory

theorem varietyEuclideanTransition_injOn (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {S : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (heS : S ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hfS : ∀ z ∈ S, e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ f.source) :
    InjOn (MetricJacobian.CM.Construction.varietyEuclideanTransition V e f) S := by
  intro z hz w hw h
  apply (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).injective
  apply e.symm.injOn (heS hz) (heS hw)
  apply f.injOn (hfS z hz) (hfS w hw)
  exact (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.injective h

theorem varietyEuclideanTransition_inverse_point (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hfz : e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ f.source) :
    f.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (MetricJacobian.CM.Construction.varietyEuclideanTransition V e f z)) =
      e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) := by
  simp only [MetricJacobian.CM.Construction.varietyEuclideanTransition, Function.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply, f.left_inv hfz]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrals of a manifold function, computed with the genuine metric density,
agree in overlapping Euclidean chart coordinates. -/
theorem varietyMetric_integral_transition (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    {S : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hS : MeasurableSet S)
    (heS : S ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hfS : ∀ z ∈ S, e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ f.source)
    (h : V.analyticSpace → F) :
    (∫ w in MetricJacobian.CM.Construction.varietyEuclideanTransition V e f '' S,
      Metric.CM.Construction.varietyMetricDensity V f w • h (f.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w))) =
    ∫ z in S, Metric.CM.Construction.varietyMetricDensity V e z • h (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun z hz => (MetricJacobian.CM.Construction.varietyEuclideanTransition_hasFDerivAt V e f he hf (heS hz) (hfS z hz)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (varietyEuclideanTransition_injOn V e f heS hfS)]
  apply setIntegral_congr_fun hS
  intro z hz
  dsimp only
  rw [varietyEuclideanTransition_inverse_point V e f (hfS z hz), smul_smul,
    ← MetricJacobian.CM.Construction.varietyMetricDensity_transition V e f he hf (heS hz) (hfS z hz)]

/-- The nonnegative integration identity, used to compare the local volume measures. -/
theorem varietyMetric_lintegral_transition (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    {S : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hS : MeasurableSet S)
    (heS : S ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hfS : ∀ z ∈ S, e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ f.source)
    (h : V.analyticSpace → ℝ≥0∞) :
    (∫⁻ w in MetricJacobian.CM.Construction.varietyEuclideanTransition V e f '' S,
      ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V f w) * h (f.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w))) =
    ∫⁻ z in S, ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z) * h (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun z hz => (MetricJacobian.CM.Construction.varietyEuclideanTransition_hasFDerivAt V e f he hf (heS hz) (hfS z hz)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (varietyEuclideanTransition_injOn V e f heS hfS)]
  apply setLIntegral_congr_fun hS
  intro z hz
  dsimp only
  rw [varietyEuclideanTransition_inverse_point V e f (hfS z hz), ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _),
    ← MetricJacobian.CM.Construction.varietyMetricDensity_transition V e f he hf (heS hz) (hfS z hz)]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricIntegration.CM.Construction
