import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricCoefficientDivergence
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! # Antiholomorphic Divergence -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction

noncomputable section

/-! The conjugate coefficient identity uses the opposite directional
derivative and the transposed inverse-Hermitian indices. -/

open Filter
open scoped _root_.Topology ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

def antiholomorphicDirectionalDerivative (f : E → ℂ) (x u : E) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f x u + Complex.I * fderiv ℝ f x (Complex.I • u))

theorem antiholomorphicDirectionalDerivative_congr {f g : E → ℂ} {x : E}
    (h : f =ᶠ[𝓝 x] g) (u : E) :
    antiholomorphicDirectionalDerivative f x u = antiholomorphicDirectionalDerivative g x u := by
  rw [antiholomorphicDirectionalDerivative, antiholomorphicDirectionalDerivative, h.fderiv_eq]

theorem antiholomorphicDirectionalDerivative_star (f : E → ℂ) (x u : E) :
    antiholomorphicDirectionalDerivative (fun y => star (f y)) x u =
      star (MetricDerivative.CM.Construction.holomorphicDirectionalDerivative f x u) := by
  have hD (v : E) : fderiv ℝ (fun y => star (f y)) x v = star (fderiv ℝ f x v) := by
    exact congrArg (fun L : E →L[ℝ] ℂ => L v) (fderiv_star (𝕜 := ℝ) (f := f) (x := x))
  rw [antiholomorphicDirectionalDerivative, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative, hD, hD]
  simp only [star_mul, star_sub, star_div₀, star_one, star_ofNat,
    Complex.star_def, Complex.conj_I]
  ring

theorem varietyEuclideanMetric_weighted_inverse_antiholomorphic_divergence
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (k : Fin V.complexDimension) :
    ∑ i, antiholomorphicDirectionalDerivative
      (fun w => (Metric.CM.Construction.varietyMetricDensity V e w : ℂ) *
        (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
          (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w))⁻¹ k i)
      z (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i) = 0 := by
  let M := fun w => InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w)
  have hstar := congrArg (star : ℂ → ℂ)
    (MetricCoefficientDivergence.CM.Construction.varietyEuclideanMetric_weighted_inverse_divergence V e he hz k)
  rw [star_sum, star_zero] at hstar
  have hi (i : Fin V.complexDimension) :
      (fun w => (Metric.CM.Construction.varietyMetricDensity V e w : ℂ) * (M w)⁻¹ k i) =ᶠ[𝓝 z]
        (fun w => star ((Metric.CM.Construction.varietyMetricDensity V e w : ℂ) * (M w)⁻¹ i k)) := by
    filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with w hw
    have hP := (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_posDef V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hw).isHermitian.inv.apply k i
    rw [star_mul, show star (Metric.CM.Construction.varietyMetricDensity V e w : ℂ) =
      (Metric.CM.Construction.varietyMetricDensity V e w : ℂ) from Complex.conj_ofReal _]
    exact (congrArg ((Metric.CM.Construction.varietyMetricDensity V e w : ℂ) * ·) hP.symm).trans (mul_comm _ _)
  calc
    _ = ∑ i, star (MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
        (fun w => (Metric.CM.Construction.varietyMetricDensity V e w : ℂ) * (M w)⁻¹ i k)
        z (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [antiholomorphicDirectionalDerivative_congr (hi i), antiholomorphicDirectionalDerivative_star]
    _ = 0 := hstar

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction
