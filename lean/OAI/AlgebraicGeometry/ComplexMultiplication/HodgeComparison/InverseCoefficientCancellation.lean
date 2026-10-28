import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Inverse Coefficient Cancellation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseCoefficientCancellation.CM.Construction

noncomputable section

/-! The Kähler coefficient symmetry cancels the trace and inverse-matrix
derivative terms in the weighted inverse-metric divergence. -/

theorem kahler_inverse_coefficient_cancellation {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (P : Matrix ι ι R) (A : ι → Matrix ι ι R)
    (hA : ∀ i j k, A i j k = A k j i) (k : ι) :
    ∑ i, ((P * A i).trace * P i k - (P * A i * P) i k) = 0 := by
  have hsum : (∑ i, (P * A i * P) i k) = ∑ i, (P * A i).trace * P i k := by
    calc
      _ = ∑ i, ∑ a, ∑ b, P i b * A a b i * P a k := by
        simp only [Matrix.mul_apply, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [hA i b a]
      _ = ∑ a, ∑ i, ∑ b, P i b * A a b i * P a k := Finset.sum_comm
      _ = _ := by simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_sub_distrib, ← hsum, sub_self]

def varietyHermitianMatrix (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {ι : Type*} (v : ι → V.analyticModel) (y : V.analyticModel) : Matrix ι ι ℂ :=
  fun i j => Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricHermitianPair (KahlerDifferential.CM.Construction.varietyMetricInChart V e y) (v i) (v j)

def varietyHermitianMatrixDerivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {ι : Type*} (v : ι → V.analyticModel) (y : V.analyticModel) (i : ι) : Matrix ι ι ℂ :=
  fun j k => MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun z => varietyHermitianMatrix V e v z j k) y (v i)

theorem varietyHermitian_inverse_coefficient_cancellation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V.analyticModel)
    {y : V.analyticModel} (hy : y ∈ e.target) (k : ι) :
    ∑ i, (((varietyHermitianMatrix V e v y)⁻¹ * varietyHermitianMatrixDerivative V e v y i).trace *
        (varietyHermitianMatrix V e v y)⁻¹ i k -
      ((varietyHermitianMatrix V e v y)⁻¹ * varietyHermitianMatrixDerivative V e v y i *
        (varietyHermitianMatrix V e v y)⁻¹) i k) = 0 := by
  apply kahler_inverse_coefficient_cancellation
  intro i j l
  exact MetricDerivative.CM.Construction.varietyHermitian_holomorphic_derivative V e he hy (v i) (v j) (v l)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseCoefficientCancellation.CM.Construction
