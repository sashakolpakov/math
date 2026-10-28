import OAI.Analysis.HodgeTheory.Decomposition.WeightedMetricDerivative
import OAI.Analysis.HodgeTheory.Decomposition.ConnectionSymbolTrace

/-! # Covariant Adjoint Pair -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CovariantAdjointPair.Constructions

noncomputable section

/-! The density-weighted formal adjoint is contraction of the covariant
derivative. All volume and connection zero-order terms cancel explicitly. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def bilinearCovariantCodifferential (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (x : E) : DifferentialForms.Manifold.Basic.FormValue E n :=
  -∑ i, SymbolDifferential.Constructions.exteriorContraction n (KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)
    (CovectorConnection.Constructions.covectorConnectionDerivative (n + 1) Γ a x (b i))

theorem covariantAdjointPair_derivative_sum (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (c : DifferentialForms.Manifold.Basic.FormValue E n) {x : E}
    (hB : DifferentiableAt ℝ B x) (ha : DifferentiableAt ℝ a x)
    (hρ : DifferentiableAt ℝ (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y)) x)
    (hBs : ∀ v w, B x v w = B x w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hΓ : ∀ u v w, B x (Γ x u v) w + B x v (Γ x u w) = fderiv ℝ B x u v w)
    (hΓs : ∀ u v, Γ x u v = Γ x v u) :
    (∑ i, fderiv ℝ (fun y => (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y) : ℂ) *
      BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (B y) (a y)
        (SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c)) x (b i)) =
      -(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) *
        BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (bilinearCovariantCodifferential b n B Γ a x) c := by
  simp_rw [WeightedMetricDerivative.Constructions.weightedMetricPair_derivative b (n + 1) B Γ a _ _ hB ha hρ hBs hpos (hΓ _)]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have ht : (∑ i, BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (B x) (a x)
      (CovectorConnection.Constructions.covectorInfinitesimalAction (n + 1) (Γ x (b i))
        (SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c))) =
      ∑ i, (LinearMap.toMatrix b b (Γ x (b i)).toLinearMap).trace •
        BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (B x) (a x)
          (SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c) := by
    rw [← BilinearPairAlgebra.Constructions.bilinearFormMetricPair_sum_right, ConnectionSymbolTrace.Constructions.symmetricConnection_symbol_trace b n (Γ x) hΓs c,
      BilinearPairAlgebra.Constructions.bilinearFormMetricPair_sum_right]
    simp only [BilinearPairAlgebra.Constructions.bilinearFormMetricPair_real_smul_right]
  rw [ht, sub_add_cancel]
  simp_rw [BilinearPairAlgebra.Constructions.bilinearFormMetricPair_exteriorSymbol_right b n (B x) hBs hpos]
  rw [← BilinearPairAlgebra.Constructions.bilinearFormMetricPair_sum_left, bilinearCovariantCodifferential,
    BilinearPairAlgebra.Constructions.bilinearFormMetricPair_neg_left, neg_mul_neg]

end

end OAI.Analysis.HodgeTheory.Decomposition.CovariantAdjointPair.Constructions
