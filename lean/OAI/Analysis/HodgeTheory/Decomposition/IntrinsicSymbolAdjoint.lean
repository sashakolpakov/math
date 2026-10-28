import OAI.Analysis.HodgeTheory.Decomposition.MetricDualBasisForms
import OAI.Analysis.HodgeTheory.Decomposition.ComplexMetric

/-! # Intrinsic Symbol Adjoint -/

namespace OAI.Analysis.HodgeTheory.Decomposition.IntrinsicSymbolAdjoint.Constructions

noncomputable section

/-! Exterior multiplication is adjoint to insertion of the metric-dual
vector for the intrinsic pairing on all genuine alternating covectors. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem formMetricPair_exteriorSymbol_inner (n : ℕ) (w : E)
    (a : DifferentialForms.Manifold.Basic.FormValue E n) (c : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    ExteriorPair.Constructions.formMetricPair (n + 1) (SymbolDifferential.Constructions.exteriorDifferentialSymbol n (innerSL ℝ w) a) c =
      ExteriorPair.Constructions.formMetricPair n a (SymbolDifferential.Constructions.exteriorContraction n w c) := by
  rw [MetricDualBasisForms.Constructions.metricDualTuple_basis_expansion (stdOrthonormalBasis ℝ E) n a,
    map_sum, MetricDualBasisForms.Constructions.formMetricPair_sum_left, MetricDualBasisForms.Constructions.formMetricPair_sum_left]
  apply Finset.sum_congr rfl
  intro s _
  rw [ComplexMetric.Constructions.exteriorDifferentialSymbol_complex_smul, UnitaryTypes.Constructions.formMetricPair_smul_left, UnitaryTypes.Constructions.formMetricPair_smul_left,
    MetricDualForms.Constructions.exteriorSymbol_metricDualTuple, MetricDualForms.Constructions.metricDualTupleForm_pair, MetricDualForms.Constructions.metricDualTupleForm_pair]
  rfl

theorem formMetricPair_exteriorSymbol (n : ℕ) (ξ : E →L[ℝ] ℝ)
    (a : DifferentialForms.Manifold.Basic.FormValue E n) (c : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    ExteriorPair.Constructions.formMetricPair (n + 1) (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a) c =
      ExteriorPair.Constructions.formMetricPair n a (SymbolDifferential.Constructions.exteriorContraction n ((InnerProductSpace.toDual ℝ E).symm ξ) c) := by
  have hξ : innerSL ℝ ((InnerProductSpace.toDual ℝ E).symm ξ) = ξ := by
    ext v
    exact InnerProductSpace.toDual_symm_apply
  have h := formMetricPair_exteriorSymbol_inner n ((InnerProductSpace.toDual ℝ E).symm ξ) a c
  rw [hξ] at h
  exact h

end

end OAI.Analysis.HodgeTheory.Decomposition.IntrinsicSymbolAdjoint.Constructions
