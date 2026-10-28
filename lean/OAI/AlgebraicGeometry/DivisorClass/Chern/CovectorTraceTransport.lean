import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorNeg

/-! # Covector Trace Transport -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTraceTransport

noncomputable section

/-! Moving a tangent endomorphism across the actual inverse-metric covector trace. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem covector_trace_basis_transport (b : Module.Basis ι ℝ E) (n : ℕ)
    (S : (E →L[ℝ] ℝ) →L[ℝ] E) (T : E →L[ℝ] E) (R : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    (∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (S ((b.coord i).toContinuousLinearMap.comp T)) (R (b i))) =
      ∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (S (b.coord i).toContinuousLinearMap) (R (T (b i))) := by
  have hS (i : ι) : S ((b.coord i).toContinuousLinearMap.comp T) =
      ∑ j, b.repr (T (b j)) i • S (b.coord j).toContinuousLinearMap := by
    have h := congrArg S (Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions.continuousCovector_basis_expansion b ((b.coord i).toContinuousLinearMap.comp T))
    simp only [map_sum, map_smul, ContinuousLinearMap.comp_apply] at h
    exact h
  simp_rw [hS, Analysis.HodgeTheory.Decomposition.BivectorContraction.Constructions.exteriorContraction_sum_vector, Analysis.HodgeTheory.Decomposition.ContractionAlgebra.Constructions.exteriorContraction_smul_vector]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hr : (∑ i, b.repr (T (b j)) i • R (b i)) = R (T (b j)) := by
    simpa only [map_sum, map_smul] using congrArg R (b.sum_repr (T (b j)))
  rw [← hr, map_sum]
  simp only [map_smul]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTraceTransport
