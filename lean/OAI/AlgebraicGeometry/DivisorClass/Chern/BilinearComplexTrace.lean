import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTensorAlgebra

/-! # Bilinear Complex Trace -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.BilinearComplexTrace

noncomputable section

section

/-! Moving the complex structure between the two slots of the inverse-metric tensor trace. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem bilinear_trace_basis_transport (b : Module.Basis ι ℝ E)
    (S : (E →L[ℝ] ℝ) →L[ℝ] E) (L : E →L[ℝ] E) (T : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) :
    (∑ i, T (S ((b.coord i).toContinuousLinearMap.comp L)) (b i)) =
      ∑ i, T (S (b.coord i).toContinuousLinearMap) (L (b i)) := by
  have hS (i : ι) : S ((b.coord i).toContinuousLinearMap.comp L) =
      ∑ j, b.repr (L (b j)) i • S (b.coord j).toContinuousLinearMap := by
    have h := congrArg S (Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions.continuousCovector_basis_expansion b ((b.coord i).toContinuousLinearMap.comp L))
    simp only [map_sum, map_smul, ContinuousLinearMap.comp_apply] at h
    exact h
  simp only [hS, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg (T (S (b.coord j).toContinuousLinearMap)) (b.sum_repr (L (b j)))
  simpa only [map_sum, map_smul] using h

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem bilinear_metric_trace_J (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (hBJ : ∀ v w, B (Complex.I • v) w = -B v (Complex.I • w))
    (T : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) :
    (∑ i, T (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) (b i)) =
      -(∑ i, T (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) (Complex.I • b i)) := by
  have h := bilinear_trace_basis_transport b (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) T
  simp only [Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions.bilinearMetricSharp_comp_J B hpos hBJ, map_neg, LinearMap.neg_apply,
    Finset.sum_neg_distrib, ContinuousLinearMap.lsmul_apply] at h
  simpa only [neg_neg] using congrArg Neg.neg h

end

/-! Symmetry and complex-structure cancellation for the original inverse-metric trace of a complex bilinear tensor. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι κ : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem bilinearMetric_complex_trace_orthogonal (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (b : Module.Basis ι ℝ E) (c : Module.Basis κ ℝ E)
    (hc : ∀ j k, B (c j) (c k) = if j = k then 1 else 0) (T : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) :
    (∑ i, T (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) (b i)) = ∑ j, T (c j) (c j) := by
  have hs (i : ι) : Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap =
      ∑ j, b.coord i (c j) • c j := by
    have hh := Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions.bilinearMetricSharp_dual_expansion B c (b.coord i).toContinuousLinearMap
    simp only [Positive.MetricTrace.orthogonalBasis_metric_sharp B hpos c hc] at hh
    exact hh.symm
  simp only [hs, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hh := congrArg (T (c j)) (b.sum_repr (c j))
  simpa only [map_sum, map_smul, Module.Basis.coord_apply] using hh

omit [Fintype κ] [DecidableEq κ] in
theorem bilinearMetric_complex_trace_flip (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (b : Module.Basis ι ℝ E) (T : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) :
    (∑ i, T (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) (b i)) =
      ∑ i, T (b i) (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) := by
  let F := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.RealMetricFiber E (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)
  let L := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.realMetricFiberContinuousEquiv (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)
  let o := stdOrthonormalBasis ℝ F
  let c := o.toBasis.map L.toLinearEquiv
  have hc (j k) : B (c j) (c k) = if j = k then 1 else 0 := o.inner_eq_ite j k
  exact (bilinearMetric_complex_trace_orthogonal B hpos b c hc T).trans
    (bilinearMetric_complex_trace_orthogonal B hpos b c hc T.flip).symm

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [Fintype κ] [DecidableEq κ] in
theorem bilinearMetric_complex_trace_J_skew (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (hBJ : ∀ v w, B (Complex.I • v) w = -B v (Complex.I • w))
    (b : Module.Basis ι ℝ E) (T : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) :
    (∑ i, T (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) (b i)) =
      -(∑ i, T (b i) (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)) := by
  let J := (ContinuousLinearMap.lsmul ℝ ℂ Complex.I : E →L[ℝ] E).toLinearMap
  let U : E →ₗ[ℝ] E →ₗ[ℝ] ℂ := (LinearMap.llcomp ℝ E E ℂ).flip J |>.comp T
  have hf := bilinearMetric_complex_trace_flip B hB hpos b U
  exact (bilinear_metric_trace_J b B hpos hBJ T).trans (congrArg Neg.neg hf)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.BilinearComplexTrace
