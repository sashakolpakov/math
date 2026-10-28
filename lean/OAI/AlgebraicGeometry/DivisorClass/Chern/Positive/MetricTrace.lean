import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorMetricSharp

/-! # Metric Trace -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.MetricTrace

noncomputable section

/-! Contraction by a positive tangent metric preserves nonnegativity of a real bilinear form. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι κ : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [FiniteDimensional ℝ E] [Fintype κ] in
theorem orthogonalBasis_metric_coordinate (B : E →L[ℝ] E →L[ℝ] ℝ) (b : Module.Basis κ ℝ E)
    (hb : ∀ j k, B (b j) (b k) = if j = k then 1 else 0) (j : κ) (v : E) :
    B (b j) v = b.coord j v := by
  have h : (B (b j)).toLinearMap = b.coord j := by
    apply b.ext
    intro k
    simp only [ContinuousLinearMap.coe_coe, hb, Module.Basis.coord_apply, Module.Basis.repr_self_apply, eq_comm]
  exact congrArg (fun L : E →ₗ[ℝ] ℝ => L v) h

omit [Fintype ι] [Fintype κ] in
theorem orthogonalBasis_metric_sharp (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (b : Module.Basis κ ℝ E)
    (hb : ∀ j k, B (b j) (b k) = if j = k then 1 else 0) (j : κ) :
    Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap = b j := by
  apply Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.positive_bilinear_left_ext B hpos
  intro v
  rw [Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos, orthogonalBasis_metric_coordinate B b hb]
  rfl

theorem bilinearMetric_trace_orthogonal (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (b : Module.Basis ι ℝ E) (c : Module.Basis κ ℝ E)
    (hc : ∀ j k, B (c j) (c k) = if j = k then 1 else 0) (T : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    (∑ i, T (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) (b i)) = ∑ j, T (c j) (c j) := by
  have hs (i : ι) : Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap =
      ∑ j, b.coord i (c j) • c j := by
    have h := Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions.bilinearMetricSharp_dual_expansion B c (b.coord i).toContinuousLinearMap
    simp only [orthogonalBasis_metric_sharp B hpos c hc] at h
    exact h.symm
  simp only [hs, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg (T (c j)) (b.sum_repr (c j))
  simpa only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply] using h

omit [Fintype κ] [DecidableEq κ] in
theorem bilinearMetric_trace_nonneg (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (b : Module.Basis ι ℝ E) (T : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hT : ∀ v, 0 ≤ T v v) :
    0 ≤ ∑ i, T (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) (b i) := by
  let F := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.RealMetricFiber E (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)
  let L := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.realMetricFiberContinuousEquiv (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)
  let o := stdOrthonormalBasis ℝ F
  let c := o.toBasis.map L.toLinearEquiv
  have hc (j k) : B (c j) (c k) = if j = k then 1 else 0 := by
    exact o.inner_eq_ite j k
  rw [bilinearMetric_trace_orthogonal B hpos b c hc]
  exact Finset.sum_nonneg (fun j _ => hT (c j))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.MetricTrace
