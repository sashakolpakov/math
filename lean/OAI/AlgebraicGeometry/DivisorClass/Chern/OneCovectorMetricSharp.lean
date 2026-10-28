import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormCoordinates
import OAI.Analysis.HodgeTheory.Decomposition.MetricDualBasis
import OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetric
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorPair

/-! # One Covector Metric Sharp -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorMetricSharp

noncomputable section

/-! The original degree-one metric pairing is evaluation on the actual metric-dual real and imaginary covectors. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorPair.CM.Construction

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [Fintype ι] [LinearOrder ι] in
theorem metricDualVector_eq_sharp (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (ξ : E →L[ℝ] ℝ) :
    ComplexMultiplication.HodgeComparison.CovectorMetric.CM.Construction.metricDualVector B ξ = Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B ξ := by
  apply Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.positive_bilinear_left_ext B hpos
  intro w
  rw [ComplexMultiplication.HodgeComparison.CovectorMetric.CM.Construction.metricDualVector_spec B hpos, Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos]

omit [Fintype ι] [LinearOrder ι] in
theorem covectorMetric_sharp_right (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (ξ η : E →L[ℝ] ℝ) : ComplexMultiplication.HodgeComparison.CovectorMetric.CM.Construction.covectorMetric B ξ η = ξ (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B η) := by
  change η (ComplexMultiplication.HodgeComparison.CovectorMetric.CM.Construction.metricDualVector B ξ) = _
  rw [metricDualVector_eq_sharp B hpos, ← Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos η, hB,
    Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos]

theorem bilinearFormMetricPair_one_re_sharp (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a c).re =
      (AntiOneFormCoordinates.oneFormLinear a (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear c)))).re +
      (AntiOneFormCoordinates.oneFormLinear a (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.imCLM.comp (AntiOneFormCoordinates.oneFormLinear c)))).im := by
  let T := (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.realMetricFiberContinuousEquiv (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)).symm
  let q := (AntiOneFormCoordinates.oneFormLinear a).comp T.symm.toContinuousLinearMap
  let r := (AntiOneFormCoordinates.oneFormLinear c).comp T.symm.toContinuousLinearMap
  have hp := ComplexMultiplication.HodgeComparison.CovectorPair.CM.Construction.covectorInner_re_metric_pullback B hpos T (fun _ _ => rfl) q r
  have hq : q.comp T.toContinuousLinearMap = AntiOneFormCoordinates.oneFormLinear a := by ext v; simp [q]
  have hr : r.comp T.toContinuousLinearMap = AntiOneFormCoordinates.oneFormLinear c := by ext v; simp [r]
  rw [hq, hr, covectorMetric_sharp_right B hB hpos, covectorMetric_sharp_right B hB hpos] at hp
  rw [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b 1 B hB hpos, ComplexMultiplication.HodgeComparison.ExteriorMetricLowDegree.CM.Construction.formMetricPair_one]
  exact hp

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorMetricSharp
