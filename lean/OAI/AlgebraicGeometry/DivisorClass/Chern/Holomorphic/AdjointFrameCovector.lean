import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.IntrinsicKahlerAdjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiMultiplication

/-! # Adjoint Frame Covector -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual reconstructed adjoint frame is the native covariant metric trace. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.chartCovariantAdjointFrame_covector (n : ℕ)
    (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (n + 1)) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (h.chartCovariantAdjointFrame V e i n b) z =
      Line.ConnectionSymbols.lineCovariantCodifferential (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (n + 1) (b.val i).extension) z := by
  apply (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).injective
  change Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n (h.chartCovariantAdjointFrame V e i n b) z = _
  rw [h.chartCovariantAdjointFrame_coefficients V e he i n b hz.1]
  have heq : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i (n + 1) b).extension =ᶠ[𝓝 z]
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (b.val i).extension := by
    filter_upwards [(ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz] with y hy
    exact Holomorphic.ChartTestDerivatives.holomorphicLineGlobalFrame_coefficients V e i (n + 1) b hy
  exact (h.projectiveCovariantAdjointCoefficients_congr V e i n _ _ heq).trans
    (h.projectiveCovariantAdjointCoefficients_eq V e he n ⊤ b i ⟨hz.1, trivial, hz.2⟩)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightedCovariantChartAdjoint_covector (n : ℕ)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (n + 1)) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n ((h.weightedCovariantChartAdjoint V e he i n f hf hs b).val i).extension z =
      star (f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) • Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (h.chartCovariantAdjointFrame V e i n b) z := by
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply ((h.weightedCovariantChartAdjoint V e he i n f hf hs b).val i)
      ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), trivial, hz.2⟩,
    h.weightedCovariantChartAdjoint_inFrame V e he i n f hf hs b
      ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), e.map_target hz.1, hz.2⟩]
  ext v
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
