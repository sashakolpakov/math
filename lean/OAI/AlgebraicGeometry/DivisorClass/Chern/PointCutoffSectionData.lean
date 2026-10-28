import OAI.AlgebraicGeometry.DivisorClass.Chern.PointFrameCutoffData
import OAI.AlgebraicGeometry.DivisorClass.Chern.CutoffUnitSourceSupport
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogSourceNormBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ZeroChartValues

/-! # Point Cutoff Section Data -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PointCutoffSectionData

noncomputable section

/-! Constructed original point cutoff sections have unit value, a locally zero Dolbeault source, and a uniformly bounded actual logarithmic source norm. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem exists_projective_point_cutoff_section (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hx : x ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (m : ℕ) :
    ∃ a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0, ∃ U : Opens V.analyticSpace, ∃ M : ℝ,
      Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x ∈ U ∧ Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a x = 1 ∧
      HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (le_top : U ≤ ⊤) (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) = 0 ∧
      0 < M ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ((h.withPotential (PointLogMetricSolver.projectivePointLogPotential V e he x hx.1 m ε hε)).formIntegralPair V 1
        (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a)).re ≤ M := by
  let W := Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  have hxW : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x ∈ W := ⟨e.map_target hx.1, hx.2⟩
  have H := PointFrameCutoffData.exists_projective_point_cutoff_open V W (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x) hxW
  let f := H.choose
  have hf := H.choose_spec.1
  have hs := H.choose_spec.2.1
  let U := H.choose_spec.2.2.choose
  have hUdata := H.choose_spec.2.2.choose_spec
  have hfs : tsupport f ⊆ (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Set V.analyticSpace) :=
    fun _ hy => (hs hy).2
  have hfe : tsupport f ⊆ e.source := fun _ hy => (hs hy).1
  have hUi : U ≤ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i :=
    fun _ hy => (hUdata.2.1 hy).2
  let a := Holomorphic.CutoffUnitSection.holomorphicLineCutoffUnitSection V u i f hf hfs
  have HK := CutoffUnitSourceSupport.holomorphicLineCutoffUnitSection_source_support V u e i f hf hfs hfe U hUi hUdata.2.2 x hUdata.1
  let K := HK.choose
  have HKdata := HK.choose_spec
  have HB := LogSourceNormBound.projectivePointLogPotential_source_norm_bound V h e he x hx.1 m 1
    (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) HKdata.1 HKdata.2.1 HKdata.2.2.1 (HKdata.2.2.2 h)
  refine ⟨a, U, HB.choose, hUdata.1, ?_,
    Holomorphic.CutoffUnitSection.holomorphicLineCutoffUnitSection_dbar_one V u i f hf hfs U hUi hUdata.2.2,
    HB.choose_spec.1, HB.choose_spec.2⟩
  rw [Holomorphic.ZeroChartValues.holomorphicLineZeroChart_apply V e i hx]
  exact (Holomorphic.CutoffUnitSection.holomorphicLineCutoffUnitSection_apply V u i f hf hfs i
    ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x, trivial, hx.2⟩ hx.2 0).trans
      ((congrArg (fun w : ℂ => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x) * w)
        (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition_self V.analyticModel V.analyticSpace u i
          (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x) hx.2)).trans
        ((mul_one _).trans (hUdata.2.2 _ hUdata.1)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PointCutoffSectionData
