import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ZeroChartHolomorphic
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ZeroChartPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Dolbeault

/-! # Zero Chart Values -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ZeroChartValues

noncomputable section

/-! Literal local scalar coefficients agree with the original section values and preserve subtraction. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
  {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
  (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))

theorem holomorphicLineZeroChart_apply (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    ZeroChartPair.holomorphicLineZeroChart V e i a z = a.val i ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, trivial, hz.2⟩ 0 := by
  rw [ZeroChartPair.holomorphicLineZeroChart, Projective.ZeroChartHolomorphic.projectiveOpenZeroChart_scalar V e _ (a.val i) z]
  exact Manifold.DolbeaultZeroKernel.openManifoldZeroScalar_apply (a.val i) ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, trivial, hz.2⟩

include hz in
theorem holomorphicLineZeroChart_sub (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    ZeroChartPair.holomorphicLineZeroChart V e i (a - b) z =
      ZeroChartPair.holomorphicLineZeroChart V e i a z - ZeroChartPair.holomorphicLineZeroChart V e i b z := by
  rw [holomorphicLineZeroChart_apply V e i hz, holomorphicLineZeroChart_apply V e i hz,
    holomorphicLineZeroChart_apply V e i hz]
  rw [sub_eq_add_neg a b, ← neg_one_smul ℂ b]
  change (a.val i + (-1 : ℂ) • b.val i) ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, trivial, hz.2⟩ 0 = _
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.add_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smul_apply,
    ContinuousAlternatingMap.add_apply]
  change _ + (-1 : ℂ) * _ = _ - _
  rw [neg_one_mul, ← sub_eq_add_neg]
  rfl

theorem holomorphicLineZeroChart_holomorphic_section (s : HolomorphicSection.Data.HolomorphicLineSection u ⊤) :
    ZeroChartPair.holomorphicLineZeroChart V e i (HolomorphicLine.AntiForms.holomorphicLineSectionSmoothZeroForm u ⊤ s) z =
      s.val i ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, trivial, hz.2⟩ := by
  rw [holomorphicLineZeroChart_apply V e i hz]
  exact ManifoldZeroForms.holomorphicManifoldZeroForm_apply (s.val i) _ 0

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ZeroChartValues
