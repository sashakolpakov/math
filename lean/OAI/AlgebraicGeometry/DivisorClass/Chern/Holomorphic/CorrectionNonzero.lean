import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.SectionCorrection
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ZeroChartValues

/-! # Correction Nonzero -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CorrectionNonzero

noncomputable section

/-! Correcting a unit-valued original smooth section by a primitive with coefficient norm less than one gives an actual nonzero holomorphic section value. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicLine_nonzero_section_of_small_correction (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hx : x ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (a b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 0)
    (hb : HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 b = HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 a)
    (ha : ZeroChartPair.holomorphicLineZeroChart V e i a.val x = 1)
    (hsmall : ‖ZeroChartPair.holomorphicLineZeroChart V e i b.val x‖ < 1) :
    ∃ s : HolomorphicSection.Data.HolomorphicLineSection u ⊤, s.val i ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x, trivial, hx.2⟩ ≠ 0 := by
  let H := HolomorphicSmooth.SectionCorrection.holomorphicLine_section_of_equal_dolbeault V a b hb
  let s := H.choose
  have hs := congrArg (fun t : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 0 => ZeroChartPair.holomorphicLineZeroChart V e i t.val x) H.choose_spec
  change ZeroChartPair.holomorphicLineZeroChart V e i (HolomorphicLine.AntiForms.holomorphicLineSectionSmoothZeroForm u ⊤ s) x =
    ZeroChartPair.holomorphicLineZeroChart V e i (a.val - b.val) x at hs
  rw [ZeroChartValues.holomorphicLineZeroChart_holomorphic_section V e i hx,
    ZeroChartValues.holomorphicLineZeroChart_sub V e i hx, ha] at hs
  refine ⟨s, fun hz => ?_⟩
  have hb1 : ZeroChartPair.holomorphicLineZeroChart V e i b.val x = 1 := (sub_eq_zero.mp (hs.symm.trans hz)).symm
  rw [hb1, norm_one] at hsmall
  exact (lt_irrefl (1 : ℝ)) hsmall

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CorrectionNonzero
