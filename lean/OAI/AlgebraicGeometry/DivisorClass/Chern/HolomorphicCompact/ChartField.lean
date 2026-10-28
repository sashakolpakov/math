import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.CoordinatesLp
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiMultiplication

/-! # Chart Field -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.ChartField

noncomputable section

section

/-! Literal smooth compact chart fields for original bundle cutoff forms, obtained from the already constructed frame coefficients. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

def holomorphicLineCompactChartField (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n :=
  (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).symm
    (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs a z)

theorem holomorphicLineCompactChartField_coefficients (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
      (holomorphicLineCompactChartField V e i n f hf hs a z) =
        HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs a z :=
  (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).apply_symm_apply _

include he in
theorem holomorphicLineCompactChartField_smooth (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ContDiff ℝ ∞ (holomorphicLineCompactChartField V e i n f hf hs a) :=
  ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
    (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_smooth V u e he i n f hf hs a)

theorem holomorphicLineCompactChartField_compact (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    HasCompactSupport (holomorphicLineCompactChartField V e i n f hf hs a) :=
  (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_compact V u e i n f hf hs a).comp_left
    (g := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).symm)
    (map_zero _)

theorem holomorphicLineCompactChartField_tsupport (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    tsupport (holomorphicLineCompactChartField V e i n f hf hs a) ⊆
      ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
  (tsupport_comp_subset (g := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).symm)
    (map_zero _) (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs a)).trans
      (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_tsupport V u e i n f hf hs a)

theorem holomorphicLineCompactChartField_tsupport_image (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    tsupport (holomorphicLineCompactChartField V e i n f hf hs a) ⊆
      Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport f :=
  (tsupport_comp_subset (g := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).symm)
    (map_zero _) (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs a)).trans
      (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport V e n _ (isClosed_tsupport f).isCompact
        (fun _ hx => (hs hx).1) (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_zero V u e i n f hf hs a))

include hs in
theorem holomorphicLineCutoff_image_domain :
    Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport f ⊆
      ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) := by
  rintro z ⟨x, hx, rfl⟩
  refine ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hs hx).1, ?_⟩
  change Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x) ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  rw [Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e x (hs hx).1]
  exact (hs hx).2

theorem holomorphicLineCompactChartField_inFrame (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    holomorphicLineCompactChartField V e i n f hf hs a z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n ((Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a).val i).extension z := by
  apply (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).injective
  rw [holomorphicLineCompactChartField_coefficients]
  exact Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_eq V u e i n f hf hs a hz

theorem holomorphicLineCompactChartField_eventually_inFrame (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    holomorphicLineCompactChartField V e i n f hf hs a =ᶠ[nhds z]
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n ((Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a).val i).extension := by
  filter_upwards [(ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz] with y hy
  exact holomorphicLineCompactChartField_inFrame V e i n f hf hs a hy

end

/-! Compact chart fields agree whenever the original globally cut-off bundle forms agree. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicLineCompactChartField_cutoff_congr (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace) (n : ℕ)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (g : V.analyticSpace → ℂ) (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hsg : tsupport g ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (hac : Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a = Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n g hg c) :
    holomorphicLineCompactChartField V e i n f hf hsf a =
      holomorphicLineCompactChartField V e i n g hg hsg c := by
  funext z
  by_cases hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  · exact (holomorphicLineCompactChartField_inFrame V e i n f hf hsf a hz).trans
      ((congrArg (fun t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n => Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (t.val i).extension z) hac).trans
        (holomorphicLineCompactChartField_inFrame V e i n g hg hsg c hz).symm)
  · have ha : holomorphicLineCompactChartField V e i n f hf hsf a z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hz (holomorphicLineCompactChartField_tsupport V e i n f hf hsf a ht))
    have hc : holomorphicLineCompactChartField V e i n g hg hsg c z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hz (holomorphicLineCompactChartField_tsupport V e i n g hg hsg c ht))
    exact ha.trans hc.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.ChartField
