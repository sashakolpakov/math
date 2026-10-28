import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.AntiTestEnergy
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.ChartField

/-! # Anti Test Energy -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Literal compact chart fields of the original antiholomorphic bundle forms admit arbitrary smooth tests in their real energy pairing. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem Holomorphic.AntiTestEnergy.holomorphicLineCompactChartField_anti (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (n : ℕ)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ n) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    ∀ (c : ℂˣ) (t : Fin n → ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V),
      HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i n f hf hs a.val z (fun j => (c : ℂ) • t j) =
        Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 n c * HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i n f hf hs a.val z t := by
  by_cases hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  · rw [HolomorphicCompact.ChartField.holomorphicLineCompactChartField_inFrame V e i n f hf hs a.val hz]
    have hp := Holomorphic.AntiMultiplication.holomorphicLineSmoothMul_anti u ⊤ f hf n a
    intro c t
    change ((Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a.val).val i).extension.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
      (fun j => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((c : ℂ) • t j)) = _
    simp only [map_smul]
    exact hp i e he _ ⟨hz.1, trivial, hz.2⟩ c (fun j => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (t j))
  · have hc := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i n f hf hs a.val ht))
    rw [hc]
    intro c t
    change (0 : ℂ) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 n c * 0
    exact (mul_zero _).symm

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullEnergy_anti_test_re (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hc : DifferentiableAt ℝ c z)
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let w := h.projectiveWeightChart V e i
    let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
    (Line.RoughDivergence.lineCovectorFullEnergyPair b 1 B G A w s (fun y => OneCovectorAntiProjection.oneCovectorAntiProjection (c y)) z).re =
      (Line.RoughDivergence.lineCovectorFullEnergyPair b 1 B G A w s c z).re := by
  have hw : h.projectiveWeightChart V e i z = Complex.ofReal (h.projectiveWeightChart V e i z).re := by
    rw [h.projectiveWeightChart_apply V e i hz, Complex.ofReal_re]
  exact Line.AntiTestEnergy.lineCovectorFullEnergyPair_anti_test_re _ _ _ _ _ _ c
    ((HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i 1 f hf hs a.val).differentiable (by simp) z) hc
    (Filter.Eventually.of_forall (Holomorphic.AntiTestEnergy.holomorphicLineCompactChartField_anti V e he i 1 f hf hs a))
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_right V e he hz.1)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz.1) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz.1)
    (Analysis.HodgeTheory.Decomposition.EuclideanMetricDerivative.Constructions.projectiveEuclideanMetric_J_skew V e he hz.1) hw

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
