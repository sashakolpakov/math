import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GluedDivergence
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerDecomposition

/-! # Lower Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The actual global Dolbeault Laplacian pairing decomposes into the glued rough pairing and the original curvature contribution. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerPair_decomposition
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z
    h.projectiveGlobalPair V e 1 (h.smoothDolbeaultLaplacianOne V a) a.val z =
      h.projectiveRoughPair V e ⊤ 1 a.val a.val z +
        (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * (h.projectiveWeightChart V e i z *
          Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B
            (BaseCurvatureAction.baseCurvatureAction b B (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z f +
              Line.CurvatureContraction.lineCurvatureAction b B (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) f) f) := by
  dsimp only
  have hd := h.smoothDolbeaultLaplacianOne_decomposition V e he i a hz
  dsimp only at hd
  rw [h.projectiveGlobalPair_inFrame V e he 1 (h.smoothDolbeaultLaplacianOne V a) a.val i hz,
    hd, h.projectiveRoughPair_onOpen V e he ⊤ 1 a.val a.val i ⟨hz.1, trivial, hz.2⟩]
  simp only [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFrameRoughPair, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left, mul_add]
  ring

end

/-! The original coordinate curvature estimate implies the actual global bundle pairing estimate. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerPairLowerBound (T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (c : ℝ) : Prop :=
  ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1, ∀ z ∈ T,
    c * (h.projectiveGlobalPair V e 1 a.val a.val z).re ≤
      (h.projectiveGlobalPair V e 1 (h.smoothDolbeaultLaplacianOne V a) a.val z -
        h.projectiveRoughPair V e ⊤ 1 a.val a.val z).re

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerPairLowerBound_of_curvature
    {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (c : ℝ)
    (hC : ∀ z ∈ T, ∀ f : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 0 1 f →
      let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
      let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z
      c * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B f f).re ≤
        (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B
          (BaseCurvatureAction.baseCurvatureAction b B (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z f +
            Line.CurvatureContraction.lineCurvatureAction b B (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) f) f).re) :
    h.projectiveBochnerPairLowerBound V e T c := by
  intro a z hz
  let i := e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
  have hzi : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
    ⟨hTD hz, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain i⟩
  have hp : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 0 1 (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z) :=
    Projective.CovariantDolbeault.projectiveOpenChartForm_pure V e he _ 0 1 (a.val.val i) (a.property i) ⟨hTD hz, trivial, hzi.2⟩
  have hb := hC z hz (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z) hp
  dsimp only at hb
  have hw := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he (hTD hz)).le
      (h.positive i ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hzi.2⟩).le)
  rw [h.projectiveBochnerPair_decomposition V e he a i hzi]
  rw [add_sub_cancel_left, h.projectiveGlobalPair_inFrame V e he 1 a.val a.val i hzi,
    h.projectiveWeightChart_apply V e i hzi]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  convert hw using 1 <;> (try ring_nf)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
