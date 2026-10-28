import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiTwoFormCoefficients
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorTypes

/-! # Anti Two Contractions -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Contracting genuine (0,2) covectors, and taking their actual covariant metric trace, gives (0,1) covectors. -/

open scoped ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Linear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem AntiTwoContractions.realLinearMap_conjugate_smul_of_I (D : E →L[ℝ] ℂ)
    (hD : ∀ v, D (Complex.I • v) = -Complex.I * D v) (c : ℂ) (v : E) :
    D (c • v) = star c * D v := by
  have hp : Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ D = D := by
    ext w
    rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, hD]
    change (1 / 2 : ℂ) * (D w + Complex.I * (-Complex.I * D w)) = D w
    calc
      _ = (1 / 2 : ℂ) * (D w - Complex.I ^ 2 * D w) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have h := Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul E ℂ D c v
  rw [hp] at h
  exact h

theorem AntiTwoContractions.antiTwoForm_contraction (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 2 a) (v : E) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction 1 v a) := by
  intro c t
  rw [AntiOneFormCoordinates.oneFormLinear_reconstruct, AntiOneFormCoordinates.oneFormLinear_reconstruct]
  change AntiTwoFormCoefficients.twoFormBilinear a v ((c : ℂ) • t 0) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 1 c * AntiTwoFormCoefficients.twoFormBilinear a v (t 0)
  rw [AntiTwoContractions.realLinearMap_conjugate_smul_of_I (AntiTwoFormCoefficients.twoFormBilinear a v) (AntiTwoFormCoefficients.antiTwoForm_J_right a ha v),
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, pow_one, one_mul]

end Linear

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointOne_anti
    (U : TopologicalSpace.Opens V.analyticSpace) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u U 2) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 0 1
      (Line.ConnectionSymbols.lineCovariantCodifferential (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (a.val.val i).extension) z) := by
  apply (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 0 1).neg_mem
  apply (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 0 1).sum_mem
  intro j _
  apply AntiTwoContractions.antiTwoForm_contraction
  intro c t
  exact h.projectiveCovectorConnection_anti V e he U 2 a i hz _ c t

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
