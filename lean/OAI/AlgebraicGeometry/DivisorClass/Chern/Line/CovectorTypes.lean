import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CovariantDolbeault
import OAI.Analysis.HodgeTheory.Decomposition.CovectorConnectionTypes

/-! # Covector Types -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual bundle covariant derivative preserves original antiholomorphic covector types. -/

open Filter
open scoped _root_.Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.CovectorConnectionTypes.Constructions

theorem Line.CovectorTypes.lineCovectorConnectionDerivative_pure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (p q : ℕ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q)) (x : E) (ha : DifferentiableAt ℝ a x)
    (hpure : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (a y))
    (hG : ∀ v w, G x v (Complex.I • w) = Complex.I • G x v w) (v : E) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (Line.ConnectionSymbols.lineCovectorConnectionDerivative (p + q) G A a x v) := by
  rw [Line.ConnectionSymbols.lineCovectorConnectionDerivative_apply]
  exact (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E p q).add_mem
    (Analysis.HodgeTheory.Decomposition.CovectorConnectionTypes.Constructions.covectorConnectionDerivative_pure p q G a x ha hpure hG v)
    ((Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E p q).smul_mem (A x v) hpure.self_of_nhds)

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovectorConnection_anti
    (U : TopologicalSpace.Opens V.analyticSpace) (q : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u U q)
    (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (c : ℂˣ) (t : Fin q → ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Line.ConnectionSymbols.lineCovectorConnectionDerivative q (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e q (a.val.val i).extension) z v (fun j => (c : ℂ) • t j) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 q c * Line.ConnectionSymbols.lineCovectorConnectionDerivative q (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e q (a.val.val i).extension) z v t := by
  have ha := ((ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he _ q (a.val.val i)).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hpure : ∀ᶠ y in 𝓝 z, ∀ (c : ℂˣ) (t : Fin q → ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V),
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e q (a.val.val i).extension y (fun j => (c : ℂ) • t j) =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 q c * Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e q (a.val.val i).extension y t := by
    filter_upwards [(ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz] with y hy
    intro c t
    change (a.val.val i).extension.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y)
      (fun j => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((c : ℂ) • t j)) = _
    simp only [map_smul]
    exact a.property i e he _ hy c (fun j => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (t j))
  have htype := Line.CovectorTypes.lineCovectorConnectionDerivative_pure (E := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 0 q
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
  unfold Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree at htype
  rw [Nat.zero_add q] at htype
  exact htype _ z ha hpure (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_right V e he hz.1) v c t

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
