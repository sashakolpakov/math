import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth
import OAI.Analysis.HodgeTheory.Decomposition.CovectorConnectionTypes
import OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms

/-! # Projective Covector Connection -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions

noncomputable section

/-! The genuine smooth projective covector connection, its exterior
derivative, and its preservation of each actual manifold bidegree. -/

open scoped ContDiff _root_.Topology

theorem covectorConnectionDerivative_smoothOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E}
    (hU : IsOpen U) (hΓ : ContDiffOn ℝ ∞ Γ U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (CovectorConnection.Constructions.covectorConnectionDerivative n Γ a) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ a) U := ha.fderiv_of_isOpen hU (by simp)
  let L : DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] (E →L[ℝ] E) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n :=
    ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM ℂ (ContinuousLinearMap.id ℝ E)
  have hL : ContDiff ℝ ∞ L := ContinuousLinearMap.contDiff
    (𝕜 := ℝ) (E := DifferentialForms.Manifold.Basic.FormValue E n) (F := (E →L[ℝ] E) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) L
  have hA : ContDiffOn ℝ ∞
      (fun x => (a x).fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ E)) U :=
    hL.comp_contDiffOn ha
  exact hD.sub (hA.clm_comp hΓ)

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def projectiveFormCovariantDerivative (n : ℕ)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n :=
  CovectorConnection.Constructions.covectorConnectionDerivative n (ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (EuclideanForms.Constructions.euclideanChartForm V e n a.val) z

include he

theorem projectiveFormCovariantDerivative_smooth (n : ℕ)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    ContDiffOn ℝ ∞ (projectiveFormCovariantDerivative V e n a)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  covectorConnectionDerivative_smoothOn n _ _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he) (EuclideanForms.Constructions.euclideanChartForm_smooth V e he n a)

theorem projectiveFormCovariantDerivative_alternation (n : ℕ)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ContinuousAlternatingMap.alternatizeUncurryFin (projectiveFormCovariantDerivative V e n a z) =
      EuclideanForms.Constructions.euclideanChartForm V e (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val z := by
  rw [EuclideanForms.Constructions.euclideanChartForm_d V e he n a z hz]
  exact CovectorConnection.Constructions.covectorConnectionDerivative_alternation n _ _ z (ProjectiveConnection.Constructions.projectiveConnectionCoefficient_symmetric V e he hz)

theorem euclideanChartForm_pure (p q : ℕ)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (p + q))
    (ha : DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace p q a.val)
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    DifferentialForms.Manifold.Bidegree.HasBidegree (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) p q (EuclideanForms.Constructions.euclideanChartForm V e (p + q) a.val z) := by
  intro c v
  change a.val.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
    (fun i => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((c : ℂ) • v i)) = _
  simp only [map_smul]
  exact ha e he _ hz c (fun i => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (v i))

theorem projectiveFormCovariantDerivative_pure (p q : ℕ)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (p + q))
    (ha : DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace p q a.val)
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    DifferentialForms.Manifold.Bidegree.HasBidegree (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) p q (projectiveFormCovariantDerivative V e (p + q) a z u) := by
  apply CovectorConnectionTypes.Constructions.covectorConnectionDerivative_pure p q _ _ z
  · exact ((EuclideanForms.Constructions.euclideanChartForm_smooth V e he (p + q) a).contDiffAt
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  · filter_upwards [(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
    exact euclideanChartForm_pure V e he p q a ha hy
  · exact ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_right V e he hz

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions
