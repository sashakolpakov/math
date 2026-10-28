import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerFormParallel
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Powers

/-! # Kahler Powers Parallel -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerPowersParallel.CM.Construction

noncomputable section

/-! Every actual exterior power of the Fubini–Study form is parallel
for the constructed projective metric connection. -/

open scoped ContDiff _root_.Manifold

theorem covectorConnectionDerivative_constant_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E 0) (x : E) :
    Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative 0 Γ (fun _ => c) x = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousAlternatingMap.ext
  intro v
  rw [Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply, fderiv_const_apply]
  change 0 - Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 0 (Γ x u) c v = 0
  rw [Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction_apply, Finset.univ_eq_empty, Finset.sum_empty, sub_zero]

theorem euclideanChartForm_wedge (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) {p q : ℕ}
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace p)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace q) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (p + q) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b).val =
      fun z => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e p a.val z) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e q b.val z) := by
  funext z
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
  dsimp only [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge]
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart]
  exact (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback _ _ _).symm

theorem projectiveParallel_wedge (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {p q : ℕ}
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace p)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace q)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (ha : Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e p a z = 0)
    (hb : Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e q b z = 0) :
    Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e (p + q) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) z = 0 := by
  unfold Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative
  rw [euclideanChartForm_wedge]
  apply WedgeCovariantDerivative.CM.Construction.covectorConnectionDerivative_wedge_parallel
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (((Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_smooth V e he p a).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).of_le (by simp))
    (((Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_smooth V e he q b).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).of_le (by simp)) ha hb

theorem projectiveParallel_degreeCast (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) {n m : ℕ} (h : n = m)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (ha : Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e n a z = 0) :
    Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e m (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast h a) z = 0 := by
  subst m
  exact ha

theorem constantZeroForm_parallel (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (c : ℂ) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e 0 (NormalizedPrimitives.CM.Construction.constantZeroForm V.analyticModel V.analyticSpace c) z = 0 := by
  have hc : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 (NormalizedPrimitives.CM.Construction.constantZeroForm V.analyticModel V.analyticSpace c).val =
      fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Fin 0) c := by
    funext y
    ext v
    change NormalizedPrimitives.CM.Construction.constantZeroForm V.analyticModel V.analyticSpace c
      (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y)) _ = c
    have h := NormalizedPrimitives.CM.Construction.constantZeroForm_scalar V.analyticModel V.analyticSpace c
      (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y))
    refine Eq.trans ?_ h
    apply congrArg (NormalizedPrimitives.CM.Construction.constantZeroForm V.analyticModel V.analyticSpace c
      (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y)))
    exact Subsingleton.elim _ _
  unfold Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative
  rw [hc]
  exact covectorConnectionDerivative_constant_zero _ _ _

theorem fubiniStudyPower_parallel (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (k : ℕ)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e (k + k) (Powers.CM.Construction.fubiniStudyPower V k).val z = 0 := by
  induction k with
  | zero => exact constantZeroForm_parallel V e 1 z
  | succ k hk =>
      apply projectiveParallel_degreeCast V e (by omega)
      exact projectiveParallel_wedge V e he (Powers.CM.Construction.fubiniStudyPower V k).val (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V)
        hz hk (KahlerFormParallel.CM.Construction.fubiniStudyForm_parallel V e he hz)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerPowersParallel.CM.Construction
