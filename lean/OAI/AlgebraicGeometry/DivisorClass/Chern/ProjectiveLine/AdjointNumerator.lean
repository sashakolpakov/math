import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.MetricOperator
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionOperator
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.WeightedAdjoint
import OAI.Analysis.HodgeTheory.Decomposition.FormalAdjointPairDerivative

/-! # Adjoint Numerator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The native matrix formal adjoint equals the actual covariant metric trace on original bundle frames. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.FormalAdjointPairDerivative.Constructions

theorem ProjectiveLine.AdjointNumerator.lineComplexFDerivRe {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : D → ℂ) {x : D} (hf : DifferentiableAt ℝ f x) (v : D) :
    fderiv ℝ (fun y => (f y).re) x v = (fderiv ℝ f x v).re := by
  have hd := Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt
  exact congrArg (fun L : D →L[ℝ] ℝ => L v) hd.fderiv

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointNumerator (i : V.analyticSpace) (n : ℕ)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.formalAdjointNumerator (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n)
    (h.projectiveWeightedFormOperator V e i (n + 1)) a z +
      (Line.ConnectionOperator.lineConnectionCoordinateOperator (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (h.projectiveConnectionChart V e i z)).adjoint (h.projectiveWeightedFormOperator V e i (n + 1) z (a z))

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantAdjointNumerator_eq (n : ℕ) (U : Opens V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U (n + 1)) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveCovariantAdjointNumerator V e i n
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (a.val i).extension) z =
        h.projectiveWeightedFormOperator V e i n z
          (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
            (Line.ConnectionSymbols.lineCovariantCodifferential (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
              (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
              (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (n + 1) (a.val i).extension) z)) := by
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let Q := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n
  let P := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)
  let α := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (n + 1) (a.val i).extension
  have hz' : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := hz.1
  have hzi : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
    ⟨hz.1, hz.2.2⟩
  have hB := ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).contDiffAt
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz')).differentiableAt (by simp)
  have hw := ((h.projectiveWeightChart_smooth V e he i).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hzi)).differentiableAt (by simp)
  have hα := ((ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he
    (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) (n + 1) (a.val i)).contDiffAt
      ((ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hρ := ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).contDiffAt
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz')).differentiableAt (by simp)
  have hM := ((h.projectiveWeightedFormOperator_smooth V e he i (n + 1)).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hzi)).differentiableAt (by simp)
  have hPα : DifferentiableAt ℝ (fun y => P (α y)) z :=
    (P.toContinuousLinearMap.restrictScalars ℝ).differentiableAt.comp z hα
  apply ext_inner_right ℝ
  intro v
  obtain ⟨c, rfl⟩ := Q.surjective v
  let F (j : Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (y : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
    h.projectiveWeightChart V e i y * ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e y : ℂ) *
      Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e y) (α y)
        (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord j).toContinuousLinearMap c))
  have hF (j : Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) : DifferentiableAt ℝ (F j) z := by
    have hp := Analysis.HodgeTheory.Decomposition.WeightedMetricDerivative.Constructions.bilinearFormMetricPair_differentiableAt b (n + 1) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
      α (fun _ => Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord j).toContinuousLinearMap c) hB hα
      (differentiableAt_const _) (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b (n + 1) _
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz') (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz'))
    exact hw.mul ((Complex.ofRealCLM.differentiableAt.comp z hρ).mul hp)
  have hI (j : Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) :
      (fun y => inner ℝ (h.projectiveWeightedFormOperator V e i (n + 1) y (P (α y)))
        (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n j (Q c))) = (fun y => (F j y).re) := by
    funext y
    change inner ℝ (h.projectiveWeightedFormOperator V e i (n + 1) y (P (α y)))
      (P (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord j).toContinuousLinearMap (Q.symm (Q c)))) = _
    rw [Q.symm_apply_apply]
    exact h.projectiveWeightedFormOperator_pair V e i (n + 1) y _ _
  change inner ℝ (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.formalAdjointNumerator (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n) (h.projectiveWeightedFormOperator V e i (n + 1))
      (fun y => P (α y)) z +
      (Line.ConnectionOperator.lineConnectionCoordinateOperator b n (h.projectiveConnectionChart V e i z)).adjoint
        (h.projectiveWeightedFormOperator V e i (n + 1) z (P (α z)))) (Q c) = _
  rw [inner_add_left, Analysis.HodgeTheory.Decomposition.FormalAdjointPairDerivative.Constructions.formalAdjointNumerator_pair_derivative _ _ _ _ hM hPα]
  simp_rw [hI, ProjectiveLine.AdjointNumerator.lineComplexFDerivRe _ (hF _)]
  rw [ContinuousLinearMap.adjoint_inner_left, Line.ConnectionOperator.lineConnectionCoordinateOperator_apply,
    h.projectiveWeightedFormOperator_pair V e i (n + 1), h.projectiveWeightedFormOperator_pair V e i n]
  have hr := congrArg Complex.re (h.projectiveWeightedAdjoint V e he n U a i c hz)
  rw [Complex.re_sum] at hr
  change (∑ j, (fderiv ℝ (F j) z (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) j)).re) = _ at hr
  rw [hr]
  simp only [← mul_assoc, mul_sub, Complex.sub_re, α]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
