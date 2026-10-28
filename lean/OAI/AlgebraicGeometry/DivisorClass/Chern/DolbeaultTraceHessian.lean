import OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantDolbeaultHessian
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OneAdjointCoordinates

/-! # Dolbeault Trace Hessian -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The other original Dolbeault Laplacian term is the covariant Hessian trace of the actual one-form differential. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem DolbeaultTraceHessian.exteriorContraction_one_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v w : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction 1 v a (fun _ => w) = a ![v, w] := by
  change a (Matrix.vecCons v (fun _ : Fin 1 => w)) = a ![v, w]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem DolbeaultTraceHessian.exteriorContraction_one_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (v : ι → E) (a : ι → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (w : E) :
    (-∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction 1 (v i) (a i)) (fun _ => w) = -∑ i, a i ![v i, w] := by
  simp [DolbeaultTraceHessian.exteriorContraction_one_apply]

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectedDegreeCodifferentialOne_scalar (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 2) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let S := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    let D := Line.ConnectionSymbols.lineCovectorConnectionDerivative 2 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (a.val.val i).extension) z
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1
      ((Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I (h.degreeCodifferential V 1 a.val)).val i).extension z (fun _ => w) =
      -∑ j, D (b j) ![S (b.coord j).toContinuousLinearMap, w] := by
  have hd := congrArg (fun F : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 => F (fun _ => w))
    (h.projectedDegreeCodifferentialOne_covector V e he i a hz)
  exact hd.trans (DolbeaultTraceHessian.exteriorContraction_one_sum _ _ w)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectedDegreeCodifferentialOne_dolbeault_hessian (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let S := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    let H := Line.CovectorHessian.lineCovectorHessian 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension) z
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1
      ((Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I (h.degreeCodifferential V 1 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val)).val i).extension z (fun _ => w) =
      -∑ j, ((1 / 2 : ℂ) * (H (b j) (S (b.coord j).toContinuousLinearMap) (fun _ => w) +
          Complex.I * H (b j) (Complex.I • S (b.coord j).toContinuousLinearMap) (fun _ => w)) -
        (1 / 2 : ℂ) * (H (b j) w (fun _ => S (b.coord j).toContinuousLinearMap) +
          Complex.I * H (b j) (Complex.I • w) (fun _ => S (b.coord j).toContinuousLinearMap))) := by
  have hd := h.projectedDegreeCodifferentialOne_scalar V e he i (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a) hz w
  apply hd.trans
  apply congrArg (fun c : ℂ => -c)
  apply Finset.sum_congr rfl
  intro j _
  exact h.projectiveDolbeaultOne_hessian V e he ⊤ a i ⟨hz.1, trivial, hz.2⟩ _ _ w

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
