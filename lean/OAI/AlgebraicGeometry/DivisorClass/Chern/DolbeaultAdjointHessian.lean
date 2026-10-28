import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CovectorHessian
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OneAdjointCoordinates

/-! # Dolbeault Adjoint Hessian -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original Dolbeault derivative of the original degree-zero adjoint is the antiholomorphic trace of the bundle Hessian. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem DolbeaultAdjointHessian.alternation_zero_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 0) (v : Fin 1 → E) :
    alternatizeUncurryFin N v = N (v 0) (fun j => Fin.elim0 j) := by
  have ht : Fin.tail v = (fun j : Fin 0 => Fin.elim0 j) := by funext j; exact Fin.elim0 j
  simp [alternatizeUncurryFin_apply, ht]

theorem DolbeaultAdjointHessian.exteriorContraction_zero_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (t : Fin 0 → E) :
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction 0 v a t = a (fun _ => v) := by
  change a (Matrix.vecCons v t) = a (fun _ => v)
  congr 1
  funext j
  fin_cases j
  rfl

theorem DolbeaultAdjointHessian.exteriorContraction_zero_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (v : ι → E) (a : ι → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    (-∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction 0 (v i) (a i)) (fun j => Fin.elim0 j) =
      -∑ i, a i (fun _ => v i) := by
  simp [DolbeaultAdjointHessian.exteriorContraction_zero_apply]

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveDolbeaultZero_scalar
    (U : Opens V.analyticSpace) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let D := Line.ConnectionSymbols.lineCovectorConnectionDerivative 0 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 (a.val i).extension) z
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u U 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u U a)).val.val i).extension z (fun _ => w) =
      (1 / 2 : ℂ) * (D w (fun j => Fin.elim0 j) + Complex.I * D (Complex.I • w) (fun j => Fin.elim0 j)) := by
  have hd := congrArg (fun F : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 => F (fun _ => w))
    (h.projectiveDolbeault_covariant V e he U 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u U a) i hz)
  simp only [DolbeaultAdjointHessian.alternation_zero_apply, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, smul_eq_mul] at hd
  exact hd

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.degreeCodifferential_hessian_scalar (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let S := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension
    Line.ConnectionSymbols.lineCovectorConnectionDerivative 0 G A
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 ((h.degreeCodifferential V 0 a.val).val i).extension) z w (fun j => Fin.elim0 j) =
      -∑ j, Line.CovectorHessian.lineCovectorHessian 1 G A f z w (b j) (fun _ => S (b.coord j).toContinuousLinearMap) := by
  have hd := congrArg (fun F : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 0 => F (fun j => Fin.elim0 j))
    (h.degreeCodifferential_hessian V e he i a hz w)
  exact hd.trans (DolbeaultAdjointHessian.exteriorContraction_zero_sum _ _)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveDolbeaultAdjoint_hessian (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let S := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    let H := Line.CovectorHessian.lineCovectorHessian 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension) z
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1
      ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 a.val))).val.val i).extension z (fun _ => w) =
      -(1 / 2 : ℂ) * ((∑ j, H w (b j) (fun _ => S (b.coord j).toContinuousLinearMap)) +
        Complex.I * ∑ j, H (Complex.I • w) (b j) (fun _ => S (b.coord j).toContinuousLinearMap)) := by
  have hd := h.projectiveDolbeaultZero_scalar V e he ⊤ (h.degreeCodifferential V 0 a.val) i ⟨hz.1, trivial, hz.2⟩ w
  have hw := h.degreeCodifferential_hessian_scalar V e he i a hz w
  have hJw := h.degreeCodifferential_hessian_scalar V e he i a hz (Complex.I • w)
  exact hd.trans ((congrArg₂ (fun p q : ℂ => (1 / 2 : ℂ) * (p + Complex.I * q)) hw hJw).trans (by ring))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
