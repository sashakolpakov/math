import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Cutoff

/-! # Covariant Dolbeault Hessian -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! Differentiating the original Dolbeault operator gives the antiholomorphic alternation of the actual covariant Hessian tensor. -/

open _root_.TopologicalSpace Filter _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

theorem CovariantDolbeaultHessian.lineCovectorConnectionDerivative_antilinearAlternation
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype ι]
    (b : Module.Basis ι ℝ E) (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {x : E} (hN : DifferentiableAt ℝ N x) (v : E)
    (hG : ∀ w, G x v (Complex.I • w) = Complex.I • G x v w) :
    Line.ConnectionSymbols.lineCovectorConnectionDerivative (n + 1) G A
      (fun y => alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (N y))) x v =
      alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (Line.HessianBilinear.lineCovectorTensorDerivative n G A N x v)) := by
  have hP : DifferentiableAt ℝ (fun y => Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (N y)) x :=
    (((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)).restrictScalars ℝ).differentiableAt).comp x hN
  rw [Line.HessianBilinear.lineCovectorConnectionDerivative_alternation b n G A _ hP v,
    Line.Cutoff.lineCovectorTensorDerivative_antilinear n G A N hN v hG]

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveDolbeault_covariantDerivative
    (U : Opens V.analyticSpace) (q : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u U q) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let N := Line.ConnectionSymbols.lineCovectorConnectionDerivative q G A (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e q (a.val.val i).extension)
    Line.ConnectionSymbols.lineCovectorConnectionDerivative (q + 1) G A
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (q + 1) ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u U q a).val.val i).extension) z v =
      alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) q)
        (Line.HessianBilinear.lineCovectorTensorDerivative q G A N z v)) := by
  let W := ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
  let A := h.projectiveConnectionChart V e i
  let N := Line.ConnectionSymbols.lineCovectorConnectionDerivative q G A (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e q (a.val.val i).extension)
  have hN : DifferentiableAt ℝ N z :=
    ((h.projectiveCovectorConnection_smooth V e he U q a.val i).contDiffAt (W.isOpen.mem_nhds hz)).differentiableAt (by simp)
  have heq : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (q + 1) ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u U q a).val.val i).extension =ᶠ[𝓝 z]
      (fun y => alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) q) (N y))) := by
    filter_upwards [W.isOpen.mem_nhds hz] with y hy
    exact h.projectiveDolbeault_covariant V e he U q a i hy
  exact (congrArg (fun T => T v) (Holomorphic.AdjointDerivative.lineCovectorConnectionDerivative_congr (q + 1) G A _ _ heq)).trans
    (CovariantDolbeaultHessian.lineCovectorConnectionDerivative_antilinearAlternation
      (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis q G A N hN v
      (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_right V e he hz.1 v))

end

/-! The actual differentiated bundle Dolbeault one-form operator, evaluated as a covariant Hessian in two directions. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem CovariantDolbeaultHessian.alternation_one_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (v : Fin 2 → E) :
    alternatizeUncurryFin N v = N (v 0) (fun _ => v 1) - N (v 1) (fun _ => v 0) := by
  have h0 : Fin.tail v = (fun _ : Fin 1 => v 1) := by funext j; fin_cases j; rfl
  have h1 : Fin.removeNth (1 : Fin 2) v = (fun _ : Fin 1 => v 0) := by funext j; fin_cases j; rfl
  simp [alternatizeUncurryFin_apply, Fin.sum_univ_two, h0, h1, sub_eq_add_neg]

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveDolbeaultOne_hessian
    (U : Opens V.analyticSpace) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u U 1) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v w t : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension
    Line.ConnectionSymbols.lineCovectorConnectionDerivative 2 G A
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u U 1 a).val.val i).extension) z v ![w, t] =
      (1 / 2 : ℂ) * (Line.CovectorHessian.lineCovectorHessian 1 G A f z v w (fun _ => t) +
        Complex.I * Line.CovectorHessian.lineCovectorHessian 1 G A f z v (Complex.I • w) (fun _ => t)) -
      (1 / 2 : ℂ) * (Line.CovectorHessian.lineCovectorHessian 1 G A f z v t (fun _ => w) +
        Complex.I * Line.CovectorHessian.lineCovectorHessian 1 G A f z v (Complex.I • t) (fun _ => w)) := by
  have hN := ((h.projectiveCovectorConnection_smooth V e he U 1 a.val i).contDiffAt
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hd := congrArg (fun F : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 2 => F ![w, t])
    (h.projectiveDolbeault_covariantDerivative V e he U 1 a i hz v)
  simp only [CovariantDolbeaultHessian.alternation_one_apply, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Line.HessianBilinear.lineCovectorTensorDerivative_hessian 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension) hN] at hd
  exact hd

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
