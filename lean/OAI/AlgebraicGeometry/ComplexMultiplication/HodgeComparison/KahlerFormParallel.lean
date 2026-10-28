import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WedgeCovariantDerivative
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection

/-! # Kahler Form Parallel -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerFormParallel.CM.Construction

noncomputable section

/-! The actual projective Kähler form is parallel for the metric
connection: the metric and complex structure determine its coefficients. -/

open OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions
open Filter
open scoped _root_.Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem real_twoForm_metric_recover (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v : E)
    (hr : (f ![u, v]).im = 0) :
    f ![u, v] = -((KahlerDifferential.CM.Construction.metricFromTwoForm f u (Complex.I • v) : ℝ) : ℂ) := by
  rw [KahlerDifferential.CM.Construction.metricFromTwoForm_J_right, Complex.ofReal_neg, neg_neg]
  apply Complex.ext
  · rfl
  · exact hr

theorem real_twoForm_derivative_metric {f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2} {x : E}
    (hf : DifferentiableAt ℝ f x)
    (hr : ∀ᶠ y in 𝓝 x, ∀ v : Fin 2 → E, (f y v).im = 0) (u v w : E) :
    (fderiv ℝ f x u) ![v, w] =
      -((fderiv ℝ (fun y => KahlerDifferential.CM.Construction.metricFromTwoForm (f y)) x u v (Complex.I • w) : ℝ) : ℂ) := by
  let B := fun y => KahlerDifferential.CM.Construction.metricFromTwoForm (f y)
  have hB : DifferentiableAt ℝ B x :=
    ((KahlerDifferential.CM.Construction.metricFromTwoForm_smooth (E := E)).differentiable (by simp)).differentiableAt.comp x hf
  have he : (fun y => f y ![v, w]) =ᶠ[𝓝 x] (fun y => -((B y v (Complex.I • w) : ℝ) : ℂ)) := by
    filter_upwards [hr] with y hy
    exact real_twoForm_metric_recover (f y) v w (hy _)
  have hdB := (hB.clm_apply (differentiableAt_const v)).clm_apply
    (differentiableAt_const (Complex.I • w))
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp x hdB.hasFDerivAt).neg
  change HasFDerivAt (fun y => -((B y v (Complex.I • w) : ℝ) : ℂ))
    ((-Complex.ofRealCLM).comp (fderiv ℝ (fun y => B y v (Complex.I • w)) x)) x at hd
  rw [← fderiv_continuousAlternatingMap_apply_const_apply hf, he.fderiv_eq, hd.fderiv]
  change -((fderiv ℝ (fun y => B y v (Complex.I • w)) x u : ℝ) : ℂ) = _
  rw [MetricDerivative.CM.Construction.bilinearDerivative_apply B hB]

theorem metric_compatible_twoForm_parallel
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2} {x : E}
    (hf : DifferentiableAt ℝ f x)
    (hr : ∀ᶠ y in 𝓝 x, ∀ v : Fin 2 → E, (f y v).im = 0)
    (hΓ : ∀ u v w, KahlerDifferential.CM.Construction.metricFromTwoForm (f x) (Γ x u v) w +
      KahlerDifferential.CM.Construction.metricFromTwoForm (f x) v (Γ x u w) =
        fderiv ℝ (fun y => KahlerDifferential.CM.Construction.metricFromTwoForm (f y)) x u v w)
    (hJ : ∀ u v, Γ x u (Complex.I • v) = Complex.I • Γ x u v) :
    Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative 2 Γ f x = 0 := by
  have hrx := hr.self_of_nhds
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply]
  change (fderiv ℝ f x u) v - Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 2 (Γ x u) (f x) v = 0
  rw [hv, real_twoForm_derivative_metric hf hr, ← hΓ, hJ, Complex.ofReal_add, neg_add_rev]
  rw [← real_twoForm_metric_recover (f x) (Γ x u (v 0)) (v 1) (hrx _),
    ← real_twoForm_metric_recover (f x) (v 0) (Γ x u (v 1)) (hrx _)]
  rw [Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction_apply, Fin.sum_univ_two]
  have h₀ : Function.update ![v 0, v 1] 0 (Γ x u (v 0)) = ![Γ x u (v 0), v 1] := by
    ext i; fin_cases i <;> simp
  have h₁ : Function.update ![v 0, v 1] 1 (Γ x u (v 1)) = ![v 0, Γ x u (v 1)] := by
    ext i; fin_cases i <;> simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h₀, h₁]
  abel

theorem fubiniStudyForm_parallel (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e 2 (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V) z = 0 := by
  apply metric_compatible_twoForm_parallel (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (((Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_smooth V e he 2 (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V)).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp))
  · filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
    intro v
    exact VarietyMetric.CM.Construction.varietyFubiniStudyForm_real_inChart V e he hy
      (fun i => EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (v i))
  · intro u v w
    exact Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_metric V e he hz u v w
  · intro u v
    exact Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_right V e he hz u v

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerFormParallel.CM.Construction
