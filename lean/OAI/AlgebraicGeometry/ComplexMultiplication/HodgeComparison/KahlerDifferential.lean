import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietyMetric
import Mathlib.Analysis.Normed.Module.Alternating.Curry

/-! # Kahler Differential -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction

noncomputable section

section

/-! The smooth positive metric obtained from the actual projective Kähler form. -/

open scoped ContDiff _root_.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def twoFormBilinear : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E 2 →L[ℝ] (E →L[ℝ] E →L[ℝ] ℂ) :=
  (ContinuousLinearMap.compL ℝ E (OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (E →L[ℝ] ℂ)
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ)
      (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := ℂ) (n := 1)).toContinuousLinearMap

theorem twoFormBilinear_apply (φ : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v : E) :
    twoFormBilinear φ u v = φ ![u, v] := by
  change φ (Matrix.vecCons u (fun _ : Fin 1 => v)) = φ ![u, v]
  apply congrArg φ
  funext i
  fin_cases i <;> rfl

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def metricCovectorFromOneForm : (E →L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E ℂ ℝ Complex.reCLM).comp
    ((ContinuousLinearMap.compL ℝ E E ℂ).flip (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))

/-- The real bilinear metric is g(u,v) = Re ω(u, Iv). -/
def metricFromTwoForm : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E 2 →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℂ) (E →L[ℝ] ℝ)
    metricCovectorFromOneForm).comp twoFormBilinear

theorem metricFromTwoForm_apply (φ : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v : E) :
    metricFromTwoForm φ u v = (φ ![u, Complex.I • v]).re := by
  change (twoFormBilinear φ u (Complex.I • v)).re = _
  rw [twoFormBilinear_apply]

theorem metricFromTwoForm_smooth : ContDiff ℝ ∞ (metricFromTwoForm (E := E)) :=
  ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (∞ : ℕ∞ω))
    (E := OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (F := E →L[ℝ] E →L[ℝ] ℝ) (metricFromTwoForm (E := E))

theorem metricFromTwoForm_pullback
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    (φ : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue F 2) (L : E →L[ℂ] F) (u v : E) :
    metricFromTwoForm (φ.compContinuousLinearMap (L.restrictScalars ℝ)) u v =
      metricFromTwoForm φ (L u) (L v) := by
  rw [metricFromTwoForm_apply, metricFromTwoForm_apply]
  apply congrArg Complex.re
  change φ (fun j => L (![u, Complex.I • v] j)) = φ ![L u, Complex.I • L v]
  apply congrArg φ
  funext j
  fin_cases j
  · rfl
  · exact L.map_smul Complex.I v

def varietyMetricInChart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (y : V.analyticModel) :
    V.analyticModel →L[ℝ] V.analyticModel →L[ℝ] ℝ :=
  metricFromTwoForm ((IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2).inChart e y)

theorem varietyMetricInChart_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    ContDiffOn ℝ ∞ (varietyMetricInChart V e) e.target := by
  change ContDiffOn ℝ ∞ ((metricFromTwoForm (E := V.analyticModel)) ∘
    (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2).inChart e) e.target
  have hm := metricFromTwoForm_smooth (E := V.analyticModel)
  have hf : ContDiffOn ℝ ∞
      ((IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2).inChart e) e.target := by
    simpa only [OAI.Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, Set.preimage_univ, Set.inter_univ] using
      (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V).smooth e he
  exact hm.comp_contDiffOn hf

theorem varietyMetricInChart_positive (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {y : V.analyticModel} (hy : y ∈ e.target)
    (u : V.analyticModel) (hu : u ≠ 0) : 0 < varietyMetricInChart V e y u u := by
  rw [varietyMetricInChart, metricFromTwoForm_apply]
  exact VarietyMetric.CM.Construction.varietyFubiniStudyForm_positive_inChart V e he hy u hu

theorem varietyMetricInChart_eq_fubiniStudy (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {y : V.analyticModel} (hy : y ∈ e.target)
    (i : Fin (V.ambientDimension + 1))
    (hi : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V (e.symm y)))
    (u v : V.analyticModel) :
    varietyMetricInChart V e y u v =
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm
        (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V) i (e.symm y))
        (fderiv ℂ (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V) i ∘ e.symm) y).toLinearMap
        u v).re := by
  rw [varietyMetricInChart, metricFromTwoForm_apply]
  change ((ProjectiveGluing.CM.Construction.projectiveCurvatureForm _ _ _ : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2).inChart e y
    ![u, Complex.I • v]).re = _
  rw [ProjectiveGluing.CM.Construction.projectiveCurvatureForm_inChart_apply _ _ _ e he hy i hi]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_smul,
    smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add, Complex.ofReal_re]

theorem varietyMetricInChart_symmetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {y : V.analyticModel} (hy : y ∈ e.target)
    (u v : V.analyticModel) : varietyMetricInChart V e y u v = varietyMetricInChart V e y v u := by
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch
    (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V (e.symm y))
  rw [varietyMetricInChart_eq_fubiniStudy V e he hy i hi,
    varietyMetricInChart_eq_fubiniStudy V e he hy i hi, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm_symm]
  simp only [Complex.star_def, Complex.conj_re]

theorem varietyMetricInChart_transition (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    {y : V.analyticModel} (hy : y ∈ e.target) (hfy : e.symm y ∈ f.source)
    (u v : V.analyticModel) :
    varietyMetricInChart V e y u v = varietyMetricInChart V f (f (e.symm y))
      (fderiv ℝ (f ∘ e.symm) y u) (fderiv ℝ (f ∘ e.symm) y v) := by
  have hhol := (OAI.Analysis.DifferentialForms.Manifold.ComplexCharts.complexContDiffAt_chart_transition e f he hf hy hfy).differentiableAt (by simp)
  rw [varietyMetricInChart,
    OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_transition _ e f he hf hy hfy, hhol.fderiv_restrictScalars ℝ,
    metricFromTwoForm_pullback]
  rfl

end

/-! The closedness of the actual projective Kähler form imposes the
first-derivative cyclic identity on its actual metric coefficients. -/

open scoped ContDiff _root_.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closed_twoForm_derivative (f : E → OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E}
    (hf : DifferentiableAt ℝ f x) (hclosed : extDeriv f x = 0) (u v w : E) :
    fderiv ℝ (fun y => f y ![v, w]) x u - fderiv ℝ (fun y => f y ![u, w]) x v +
      fderiv ℝ (fun y => f y ![u, v]) x w = 0 := by
  have h := congrArg (fun a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E 3 => a ![u, v, w]) hclosed
  rw [extDeriv_apply hf, Fin.sum_univ_three] at h
  have h0 : (0 : Fin 3).removeNth ![u, v, w] = ![v, w] := by ext i; fin_cases i <;> rfl
  have h1 : (1 : Fin 3).removeNth ![u, v, w] = ![u, w] := by ext i; fin_cases i <;> rfl
  have h2 : (2 : Fin 3).removeNth ![u, v, w] = ![u, v] := by ext i; fin_cases i <;> rfl
  rw [h0, h1, h2] at h
  change (1 : ℤ) • fderiv ℝ (fun y => f y ![v, w]) x u +
    (-1 : ℤ) • fderiv ℝ (fun y => f y ![u, w]) x v +
    (1 : ℤ) • fderiv ℝ (fun y => f y ![u, v]) x w = 0 at h
  simpa only [one_smul, neg_one_smul, sub_eq_add_neg] using h

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem metricFromTwoForm_J_right (f : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (v w : E) :
    metricFromTwoForm f v (Complex.I • w) = -(f ![v, w]).re := by
  rw [metricFromTwoForm_apply, smul_smul, Complex.I_mul_I, neg_one_smul]
  have h := (twoFormBilinear f v).map_neg w
  simp only [twoFormBilinear_apply] at h
  rw [h, Complex.neg_re]

theorem closed_twoForm_metric_derivative (f : E → OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E}
    (hf : DifferentiableAt ℝ f x) (hclosed : extDeriv f x = 0) (u v w : E) :
    fderiv ℝ (fun y => metricFromTwoForm (f y) v (Complex.I • w)) x u -
      fderiv ℝ (fun y => metricFromTwoForm (f y) u (Complex.I • w)) x v +
      fderiv ℝ (fun y => metricFromTwoForm (f y) u (Complex.I • v)) x w = 0 := by
  have hreal (a b c : E) :
      fderiv ℝ (fun y => metricFromTwoForm (f y) b (Complex.I • c)) x a =
        -(fderiv ℝ (fun y => f y ![b, c]) x a).re := by
    simp_rw [metricFromTwoForm_J_right]
    have hd := (hf.continuousAlternatingMap_apply_const ![b, c]).hasFDerivAt
    have hr := (Complex.reCLM.hasFDerivAt.comp x hd).neg
    change HasFDerivAt (fun y => -(f y ![b, c]).re)
      ((-Complex.reCLM).comp (fderiv ℝ (fun y => f y ![b, c]) x)) x at hr
    rw [hr.fderiv]
    rfl
  rw [hreal, hreal, hreal]
  have h := congrArg Complex.re (closed_twoForm_derivative f hf hclosed u v w)
  simp only [Complex.add_re, Complex.sub_re, Complex.zero_re] at h
  linarith

theorem varietyMetricInChart_closed_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {y : V.analyticModel} (hy : y ∈ e.target) (u v w : V.analyticModel) :
    fderiv ℝ (fun z => varietyMetricInChart V e z v (Complex.I • w)) y u -
      fderiv ℝ (fun z => varietyMetricInChart V e z u (Complex.I • w)) y v +
      fderiv ℝ (fun z => varietyMetricInChart V e z u (Complex.I • v)) y w = 0 := by
  have hf := (OAI.Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V).smooth e he hy).differentiableAt (by simp)
  have hd := OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V) e he hy
  rw [IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm_closed] at hd
  have hzero : extDeriv ((IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V).val.inChart e) y = 0 := by
    rw [← hd]
    ext s
    rfl
  exact closed_twoForm_metric_derivative _ hf hzero u v w

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction
