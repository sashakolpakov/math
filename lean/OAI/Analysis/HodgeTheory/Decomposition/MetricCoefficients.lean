import OAI.Analysis.HodgeTheory.Decomposition.Contraction
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric

/-! # Metric Coefficients -/

namespace OAI.Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions

noncomputable section

section

/-! The form metric in fixed chart coordinates, expressed by minors of the
actual tangent metric and inversion of their Gram matrix. -/

open scoped BigOperators ContDiff _root_.Manifold

section MatrixSmoothness

variable {D ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [Fintype ι] [DecidableEq ι] {U : Set D}

theorem matrixDet_smoothOn (A : D → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) :
    ContDiffOn ℝ ∞ (fun x => (A x).det) U := by
  simp only [Matrix.det_apply']
  fun_prop

theorem matrixInverse_entry_smoothOn (A : D → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hdet : ∀ x ∈ U, (A x).det ≠ 0) (i j : ι) :
    ContDiffOn ℝ ∞ (fun x => (A x)⁻¹ i j) U := by
  have hd : ContDiffOn ℝ ∞ (fun x => (A x).det⁻¹) U := (matrixDet_smoothOn A hA).inv hdet
  have ha : ContDiffOn ℝ ∞ (fun x => ((A x).updateRow j (Pi.single i 1)).det) U := by
    apply matrixDet_smoothOn
    intro k l
    by_cases hkj : k = j
    · subst k
      simpa only [Matrix.updateRow_self] using
        (contDiffOn_const (c := (Pi.single i 1 : ι → ℝ) l))
    · simpa only [Matrix.updateRow_ne hkj] using hA k l
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  exact hd.mul ha

end MatrixSmoothness

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι ℝ V.analyticModel) (n : ℕ)

def exteriorCoordinateTuple (s : Set.powersetCard ι n) : Fin n → V.analyticModel :=
  b ∘ (Set.powersetCard.ofFinEmbEquiv.symm s)

def projectiveExteriorGram (y : V.analyticModel) :
    Matrix (Set.powersetCard ι n) (Set.powersetCard ι n) ℝ :=
  fun s t => Matrix.det (fun i j : Fin n =>
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y (exteriorCoordinateTuple V b n s j) (exteriorCoordinateTuple V b n t i))

def projectiveExteriorBasis (y : V.analyticModel) (hy : y ∈ e.target) :
    Module.Basis (Set.powersetCard ι n) ℝ (⋀[ℝ]^n (MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy)) :=
  (b.map (ProjectiveFormMetric.Constructions.projectiveMetricFiberRealEquiv V e he y hy).symm.toLinearEquiv).exteriorPower n

omit [Fintype ι] in
theorem projectiveExteriorBasis_gram (y : V.analyticModel) (hy : y ∈ e.target) :
    Matrix.gram ℝ (projectiveExteriorBasis V e he b n y hy) = projectiveExteriorGram V e b n y := by
  ext s t
  simp only [Matrix.gram_apply, projectiveExteriorBasis, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.inner_ιMulti_ιMulti]
  apply congrArg Matrix.det
  ext i j
  simp only [Matrix.of_apply, Function.comp_apply, Module.Basis.map_apply]
  rw [ProjectiveFormMetric.Constructions.projectiveMetricFiber_real_inner]
  rfl

include he

theorem projectiveExteriorGram_det_ne_zero (y : V.analyticModel) (hy : y ∈ e.target) :
    (projectiveExteriorGram V e b n y).det ≠ 0 := by
  rw [← projectiveExteriorBasis_gram V e he b n y hy]
  exact (Matrix.posDef_gram_of_linearIndependent
    (projectiveExteriorBasis V e he b n y hy).linearIndependent).det_pos.ne'

omit [Fintype ι] in
theorem projectiveExteriorGram_entry_smooth (s t : Set.powersetCard ι n) :
    ContDiffOn ℝ ∞ (fun y => projectiveExteriorGram V e b n y s t) e.target := by
  apply matrixDet_smoothOn
  intro i j
  exact ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_smooth V e he).clm_apply
    (contDiffOn_const (c := exteriorCoordinateTuple V b n s j))).clm_apply
    (contDiffOn_const (c := exteriorCoordinateTuple V b n t i))

theorem projectiveExteriorGram_inverse_smooth (s t : Set.powersetCard ι n) :
    ContDiffOn ℝ ∞ (fun y => (projectiveExteriorGram V e b n y)⁻¹ s t) e.target :=
  matrixInverse_entry_smoothOn (projectiveExteriorGram V e b n)
    (projectiveExteriorGram_entry_smooth V e he b n)
    (projectiveExteriorGram_det_ne_zero V e he b n) s t

omit [Fintype ι] in
/-- Covector values on the transported exterior basis are the fixed chart coefficients. -/
theorem metricCoordinateForm_exteriorBasis (y : V.analyticModel) (hy : y ∈ e.target)
    (form : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n) (s : Set.powersetCard ι n) :
    DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv (MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) n
      (ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n form) (projectiveExteriorBasis V e he b n y hy s) =
      form (exteriorCoordinateTuple V b n s) := by
  simp only [projectiveExteriorBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_apply_ιMulti]
  rfl

/-- The global metric's chart expression is an explicit inverse-Gram contraction. -/
theorem projectiveChartFormPair_coordinate_formula (y : V.analyticModel) (hy : y ∈ e.target)
    (a c : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n) :
    ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a c =
      ∑ s, ∑ t, star (a (exteriorCoordinateTuple V b n t)) *
        ((projectiveExteriorGram V e b n y)⁻¹ s t : ℂ) * c (exteriorCoordinateTuple V b n s) := by
  unfold ProjectiveFormMetric.Constructions.projectiveChartFormPair ExteriorPair.Constructions.formMetricPair
  rw [Contraction.Constructions.covectorInner_inverse_gram (projectiveExteriorBasis V e he b n y hy)]
  simp only [projectiveExteriorBasis_gram, metricCoordinateForm_exteriorBasis]

end

/-! Smoothness of the genuine pointwise form metric, proved through the fixed
coordinate contraction formula. -/

open scoped BigOperators ContDiff _root_.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation at a fixed tuple is a bounded linear functional on alternating covectors. -/
def formEvaluation (n : ℕ) (v : Fin n → E) : DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun form => form v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (∏ i, ‖v i‖) (fun form => by
      change ‖form v‖ ≤ (∏ i, ‖v i‖) * ‖form‖
      rw [mul_comm]
      exact form.le_opNorm v)

theorem smooth_fixed_form_evaluation {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (n : ℕ) (v : Fin n → E) {U : Set D} {a : D → DifferentialForms.Manifold.Basic.FormValue E n}
    (ha : ContDiffOn ℝ ∞ a U) : ContDiffOn ℝ ∞ (fun y => a y v) U :=
  (formEvaluation n v).contDiff.comp_contDiffOn ha

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

def projectiveFormMetricExpression
    (a c : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (y : V.analyticModel) : ℂ :=
  let b := Module.finBasis ℝ V.analyticModel
  ∑ s, ∑ t, star (a.inChart e y (exteriorCoordinateTuple V b n t)) *
    ((projectiveExteriorGram V e b n y)⁻¹ s t : ℂ) * c.inChart e y (exteriorCoordinateTuple V b n s)

include he

theorem projectiveFormPointPair_chartExpression
    (a c : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (y : V.analyticModel) (hy : y ∈ e.target) :
    ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a c (e.symm y) = projectiveFormMetricExpression V e n a c y := by
  rw [ProjectiveFormMetric.Constructions.projectiveFormPointPair_eq_chart V e he (e.symm y) (e.map_target hy),
    projectiveChartFormPair_coordinate_formula V e he (Module.finBasis ℝ V.analyticModel) n]
  simp only [e.right_inv hy, projectiveFormMetricExpression]

theorem projectiveFormMetricExpression_smooth
    (a c : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    ContDiffOn ℝ ∞ (projectiveFormMetricExpression V e n a.val c.val) e.target := by
  let b := Module.finBasis ℝ V.analyticModel
  have ha : ContDiffOn ℝ ∞ (a.val.inChart e) e.target := by
    simpa only [DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, Set.preimage_univ, Set.inter_univ] using a.smooth e he
  have hc : ContDiffOn ℝ ∞ (c.val.inChart e) e.target := by
    simpa only [DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, Set.preimage_univ, Set.inter_univ] using c.smooth e he
  have hevala (s : Set.powersetCard (Fin (Module.finrank ℝ V.analyticModel)) n) :
      ContDiffOn ℝ ∞ (fun y => a.val.inChart e y (exteriorCoordinateTuple V b n s)) e.target :=
    smooth_fixed_form_evaluation n _ ha
  have hevalc (s : Set.powersetCard (Fin (Module.finrank ℝ V.analyticModel)) n) :
      ContDiffOn ℝ ∞ (fun y => c.val.inChart e y (exteriorCoordinateTuple V b n s)) e.target :=
    smooth_fixed_form_evaluation n _ hc
  have hcoeff (s t : Set.powersetCard (Fin (Module.finrank ℝ V.analyticModel)) n) :
      ContDiffOn ℝ ∞ (fun y => ((projectiveExteriorGram V e b n y)⁻¹ s t : ℂ)) e.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (projectiveExteriorGram_inverse_smooth V e he b n s t)
  have hconj : ContDiff ℝ ∞ (star : ℂ → ℂ) := Complex.conjCLE.contDiff
  unfold projectiveFormMetricExpression
  change ContDiffOn ℝ ∞ (fun y => ∑ s, ∑ t,
    star (a.val.inChart e y (exteriorCoordinateTuple V b n t)) *
      ((projectiveExteriorGram V e b n y)⁻¹ s t : ℂ) *
      c.val.inChart e y (exteriorCoordinateTuple V b n s)) e.target
  fun_prop

/-- In every genuine chart the global metric pairing of smooth forms is smooth. -/
theorem projectiveFormPointPair_smooth_inChart
    (a c : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    ContDiffOn ℝ ∞ (fun y => ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val c.val (e.symm y)) e.target := by
  apply (projectiveFormMetricExpression_smooth V e he n a c).congr
  intro y hy
  exact projectiveFormPointPair_chartExpression V e he n a.val c.val y hy

omit he in
/-- The genuine pointwise metric pairing of smooth forms is continuous globally. -/
theorem projectiveFormPointPair_continuous
    (a c : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    Continuous (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val c.val) := by
  rw [continuous_iff_continuousAt]
  intro x
  let e := chartAt V.analyticModel x
  have he := chart_mem_atlas V.analyticModel x
  have hx := mem_chart_source V.analyticModel x
  have hc := (projectiveFormMetricExpression_smooth V e he n a c).continuousOn.continuousAt
    (e.open_target.mem_nhds (e.map_source hx))
  have hec := e.continuousOn.continuousAt (e.open_source.mem_nhds hx)
  have hcomp : ContinuousAt (fun z => projectiveFormMetricExpression V e n a.val c.val (e z)) x :=
    hc.comp hec
  apply hcomp.congr
  filter_upwards [e.open_source.mem_nhds hx] with z hz
  have h := projectiveFormPointPair_chartExpression V e he n a.val c.val (e z) (e.map_source hz)
  simpa only [e.left_inv hz] using h.symm

end

end OAI.Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions
