import OAI.Analysis.HodgeTheory.Decomposition.MetricCoefficients
import OAI.Analysis.HodgeTheory.Decomposition.UnitaryTypes
import OAI.Analysis.HodgeTheory.Decomposition.Projectors

/-! # Global Orthogonality -/

namespace OAI.Analysis.HodgeTheory.Decomposition.GlobalOrthogonality.Constructions

noncomputable section

/-! Orthogonality of the actual componentwise pure forms for the global
projective metric, before taking de Rham cohomology. -/

open scoped _root_.Manifold

theorem metricCoordinateForm_pure (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (y : V.analyticModel) (hy : y ∈ e.target)
    (n : ℕ) (i : Core.Constructions.Bidegree n) (a : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n)
    (ha : a.toAlternatingMap ∈ Pointwise.Constructions.algebraicPureSpace V.analyticModel n i) :
    (ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n a).toAlternatingMap ∈
      Pointwise.Constructions.algebraicPureSpace (MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) n i := by
  intro z v
  change a (fun k => MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy ((z : ℂ) • v k)) =
    DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z * a (fun k => MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy (v k))
  simp only [map_smul]
  exact ha z (fun k => MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy (v k))

theorem projectiveChartFormPair_pure_orthogonal (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (y : V.analyticModel) (hy : y ∈ e.target)
    (n : ℕ) (i j : Core.Constructions.Bidegree n) (hij : i ≠ j) (a b : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n)
    (ha : a.toAlternatingMap ∈ Pointwise.Constructions.algebraicPureSpace V.analyticModel n i)
    (hb : b.toAlternatingMap ∈ Pointwise.Constructions.algebraicPureSpace V.analyticModel n j) :
    ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a b = 0 :=
  UnitaryTypes.Constructions.formMetricPair_pure_orthogonal n i j hij _ _
    (metricCoordinateForm_pure V e he y hy n i a ha)
    (metricCoordinateForm_pure V e he y hy n j b hb)

theorem projectiveFormPointPair_pure_orthogonal (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (n : ℕ) (i j : Core.Constructions.Bidegree n) (hij : i ≠ j)
    (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (ha : ∀ e ∈ atlas V.analyticModel V.analyticSpace, ∀ y ∈ e.target,
      (a.inChart e y).toAlternatingMap ∈ Pointwise.Constructions.algebraicPureSpace V.analyticModel n i)
    (hb : ∀ e ∈ atlas V.analyticModel V.analyticSpace, ∀ y ∈ e.target,
      (b.inChart e y).toAlternatingMap ∈ Pointwise.Constructions.algebraicPureSpace V.analyticModel n j)
    (x : V.analyticSpace) : ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b x = 0 := by
  let e := chartAt V.analyticModel x
  have he := chart_mem_atlas V.analyticModel x
  have hx := mem_chart_source V.analyticModel x
  rw [ProjectiveFormMetric.Constructions.projectiveFormPointPair_eq_chart V e he x hx]
  exact projectiveChartFormPair_pure_orthogonal V e he (e x) (e.map_source hx) n i j hij _ _
    (ha e he (e x) (e.map_source hx)) (hb e he (e x) (e.map_source hx))

def componentPointPair (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (a b : X.componentForms n) (C : irreducibleComponents X.carrier)
    (x : (X.componentVariety C).analyticSpace) : ℂ :=
  ProjectiveFormMetric.Constructions.projectiveFormPointPair (X.componentVariety C) n (a C).val (b C).val x

/-- Distinct global pure types are pointwise orthogonal in the constructed projective metric. -/
theorem componentPointPair_pure_orthogonal (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (i j : Core.Constructions.Bidegree n) (hij : i ≠ j) (a b : X.componentForms n)
    (ha : a ∈ Core.Constructions.pureFormsAt X n i) (hb : b ∈ Core.Constructions.pureFormsAt X n j)
    (C : irreducibleComponents X.carrier) (x : (X.componentVariety C).analyticSpace) :
    componentPointPair X n a b C x = 0 :=
  projectiveFormPointPair_pure_orthogonal (X.componentVariety C) n i j hij (a C).val (b C).val
    ((Projectors.Constructions.pureFormsAt_iff_chartEval X n i a).mp ha C)
    ((Projectors.Constructions.pureFormsAt_iff_chartEval X n j b).mp hb C) x

theorem componentPointPair_continuous (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (a b : X.componentForms n) (C : irreducibleComponents X.carrier) :
    Continuous (componentPointPair X n a b C) :=
  MetricCoefficients.Constructions.projectiveFormPointPair_continuous (X.componentVariety C) n (a C) (b C)

/-- The pointwise metric detects zero of an actual smooth componentwise form. -/
theorem componentPointPair_definite (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (a : X.componentForms n)
    (ha : ∀ C x, componentPointPair X n a a C x = 0) : a = 0 := by
  funext C
  apply DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  exact ProjectiveFormMetric.Constructions.projectiveFormPointPair_definite (X.componentVariety C) n (a C).val x (ha C x)

end

end OAI.Analysis.HodgeTheory.Decomposition.GlobalOrthogonality.Constructions
