import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts

/-! # Variety Metric -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietyMetric.CM.Construction

noncomputable section

/-! Positivity of the actual Fubini--Study form on a smooth projective variety. -/

open scoped ContDiff _root_.Manifold _root_.Topology
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

attribute [local instance] IntrinsicProjectiveCharts.CM.Construction.projectiveIntegral IntrinsicProjectiveCharts.CM.Construction.projectiveSmooth IntrinsicProjectiveCharts.CM.Construction.projectiveNativeChartedSpace

def dropHomogeneousCoordinate (n : ℕ) (i : Fin (n + 1)) :
    (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Fintype.card {j : Fin (n + 1) // j ≠ i}) → ℂ) :=
  ContinuousLinearMap.pi (fun k =>
    ContinuousLinearMap.proj ((Fintype.equivFin {j : Fin (n + 1) // j ≠ i}).symm k).val)

theorem nativeProjectiveCoordinateChart_eq_drop (n : ℕ) (i : Fin (n + 1))
    (q : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) (hq : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q)) :
    IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart n i q = dropHomogeneousCoordinate n i
      (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q)) := by
  funext k
  exact IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart_apply n i q hq k

theorem nativeProjectiveEmbedding_fderiv_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {y : V.analyticModel} (hy : y ∈ e.target)
    (i : Fin (V.ambientDimension + 1))
    (hi : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V (e.symm y))) :
    Function.Injective (fderiv ℂ
      (IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart V.ambientDimension i ∘
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProjectiveScheme.CM.Construction.projectiveEmbeddingMap V) ∘ e.symm) y) := by
  let c : (ProjectiveScheme.CM.Construction.projectiveSpaceVariety V.ambientDimension).analyticSpace →
      (Fin (Fintype.card {j : Fin (V.ambientDimension + 1) // j ≠ i}) → ℂ) :=
    IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart V.ambientDimension i
  let a : V.analyticSpace → (ProjectiveScheme.CM.Construction.projectiveSpaceVariety V.ambientDimension).analyticSpace :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProjectiveScheme.CM.Construction.projectiveEmbeddingMap V)
  have hc : a (e.symm y) ∈ (IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart V.ambientDimension i).source :=
    IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart_mem_source V.ambientDimension i _ hi
  have hcD := IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart_mdifferentiable V.ambientDimension i
  have heD := mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, V.analyticModel)) he
  have haD := (ProjectiveScheme.CM.Construction.projectiveEmbeddingMap_holomorphic V).mdifferentiableAt
    (x := e.symm y) (by simp)
  have heAt := heD.symm.mdifferentiableAt hy
  have hcAt := hcD.mdifferentiableAt hc
  change Function.Injective (fderiv ℂ (c ∘ a ∘ e.symm) y)
  rw [← mfderiv_eq_fderiv, mfderiv_comp y hcAt (haD.comp y heAt), mfderiv_comp y haD heAt]
  exact (hcD.mfderiv_bijective hc).1.comp
    ((ProjectiveScheme.CM.Construction.projectiveEmbeddingMap_injective_differential V (e.symm y)).comp
      (heD.symm.mfderiv_bijective hy).1)

theorem projectiveEmbeddingCoordinates_fderiv_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {y : V.analyticModel} (hy : y ∈ e.target)
    (i : Fin (V.ambientDimension + 1))
    (hi : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V (e.symm y))) :
    Function.Injective (fderiv ℂ
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V) i ∘ e.symm) y) := by
  let U := ProjectiveGluing.CM.Construction.projectiveLiftDomain (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V) (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates_continuous V) i
  let F := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V) i ∘ e.symm
  let P := dropHomogeneousCoordinate V.ambientDimension i
  have hF : DifferentiableAt ℂ F y :=
    (ManifoldMetric.CM.Construction.manifoldLift_inChart_holomorphic U.isOpen _ (IntrinsicProjectiveCharts.CM.Construction.projectiveEmbeddingCoordinates_holomorphic V i)
      e he ⟨hy, hi⟩).differentiableAt (by simp)
  have hlocal : IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart V.ambientDimension i ∘
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProjectiveScheme.CM.Construction.projectiveEmbeddingMap V) ∘ e.symm =ᶠ[𝓝 y] P ∘ F := by
    filter_upwards [(Analysis.DifferentialForms.Manifold.Algebra.isOpen_manifoldFormChartDomain e U.isOpen).mem_nhds
      (show y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set V.analyticSpace) from ⟨hy, hi⟩)] with z hz
    exact nativeProjectiveCoordinateChart_eq_drop V.ambientDimension i _ hz.2
  have hder : fderiv ℂ (IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart V.ambientDimension i ∘
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProjectiveScheme.CM.Construction.projectiveEmbeddingMap V) ∘ e.symm) y = P.comp (fderiv ℂ F y) :=
    hlocal.fderiv_eq.trans (P.hasFDerivAt.comp y hF.hasFDerivAt).fderiv
  intro u v huv
  apply nativeProjectiveEmbedding_fderiv_injective V e he hy i hi
  rw [hder]
  change P (fderiv ℂ F y u) = P (fderiv ℂ F y v)
  exact congrArg P huv

/-- Positivity follows from the actual closed-immersion differential; no
metric or positivity assumption is attached to the variety. -/
theorem varietyFubiniStudyForm_positive_inChart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {y : V.analyticModel} (hy : y ∈ e.target)
    (u : V.analyticModel) (hu : u ≠ 0) :
    0 < ((IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2).inChart e y
      ![u, Complex.I • u]).re := by
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V (e.symm y))
  exact ProjectiveGluing.CM.Construction.projectiveCurvatureForm_positive_inChart (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V)
    (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates_continuous V) (IntrinsicProjectiveCharts.CM.Construction.projectiveEmbeddingCoordinates_holomorphic V)
    e he hy i hi (projectiveEmbeddingCoordinates_fderiv_injective V e he hy i hi) u hu

theorem varietyFubiniStudyForm_real_inChart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {y : V.analyticModel} (hy : y ∈ e.target)
    (v : Fin 2 → V.analyticModel) :
    ((IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2).inChart e y v).im = 0 := by
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V (e.symm y))
  rw [show (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2) =
    ProjectiveGluing.CM.Construction.projectiveCurvatureForm (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V) (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates_continuous V)
      (IntrinsicProjectiveCharts.CM.Construction.projectiveEmbeddingCoordinates_holomorphic V) from rfl]
  rw [ProjectiveGluing.CM.Construction.projectiveCurvatureForm_inChart_apply _ _ _ e he hy i hi]
  exact Complex.ofReal_im _

theorem varietyFubiniStudyForm_positive (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x : V.analyticSpace)
    (u : TangentSpace 𝓘(ℝ, V.analyticModel) x) (hu : u ≠ 0) :
    0 < (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I u]).re := by
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas _ x
  have hx : x ∈ e.source := mem_chart_source _ x
  let τ := Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := V.analyticModel) x
  have hτu : τ u ≠ 0 := by
    intro h
    exact hu (τ.injective (h.trans τ.map_zero.symm))
  have hp := varietyFubiniStudyForm_positive_inChart V e he (e.map_source hx) (τ u) hτu
  have hval : (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2).inChart e
      (e x) ![τ u, Complex.I • τ u] =
      IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I u] := by
    rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at _ e he x hx]
    apply congrArg (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x)
    funext j
    fin_cases j
    · exact τ.symm_apply_apply u
    · rfl
  rwa [hval] at hp

theorem varietyFubiniStudyForm_real (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x : V.analyticSpace)
    (v : Fin 2 → TangentSpace 𝓘(ℝ, V.analyticModel) x) :
    (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x v).im = 0 := by
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas _ x
  have hx : x ∈ e.source := mem_chart_source _ x
  let τ := Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx
  have hr := varietyFubiniStudyForm_real_inChart V e he (e.map_source hx) (fun i => τ (v i))
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at _ e he x hx] at hr
  simpa only [τ, ContinuousLinearEquiv.symm_apply_apply] using hr

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietyMetric.CM.Construction
