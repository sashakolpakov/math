import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HomogeneousMetric
import OAI.Analysis.DifferentialForms.Manifold.LocalPullback
import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import OAI.Analysis.DifferentialForms.Manifold.Holomorphic

/-! # Manifold Metric -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ManifoldMetric.CM.Construction

noncomputable section

/-! The Fubini--Study curvature in actual manifold tangent spaces. -/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem rawForm_toManifold_smoothOn {form : Analysis.DifferentialForms.Manifold.Basic.RawForm E n} {U : Set E}
    (hform : ContDiffOn ℝ ∞ form U) : Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn form.toManifold U := by
  intro e he
  rw [chartedSpaceSelf_atlas] at he
  subst e
  simpa only [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_refl, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.toNormedSpace_toManifold,
    Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, OpenPartialHomeomorph.refl_target,
    OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
    Set.preimage_id, Set.univ_inter] using hform

theorem rawForm_toManifold_extDeriv (form : Analysis.DifferentialForms.Manifold.Basic.RawForm E n) :
    form.toManifold.exteriorDerivative = Analysis.DifferentialForms.Manifold.Basic.RawForm.toManifold (extDeriv form) := by
  funext x
  change ((extDeriv (form.toManifold.inChart (OpenPartialHomeomorph.refl E)) x).compContinuousLinearMap
    (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (OpenPartialHomeomorph.refl E) x)) = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_refl, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.toNormedSpace_toManifold]
  unfold Analysis.DifferentialForms.Manifold.Charts.chartTangentMap
  change (extDeriv form x).compContinuousLinearMap
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (@id E) x)) = _
  rw [mfderiv_id, ContinuousLinearMap.comp_id]
  rfl

variable {ι : Type*} [Fintype ι]

def homogeneousManifoldBerry : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (ι → ℂ) (ι → ℂ) 1 :=
  Analysis.DifferentialForms.Manifold.Basic.RawForm.toManifold HomogeneousMetric.CM.Construction.homogeneousBerryRawForm

theorem homogeneousManifoldBerry_smooth :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (homogeneousManifoldBerry (ι := ι))
      (HomogeneousMetric.CM.Construction.nonzeroHomogeneousDomain (ι := ι) : Set (ι → ℂ)) :=
  rawForm_toManifold_smoothOn (HomogeneousMetric.CM.Construction.homogeneousBerryRawForm_smoothOn (ι := ι))

theorem homogeneousManifoldBerry_curvature (w : HomogeneousMetric.CM.Construction.nonzeroHomogeneousDomain (ι := ι)) :
    homogeneousManifoldBerry.exteriorDerivative (w : ι → ℂ) =
      (HomogeneousMetric.CM.Construction.homogeneousFubiniStudyTwoForm w).compContinuousLinearMap
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (w : ι → ℂ)).toContinuousLinearMap := by
  rw [homogeneousManifoldBerry, rawForm_toManifold_extDeriv]
  have hd := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_ofRaw_apply HomogeneousMetric.CM.Construction.homogeneousBerryRawForm HomogeneousMetric.CM.Construction.homogeneousBerryRawForm_smoothOn w
  change HomogeneousMetric.CM.Construction.homogeneousFubiniStudyTwoForm w = extDeriv HomogeneousMetric.CM.Construction.homogeneousBerryRawForm (w : ι → ℂ) at hd
  rw [hd]
  rfl

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def manifoldLiftBerry (f : M → ι → ℂ) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M 1 :=
  homogeneousManifoldBerry.pullback f

def manifoldLiftCurvature (f : M → ι → ℂ) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M 2 :=
  (manifoldLiftBerry (E := E) f).exteriorDerivative

variable {U : Set M} (hU : IsOpen U) (f : M → ι → ℂ)
  (hf : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ f U) (hn : ∀ x ∈ U, f x ≠ 0)

omit [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [IsManifold 𝓘(ℂ, E) ∞ M] [ChartedSpace E M] in
theorem manifoldChartDomain_point {e : OpenPartialHomeomorph M E} {y : E}
    (hy : y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e U) : e.symm y ∈ U := hy.2

include hU hf in
omit [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem manifoldLift_realSmooth : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ι → ℂ) ∞ f U := by
  intro x hx
  exact (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiffAt_real_of_complex ((hf x hx).contMDiffAt (hU.mem_nhds hx))).contMDiffWithinAt

include hU hf hn in
theorem manifoldLiftBerry_smooth : Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (manifoldLiftBerry (E := E) f) U := by
  apply Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.pullback_smooth_on _ hU
    (HomogeneousMetric.CM.Construction.nonzeroHomogeneousDomain (ι := ι)).isOpen homogeneousManifoldBerry_smooth
    f (manifoldLift_realSmooth hU f hf)
  exact hn

include hU hf hn in
theorem manifoldLiftCurvature_smooth : Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (manifoldLiftCurvature (E := E) f) U :=
  (manifoldLiftBerry (E := E) f).exteriorDerivative_smooth_on hU (manifoldLiftBerry_smooth hU f hf hn)

include hU hf hn in
theorem manifoldLiftCurvature_closed {x : M} (hx : x ∈ U) :
    (manifoldLiftCurvature (E := E) f).exteriorDerivative x = 0 :=
  (manifoldLiftBerry (E := E) f).exteriorDerivative_squared_on hU
    (manifoldLiftBerry_smooth hU f hf hn) hx

include hU hf in
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem manifoldLift_inChart_holomorphic (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) {y : E} (hy : y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e U) :
    ContDiffAt ℂ ∞ (f ∘ e.symm) y := by
  have he' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ e.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy.1
  exact (((hf (e.symm y) hy.2).contMDiffAt (hU.mem_nhds hy.2)).comp y he').contDiffAt

include hU hf in
theorem manifoldLiftCurvature_inChart (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) {y : E} (hy : y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e U) :
    (manifoldLiftCurvature (E := E) f).inChart e y =
      (HomogeneousMetric.CM.Construction.homogeneousFubiniStudyTwoForm ⟨f (e.symm y), hn _ (manifoldChartDomain_point hy)⟩).compContinuousLinearMap
        (fderiv ℝ (f ∘ e.symm) y) := by
  have hloc := (homogeneousManifoldBerry (ι := ι)).pullback_inChart_eventuallyEq_on f hU
    (manifoldLift_realSmooth hU f hf) e (OpenPartialHomeomorph.refl (ι → ℂ))
    he (by simp) hy (by simp)
  have hloc' : (manifoldLiftBerry (E := E) f).inChart e =ᶠ[𝓝 y]
      fun z => (HomogeneousMetric.CM.Construction.homogeneousBerryRawForm (f (e.symm z))).compContinuousLinearMap
        (fderiv ℝ (f ∘ e.symm) z) := by
    simpa only [manifoldLiftBerry, homogeneousManifoldBerry, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_refl,
      Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.toNormedSpace_toManifold, OpenPartialHomeomorph.refl_apply,
      Function.id_comp, id_eq] using hloc
  rw [manifoldLiftCurvature, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.exteriorDerivative_inChart_on _ hU
    (manifoldLiftBerry_smooth hU f hf hn) e he hy, hloc'.extDeriv_eq]
  have hchain := extDeriv_pullback (f := f ∘ e.symm)
    ((HomogeneousMetric.CM.Construction.homogeneousBerryRawForm_smoothAt (hn _ (manifoldChartDomain_point hy))).differentiableAt (by simp))
    ((manifoldLift_inChart_holomorphic hU f hf e he hy).restrict_scalars ℝ)
    Analysis.DifferentialForms.Manifold.SquareZero.minSmoothness_real_two_le_infty
  change extDeriv (fun z => (HomogeneousMetric.CM.Construction.homogeneousBerryRawForm ((f ∘ e.symm) z)).compContinuousLinearMap
    (fderiv ℝ (f ∘ e.symm) z)) y = _
  rw [hchain]
  have hd := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_ofRaw_apply HomogeneousMetric.CM.Construction.homogeneousBerryRawForm HomogeneousMetric.CM.Construction.homogeneousBerryRawForm_smoothOn
    (⟨f (e.symm y), hn _ hy.2⟩ : HomogeneousMetric.CM.Construction.nonzeroHomogeneousDomain (ι := ι))
  exact congrArg (fun value : Analysis.DifferentialForms.Manifold.Basic.FormValue (ι → ℂ) 2 =>
    value.compContinuousLinearMap (fderiv ℝ (f ∘ e.symm) y)) hd.symm

include hU hf hn in
theorem manifoldLiftCurvature_hasBidegree (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) {y : E} (hy : y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e U) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 ((manifoldLiftCurvature (E := E) f).inChart e y) := by
  rw [manifoldLiftCurvature_inChart hU f hf hn e he hy]
  rw [((manifoldLift_inChart_holomorphic hU f hf e he hy).differentiableAt
    (by simp)).fderiv_restrictScalars ℝ]
  exact AlgebraicTopology.DeRham.Comparison.BidegreeRestriction.hasBidegree_pullback (HomogeneousMetric.CM.Construction.homogeneousFubiniStudyTwoForm_hasBidegree _)
    (fderiv ℂ (f ∘ e.symm) y)

include hU hf hn in
theorem manifoldLiftCurvature_inChart_apply (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) {y : E} (hy : y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e U) (v : Fin 2 → E) :
    (manifoldLiftCurvature (E := E) f).inChart e y v = Complex.ofReal
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm (f (e.symm y)) (fderiv ℂ (f ∘ e.symm) y).toLinearMap
        (v 0) (v 1)).im := by
  rw [manifoldLiftCurvature_inChart hU f hf hn e he hy,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, HomogeneousMetric.CM.Construction.homogeneousFubiniStudyTwoForm_apply]
  rw [((manifoldLift_inChart_holomorphic hU f hf e he hy).differentiableAt
    (by simp)).fderiv_restrictScalars ℝ]
  rfl

theorem rawManifoldForm_eq_at_of_inChart_eq (form other : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (x : M) (hx : x ∈ e.source)
    (h : form.inChart e (e x) = other.inChart e (e x)) : form x = other x := by
  ext v
  have hval := congrArg (fun α : Analysis.DifferentialForms.Manifold.Basic.FormValue E n => α (fun i => Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx (v i))) h
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at] at hval
  · simpa only [ContinuousLinearEquiv.symm_apply_apply] using hval
  all_goals assumption

include hU hf hn in
theorem manifoldLiftCurvature_gauge
    (g : M → ι → ℂ) (hg : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ g U)
    (hng : ∀ x ∈ U, g x ≠ 0) (a : M → ℂ) (ha : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ a U)
    (hna : ∀ x ∈ U, a x ≠ 0) (hfg : ∀ x ∈ U, f x = a x • g x) {x : M} (hx : x ∈ U) :
    manifoldLiftCurvature (E := E) f x = manifoldLiftCurvature (E := E) g x := by
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hex : x ∈ e.source := mem_chart_source E x
  have hy : e x ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e U :=
    ⟨e.map_source hex, by
      change e.symm (e x) ∈ U
      simpa only [e.left_inv hex] using hx⟩
  apply rawManifoldForm_eq_at_of_inChart_eq _ _ e he x hex
  ext v
  rw [manifoldLiftCurvature_inChart_apply hU f hf hn e he hy,
    manifoldLiftCurvature_inChart_apply hU g hg hng e he hy]
  have hga := manifoldLift_inChart_holomorphic hU g hg e he hy
  have haa : ContDiffAt ℂ ∞ (a ∘ e.symm) (e x) :=
    (((ha (e.symm (e x)) hy.2).contMDiffAt (hU.mem_nhds hy.2)).comp (e x)
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy.1)).contDiffAt
  have hloc : f ∘ e.symm =ᶠ[𝓝 (e x)] (a ∘ e.symm) • (g ∘ e.symm) := by
    filter_upwards [(Analysis.DifferentialForms.Manifold.Algebra.isOpen_manifoldFormChartDomain e hU).mem_nhds hy] with z hz
    exact hfg _ hz.2
  have hD : (fderiv ℂ (f ∘ e.symm) (e x)).toLinearMap =
      a (e.symm (e x)) • (fderiv ℂ (g ∘ e.symm) (e x)).toLinearMap +
      (fderiv ℂ (a ∘ e.symm) (e x)).toLinearMap.smulRight (g (e.symm (e x))) := by
    rw [hloc.fderiv_eq]
    exact congrArg ContinuousLinearMap.toLinearMap
      (fderiv_smul (haa.differentiableAt (by simp)) (hga.differentiableAt (by simp)))
  rw [hfg _ hy.2, hD, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm_gauge
    (a (e.symm (e x))) (hna _ hy.2) (g (e.symm (e x))) (hng _ hy.2)]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ManifoldMetric.CM.Construction
