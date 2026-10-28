import OAI.Analysis.DifferentialForms.Manifold.PullbackLaws
import OAI.Analysis.DifferentialForms.Manifold.LocalDerivative

/-! # Local Pullback -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Pullback on open manifold domains

The ordinary tangent pullback requires smoothness only on its actual source
domain. Its smoothness and compatibility with exterior differentiation are
proved from the local coordinate formulas and the genuine manifold chain rule.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  {n : ℕ} {S : Set M} {T : Set N}

theorem Algebra.RawManifoldForm.pullback_inChart_eventuallyEq_on (form : Algebra.RawManifoldForm F N n)
    (g : M → N) (hS : IsOpen S) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g S)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ atlas E M) (hf : f ∈ atlas F N) {y : E}
    (hy : y ∈ Algebra.manifoldFormChartDomain e S) (hfy : g (e.symm y) ∈ f.source) :
    (form.pullback g).inChart e =ᶠ[𝓝 y]
      fun z => (form.inChart f (f (g (e.symm z)))).compContinuousLinearMap
        (fderiv ℝ (f ∘ g ∘ e.symm) z) := by
  have hgAt := (hg (e.symm y) hy.2).contMDiffAt (hS.mem_nhds hy.2)
  have hsource : ∀ᶠ z in 𝓝 y, e.symm z ∈ S :=
    (e.continuousAt_symm hy.1).preimage_mem_nhds (hS.mem_nhds hy.2)
  have htarget : ∀ᶠ z in 𝓝 y, g (e.symm z) ∈ f.source :=
    (hgAt.continuousAt.comp (e.continuousAt_symm hy.1)).preimage_mem_nhds
      (f.open_source.mem_nhds hfy)
  filter_upwards [e.open_target.mem_nhds hy.1, hsource, htarget] with z hz hzS hzF
  exact form.pullback_inChart g e f he hf hz hzF
    (((hg (e.symm z) hzS).contMDiffAt (hS.mem_nhds hzS)).mdifferentiableAt (by simp))

/-- Actual tangent pullback preserves smoothness on the given open domains. -/
theorem Algebra.RawManifoldForm.pullback_smooth_on (form : Algebra.RawManifoldForm F N n)
    (hS : IsOpen S) (hT : IsOpen T) (hform : Algebra.IsSmoothManifoldFormOn form T)
    (g : M → N) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g S)
    (hmap : MapsTo g S T) :
    Algebra.IsSmoothManifoldFormOn (E := E) (form.pullback g) S := by
  intro e he y hy
  let f := chartAt F (g (e.symm y))
  have hf : f ∈ atlas F N := chart_mem_atlas F (g (e.symm y))
  have hfy : g (e.symm y) ∈ f.source := mem_chart_source F (g (e.symm y))
  have hgAt := (hg (e.symm y) hy.2).contMDiffAt (hS.mem_nhds hy.2)
  have hcoord := ManifoldPullback.contDiffAt_manifoldMap_inChart g e f he hf hy.1 hfy hgAt
  have hfT : f (g (e.symm y)) ∈ Algebra.manifoldFormChartDomain f T := by
    refine ⟨f.map_source hfy, ?_⟩
    change f.symm (f (g (e.symm y))) ∈ T
    rw [f.left_inv hfy]
    exact hmap hy.2
  have hcoeff : ContDiffAt ℝ ∞ (form.inChart f) (f (g (e.symm y))) :=
    LocalDerivative.smoothManifoldFormOn_contDiffAt_inChart hT hform f hf hfT
  have hcomposed : ContDiffAt ℝ ∞
      (fun z => form.inChart f (f (g (e.symm z)))) y :=
    ContDiffAt.comp (𝕜 := ℝ) (n := ∞)
      (f := f ∘ g ∘ e.symm) (g := form.inChart f) y hcoeff hcoord
  have hsmooth : ContDiffAt ℝ ∞ (fun z =>
      (form.inChart f (f (g (e.symm z)))).compContinuousLinearMap
        (fderiv ℝ (f ∘ g ∘ e.symm) z)) y :=
    Alternatization.contDiffAt_alternating_compContinuousLinearMap
      hcomposed (hcoord.fderiv_right (by simp))
  exact (hsmooth.congr_of_eventuallyEq
    (form.pullback_inChart_eventuallyEq_on g hS hg e f he hf hy hfy)).contDiffWithinAt

/-- The coordinate exterior-derivative chain rule needs only local smoothness. -/
theorem Algebra.RawManifoldForm.extDeriv_pullback_inChart_on (form : Algebra.RawManifoldForm F N n)
    (hS : IsOpen S) (hT : IsOpen T) (hform : Algebra.IsSmoothManifoldFormOn form T)
    (g : M → N) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g S)
    (hmap : MapsTo g S T)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ atlas E M) (hf : f ∈ atlas F N) {y : E}
    (hy : y ∈ Algebra.manifoldFormChartDomain e S) (hfy : g (e.symm y) ∈ f.source) :
    extDeriv ((form.pullback g).inChart e) y =
      (extDeriv (form.inChart f) (f (g (e.symm y)))).compContinuousLinearMap
        (fderiv ℝ (f ∘ g ∘ e.symm) y) := by
  rw [(form.pullback_inChart_eventuallyEq_on g hS hg e f he hf hy hfy).extDeriv_eq]
  have hfT : f (g (e.symm y)) ∈ Algebra.manifoldFormChartDomain f T := by
    refine ⟨f.map_source hfy, ?_⟩
    change f.symm (f (g (e.symm y))) ∈ T
    rw [f.left_inv hfy]
    exact hmap hy.2
  exact extDeriv_pullback
    ((LocalDerivative.smoothManifoldFormOn_contDiffAt_inChart hT hform f hf hfT).differentiableAt
      (by simp))
    (ManifoldPullback.contDiffAt_manifoldMap_inChart g e f he hf hy.1 hfy
      ((hg (e.symm y) hy.2).contMDiffAt (hS.mem_nhds hy.2)))
    SquareZero.minSmoothness_real_two_le_infty

/-- Exterior differentiation commutes with actual tangent pullback at each point
of the open source domain. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_pullback_on (form : Algebra.RawManifoldForm F N n)
    (hS : IsOpen S) (hT : IsOpen T) (hform : Algebra.IsSmoothManifoldFormOn form T)
    (g : M → N) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g S)
    (hmap : MapsTo g S T) {x : M} (hxS : x ∈ S) :
    (form.pullback (E := E) g).exteriorDerivative x =
      form.exteriorDerivative.pullback (E := E) g x := by
  let e := chartAt E x
  let f := chartAt F (g x)
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hf : f ∈ atlas F N := chart_mem_atlas F (g x)
  have hx : x ∈ e.source := mem_chart_source E x
  have hy : e x ∈ Algebra.manifoldFormChartDomain e S := by
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ S
    rwa [e.left_inv hx]
  have hfy : g (e.symm (e x)) ∈ f.source := by
    rw [e.left_inv hx]
    exact mem_chart_source F (g x)
  have hfT : f (g (e.symm (e x))) ∈ Algebra.manifoldFormChartDomain f T := by
    refine ⟨f.map_source hfy, ?_⟩
    change f.symm (f (g (e.symm (e x)))) ∈ T
    rw [f.left_inv hfy]
    exact hmap hy.2
  have hchart : ((form.pullback g).exteriorDerivative).inChart e (e x) =
      (form.exteriorDerivative.pullback g).inChart e (e x) := by
    rw [(form.pullback g).exteriorDerivative_inChart_on hS
      (form.pullback_smooth_on hS hT hform g hg hmap) e he hy]
    rw [form.extDeriv_pullback_inChart_on hS hT hform g hg hmap e f he hf hy hfy]
    rw [form.exteriorDerivative.pullback_inChart g e f he hf hy.1 hfy
      (((hg (e.symm (e x)) hy.2).contMDiffAt (hS.mem_nhds hy.2)).mdifferentiableAt
        (by simp))]
    rw [form.exteriorDerivative_inChart_on hT hform f hf hfT]
  have hcovector := congrArg
    (fun value : E [⋀^Fin (n + 1)]→L[ℝ] ℂ =>
      value.compContinuousLinearMap (Charts.chartTangentMap e x)) hchart
  simpa only [Algebra.RawManifoldForm.inChart_comp_chartTangentMap _ e he hx] using hcovector

end

end OAI.Analysis.DifferentialForms.Manifold
