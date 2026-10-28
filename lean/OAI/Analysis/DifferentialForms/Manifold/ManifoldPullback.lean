import OAI.Analysis.DifferentialForms.Manifold.Derivative
import OAI.Analysis.DifferentialForms.Manifold.Alternatization

/-! # Manifold Pullback -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
Pullback of genuine smooth manifold forms along a smooth map. The definition uses
the actual tangent derivative; its coordinate formula and smoothness are proved.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  {n : ℕ}

/-- The ordinary derivative of a coordinate representation is the tangent
derivative conjugated by the derivatives of the two charts. -/
theorem ManifoldPullback.fderiv_manifoldMap_inChart (g : M → N)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ atlas E M) (hf : f ∈ atlas F N) {y : E}
    (hy : y ∈ e.target) (hfy : g (e.symm y) ∈ f.source)
    (hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) g (e.symm y)) :
    fderiv ℝ (f ∘ g ∘ e.symm) y =
      (Charts.chartTangentMap f (g (e.symm y))).comp
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g (e.symm y)).comp
          (Charts.chartInverseTangentMap e y)) := by
  have he' := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E)) he hy
  have hf' := mdifferentiableAt_atlas (I := 𝓘(ℝ, F)) hf hfy
  have hge := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, F)) y hg he'
  have htotal := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))
    (I'' := 𝓘(ℝ, F)) y hf' (hg.comp y he')
  rw [mfderiv_eq_fderiv, hge] at htotal
  ext v
  exact congrArg (fun linear => linear v) htotal

/-- A smooth manifold map has a smooth coordinate representation near every
point where the chosen source and target charts apply. -/
theorem ManifoldPullback.contDiffAt_manifoldMap_inChart (g : M → N)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ atlas E M) (hf : f ∈ atlas F N) {y : E}
    (hy : y ∈ e.target) (hfy : g (e.symm y) ∈ f.source)
    (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g (e.symm y)) :
    ContDiffAt ℝ ∞ (f ∘ g ∘ e.symm) y := by
  have he' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy
  have hf' : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ f (g (e.symm y)) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hf) hfy
  exact (hf'.comp y (hg.comp y he')).contDiffAt

section

/-- Pullback of an actual alternating covector field along the tangent map. -/
def Algebra.RawManifoldForm.pullback (form : Algebra.RawManifoldForm F N n) (g : M → N) : Algebra.RawManifoldForm E M n :=
  fun x => (form (g x)).compContinuousLinearMap (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x)

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
@[simp]
theorem Algebra.RawManifoldForm.pullback_apply (form : Algebra.RawManifoldForm F N n) (g : M → N) (x : M) :
    form.pullback g x =
      (form (g x)).compContinuousLinearMap (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x) := rfl

/-- The coordinate formula for pullback follows from the manifold chain rule. -/
theorem Algebra.RawManifoldForm.pullback_inChart (form : Algebra.RawManifoldForm F N n) (g : M → N)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ atlas E M) (hf : f ∈ atlas F N) {y : E}
    (hy : y ∈ e.target) (hfy : g (e.symm y) ∈ f.source)
    (hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) g (e.symm y)) :
    (form.pullback g).inChart e y =
      (form.inChart f (f (g (e.symm y)))).compContinuousLinearMap
        (fderiv ℝ (f ∘ g ∘ e.symm) y) := by
  change ((form (g (e.symm y))).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g (e.symm y))).compContinuousLinearMap
        (Charts.chartInverseTangentMap e y) =
    ((form (f.symm (f (g (e.symm y))))).compContinuousLinearMap
      (Charts.chartInverseTangentMap f (f (g (e.symm y))))).compContinuousLinearMap _
  rw [f.left_inv hfy, ManifoldPullback.fderiv_manifoldMap_inChart g e f he hf hy hfy hg]
  ext v
  change form (g (e.symm y))
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g (e.symm y)
        (Charts.chartInverseTangentMap e y (v i))) =
    form (g (e.symm y))
      (fun i => Charts.chartInverseTangentMap f (f (g (e.symm y)))
        (Charts.chartTangentMap f (g (e.symm y))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g (e.symm y)
            (Charts.chartInverseTangentMap e y (v i)))))
  apply congrArg (form (g (e.symm y)))
  funext i
  exact (congrArg (fun linear => linear
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g (e.symm y) (Charts.chartInverseTangentMap e y (v i))))
    (Charts.chartInverseTangentMap_comp f hf hfy)).symm

/-- The coordinate identity holds on a neighborhood, as required to transport
derivatives and smoothness. -/
theorem Algebra.RawManifoldForm.pullback_inChart_eventuallyEq (form : Algebra.RawManifoldForm F N n) (g : M → N)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ atlas E M) (hf : f ∈ atlas F N) {y : E}
    (hy : y ∈ e.target) (hfy : g (e.symm y) ∈ f.source) :
    (form.pullback g).inChart e =ᶠ[𝓝 y]
      fun z => (form.inChart f (f (g (e.symm z)))).compContinuousLinearMap
        (fderiv ℝ (f ∘ g ∘ e.symm) z) := by
  have hopen := e.isOpen_inter_preimage_symm (f.open_source.preimage hg.continuous)
  filter_upwards [hopen.mem_nhds ⟨hy, hfy⟩] with z hz
  exact form.pullback_inChart g e f he hf hz.1 hz.2 (hg.mdifferentiableAt (by simp))

/-- Pullback preserves the standard chartwise smoothness condition. -/
theorem Algebra.RawManifoldForm.pullback_smooth (form : Algebra.RawManifoldForm F N n)
    (hform : Algebra.IsSmoothManifoldFormOn form univ) (g : M → N)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g) :
    Algebra.IsSmoothManifoldFormOn (E := E) (form.pullback g) univ := by
  intro e he y hy
  let f := chartAt F (g (e.symm y))
  have hf : f ∈ atlas F N := chart_mem_atlas F (g (e.symm y))
  have hfy : g (e.symm y) ∈ f.source := mem_chart_source F (g (e.symm y))
  have hcoord := ManifoldPullback.contDiffAt_manifoldMap_inChart g e f he hf hy.1 hfy hg.contMDiffAt
  have hcoeff : ContDiffAt ℝ ∞ (form.inChart f) (f (g (e.symm y))) :=
    Derivative.smoothForm_contDiffAt_inChart (form := form) hform f hf (f.map_source hfy)
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
    (form.pullback_inChart_eventuallyEq g hg e f he hf hy.1 hfy)).contDiffWithinAt

end

/-- The complex-linear pullback map on actual smooth manifold forms. -/
def Algebra.SmoothManifoldForm.pullback (g : M → N) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g) :
    Algebra.SmoothManifoldForm F N n →ₗ[ℂ] Algebra.SmoothManifoldForm E M n where
  toFun form := ⟨(form : Algebra.RawManifoldForm F N n).pullback g,
    (form : Algebra.RawManifoldForm F N n).pullback_smooth form.smooth g hg⟩
  map_add' form other := by
    apply Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    rfl
  map_smul' c form := by
    apply Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    rfl

@[simp]
theorem Algebra.SmoothManifoldForm.pullback_apply (g : M → N) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (form : Algebra.SmoothManifoldForm F N n) (x : M) :
    Algebra.SmoothManifoldForm.pullback g hg form x =
      (form (g x)).compContinuousLinearMap (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x) := rfl

end

end OAI.Analysis.DifferentialForms.Manifold
