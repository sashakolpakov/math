import OAI.Analysis.DifferentialForms.Manifold.ManifoldPullback

/-! # Pullback Laws -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
Identity, composition, and exterior-derivative compatibility for the actual
manifold pullback. No comparison with singular cohomology is asserted here.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ}

section

@[simp]
theorem Algebra.RawManifoldForm.pullback_id (form : Algebra.RawManifoldForm E M n) :
    form.pullback (E := E) (id : M → M) = form := by
  funext x
  ext v
  simp only [Algebra.RawManifoldForm.pullback_apply, mfderiv_id,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.id_apply, Function.comp_def, id_eq]

/-- Functoriality is precisely the manifold chain rule on every tangent input. -/
theorem Algebra.RawManifoldForm.pullback_comp (form : Algebra.RawManifoldForm G P n)
    (g : M → N) (hg : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) g)
    (h : N → P) (hh : MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, G) h) :
    form.pullback (E := E) (h ∘ g) =
      (form.pullback (E := F) h).pullback (E := E) g := by
  funext x
  ext v
  simp only [Algebra.RawManifoldForm.pullback_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    mfderiv_comp x (hh (g x)) (hg x), ContinuousLinearMap.coe_comp,
    Function.comp_assoc, Function.comp_apply]

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The chart expression determines the actual tangent covector. -/
theorem Algebra.RawManifoldForm.inChart_comp_chartTangentMap (form : Algebra.RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {x : M}
    (hx : x ∈ e.source) :
    (form.inChart e (e x)).compContinuousLinearMap (Charts.chartTangentMap e x) = form x := by
  change ((form (e.symm (e x))).compContinuousLinearMap
    (Charts.chartInverseTangentMap e (e x))).compContinuousLinearMap _ = _
  rw [e.left_inv hx]
  ext v
  change form x (fun i => Charts.chartInverseTangentMap e (e x) (Charts.chartTangentMap e x (v i))) =
    form x v
  apply congrArg (form x)
  funext i
  exact congrArg (fun linear => linear (v i)) (Charts.chartInverseTangentMap_comp e he hx)

variable [IsManifold 𝓘(ℝ, F) ∞ N]

/-- Exterior differentiation of a pulled-back form, in arbitrary valid charts. -/
theorem Algebra.RawManifoldForm.extDeriv_pullback_inChart (form : Algebra.RawManifoldForm F N n)
    (hform : Algebra.IsSmoothManifoldFormOn form univ)
    (g : M → N) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ atlas E M) (hf : f ∈ atlas F N) {y : E}
    (hy : y ∈ e.target) (hfy : g (e.symm y) ∈ f.source) :
    extDeriv ((form.pullback g).inChart e) y =
      (extDeriv (form.inChart f) (f (g (e.symm y)))).compContinuousLinearMap
        (fderiv ℝ (f ∘ g ∘ e.symm) y) := by
  rw [(form.pullback_inChart_eventuallyEq g hg e f he hf hy hfy).extDeriv_eq]
  exact extDeriv_pullback
    ((Derivative.smoothForm_contDiffAt_inChart (form := form) hform f hf (f.map_source hfy)).differentiableAt
      (by simp))
    (ManifoldPullback.contDiffAt_manifoldMap_inChart g e f he hf hy hfy hg.contMDiffAt)
    SquareZero.minSmoothness_real_two_le_infty

/-- The global exterior derivative commutes with pullback along a smooth map. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_pullback (form : Algebra.RawManifoldForm F N n)
    (hform : Algebra.IsSmoothManifoldFormOn form univ)
    (g : M → N) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g) :
    (form.pullback (E := E) g).exteriorDerivative =
      form.exteriorDerivative.pullback (E := E) g := by
  funext x
  let e := chartAt E x
  let f := chartAt F (g x)
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hf : f ∈ atlas F N := chart_mem_atlas F (g x)
  have hx : x ∈ e.source := mem_chart_source E x
  have hy : e x ∈ e.target := e.map_source hx
  have hfy : g (e.symm (e x)) ∈ f.source := by
    rw [e.left_inv hx]
    exact mem_chart_source F (g x)
  have hchart : ((form.pullback g).exteriorDerivative).inChart e (e x) =
      (form.exteriorDerivative.pullback g).inChart e (e x) := by
    rw [(form.pullback g).exteriorDerivative_inChart
      (form.pullback_smooth hform g hg) e he hy]
    rw [form.extDeriv_pullback_inChart hform g hg e f he hf hy hfy]
    rw [form.exteriorDerivative.pullback_inChart g e f he hf hy hfy
      (hg.mdifferentiableAt (by simp))]
    rw [form.exteriorDerivative_inChart hform f hf (f.map_source hfy)]
  have hcovector := congrArg
    (fun value : E [⋀^Fin (n + 1)]→L[ℝ] ℂ =>
      value.compContinuousLinearMap (Charts.chartTangentMap e x)) hchart
  simpa only [Algebra.RawManifoldForm.inChart_comp_chartTangentMap _ e he hx] using hcovector

end

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  [IsManifold 𝓘(ℝ, G) ∞ P]

@[simp]
theorem Algebra.SmoothManifoldForm.pullback_id (form : Algebra.SmoothManifoldForm E M n) :
    Algebra.SmoothManifoldForm.pullback (id : M → M) contMDiff_id form = form := by
  apply Algebra.SmoothManifoldForm.ext
  intro x
  exact congrFun (Algebra.RawManifoldForm.pullback_id (form : Algebra.RawManifoldForm E M n)) x

theorem Algebra.SmoothManifoldForm.pullback_comp (g : M → N) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (h : N → P) (hh : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ h)
    (form : Algebra.SmoothManifoldForm G P n) :
    Algebra.SmoothManifoldForm.pullback (h ∘ g) (hh.comp hg) form = Algebra.SmoothManifoldForm.pullback g hg (Algebra.SmoothManifoldForm.pullback h hh form) := by
  apply Algebra.SmoothManifoldForm.ext
  intro x
  exact congrFun ((form : Algebra.RawManifoldForm G P n).pullback_comp
    g (hg.mdifferentiable (by simp)) h (hh.mdifferentiable (by simp))) x

/-- Naturality of the exterior derivative for genuine smooth manifold forms. -/
theorem Algebra.SmoothManifoldForm.d_pullback (g : M → N) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (form : Algebra.SmoothManifoldForm F N n) :
    Algebra.SmoothManifoldForm.d (Algebra.SmoothManifoldForm.pullback g hg form) = Algebra.SmoothManifoldForm.pullback g hg (Algebra.SmoothManifoldForm.d form) := by
  apply Algebra.SmoothManifoldForm.ext
  intro x
  exact congrFun ((form : Algebra.RawManifoldForm F N n).exteriorDerivative_pullback
    form.smooth g hg) x

end

end OAI.Analysis.DifferentialForms.Manifold
