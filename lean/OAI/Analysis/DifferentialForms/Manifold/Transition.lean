import OAI.Analysis.DifferentialForms.Manifold.Charts

/-! # Transition -/

namespace OAI.Analysis.DifferentialForms.Manifold

/-!
# Change of chart for actual differential forms

The chart formulas follow from the tangent chain rule. Local equality then
transports exterior differentiation through the same coordinate changes.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

/-- Covector fields in two charts are related by ordinary differential-form
pullback along the actual transition map. -/
theorem Algebra.RawManifoldForm.inChart_transition (form : Algebra.RawManifoldForm E M n)
    (e f : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (hf : f ∈ atlas E M)
    {y : E} (hy : y ∈ e.target) (hfy : e.symm y ∈ f.source) :
    form.inChart e y =
      (form.inChart f (f (e.symm y))).compContinuousLinearMap
        (fderiv ℝ (f ∘ e.symm) y) := by
  change (form (e.symm y)).compContinuousLinearMap (Charts.chartInverseTangentMap e y) =
    ((form (f.symm (f (e.symm y)))).compContinuousLinearMap
      (Charts.chartInverseTangentMap f (f (e.symm y)))).compContinuousLinearMap _
  rw [f.left_inv hfy, Charts.fderiv_chart_transition e f he hf hy hfy]
  ext v
  change form (e.symm y) (fun i => Charts.chartInverseTangentMap e y (v i)) =
    form (e.symm y) (fun i => Charts.chartInverseTangentMap f (f (e.symm y))
      (Charts.chartTangentMap f (e.symm y) (Charts.chartInverseTangentMap e y (v i))))
  apply congrArg (form (e.symm y))
  funext i
  exact (congrArg (fun linear => linear (Charts.chartInverseTangentMap e y (v i)))
    (Charts.chartInverseTangentMap_comp f hf hfy)).symm

/-- The coordinate-change identity holds on a neighborhood of every overlap point. -/
theorem Algebra.RawManifoldForm.inChart_transition_eventuallyEq (form : Algebra.RawManifoldForm E M n)
    (e f : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (hf : f ∈ atlas E M)
    {y : E} (hy : y ∈ e.target) (hfy : e.symm y ∈ f.source) :
    form.inChart e =ᶠ[𝓝 y]
      (fun z => (form.inChart f (f (e.symm z))).compContinuousLinearMap
        (fderiv ℝ (f ∘ e.symm) z)) := by
  filter_upwards [(e.isOpen_inter_preimage_symm f.open_source).mem_nhds ⟨hy, hfy⟩]
    with z hz
  exact form.inChart_transition e f he hf hz.1 hz.2

/-- Exterior differentiation obeys the same transition law whenever the
coefficient expression is differentiable at the overlap point. -/
theorem Algebra.RawManifoldForm.extDeriv_inChart_transition_of_differentiableAt
    (form : Algebra.RawManifoldForm E M n)
    (e f : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (hf : f ∈ atlas E M)
    {y : E} (hy : y ∈ e.target) (hfy : e.symm y ∈ f.source)
    (hform : DifferentiableAt ℝ (form.inChart f) (f (e.symm y))) :
    extDeriv (form.inChart e) y =
      (extDeriv (form.inChart f) (f (e.symm y))).compContinuousLinearMap
        (fderiv ℝ (f ∘ e.symm) y) := by
  rw [(form.inChart_transition_eventuallyEq e f he hf hy hfy).extDeriv_eq]
  exact extDeriv_pullback hform (Charts.contDiffAt_chart_transition e f he hf hy hfy)
    SquareZero.minSmoothness_real_two_le_infty

/-- A smooth global differential form has compatible local exterior derivatives. -/
theorem Algebra.RawManifoldForm.extDeriv_inChart_transition (form : Algebra.RawManifoldForm E M n)
    (hform : Algebra.IsSmoothManifoldFormOn form univ)
    (e f : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (hf : f ∈ atlas E M)
    {y : E} (hy : y ∈ e.target) (hfy : e.symm y ∈ f.source) :
    extDeriv (form.inChart e) y =
      (extDeriv (form.inChart f) (f (e.symm y))).compContinuousLinearMap
        (fderiv ℝ (f ∘ e.symm) y) := by
  have hs : ContDiffOn ℝ ∞ (form.inChart f) f.target := by
    simpa only [Algebra.manifoldFormChartDomain, preimage_univ, inter_univ] using hform f hf
  exact form.extDeriv_inChart_transition_of_differentiableAt e f he hf hy hfy
    ((hs.contDiffAt (f.open_target.mem_nhds (f.map_source hfy))).differentiableAt (by simp))

end OAI.Analysis.DifferentialForms.Manifold
